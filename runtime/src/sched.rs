//! fz-qw6 — selective-receive scheduler primitives.
//!
//! The same three operations — sender-probe, initial-scan, after-timer
//! fire — drive `Term::ReceiveMatched` on every execution path. JIT
//! state lives in `Runtime` (src/runtime.rs); AOT state lives in the
//! thread-locals on `aot_shim`. Both call into the same pure helpers
//! here so the logic exists once.
//!
//! Each helper takes `&mut Process` and mutates the task's
//! selective-receive state directly; timer cancellation goes through
//! `scheduler_hooks::dispatch_timer_cancel`, which dispatches to
//! whichever wheel the caller installed.

use crate::any_value::{self, AnyValue, AnyValueRef, ValueKind};
use crate::exec_ctx::timer_cancel;
use crate::heap::Heap;
use crate::park::materialize_outcome_closure;
use crate::process::{Process, ProcessState};
use crate::timer::TimerId;
use std::collections::VecDeque;
use std::ptr::write;

/// Mint a fresh-task entry thunk on `heap`: a one-capture closure whose code
/// is `fz_entry_thunk` and whose capture[0] is `inner` (the task's inner
/// closure). The scheduler resumes this thunk through the single `fz_resume`
/// verb; on first resume the thunk supplies `inner`'s halt-cont and enters it.
///
/// `inner` must already live in `heap` (deep-copied closure, or a freshly
/// minted main inner). The capture is a real closure reference, so GC traces
/// through the thunk to the inner closure.
pub fn mint_entry_thunk(heap: &mut Heap, entry_thunk_addr: *const u8, inner: *mut u8) -> *mut u8 {
    // Placeholder schema id: a scaffolding closure's schema is never consulted
    // (see `alloc_closure_slots_with_schema`), so minting does not register a
    // `ClosureEnv1` schema that would shift program schema ids.
    let bits = heap.alloc_closure_slots_with_schema(SCAFFOLDING_SCHEMA_ID, 1, 0);
    let p = any_value::closure_addr_from_tagged(bits).expect("entry thunk closure ptr");
    let inner_av = AnyValue::HeapRef(
        AnyValueRef::from_heap_object(ValueKind::CLOSURE, inner as *const u8).expect("entry thunk inner closure ref"),
    );
    unsafe {
        write(p.add(8) as *mut u64, entry_thunk_addr as u64);
        any_value::closure_capture_set(p, 0, inner_av);
    }
    p
}

/// Placeholder schema id written into scheduler scaffolding closures whose
/// schema is never consulted. See `Heap::alloc_closure_slots_with_schema`.
const SCAFFOLDING_SCHEMA_ID: u32 = 0;

/// Mint a main-style entry's synthetic inner closure on `heap`: code is
/// `fz_main_trampoline`, capture[0] is the raw `(cont)` main fn pointer stored
/// as a raw int (so GC never treats it as a heap reference), and `halt_kind`
/// matches the entry fn's return repr. Wrapping this in `mint_entry_thunk`
/// lets a plain main fn ride the same resume path as a spawned user closure.
pub fn mint_main_inner(
    heap: &mut Heap,
    main_trampoline_addr: *const u8,
    main_fp: *const u8,
    halt_kind: u16,
) -> *mut u8 {
    let bits = heap.alloc_closure_slots_with_schema(SCAFFOLDING_SCHEMA_ID, 1, halt_kind);
    let p = any_value::closure_addr_from_tagged(bits).expect("main inner closure ptr");
    unsafe {
        write(p.add(8) as *mut u64, main_trampoline_addr as u64);
        any_value::closure_capture_set(p, 0, AnyValue::Int(main_fp as i64));
    }
    p
}

/// Outcome of `probe_sender`.
#[derive(Debug, PartialEq, Eq)]
pub enum ProbeOutcome {
    /// Matcher hit: caller should enqueue the receiver for dispatch.
    Hit,
    /// No matcher hit (either no `wait` or the matcher
    /// rejected). Message is in the mailbox; caller must NOT do the
    /// non-selective Blocked→Ready wake — a selective-receive park is not
    /// satisfied by a generic arrival.
    Miss,
}

/// Sender-side selective-receive probe. Called on `send` arrival.
///
/// If `task.wait.is_some()`, run its matcher against `msg`:
/// - Hit: clear `wait`, cancel after-timer (via
///   `dispatch_timer_cancel`), set `runnable_closure`, flip
///   Ready. Caller enqueues.
/// - Miss: push msg to mailbox. Caller does NOT wake.
///
/// If not parked: push msg to mailbox. Returns Miss; caller may apply
/// the non-selective wake rule itself.
pub fn probe_sender(task: &mut Process, msg: AnyValueRef) -> ProbeOutcome {
    let task_ptr: *mut Process = task;
    if let Some(park) = task.wait.as_ref() {
        match park.try_match(task_ptr, msg) {
            Some((clause_idx, bound_vals)) => {
                let (template, timer_id) = {
                    let park = task.wait.as_ref().expect("checked above");
                    (park.clause_bodies[clause_idx], park.after_timer_id)
                };
                let cont = materialize_outcome_closure(&mut task.heap, template, &bound_vals);
                task.wait = None;
                if let Some(id) = timer_id {
                    timer_cancel(task, id);
                }
                task.set_runnable_closure(cont);
                task.state = ProcessState::Ready;
                ProbeOutcome::Hit
            }
            None => {
                task.mailbox.push_back(msg);
                ProbeOutcome::Miss
            }
        }
    } else {
        task.mailbox.push_back(msg);
        ProbeOutcome::Miss
    }
}

/// Outcome of `initial_scan`.
#[derive(Debug, PartialEq, Eq)]
pub enum ScanOutcome {
    /// Matcher hit during the mailbox walk; `runnable_closure`
    /// is set, caller should dispatch.
    Hit,
    /// `wait` was set but no message matched. Task is now
    /// Blocked; mailbox left intact (save-queue semantics).
    Miss,
    /// No `wait` or empty mailbox. No state change.
    NotApplicable,
}

/// Initial-scan entry. Called when a task wakes Ready with a
/// `wait` and mailbox messages already present.
///
/// Walks mailbox in arrival order trying the matcher on each message.
/// First hit: splice the message out, restore the rejected prefix in
/// original order, cancel after-timer, set `runnable_closure`.
/// No hit: state ← Blocked; mailbox untouched (Erlang save-queue rule).
pub fn initial_scan(task: &mut Process) -> ScanOutcome {
    if task.wait.is_none() || task.mailbox.is_empty() {
        return ScanOutcome::NotApplicable;
    }
    let task_ptr: *mut Process = task;

    let mut hit: Option<(usize, Vec<AnyValueRef>)> = None;
    let mut scanned: VecDeque<AnyValueRef> = VecDeque::new();
    while let Some(msg) = task.mailbox.pop_front() {
        let park = task.wait.as_ref().expect("checked above");
        match park.try_match(task_ptr, msg) {
            Some(h) => {
                hit = Some(h);
                break;
            }
            None => scanned.push_back(msg),
        }
    }
    while let Some(m) = scanned.pop_back() {
        task.mailbox.push_front(m);
    }

    match hit {
        Some((clause_idx, bound_vals)) => {
            let (template, timer_id) = {
                let park = task.wait.as_ref().expect("checked above");
                (park.clause_bodies[clause_idx], park.after_timer_id)
            };
            let cont = materialize_outcome_closure(&mut task.heap, template, &bound_vals);
            task.wait = None;
            if let Some(id) = timer_id {
                timer_cancel(task, id);
            }
            task.set_runnable_closure(cont);
            ScanOutcome::Hit
        }
        None => {
            task.state = ProcessState::Blocked;
            ScanOutcome::Miss
        }
    }
}

/// After-timer fire. Called by the scheduler's timer drain for each
/// expired entry. If `task` is still parked on a `ReceiveMatched` with
/// that exact `id`, stash the after-cont as the runnable zero-arg closure and
/// flip Ready.
///
/// Returns `true` when the task transitioned (caller should enqueue);
/// `false` for stale entries whose task is no longer parked on this
/// timer (matcher hit got there first, etc.).
pub fn fire_after_timer(task: &mut Process, id: TimerId) -> bool {
    let Some(park) = task.wait.as_ref() else {
        return false;
    };
    if park.after_timer_id != Some(id) {
        return false;
    }
    let after_cont = park.after_cont;
    task.wait = None;
    task.set_runnable_closure(after_cont);
    task.state = ProcessState::Ready;
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::any_value::AnyValueRef;
    use crate::any_value::ValueKind;
    use crate::heap::SchemaRegistry;
    use crate::park::ParkRecord;
    use std::cell::RefCell;
    use std::ptr::{read, write};
    use std::rc::Rc;

    extern "C" fn match_42(
        _process: *mut Process,
        msg: u64,
        _pinned: *const AnyValueRef,
        out: *mut AnyValueRef,
    ) -> u32 {
        let msg_ref = AnyValueRef::from_raw_word(msg).expect("msg ref");
        if msg_ref.load_int().expect("int msg") == 42 {
            unsafe {
                *out = msg_ref;
            }
            1
        } else {
            0
        }
    }

    fn int_ref(n: i64) -> AnyValueRef {
        let slot = Box::leak(Box::new(n as u64));
        AnyValueRef::from_scalar_slot(ValueKind::INT, slot as *const u64).expect("test int ref")
    }

    fn fresh_task() -> Process {
        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        Process::new(schemas)
    }

    fn template_closure(task: &mut Process, stub: usize) -> *mut u8 {
        let bits = task.heap.alloc_closure_slots(0, 1, 0);
        let p = any_value::closure_addr_from_tagged(bits).expect("template closure ptr");
        unsafe {
            write(p.add(8) as *mut u64, stub as u64);
            any_value::closure_capture_set(p, 0, AnyValue::null());
        }
        bits as *mut u8
    }

    fn park_on_42(task: &mut Process, timer: Option<TimerId>) {
        let template = template_closure(task, 0xdead_beef);
        task.wait = Some(Box::new(ParkRecord {
            matcher_fn: match_42,
            pinned: vec![],
            clause_bodies: vec![template],
            clause_bound_counts: vec![1],
            bound_arity: 1,
            after_deadline_ms: timer.map(|_| 0),
            after_cont: 0xcafe_babe as *mut u8,
            after_timer_id: timer,
        }));
        task.state = ProcessState::Blocked;
    }

    #[test]
    fn probe_sender_hit_sets_runnable_and_flips_ready() {
        let mut task = fresh_task();
        park_on_42(&mut task, None);
        assert_eq!(probe_sender(&mut task, int_ref(42)), ProbeOutcome::Hit);
        assert!(task.wait.is_none());
        assert_eq!(task.state, ProcessState::Ready);
        let runnable = task.runnable_ptr();
        assert!(!runnable.is_null());
        unsafe {
            assert_eq!(read((runnable as *const u8).add(8) as *const u64), 0xdead_beef);
            let cont_addr = runnable;
            let capture_ref =
                AnyValueRef::from_raw_word(any_value::closure_capture_ref_word(cont_addr, 1)).expect("capture ref");
            assert_eq!(capture_ref.load_int().expect("capture int ref"), 42);
        }
        assert!(task.mailbox.is_empty());
    }

    #[test]
    fn probe_sender_miss_pushes_mailbox_keeps_park() {
        let mut task = fresh_task();
        park_on_42(&mut task, None);
        assert_eq!(probe_sender(&mut task, int_ref(99)), ProbeOutcome::Miss);
        assert!(task.wait.is_some());
        assert_eq!(task.state, ProcessState::Blocked);
        assert!(task.runnable_ptr().is_null());
        assert_eq!(task.mailbox.len(), 1);
    }

    #[test]
    fn probe_sender_not_parked_pushes_mailbox_returns_miss() {
        let mut task = fresh_task();
        assert_eq!(probe_sender(&mut task, int_ref(7)), ProbeOutcome::Miss);
        assert_eq!(task.mailbox.len(), 1);
    }

    #[test]
    fn initial_scan_not_applicable_without_park() {
        let mut task = fresh_task();
        task.mailbox.push_back(int_ref(42));
        assert_eq!(initial_scan(&mut task), ScanOutcome::NotApplicable);
        assert_eq!(task.mailbox.len(), 1);
    }

    #[test]
    fn initial_scan_not_applicable_with_empty_mailbox() {
        let mut task = fresh_task();
        park_on_42(&mut task, None);
        assert_eq!(initial_scan(&mut task), ScanOutcome::NotApplicable);
        assert!(task.wait.is_some());
    }

    #[test]
    fn initial_scan_hit_splices_and_preserves_prefix_order() {
        let mut task = fresh_task();
        park_on_42(&mut task, None);
        task.mailbox.push_back(int_ref(1));
        task.mailbox.push_back(int_ref(2));
        task.mailbox.push_back(int_ref(42));
        task.mailbox.push_back(int_ref(3));
        assert_eq!(initial_scan(&mut task), ScanOutcome::Hit);
        assert!(task.wait.is_none());
        assert!(!task.runnable_ptr().is_null());
        // 1, 2, 3 stay in arrival order; 42 was spliced out.
        let mb: Vec<i64> = task.mailbox.iter().map(|v| v.load_int().unwrap()).collect();
        assert_eq!(mb, vec![1, 2, 3]);
    }

    #[test]
    fn initial_scan_miss_blocks_and_preserves_mailbox() {
        let mut task = fresh_task();
        park_on_42(&mut task, None);
        task.mailbox.push_back(int_ref(1));
        task.mailbox.push_back(int_ref(2));
        assert_eq!(initial_scan(&mut task), ScanOutcome::Miss);
        assert_eq!(task.state, ProcessState::Blocked);
        assert!(task.wait.is_some());
        let mb: Vec<i64> = task.mailbox.iter().map(|v| v.load_int().unwrap()).collect();
        assert_eq!(mb, vec![1, 2]);
    }

    #[test]
    fn fire_after_timer_matches_id_and_transitions() {
        let mut task = fresh_task();
        park_on_42(&mut task, Some(7));
        assert!(fire_after_timer(&mut task, 7));
        assert!(task.wait.is_none());
        assert_eq!(task.state, ProcessState::Ready);
        assert_eq!(task.runnable_ptr() as usize, 0xcafe_babe);
    }

    #[test]
    fn fire_after_timer_stale_id_no_transition() {
        let mut task = fresh_task();
        park_on_42(&mut task, Some(7));
        assert!(!fire_after_timer(&mut task, 99));
        assert!(task.wait.is_some());
        assert_eq!(task.state, ProcessState::Blocked);
    }

    #[test]
    fn fire_after_timer_unparked_no_transition() {
        let mut task = fresh_task();
        assert!(!fire_after_timer(&mut task, 7));
    }
}
