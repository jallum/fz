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
#[path = "sched_test.rs"]
mod sched_test;
