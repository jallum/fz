//! fz-qw6 — selective-receive scheduler primitives.
//!
//! The same three operations — receive-reach, sender-probe, after-timer
//! fire — drive `Term::ReceiveMatched` on every execution path. The JIT
//! `Runtime` (src/exec/runtime.rs) and `aot_shim`'s `AotScheduler` both
//! call into the same pure helpers here so the logic exists once; their
//! run queue and timers live in `sched_core`.
//!
//! Each helper takes `&mut Process` and mutates the task's
//! selective-receive state directly; timer cancellation goes through
//! `scheduler_hooks::dispatch_timer_cancel`, which dispatches to
//! whichever wheel the caller installed.

use crate::any_value::{self, AnyValue, AnyValueRef, ValueKind};
use crate::exec_ctx::{timer_cancel, timer_schedule};
use crate::heap::Heap;
use crate::park::{ParkRecord, materialize_outcome_closure};
use crate::process::{Process, ProcessState};
use crate::timer::TimerId;
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
    let bits = heap.alloc_closure_slots(crate::any_value::ClosureDenotationId::INTERNAL, SCAFFOLDING_ARITY, 1, 0);
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

/// Scheduler scaffolding closures are entered by `fz_resume`, never applied to
/// user arguments and never rendered, so their arity is 0.
const SCAFFOLDING_ARITY: u16 = 0;

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
    let bits = heap.alloc_closure_slots(
        crate::any_value::ClosureDenotationId::INTERNAL,
        SCAFFOLDING_ARITY,
        1,
        halt_kind,
    );
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
    /// No matcher hit (either no `wait` or the matcher rejected). Message is
    /// in the mailbox and nothing wakes: a parked receive is not satisfied by
    /// a generic arrival.
    Miss,
}

/// Sender-side selective-receive probe. Called on `send` arrival, with `msg`
/// already copied into the receiver's heap. One answer to "does this send
/// wake a waiting receive?" for every execution path.
///
/// If `task.wait.is_some()`, the receive has already searched the mailbox, so
/// only `msg` is tested against its matcher:
/// - Hit: clear `wait`, cancel the after-timer, set `runnable_closure`. The
///   caller makes the process runnable through its scheduling core.
/// - Miss: push msg to mailbox. Caller does NOT wake.
///
/// If not parked: push msg to mailbox. Returns Miss.
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

/// A process sending to itself hands its own mailbox the reference it already
/// holds; nothing leaves the heap. The sender is running, so it cannot be
/// parked, and the mailbox push is the whole delivery.
pub fn self_send(task: &mut Process, msg: AnyValueRef) {
    assert!(task.wait.is_none(), "a running process has no parked receive");
    task.mailbox.push_back(msg);
}

/// What reaching a `receive` does to the running process.
#[derive(Debug, PartialEq, Eq)]
pub enum ReceiveStep {
    /// The receive is decided: run this closure now (the matched clause's
    /// outcome closure, or the `after` body). The process keeps running.
    Continue(*mut u8),
    /// Nothing matched and the receive must wait. `wait` is recorded, the
    /// after-timer (if any) is armed and the process is Blocked.
    Parked,
}

/// A receive, decided where it is reached. Walks the mailbox oldest first
/// trying the matcher on each message:
/// - Hit: splice the message out (the rest keep their order) and continue
///   with the clause's outcome closure.
/// - Miss with `after 0`: continue with the `after` body.
/// - Miss otherwise: record `park` as `wait`, arm the after-timer for a
///   positive `after`, and Block. The mailbox is left intact (save-queue rule).
///
/// A process with `wait` set has therefore always searched its whole
/// mailbox, so a sender only has to test its own message.
pub fn reach_receive(task: &mut Process, mut park: ParkRecord) -> ReceiveStep {
    let task_ptr: *mut Process = task;
    let hit = (0..task.mailbox.len()).find_map(|i| {
        park.try_match(task_ptr, task.mailbox[i])
            .map(|(clause_idx, bound_vals)| (i, clause_idx, bound_vals))
    });
    if let Some((i, clause_idx, bound_vals)) = hit {
        task.mailbox.remove(i);
        return ReceiveStep::Continue(park.outcome_closure(&mut task.heap, clause_idx, &bound_vals));
    }
    match park.after_deadline_ms {
        Some(0) => ReceiveStep::Continue(park.after_cont),
        after_ms => {
            park.after_timer_id = after_ms.and_then(|ms| timer_schedule(task, task.pid, ms));
            task.wait = Some(Box::new(park));
            task.state = ProcessState::Blocked;
            ReceiveStep::Parked
        }
    }
}

/// After-timer fire. Called by the scheduler's timer drain for each
/// expired entry. If `task` is still parked on a `ReceiveMatched` with
/// that exact `id`, stash the after-cont as the runnable zero-arg closure.
///
/// Returns `true` when the after entry fired and the caller makes the task
/// runnable through its scheduling core; `false` for stale entries whose
/// task is no longer parked on this timer (matcher hit got there first, etc.).
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
    true
}

#[cfg(test)]
#[path = "sched_test.rs"]
mod sched_test;
