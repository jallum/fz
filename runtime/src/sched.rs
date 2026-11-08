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
//!
//! A send never writes into the receiver's heap. The sender matches and
//! copies on its own heap, inside a gift window, and queues the result on the
//! receiver's `in_queue`; the receiver grafts the queue at its next dispatch.

use crate::any_value::{self, AnyValue, AnyValueRef, ValueKind};
use crate::exec_ctx::{timer_cancel, timer_schedule};
use crate::heap::{GiftSegment, Heap, deep_copy_any_value_ref};
use crate::park::ParkRecord;
use crate::process::{PidId, Process, ProcessState};
use crate::timer::TimerId;
use std::collections::HashMap;
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

/// Storage one process allocated for another, with what the receiver does
/// with it. The segment holds every heap object the payload's references
/// point at; nothing in it points back into the sender.
pub struct Gift {
    pub segment: GiftSegment,
    pub payload: GiftPayload,
}

pub enum GiftPayload {
    /// A message the receiver was not waiting for. It joins the mailbox.
    Message(AnyValueRef),
    /// A message the sender matched against the receiver's parked receive:
    /// the winning clause and the values its pattern bound. The message
    /// itself is consumed by the match and never reaches the mailbox.
    Match {
        clause_idx: usize,
        bound_vals: Vec<AnyValueRef>,
    },
}

/// Outcome of `probe_sender`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProbeOutcome {
    /// The sender matched the receiver's parked receive. The caller makes
    /// the receiver runnable through its scheduling core.
    Hit,
    /// Nothing to match (no parked receive, or one a sender has already
    /// matched) or the matcher rejected. The message is queued for the
    /// mailbox and nothing wakes: a parked receive is not satisfied by a
    /// generic arrival.
    Miss,
}

/// What one send cost and produced, for telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SendProbe {
    pub outcome: ProbeOutcome,
    pub receiver: PidId,
    /// Reductions the matcher charged the sender.
    pub reductions: i64,
    /// Bytes and blocks of the gift segment the send produced.
    pub gift_bytes: usize,
    pub gift_blocks: usize,
}

/// Copy `values` into a gift window on `heap`. One forwarding map spans all
/// of them, so structure shared between two values stays shared in the copy.
/// Nothing to copy opens no window and costs no block.
pub fn gift_copy(heap: &mut Heap, values: &[AnyValueRef]) -> (GiftSegment, Vec<AnyValueRef>) {
    if values.is_empty() {
        return (GiftSegment::empty(), Vec::new());
    }
    let source = heap.view();
    let mut forwarding = HashMap::new();
    heap.begin_gift();
    let copied = values
        .iter()
        .map(|value| deep_copy_any_value_ref(*value, &source, heap, &mut forwarding))
        .collect();
    (heap.end_gift(), copied)
}

/// Sender-side selective-receive probe. Called on `send` arrival with `msg`
/// on the sender's heap. One answer to "does this send wake a waiting
/// receive?" for every execution path.
///
/// A receiver with `wait` set has already searched its mailbox, so only
/// `msg` is tested against its matcher, and the matcher runs on the sender:
/// the sender is the running process, and anything the matcher boxes lands
/// on its heap. Either way the sender copies what the receiver will keep into
/// a gift on its own heap and queues it on the receiver:
/// - Hit: the bound values, with the after-timer cancelled so it cannot fire
///   for a receive that is already decided. The caller wakes the receiver.
/// - Miss: the whole message, for the mailbox. The caller does not wake.
///
/// A receiver whose receive is already matched by an earlier sender is not
/// probed again; that message is a miss.
pub fn probe_sender(sender: &mut Process, receiver: &mut Process, msg: AnyValueRef) -> SendProbe {
    let sender_ptr: *mut Process = sender;
    let mut reductions = 0;
    let matched = match receiver.wait.as_ref() {
        Some(park) if !receiver.has_pending_match() => {
            let before = sender.reductions_remaining;
            let hit = park.try_match(sender_ptr, msg);
            reductions = i64::from(before) - i64::from(sender.reductions_remaining);
            hit
        }
        _ => None,
    };
    match matched {
        Some((clause_idx, bound_vals)) => {
            let timer = receiver
                .wait
                .as_mut()
                .expect("a matched receive is still parked")
                .after_timer_id
                .take();
            if let Some(id) = timer {
                timer_cancel(receiver, id);
            }
            gift_match(sender, receiver, clause_idx, &bound_vals, reductions)
        }
        None => SendProbe {
            reductions,
            ..gift_message(sender, receiver, msg)
        },
    }
}

/// A miss: gift `msg` whole for `receiver`'s mailbox. The caller does not
/// wake the receiver.
pub fn gift_message(sender: &mut Process, receiver: &mut Process, msg: AnyValueRef) -> SendProbe {
    let (segment, copied) = gift_copy(&mut sender.heap, &[msg]);
    queue_gift(
        receiver,
        segment,
        GiftPayload::Message(copied[0]),
        ProbeOutcome::Miss,
        0,
    )
}

/// A hit: gift the values clause `clause_idx` bound, charging `reductions`
/// to the probe. The caller has cancelled the receive's after-timer and goes
/// on to wake the receiver.
pub fn gift_match(
    sender: &mut Process,
    receiver: &mut Process,
    clause_idx: usize,
    bound: &[AnyValueRef],
    reductions: i64,
) -> SendProbe {
    let (segment, bound_vals) = gift_copy(&mut sender.heap, bound);
    let payload = GiftPayload::Match { clause_idx, bound_vals };
    queue_gift(receiver, segment, payload, ProbeOutcome::Hit, reductions)
}

fn queue_gift(
    receiver: &mut Process,
    segment: GiftSegment,
    payload: GiftPayload,
    outcome: ProbeOutcome,
    reductions: i64,
) -> SendProbe {
    let probe = SendProbe {
        outcome,
        receiver: receiver.pid,
        reductions,
        gift_bytes: segment.fill_bytes(),
        gift_blocks: segment.block_count(),
    };
    push_gift(receiver, Gift { segment, payload });
    probe
}

/// Queue a gift on `receiver`. A parked receive is decided once, so a second
/// match for the same receiver is a scheduler bug.
pub fn push_gift(receiver: &mut Process, gift: Gift) {
    if matches!(gift.payload, GiftPayload::Match { .. }) {
        assert!(
            !receiver.has_pending_match(),
            "a receiver takes one match per parked receive"
        );
    }
    receiver.in_queue.push_back(gift);
}

/// Graft every queued gift into `task`'s heap, in arrival order. Messages
/// join the mailbox; the match for the parked receive, if a sender queued
/// one, is returned for the caller to deliver. Runs at the start of a
/// dispatch, before any of the task's code or a collection touches the heap,
/// so the task never sees a reference into storage it does not own.
pub fn drain_in_queue(task: &mut Process) -> Option<(usize, Vec<AnyValueRef>)> {
    let mut matched = None;
    while let Some(Gift { segment, payload }) = task.in_queue.pop_front() {
        task.heap.graft(segment);
        match payload {
            GiftPayload::Message(msg) => task.mailbox.push_back(msg),
            GiftPayload::Match { clause_idx, bound_vals } => {
                assert!(matched.is_none(), "a receiver takes one match per parked receive");
                matched = Some((clause_idx, bound_vals));
            }
        }
    }
    matched
}

/// Drain the in-queue and, when a sender matched the parked receive, finish
/// the receive: the park record is taken and the winning clause's outcome
/// closure, built over the gifted bound values, becomes the task's runnable.
/// The compiled paths (JIT and AOT) call this as the first act of a dispatch.
pub fn deliver_in_queue(task: &mut Process) {
    if let Some((clause_idx, bound_vals)) = drain_in_queue(task) {
        let park = task.wait.take().expect("a matched receive is still parked");
        let cont = park.outcome_closure(&mut task.heap, clause_idx, &bound_vals);
        task.set_runnable_closure(cont);
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
