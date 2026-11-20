//! Selective-receive scheduler primitives.
//!
//! The same three operations — receive-reach, sender-probe, after-timer
//! fire — drive `Term::ReceiveMatched` on every execution path. The JIT
//! `Runtime` (src/exec/runtime.rs) and `aot_shim`'s `AotScheduler` both
//! call into the same pure helpers here so the logic exists once; their
//! run queue and timers live in `sched_core`.
//!
//! Each helper takes the process and mutates its selective-receive state
//! under its delivery lock (`delivery.rs`); timer cancellation goes through
//! `scheduler_hooks::dispatch_timer_cancel`, which dispatches to
//! whichever wheel the caller installed.
//!
//! A send never writes into the receiver's heap. The sender matches and
//! copies on its own heap, inside a gift window, and queues the result on the
//! receiver's `in_queue`; the receiver grafts the queue at its next dispatch.

use crate::any_value::{self, AnyValue, AnyValueRef, ValueKind};
use crate::delivery::Delivery;
use crate::exec_ctx::{timer_cancel, timer_schedule};
use crate::heap::{GiftSegment, Heap, HeapView, deep_copy_any_value_ref, measure_deep_copy};
use crate::mailbox::Mailbox;
use crate::park::{ParkRecord, Roots};
use crate::process::{PidId, Process, ProcessState};
use crate::timer::TimerId;
use std::ptr::write;

/// Mint a fresh-task entry thunk on `heap`: a one-capture closure whose code
/// is `fz_entry_thunk` and whose `capture[0]` is `inner` (the task's inner
/// closure). The scheduler resumes this thunk through the single `fz_resume`
/// verb; on first resume the thunk supplies `inner`'s halt-cont and enters it.
///
/// `inner` must already live in `heap` (deep-copied closure, or a freshly
/// minted main inner). The capture is a real closure reference, so GC traces
/// through the thunk to the inner closure.
pub fn mint_entry_thunk(heap: &mut Heap, entry_thunk_addr: *const u8, inner: AnyValueRef) -> AnyValueRef {
    let bits = heap.alloc_closure_slots(crate::any_value::ClosureDenotationId::INTERNAL, SCAFFOLDING_ARITY, 1, 0);
    let p = any_value::closure_addr_from_tagged(bits).expect("entry thunk closure ptr");
    let inner_av = AnyValue::from_ref(inner).expect("entry thunk inner closure ref");
    assert_eq!(inner.tag(), ValueKind::CLOSURE, "an entry thunk wraps a closure");
    unsafe {
        write(p.add(8) as *mut u64, entry_thunk_addr as u64);
        any_value::closure_capture_set(p, 0, inner_av);
    }
    AnyValueRef::from_heap_object(ValueKind::CLOSURE, p).expect("entry thunk closure ref")
}

/// Scheduler scaffolding closures are entered by `fz_resume`, never applied to
/// user arguments and never rendered, so their arity is 0.
const SCAFFOLDING_ARITY: u16 = 0;

/// Mint a main-style entry's synthetic inner closure on `heap`: code is
/// `fz_main_trampoline`, `capture[0]` is the raw `(cont)` main fn pointer stored
/// as a raw int (so GC never treats it as a heap reference), and `halt_kind`
/// matches the entry fn's return repr. Wrapping this in `mint_entry_thunk`
/// lets a plain main fn ride the same resume path as a spawned user closure.
pub fn mint_main_inner(
    heap: &mut Heap,
    main_trampoline_addr: *const u8,
    main_fp: *const u8,
    halt_kind: u16,
) -> AnyValueRef {
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
    AnyValueRef::from_heap_object(ValueKind::CLOSURE, p).expect("main inner closure ref")
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
    /// the winning clause and the roots its arguments are read from. The
    /// message itself is consumed by the match and never reaches the mailbox.
    Match { clause_idx: usize, roots: Roots },
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
    /// The roots a hit carries; zero for a miss, whose message is one value.
    pub gift_roots: usize,
}

/// Measure `values`, then copy them into a gift window on `heap` sized to the
/// measurement. A copy keeps no record of what it has copied, as a send in BEAM
/// does not: structure shared between two values, or within one, arrives as a
/// separate copy at each place it is reached. A copy that allocates nothing
/// (no values, or only values that cross as they are) opens no window and
/// costs no block.
pub fn gift_copy(heap: &mut Heap, values: &[AnyValueRef]) -> (GiftSegment, Roots) {
    let Some(source) = open_gift(heap, values) else {
        return (GiftSegment::empty(), values.iter().copied().collect());
    };
    let copied = values
        .iter()
        .map(|value| deep_copy_any_value_ref(*value, &source, heap))
        .collect();
    (heap.end_gift(), copied)
}

/// `gift_copy` of one value, which needs no vector to hold its copy.
pub fn gift_copy_one(heap: &mut Heap, value: AnyValueRef) -> (GiftSegment, AnyValueRef) {
    let Some(source) = open_gift(heap, &[value]) else {
        return (GiftSegment::empty(), value);
    };
    let copied = deep_copy_any_value_ref(value, &source, heap);
    (heap.end_gift(), copied)
}

/// Measure `values` and open a gift window sized to them, returning the view
/// of the source the copy reads. `None` when the copy allocates nothing, and
/// no window opens.
fn open_gift(heap: &mut Heap, values: &[AnyValueRef]) -> Option<HeapView> {
    let source = heap.view();
    let measured = measure_deep_copy(values, &source);
    if measured == 0 {
        return None;
    }
    heap.begin_gift(measured);
    Some(source)
}

/// Sender-side selective-receive probe. Called on `send` arrival with `msg`
/// on the sender's heap. One answer to "does this send wake a waiting
/// receive?" for every execution path.
///
/// The receiver's delivery lock is held from reading the park to queueing the
/// gift, so one sender decides the receive and any other sender, or the
/// after-timer, finds it decided. A receiver with a park has already searched
/// its mailbox, so only `msg` is tested against its matcher, and the matcher
/// runs on the sender: the sender is the running process, and anything the
/// matcher boxes lands on its heap. Either way the sender copies what the
/// receiver will keep into a gift on its own heap and queues it on the
/// receiver:
/// - Hit: the roots the winning clause reads its arguments from, with the
///   after-timer cancelled so it cannot fire for a receive that is already
///   decided. The caller wakes the receiver.
/// - Miss: the whole message, for the mailbox. The caller does not wake.
///
/// A receiver whose receive is already matched by an earlier sender is not
/// probed again; that message is a miss.
pub fn probe_sender(sender: &mut Process, receiver: &Process, msg: AnyValueRef) -> SendProbe {
    let mut delivery = receiver.delivery.lock();
    let sender_ptr: *mut Process = sender;
    let mut roots = Roots::new();
    let before = sender.reductions_remaining;
    let hit = delivery
        .undecided_park()
        .and_then(|park| park.try_match(sender_ptr, msg, &mut roots))
        .map(|(clause_idx, roots)| (clause_idx, roots.len()));
    let reductions = i64::from(before) - i64::from(sender.reductions_remaining);
    let Some((clause_idx, root_count)) = hit else {
        return SendProbe {
            reductions,
            ..gift_message(sender, &mut delivery, receiver.pid, msg)
        };
    };
    let timer = delivery
        .park_mut()
        .expect("a matched receive is still parked")
        .after_timer_id
        .take();
    if let Some(id) = timer {
        timer_cancel(receiver, id);
    }
    gift_match(
        sender,
        &mut delivery,
        receiver.pid,
        clause_idx,
        &roots[..root_count],
        reductions,
    )
}

/// A miss: gift `msg` whole for the receiver's mailbox. The caller holds the
/// receiver's delivery lock and does not wake the receiver.
pub fn gift_message(sender: &mut Process, delivery: &mut Delivery, receiver: PidId, msg: AnyValueRef) -> SendProbe {
    let (segment, copied) = gift_copy_one(&mut sender.heap, msg);
    queue_gift(
        delivery,
        receiver,
        segment,
        GiftPayload::Message(copied),
        ProbeOutcome::Miss,
        0,
    )
}

/// A hit: gift the roots clause `clause_idx` reads its arguments from,
/// charging `reductions` to the probe. The caller holds the receiver's delivery lock, has cancelled
/// the receive's after-timer and goes on to wake the receiver.
pub fn gift_match(
    sender: &mut Process,
    delivery: &mut Delivery,
    receiver: PidId,
    clause_idx: usize,
    roots: &[AnyValueRef],
    reductions: i64,
) -> SendProbe {
    let (segment, roots) = gift_copy(&mut sender.heap, roots);
    let payload = GiftPayload::Match { clause_idx, roots };
    queue_gift(delivery, receiver, segment, payload, ProbeOutcome::Hit, reductions)
}

fn queue_gift(
    delivery: &mut Delivery,
    receiver: PidId,
    segment: GiftSegment,
    payload: GiftPayload,
    outcome: ProbeOutcome,
    reductions: i64,
) -> SendProbe {
    let probe = SendProbe {
        outcome,
        receiver,
        reductions,
        gift_bytes: segment.fill_bytes(),
        gift_blocks: segment.block_count(),
        gift_roots: match &payload {
            GiftPayload::Message(_) => 0,
            GiftPayload::Match { roots, .. } => roots.len(),
        },
    };
    delivery.push_gift(Gift { segment, payload });
    probe
}

/// Drain every queued gift, in arrival order. A message joins the mailbox
/// with its gift segment and waits outside the heap until a receive takes it.
/// The match for the parked receive, if a sender queued one, is grafted into
/// the task's heap and returned for the caller to deliver. The caller holds
/// the task's delivery lock and passes the task's heap and mailbox. Runs at
/// the start of a dispatch, before any of the task's code or a collection
/// touches the heap, so the task never sees a reference into storage it does
/// not own.
pub fn drain_in_queue(delivery: &mut Delivery, heap: &mut Heap, mailbox: &mut Mailbox) -> Option<(usize, Roots)> {
    let mut matched = None;
    while let Some(Gift { segment, payload }) = delivery.pop_gift() {
        match payload {
            GiftPayload::Message(msg) => mailbox.push(msg, segment),
            GiftPayload::Match { clause_idx, roots } => {
                heap.graft(segment);
                assert!(matched.is_none(), "a receiver takes one match per parked receive");
                matched = Some((clause_idx, roots));
            }
        }
    }
    matched
}

/// Drain the in-queue and, when a sender matched the parked receive, finish
/// the receive: the park record is taken and the winning clause's outcome
/// closure, built over the arguments its projector reads out of the gifted
/// roots, becomes the task's runnable.
/// The delivery lock is held from the first entry taken to the park taken.
/// The compiled paths (JIT and AOT) call this as the first act of a dispatch.
pub fn deliver_in_queue(task: &mut Process) {
    let mut delivery = task.delivery.lock();
    let Some((clause_idx, roots)) = drain_in_queue(&mut delivery, &mut task.heap, &mut task.mailbox) else {
        return;
    };
    let park = delivery.take_park().expect("a matched receive is still parked");
    drop(delivery);
    let cont = park.outcome_closure(task, clause_idx, &roots);
    task.set_runnable_closure(cont);
}

/// A process sending to itself copies the message into a gift, as a send to
/// another process does, and the gift waits in its own mailbox until a receive
/// takes it. The sender is running, so it cannot be parked, and the mailbox
/// push is the whole delivery. It does not go through the in-queue: a receive
/// reads only the mailbox (`reach_receive`, the interpreter's receive), and
/// the in-queue is drained only at the start of a dispatch, so a queued
/// self-send would be invisible to a receive in the same dispatch. The
/// in-queue is empty while the process runs, so the push also keeps the
/// message after every message other senders queued earlier.
pub fn self_send(task: &mut Process, msg: AnyValueRef) {
    assert!(
        task.delivery.lock().park().is_none(),
        "a running process has no parked receive"
    );
    let (segment, copy) = gift_copy_one(&mut task.heap, msg);
    task.mailbox.push(copy, segment);
}

/// What reaching a `receive` does to the running process.
#[derive(Debug, PartialEq, Eq)]
pub enum ReceiveStep {
    /// The receive is decided: run this closure now (the matched clause's
    /// outcome closure, or the `after` body). The process keeps running.
    Continue(AnyValueRef),
    /// Nothing matched and the receive must wait. The park is recorded, the
    /// after-timer (if any) is armed and the process is Blocked.
    Parked,
}

/// A receive, decided where it is reached. Walks the mailbox oldest first
/// trying the matcher on each message:
/// - Hit: splice the message out (the rest keep their order) and continue
///   with the clause's outcome closure.
/// - Miss with `after 0`: continue with the `after` body.
/// - Miss otherwise: record `park`, arm the after-timer for a positive
///   `after`, and Block. The mailbox is left intact (save-queue rule).
///
/// The delivery lock is held across the walk and the install. A send that
/// arrived after the walk passed a message but before the park existed would
/// find no park to probe and be probed by nobody; under the lock it waits
/// for the install and is then probed against the park. A process with a park
/// has therefore always searched its whole mailbox, so a sender only has to
/// test its own message.
pub fn reach_receive(task: &mut Process, mut park: ParkRecord) -> ReceiveStep {
    let task_ptr: *mut Process = task;
    let mut delivery = task.delivery.lock();
    let mut roots = Roots::new();
    let hit = task
        .mailbox
        .first_match::<_, std::convert::Infallible>(|message| {
            Ok(park
                .try_match(task_ptr, message, &mut roots)
                .map(|(clause_idx, roots)| (clause_idx, roots.len())))
        })
        .unwrap_or_else(|never| match never {})
        .map(|(index, (clause_idx, root_count))| (index, clause_idx, root_count));
    if let Some((i, clause_idx, root_count)) = hit {
        drop(delivery);
        task.mailbox.take(i, &mut task.heap);
        return ReceiveStep::Continue(park.outcome_closure(task, clause_idx, &roots[..root_count]));
    }
    match park.after_deadline_ms {
        Some(0) => ReceiveStep::Continue(park.after_closure(&mut task.heap)),
        after_ms => {
            park.after_timer_id = after_ms.and_then(|ms| timer_schedule(task, task.pid, ms));
            delivery.install_park(park);
            drop(delivery);
            task.state = ProcessState::Blocked;
            ReceiveStep::Parked
        }
    }
}

/// After-timer fire. Called by the scheduler's timer drain for each
/// expired entry. If `task` is still parked on a `ReceiveMatched` with
/// that exact `id`, stash the after-cont as the runnable zero-arg closure.
/// The park is taken under the delivery lock, so the timer and a sender's hit
/// cannot both decide the same receive.
///
/// Returns `true` when the after entry fired and the caller makes the task
/// runnable through its scheduling core; `false` for stale entries whose
/// task is no longer parked on this timer (matcher hit got there first, etc.).
pub fn fire_after_timer(task: &mut Process, id: TimerId) -> bool {
    let mut delivery = task.delivery.lock();
    if delivery.park().is_none_or(|park| park.after_timer_id != Some(id)) {
        return false;
    }
    let park = delivery.take_park().expect("checked above");
    drop(delivery);
    let after = park.after_closure(&mut task.heap);
    task.set_runnable_closure(after);
    true
}

#[cfg(test)]
#[path = "sched_test.rs"]
mod sched_test;
