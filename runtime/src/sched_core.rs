//! The scheduling core: the run queue, the timer wheel, and the one loop that
//! decides when a program is idle.
//!
//! The JIT `Runtime`, the AOT `AotScheduler`, and the interpreter's scheduler
//! adapter each own a [`SchedulingCore`] and implement [`Scheduler`] to say how
//! an expired timer wakes their process. [`SchedulingCore::make_runnable`] is
//! the one place a process becomes Ready: it writes the state and queues the
//! pid together, so a process is in the run queue exactly when it is Ready.
//! [`next_runnable`] is the single place that answers "what runs next?": it
//! wakes expired timers, hands out the next runnable process, sleeps until the
//! next deadline when only timers remain, and reports idle only when nothing is
//! runnable and no timer is pending. [`end_quantum`] is the single place that
//! answers "what happens to a process after its quantum?": it collects when
//! the heap is due, runs the destructors of the resources that collection or
//! the exit freed, and says whether the process is requeued, parked or gone.

use crate::any_value::{AnyValueRef, ValueKind};
use crate::heap::GcStats;
use crate::process::{Collection, GcBoundary, PidId, Process, ProcessState};
use crate::scheduler_hooks::{TimerCancelHook, TimerScheduleHook};
use crate::timer::{TimerId, TimerWheel};
use std::collections::VecDeque;
use std::thread::sleep;
use std::time::{Duration, Instant};

/// The run queue and the timer wheel of one scheduler.
#[derive(Default)]
pub struct SchedulingCore {
    run_queue: VecDeque<PidId>,
    timers: TimerWheel,
}

impl SchedulingCore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Make `pid` runnable and record that in `state`. A process that is New,
    /// Running (it yielded) or Blocked becomes Ready and is queued behind every
    /// process already runnable. A process that is already Ready sits in the
    /// queue and is not queued twice; an Exited process never runs again.
    /// Returns whether this call is the one that made the process runnable.
    pub fn make_runnable(&mut self, pid: PidId, state: &mut ProcessState) -> bool {
        match *state {
            ProcessState::New | ProcessState::Running | ProcessState::Blocked => {
                *state = ProcessState::Ready;
                self.run_queue.push_back(pid);
                true
            }
            ProcessState::Ready | ProcessState::Exited => false,
        }
    }

    /// The runnable processes in the order they will run.
    pub fn queued(&self) -> &VecDeque<PidId> {
        &self.run_queue
    }

    /// Schedule a wake-up for `pid` after `after`. The returned id cancels it.
    pub fn schedule_timer(&mut self, pid: PidId, after: Duration) -> TimerId {
        self.timers.schedule(pid, after)
    }

    /// Cancel a timer. No-op when it already fired or never existed.
    pub fn cancel_timer(&mut self, id: TimerId) {
        self.timers.cancel(id);
    }

    /// The earliest pending timer deadline.
    pub fn next_deadline(&self) -> Option<Instant> {
        self.timers.next_deadline()
    }
}

/// What a scheduler contributes to the shared loop.
pub trait Scheduler {
    fn core(&mut self) -> &mut SchedulingCore;

    /// The timer `timer` that `pid` was waiting on has expired. A scheduler
    /// whose process is still waiting on that timer makes it runnable through
    /// its core; a stale timer, whose process a message already woke, is
    /// dropped.
    fn wake_expired(&mut self, pid: PidId, timer: TimerId);

    /// The core is about to sleep for `wait` because only timers remain.
    fn about_to_sleep(&mut self, _wait: Duration) {}

    /// Run the destructor closure `closure` of a freed resource on `process`
    /// with the boxed `payload`, both value-ref words. Only a driver can run
    /// fz code: compiled drivers enter the drain shim through the pinned
    /// register, the interpreter interprets the closure. The call returns when
    /// the destructor has finished.
    fn run_destructor(&mut self, process: &mut Process, closure: u64, payload: u64);

    /// Collect `process`'s heap. A driver that holds heap values of `process`
    /// outside it, across the boundary, gathers them as the `transient` roots
    /// of [`Process::collect`] and writes the forwarded values back. The
    /// default holds none.
    fn collect_heap(&mut self, process: &mut Process) -> GcStats {
        process.collect(&mut [])
    }
}

/// What a scheduler does with a process whose quantum has ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Disposition {
    /// The process yielded and is still runnable: queue it behind the others.
    Requeue,
    /// The process parked on a receive that found nothing: a send or its
    /// after-timer wakes it.
    Parked,
    /// The process halted; its heap and its resources are released.
    Exited,
}

/// The outcome of [`end_quantum`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QuantumEnd {
    pub disposition: Disposition,
    /// The collection the boundary performed, if the heap was due.
    pub collection: Option<Collection>,
}

/// The step after every quantum, for every state. It reads the boundary off
/// `process`, collects when the heap is due, and clears the quantum's yield
/// reasons. A halted process is marked Exited and releases every stub on its
/// MSO chain, since nothing is live. Every destructor the collection or the
/// exit queued then runs through `scheduler`, and `process.dtors_dispatched`
/// counts them.
pub fn end_quantum<S: Scheduler + ?Sized>(scheduler: &mut S, process: &mut Process) -> QuantumEnd {
    let boundary = process.quantum_boundary();
    let collection = process.needs_boundary_gc().then(|| Collection {
        pid: process.pid,
        boundary,
        stats: scheduler.collect_heap(process),
    });
    process.clear_yield_reasons();
    let disposition = match boundary {
        GcBoundary::Yield => Disposition::Requeue,
        GcBoundary::Park => Disposition::Parked,
        GcBoundary::Exit => {
            process.state = ProcessState::Exited;
            process.heap.release_resources_at_exit();
            Disposition::Exited
        }
    };
    drain_destructors(scheduler, process);
    QuantumEnd {
        disposition,
        collection,
    }
}

/// Run every queued destructor on `process`, oldest first. A destructor runs
/// to completion with a full reduction budget; one that yielded would
/// overwrite the process's own continuation, so that is a fault.
pub fn drain_destructors<S: Scheduler + ?Sized>(scheduler: &mut S, process: &mut Process) {
    while let Some((closure, payload)) = process.heap.pending_dtors.pop_front() {
        let payload_tag = AnyValueRef::from_raw_word(payload)
            .expect("a queued destructor payload is a valid value ref")
            .tag();
        assert_eq!(
            payload_tag,
            ValueKind::INT,
            "a queued destructor payload stays boxed as an integer"
        );
        let continuation = process.runnable_closure();
        process.reset_reduction_budget();
        scheduler.run_destructor(process, closure, payload);
        process.dtors_dispatched += 1;
        assert_eq!(
            process.runnable_closure(),
            continuation,
            "a destructor must finish within one quantum; it yielded"
        );
    }
}

/// The next process to run, or `None` when the scheduler is idle: nothing is
/// runnable and no timer is pending.
pub fn next_runnable<S: Scheduler + ?Sized>(scheduler: &mut S) -> Option<PidId> {
    loop {
        let expired = scheduler.core().timers.drain_expired(Instant::now());
        for entry in expired {
            scheduler.wake_expired(entry.pid, entry.id);
        }
        if let Some(pid) = scheduler.core().run_queue.pop_front() {
            return Some(pid);
        }
        let deadline = scheduler.core().timers.next_deadline()?;
        let wait = deadline.saturating_duration_since(Instant::now());
        scheduler.about_to_sleep(wait);
        sleep(wait);
    }
}

/// The `ExecCtx::timer_schedule` hook of scheduler type `S`. The context's
/// erased scheduler handle must point at an `S`.
pub fn timer_schedule_hook<S: Scheduler>() -> TimerScheduleHook {
    schedule_timer_on::<S>
}

/// The `ExecCtx::timer_cancel` hook of scheduler type `S`. The context's
/// erased scheduler handle must point at an `S`, or be null.
pub fn timer_cancel_hook<S: Scheduler>() -> TimerCancelHook {
    cancel_timer_on::<S>
}

extern "C" fn schedule_timer_on<S: Scheduler>(scheduler: *mut (), pid: u32, after_ms: u64) -> u64 {
    let scheduler = unsafe { &mut *(scheduler as *mut S) };
    scheduler.core().schedule_timer(pid, Duration::from_millis(after_ms))
}

extern "C" fn cancel_timer_on<S: Scheduler>(scheduler: *mut (), timer_id: u64) {
    if scheduler.is_null() {
        return;
    }
    let scheduler = unsafe { &mut *(scheduler as *mut S) };
    scheduler.core().cancel_timer(timer_id);
}

#[cfg(test)]
#[path = "sched_core_test.rs"]
mod sched_core_test;
