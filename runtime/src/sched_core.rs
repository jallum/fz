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
//! runnable and no timer is pending.

use crate::process::{PidId, ProcessState};
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
