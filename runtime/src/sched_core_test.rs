use super::*;
use crate::process::ProcessState;
use std::collections::HashMap;

/// A scheduler whose only behaviour is to record what the shared loop asks of
/// it. It keeps a state word per pid so the core has something to transition.
struct Recording {
    core: SchedulingCore,
    states: HashMap<PidId, ProcessState>,
    wakes_process: bool,
    woken: Vec<(PidId, TimerId)>,
    slept: Vec<Duration>,
}

impl Recording {
    fn new() -> Self {
        Self {
            core: SchedulingCore::new(),
            states: HashMap::new(),
            wakes_process: true,
            woken: Vec::new(),
            slept: Vec::new(),
        }
    }

    /// Ask the core to make `pid` runnable from whatever state it last had; a
    /// pid never seen before starts out New.
    fn make_runnable(&mut self, pid: PidId) -> bool {
        let state = self.states.entry(pid).or_insert(ProcessState::New);
        self.core.make_runnable(pid, state)
    }

    fn state(&self, pid: PidId) -> ProcessState {
        self.states[&pid]
    }
}

impl Scheduler for Recording {
    fn core(&mut self) -> &mut SchedulingCore {
        &mut self.core
    }

    fn wake_expired(&mut self, pid: PidId, timer: TimerId) {
        self.woken.push((pid, timer));
        if self.wakes_process {
            self.make_runnable(pid);
        }
    }

    fn about_to_sleep(&mut self, wait: Duration) {
        self.slept.push(wait);
    }
}

fn ms(n: u64) -> Duration {
    Duration::from_millis(n)
}

fn queued(s: &Recording) -> Vec<PidId> {
    s.core.queued().iter().copied().collect()
}

#[test]
fn a_blocked_process_woken_once_is_queued_once_and_marked_ready() {
    let mut s = Recording::new();
    s.states.insert(7, ProcessState::Blocked);

    assert!(s.make_runnable(7), "this wake is the one that made it runnable");
    assert_eq!(s.state(7), ProcessState::Ready);
    assert_eq!(queued(&s), vec![7]);
}

#[test]
fn a_second_wake_of_a_ready_process_does_not_queue_it_again() {
    let mut s = Recording::new();
    s.states.insert(7, ProcessState::Blocked);
    assert!(s.make_runnable(7));

    assert!(!s.make_runnable(7), "already queued: nothing newly runnable");
    assert_eq!(queued(&s), vec![7]);
    assert_eq!(next_runnable(&mut s), Some(7));
    assert_eq!(next_runnable(&mut s), None, "two wakes, one run");
}

#[test]
fn repeated_wakes_leave_the_queue_order_unchanged() {
    let mut s = Recording::new();
    for pid in [3, 1, 2] {
        s.states.insert(pid, ProcessState::Blocked);
    }

    s.make_runnable(3);
    s.make_runnable(1);
    s.make_runnable(3);
    s.make_runnable(2);
    s.make_runnable(1);

    assert_eq!(queued(&s), vec![3, 1, 2]);
}

#[test]
fn a_new_process_is_queued_by_its_first_wake() {
    let mut s = Recording::new();
    s.states.insert(4, ProcessState::New);

    assert!(s.make_runnable(4));
    assert_eq!(s.state(4), ProcessState::Ready);
    assert_eq!(queued(&s), vec![4]);
}

#[test]
fn a_running_process_that_yields_is_queued_behind_the_others() {
    let mut s = Recording::new();
    s.states.insert(1, ProcessState::Running);
    s.states.insert(2, ProcessState::Blocked);
    s.make_runnable(2);

    assert!(s.make_runnable(1));
    assert_eq!(s.state(1), ProcessState::Ready);
    assert_eq!(queued(&s), vec![2, 1]);
}

#[test]
fn an_exited_process_is_never_queued() {
    let mut s = Recording::new();
    s.states.insert(9, ProcessState::Exited);

    assert!(!s.make_runnable(9));
    assert_eq!(s.state(9), ProcessState::Exited);
    assert!(queued(&s).is_empty());
}

#[test]
fn an_empty_core_is_idle_without_sleeping() {
    let mut s = Recording::new();
    assert_eq!(next_runnable(&mut s), None);
    assert!(s.slept.is_empty());
}

#[test]
fn runnable_processes_come_out_in_queue_order_and_then_idle() {
    let mut s = Recording::new();
    s.make_runnable(3);
    s.make_runnable(1);
    s.make_runnable(2);
    assert_eq!(next_runnable(&mut s), Some(3));
    assert_eq!(next_runnable(&mut s), Some(1));
    assert_eq!(next_runnable(&mut s), Some(2));
    assert_eq!(next_runnable(&mut s), None);
    assert!(s.slept.is_empty(), "a runnable queue never sleeps");
}

#[test]
fn a_pending_timer_keeps_the_core_from_idling_until_it_fires() {
    let mut s = Recording::new();
    s.states.insert(7, ProcessState::Blocked);
    let timer = s.core.schedule_timer(7, ms(20));
    let started = Instant::now();

    assert_eq!(
        next_runnable(&mut s),
        Some(7),
        "the timer's process runs once it expires"
    );

    assert!(started.elapsed() >= ms(20), "the core slept out the whole deadline");
    assert_eq!(s.woken, vec![(7, timer)]);
    assert_eq!(s.state(7), ProcessState::Ready, "the wake went through the core");
    assert_eq!(s.slept.len(), 1, "one sleep is reported for one timer wait");
    assert!(s.slept[0] <= ms(20) && s.slept[0] > Duration::ZERO);
    assert_eq!(next_runnable(&mut s), None, "idle once the timer is spent");
}

#[test]
fn a_timer_firing_for_a_process_a_message_already_queued_does_not_queue_it_twice() {
    let mut s = Recording::new();
    s.states.insert(7, ProcessState::Blocked);
    s.core.schedule_timer(7, ms(5));
    s.make_runnable(7);

    assert_eq!(next_runnable(&mut s), Some(7), "the message's wake runs first");
    assert!(s.slept.is_empty(), "no sleep while something can run");
    assert_eq!(
        next_runnable(&mut s),
        None,
        "the late timer finds it Ready and queues nothing"
    );
    assert_eq!(s.woken.len(), 1, "the timer still expired and was offered");
}

#[test]
fn a_cancelled_timer_does_not_hold_the_core_open() {
    let mut s = Recording::new();
    let timer = s.core.schedule_timer(7, ms(10_000));
    s.core.cancel_timer(timer);

    assert_eq!(next_runnable(&mut s), None);
    assert!(s.slept.is_empty());
    assert!(s.woken.is_empty());
}

#[test]
fn a_timer_whose_process_is_already_awake_is_not_queued() {
    let mut s = Recording::new();
    s.wakes_process = false;
    s.core.schedule_timer(7, ms(5));

    assert_eq!(next_runnable(&mut s), None);
    assert_eq!(s.woken.len(), 1);
    assert_eq!(s.slept.len(), 1, "the stale timer was still waited for, then dropped");
}

#[test]
fn runnable_work_runs_before_a_pending_timer_is_waited_for() {
    let mut s = Recording::new();
    s.core.schedule_timer(9, ms(15));
    s.make_runnable(1);

    assert_eq!(next_runnable(&mut s), Some(1));
    assert!(s.slept.is_empty(), "no sleep while something can run");
    assert_eq!(next_runnable(&mut s), Some(9));
    assert_eq!(s.slept.len(), 1);
}

#[test]
fn staggered_timers_wake_in_deadline_order() {
    let mut s = Recording::new();
    s.core.schedule_timer(1, ms(40));
    s.core.schedule_timer(2, ms(10));

    assert_eq!(next_runnable(&mut s), Some(2));
    assert_eq!(next_runnable(&mut s), Some(1));
    assert_eq!(next_runnable(&mut s), None);
    assert_eq!(s.slept.len(), 2);
}

#[test]
fn the_timer_hooks_schedule_and_cancel_through_the_scheduler_handle() {
    let mut s = Recording::new();
    let handle = &mut s as *mut Recording as *mut ();

    let id = timer_schedule_hook::<Recording>()(handle, 4, 10_000);
    assert!(s.core.next_deadline().is_some());
    timer_cancel_hook::<Recording>()(handle, id);
    assert!(s.core.next_deadline().is_none());
    timer_cancel_hook::<Recording>()(std::ptr::null_mut(), id);
}
