use super::*;

/// A scheduler whose only behaviour is to record what the shared loop asks of it.
struct Recording {
    core: SchedulingCore,
    wakes_process: bool,
    woken: Vec<(PidId, TimerId)>,
    slept: Vec<Duration>,
}

impl Recording {
    fn new() -> Self {
        Self {
            core: SchedulingCore::new(),
            wakes_process: true,
            woken: Vec::new(),
            slept: Vec::new(),
        }
    }
}

impl Scheduler for Recording {
    fn core(&mut self) -> &mut SchedulingCore {
        &mut self.core
    }

    fn wake_expired(&mut self, pid: PidId, timer: TimerId) -> bool {
        self.woken.push((pid, timer));
        self.wakes_process
    }

    fn about_to_sleep(&mut self, wait: Duration) {
        self.slept.push(wait);
    }
}

fn ms(n: u64) -> Duration {
    Duration::from_millis(n)
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
    s.core.enqueue(3);
    s.core.enqueue(1);
    s.core.enqueue(2);
    assert_eq!(next_runnable(&mut s), Some(3));
    assert_eq!(next_runnable(&mut s), Some(1));
    assert_eq!(next_runnable(&mut s), Some(2));
    assert_eq!(next_runnable(&mut s), None);
    assert!(s.slept.is_empty(), "a runnable queue never sleeps");
}

#[test]
fn a_pending_timer_keeps_the_core_from_idling_until_it_fires() {
    let mut s = Recording::new();
    let timer = s.core.schedule_timer(7, ms(20));
    let started = Instant::now();

    assert_eq!(
        next_runnable(&mut s),
        Some(7),
        "the timer's process runs once it expires"
    );

    assert!(started.elapsed() >= ms(20), "the core slept out the whole deadline");
    assert_eq!(s.woken, vec![(7, timer)]);
    assert_eq!(s.slept.len(), 1, "one sleep is reported for one timer wait");
    assert!(s.slept[0] <= ms(20) && s.slept[0] > Duration::ZERO);
    assert_eq!(next_runnable(&mut s), None, "idle once the timer is spent");
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
    s.core.enqueue(1);

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
