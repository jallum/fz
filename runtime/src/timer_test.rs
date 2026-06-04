use super::*;
use std::thread::sleep;

fn ms(n: u64) -> Duration {
    Duration::from_millis(n)
}

#[test]
fn new_is_empty() {
    let mut w = TimerWheel::new();
    assert_eq!(w.len(), 0);
    assert!(w.next_deadline().is_none());
    assert!(w.drain_expired(Instant::now()).is_empty());
}

#[test]
fn schedule_returns_monotonic_ids() {
    let mut w = TimerWheel::new();
    let a = w.schedule(1, ms(10));
    let b = w.schedule(2, ms(20));
    let c = w.schedule(3, ms(30));
    assert!(a < b && b < c);
}

#[test]
fn drain_at_now_returns_nothing_when_all_future() {
    let mut w = TimerWheel::new();
    w.schedule(1, ms(50));
    let drained = w.drain_expired(Instant::now());
    assert!(drained.is_empty());
    assert_eq!(w.len(), 1);
}

#[test]
fn drain_past_all_returns_all_in_deadline_order() {
    let mut w = TimerWheel::new();
    // Schedule out of order; wheel sorts by deadline.
    let id_b = w.schedule(2, ms(20));
    let id_a = w.schedule(1, ms(10));
    let id_c = w.schedule(3, ms(30));
    sleep(ms(50));
    let drained = w.drain_expired(Instant::now());
    let ids: Vec<TimerId> = drained.iter().map(|e| e.id).collect();
    assert_eq!(ids, vec![id_a, id_b, id_c]);
    assert_eq!(w.len(), 0);
}

#[test]
fn drain_takes_only_expired() {
    let mut w = TimerWheel::new();
    let near = w.schedule(1, ms(10));
    let _far = w.schedule(2, ms(500));
    sleep(ms(30));
    let drained = w.drain_expired(Instant::now());
    assert_eq!(drained.len(), 1);
    assert_eq!(drained[0].id, near);
    assert_eq!(w.len(), 1);
}

#[test]
fn cancel_removes_entry() {
    let mut w = TimerWheel::new();
    let id = w.schedule(1, ms(100));
    assert_eq!(w.len(), 1);
    w.cancel(id);
    assert_eq!(w.len(), 0);
}

#[test]
fn cancel_unknown_id_is_noop() {
    let mut w = TimerWheel::new();
    let id = w.schedule(1, ms(100));
    w.cancel(9999);
    assert_eq!(w.len(), 1);
    w.cancel(id);
    w.cancel(id); // double-cancel of same id also no-op
    assert_eq!(w.len(), 0);
}

#[test]
fn next_deadline_tracks_earliest() {
    let mut w = TimerWheel::new();
    assert!(w.next_deadline().is_none());
    let _b = w.schedule(2, ms(200));
    let early = w.next_deadline().unwrap();
    let _a = w.schedule(1, ms(50));
    let earlier = w.next_deadline().unwrap();
    assert!(earlier < early);
}

#[test]
fn cancel_preserves_order_of_remaining_entries() {
    let mut w = TimerWheel::new();
    let _a = w.schedule(1, ms(10));
    let mid = w.schedule(2, ms(50));
    let _c = w.schedule(3, ms(100));
    w.cancel(mid);
    sleep(ms(120));
    let drained = w.drain_expired(Instant::now());
    let pids: Vec<PidId> = drained.iter().map(|e| e.pid).collect();
    assert_eq!(pids, vec![1, 3]);
}
