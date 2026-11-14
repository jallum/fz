use super::*;
use std::time::Duration;

fn ms(n: u64) -> Duration {
    Duration::from_millis(n)
}

/// A wheel and the instant its deadlines are measured from. Tests choose the
/// `now` they drain at, so no test waits for a deadline to pass.
fn wheel_at_origin() -> (TimerWheel, Instant) {
    (TimerWheel::new(), Instant::now())
}

#[test]
fn new_is_empty() {
    let (mut w, origin) = wheel_at_origin();
    assert_eq!(w.len(), 0);
    assert!(w.next_deadline().is_none());
    assert!(w.drain_expired(origin).is_empty());
}

#[test]
fn schedule_returns_monotonic_ids() {
    let (mut w, origin) = wheel_at_origin();
    let a = w.schedule(1, origin + ms(10)).id;
    let b = w.schedule(2, origin + ms(20)).id;
    let c = w.schedule(3, origin + ms(30)).id;
    assert!(a < b && b < c);
}

#[test]
fn drain_before_every_deadline_returns_nothing() {
    let (mut w, origin) = wheel_at_origin();
    w.schedule(1, origin + ms(50));
    let drained = w.drain_expired(origin + ms(49));
    assert!(drained.is_empty());
    assert_eq!(w.len(), 1);
}

#[test]
fn drain_past_all_returns_all_in_deadline_order() {
    let (mut w, origin) = wheel_at_origin();
    // Schedule out of order; wheel sorts by deadline.
    let id_b = w.schedule(2, origin + ms(20)).id;
    let id_a = w.schedule(1, origin + ms(10)).id;
    let id_c = w.schedule(3, origin + ms(30)).id;
    let drained = w.drain_expired(origin + ms(50));
    let ids: Vec<TimerId> = drained.iter().map(|e| e.id).collect();
    assert_eq!(ids, vec![id_a, id_b, id_c]);
    assert_eq!(w.len(), 0);
}

#[test]
fn drain_takes_only_expired() {
    let (mut w, origin) = wheel_at_origin();
    let near = w.schedule(1, origin + ms(10)).id;
    let _far = w.schedule(2, origin + ms(500));
    let drained = w.drain_expired(origin + ms(30));
    assert_eq!(drained.len(), 1);
    assert_eq!(drained[0].id, near);
    assert_eq!(w.len(), 1);
}

#[test]
fn a_deadline_is_expired_at_exactly_now() {
    let (mut w, origin) = wheel_at_origin();
    w.schedule(1, origin + ms(10));
    assert_eq!(w.drain_expired(origin + ms(10)).len(), 1);
}

#[test]
fn cancel_removes_entry_and_returns_it() {
    let (mut w, origin) = wheel_at_origin();
    let armed = w.schedule(1, origin + ms(100));
    assert_eq!(w.len(), 1);
    assert_eq!(w.cancel(armed.id), Some(armed));
    assert_eq!(w.len(), 0);
}

#[test]
fn cancel_unknown_id_is_noop() {
    let (mut w, origin) = wheel_at_origin();
    let id = w.schedule(1, origin + ms(100)).id;
    assert_eq!(w.cancel(9999), None);
    assert_eq!(w.len(), 1);
    assert!(w.cancel(id).is_some());
    assert_eq!(w.cancel(id), None, "double-cancel of the same id is a no-op");
    assert_eq!(w.len(), 0);
}

#[test]
fn next_deadline_tracks_earliest() {
    let (mut w, origin) = wheel_at_origin();
    assert!(w.next_deadline().is_none());
    let _b = w.schedule(2, origin + ms(200));
    let early = w.next_deadline().unwrap();
    let _a = w.schedule(1, origin + ms(50));
    let earlier = w.next_deadline().unwrap();
    assert!(earlier < early);
}

#[test]
fn cancel_preserves_order_of_remaining_entries() {
    let (mut w, origin) = wheel_at_origin();
    let _a = w.schedule(1, origin + ms(10));
    let mid = w.schedule(2, origin + ms(50)).id;
    let _c = w.schedule(3, origin + ms(100));
    w.cancel(mid);
    let drained = w.drain_expired(origin + ms(120));
    let pids: Vec<PidId> = drained.iter().map(|e| e.pid).collect();
    assert_eq!(pids, vec![1, 3]);
}
