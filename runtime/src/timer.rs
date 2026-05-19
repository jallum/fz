//! fz-sum — minimal scheduler timer.
//!
//! A sorted-vector wheel sufficient for v1 single-worker scheduling. Each
//! entry pairs a deadline with the PID that should be woken when the
//! deadline expires. The dispatcher (B2: `dispatch_send` / scheduler tick)
//! drains expired entries and routes them to the parked process's
//! after-continuation; F2 only owns the data structure and its tests.
//!
//! v1 is single-worker (src/runtime.rs:43-54), so no synchronization is
//! used. Multi-worker will need an Arc<Mutex<TimerWheel>> or a per-worker
//! shard — orthogonal to the per-receive semantics this wheel exists to
//! support.

use crate::process::PidId;
use std::time::{Duration, Instant};

pub type TimerId = u64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TimerEntry {
    pub id: TimerId,
    pub deadline: Instant,
    pub pid: PidId,
}

/// Sorted-vector timer wheel. Insertion is O(n) (linear probe + insert);
/// drain is O(k) where k is the number of expired entries. Adequate for
/// v1 receive-after counts in the low tens per process; replace with a
/// real wheel or binary heap if benchmarks demand.
pub struct TimerWheel {
    entries: Vec<TimerEntry>, // ascending by deadline; ties broken by id
    next_id: TimerId,
}

impl Default for TimerWheel {
    fn default() -> Self {
        Self::new()
    }
}

impl TimerWheel {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            next_id: 1,
        }
    }

    /// Schedule a wake-up for `pid` after `after` elapses. Returns the
    /// fresh TimerId; the caller must hold onto it for cancellation.
    pub fn schedule(&mut self, pid: PidId, after: Duration) -> TimerId {
        let id = self.next_id;
        self.next_id += 1;
        let entry = TimerEntry {
            id,
            deadline: Instant::now() + after,
            pid,
        };
        let pos = self
            .entries
            .binary_search_by(|e| e.deadline.cmp(&entry.deadline).then(e.id.cmp(&entry.id)))
            .unwrap_or_else(|i| i);
        self.entries.insert(pos, entry);
        id
    }

    /// Cancel a previously scheduled timer. No-op if `id` is unknown
    /// (already fired, already cancelled, or never existed). The pattern
    /// matches BEAM's `erlang:cancel_timer/1` for an absent id; callers
    /// should not need to distinguish.
    pub fn cancel(&mut self, id: TimerId) {
        if let Some(pos) = self.entries.iter().position(|e| e.id == id) {
            self.entries.remove(pos);
        }
    }

    /// Drain every entry whose deadline is at or before `now` in
    /// ascending deadline order. The scheduler calls this on each tick
    /// and routes each entry to the matching parked process.
    pub fn drain_expired(&mut self, now: Instant) -> Vec<TimerEntry> {
        let cut = self
            .entries
            .iter()
            .position(|e| e.deadline > now)
            .unwrap_or(self.entries.len());
        self.entries.drain(..cut).collect()
    }

    /// Earliest pending deadline, if any. Scheduler uses this to decide
    /// how long to sleep between ticks when no run-queue work is ready.
    pub fn next_deadline(&self) -> Option<Instant> {
        self.entries.first().map(|e| e.deadline)
    }

    /// Test-only hook: number of pending entries.
    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.entries.len()
    }
}

#[cfg(test)]
mod tests {
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
}
