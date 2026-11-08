//! The state a send and a receive contest, behind one lock.
//!
//! A process that reaches `receive` and a process that sends to it meet in
//! three places: the park record (the receive waiting for a match), the
//! in-queue (storage other processes allocated for this one) and the walk of
//! the mailbox that decides whether the receive has to park at all. They are
//! one critical section's worth of state, so they live in one struct behind
//! one mutex and are reachable only through its guard.
//!
//! The mailbox stays outside the lock: only the owning process touches it,
//! and only after a drain.

use crate::park::ParkRecord;
use crate::sched::{Gift, GiftPayload};
use std::collections::VecDeque;
use std::sync::{Mutex, MutexGuard};

/// The park record and the in-queue of one process.
#[derive(Default)]
pub struct Delivery {
    /// The process is blocked in selective `receive`. The record stays until
    /// the scheduler delivers the match a sender queued, or the after-timer
    /// fires; whoever takes it decides the receive.
    park: Option<Box<ParkRecord>>,
    /// Gifts in arrival order. At most one is a match for the parked receive.
    in_queue: VecDeque<Gift>,
}

impl Delivery {
    pub fn park(&self) -> Option<&ParkRecord> {
        self.park.as_deref()
    }

    pub fn park_mut(&mut self) -> Option<&mut ParkRecord> {
        self.park.as_deref_mut()
    }

    pub fn install_park(&mut self, park: ParkRecord) {
        assert!(self.park.is_none(), "a process parks in one receive at a time");
        self.park = Some(Box::new(park));
    }

    pub fn take_park(&mut self) -> Option<Box<ParkRecord>> {
        self.park.take()
    }

    /// The park a sender may still probe: a receive is decided once, so a
    /// park whose match is already queued is no longer probed.
    pub fn undecided_park(&self) -> Option<&ParkRecord> {
        self.park().filter(|_| !self.has_pending_match())
    }

    /// Has a sender already matched the parked receive? The match waits in
    /// the in-queue for the next dispatch.
    pub fn has_pending_match(&self) -> bool {
        self.in_queue
            .iter()
            .any(|gift| matches!(gift.payload, GiftPayload::Match { .. }))
    }

    /// Queue a gift. A parked receive is decided once, so a second match for
    /// the same receive is a scheduler bug.
    pub fn push_gift(&mut self, gift: Gift) {
        if matches!(gift.payload, GiftPayload::Match { .. }) {
            assert!(
                !self.has_pending_match(),
                "a receiver takes one match per parked receive"
            );
        }
        self.in_queue.push_back(gift);
    }

    pub fn pop_gift(&mut self) -> Option<Gift> {
        self.in_queue.pop_front()
    }

    pub fn queued_gifts(&self) -> impl Iterator<Item = &Gift> {
        self.in_queue.iter()
    }
}

/// A `Delivery` that can be reached only by holding its lock.
#[derive(Default)]
pub struct DeliveryLock {
    inner: Mutex<Delivery>,
}

impl DeliveryLock {
    pub fn lock(&self) -> MutexGuard<'_, Delivery> {
        self.inner
            .lock()
            .expect("a panic while holding the delivery lock poisons it")
    }

    /// The guard if nobody holds the lock right now.
    #[cfg(test)]
    pub fn try_lock(&self) -> Option<MutexGuard<'_, Delivery>> {
        use std::sync::TryLockError;
        match self.inner.try_lock() {
            Ok(guard) => Some(guard),
            Err(TryLockError::WouldBlock) => None,
            Err(TryLockError::Poisoned(_)) => panic!("the delivery lock is poisoned"),
        }
    }
}
