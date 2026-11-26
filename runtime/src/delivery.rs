//! The state a send and a receive contest, behind one borrow.
//!
//! A process that reaches `receive` and a process that sends to it meet in
//! three places: the park record (the receive waiting for a match), the
//! in-queue (storage other processes allocated for this one) and the walk of
//! the mailbox that decides whether the receive has to park at all. They are
//! one critical section's worth of state, so they live in one struct inside
//! one `RefCell` and are reachable only through its borrow.
//!
//! A scheduler runs on one OS thread (`src/exec/runtime.rs`), and a process
//! belongs to one scheduler, so a send and a receive never overlap in time:
//! the borrow marks the section that must not be re-entered, and a nested
//! borrow panics instead of waiting. The process holds no allocation for it.
//!
//! The mailbox stays outside the cell: only the owning process touches it,
//! and only after a drain.

use crate::park::ParkRecord;
use crate::sched::{Gift, GiftPayload};
use std::cell::{Ref, RefCell, RefMut};
use std::collections::VecDeque;

/// The park record and the in-queue of one process.
#[derive(Default)]
pub struct Delivery {
    /// The process is blocked in selective `receive`. The record stays until
    /// the scheduler delivers the match a sender queued, or the after-timer
    /// fires; whoever takes it decides the receive.
    park: Option<ParkRecord>,
    /// Gifts in arrival order. At most one is a match for the parked receive.
    in_queue: VecDeque<Gift>,
}

impl Delivery {
    pub fn park(&self) -> Option<&ParkRecord> {
        self.park.as_ref()
    }

    pub fn park_mut(&mut self) -> Option<&mut ParkRecord> {
        self.park.as_mut()
    }

    pub fn install_park(&mut self, park: ParkRecord) {
        assert!(self.park.is_none(), "a process parks in one receive at a time");
        self.park = Some(park);
    }

    pub fn take_park(&mut self) -> Option<ParkRecord> {
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

    /// Forget the park record and give back every queued gift, keeping the
    /// queue's storage.
    pub fn clear(&mut self) {
        self.park = None;
        self.in_queue.clear();
    }

    pub fn queued_gifts(&self) -> impl Iterator<Item = &Gift> {
        self.in_queue.iter()
    }
}

/// A `Delivery` that can be reached only through a borrow.
///
/// The cell is a `RefCell`: it allocates nothing and costs a flag test per
/// borrow. A nested conflicting borrow panics.
#[derive(Default)]
pub struct DeliveryCell {
    inner: RefCell<Delivery>,
}

impl DeliveryCell {
    pub fn borrow(&self) -> Ref<'_, Delivery> {
        self.inner.borrow()
    }

    pub fn borrow_mut(&self) -> RefMut<'_, Delivery> {
        self.inner.borrow_mut()
    }

    /// The delivery state through exclusive access: no borrow can be live.
    pub fn get_mut(&mut self) -> &mut Delivery {
        self.inner.get_mut()
    }

    /// The mutable borrow if nobody holds a borrow right now.
    #[cfg(test)]
    pub fn try_borrow_mut(&self) -> Option<RefMut<'_, Delivery>> {
        self.inner.try_borrow_mut().ok()
    }
}
