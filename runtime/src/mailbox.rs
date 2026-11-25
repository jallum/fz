//! A process's mailbox: the messages it has received and not yet taken, oldest
//! first.
//!
//! Every message arrives as a gift: a block of its own that no heap owns yet,
//! whether another process sent it or the process sent it to itself. It waits
//! in the mailbox with that block, outside the heap, so the mailbox is never a
//! collection root. The receive that takes a message grafts its block into the
//! receiver's heap, where it is young.

use crate::any_value::Stored;
use crate::heap::{GiftSegment, Heap};
use std::collections::VecDeque;

/// A message and the gift segment that holds it. A message that is a number,
/// an atom or a pid holds nothing in its segment, which is then empty.
struct Waiting {
    message: Stored,
    segment: GiftSegment,
}

#[derive(Default)]
pub struct Mailbox {
    queue: VecDeque<Waiting>,
}

impl Mailbox {
    pub fn len(&self) -> usize {
        self.queue.len()
    }

    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    /// Give back every message's block, keeping the queue's storage.
    pub fn clear(&mut self) {
        self.queue.clear();
    }

    /// Append `message`, which waits in `segment` until a receive takes it.
    pub fn push(&mut self, message: Stored, segment: GiftSegment) {
        self.queue.push_back(Waiting { message, segment });
    }

    /// The messages, oldest first.
    pub fn messages(&self) -> impl Iterator<Item = Stored> + '_ {
        self.queue.iter().map(|waiting| waiting.message)
    }

    /// The oldest message.
    pub fn front(&self) -> Option<Stored> {
        self.queue.front().map(|waiting| waiting.message)
    }

    /// The message at `index`, counting from the oldest.
    pub fn get(&self, index: usize) -> Option<Stored> {
        self.queue.get(index).map(|waiting| waiting.message)
    }

    /// The first message, oldest first, for which `f` answers `Some`, with its
    /// index.
    pub fn first_match<T, E>(
        &self,
        mut f: impl FnMut(Stored) -> Result<Option<T>, E>,
    ) -> Result<Option<(usize, T)>, E> {
        for (index, waiting) in self.queue.iter().enumerate() {
            if let Some(found) = f(waiting.message)? {
                return Ok(Some((index, found)));
            }
        }
        Ok(None)
    }

    /// Remove the message at `index`: its block joins `heap`, young. An empty
    /// segment adds no block.
    pub fn take(&mut self, index: usize, heap: &mut Heap) {
        let waiting = self
            .queue
            .remove(index)
            .expect("a receive takes a message the mailbox holds");
        heap.graft(waiting.segment);
    }
}

#[cfg(test)]
#[path = "mailbox_test.rs"]
mod mailbox_test;
