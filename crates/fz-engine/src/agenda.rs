use crate::fast_hash::HashSet;
use std::collections::VecDeque;
use std::hash::Hash;

#[derive(Debug)]
pub struct Agenda<J> {
    queue: VecDeque<J>,
    queued: HashSet<J>,
}

impl<J> Default for Agenda<J> {
    fn default() -> Self {
        Self {
            queue: VecDeque::new(),
            queued: HashSet::default(),
        }
    }
}

impl<J> Agenda<J>
where
    J: Clone + Eq + Hash,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn enqueue(&mut self, job: J) -> bool {
        if !self.queued.insert(job.clone()) {
            return false;
        }
        self.queue.push_back(job);
        true
    }

    pub fn pop(&mut self) -> Option<J> {
        let job = self.take()?;
        self.queued.remove(&job);
        Some(job)
    }

    #[cfg(not(feature = "pop_order"))]
    fn take(&mut self) -> Option<J> {
        self.queue.pop_front()
    }

    #[cfg(feature = "pop_order")]
    fn take(&mut self) -> Option<J> {
        match pop_order::current() {
            pop_order::PopOrder::Fifo => self.queue.pop_front(),
            pop_order::PopOrder::Lifo => self.queue.pop_back(),
        }
    }

    pub fn contains(&self, job: &J) -> bool {
        self.queued.contains(job)
    }

    pub fn len(&self) -> usize {
        self.queue.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Which end of the queue `pop` takes, selectable per thread. Compiled only
/// for test builds (the `pop_order` feature is enabled by the root crate's
/// dev-dependency), so a test can prove a result does not depend on the
/// order jobs run in by running the real drive under both.
#[cfg(feature = "pop_order")]
pub mod pop_order {
    use std::cell::Cell;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum PopOrder {
        Fifo,
        Lifo,
    }

    thread_local! {
        static CURRENT: Cell<PopOrder> = const { Cell::new(PopOrder::Fifo) };
    }

    pub(crate) fn current() -> PopOrder {
        CURRENT.with(Cell::get)
    }

    /// Runs `body` with this thread's agendas popping in `order`.
    pub fn with<R>(order: PopOrder, body: impl FnOnce() -> R) -> R {
        struct Restore(PopOrder);
        impl Drop for Restore {
            fn drop(&mut self) {
                CURRENT.with(|current| current.set(self.0));
            }
        }
        let _restore = Restore(CURRENT.with(|current| current.replace(order)));
        body()
    }
}

#[cfg(test)]
#[path = "agenda_test.rs"]
mod agenda_test;
