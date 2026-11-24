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
            pop_order::PopOrder::Seeded(_) => {
                let index = pop_order::next_index(self.queue.len())?;
                self.queue.swap_remove_back(index)
            }
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

/// Which queued job `pop` takes (the oldest, the newest, or a pseudo-random
/// one per seed), selectable per thread. Compiled only for test builds (the
/// `pop_order` feature is enabled by the root crate's dev-dependency), so a
/// test can prove a result does not depend on the order jobs run in by
/// running the real drive under several orders.
#[cfg(feature = "pop_order")]
pub mod pop_order {
    use std::cell::Cell;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum PopOrder {
        Fifo,
        Lifo,
        /// Each pop takes a pseudo-random queued job; the sequence is a
        /// function of the seed alone.
        Seeded(u64),
    }

    thread_local! {
        static CURRENT: Cell<PopOrder> = const { Cell::new(PopOrder::Fifo) };
        static RNG: Cell<u64> = const { Cell::new(1) };
    }

    /// The xorshift64 state a seed starts from: the seed is spread by a
    /// golden-ratio multiply and forced odd, so it is never the zero state.
    fn initial_state(seed: u64) -> u64 {
        seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1
    }

    pub(crate) fn current() -> PopOrder {
        CURRENT.with(Cell::get)
    }

    /// A xorshift64 draw reduced to `0..len`; `None` when `len` is zero.
    pub(crate) fn next_index(len: usize) -> Option<usize> {
        if len == 0 {
            return None;
        }
        RNG.with(|rng| {
            let mut x = rng.get();
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            rng.set(x);
            Some((x % len as u64) as usize)
        })
    }

    /// Runs `body` with this thread's agendas popping in `order`; the previous
    /// order and its draw position return afterwards.
    pub fn with<R>(order: PopOrder, body: impl FnOnce() -> R) -> R {
        struct Restore(PopOrder, u64);
        impl Drop for Restore {
            fn drop(&mut self) {
                CURRENT.with(|current| current.set(self.0));
                RNG.with(|rng| rng.set(self.1));
            }
        }
        let state = match order {
            PopOrder::Seeded(seed) => initial_state(seed),
            _ => RNG.with(Cell::get),
        };
        let _restore = Restore(
            CURRENT.with(|current| current.replace(order)),
            RNG.with(|rng| rng.replace(state)),
        );
        body()
    }
}

#[cfg(test)]
#[path = "agenda_test.rs"]
mod agenda_test;
