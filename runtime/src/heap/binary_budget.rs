//! The off-heap binary bytes a heap has made, and the point at which they make
//! a collection due.
//!
//! A shared binary's bytes live outside the heap; the heap holds a 32-byte
//! BinRef and views of it. The bytes are freed only when a collection finds
//! the BinRef dead, so a process that makes large binaries and drops them
//! would allocate gigabytes between collections that the heap's own byte count
//! never notices. The budget makes those bytes count: a collection is due
//! once the binary bytes made since the last collection reach the bytes the
//! heap still holds, as BEAM's virtual heap does.

use super::stats::Generation;

/// The least the binary budget ever is. Collecting costs a trace of the heap
/// however few binary bytes it frees, so a heap holding almost no binary bytes
/// is not collected for every few large binaries it makes; 256 KiB is the
/// bytes a process may make before the first collection it owes to them.
pub const MIN_BINARY_BUDGET: usize = 256 * 1024;

/// The binary bytes a heap made since its last collection, the binary bytes it
/// holds, and the young binary bytes at which a collection is due.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinaryBudget {
    young_binary_bytes: usize,
    held_binary_bytes: usize,
    budget: usize,
}

impl BinaryBudget {
    pub const fn new() -> Self {
        Self {
            young_binary_bytes: 0,
            held_binary_bytes: 0,
            budget: MIN_BINARY_BUDGET,
        }
    }

    /// The capacity of a shared binary's buffer made since the last
    /// collection. An in-place append makes no buffer and records nothing.
    pub fn record_made(&mut self, capacity: usize) {
        self.young_binary_bytes += capacity;
    }

    /// The binary bytes made since the last collection.
    pub fn young_binary_bytes(&self) -> usize {
        self.young_binary_bytes
    }

    /// The binary bytes the heap held after its last collection.
    pub fn held_binary_bytes(&self) -> usize {
        self.held_binary_bytes
    }

    /// The young binary bytes at which a collection is due.
    pub fn budget(&self) -> usize {
        self.budget
    }

    /// The binary bytes made since the last collection have reached the budget.
    pub fn is_due(&self) -> bool {
        self.young_binary_bytes >= self.budget
    }

    /// A collection of `generation` kept `survivor_bytes` of binary buffers
    /// among the BinRefs it examined. A major collection examines every BinRef,
    /// so the survivors are all the heap holds; a minor one examines the young
    /// ones, which join what the heap already held. The next budget is the
    /// bytes held, so a heap that holds N binary bytes collects after making N
    /// more.
    pub fn after_collection(&mut self, generation: Generation, survivor_bytes: usize) {
        self.held_binary_bytes = match generation {
            Generation::Major => survivor_bytes,
            Generation::Minor => self.held_binary_bytes + survivor_bytes,
        };
        self.young_binary_bytes = 0;
        self.budget = self.held_binary_bytes.max(MIN_BINARY_BUDGET);
    }
}

impl Default for BinaryBudget {
    fn default() -> Self {
        Self::new()
    }
}
