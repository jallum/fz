//! What a collection leaves behind for whoever observes it: the blocks it
//! copied out of, still held, and the old blocks it filled.

use super::block_pool::{Block, Footprint, is_pooled_capacity};
use super::{GcStats, Heap};

/// A finished collection. It holds the from-space blocks until it is dropped,
/// so an observer reads them as they were, and dropping it releases them: a
/// pooled block back to the pool, an exact block to the system. The heap's
/// fresh tip is already installed, so a release never hands the heap an address
/// the from-space is giving up.
#[must_use = "the from-space is released when the collection is dropped"]
pub struct Collected<'h> {
    heap: &'h mut Heap,
    stats: &'h GcStats,
}

impl<'h> Collected<'h> {
    pub(super) fn new(heap: &'h mut Heap, stats: &'h GcStats) -> Self {
        Self { heap, stats }
    }

    /// What the collection measured and counted.
    pub fn stats(&self) -> &GcStats {
        self.stats
    }

    /// The heap, whose [`Heap::collected_blocks`] answer for this collection.
    pub fn heap(&self) -> &Heap {
        self.heap
    }
}

impl Drop for Collected<'_> {
    fn drop(&mut self) {
        self.heap.release_from_space();
    }
}

/// The blocks of the latest collection, read from the heap that made it: the
/// from-space it copied out of, which is held until the collection's
/// [`Collected`] is dropped, and the old blocks it filled. Every figure is
/// computed from the blocks when asked.
#[derive(Clone, Copy)]
pub struct CollectedBlocks<'h> {
    from_space: &'h [Block],
    retired: &'h [Block],
}

impl<'h> CollectedBlocks<'h> {
    pub(super) fn new(from_space: &'h [Block], retired: &'h [Block]) -> Self {
        Self { from_space, retired }
    }

    /// Blocks of the from-space the collection releases.
    pub fn blocks_released(&self) -> u64 {
        self.from_space.len() as u64
    }

    /// Capacity of the from-space blocks.
    pub fn from_space_capacity_bytes(&self) -> u64 {
        self.from_space.iter().map(|block| block.capacity as u64).sum()
    }

    /// Capacity of the blocks the collection's copy filled, the guess block and
    /// any overflow blocks. Less `copied_bytes`, the room the copy left unused
    /// in old blocks.
    pub fn to_space_capacity_bytes(&self) -> u64 {
        self.retired.iter().map(|block| block.capacity as u64).sum()
    }

    /// The thread's `held` footprint once the from-space is released: its
    /// capacity is no longer in use, and the pooled share of it rests idle.
    pub fn footprint_once_released(&self, held: Footprint) -> Footprint {
        let capacity: usize = self.from_space.iter().map(|block| block.capacity).sum();
        let pooled: usize = self
            .from_space
            .iter()
            .filter(|block| is_pooled_capacity(block.capacity))
            .map(|block| block.capacity)
            .sum();
        Footprint {
            in_use_bytes: held.in_use_bytes - capacity,
            idle_bytes: held.idle_bytes + pooled,
            peak_in_use_bytes: held.peak_in_use_bytes,
        }
    }
}
