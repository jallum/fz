//! What a collection takes as from-space, and the one question it asks of it.

use super::super::Heap;
use crate::heap::Generation;
use std::cell::Cell;

/// The young blocks' address ranges, sorted. Young blocks are few: the tip, the
/// ones it climbed past since the last collection, and any huge object's block.
/// The range a pointer hit last is tried first, since neighbouring pointers
/// mostly share a block; a miss searches the rest.
struct YoungRanges {
    ranges: Vec<(usize, usize)>,
    last_hit: Cell<usize>,
}

impl YoungRanges {
    fn of(heap: &Heap) -> Self {
        let mut ranges: Vec<(usize, usize)> = heap
            .young_ranges()
            .map(|(start, end)| (start as usize, end as usize))
            .collect();
        ranges.sort_unstable();
        Self {
            ranges,
            last_hit: Cell::new(0),
        }
    }

    fn contains(&self, addr: usize) -> bool {
        let within = |&(start, end): &(usize, usize)| start <= addr && addr < end;
        if self.ranges.get(self.last_hit.get()).is_some_and(within) {
            return true;
        }
        let next = self.ranges.partition_point(|&(start, _)| start <= addr);
        let Some(index) = next.checked_sub(1) else {
            return false;
        };
        let hit = within(&self.ranges[index]);
        if hit {
            self.last_hit.set(index);
        }
        hit
    }
}

/// What a collection knows about from-space.
///
/// A major collection takes every block, so every untagged pointer is in it. A
/// minor collection takes the young blocks, and an untagged pointer outside
/// them points into an old block, which the collection leaves as it is. A debug
/// build also keeps the from-space block ranges and checks that the literal bit
/// and the address agree: a tagged pointer lies in no heap block, an untagged one
/// lies in from-space or in a block a minor collection leaves, and none lies in
/// to-space.
pub(in super::super) struct FromSpace {
    young: Option<YoungRanges>,
    #[cfg(debug_assertions)]
    ranges: Vec<(*mut u8, *mut u8)>,
}

impl FromSpace {
    /// The from-space of a collection of `generation` about to start: the
    /// blocks `heap` owns now that the generation takes.
    pub(in super::super) fn of(heap: &Heap, generation: Generation) -> Self {
        Self {
            young: (generation == Generation::Minor).then(|| YoungRanges::of(heap)),
            #[cfg(debug_assertions)]
            ranges: match generation {
                Generation::Minor => heap.young_ranges().collect(),
                Generation::Major => heap.block_ranges().collect(),
            },
        }
    }

    /// Whether the collection moves the object at `p`, whose literal bit is
    /// `literal`: untagged and inside from-space.
    #[inline]
    pub(in super::super) fn moves(&self, heap: &Heap, p: *mut u8, literal: bool) -> bool {
        self.assert_classified(heap, p, literal);
        !literal && self.young.as_ref().is_none_or(|young| young.contains(p as usize))
    }

    #[inline]
    fn assert_classified(&self, heap: &Heap, p: *mut u8, literal: bool) {
        #[cfg(debug_assertions)]
        {
            use super::super::ref_io::ptr_in_ranges;
            let in_from_space = ptr_in_ranges(p, self.ranges.iter().copied());
            let in_left_in_place = ptr_in_ranges(p, heap.old_ranges());
            assert_eq!(
                in_from_space || in_left_in_place,
                !literal,
                "{p:p} is {} but lies {} a heap block",
                if literal {
                    "tagged literal"
                } else {
                    "an untagged heap pointer"
                },
                if literal { "in" } else { "outside" },
            );
            assert!(
                !ptr_in_ranges(p, heap.young_ranges()),
                "{p:p} lies in to-space while it is being forwarded"
            );
        }
        #[cfg(not(debug_assertions))]
        let _ = (heap, p, literal);
    }
}
