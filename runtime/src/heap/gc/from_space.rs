//! What a collection takes as from-space, and the one question it asks of it.

use super::super::Heap;
use super::super::arena::{Reservation, range};
use crate::heap::Generation;

/// What a collection knows about from-space.
///
/// A major collection takes every block, so every untagged pointer is in it. A
/// minor collection takes the young blocks, and an untagged pointer to any
/// other block points into an old one, which the collection leaves as it is.
/// The age table says which: a block is young from the moment it is made, and a
/// collection's to-space is made old. A debug build also checks that the literal
/// bit and the address agree: a tagged pointer lies outside the heap range, an
/// untagged one lies in a young or an old block, and none lies in to-space.
pub(in super::super) struct FromSpace {
    ages: &'static Reservation,
    minor: bool,
}

impl FromSpace {
    /// The from-space of a collection of `generation` about to start.
    pub(in super::super) fn of(_heap: &Heap, generation: Generation) -> Self {
        Self {
            ages: range(),
            minor: generation == Generation::Minor,
        }
    }

    /// Whether the collection moves the object at `p`, whose literal bit is
    /// `literal`: untagged and, for a minor collection, young.
    #[inline]
    pub(in super::super) fn moves(&self, heap: &Heap, p: *mut u8, literal: bool) -> bool {
        self.assert_classified(heap, p, literal);
        !literal && (!self.minor || self.ages.is_young_in_range(p))
    }

    #[inline]
    fn assert_classified(&self, heap: &Heap, p: *mut u8, literal: bool) {
        #[cfg(debug_assertions)]
        {
            use super::super::ref_io::ptr_in_ranges;
            assert_eq!(
                self.ages.in_block(p),
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

#[cfg(test)]
#[path = "from_space_test.rs"]
mod from_space_test;
