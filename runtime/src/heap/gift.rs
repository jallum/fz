//! The gift window: a heap lends its allocation path to a copy whose result
//! belongs to another heap.
//!
//! A sender that has matched a message for a receiver measures what the
//! receiver will keep (`measure_deep_copy`) and copies it into its own heap,
//! through the ordinary bump allocator, but with the tip set aside:
//! `begin_gift` installs one fresh block of the smallest capacity that holds
//! the measured bytes, the copy fills it, and `end_gift` turns that block and
//! the off-heap stubs the copy pushed into a `GiftSegment` and puts the saved
//! tip back. The copy allocates exactly the measured bytes, so it cannot run
//! past the block; `end_gift` refuses a window whose fill is not the
//! measurement. The receiver later
//! calls `graft` and owns the segment's block and off-heap stubs as if it had
//! allocated them. Its next Cheney pass treats the grafted block as
//! from-space and copies the live data out.
//!
//! No process ever writes into another process's live heap: the sender only
//! writes into a block that is not yet anyone's, and the receiver only moves
//! pointers.

use super::Heap;
use super::block_pool::{Block, pick_block_capacity, pool_alloc};
use crate::procbin::{mso_release_chain, mso_set_next};

/// What `begin_gift` records so `end_gift` can cut the segment: the tip to
/// restore, the gift block's start (the tip while the copy has not
/// overflowed), the allocation count and mso head at that moment, and the
/// oldest stub pushed since.
pub(super) struct GiftWindow {
    pub(super) saved_tip: Block,
    block_start: *mut u8,
    /// The bytes the copy was measured at; the gift block's fill must equal
    /// it when the window closes.
    measured_bytes: usize,
    alloc_count: u64,
    saved_mso_head: u64,
    /// The first stub pushed onto the mso chain while the window was open,
    /// or 0 if none was. Its `mso_next` is the seam where the gift's prefix
    /// meets whatever chain it is spliced onto.
    oldest_mso: u64,
}

/// A detached run of heap storage with no reference into any heap. It holds
/// the one block the copy filled (by start, fill and capacity), the off-heap
/// stubs it pushed (as an mso chain whose last link is 0) and how many
/// objects it allocated. `Heap::graft` adopts all of it; dropping an
/// un-grafted segment releases the block and every stub's off-heap
/// reference, so an orphan leaks nothing.
pub struct GiftSegment {
    /// `None` only for the segment of a copy that allocated nothing.
    block: Option<Block>,
    mso_head: u64,
    oldest_mso: u64,
    objects: u64,
}

impl GiftSegment {
    /// The segment of a copy that copied nothing: no block, no
    /// stubs. Grafting it changes nothing, and it never
    /// touches the block pool.
    pub fn empty() -> Self {
        GiftSegment {
            block: None,
            mso_head: 0,
            oldest_mso: 0,
            objects: 0,
        }
    }

    /// Bytes written into the segment's block.
    pub fn fill_bytes(&self) -> usize {
        self.block.as_ref().map_or(0, Block::fill)
    }

    /// One for a copy that allocated, zero for one that did not.
    pub fn block_count(&self) -> usize {
        usize::from(self.block.is_some())
    }

    /// The head of the segment's own mso chain, or 0 when the copy made no
    /// off-heap stub.
    pub fn mso_head(&self) -> u64 {
        self.mso_head
    }
}

impl Drop for GiftSegment {
    fn drop(&mut self) {
        mso_release_chain(self.mso_head);
        if let Some(block) = self.block.take() {
            block.release();
        }
    }
}

impl Heap {
    /// Set the tip aside and allocate into one fresh block that holds
    /// `measured_bytes` until `end_gift`. Everything allocated in between
    /// belongs to the gift; the heap's own data is untouched and its free
    /// space is kept.
    pub fn begin_gift(&mut self, measured_bytes: usize) {
        assert!(self.gift.is_none(), "begin_gift while a gift window is already open");
        let saved_tip = self.current_block();
        let capacity = pick_block_capacity(measured_bytes);
        let start = pool_alloc(capacity);
        self.gift = Some(GiftWindow {
            saved_tip,
            block_start: start,
            measured_bytes,
            alloc_count: self.alloc_count,
            saved_mso_head: self.mso_head,
            oldest_mso: 0,
        });
        self.install_block(Block {
            start,
            top: start,
            capacity,
        });
    }

    /// Cut the gift block and the stubs pushed since `begin_gift` into a
    /// segment and restore the saved tip. The block's fill must be the
    /// measured bytes: a copy that allocated more or less than its measure is
    /// a disagreement between two passes that must walk the same objects, and
    /// it stops here. Allocation statistics stay with this heap: the sender
    /// did the work.
    pub fn end_gift(&mut self) -> GiftSegment {
        let window = self.gift.take().expect("end_gift without an open gift window");
        assert!(
            self.block_start == window.block_start,
            "gift copy overflowed its measured block: the measure and the copy disagree"
        );
        let block = self.current_block();
        assert_eq!(
            block.fill(),
            window.measured_bytes,
            "gift copy allocated a different number of bytes than it was measured at: the measure and the copy disagree"
        );
        let mso_head = if window.oldest_mso == 0 {
            0
        } else {
            mso_set_next(window.oldest_mso, 0);
            self.mso_head
        };
        self.mso_head = window.saved_mso_head;
        let objects = self.alloc_count - window.alloc_count;
        self.alloc_count = window.alloc_count;
        self.install_block(window.saved_tip);
        GiftSegment {
            block: Some(block),
            mso_head,
            oldest_mso: window.oldest_mso,
            objects,
        }
    }

    /// Take ownership of a segment: its block joins this heap's parked blocks
    /// as from-space, its mso prefix is spliced ahead of this heap's chain.
    /// Its fill counts toward `should_gc`, so a heap that receives many gifts
    /// collects them.
    pub fn graft(&mut self, mut segment: GiftSegment) {
        self.blocks.extend(segment.block.take());
        if segment.mso_head != 0 {
            mso_set_next(segment.oldest_mso, self.mso_head);
            self.mso_head = segment.mso_head;
            segment.mso_head = 0;
        }
        self.alloc_count += segment.objects;
    }

    /// Make `bits` the head of the mso chain and return the previous head,
    /// which the caller writes into the new stub's `mso_next` link. An open
    /// gift window remembers the first stub pushed through it.
    pub(crate) fn mso_push(&mut self, bits: u64) -> u64 {
        let previous = self.mso_head;
        self.mso_head = bits;
        if let Some(window) = &mut self.gift
            && window.oldest_mso == 0
        {
            window.oldest_mso = bits;
        }
        previous
    }
}
