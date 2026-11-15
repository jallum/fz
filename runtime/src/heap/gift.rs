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
//! calls `graft` and owns the segment's block and off-heap stubs as if a
//! collection had kept them: they are old. A gift is packed, and references
//! only itself and literals, so nothing in it points at the receiver's young
//! data. Only a major collection copies the live data out of it.
//!
//! No process ever writes into another process's live heap: the sender only
//! writes into a block that is not yet anyone's, and the receiver only moves
//! pointers.

use super::Heap;
use super::block_pool::{Block, pick_block_capacity, pool_alloc};
use crate::procbin::{MsoStub, ProcBin, mso_release_chain, mso_set_next};
use crate::resource::ResourceStub;

/// What `begin_gift` records so `end_gift` can cut the segment: the tip to
/// restore, the gift block's start (the tip while the copy has not
/// overflowed), the allocation count at that moment, and the stubs each chain
/// had.
pub(super) struct GiftWindow {
    pub(super) saved_tip: Block,
    block_start: *mut u8,
    /// The bytes the copy was measured at; the gift block's fill must equal
    /// it when the window closes.
    measured_bytes: usize,
    alloc_count: u64,
    binaries: WindowChain,
    resources: WindowChain,
}

/// One chain of an open gift window: its head when the window opened, and the
/// first stub pushed onto it since, or 0 if none was. That stub's `mso_next`
/// is the seam where the gift's prefix meets whatever chain it is spliced
/// onto.
#[derive(Clone, Copy)]
struct WindowChain {
    saved_head: u64,
    oldest: u64,
}

impl WindowChain {
    fn open(head: u64) -> Self {
        WindowChain {
            saved_head: head,
            oldest: 0,
        }
    }

    fn note_push(&mut self, bits: u64) {
        if self.oldest == 0 {
            self.oldest = bits;
        }
    }

    /// Cut the stubs pushed since the window opened off `head`, restoring the
    /// head the window saved.
    fn cut<S: MsoStub>(self, head: &mut u64) -> SegmentChain {
        let cut = if self.oldest == 0 {
            SegmentChain::EMPTY
        } else {
            mso_set_next::<S>(self.oldest, 0);
            SegmentChain {
                head: *head,
                oldest: self.oldest,
            }
        };
        *head = self.saved_head;
        cut
    }
}

/// A detached chain of stubs of one kind: its head, and the oldest stub, whose
/// link is 0 until the chain is spliced onto another.
#[derive(Clone, Copy)]
struct SegmentChain {
    head: u64,
    oldest: u64,
}

impl SegmentChain {
    const EMPTY: SegmentChain = SegmentChain { head: 0, oldest: 0 };

    /// Splice this chain ahead of `onto` and return the combined chain's head.
    fn splice_onto<S: MsoStub>(self, onto: u64) -> u64 {
        if self.head == 0 {
            return onto;
        }
        mso_set_next::<S>(self.oldest, onto);
        self.head
    }
}

/// A detached run of heap storage with no reference into any heap. It holds
/// the one block the copy filled (by start, fill and capacity), the off-heap
/// stubs it pushed (a binary chain and a resource chain, each ending in 0) and
/// how many objects it allocated. `Heap::graft` adopts all of it; dropping an
/// un-grafted segment releases the block and every stub's off-heap
/// reference, so an orphan leaks nothing.
pub struct GiftSegment {
    /// `None` only for the segment of a copy that allocated nothing.
    block: Option<Block>,
    binaries: SegmentChain,
    resources: SegmentChain,
    objects: u64,
}

impl GiftSegment {
    /// The segment of a copy that copied nothing: no block, no
    /// stubs. Grafting it changes nothing, and it never
    /// touches the block pool.
    pub fn empty() -> Self {
        GiftSegment {
            block: None,
            binaries: SegmentChain::EMPTY,
            resources: SegmentChain::EMPTY,
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

    /// The head of the segment's own binary chain, or 0 when the copy made no
    /// binary stub.
    pub fn mso_head(&self) -> u64 {
        self.binaries.head
    }

    /// The head of the segment's own resource chain, or 0 when the copy made
    /// no resource stub.
    pub fn resource_head(&self) -> u64 {
        self.resources.head
    }
}

impl Drop for GiftSegment {
    fn drop(&mut self) {
        mso_release_chain::<ProcBin>(self.binaries.head);
        mso_release_chain::<ResourceStub>(self.resources.head);
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
            binaries: WindowChain::open(self.mso_head),
            resources: WindowChain::open(self.resource_head),
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
        let binaries = window.binaries.cut::<ProcBin>(&mut self.mso_head);
        let resources = window.resources.cut::<ResourceStub>(&mut self.resource_head);
        let objects = self.alloc_count - window.alloc_count;
        self.alloc_count = window.alloc_count;
        self.install_block(window.saved_tip);
        GiftSegment {
            block: Some(block),
            binaries,
            resources,
            objects,
        }
    }

    /// Take ownership of a segment: its block joins this heap's old blocks, its
    /// stub prefixes are spliced ahead of this heap's old chains.
    /// The gift is packed and fully live, like the heap after a collection, so
    /// its fill raises `live_baseline` rather than counting as allocation.
    pub fn graft(&mut self, mut segment: GiftSegment) {
        if let Some(block) = segment.block.take() {
            self.live_baseline += block.fill();
            self.old_blocks.push(block);
        }
        self.mso_old_head = segment.binaries.splice_onto::<ProcBin>(self.mso_old_head);
        self.resource_old_head = segment.resources.splice_onto::<ResourceStub>(self.resource_old_head);
        segment.binaries = SegmentChain::EMPTY;
        segment.resources = SegmentChain::EMPTY;
        self.old_objects += segment.objects;
    }

    /// Whether `begin_gift` has set the tip aside and `end_gift` has not yet cut
    /// the segment.
    pub(super) fn gift_window_is_open(&self) -> bool {
        self.gift.is_some()
    }

    /// Make `bits` the head of the binary chain and return the previous head,
    /// which the caller writes into the new stub's `mso_next` link. An open
    /// gift window remembers the first stub pushed through it.
    pub(crate) fn mso_push(&mut self, bits: u64) -> u64 {
        let previous = self.mso_head;
        self.mso_head = bits;
        if let Some(window) = &mut self.gift {
            window.binaries.note_push(bits);
        }
        previous
    }

    /// Make `bits` the head of the resource chain; the counterpart of
    /// `mso_push` for a resource stub.
    pub(crate) fn resource_push(&mut self, bits: u64) -> u64 {
        let previous = self.resource_head;
        self.resource_head = bits;
        if let Some(window) = &mut self.gift {
            window.resources.note_push(bits);
        }
        previous
    }
}
