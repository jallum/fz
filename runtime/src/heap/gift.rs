//! The gift window: a heap lends its allocation path to a copy whose result
//! belongs to another heap.
//!
//! A sender that has matched a message for a receiver copies what the receiver
//! will keep. It does so into its own heap, through the ordinary bump
//! allocator, but with the tip set aside: `begin_gift` installs a fresh block,
//! the copy allocates as usual (overflowing into larger blocks exactly as any
//! allocation does), and `end_gift` cuts everything allocated since the window
//! opened into a `GiftSegment` and puts the saved tip back. The receiver later
//! calls `graft` and owns the segment's blocks, fragments, off-heap stubs and
//! deferred destructors as if it had allocated them. Its next Cheney pass
//! treats the adopted blocks as from-space and copies the live data out.
//!
//! No process ever writes into another process's live heap: the sender only
//! writes into blocks that are not yet anyone's, and the receiver only moves
//! pointers.

use super::block_pool::{Block, pool_alloc, pool_free};
use super::fragment::Fragment;
use super::{Heap, SIZE_TABLE};
use crate::procbin::{mso_release_chain, mso_set_next};
use std::alloc::dealloc;
use std::sync::atomic::Ordering;

/// What `begin_gift` records so `end_gift` can cut the segment with splits
/// alone: the tip to restore, the list lengths at which the window opened, the
/// mso head at that moment, and the oldest stub pushed since.
pub(super) struct GiftWindow {
    pub(super) saved_tip: Block,
    abandoned_len: usize,
    fragments_len: usize,
    pending_dtors_len: usize,
    alloc_count: u64,
    saved_mso_head: u64,
    /// The first stub pushed onto the mso chain while the window was open,
    /// or 0 if none was. Its `mso_next` is the seam where the gift's prefix
    /// meets whatever chain it is spliced onto.
    oldest_mso: u64,
}

/// A detached run of heap storage with no reference into any heap. It holds
/// the blocks the copy filled (by start, fill and size class), the oversize
/// fragments it made, the off-heap stubs it pushed (as an mso chain whose
/// last link is 0), the destructors it deferred and how many objects it
/// allocated. `Heap::graft` adopts all of it; dropping an un-grafted segment
/// returns every block to the pool, frees every fragment and releases every
/// stub's off-heap reference, so an orphan leaks nothing.
pub struct GiftSegment {
    blocks: Vec<Block>,
    fragments: Vec<Fragment>,
    mso_head: u64,
    oldest_mso: u64,
    pending_dtors: Vec<(u64, u64)>,
    objects: u64,
}

impl GiftSegment {
    /// The segment of a copy that copied nothing: no blocks, no fragments, no
    /// stubs, no destructors. Grafting it changes nothing, and it never
    /// touches the block pool.
    pub fn empty() -> Self {
        GiftSegment {
            blocks: Vec::new(),
            fragments: Vec::new(),
            mso_head: 0,
            oldest_mso: 0,
            pending_dtors: Vec::new(),
            objects: 0,
        }
    }

    /// Bytes written into the segment's blocks, by fill.
    pub fn fill_bytes(&self) -> usize {
        self.blocks.iter().map(Block::fill).sum()
    }

    pub fn block_count(&self) -> usize {
        self.blocks.len()
    }

    pub fn fragment_count(&self) -> usize {
        self.fragments.len()
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
        for f in self.fragments.drain(..) {
            unsafe { dealloc(f.ptr, f.layout) };
        }
        for block in self.blocks.drain(..) {
            pool_free(block.start, block.size_class);
        }
    }
}

impl Heap {
    /// Set the tip aside and allocate into a fresh block from the smallest
    /// size class until `end_gift`. Everything allocated in between belongs to
    /// the gift; the heap's own data is untouched and its free space is kept.
    pub fn begin_gift(&mut self) {
        assert!(self.gift.is_none(), "begin_gift while a gift window is already open");
        let saved_tip = self.current_block();
        self.gift = Some(GiftWindow {
            saved_tip,
            abandoned_len: self.abandoned_blocks.len(),
            fragments_len: self.fragments.len(),
            pending_dtors_len: self.pending_dtors.len(),
            alloc_count: self.alloc_count,
            saved_mso_head: self.mso_head,
            oldest_mso: 0,
        });
        let start = pool_alloc(0);
        self.install_block(Block {
            start,
            top: start,
            size_class: 0,
        });
    }

    /// Cut everything allocated since `begin_gift` into a segment and restore
    /// the saved tip. The pressure flag is recomputed for the restored heap,
    /// since allocation inside the window may have raised it for bytes that
    /// are no longer here. Allocation statistics stay with this heap: the
    /// sender did the work.
    pub fn end_gift(&mut self) -> GiftSegment {
        let window = self.gift.take().expect("end_gift without an open gift window");
        let mut blocks = self.abandoned_blocks.split_off(window.abandoned_len);
        blocks.push(self.current_block());
        let fragments = self.fragments.split_off(window.fragments_len);
        let pending_dtors = self.pending_dtors.split_off(window.pending_dtors_len).into();
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
        self.pressure
            .store(self.bytes_used() >= self.gc_threshold_bytes, Ordering::Relaxed);
        GiftSegment {
            blocks,
            fragments,
            mso_head,
            oldest_mso: window.oldest_mso,
            pending_dtors,
            objects,
        }
    }

    /// Take ownership of a segment: its blocks become adopted from-space, its
    /// fragments join this heap's, its mso prefix is spliced ahead of this
    /// heap's chain, and its deferred destructors queue behind this heap's.
    /// Adopted bytes count toward allocation pressure by fill, so a heap that
    /// receives many gifts collects them.
    pub fn graft(&mut self, mut segment: GiftSegment) {
        self.adopted_blocks.append(&mut segment.blocks);
        self.fragments.append(&mut segment.fragments);
        if segment.mso_head != 0 {
            mso_set_next(segment.oldest_mso, self.mso_head);
            self.mso_head = segment.mso_head;
            segment.mso_head = 0;
        }
        self.pending_dtors.extend(segment.pending_dtors.drain(..));
        self.alloc_count += segment.objects;
        if self.bytes_used() >= self.gc_threshold_bytes {
            self.pressure.store(true, Ordering::Relaxed);
        }
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

    /// Capacity of the smallest block a gift window opens with.
    pub fn gift_first_block_bytes() -> usize {
        SIZE_TABLE[0]
    }
}
