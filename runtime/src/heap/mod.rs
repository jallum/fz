//! Per-process bump arena with a generational Cheney collector (cps-in-clif
//! §6.1, §6.4, §7).
//!
//! Allocation is pure bump: `bump_top += size`. When `bump_top` would cross
//! `block_end`, we allocate a fresh (larger) block and park the old one in
//! `young_blocks`. Block capacities are `SIZE_TABLE` entries, which the pool
//! recycles, or for an object larger than the whole table exactly that
//! object's size, a span of its own that is reused once it is released.
//!
//! Every block is a span of one reserved range of address space (`arena`),
//! and a table beside it holds a byte per granule saying whether the block
//! that owns the granule is young. A young block (the tip, the blocks
//! allocation parks and a gift's block) marks the table when it is made; a
//! pooled block's mark stays under its span through release and reuse, so
//! the table is written only when a span's youth changes. An old block (a
//! collection's to-space, its overflow blocks and the huge objects it copies)
//! writes the table only to clear a mark a young block left. The range grows
//! by reserving the next chunk at its exact end, and a table that cannot
//! follow stops the program loudly.
//! Whether an object is young
//! is a read of that table at its address (`Reservation::is_young`), and a minor
//! collection's from-space is the granules that read young (`FromSpace`), so
//! nothing is collected or sorted per collection. Off-heap binaries, resources
//! and static literals are the system allocator's and lie outside the range,
//! so a literal's address reads as no block.
//!
//! A block has an age. Young blocks are the tip and the blocks allocation has
//! parked since the last collection. A collection copies the survivors of its
//! from-space into fresh blocks through the same bump path (a copy that fills
//! its tip parks it and climbs the table, like an allocation); those blocks are
//! old, and the from-space is released. A minor collection's from-space is the
//! young blocks, so old blocks stay where they are and are not traced through:
//! nothing old points at anything young, because data is immutable and the
//! collector marks every list cell it keeps as shared, so none is rewritten in
//! place. A major collection's from-space is every block, and runs once the old
//! blocks have outgrown what the last major collection left. A grafted gift
//! block is young, parked with the blocks allocation parked: a minor
//! collection reclaims it if the message is dead and copies it once if live.
//!
//! GC is *not* synchronous on allocation. `Heap::should_gc` is a pure
//! function of the heap's state: the young bytes against the old bytes (or half
//! the smallest tip). The scheduler asks at the next natural boundary and
//! calls GC over process roots; the question never expires the reduction
//! budget. All SSA values are gone (Cranelift's Tail CC popped them), so only
//! scheduler-owned closures, mailbox roots, and interpreter-owned explicit
//! roots are traced.
//!
//! One `gc::forward::Tracer` carries a collection: the from-space, the heap,
//! the schemas and the queue of copied objects. Its `forward(word,
//! kind)` is the only way a collection moves a value: the word a container
//! stores, with its kind, comes back unchanged unless the kind is a heap kind
//! and the object is in from-space, in which case it comes back naming the
//! to-space copy. Roots and every trace method go through it. The collection
//! counts nothing per object: `copied_bytes` is the fill of to-space, read once
//! at the end, and `copied_objects` is the length of the queue of copied
//! objects plus the scalar boxes the roots copied.
//!
//! Forwarding marker: every heap object is 16-byte aligned, so a live
//! pointer's low nibble is clear. A copied from-space object has the one
//! marker word of its kind (`gc::forwarding`) overwritten with the to-space
//! address plus a set low nibble; nothing else uses the low bits.

pub(crate) mod arena;
mod binary_budget;
mod block_pool;
mod collected;
mod deep_copy;
mod gc;
mod gift;
mod imp;
mod map_trie;
mod map_view;
mod ref_io;
mod schema;
mod stats;

#[cfg(test)]
mod binary_budget_test;
#[cfg(test)]
mod deep_copy_test;
#[cfg(test)]
mod gift_test;
#[cfg(test)]
mod heap_test;
#[cfg(test)]
mod minor_collection_test;
#[cfg(test)]
mod schema_test;

pub use self::binary_budget::{BinaryBudget, MIN_BINARY_BUDGET};
use self::block_pool::Block;
use self::gc::CopiedObject;
use self::gift::GiftWindow;
use crate::process::Node;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;

#[cfg(all(test, debug_assertions))]
pub(crate) use self::block_pool::UNWRITTEN_BYTE;
#[cfg(test)]
pub use self::block_pool::pool_drain_for_test;
pub use self::block_pool::{Footprint, pool_footprint, pool_outstanding_blocks, pool_total_cached_blocks};
pub use self::block_pool::{SIZE_TABLE, next_block_capacity, pick_block_capacity, pick_tip_capacity};
pub(crate) use self::block_pool::{binary_buffer_allocated, binary_buffer_freed, poisoned};
pub use self::collected::{Collected, CollectedBlocks};
pub use self::deep_copy::{
    HeapView, deep_copy_any_value, deep_copy_any_value_ref, deep_copy_slot, deep_copy_stored, measure_deep_copy,
};
pub(crate) use self::gc::forwarding::forwarded_target;
pub use self::gc::roots::{RootForwarder, Roots};
pub use self::gift::GiftSegment;
pub use self::imp::{closure_capture_ref, list_head_ref, list_tail_ref};
pub use self::map_view::{MAP_BATCH_LEN, MapLayout, MapPart};
pub use self::ref_io::{map_entries_refs, map_entry_refs, map_slot_refs};
pub use self::schema::{FieldDescriptor, FieldKind, NamedSchema, Schema, SchemaIdentity, SchemaRegistry, StructKey};
pub use self::stats::{AllocStat, GcStats, Generation, HeapAllocKind, HeapAllocStats, StubCounts, StubSite};

/// Bitstrings above this many bytes are routed through the
/// shared zone (refcounted off-heap `SharedBin`, held by one per-process
/// `BinRef`, and named by per-process `BinView` objects) instead of being inlined on the per-process heap. Matches
/// BEAM's refc-binary threshold.
pub const SHARED_BIN_THRESHOLD_BYTES: usize = 64;

/// Byte offsets, from the start of a `Heap`, of the fields compiled code
/// updates to place an object at the tip without calling the runtime: the
/// bump pointer and its block's start and end.
#[derive(Clone, Copy, Debug)]
pub struct InlineAllocLayout {
    pub block_start: usize,
    pub bump_top: usize,
    pub block_end: usize,
}

pub const INLINE_ALLOC_LAYOUT: InlineAllocLayout = InlineAllocLayout {
    block_start: std::mem::offset_of!(Heap, block_start),
    bump_top: std::mem::offset_of!(Heap, bump_top),
    block_end: std::mem::offset_of!(Heap, block_end),
};

pub struct Heap {
    block_start: *mut u8,
    bump_top: *mut u8,
    block_end: *mut u8,
    /// The tip's capacity in bytes: a `SIZE_TABLE` entry, or an exact size
    /// above the table for a block made to hold a larger object.
    block_size: usize,
    /// The bytes in old blocks: set by a major collection to the bytes it
    /// copied, raised by a minor collection by the bytes it copied, left alone
    /// by allocation and by a graft. Zero until the first collection. `should_gc` counts the young bytes against
    /// it, and a major collection's to-space guess is sized to it.
    pub(crate) live_baseline: usize,
    /// The old bytes the last major collection left: what the next one is
    /// measured against. Zero until the first major collection.
    old_after_last_major: usize,
    /// The bytes the last minor collection copied: the guess for how many the
    /// next one will. Zero until the first minor collection.
    last_minor_copied_bytes: usize,
    /// The capacity of the next overflow block a collection's copy installs
    /// when the to-space block fills. Reset when a collection starts to the
    /// smallest class, or to the last table entry when the to-space guess
    /// reaches it, and raised a class per overflow block up to that entry.
    overflow_step: usize,
    /// Blocks allocation has stopped bumping into since the last collection:
    /// tips abandoned by `climb_tip`, single-object blocks from
    /// `alloc_parked`, and blocks grafted from gift segments. With the tip they
    /// are the young blocks. Each records its fill and capacity, so a
    /// collection counts it by fill and releases it.
    young_blocks: Vec<Block>,
    /// The blocks the latest collection copied out of, held until its
    /// `Collected` is dropped and empty otherwise. It and `young_blocks` swap
    /// roles at every collection, so neither is ever freed.
    from_blocks: Vec<Block>,
    /// Where in `old_blocks` the blocks the latest collection filled begin.
    retired_from: usize,
    /// The worklist a collection's trace scans, emptied when the collection
    /// ends and kept for the next one.
    worklist: Vec<CopiedObject>,
    /// The bump pointer at which the young bytes reach the collection budget:
    /// `should_gc` is `bump_top >= collect_at`. It is the tip's start plus
    /// `collect_room`, moved when a tip is installed, and never by compiled
    /// code, which moves only `bump_top`.
    collect_at: *mut u8,
    /// The bytes the tip may take before a collection is due: the budget less
    /// the parked bytes, set from the budget after a collection, lowered by
    /// each park, and zero once the binary budget is due.
    collect_room: usize,
    /// The sum of the fill of `young_blocks`, kept as blocks are parked so
    /// `young_bytes` is asked in constant time at every scheduling boundary.
    parked_fill: usize,
    /// The bytes of `young_blocks` that grafts parked since the last
    /// collection: the received share of the young bytes.
    received_bytes: usize,
    /// Blocks a collection filled with survivors. Released by `Drop` and by a
    /// major collection.
    old_blocks: Vec<Block>,
    /// The open gift window, if `begin_gift` has set the tip aside and
    /// `end_gift` has not yet cut the segment.
    gift: Option<GiftWindow>,
    /// The atom-name authority for map key ordering. A process heap shares its
    /// process's node, so every map construction and lookup uses the same atom
    /// order as `Kernel.compare` without callers having to supply ambient
    /// process state.
    pub(crate) node: Rc<Node>,
    pub(crate) schemas: Rc<RefCell<SchemaRegistry>>,
    /// Each named struct's keys as atoms, so reading a struct as a map
    /// compares atom ids, never names.
    pub(crate) struct_maps: map_view::StructMaps,
    /// Count of GC invocations.
    pub gc_run_count: u64,
    /// Objects in old blocks: those collections kept.
    old_objects: u64,
    /// Binaries this heap has marked shared since it was made: each counts
    /// once, when its mark goes from clear to set. Compiled code that marks a
    /// binary inline adds to it at `BINARIES_SHARED_OFFSET`.
    pub(crate) binaries_shared: u64,
    /// Intrusive chain of the young off-heap
    /// objects: tagged head bits for a singly-linked list of the BinRefs and
    /// resource stubs allocated or received since the last collection; each entry's
    /// `off_heap_next` slot stores the previous tagged chain entry, and its kind tag
    /// names which of the two it is. Binary views are on no chain.
    /// The post-Cheney sweep (`off_heap::sweep`) moves each survivor onto
    /// `off_heap_old_head` and releases the rest; `Heap::drop` calls
    /// `off_heap::drop_all` before pool reclaim so SharedBin references are
    /// balanced.
    pub off_heap_head: u64,
    /// The chain of the old off-heap objects: those a collection kept. A minor sweep never walks it, so an old BinRef or resource
    /// stub is found dead by a major collection.
    pub off_heap_old_head: u64,
    /// The shared-binary bytes made since the last collection and the budget
    /// they make a collection due at.
    pub binary_budget: BinaryBudget,
    /// Binary views made since the last collection, by site; a collection
    /// reports them and starts the count again.
    pub stubs_made: StubCounts,
    /// BinRefs made since the last collection, by site; a collection reports
    /// them and starts the count again.
    pub binrefs_made: StubCounts,
    /// Pending dtor invocations. When the off-heap sweep finds a Resource stub
    /// whose off-heap refcount transitioned to zero, it enqueues
    /// `(closure_bits, payload_ref)` here instead of running fz code from
    /// inside the collection; the scheduler drains the queue before the
    /// process next runs, after a collection and at exit.
    pub pending_dtors: VecDeque<(u64, u64)>,
}
