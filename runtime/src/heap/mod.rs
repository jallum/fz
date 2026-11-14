//! Per-process bump arena with a generational Cheney collector (cps-in-clif
//! §6.1, §6.4, §7).
//!
//! Allocation is pure bump: `bump_top += size`. When `bump_top` would cross
//! `block_end`, we allocate a fresh (larger) block and park the old one in
//! `young_blocks`. Block capacities are `SIZE_TABLE` entries, which the pool
//! recycles, or for an object larger than the whole table exactly that
//! object's size, which the system allocator provides and takes back.
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
//! block is old at birth: a gift references only itself and literals.
//!
//! GC is *not* synchronous on allocation. `Heap::should_gc` is a pure
//! function of the heap's state: the young bytes against the old bytes (or half
//! the smallest tip). The scheduler asks at the next natural boundary and
//! calls GC over process roots; the question never expires the reduction
//! budget. All SSA values are gone (Cranelift's Tail CC popped them), so only
//! scheduler-owned closures, mailbox roots, and interpreter-owned explicit
//! roots are traced.
//!
//! Forwarding marker: every heap object is 16-byte aligned, so a live
//! pointer's low nibble is clear. A copied from-space object has the one
//! marker word of its kind (`gc::forwarding`) overwritten with the to-space
//! address plus a set low nibble; nothing else uses the low bits.

mod block_pool;
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
mod deep_copy_test;
#[cfg(test)]
mod gift_test;
#[cfg(test)]
mod heap_test;
#[cfg(test)]
mod minor_collection_test;
#[cfg(test)]
mod schema_test;

use self::block_pool::Block;
use self::gift::GiftWindow;
use crate::process::Node;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;

#[cfg(test)]
pub use self::block_pool::pool_drain_for_test;
pub use self::block_pool::{SIZE_TABLE, next_block_capacity, pick_block_capacity};
pub use self::block_pool::{pool_outstanding_blocks, pool_total_cached_blocks};
pub use self::deep_copy::{
    AddressMap, AddressSet, HeapView, deep_copy_any_value, deep_copy_any_value_ref, deep_copy_slot, measure_deep_copy,
};
pub(crate) use self::gc::forwarding::forwarded_target;
pub use self::gift::GiftSegment;
pub use self::imp::{closure_capture_ref, list_head_ref, list_tail_ref};
pub use self::map_view::MapLayout;
pub use self::ref_io::{map_entries_refs, map_entry_refs, map_slot_refs};
pub use self::schema::{FieldDescriptor, FieldKind, NamedSchema, Schema, SchemaIdentity, SchemaRegistry, StructKey};
pub use self::stats::{AllocStat, GcStats, Generation, HeapAllocKind, HeapAllocStats};

/// Bitstrings above this many bytes are routed through the
/// shared zone (refcounted off-heap `SharedBin` + per-process `ProcBin`
/// stub) instead of being inlined on the per-process heap. Matches
/// BEAM's refc-binary threshold.
pub const SHARED_BIN_THRESHOLD_BYTES: usize = 64;

pub struct Heap {
    block_start: *mut u8,
    bump_top: *mut u8,
    block_end: *mut u8,
    /// The tip's capacity in bytes: a `SIZE_TABLE` entry, or an exact size
    /// above the table for a block made to hold a larger object.
    block_size: usize,
    /// The bytes in old blocks: set by a major collection to the bytes it
    /// copied, raised by a minor collection by the bytes it copied and by a
    /// graft by the gift's fill, left alone by allocation. Zero until the
    /// first collection or graft. `should_gc` counts the young bytes against
    /// it, and a collection's fresh tip is sized to it.
    pub live_baseline: usize,
    /// The old bytes the last major collection left: what the next one is
    /// measured against. Zero until the first major collection.
    old_after_last_major: usize,
    /// The bytes the last collection copied: the guess for how many a minor
    /// collection will. Zero until the first collection.
    last_copied_bytes: usize,
    /// Blocks allocation has stopped bumping into since the last collection:
    /// tips abandoned by `climb_tip` and single-object blocks from
    /// `alloc_parked`. With the tip they are the young blocks. Each records its
    /// fill and capacity, so a collection counts it by fill and releases it.
    young_blocks: Vec<Block>,
    /// Blocks a collection filled with survivors and blocks grafted from
    /// gift segments. Released by `Drop` and by a major collection.
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
    /// Objects allocated since the last collection. With `old_objects` it
    /// backs `live_count()`: under bump-only with no reclaim, every object
    /// allocated is "live".
    alloc_count: u64,
    /// Objects in old blocks: those collections kept and gifts brought.
    old_objects: u64,
    /// Total allocation requests made by kind since the last explicit
    /// process/user-code reset. Unlike `alloc_count`, GC never rewrites this.
    alloc_stats: HeapAllocStats,
    /// Intrusive MSO ("Mixed Set / Off-heap") chain of the young stubs: tagged
    /// head bits for a singly-linked list of live strict ProcBin and Resource
    /// stubs allocated since the last collection; each entry's `mso_next` slot
    /// stores the previous tagged chain entry.
    /// The post-Cheney sweep (`procbin::mso_sweep`) moves each survivor onto
    /// `mso_old_head` and releases the rest; `Heap::drop` calls
    /// `procbin::mso_drop_all` before pool reclaim so SharedBin references are
    /// balanced.
    pub mso_head: u64,
    /// The chain of the old stubs: those a collection kept and those gifts
    /// brought. A minor sweep never walks it, so an old stub is found dead by
    /// a major collection.
    pub mso_old_head: u64,
    /// Pending dtor invocations. When the MSO sweep finds a Resource stub
    /// whose off-heap refcount transitioned to zero, it enqueues
    /// `(closure_bits, payload_ref)` here instead of running fz code from
    /// inside the collection; the scheduler drains the queue before the
    /// process next runs, after a collection and at exit.
    pub pending_dtors: VecDeque<(u64, u64)>,
}
