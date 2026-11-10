//! Per-process bump arena with Cheney GC (cps-in-clif §6.1, §6.4, §7).
//!
//! One block per `Process`. Allocation is pure bump: `bump_top += size`. When
//! `bump_top` would cross `block_end`, we allocate a fresh (larger) block and
//! park the old one in `blocks`; a grafted gift segment parks its blocks there
//! too. Block capacities are `SIZE_TABLE` entries, which the pool recycles, or
//! for an object larger than the whole table exactly that object's size, which
//! the system allocator provides and takes back. At the next park-time GC, the collector copies everything reachable
//! from scheduler-owned roots into a fresh tip through the same bump path
//! (a copy that fills the tip parks it and climbs the table, like an
//! allocation); the old current block and all parked blocks are then freed.
//!
//! GC is *not* synchronous on allocation. `Heap::should_gc` is a pure
//! function of the heap's state: the bytes a collection could copy (the tip's
//! fill plus every parked block's fill) against half
//! the tip's capacity. The scheduler asks at the next natural boundary and
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
pub(crate) use self::ref_io::map_entry_refs;
pub use self::schema::{
    BITSTRING_READER_SCHEMA, BITSTRING_RESULT_SCHEMA, FieldDescriptor, FieldKind, Schema, SchemaIdentity,
    SchemaRegistry,
};
pub use self::stats::{AllocStat, GcStats, HeapAllocKind, HeapAllocStats};

/// fz-cty.5 — bitstrings above this many bytes are routed through the
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
    /// The bytes known to be live: set by a collection to the bytes that
    /// survived, raised by a graft by the gift's fill, left alone by
    /// allocation. Zero until the first collection or graft. `should_gc`
    /// counts allocation against it, and a collection's fresh tip is sized
    /// to it.
    pub live_baseline: usize,
    /// Blocks the heap has stopped bumping into: old tips abandoned by `grow`
    /// and blocks grafted from other heaps' gift segments. Each records its
    /// fill and capacity, so `Drop` / gc() can return it to the pool (§6.6)
    /// and the collector counts it by fill. Cheney frees the entire list at
    /// every collection.
    blocks: Vec<Block>,
    /// The open gift window, if `begin_gift` has set the tip aside and
    /// `end_gift` has not yet cut the segment.
    gift: Option<GiftWindow>,
    /// The atom-name authority for map key ordering. A process heap shares its
    /// process's node, so every map construction and lookup uses the same atom
    /// order as `Kernel.compare` without callers having to supply ambient
    /// process state.
    pub(crate) node: Rc<Node>,
    pub(crate) schemas: Rc<RefCell<SchemaRegistry>>,
    /// Count of GC invocations. Stub in fz-siu.7; real body lands in .8.
    pub gc_run_count: u64,
    /// Total allocations made since last successful GC. Backs `live_count()`
    /// — under bump-only with no reclaim, every alloc since-start is "live".
    /// .8 resets this on each Cheney pass to the surviving-object count.
    alloc_count: u64,
    /// Total allocation requests made by kind since the last explicit
    /// process/user-code reset. Unlike `alloc_count`, GC never rewrites this.
    alloc_stats: HeapAllocStats,
    /// Intrusive MSO ("Mixed Set / Off-heap") chain. Tagged head
    /// bits for a singly-linked list of live strict ProcBin and Resource
    /// stubs allocated on this heap; each entry's `mso_next` slot stores the
    /// previous tagged chain entry.
    /// The post-Cheney sweep (`procbin::mso_sweep`) rewrites entries to
    /// their to-space copies; `Heap::drop` calls `procbin::mso_drop_all`
    /// before pool reclaim so SharedBin references are balanced.
    pub mso_head: u64,
    /// Pending dtor invocations. When the MSO sweep finds a Resource stub
    /// whose off-heap refcount transitioned to zero, it enqueues
    /// `(closure_bits, payload_ref)` here instead of running fz code from
    /// inside the collection; the scheduler drains the queue before the
    /// process next runs, after a collection and at exit.
    pub pending_dtors: VecDeque<(u64, u64)>,
}
