//! Per-process bump arena with Cheney GC (cps-in-clif §6.1, §6.4, §7).
//!
//! One block per `Process`. Allocation is pure bump: `bump_top += size`. When
//! `bump_top` would cross `block_end`, we allocate a fresh (larger) block and
//! park the old one in `abandoned_blocks`. At the next park-time GC, the
//! collector copies everything reachable from scheduler-owned roots into a
//! fresh to-space block; the old current block and all abandoned blocks are
//! then freed.
//!
//! GC is *not* synchronous on allocation. `note_alloc_pressure` sets a flag
//! when occupancy crosses `gc_threshold_bytes`; the scheduler reads the flag
//! at park-time (next quantum boundary) and calls GC over process roots.
//! All SSA values are gone (Cranelift's Tail CC popped them), so only
//! scheduler-owned closures, mailbox roots, and interpreter-owned explicit
//! roots are traced.
//!
//! Forwarding marker: a copied from-space object gets `(to_addr & !0xF) |
//! TAG_FWD` written into word 0. Strict pointer tags carry the object kind.

mod block_pool;
mod deep_copy;
mod fragment;
mod gc;
mod imp;
mod key_cmp;
mod ref_io;
mod schema;
mod stats;

#[cfg(test)]
mod tests;

use self::fragment::Fragment;
use std::cell::RefCell;
use std::rc::Rc;

pub use self::block_pool::{SIZE_TABLE, pick_size_class};
#[cfg(test)]
pub use self::block_pool::{pool_drain_for_test, pool_total_cached_blocks};
pub use self::deep_copy::{
    deep_copy_any_value, deep_copy_any_value_ref, deep_copy_slot, deep_copy_tagged_bits,
};
pub use self::schema::{FieldDescriptor, FieldKind, Schema, SchemaRegistry};
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
    block_size: usize,
    /// Index into SIZE_TABLE (§6.3, wired in fz-siu.9). Tracked here so
    /// proactive shrinkage can read/adjust it without growing the API.
    pub size_class: u8,
    /// 75% of `block_end`. Crossing this pointer in `alloc()` sets
    /// `FZ_SHOULD_YIELD` so the next back-edge can yield a continuation
    /// closure or let the interpreter forward its current roots in place.
    pub gc_watermark: *mut u8,
    /// Exact live bytes after the most recent GC. Zero until the first GC.
    /// Used by proactive shrinkage to size the to-space and detect low-live
    /// quiet periods.
    pub last_gc_live_bytes: usize,
    /// Telemetry from the most recent GC. Tests and runtime hosts can inspect
    /// this without coupling the `fz-runtime` crate to the compiler telemetry
    /// bus.
    pub last_gc_stats: GcStats,
    /// Old blocks abandoned by `grow`. Each carries its size_class so
    /// `Drop` / gc() can return it to the pool (§6.6). Cheney (.8)
    /// frees the entire list at every collection.
    abandoned_blocks: Vec<(*mut u8, u8)>,
    pub(crate) schemas: Rc<RefCell<SchemaRegistry>>,
    /// Park-time GC flag. Set by `note_alloc_pressure` when occupancy
    /// crosses `gc_threshold_bytes`; cleared by the scheduler after `gc()`.
    /// AtomicBool: the libdispatch worker pool may observe this from a
    /// thread other than the one that set it (one task per worker at a
    /// time, but the flag is read at scheduler boundaries).
    pressure: std::sync::atomic::AtomicBool,
    pub gc_threshold_bytes: usize,
    /// Count of GC invocations. Stub in fz-siu.7; real body lands in .8.
    pub gc_run_count: u64,
    /// Total allocations made since last successful GC. Backs `live_count()`
    /// — under bump-only with no reclaim, every alloc since-start is "live".
    /// .8 resets this on each Cheney pass to the surviving-object count.
    alloc_count: u64,
    /// Total allocation requests made by kind since the last explicit
    /// process/user-code reset. Unlike `alloc_count`, GC never rewrites this.
    alloc_stats: HeapAllocStats,
    /// fz-q8d.1 — intrusive MSO ("Mixed Set / Off-heap") chain. Tagged head
    /// bits for a singly-linked list of live strict ProcBin and Resource
    /// stubs allocated on this heap; each entry's `mso_next` slot stores the
    /// previous tagged chain entry.
    /// The post-Cheney sweep (`procbin::mso_sweep`) rewrites entries to
    /// their to-space copies; `Heap::drop` calls `procbin::mso_drop_all`
    /// before pool reclaim so SharedBin references are balanced.
    pub mso_head: u64,
    /// fz-4mk — pending dtor invocations. When an MSO sweep finds a
    /// Resource stub whose off-heap refcount transitioned to
    /// zero, instead of firing the dtor inline (which would mean running
    /// fz code from inside the GC pause), we enqueue
    /// `(closure_bits, payload)` here and the scheduler drains the queue
    /// at the next quantum boundary. See ticket fz-4mk.
    pub pending_dtors: std::collections::VecDeque<(u64, u64)>,
    /// fz-q8d.4 — fragment list. Oversized allocations (above the
    /// largest size_class) live here as their own system-allocator
    /// backed singletons. GC marks them via the `mark` bit; survivors
    /// stay put across collections, dead fragments are freed.
    fragments: Vec<Fragment>,
}
