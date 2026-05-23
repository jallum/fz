//! Per-process bump arena with Cheney GC (cps-in-clif §6.1, §6.4, §7).
//!
//! One block per `Process`. Allocation is pure bump: `bump_top += size`. When
//! `bump_top` would cross `block_end`, we allocate a fresh (larger) block and
//! park the old one in `abandoned_blocks`. At the next park-time GC, the
//! collector copies everything reachable from the root (process.parked_cont)
//! into a fresh to-space block; the old current block and all abandoned
//! blocks are then freed.
//!
//! GC is *not* synchronous on allocation. `note_alloc_pressure` sets a flag
//! when occupancy crosses `gc_threshold_bytes`; the scheduler reads the flag
//! at park-time (next quantum boundary) and calls `gc()`. Cheney runs with a
//! single root by design (§7): all SSA values are gone (Cranelift's Tail CC
//! popped them), so `process.parked_cont` is the only fz-side reference into
//! the arena.
//!
//! Forwarding marker: a copied from-space object's `HeapHeader` is overwritten
//! with `kind = FORWARDED_KIND` and the to-space pointer at offset 8.

#![allow(dead_code)]

use crate::fz_value::{FzValue, HeapHeader, HeapKind, ListCons, TypedValue, ValueKind};
use crate::procbin::{ProcBin, SharedBinHandle, alloc_procbin, mso_drop_all, mso_sweep};
use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Copy)]
struct CopiedObject {
    ptr: *mut u8,
    tag: u64,
}

/// Sentinel `HeapHeader.kind` for an already-copied (forwarded) from-space
/// object. The new pointer is stored at offset 8 of the from-header.
/// Distinct from all valid `HeapKind` discriminants (0..=9).
pub const FORWARDED_KIND: u16 = 0xFFFE;

/// Preset block sizes (bytes). Fibonacci-shape at the low end (§6.3) then
/// geometric tail (~×1.2, ceiling-rounded to 16 alignment). Cheney picks the
/// smallest entry that fits `live_bytes + slack`.
///
/// 32 entries covers ~6 MiB — heaps larger than the tail clamp to the last
/// class (`pick_size_class` never panics).
pub const SIZE_TABLE: [usize; 32] = build_size_table();

const fn build_size_table() -> [usize; 32] {
    let mut t = [0usize; 32];
    let prefix: [usize; 12] = [
        1024, 1536, 2560, 4096, 6656, 10752, 17408, 28160, 45568, 73728, 119296, 192768,
    ];
    let mut i = 0;
    while i < 12 {
        t[i] = prefix[i];
        i += 1;
    }
    while i < 32 {
        // next ≈ ceil(prev * 1.2) then aligned up to 16. Integer-only:
        //   ceil(prev * 6 / 5) = (prev * 6 + 4) / 5.
        let raw = (t[i - 1] * 6).div_ceil(5);
        t[i] = (raw + 15) & !15;
        i += 1;
    }
    t
}

/// Smallest size_class whose `SIZE_TABLE[class]` ≥ `bytes`. Clamps to the
/// last index for inputs that exceed the tail (§6.3) — never panics.
pub fn pick_size_class(bytes: usize) -> u8 {
    for (idx, &size) in SIZE_TABLE.iter().enumerate() {
        if size >= bytes {
            return idx as u8;
        }
    }
    (SIZE_TABLE.len() - 1) as u8
}

/// Per-thread block pool (§6.6). One free list per size_class. Spawn /
/// grow / gc pull from here; Heap::drop and gc()'s old-block release
/// return blocks here. Avoids per-spawn `malloc`/`free` churn under
/// heavy spawn pressure. Single-threaded for v1 (worker pool = 1, per
/// fz-ul4.19.1); the multi-worker follow-up will switch to either
/// per-worker pools or a Mutex-guarded shared pool.
struct BlockPool {
    free_lists: [Vec<*mut u8>; SIZE_TABLE.len()],
}

impl BlockPool {
    const fn new() -> Self {
        // Const init: 32 empty Vecs. `[Vec::new(); N]` doesn't const-init
        // because Vec is not Copy; use a manual array build.
        Self {
            free_lists: [const { Vec::new() }; SIZE_TABLE.len()],
        }
    }

    fn alloc(&mut self, size_class: u8) -> *mut u8 {
        let idx = size_class as usize;
        let size = SIZE_TABLE[idx];
        if let Some(p) = self.free_lists[idx].pop() {
            // Recycled blocks: zero before returning. Cheney + Heap::new
            // expect zero pages.
            unsafe {
                std::ptr::write_bytes(p, 0, size);
            }
            return p;
        }
        let layout = Layout::from_size_align(size, 16).expect("bad block layout");
        let p = unsafe { alloc_zeroed(layout) };
        assert!(!p.is_null(), "block pool: malloc failed");
        p
    }

    fn free(&mut self, p: *mut u8, size_class: u8) {
        // Free lists grow unbounded in v1. A real-world deployment would
        // cap each list (e.g., 4 entries) and `dealloc` the overflow.
        // For now we accept the worst-case memory footprint to keep the
        // pool deterministic.
        self.free_lists[size_class as usize].push(p);
    }
}

impl Drop for BlockPool {
    fn drop(&mut self) {
        // At thread exit (or test teardown), free any cached blocks.
        for (idx, list) in self.free_lists.iter_mut().enumerate() {
            let size = SIZE_TABLE[idx];
            let layout = Layout::from_size_align(size, 16).expect("bad block layout");
            for p in list.drain(..) {
                unsafe {
                    dealloc(p, layout);
                }
            }
        }
    }
}

thread_local! {
    static BLOCK_POOL: RefCell<BlockPool> = const { RefCell::new(BlockPool::new()) };
}

fn pool_alloc(size_class: u8) -> *mut u8 {
    BLOCK_POOL.with(|p| p.borrow_mut().alloc(size_class))
}

/// Returns a block to the pool. If the TLS pool has already been dropped
/// (thread teardown ordering), falls back to a direct `dealloc` — the
/// block leaks nothing, just bypasses the cache.
fn pool_free(p: *mut u8, size_class: u8) {
    let result = BLOCK_POOL.try_with(|pool| pool.borrow_mut().free(p, size_class));
    if result.is_err() {
        let size = SIZE_TABLE[size_class as usize];
        let layout = Layout::from_size_align(size, 16).expect("bad block layout");
        unsafe {
            dealloc(p, layout);
        }
    }
}

/// Test-only: drains every cached block in the per-thread pool back to
/// `dealloc`. Used to assert pool occupancy in acceptance tests; not
/// called from the runtime hot path.
#[cfg(test)]
pub fn pool_drain_for_test() {
    BLOCK_POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        for (idx, list) in pool.free_lists.iter_mut().enumerate() {
            let size = SIZE_TABLE[idx];
            let layout = Layout::from_size_align(size, 16).expect("bad block layout");
            for p in list.drain(..) {
                unsafe {
                    dealloc(p, layout);
                }
            }
        }
    });
}

/// Test-only: total cached blocks across all size classes.
#[cfg(test)]
pub fn pool_total_cached_blocks() -> usize {
    BLOCK_POOL.with(|pool| pool.borrow().free_lists.iter().map(|l| l.len()).sum())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldKind {
    /// Tagged FzValue bits. GC tracer follows this slot.
    FzValue,
    /// 8 bytes of raw f64 payload. GC tracer skips this slot. Introduced by
    /// fz-ul4.27.5.2 to let typed-float entry-frame params live as raw f64
    /// instead of as a tagged ptr to a heap-resident boxed float.
    RawF64,
    /// 8 bytes of raw i64 — an int payload with the tag/shift stripped.
    /// GC tracer skips this slot. Introduced by fz-ul4.27.5.3 so typed-int
    /// entry-frame params can live as raw i64 instead of the tagged
    /// `(n << 3) | TAG_INT` form, letting arithmetic ops skip the
    /// per-op sshr/ishl round trip.
    RawI64,
    /// Generic raw bytes — width in bytes. GC tracer skips this slot. Used
    /// by miscellaneous non-frame schemas (bitstrings, etc.) and reserved
    /// for VR.3.3 (raw i64 entry-param slots).
    RawBytes(u32),
}

#[derive(Debug, Clone)]
pub struct FieldDescriptor {
    pub offset: u32,
    pub kind: FieldKind,
}

#[derive(Debug, Clone)]
pub struct Schema {
    pub name: String,
    pub size: u32,
    pub fields: Vec<FieldDescriptor>,
}

impl Schema {
    /// fz-ul4.38 — canonical `Tuple{N}` schema. N FzValue slots at offsets
    /// 0, 8, 16, … Used by every path that registers tuple schemas: JIT
    /// codegen (`ir_codegen::compile_with_backend`), interp lazy
    /// registration (`ir_interp::interp_tuple_schema_id`), and the AOT
    /// startup hook (`aot_shim::fz_aot_setup`). Single source of truth.
    pub fn tuple_of_arity(arity: usize) -> Self {
        Self {
            name: format!("Tuple{}", arity),
            size: (arity * 8) as u32,
            fields: (0..arity)
                .map(|i| FieldDescriptor {
                    offset: (i * 8) as u32,
                    kind: FieldKind::FzValue,
                })
                .collect(),
        }
    }
}

pub struct SchemaRegistry {
    schemas: Vec<Schema>,
}

impl SchemaRegistry {
    pub fn new() -> Self {
        Self {
            schemas: Vec::new(),
        }
    }

    pub fn register(&mut self, schema: Schema) -> u32 {
        let id = self.schemas.len() as u32;
        self.schemas.push(schema);
        id
    }

    pub fn get(&self, id: u32) -> &Schema {
        &self.schemas[id as usize]
    }

    pub fn len(&self) -> usize {
        self.schemas.len()
    }

    pub fn is_empty(&self) -> bool {
        self.schemas.is_empty()
    }
}

impl Default for SchemaRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// fz-cty.5 — bitstrings above this many bytes are routed through the
/// shared zone (refcounted off-heap `SharedBin` + per-process `ProcBin`
/// stub) instead of being inlined on the per-process heap. Matches
/// BEAM's refc-binary threshold.
pub const SHARED_BIN_THRESHOLD_BYTES: usize = 64;

/// fz-q8d.4 — objects larger than the largest size_class are allocated as
/// their own system-allocator backed fragment, bypassing the bump arena.
/// Threshold is the largest entry of `SIZE_TABLE`; anything strictly
/// larger goes to fragments.
const FRAGMENT_THRESHOLD: usize = SIZE_TABLE[SIZE_TABLE.len() - 1];

/// fz-q8d.4 — a single oversized allocation outside the bump arena.
/// Participates in GC via a mark bit instead of being copied.
struct Fragment {
    ptr: *mut u8,
    size: usize,
    layout: Layout,
    mark: bool,
}

pub struct Heap {
    block_start: *mut u8,
    bump_top: *mut u8,
    block_end: *mut u8,
    block_size: usize,
    /// Index into SIZE_TABLE (§6.3, wired in fz-siu.9). Tracked here so
    /// proactive shrinkage can read/adjust it without growing the API.
    pub size_class: u8,
    /// 75% of `block_end`. Crossing this pointer in `alloc()` sets
    /// `FZ_SHOULD_YIELD` so the scheduler can run `gc_mid_flight` at the
    /// next back-edge yield point.
    pub gc_watermark: *mut u8,
    /// Exact live bytes after the most recent GC. Zero until the first GC.
    /// Used by `gc_mid_flight` and proactive shrinkage to size the to-space
    /// and detect low-live quiet periods.
    pub last_gc_live_bytes: usize,
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
    /// fz-q8d.1 — intrusive MSO ("Mixed Set / Off-heap") chain. Head of a
    /// singly-linked list of live `HeapKind::ProcBin` objects allocated on
    /// this heap; each ProcBin's `mso_next` slot stores the predecessor.
    /// The post-Cheney sweep (`procbin::mso_sweep`) rewrites entries to
    /// their to-space copies; `Heap::drop` calls `procbin::mso_drop_all`
    /// before pool reclaim so SharedBin references are balanced.
    pub mso_head: *mut HeapHeader,
    /// fz-4mk — pending dtor invocations. When an MSO sweep finds a
    /// `HeapKind::Resource` stub whose off-heap refcount transitioned to
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

impl Heap {
    pub fn new(capacity: usize, schemas: Rc<RefCell<SchemaRegistry>>) -> Self {
        assert!(
            capacity > 0 && capacity.is_multiple_of(16),
            "capacity must be 16-aligned"
        );
        let size_class = pick_size_class(capacity);
        let block_size = SIZE_TABLE[size_class as usize];
        let block_start = pool_alloc(size_class);
        let block_end = unsafe { block_start.add(block_size) };
        Self {
            block_start,
            bump_top: block_start,
            block_end,
            block_size,
            size_class,
            gc_watermark: watermark_for(block_start, block_size),
            last_gc_live_bytes: 0,
            abandoned_blocks: Vec::new(),
            schemas,
            pressure: std::sync::atomic::AtomicBool::new(false),
            // Default: half the block. Tunable per-Process for tests that
            // want to force the park-time GC hook to fire.
            gc_threshold_bytes: block_size / 2,
            gc_run_count: 0,
            alloc_count: 0,
            mso_head: std::ptr::null_mut(),
            pending_dtors: std::collections::VecDeque::new(),
            fragments: Vec::new(),
        }
    }

    pub fn should_gc(&self) -> bool {
        self.pressure.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub fn clear_should_gc_flag(&self) {
        self.pressure
            .store(false, std::sync::atomic::Ordering::Relaxed);
    }

    fn note_alloc_pressure(&self) {
        if self.bytes_used() >= self.gc_threshold_bytes {
            self.pressure
                .store(true, std::sync::atomic::Ordering::Relaxed);
        }
    }

    /// Bump-only allocator. Rounds `size` up to 16 and advances `bump_top`.
    /// On overflow, abandons the current block and allocates a fresh
    /// pool-backed block at the next size_class. The next park-time
    /// Cheney recycles the whole abandoned chain.
    ///
    /// fz-q8d.4 — objects larger than `FRAGMENT_THRESHOLD` (the last
    /// `SIZE_TABLE` entry, ~6 MiB) are allocated as system-allocator
    /// backed singletons attached to `self.fragments`. They don't move
    /// during Cheney; the collector marks them in place and frees
    /// survivors / unmarked fragments at sweep time.
    pub fn alloc(&mut self, size: usize) -> *mut HeapHeader {
        let size = (size + 15) & !15;
        assert!(size >= 16, "alloc must include at least the 16-byte header");
        // Oversize allocations route through the fragment path.
        if size > FRAGMENT_THRESHOLD {
            let layout = Layout::from_size_align(size, 16).expect("fragment layout");
            let ptr = unsafe { alloc_zeroed(layout) };
            assert!(!ptr.is_null(), "fragment allocation failed");
            self.fragments.push(Fragment {
                ptr,
                size,
                layout,
                mark: false,
            });
            self.alloc_count += 1;
            self.note_alloc_pressure();
            return ptr as *mut HeapHeader;
        }
        let new_top = unsafe { self.bump_top.add(size) };
        if new_top > self.block_end {
            // Grow: pick the smallest size_class > current that also fits
            // `size`. Allocate via the pool; abandon the current block
            // for Cheney/Drop to return.
            let want_for_alloc = pick_size_class(size);
            let bumped = self
                .size_class
                .saturating_add(1)
                .min((SIZE_TABLE.len() - 1) as u8);
            let new_class = want_for_alloc.max(bumped);
            let new_size = SIZE_TABLE[new_class as usize];
            self.abandoned_blocks
                .push((self.block_start, self.size_class));
            let new_block = pool_alloc(new_class);
            self.block_start = new_block;
            self.bump_top = new_block;
            self.block_end = unsafe { new_block.add(new_size) };
            self.block_size = new_size;
            self.size_class = new_class;
            self.gc_watermark = watermark_for(new_block, new_size);
        }
        let p = self.bump_top;
        self.bump_top = unsafe { self.bump_top.add(size) };
        self.alloc_count += 1;
        self.note_alloc_pressure();
        if self.bump_top >= self.gc_watermark {
            crate::yield_flag::FZ_SHOULD_YIELD.store(1, std::sync::atomic::Ordering::Relaxed);
        }
        p as *mut HeapHeader
    }

    pub fn alloc_struct(&mut self, schema_id: u32) -> *mut HeapHeader {
        let payload_size = self.schemas.borrow().get(schema_id).size as usize;
        let total = (16 + payload_size + 15) & !15;
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(
                p,
                HeapHeader {
                    kind: HeapKind::Struct as u16,
                    flags: 0,
                    size_bytes: total as u32,
                    schema_id,
                    _reserved: 0,
                },
            );
            // Zero payload.
            std::ptr::write_bytes((p as *mut u8).add(16), 0, total - 16);
        }
        p
    }

    pub fn alloc_list_cons(&mut self, head: FzValue, tail: FzValue) -> u64 {
        let p = self.alloc(16);
        let head = self.typed_from_fz_value(head);
        unsafe {
            std::ptr::write(p as *mut ListCons, ListCons::new(head, tail.0));
        }
        crate::fz_value::tagged_list_bits(p as *const u8)
    }

    pub fn typed_from_fz_value(&self, value: FzValue) -> TypedValue {
        if let Some(p) = crate::fz_value::list_addr_from_tagged(value.0)
            && !p.is_null()
            && self.contains_heap_addr(p as *mut u8)
        {
            return TypedValue::heap_ptr(p, ValueKind::LIST);
        }
        if let Some(p) = crate::fz_value::map_addr_from_tagged(value.0)
            && !p.is_null()
            && self.contains_heap_addr(p as *mut u8)
        {
            return TypedValue::heap_ptr(p, ValueKind::MAP);
        }
        if let Some(p) = crate::fz_value::closure_addr_from_tagged(value.0)
            && !p.is_null()
            && self.contains_heap_addr(p as *mut u8)
        {
            return TypedValue::heap_ptr(p, ValueKind::CLOSURE);
        }
        if matches!(
            value.tag(),
            crate::fz_value::Tag::Int | crate::fz_value::Tag::Atom
        ) {
            return TypedValue::from_legacy_fz_value(value.0);
        }
        if let Some(kind) = ValueKind::new((value.0 & crate::fz_value::TAG_MASK) as u8)
            && kind.is_heap()
        {
            let p = (value.0 & !crate::fz_value::TAG_MASK) as *mut HeapHeader;
            if !p.is_null() && self.contains_heap_addr(p as *mut u8) {
                return TypedValue::heap_ptr(p, kind);
            }
        }
        TypedValue::from_legacy_fz_value(value.0)
    }

    pub fn fz_value_from_typed(&mut self, value: TypedValue) -> FzValue {
        match value.kind {
            ValueKind::NULL => FzValue::NIL,
            ValueKind::LIST => {
                if value.raw == 0 {
                    FzValue::EMPTY_LIST
                } else {
                    FzValue(crate::fz_value::tagged_list_bits(value.raw as *const u8))
                }
            }
            ValueKind::MAP => FzValue(crate::fz_value::tagged_map_bits(value.raw as *const u8)),
            ValueKind::CLOSURE => {
                FzValue(crate::fz_value::tagged_closure_bits(value.raw as *const u8))
            }
            ValueKind::INT => FzValue::from_int(value.raw as i64),
            ValueKind::ATOM => FzValue::from_atom_id(value.raw as u32),
            ValueKind::FLOAT => FzValue::from_ptr(self.alloc_float(f64::from_bits(value.raw))),
            kind if kind.is_heap() => FzValue::from_ptr(value.raw as *mut HeapHeader),
            kind => panic!("cannot convert typed value kind {kind:?} to FzValue"),
        }
    }

    pub fn contains_heap_addr(&self, p: *mut u8) -> bool {
        (p >= self.block_start && p < self.block_end)
            || self
                .abandoned_blocks
                .iter()
                .any(|&(start, sc)| p >= start && p < unsafe { start.add(SIZE_TABLE[sc as usize]) })
            || classify_fragment(p, &self.fragments).is_some()
    }

    /// Map layout: count, padded tag bytes, raw keys, raw values. Caller
    /// supplies canonically-sorted typed entries; this performs the heap copy.
    pub fn alloc_map(&mut self, entries: &[(TypedValue, TypedValue)]) -> u64 {
        let total = crate::fz_value::map_size_for_count(entries.len());
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(p as *mut u64, entries.len() as u64);
            let tag_p = crate::fz_value::map_tag_ptr(p as *const u8);
            std::ptr::write_bytes(tag_p, 0, crate::fz_value::map_tag_bytes_len(entries.len()));
            let keys = crate::fz_value::map_keys_ptr(p as *const u8, entries.len());
            let values = crate::fz_value::map_values_ptr(p as *const u8, entries.len());
            for (i, (k, v)) in entries.iter().enumerate() {
                std::ptr::write(tag_p.add(i), crate::fz_value::map_pack_tag(k.kind, v.kind));
                std::ptr::write(keys.add(i), k.raw);
                std::ptr::write(values.add(i), v.raw);
            }
        }
        crate::fz_value::tagged_map_bits(p as *const u8)
    }

    /// Bitstring layout: HeapHeader (16) + bit_len: u64 (8) + bytes (padded
    /// to 16). Caller supplies a fully-built byte buffer + bit_len; this
    /// performs the heap copy.
    ///
    /// fz-cty.5 — payloads larger than `SHARED_BIN_THRESHOLD_BYTES` route
    /// through the shared zone: a SharedBin is allocated off-heap and the
    /// per-process heap gets a 32-byte `HeapKind::ProcBin` stub referencing
    /// it. Render and bit-match dispatch on kind via
    /// `bitstring_bit_len` / `bitstring_byte_ptr`.
    pub fn alloc_bitstring(&mut self, bytes: &[u8], bit_len: u64) -> *mut HeapHeader {
        if bytes.len() > SHARED_BIN_THRESHOLD_BYTES {
            let handle = SharedBinHandle::from_bytes(bytes, bit_len);
            return alloc_procbin(self, handle).as_raw();
        }
        // fz-wu9 — reserve at least 1 byte past the payload for the
        // invisible trailing NUL. The pad-zeroing below guarantees it reads
        // as 0; bytes_len / bit_len are unchanged.
        let total = (16 + 8 + bytes.len() + 1 + 15) & !15;
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(
                p,
                HeapHeader {
                    kind: HeapKind::Bitstring as u16,
                    flags: 0,
                    size_bytes: total as u32,
                    schema_id: 0,
                    _reserved: 0,
                },
            );
            // bit_len at offset 16, then byte payload at offset 24.
            let bit_len_p = (p as *mut u8).add(16) as *mut u64;
            std::ptr::write(bit_len_p, bit_len);
            let bytes_p = (p as *mut u8).add(24);
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), bytes_p, bytes.len());
            // Zero the trailing padding so renders / debug aren't garbage.
            let pad_start = 24 + bytes.len();
            if pad_start < total {
                std::ptr::write_bytes((p as *mut u8).add(pad_start), 0, total - pad_start);
            }
        }
        p
    }

    /// Strict Closure layout (vrx.A.4):
    ///   `schema_id: u32, flags: u32, fn_ptr: u64, captures: [FzValue; n]`.
    ///
    /// The legacy `_reserved` fn-id is preserved in `schema_id`; current
    /// closure captures remain uniform tagged FzValue slots so the existing
    /// closure-target ABI and GC edge walk stay coherent.
    pub fn alloc_closure_slots(
        &mut self,
        schema_id: u32,
        captured_count: usize,
        halt_kind: u16,
    ) -> u64 {
        assert!(
            captured_count <= crate::fz_value::CLOSURE_FLAGS_CAPTURED_MASK as usize,
            "closure captured count overflow"
        );
        let total = crate::fz_value::closure_size_for_count(captured_count);
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(p as *mut u32, schema_id);
            std::ptr::write(
                (p as *mut u8).add(4) as *mut u32,
                crate::fz_value::closure_flags_pack(captured_count as u16, halt_kind) as u32,
            );
            std::ptr::write((p as *mut u8).add(8) as *mut u64, 0);
            if total > 16 {
                std::ptr::write_bytes((p as *mut u8).add(16), 0, total - 16);
            }
        }
        crate::fz_value::tagged_closure_bits(p as *const u8)
    }

    pub fn alloc_closure(
        &mut self,
        schema_id: u32,
        captured_count: usize,
        halt_kind: u16,
        fn_ptr: u64,
        captures: &[FzValue],
    ) -> u64 {
        assert!(
            captures.len() <= captured_count,
            "too many closure captures"
        );
        let bits = self.alloc_closure_slots(schema_id, captured_count, halt_kind);
        let p = crate::fz_value::closure_addr_from_tagged(bits).expect("new closure ptr");
        unsafe {
            std::ptr::write((p as *mut u8).add(8) as *mut u64, fn_ptr);
            for (i, capture) in captures.iter().enumerate() {
                std::ptr::write(
                    crate::fz_value::closure_capture_slot(p as *const u8, i),
                    *capture,
                );
            }
        }
        bits
    }

    /// Vec layout (all kinds): `HeapHeader (16) + len: u32 (4) + pad: u32 (4)
    ///   + raw_payload (16-byte aligned)`. Kind in the header, payload pure
    ///     raw data so SIMD codegen can address it uniformly. Returns the
    ///     header pointer with header + len written; payload is zeroed and the
    ///     caller writes element bytes directly at offset 24.
    fn alloc_vec_raw(&mut self, kind: HeapKind, len: u32, payload_bytes: usize) -> *mut HeapHeader {
        let total = (24 + payload_bytes + 15) & !15;
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(
                p,
                HeapHeader {
                    kind: kind as u16,
                    flags: 0,
                    size_bytes: total as u32,
                    schema_id: 0,
                    _reserved: 0,
                },
            );
            // len at offset 16 (u32); pad u32 at offset 20.
            std::ptr::write((p as *mut u8).add(16) as *mut u32, len);
            std::ptr::write((p as *mut u8).add(20) as *mut u32, 0);
            // Zero payload + any 16-alignment trailing pad.
            std::ptr::write_bytes((p as *mut u8).add(24), 0, total - 24);
        }
        p
    }

    /// Boxed float layout: `HeapHeader (16) + f64 (8) + pad (8)` = 32 bytes.
    /// Returned ptr is FzValue ptr-tagged (low 4 bits zero by alignment).
    pub fn alloc_float(&mut self, value: f64) -> *mut HeapHeader {
        let p = self.alloc(32);
        unsafe {
            std::ptr::write(
                p,
                HeapHeader {
                    kind: HeapKind::Float as u16,
                    flags: 0,
                    size_bytes: 32,
                    schema_id: 0,
                    _reserved: 0,
                },
            );
            std::ptr::write((p as *mut u8).add(16) as *mut f64, value);
            std::ptr::write_bytes((p as *mut u8).add(24), 0, 8);
        }
        p
    }

    /// Read the f64 payload of a `HeapKind::Float` object.
    pub fn read_float(p: *const HeapHeader) -> f64 {
        unsafe { std::ptr::read((p as *const u8).add(16) as *const f64) }
    }

    pub fn alloc_vec_i64(&mut self, elements: &[i64]) -> *mut HeapHeader {
        let p = self.alloc_vec_raw(HeapKind::VecI64, elements.len() as u32, elements.len() * 8);
        unsafe {
            let payload = (p as *mut u8).add(24) as *mut i64;
            std::ptr::copy_nonoverlapping(elements.as_ptr(), payload, elements.len());
        }
        p
    }

    pub fn alloc_vec_u8(&mut self, elements: &[u8]) -> *mut HeapHeader {
        let p = self.alloc_vec_raw(HeapKind::VecU8, elements.len() as u32, elements.len());
        unsafe {
            let payload = (p as *mut u8).add(24);
            std::ptr::copy_nonoverlapping(elements.as_ptr(), payload, elements.len());
        }
        p
    }

    /// Pack `bits` MSB-first into bytes (matches `bitstr::BitWriter`).
    pub fn alloc_vec_bit(&mut self, bits: &[bool]) -> *mut HeapHeader {
        let nbytes = bits.len().div_ceil(8);
        let p = self.alloc_vec_raw(HeapKind::VecBit, bits.len() as u32, nbytes);
        unsafe {
            let payload = (p as *mut u8).add(24);
            for (i, &b) in bits.iter().enumerate() {
                if b {
                    let byte_idx = i / 8;
                    let bit_idx = 7 - (i % 8);
                    *payload.add(byte_idx) |= 1 << bit_idx;
                }
            }
        }
        p
    }

    /// Read `len` field (offset 16) of any heap vec.
    pub fn vec_len(p: *const HeapHeader) -> u32 {
        unsafe { std::ptr::read((p as *const u8).add(16) as *const u32) }
    }

    /// Write an FzValue into a Struct's payload at the given field offset.
    pub fn write_field(&self, obj: *mut HeapHeader, field_offset: u32, value: FzValue) {
        unsafe {
            let p = (obj as *mut u8).add(16).add(field_offset as usize) as *mut FzValue;
            std::ptr::write(p, value);
        }
    }

    /// Read an FzValue from a Struct's payload at the given field offset.
    pub fn read_field(&self, obj: *mut HeapHeader, field_offset: u32) -> FzValue {
        unsafe {
            let p = (obj as *mut u8).add(16).add(field_offset as usize) as *const FzValue;
            std::ptr::read(p)
        }
    }

    /// Register a schema in this heap's registry, returning its id. Codegen
    /// uses this to register tuple-arity / closure / record schemas at JIT
    /// compile time so the tracer can walk their FzValue fields.
    pub fn register_schema(&self, schema: Schema) -> u32 {
        self.schemas.borrow_mut().register(schema)
    }

    /// Borrow the SchemaRegistry handle. Used by render paths that need to
    /// know a struct's arity / field layout from its schema_id.
    pub fn schemas_registry(&self) -> Rc<RefCell<SchemaRegistry>> {
        self.schemas.clone()
    }

    /// Total allocations made on this heap (since last GC). Under the
    /// fz-siu.7 stub GC, all allocations remain "live" because nothing is
    /// reclaimed. .8's Cheney pass resets this to the surviving-object
    /// count after each copy.
    pub fn live_count(&self) -> usize {
        self.alloc_count as usize
    }

    /// Always zero under bump-only. Retained for back-compat with tests
    /// asserting freelist invariants; .8 / .9 may remove entirely.
    pub fn freelist_len(&self) -> usize {
        0
    }

    /// Bytes consumed across the current block + every abandoned block.
    /// Tracks total memory footprint, not "logically live" data.
    pub fn bytes_used(&self) -> usize {
        let current = unsafe { self.bump_top.offset_from(self.block_start) } as usize;
        let abandoned: usize = self
            .abandoned_blocks
            .iter()
            .map(|(_, sc)| SIZE_TABLE[*sc as usize])
            .sum();
        // fz-q8d.4 — include fragment sizes so allocation pressure
        // accounting reflects the full per-heap footprint.
        let fragments: usize = self.fragments.iter().map(|f| f.size).sum();
        current + abandoned + fragments
    }

    /// Park-time Cheney GC (§6.4). Single-root by design: §7 establishes
    /// that the only fz-side reference into the arena at park-time is the
    /// process's `parked_cont`. The caller passes that field by mutable
    /// pointer; on return it is updated to the to-space copy (or left null
    /// if it was null on entry — nothing to trace, just recycle blocks).
    ///
    /// Algorithm: standard Cheney two-finger BFS. Allocate a to-space block
    /// at the chosen size_class (§6.3 / §6.5 picker), copy the root, then
    /// scan to-space objects breadth-first, forwarding each from-space
    /// child pointer to its newly-copied address. Off-heap pointers
    /// (static-closure / halt-cont singletons) are detected by an
    /// in-from-space range check and left untouched.
    pub fn gc(&mut self, root_slot: &mut *mut u8) {
        self.gc_with_extra_roots(root_slot, &mut []);
    }

    /// Cheney GC with an optional slice of extra root FzValues (for mid-flight
    /// roots and mailbox items). Each element is forwarded in-place.
    pub fn gc_with_extra_roots(
        &mut self,
        root_slot: &mut *mut u8,
        extra_roots: &mut [crate::fz_value::FzValue],
    ) {
        // Snapshot from-space block ranges before we allocate to-space.
        let mut from_ranges: Vec<(*mut u8, *mut u8)> =
            Vec::with_capacity(1 + self.abandoned_blocks.len());
        from_ranges.push((self.block_start, self.block_end));
        for &(p, sc) in &self.abandoned_blocks {
            from_ranges.push((p, unsafe { p.add(SIZE_TABLE[sc as usize]) }));
        }

        // fz-q8d.4 — reset fragment marks at the start of each GC.
        for f in &mut self.fragments {
            f.mark = false;
        }

        // Pick to-space size: first GC uses bytes_used() as upper bound;
        // subsequent GCs use last_gc_live_bytes * 2 (50% post-GC target).
        // Fragment bytes are excluded from the bump-arena sizing because
        // fragments don't get copied into to-space.
        let bump_live_for_sizing = if self.last_gc_live_bytes > 0 {
            self.last_gc_live_bytes.saturating_mul(2)
        } else {
            self.bytes_used()
                .saturating_sub(self.fragments.iter().map(|f| f.size).sum())
        };
        let size_class = pick_size_class(bump_live_for_sizing.max(SIZE_TABLE[0]));
        let to_size = SIZE_TABLE[size_class as usize];
        let to_start = pool_alloc(size_class);
        let to_end = unsafe { to_start.add(to_size) };
        let mut free = to_start;
        let mut frag_queue: Vec<*mut HeapHeader> = Vec::new();
        let mut copied_objects: Vec<CopiedObject> = Vec::new();

        if !root_slot.is_null() {
            let root_bits = *root_slot as u64;
            if let Some(p) = crate::fz_value::closure_addr_from_tagged(root_bits) {
                if ptr_in_from_space(p as *mut u8, &from_ranges)
                    || classify_fragment(p as *mut u8, &self.fragments).is_some()
                {
                    let new_root = cheney_forward_tagged(
                        p,
                        crate::fz_value::TAG_CLOSURE,
                        crate::fz_value::object_size(root_bits),
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &mut copied_objects,
                    );
                    *root_slot =
                        crate::fz_value::tagged_closure_bits(new_root as *const u8) as *mut u8;
                }
            } else {
                let new_root = cheney_forward(
                    *root_slot as *mut HeapHeader,
                    &from_ranges,
                    &mut self.fragments,
                    &mut frag_queue,
                    &mut free,
                    to_end,
                    &mut copied_objects,
                );
                *root_slot = new_root as *mut u8;
            }
        }

        // Forward extra roots (mid-flight args, mailbox items).
        for v in extra_roots.iter_mut() {
            if let Some(p) = crate::fz_value::map_addr_from_tagged(v.0)
                && !p.is_null()
                && (ptr_in_from_space(p as *mut u8, &from_ranges)
                    || classify_fragment(p as *mut u8, &self.fragments).is_some())
            {
                let new_p = cheney_forward_tagged(
                    p,
                    crate::fz_value::TAG_MAP,
                    crate::fz_value::object_size(v.0),
                    &mut self.fragments,
                    &mut frag_queue,
                    &mut free,
                    to_end,
                    &mut copied_objects,
                );
                *v = crate::fz_value::FzValue(crate::fz_value::tagged_map_bits(new_p as *const u8));
                continue;
            }
            if let Some(p) = crate::fz_value::list_addr_from_tagged(v.0)
                && !p.is_null()
                && (ptr_in_from_space(p as *mut u8, &from_ranges)
                    || classify_fragment(p as *mut u8, &self.fragments).is_some())
            {
                let new_p = cheney_forward_list(
                    p,
                    &mut self.fragments,
                    &mut frag_queue,
                    &mut free,
                    to_end,
                    &mut copied_objects,
                );
                *v =
                    crate::fz_value::FzValue(crate::fz_value::tagged_list_bits(new_p as *const u8));
                continue;
            }
            if let Some(p) = crate::fz_value::closure_addr_from_tagged(v.0)
                && !p.is_null()
                && (ptr_in_from_space(p as *mut u8, &from_ranges)
                    || classify_fragment(p as *mut u8, &self.fragments).is_some())
            {
                let new_p = cheney_forward_tagged(
                    p,
                    crate::fz_value::TAG_CLOSURE,
                    crate::fz_value::object_size(v.0),
                    &mut self.fragments,
                    &mut frag_queue,
                    &mut free,
                    to_end,
                    &mut copied_objects,
                );
                *v = crate::fz_value::FzValue(crate::fz_value::tagged_closure_bits(
                    new_p as *const u8,
                ));
                continue;
            }
            if let Some(p) = v.unbox_ptr()
                && !p.is_null()
                && (ptr_in_from_space(p as *mut u8, &from_ranges)
                    || classify_fragment(p as *mut u8, &self.fragments).is_some())
            {
                let new_p = cheney_forward(
                    p,
                    &from_ranges,
                    &mut self.fragments,
                    &mut frag_queue,
                    &mut free,
                    to_end,
                    &mut copied_objects,
                );
                *v = crate::fz_value::FzValue::from_ptr(new_p);
            }
        }

        // Mixed-mode BFS: alternately drain to-space scan and frag_queue
        // until both are empty. Fragments traced in frag_queue may push
        // new to-space objects (their children); newly-traced to-space
        // objects may push new fragments. Loop until no work left.
        let schemas = self.schemas.borrow();
        let mut scan_idx = 0usize;
        loop {
            // Drain to-space BFS frontier.
            while scan_idx < copied_objects.len() {
                let copied = copied_objects[scan_idx];
                scan_idx += 1;
                match copied.tag {
                    crate::fz_value::TAG_LIST => cheney_trace_list(
                        copied.ptr as *mut ListCons,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &mut copied_objects,
                    ),
                    crate::fz_value::TAG_MAP => cheney_trace_map(
                        copied.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &mut copied_objects,
                    ),
                    crate::fz_value::TAG_CLOSURE => cheney_trace_closure(
                        copied.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &mut copied_objects,
                    ),
                    _ => cheney_trace_children(
                        copied.ptr as *mut HeapHeader,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                    ),
                }
            }
            // Drain fragment queue. Each fragment's children may forward
            // either into to-space (which extends `free`, picked up by
            // the loop above on the next iteration) or into another
            // fragment (re-pushes to frag_queue).
            if let Some(frag_ptr) = frag_queue.pop() {
                cheney_trace_children(
                    frag_ptr,
                    &from_ranges,
                    &mut self.fragments,
                    &mut frag_queue,
                    &mut free,
                    to_end,
                    &schemas,
                    &mut copied_objects,
                );
                continue;
            }
            break;
        }
        drop(schemas);

        // fz-q8d.1 — MSO sweep walks the intrusive chain. Survivors get
        // rewritten to their to-space copies; dead entries release their
        // SharedBin reference. Must run before `pool_free` below because
        // it dereferences from-space ProcBins (specifically their
        // mso_next link, which Cheney never overwrites).
        mso_sweep(self);

        // fz-q8d.4 — fragment sweep: free unmarked fragments, count
        // survivors into live_count, and reset marks on those that
        // remain. `swap_remove` is safe because order doesn't matter.
        let mut live_count = copied_objects.len() as u64;
        let mut i = 0;
        while i < self.fragments.len() {
            if self.fragments[i].mark {
                self.fragments[i].mark = false;
                live_count += 1;
                i += 1;
            } else {
                let f = self.fragments.swap_remove(i);
                unsafe { dealloc(f.ptr, f.layout) };
            }
        }

        // Return old from-space (current + abandoned) to the pool (§6.6).
        pool_free(self.block_start, self.size_class);
        for (p, sc) in self.abandoned_blocks.drain(..) {
            pool_free(p, sc);
        }

        // Install to-space as the new current block.
        self.block_start = to_start;
        self.bump_top = free;
        self.block_end = to_end;
        self.block_size = to_size;
        self.size_class = size_class;
        self.alloc_count = live_count;
        self.gc_run_count += 1;
        self.gc_threshold_bytes = to_size / 2;
        self.gc_watermark = watermark_for(to_start, to_size);
        self.last_gc_live_bytes = unsafe { free.offset_from(to_start) } as usize;
    }

    /// Mid-flight GC: Cheney with `mid_flight_roots` slab + mailbox as roots.
    /// Called by the scheduler when `FZ_SHOULD_YIELD` was set and the process
    /// yields at a back-edge. `parked_cont` is null (process is mid-flight).
    pub fn gc_mid_flight(
        &mut self,
        roots: &mut [crate::fz_value::FzValue],
        mailbox: &mut std::collections::VecDeque<crate::fz_value::FzValue>,
    ) {
        let mut null_root: *mut u8 = std::ptr::null_mut();
        // Collect mailbox into a temporary vec for forwarding, then write back.
        let mb_vec: Vec<crate::fz_value::FzValue> = mailbox.drain(..).collect();
        let mut all_extras: Vec<crate::fz_value::FzValue> = roots
            .iter()
            .copied()
            .chain(mb_vec.iter().copied())
            .collect();
        self.gc_with_extra_roots(&mut null_root, &mut all_extras);
        // Write forwarded values back to roots slab and mailbox.
        let n = roots.len();
        roots.copy_from_slice(&all_extras[..n]);
        for v in &all_extras[n..] {
            mailbox.push_back(*v);
        }
        drop(mb_vec);
    }
}

/// Compute the 75%-of-block watermark pointer.
fn watermark_for(block_start: *mut u8, block_size: usize) -> *mut u8 {
    let offset = (block_size * 3) / 4;
    unsafe { block_start.add(offset) }
}

/// Forward a from-space pointer. For a block-resident object: copy to
/// `*free` and install a forwarding marker in the from-header (or
/// return the already-installed forwarded pointer). For a fragment-
/// resident object: set the fragment's mark bit and (on the false→true
/// transition) push the pointer onto `frag_queue`; the pointer is
/// returned unchanged because fragments do not move.
fn cheney_forward(
    p: *mut HeapHeader,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<*mut HeapHeader>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
) -> *mut HeapHeader {
    // fz-q8d.4 — fragment path. Fragments don't move; mark in place
    // and push to the queue on first visit so children get traced.
    if let Some(idx) = classify_fragment(p as *mut u8, fragments) {
        if !fragments[idx].mark {
            fragments[idx].mark = true;
            frag_queue.push(p);
        }
        return p;
    }
    // Block-resident path: standard Cheney copy + forward.
    let h = unsafe { &*p };
    if h.kind == FORWARDED_KIND {
        let fwd = unsafe { std::ptr::read((p as *const u8).add(8) as *const u64) };
        return fwd as *mut HeapHeader;
    }
    let size = h.size_bytes as usize;
    let dst = *free;
    let new_top = unsafe { dst.add(size) };
    assert!(new_top <= to_end, "Cheney: to-space exhausted");
    unsafe {
        std::ptr::copy_nonoverlapping(p as *const u8, dst, size);
    }
    *free = new_top;
    unsafe {
        std::ptr::write(p as *mut u16, FORWARDED_KIND);
        std::ptr::write((p as *mut u8).add(8) as *mut u64, dst as u64);
    }
    copied_objects.push(CopiedObject { ptr: dst, tag: 0 });
    let _ = from_ranges; // retained in signature for symmetry; not consulted here
    dst as *mut HeapHeader
}

fn cheney_forward_list(
    p: *mut HeapHeader,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<*mut HeapHeader>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
) -> *mut HeapHeader {
    if let Some(idx) = classify_fragment(p as *mut u8, fragments) {
        if !fragments[idx].mark {
            fragments[idx].mark = true;
            frag_queue.push(p);
        }
        return p;
    }
    if let Some(fwd) = is_forwarded_list(p as *const u8) {
        return fwd as *mut HeapHeader;
    }
    let size = 16;
    let dst = *free;
    let new_top = unsafe { dst.add(size) };
    assert!(new_top <= to_end, "Cheney: to-space exhausted");
    unsafe {
        std::ptr::copy_nonoverlapping(p as *const u8, dst, size);
    }
    *free = new_top;
    unsafe {
        std::ptr::write(
            p as *mut u64,
            (dst as u64 & !crate::fz_value::TAG_MASK) | crate::fz_value::TAG_FWD,
        );
        std::ptr::write((p as *mut u8).add(8) as *mut u64, crate::fz_value::TAG_FWD);
    }
    copied_objects.push(CopiedObject {
        ptr: dst,
        tag: crate::fz_value::TAG_LIST,
    });
    dst as *mut HeapHeader
}

fn cheney_forward_tagged(
    p: *mut HeapHeader,
    tag: u64,
    size: usize,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<*mut HeapHeader>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
) -> *mut HeapHeader {
    if let Some(idx) = classify_fragment(p as *mut u8, fragments) {
        if !fragments[idx].mark {
            fragments[idx].mark = true;
            frag_queue.push(p);
        }
        return p;
    }
    if let Some(fwd) = is_forwarded_headerless(p as *const u8) {
        return fwd as *mut HeapHeader;
    }
    let dst = *free;
    let new_top = unsafe { dst.add(size) };
    assert!(new_top <= to_end, "Cheney: to-space exhausted");
    unsafe {
        std::ptr::copy_nonoverlapping(p as *const u8, dst, size);
    }
    *free = new_top;
    unsafe {
        std::ptr::write(
            p as *mut u64,
            (dst as u64 & !crate::fz_value::TAG_MASK) | crate::fz_value::TAG_FWD,
        );
        std::ptr::write((p as *mut u8).add(8) as *mut u64, crate::fz_value::TAG_FWD);
    }
    copied_objects.push(CopiedObject { ptr: dst, tag });
    dst as *mut HeapHeader
}

fn is_forwarded_list(addr: *const u8) -> Option<*const u8> {
    let marker = unsafe { std::ptr::read(addr as *const u64) };
    if marker & crate::fz_value::TAG_MASK != crate::fz_value::TAG_FWD {
        return None;
    }
    let link_marker = unsafe { std::ptr::read(addr.add(8) as *const u64) };
    if link_marker & crate::fz_value::TAG_MASK == crate::fz_value::TAG_FWD {
        Some((marker & !crate::fz_value::TAG_MASK) as *const u8)
    } else {
        None
    }
}

fn is_forwarded_headerless(addr: *const u8) -> Option<*const u8> {
    let marker = unsafe { std::ptr::read(addr as *const u64) };
    if marker & crate::fz_value::TAG_MASK != crate::fz_value::TAG_FWD {
        return None;
    }
    let confirm = unsafe { std::ptr::read(addr.add(8) as *const u64) };
    let forwarded = marker & !crate::fz_value::TAG_MASK;
    if confirm == crate::fz_value::TAG_FWD && forwarded != 0 {
        Some(forwarded as *const u8)
    } else {
        None
    }
}

/// Return the index of the fragment containing `p`, if any.
fn classify_fragment(p: *mut u8, fragments: &[Fragment]) -> Option<usize> {
    fragments
        .iter()
        .position(|f| p >= f.ptr && p < unsafe { f.ptr.add(f.size) })
}

/// Trace every FzValue child of a to-space object, forwarding each
/// from-space pointer it contains. Off-heap (static-closure / halt-cont)
/// pointers are detected by range and left untouched.
#[allow(clippy::too_many_arguments)]
fn cheney_trace_children(
    obj: *mut HeapHeader,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<*mut HeapHeader>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
) {
    let kind = HeapKind::from_u16(unsafe { (*obj).kind }).unwrap_or_else(|| {
        panic!("Cheney scan: invalid HeapKind {:#x}", unsafe {
            (*obj).kind
        },)
    });
    match kind {
        HeapKind::Struct => {
            let schema_id = unsafe { (*obj).schema_id };
            let schema = schemas.get(schema_id);
            for f in &schema.fields {
                if let FieldKind::FzValue = f.kind {
                    let slot =
                        unsafe { (obj as *mut u8).add(16).add(f.offset as usize) as *mut FzValue };
                    forward_field(
                        slot,
                        from_ranges,
                        fragments,
                        frag_queue,
                        free,
                        to_end,
                        copied_objects,
                    );
                }
            }
        }
        HeapKind::List => unreachable!("new List cells are traced by cheney_trace_list"),
        HeapKind::Closure => {
            // Layout: stub_fp (8) at offset 16 — a code pointer, skip.
            // Captures at offset 24+i*8 — FzValue each. `flags` low 14 bits
            // are the captured count; high 2 bits are halt_kind (fz-22.6).
            let count = crate::fz_value::closure_flags_captured(unsafe { (*obj).flags }) as usize;
            for i in 0..count {
                let slot = unsafe { (obj as *mut u8).add(24).add(i * 8) as *mut FzValue };
                forward_field(
                    slot,
                    from_ranges,
                    fragments,
                    frag_queue,
                    free,
                    to_end,
                    copied_objects,
                );
            }
        }
        HeapKind::Map => {
            unreachable!("new Map cells are traced by cheney_trace_map")
        }
        HeapKind::Bitstring
        | HeapKind::Float
        | HeapKind::VecI64
        | HeapKind::VecF64
        | HeapKind::VecU8
        | HeapKind::VecBit
        | HeapKind::ProcBin => {
            // Raw payload, no FzValue children. For ProcBin the +16 payload
            // is a refcounted off-heap pointer; the MSO sweep handles that
            // edge separately.
        }
        HeapKind::Resource => {
            // Off-heap refcounted shared_ptr at +16 (handled by MSO sweep).
            // fz-4mk — dtor closure FzValue at +24; trace like any other
            // heap edge so the closure survives Cheney for deferred dispatch.
            let closure_slot = unsafe { (obj as *mut u8).add(24) as *mut FzValue };
            forward_field(
                closure_slot,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                copied_objects,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cheney_trace_list(
    obj: *mut ListCons,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<*mut HeapHeader>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
) {
    let cons = unsafe { &mut *obj };
    if cons.head_kind().is_heap() {
        let mut head_bits = FzValue(cons.head | cons.head_kind().tag() as u64);
        forward_field(
            &mut head_bits as *mut FzValue,
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
        );
        cons.head = head_bits.0 & !crate::fz_value::TAG_MASK;
    }

    let tail_addr = cons.tail_addr();
    if tail_addr != 0 {
        let mut tail_bits = FzValue(tail_addr | crate::fz_value::TAG_LIST);
        forward_field(
            &mut tail_bits as *mut FzValue,
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
        );
        let new_tail_addr = tail_bits.0 & !crate::fz_value::TAG_MASK;
        cons.link = new_tail_addr | cons.head_kind().tag() as u64;
    }
}

#[allow(clippy::too_many_arguments)]
fn cheney_trace_map(
    obj: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<*mut HeapHeader>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
) {
    let count = unsafe { crate::fz_value::map_count(obj as *const u8) };
    let tags = unsafe { crate::fz_value::map_tag_ptr(obj as *const u8) };
    let keys = unsafe { crate::fz_value::map_keys_ptr(obj as *const u8, count) };
    let values = unsafe { crate::fz_value::map_values_ptr(obj as *const u8, count) };
    for i in 0..count {
        let tag = unsafe { std::ptr::read(tags.add(i)) };
        let key_kind = crate::fz_value::map_key_kind(tag);
        if key_kind.is_heap() {
            let mut key_bits =
                FzValue(unsafe { std::ptr::read(keys.add(i)) } | key_kind.tag() as u64);
            forward_field(
                &mut key_bits,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                copied_objects,
            );
            unsafe { std::ptr::write(keys.add(i), key_bits.0 & !crate::fz_value::TAG_MASK) };
        }
        let value_kind = crate::fz_value::map_value_kind(tag);
        if value_kind.is_heap() {
            let mut value_bits =
                FzValue(unsafe { std::ptr::read(values.add(i)) } | value_kind.tag() as u64);
            forward_field(
                &mut value_bits,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                copied_objects,
            );
            unsafe { std::ptr::write(values.add(i), value_bits.0 & !crate::fz_value::TAG_MASK) };
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cheney_trace_closure(
    obj: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<*mut HeapHeader>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
) {
    let count = unsafe { crate::fz_value::closure_captured_count(obj as *const u8) };
    for i in 0..count {
        let slot = unsafe { crate::fz_value::closure_capture_slot(obj as *const u8, i) };
        forward_field(
            slot,
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
        );
    }
}

/// For one FzValue slot in a to-space (or fragment) object: if it holds
/// a Ptr-tagged pointer into from-space (block or fragment), forward
/// the target and rewrite the slot to the new location. Block-resident
/// targets get copied to to-space; fragment-resident targets stay put
/// (mark + queue). Off-heap and scalar values pass through.
#[allow(clippy::too_many_arguments)]
fn forward_field(
    slot: *mut FzValue,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<*mut HeapHeader>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
) {
    let v = unsafe { std::ptr::read(slot) };
    if let Some(p) = crate::fz_value::map_addr_from_tagged(v.0) {
        if p.is_null() {
            return;
        }
        let in_block = ptr_in_from_space(p as *mut u8, from_ranges);
        let in_frag = classify_fragment(p as *mut u8, fragments).is_some();
        if !in_block && !in_frag {
            return;
        }
        let new = cheney_forward_tagged(
            p,
            crate::fz_value::TAG_MAP,
            crate::fz_value::object_size(v.0),
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
        );
        unsafe {
            std::ptr::write(
                slot,
                FzValue(crate::fz_value::tagged_map_bits(new as *const u8)),
            );
        }
        return;
    }
    if let Some(p) = crate::fz_value::list_addr_from_tagged(v.0) {
        if p.is_null() {
            return;
        }
        let in_block = ptr_in_from_space(p as *mut u8, from_ranges);
        let in_frag = classify_fragment(p as *mut u8, fragments).is_some();
        if !in_block && !in_frag {
            return;
        }
        let new = cheney_forward_list(p, fragments, frag_queue, free, to_end, copied_objects);
        unsafe {
            std::ptr::write(
                slot,
                FzValue(crate::fz_value::tagged_list_bits(new as *const u8)),
            );
        }
        return;
    }
    if let Some(p) = crate::fz_value::closure_addr_from_tagged(v.0) {
        if p.is_null() {
            return;
        }
        let in_block = ptr_in_from_space(p as *mut u8, from_ranges);
        let in_frag = classify_fragment(p as *mut u8, fragments).is_some();
        if !in_block && !in_frag {
            return;
        }
        let new = cheney_forward_tagged(
            p,
            crate::fz_value::TAG_CLOSURE,
            crate::fz_value::object_size(v.0),
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
        );
        unsafe {
            std::ptr::write(
                slot,
                FzValue(crate::fz_value::tagged_closure_bits(new as *const u8)),
            );
        }
        return;
    }
    let p = match v.unbox_ptr() {
        Some(p) => p,
        None => return,
    };
    if p.is_null() {
        return;
    }
    let in_block = ptr_in_from_space(p as *mut u8, from_ranges);
    let in_frag = classify_fragment(p as *mut u8, fragments).is_some();
    if !in_block && !in_frag {
        return; // off-heap singleton (static closure / halt cont)
    }
    let new = cheney_forward(
        p,
        from_ranges,
        fragments,
        frag_queue,
        free,
        to_end,
        copied_objects,
    );
    unsafe {
        std::ptr::write(slot, FzValue::from_ptr(new));
    }
}

fn ptr_in_from_space(p: *mut u8, from_ranges: &[(*mut u8, *mut u8)]) -> bool {
    from_ranges
        .iter()
        .any(|&(start, end)| p >= start && p < end)
}

/// Count objects in a contiguous to-space range by walking 16-byte-header
/// records. Used to update `alloc_count` post-trace.
fn count_objects_in_range(start: *mut u8, end: *mut u8) -> usize {
    let mut p = start;
    let mut n = 0;
    while p < end {
        let h = p as *mut HeapHeader;
        let size = unsafe { (*h).size_bytes as usize };
        debug_assert!(size > 0 && size % 16 == 0);
        p = unsafe { p.add(size) };
        n += 1;
    }
    n
}

impl Drop for Heap {
    fn drop(&mut self) {
        // fz-q8d.1 — release every SharedBin held via the intrusive MSO
        // chain. Order matters: must run before pool_free below, since
        // mso_drop_all walks ProcBin payloads in the from-space blocks.
        mso_drop_all(self);
        // fz-q8d.4 — free every fragment outright. Fragments are
        // system-allocator backed; no pool involvement.
        for f in self.fragments.drain(..) {
            unsafe { dealloc(f.ptr, f.layout) };
        }
        // Return blocks to the pool (§6.6) instead of free'ing. Next
        // spawn pulls from the same class — no per-spawn malloc.
        pool_free(self.block_start, self.size_class);
        for (p, sc) in self.abandoned_blocks.drain(..) {
            pool_free(p, sc);
        }
    }
}

/// fz-ul4.19.3: Deep-copy `src` from `src_heap` into `dst_heap`,
/// returning the FzValue that points into the destination. Shares of the
/// same source object are preserved in the destination via a forwarding
/// map (caller-supplied so multiple `deep_copy_value` calls during a
/// single send can share state for nested message construction).
///
/// v1 HeapKind coverage:
///   - List, Struct (covers tuples + closures by HeapKind classification),
///     Bitstring, Float, Map: supported.
///   - VecI64 / VecF64 / VecU8 / VecBit: supported (raw payload copy).
///   - Closure: supported via Struct-style FzValue captured-slot walk.
///
/// Scalar leaves (Int, Atom, Special) pass through unchanged.
pub fn deep_copy_value(
    src: FzValue,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut HeapHeader, *mut HeapHeader>,
) -> FzValue {
    if let Some(sp) = crate::fz_value::map_addr_from_tagged(src.0)
        && !sp.is_null()
        && src_heap.contains_heap_addr(sp as *mut u8)
    {
        if let Some(&dp) = forwarding.get(&sp) {
            return FzValue(crate::fz_value::tagged_map_bits(dp as *const u8));
        }
        let count = unsafe { crate::fz_value::map_count(sp as *const u8) };
        forwarding.insert(sp, std::ptr::null_mut());
        let mut copied_entries: Vec<(TypedValue, TypedValue)> = Vec::with_capacity(count);
        for i in 0..count {
            let (key, value) = unsafe { crate::fz_value::map_entry(sp as *const u8, i) };
            let new_key = if key.kind.is_heap() {
                let copied = deep_copy_value(
                    FzValue(key.raw | key.kind.tag() as u64),
                    src_heap,
                    dst_heap,
                    forwarding,
                );
                dst_heap.typed_from_fz_value(copied)
            } else {
                key
            };
            let new_value = if value.kind.is_heap() {
                let copied = deep_copy_value(
                    FzValue(value.raw | value.kind.tag() as u64),
                    src_heap,
                    dst_heap,
                    forwarding,
                );
                dst_heap.typed_from_fz_value(copied)
            } else {
                value
            };
            copied_entries.push((new_key, new_value));
        }
        let new_bits = dst_heap.alloc_map(&copied_entries);
        let new_p = crate::fz_value::map_addr_from_tagged(new_bits).expect("new map ptr");
        forwarding.insert(sp, new_p);
        return FzValue(new_bits);
    }
    if let Some(kind) = ValueKind::new((src.0 & crate::fz_value::TAG_MASK) as u8)
        && kind.is_heap()
        && !matches!(kind, ValueKind::LIST | ValueKind::MAP)
    {
        let sp = (src.0 & !crate::fz_value::TAG_MASK) as *mut HeapHeader;
        if !sp.is_null() && src_heap.contains_heap_addr(sp as *mut u8) {
            return deep_copy_value(FzValue::from_ptr(sp), src_heap, dst_heap, forwarding);
        }
    }
    if let Some(sp) = crate::fz_value::list_addr_from_tagged(src.0)
        && !sp.is_null()
        && src_heap.contains_heap_addr(sp as *mut u8)
    {
        if let Some(&dp) = forwarding.get(&sp) {
            return FzValue(crate::fz_value::tagged_list_bits(dp as *const u8));
        }
        let bits = dst_heap.alloc_list_cons(FzValue::NIL, FzValue::EMPTY_LIST);
        let dp = crate::fz_value::list_addr_from_tagged(bits).expect("new list ptr");
        forwarding.insert(sp, dp);
        let cons = unsafe { &*(sp as *const ListCons) };
        let new_head = if cons.head_kind().is_heap() {
            let copied = deep_copy_value(
                FzValue(cons.head | cons.head_kind().tag() as u64),
                src_heap,
                dst_heap,
                forwarding,
            );
            dst_heap.typed_from_fz_value(copied)
        } else {
            cons.head_typed()
        };
        let new_tail = deep_copy_value(FzValue(cons.tail_bits()), src_heap, dst_heap, forwarding);
        unsafe {
            std::ptr::write(dp as *mut ListCons, ListCons::new(new_head, new_tail.0));
        }
        return FzValue(crate::fz_value::tagged_list_bits(dp as *const u8));
    }
    if let Some(sp) = crate::fz_value::closure_addr_from_tagged(src.0)
        && !sp.is_null()
        && src_heap.contains_heap_addr(sp as *mut u8)
    {
        return deep_copy_strict_closure(sp, src_heap, dst_heap, forwarding);
    }
    let sp = match src.unbox_ptr() {
        Some(p) => p,
        None => return src, // non-Ptr scalar
    };
    if sp.is_null() {
        return src;
    }
    if let Some(&dp) = forwarding.get(&sp) {
        return FzValue(dp as u64);
    }
    let h = unsafe { &*sp };
    if src_heap.contains_heap_addr(sp as *mut u8) && (h.size_bytes < 16 || h.size_bytes % 16 != 0) {
        return deep_copy_strict_closure(sp, src_heap, dst_heap, forwarding);
    }
    let Some(kind) = HeapKind::from_u16(h.kind) else {
        if src_heap.contains_heap_addr(sp as *mut u8) {
            return deep_copy_strict_closure(sp, src_heap, dst_heap, forwarding);
        }
        panic!("deep_copy: invalid HeapKind {:#x} at {:?}", h.kind, sp);
    };
    // Allocate the destination object up-front per-kind. Some kinds
    // (List, Struct, Map, Closure) need a placeholder so we can record
    // forwarding before recursing into children.
    let dp: *mut HeapHeader = match kind {
        HeapKind::List => {
            // Placeholder cons; head/tail are filled below.
            let bits = dst_heap.alloc_list_cons(FzValue::NIL, FzValue::EMPTY_LIST);
            crate::fz_value::list_addr_from_tagged(bits).expect("new list ptr")
        }
        HeapKind::Struct => dst_heap.alloc_struct(h.schema_id),
        HeapKind::Float => {
            // Raw payload, no children; copy and short-circuit.
            let f = Heap::read_float(sp);
            let new_p = dst_heap.alloc_float(f);
            forwarding.insert(sp, new_p);
            return FzValue(new_p as u64);
        }
        HeapKind::Bitstring => {
            let bit_len = unsafe { std::ptr::read((sp as *const u8).add(16) as *const u64) };
            let bytes_len = (bit_len as usize).div_ceil(8);
            let bytes = unsafe { std::slice::from_raw_parts((sp as *const u8).add(24), bytes_len) };
            let new_p = dst_heap.alloc_bitstring(bytes, bit_len);
            forwarding.insert(sp, new_p);
            return FzValue(new_p as u64);
        }
        HeapKind::Map => {
            // Collect (k, v) pairs from src, deep-copy each, then alloc
            // a Map in dst with the copied entries.
            let count = unsafe { crate::fz_value::map_count(sp as *const u8) };
            let mut copied_entries: Vec<(TypedValue, TypedValue)> = Vec::with_capacity(count);
            // Pre-register a placeholder forwarding so cycles don't loop;
            // we don't actually have the dst ptr yet so use null as a
            // sentinel. (Cycles through Maps require mutation, which fz
            // doesn't have today; this is just defensive.)
            let placeholder = std::ptr::null_mut();
            forwarding.insert(sp, placeholder);
            for i in 0..count {
                let (k, v) = unsafe { crate::fz_value::map_entry(sp as *const u8, i) };
                let nk = if k.kind.is_heap() {
                    let copied = deep_copy_value(
                        FzValue(k.raw | k.kind.tag() as u64),
                        src_heap,
                        dst_heap,
                        forwarding,
                    );
                    dst_heap.typed_from_fz_value(copied)
                } else {
                    k
                };
                let nv = if v.kind.is_heap() {
                    let copied = deep_copy_value(
                        FzValue(v.raw | v.kind.tag() as u64),
                        src_heap,
                        dst_heap,
                        forwarding,
                    );
                    dst_heap.typed_from_fz_value(copied)
                } else {
                    v
                };
                copied_entries.push((nk, nv));
            }
            let new_bits = dst_heap.alloc_map(&copied_entries);
            let new_p = crate::fz_value::map_addr_from_tagged(new_bits).expect("new map ptr");
            forwarding.insert(sp, new_p);
            return FzValue(new_bits);
        }
        HeapKind::Closure => {
            // fz-ul4.29.5: stub_fp at offset 16, captures (FzValue) at
            // offset 24+. Copy stub_fp as raw bytes (it's a code pointer,
            // valid across heaps); deep-copy each captured FzValue.
            let captured_count = crate::fz_value::closure_flags_captured(h.flags) as usize;
            let halt_kind = crate::fz_value::closure_flags_halt_kind(h.flags);
            let new_bits = dst_heap.alloc_closure_slots(h._reserved, captured_count, halt_kind);
            let new_p = crate::fz_value::closure_addr_from_tagged(new_bits).expect("new closure");
            forwarding.insert(sp, new_p);
            // Copy stub_fp (raw 8 bytes).
            unsafe {
                let fp = std::ptr::read((sp as *const u8).add(16) as *const u64);
                std::ptr::write((new_p as *mut u8).add(8) as *mut u64, fp);
            }
            let src_cursor = unsafe { (sp as *const u8).add(24) as *const FzValue };
            let dst_cursor = unsafe { (new_p as *mut u8).add(16) as *mut FzValue };
            for i in 0..captured_count {
                let child = unsafe { std::ptr::read(src_cursor.add(i)) };
                let nc = deep_copy_value(child, src_heap, dst_heap, forwarding);
                unsafe {
                    std::ptr::write(dst_cursor.add(i), nc);
                }
            }
            return FzValue(new_bits);
        }
        HeapKind::VecI64 => {
            let len = Heap::vec_len(sp) as usize;
            let payload = unsafe { (sp as *const u8).add(24) as *const i64 };
            let v: Vec<i64> = (0..len)
                .map(|i| unsafe { std::ptr::read(payload.add(i)) })
                .collect();
            let new_p = dst_heap.alloc_vec_i64(&v);
            forwarding.insert(sp, new_p);
            return FzValue(new_p as u64);
        }
        HeapKind::VecU8 => {
            let len = Heap::vec_len(sp) as usize;
            let payload = unsafe { (sp as *const u8).add(24) };
            let v: Vec<u8> = (0..len).map(|i| unsafe { *payload.add(i) }).collect();
            let new_p = dst_heap.alloc_vec_u8(&v);
            forwarding.insert(sp, new_p);
            return FzValue(new_p as u64);
        }
        HeapKind::VecBit => {
            let len = Heap::vec_len(sp) as usize;
            let payload = unsafe { (sp as *const u8).add(24) };
            let v: Vec<bool> = (0..len)
                .map(|i| {
                    let byte_idx = i / 8;
                    let bit_idx = 7 - (i % 8);
                    let byte = unsafe { *payload.add(byte_idx) };
                    ((byte >> bit_idx) & 1) == 1
                })
                .collect();
            let new_p = dst_heap.alloc_vec_bit(&v);
            forwarding.insert(sp, new_p);
            return FzValue(new_p as u64);
        }
        HeapKind::VecF64 => {
            panic!("deep_copy_value: HeapKind::VecF64 not yet supported (see fz-ul4.11.23)");
        }
        HeapKind::ProcBin => {
            // fz-q8d.1 — cross-heap deep_copy shares the bytes via retain.
            // The new handle holds a fresh refcount edge that alloc_procbin
            // transfers into the destination ProcBin / MSO chain.
            let src_pb = unsafe { ProcBin::from_raw(sp) };
            let handle = unsafe { SharedBinHandle::retain_from_raw(src_pb.shared_raw()) };
            let new_p = alloc_procbin(dst_heap, handle).as_raw();
            forwarding.insert(sp, new_p);
            return FzValue(new_p as u64);
        }
        HeapKind::Resource => {
            // fz-swt.7 — cross-heap deep_copy shares the Resource via retain,
            // mirroring the ProcBin path. The new handle holds a fresh
            // refcount edge that alloc_resource transfers into the
            // destination stub / MSO chain.
            // fz-4mk — also deep-copy the dtor closure into dst_heap so the
            // destination stub points at a closure native to its own heap.
            use crate::resource::{ResourceHandle, ResourceStub, alloc_resource};
            let src_rs = unsafe { ResourceStub::from_raw(sp) };
            let handle = unsafe { ResourceHandle::retain_from_raw(src_rs.shared_raw()) };
            let src_closure = src_rs.closure_ptr();
            let dst_closure = deep_copy_value(src_closure, src_heap, dst_heap, forwarding);
            let new_p = alloc_resource(dst_heap, handle, dst_closure).as_raw();
            forwarding.insert(sp, new_p);
            return FzValue(new_p as u64);
        }
    };
    forwarding.insert(sp, dp);
    // Recurse into fields, writing copied children into dst slots.
    match kind {
        HeapKind::List => {
            let cons = unsafe { &*(sp as *const ListCons) };
            let new_head = if cons.head_kind().is_heap() {
                let copied = deep_copy_value(
                    FzValue(cons.head | cons.head_kind().tag() as u64),
                    src_heap,
                    dst_heap,
                    forwarding,
                );
                dst_heap.typed_from_fz_value(copied)
            } else {
                cons.head_typed()
            };
            let new_tail =
                deep_copy_value(FzValue(cons.tail_bits()), src_heap, dst_heap, forwarding);
            unsafe {
                let cd = dp as *mut ListCons;
                std::ptr::write(cd, ListCons::new(new_head, new_tail.0));
            }
        }
        HeapKind::Struct => {
            let registry = src_heap.schemas.borrow();
            let schema = registry.get(h.schema_id);
            for f in &schema.fields {
                if let FieldKind::FzValue = f.kind {
                    let off = 16 + f.offset as usize;
                    let child =
                        unsafe { std::ptr::read((sp as *const u8).add(off) as *const FzValue) };
                    let copied = deep_copy_value(child, src_heap, dst_heap, forwarding);
                    unsafe {
                        std::ptr::write((dp as *mut u8).add(off) as *mut FzValue, copied);
                    }
                }
            }
        }
        _ => unreachable!("scalar-only kinds returned early"),
    }
    FzValue(dp as u64)
}

fn deep_copy_strict_closure(
    sp: *mut HeapHeader,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut HeapHeader, *mut HeapHeader>,
) -> FzValue {
    if let Some(&dp) = forwarding.get(&sp) {
        return FzValue(crate::fz_value::tagged_closure_bits(dp as *const u8));
    }
    let captured_count = unsafe { crate::fz_value::closure_captured_count(sp as *const u8) };
    let halt_kind = unsafe { crate::fz_value::closure_halt_kind(sp as *const u8) };
    let schema_id = unsafe { crate::fz_value::closure_schema_id(sp as *const u8) };
    let fn_ptr = unsafe { crate::fz_value::closure_fn_ptr(sp as *const u8) };
    let new_bits = dst_heap.alloc_closure_slots(schema_id, captured_count, halt_kind);
    let dp = crate::fz_value::closure_addr_from_tagged(new_bits).expect("new closure ptr");
    forwarding.insert(sp, dp);
    unsafe { std::ptr::write((dp as *mut u8).add(8) as *mut u64, fn_ptr) };
    for i in 0..captured_count {
        let cv =
            unsafe { std::ptr::read(crate::fz_value::closure_capture_slot(sp as *const u8, i)) };
        let copied = deep_copy_value(cv, src_heap, dst_heap, forwarding);
        unsafe {
            std::ptr::write(
                crate::fz_value::closure_capture_slot(dp as *const u8, i),
                copied,
            );
        }
    }
    FzValue(new_bits)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_value::FzValue;

    fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
        Rc::new(RefCell::new(SchemaRegistry::new()))
    }

    #[test]
    fn schema_registry_register_and_get() {
        let mut reg = SchemaRegistry::new();
        let id_a = reg.register(Schema {
            name: "A".into(),
            size: 0,
            fields: vec![],
        });
        let id_b = reg.register(Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor {
                    offset: 0,
                    kind: FieldKind::FzValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::FzValue,
                },
            ],
        });
        assert_eq!(id_a, 0);
        assert_eq!(id_b, 1);
        assert_eq!(reg.get(id_a).name, "A");
        assert_eq!(reg.get(id_b).name, "Pair");
    }

    /// fz-wu9 — every inline `HeapKind::Bitstring` allocation reserves
    /// at least one zero byte past its payload at offset
    /// `bytes_ptr + ceil(bit_len/8)`. Mirrors the SharedBin invariant
    /// covered by procbin.rs::shared_bin_alloc_has_trailing_nul.
    #[test]
    fn alloc_bitstring_inline_has_trailing_nul() {
        let mut h = Heap::new(1024, empty_registry());
        // Cover lengths around the 16-byte-alignment boundary so the
        // formerly-zero pad cases get exercised.
        for n in [0usize, 1, 7, 8, 9, 15, 16, 17, 24, 25] {
            let bytes: Vec<u8> = (0..n).map(|i| (i as u8) ^ 0xff).collect();
            let bit_len = (n as u64) * 8;
            let p = h.alloc_bitstring(&bytes, bit_len);
            unsafe {
                assert_eq!((*p).kind, HeapKind::Bitstring as u16);
                let payload = (p as *const u8).add(24);
                for i in 0..n {
                    assert_eq!(*payload.add(i), bytes[i], "payload byte {} at len {}", i, n);
                }
                assert_eq!(
                    *payload.add(n),
                    0,
                    "trailing NUL at offset {} for payload len {}",
                    n,
                    n
                );
            }
        }
    }

    #[test]
    fn alloc_bumps_and_tracks() {
        let mut h = Heap::new(1024, empty_registry());
        let p = h.alloc_list_cons(FzValue::from_int(1), FzValue::NIL);
        assert!(crate::fz_value::list_addr_from_tagged(p).is_some());
        assert_eq!(h.live_count(), 1);
        assert_eq!(h.bytes_used(), 16);
    }

    #[test]
    fn alloc_float_round_trips_payload() {
        let mut h = Heap::new(1024, empty_registry());
        let p = h.alloc_float(1.5);
        unsafe {
            assert_eq!((*p).kind, HeapKind::Float as u16);
            assert_eq!((*p).size_bytes, 32);
        }
        assert_eq!(Heap::read_float(p), 1.5);
    }

    #[test]
    fn alloc_vec_i64_writes_header_len_and_payload() {
        let mut h = Heap::new(1024, empty_registry());
        let p = h.alloc_vec_i64(&[10, 20, 30]);
        unsafe {
            assert_eq!((*p).kind, HeapKind::VecI64 as u16);
        }
        assert_eq!(Heap::vec_len(p), 3);
        unsafe {
            let payload = (p as *const u8).add(24) as *const i64;
            assert_eq!(std::ptr::read(payload), 10);
            assert_eq!(std::ptr::read(payload.add(1)), 20);
            assert_eq!(std::ptr::read(payload.add(2)), 30);
        }
    }

    #[test]
    fn alloc_vec_u8_packs_bytes() {
        let mut h = Heap::new(1024, empty_registry());
        let p = h.alloc_vec_u8(&[0xff, 0xab, 0x12]);
        assert_eq!(Heap::vec_len(p), 3);
        unsafe {
            let payload = (p as *const u8).add(24);
            assert_eq!(*payload, 0xff);
            assert_eq!(*payload.add(1), 0xab);
            assert_eq!(*payload.add(2), 0x12);
        }
    }

    #[test]
    fn alloc_vec_bit_packs_msb_first() {
        let mut h = Heap::new(1024, empty_registry());
        // 1,0,1,1,0,0,1 = high bits 0b1011001x -> 0xB2 (trailing bit unset).
        let p = h.alloc_vec_bit(&[true, false, true, true, false, false, true]);
        assert_eq!(Heap::vec_len(p), 7);
        unsafe {
            let payload = (p as *const u8).add(24);
            assert_eq!(*payload, 0b1011_0010);
        }
    }

    #[test]
    fn heap_pointers_are_16_aligned() {
        let mut h = Heap::new(1024, empty_registry());
        for _ in 0..10 {
            let p = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
            let addr = crate::fz_value::list_addr_from_tagged(p).expect("tagged list ptr");
            assert_eq!((addr as usize) & 15, 0);
        }
    }

    /// Bump overflow triggers a grow at the next size_class. Old block is
    /// abandoned; new block holds further allocations. `bytes_used`
    /// covers both. The next gc() returns both blocks to the pool.
    #[test]
    fn alloc_grows_to_next_size_class_on_overflow() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        // SIZE_TABLE[0] = 1024 bytes -> 64 headerless cons cells fit exactly.
        // Allocate 80 to force grow.
        let initial_block = h.block_start;
        let initial_class = h.size_class;
        for _ in 0..80 {
            let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        }
        assert_ne!(h.block_start, initial_block, "grow must move block_start");
        assert!(h.size_class > initial_class, "grow must bump size_class");
        assert_eq!(h.block_size, SIZE_TABLE[h.size_class as usize]);
        assert!(!h.abandoned_blocks.is_empty());
        assert_eq!(h.live_count(), 80);
    }

    /// `should_gc` flips once `bytes_used` crosses `gc_threshold_bytes`;
    /// `clear_should_gc_flag` resets it. The flag is independent of `gc()`
    /// itself — the scheduler reads it at park-time.
    #[test]
    fn pressure_flag_set_when_threshold_crossed() {
        let mut h = Heap::new(1024, empty_registry());
        h.gc_threshold_bytes = 64; // two cons cells.
        assert!(!h.should_gc());
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        assert!(!h.should_gc(), "1 cell at 16 bytes under 64");
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        assert!(!h.should_gc(), "2 cells at 32 bytes under 64");
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        assert!(h.should_gc(), "4 cells at 64 bytes at threshold");
        h.clear_should_gc_flag();
        assert!(!h.should_gc());
    }

    /// With a null root, Cheney recycles the arena: from-space is freed,
    /// to-space is a fresh empty block, live_count goes to zero.
    #[test]
    fn gc_with_null_root_recycles_arena() {
        let mut h = Heap::new(1024, empty_registry());
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        assert_eq!(h.live_count(), 2);
        let mut root: *mut u8 = std::ptr::null_mut();
        h.gc(&mut root);
        assert_eq!(h.gc_run_count, 1);
        assert_eq!(h.live_count(), 0, "no root → nothing copied");
        assert_eq!(h.bytes_used(), 0, "to-space is empty");
        assert!(root.is_null());
    }

    /// A rooted list survives Cheney: every cell is copied to to-space,
    /// the root pointer is rewritten to the new head, and from-space is
    /// freed. Live count matches the chain length.
    #[test]
    fn gc_copies_rooted_list_and_rewrites_root() {
        let mut h = Heap::new(1024, empty_registry());
        // Build [1, 2, 3] — head ptr is n1.
        let n3 = h.alloc_list_cons(FzValue::from_int(3), FzValue::EMPTY_LIST);
        let n2 = h.alloc_list_cons(FzValue::from_int(2), FzValue(n3));
        let n1 = h.alloc_list_cons(FzValue::from_int(1), FzValue(n2));
        let mut root = std::ptr::null_mut();
        let mut roots = [FzValue(n1)];
        let old_n1 = n1 as usize;
        h.gc_with_extra_roots(&mut root, &mut roots);
        let root_bits = roots[0].0;
        let root_ptr = crate::fz_value::list_addr_from_tagged(root_bits).unwrap();
        assert_ne!(
            root_ptr as usize, old_n1,
            "root should be rewritten to to-space"
        );
        assert_eq!(h.live_count(), 3, "all three cells copied");
        // Walk the new list and verify integers match.
        let mut cur = root_ptr as *mut ListCons;
        let mut sum = 0i64;
        let mut count = 0;
        while !cur.is_null() {
            let cons = unsafe { &*cur };
            sum += cons.head as i64;
            count += 1;
            cur = if cons.tail_addr() == 0 {
                std::ptr::null_mut()
            } else {
                cons.tail_addr() as *mut ListCons
            };
        }
        assert_eq!(count, 3);
        assert_eq!(sum, 6);
    }

    /// Cheney drops unreachable objects: a cell allocated alongside the
    /// root chain but not pointed to by it is discarded. live_count
    /// shrinks to the chain length.
    #[test]
    fn gc_drops_unreachable_objects() {
        let mut h = Heap::new(1024, empty_registry());
        let _orphan = h.alloc_list_cons(FzValue::from_int(99), FzValue::EMPTY_LIST);
        let kept = h.alloc_list_cons(FzValue::from_int(7), FzValue::EMPTY_LIST);
        assert_eq!(h.live_count(), 2);
        let mut root = std::ptr::null_mut();
        let mut roots = [FzValue(kept)];
        h.gc_with_extra_roots(&mut root, &mut roots);
        assert_eq!(h.live_count(), 1, "orphan dropped, kept survives");
        let new_cons = crate::fz_value::list_addr_from_tagged(roots[0].0).unwrap() as *mut ListCons;
        let head = unsafe { (*new_cons).head };
        assert_eq!(head as i64, 7);
    }

    #[test]
    fn list_head_can_be_a_tagged_list_without_int_collision() {
        let mut h = Heap::new(1024, empty_registry());
        let child_bits = h.alloc_list_cons(FzValue::from_int(7), FzValue::EMPTY_LIST);
        let parent_bits = h.alloc_list_cons(FzValue(child_bits), FzValue::EMPTY_LIST);
        let parent = crate::fz_value::list_addr_from_tagged(parent_bits).expect("parent list ptr");
        let cons = unsafe { &*(parent as *const ListCons) };
        assert_eq!(cons.head_kind(), ValueKind::LIST);
        assert_eq!(
            cons.head,
            crate::fz_value::list_addr_from_tagged(child_bits).unwrap() as u64
        );
    }

    #[test]
    fn deep_copy_tagged_list_preserves_nested_list_head() {
        let mut src = Heap::new(1024, empty_registry());
        let mut dst = Heap::new(1024, empty_registry());
        let child_bits = src.alloc_list_cons(FzValue::from_int(7), FzValue::EMPTY_LIST);
        let parent_bits = src.alloc_list_cons(FzValue(child_bits), FzValue::EMPTY_LIST);
        let mut forwarding = std::collections::HashMap::new();

        let copied = deep_copy_value(FzValue(parent_bits), &src, &mut dst, &mut forwarding);
        let copied_parent =
            crate::fz_value::list_addr_from_tagged(copied.0).expect("copied parent list ptr");
        let parent = unsafe { &*(copied_parent as *const ListCons) };
        assert_eq!(parent.head_kind(), ValueKind::LIST);

        let copied_child = parent.head as *mut HeapHeader;
        assert_ne!(
            copied_child,
            crate::fz_value::list_addr_from_tagged(child_bits).unwrap()
        );
        let child = unsafe { &*(copied_child as *const ListCons) };
        assert_eq!(child.head_kind(), ValueKind::INT);
        assert_eq!(child.head as i64, 7);
        assert_eq!(child.tail_bits(), FzValue::EMPTY_LIST.0);
    }

    /// Acceptance (fz-siu.10 / §6.6): spawn under load shows no per-spawn
    /// malloc after warm-up. After dropping a Heap, its block goes to the
    /// pool; the next Heap::new of the same size_class pulls from the
    /// pool, no malloc required. Repeating spawn+drop with a fixed pool
    /// occupancy proves the cache is doing its job.
    #[test]
    fn pool_caches_blocks_across_heap_drops() {
        pool_drain_for_test();
        assert_eq!(pool_total_cached_blocks(), 0, "test starts with empty pool");

        // Warm-up: create + drop one Heap. Drop returns the block.
        {
            let _h = Heap::new(SIZE_TABLE[0], empty_registry());
        }
        assert_eq!(pool_total_cached_blocks(), 1, "first drop fills the pool");

        // Subsequent spawn-equivalents (Heap::new + drop) must not increase
        // the pool occupancy — they pull from the cache, return the same
        // block. The acceptance "no per-spawn malloc": occupancy stays at
        // 1 across N create+drop cycles.
        for _ in 0..50 {
            let _h = Heap::new(SIZE_TABLE[0], empty_registry());
            assert_eq!(pool_total_cached_blocks(), 0, "alloc drained the cache");
            // _h dropped here → returns the block to the pool.
        }
        assert_eq!(
            pool_total_cached_blocks(),
            1,
            "pool stayed at 1 cached block"
        );

        pool_drain_for_test();
    }

    #[test]
    fn size_table_first_entry_is_1k() {
        assert_eq!(SIZE_TABLE[0], 1024);
    }

    #[test]
    fn size_table_is_monotonic_and_16_aligned() {
        for i in 1..SIZE_TABLE.len() {
            assert!(
                SIZE_TABLE[i] > SIZE_TABLE[i - 1],
                "non-monotonic at {}: {} <= {}",
                i,
                SIZE_TABLE[i],
                SIZE_TABLE[i - 1]
            );
            assert_eq!(
                SIZE_TABLE[i] % 16,
                0,
                "entry {} ({}) not 16-aligned",
                i,
                SIZE_TABLE[i]
            );
        }
    }

    #[test]
    fn size_table_tail_is_geometric_ish() {
        // Tail entries grow ~×1.2 (after the Fibonacci low end). Sample
        // index 20 → 21: ratio in [1.18, 1.23].
        let ratio = SIZE_TABLE[21] as f64 / SIZE_TABLE[20] as f64;
        assert!(
            ratio > 1.18 && ratio < 1.23,
            "tail ratio out of expected range: {}",
            ratio
        );
    }

    #[test]
    fn pick_size_class_smallest_fit() {
        assert_eq!(pick_size_class(0), 0);
        assert_eq!(pick_size_class(1024), 0);
        assert_eq!(pick_size_class(1025), 1);
        assert_eq!(pick_size_class(SIZE_TABLE[5]), 5);
        assert_eq!(pick_size_class(SIZE_TABLE[5] + 1), 6);
    }

    #[test]
    fn pick_size_class_clamps_on_tail_no_panic() {
        // Far past the last entry — must clamp, not panic.
        let class = pick_size_class(usize::MAX);
        assert_eq!(class as usize, SIZE_TABLE.len() - 1);
    }

    /// Acceptance: under increasing load, gc picks ascending size_class
    /// values. Build progressively longer rooted chains; each gc tracks
    /// to a higher class as live_bytes grows past each SIZE_TABLE step.
    #[test]
    fn gc_picks_ascending_size_class_as_live_grows() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let mut last_class: i32 = -1;
        // Build chains of growing length and gc each time. Working set
        // doubles each iteration to ensure size_class climbs.
        for power in 6..=12 {
            let len = 1usize << power; // 64, 128, ..., 4096 cells
            // Build a chain of `len` cons cells, rooted at head.
            let mut tail = FzValue::NIL;
            for i in 0..len {
                let cell = h.alloc_list_cons(FzValue::from_int(i as i64), tail);
                tail = FzValue(cell);
            }
            let mut root = std::ptr::null_mut();
            let mut roots = [tail];
            h.gc_with_extra_roots(&mut root, &mut roots);
            let live_bytes = len * 16;
            let expected_min = pick_size_class(live_bytes); // without slack
            assert!(
                h.size_class >= expected_min,
                "size_class {} should fit live_bytes {}",
                h.size_class,
                live_bytes
            );
            assert!(
                (h.size_class as i32) > last_class || last_class < 0,
                "size_class did not climb: prev={}, now={}",
                last_class,
                h.size_class
            );
            last_class = h.size_class as i32;
            // Drop the root so next iteration starts fresh.
            let _ = root; // reachable until here
        }
    }

    /// last_gc_live_bytes is set correctly after GC and used for to-space sizing.
    /// First GC uses bytes_used() as upper bound; subsequent GCs use
    /// last_gc_live_bytes * 2 (50% post-GC target occupancy).
    #[test]
    fn gc_updates_last_gc_live_bytes() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        assert_eq!(h.last_gc_live_bytes, 0, "zero before first gc");
        // Build [1, 2, 3].
        let n3 = h.alloc_list_cons(FzValue::from_int(3), FzValue::EMPTY_LIST);
        let n2 = h.alloc_list_cons(FzValue::from_int(2), FzValue(n3));
        let n1 = h.alloc_list_cons(FzValue::from_int(1), FzValue(n2));
        let mut root = std::ptr::null_mut();
        let mut roots = [FzValue(n1)];
        h.gc_with_extra_roots(&mut root, &mut roots);
        assert_eq!(h.last_gc_live_bytes, 3 * 16, "three cons cells = 48 bytes");

        // Second GC with same live set: to-space sizing = 48 * 2 = 96,
        // clamped to SIZE_TABLE[0]. live bytes stay the same.
        h.gc_with_extra_roots(&mut root, &mut roots);
        assert_eq!(h.last_gc_live_bytes, 3 * 16, "live bytes unchanged");
        assert_eq!(h.size_class, 0, "tiny live set stays at smallest class");
    }

    /// Watermark is set to 75% of block. After alloc crossing watermark,
    /// FZ_SHOULD_YIELD is set; it can be cleared externally.
    #[test]
    fn watermark_is_75_percent_of_block() {
        use crate::yield_flag::FZ_SHOULD_YIELD;
        use std::sync::atomic::Ordering;
        FZ_SHOULD_YIELD.store(0, Ordering::Relaxed);
        let h = Heap::new(SIZE_TABLE[0], empty_registry());
        let expected = unsafe { h.block_start.add(SIZE_TABLE[0] * 3 / 4) };
        assert_eq!(h.gc_watermark, expected);
        FZ_SHOULD_YIELD.store(0, Ordering::Relaxed); // cleanup
    }

    /// Large struct (200-byte payload, well past the old 64-byte cap)
    /// allocates without panic; grow promotes to a larger size_class as needed.
    #[test]
    fn alloc_large_struct_succeeds_and_grows_size_class() {
        let reg = empty_registry();
        // Build a schema whose payload is 200 bytes of FzValue fields.
        let n_fields = 200 / 8; // 25 FzValue slots
        let mut fields = Vec::with_capacity(n_fields);
        for i in 0..n_fields {
            fields.push(FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::FzValue,
            });
        }
        let id = reg.borrow_mut().register(Schema {
            name: "Big".into(),
            size: (n_fields * 8) as u32,
            fields,
        });
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let p = h.alloc_struct(id);
        unsafe {
            assert_eq!((*p).kind, HeapKind::Struct as u16);
            // total = 16 + 200 = 216, rounded to 224.
            assert_eq!((*p).size_bytes, 224);
        }
    }

    /// Map with 5 entries exercises both alloc and the Cheney trace path
    /// (Map walks each entry's typed children).
    #[test]
    fn alloc_large_map_round_trips_through_gc() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let entries: Vec<(TypedValue, TypedValue)> = (0..5)
            .map(|i| {
                (
                    TypedValue::new(i as u64, ValueKind::INT),
                    TypedValue::new((i * 10) as u64, ValueKind::INT),
                )
            })
            .collect();
        let bits = h.alloc_map(&entries);
        let mut root = std::ptr::null_mut();
        let mut roots = [FzValue(bits)];
        h.gc_with_extra_roots(&mut root, &mut roots);
        assert_eq!(h.live_count(), 1, "map survives GC");
        let new_p = crate::fz_value::map_addr_from_tagged(roots[0].0).unwrap();
        unsafe {
            let count = crate::fz_value::map_count(new_p as *const u8);
            assert_eq!(count, 5);
        }
    }

    #[test]
    fn map_layout_size_correct() {
        for count in [0usize, 1, 2, 3, 7, 8, 9] {
            let entries: Vec<(TypedValue, TypedValue)> = (0..count)
                .map(|i| {
                    (
                        TypedValue::new(i as u64, ValueKind::INT),
                        TypedValue::new((i + 10) as u64, ValueKind::INT),
                    )
                })
                .collect();
            let mut h = Heap::new(1024, empty_registry());
            let bits = h.alloc_map(&entries);
            assert_eq!(
                crate::fz_value::object_size(bits),
                crate::fz_value::map_size_for_count(count)
            );
        }
    }

    #[test]
    fn closure_layout_zero_captures() {
        let mut h = Heap::new(1024, empty_registry());
        let bits = h.alloc_closure(42, 0, 2, 0xfeed_beef, &[]);
        assert_eq!(
            bits & crate::fz_value::TAG_MASK,
            crate::fz_value::TAG_CLOSURE
        );
        assert_eq!(crate::fz_value::object_size(bits), 16);
        let p = crate::fz_value::closure_addr_from_tagged(bits).unwrap();
        assert_eq!(
            unsafe { crate::fz_value::closure_schema_id(p as *const u8) },
            42
        );
        assert_eq!(
            unsafe { crate::fz_value::closure_halt_kind(p as *const u8) },
            2
        );
        assert_eq!(
            unsafe { crate::fz_value::closure_fn_ptr(p as *const u8) },
            0xfeed_beef
        );
    }

    #[test]
    fn closure_layout_n_captures() {
        let mut h = Heap::new(1024, empty_registry());
        let captures = [FzValue::from_int(10), FzValue::from_int(20)];
        let bits = h.alloc_closure(7, captures.len(), 1, 0x1234, &captures);
        assert_eq!(crate::fz_value::object_size(bits), 32);
        let p = crate::fz_value::closure_addr_from_tagged(bits).unwrap();
        assert_eq!(
            unsafe { crate::fz_value::closure_captured_count(p as *const u8) },
            2
        );
        for (i, expected) in captures.iter().enumerate() {
            let got =
                unsafe { std::ptr::read(crate::fz_value::closure_capture_slot(p as *const u8, i)) };
            assert_eq!(got.0, expected.0);
        }
    }

    #[test]
    fn closure_forwarding_marker() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let bits = h.alloc_closure(12, 0, 0, 0x7777, &[]);
        let old = crate::fz_value::closure_addr_from_tagged(bits).unwrap();
        let mut root = bits as *mut u8;
        h.gc(&mut root);
        let new_bits = root as u64;
        let new_p = crate::fz_value::closure_addr_from_tagged(new_bits).unwrap();
        assert_ne!(old, new_p);
        assert_eq!(
            unsafe { crate::fz_value::closure_schema_id(new_p as *const u8) },
            12
        );
        assert_eq!(
            unsafe { crate::fz_value::closure_fn_ptr(new_p as *const u8) },
            0x7777
        );
        let marker = unsafe { std::ptr::read(old as *const u64) };
        assert_eq!(marker & crate::fz_value::TAG_MASK, crate::fz_value::TAG_FWD);
        let confirm = unsafe { std::ptr::read((old as *const u8).add(8) as *const u64) };
        assert_eq!(confirm, crate::fz_value::TAG_FWD);
    }

    #[test]
    fn closure_fn_id_preserved_in_schema_id() {
        let mut h = Heap::new(1024, empty_registry());
        let bits = h.alloc_closure_slots(99, 0, 0);
        let p = crate::fz_value::closure_addr_from_tagged(bits).unwrap();
        assert_eq!(
            unsafe { crate::fz_value::closure_schema_id(p as *const u8) },
            99
        );
    }

    #[test]
    fn map_packed_tags_round_trip() {
        let cases = [1usize, 2, 3, 7, 8, 9];
        for count in cases {
            let entries: Vec<(TypedValue, TypedValue)> = (0..count)
                .map(|i| {
                    let key_kind = if i % 2 == 0 {
                        ValueKind::ATOM
                    } else {
                        ValueKind::INT
                    };
                    let value_kind = if i % 3 == 0 {
                        ValueKind::FLOAT
                    } else {
                        ValueKind::INT
                    };
                    (
                        TypedValue::new(i as u64, key_kind),
                        TypedValue::new((100 + i) as u64, value_kind),
                    )
                })
                .collect();
            let mut h = Heap::new(1024, empty_registry());
            let bits = h.alloc_map(&entries);
            let p = crate::fz_value::map_addr_from_tagged(bits).unwrap();
            for (i, expected) in entries.iter().enumerate() {
                let got = unsafe { crate::fz_value::map_entry(p as *const u8, i) };
                assert_eq!(got, *expected);
            }
        }
    }

    #[test]
    fn map_float_value_is_unboxed_raw_bits() {
        let mut h = Heap::new(1024, empty_registry());
        let f = 3.14f64;
        let bits = h.alloc_map(&[(
            TypedValue::new(0, ValueKind::ATOM),
            TypedValue::new(f.to_bits(), ValueKind::FLOAT),
        )]);
        let p = crate::fz_value::map_addr_from_tagged(bits).unwrap();
        let (_, value) = unsafe { crate::fz_value::map_entry(p as *const u8, 0) };
        assert_eq!(value.kind, ValueKind::FLOAT);
        assert_eq!(value.raw, f.to_bits());
        assert_eq!(h.live_count(), 1, "map allocation should not box the float");
    }

    #[test]
    fn map_int_value_stores_full_i64_range() {
        let mut h = Heap::new(1024, empty_registry());
        let value = i64::MIN;
        let bits = h.alloc_map(&[(
            TypedValue::new(1, ValueKind::ATOM),
            TypedValue::new(value as u64, ValueKind::INT),
        )]);
        let p = crate::fz_value::map_addr_from_tagged(bits).unwrap();
        let (_, got) = unsafe { crate::fz_value::map_entry(p as *const u8, 0) };
        assert_eq!(got.kind, ValueKind::INT);
        assert_eq!(got.raw as i64, value);
    }

    #[test]
    fn deep_copy_tagged_map_preserves_nested_list_value() {
        let mut src = Heap::new(1024, empty_registry());
        let mut dst = Heap::new(1024, empty_registry());
        let child_bits = src.alloc_list_cons(FzValue::from_int(7), FzValue::EMPTY_LIST);
        let child_ptr = crate::fz_value::list_addr_from_tagged(child_bits).unwrap();
        let map_bits = src.alloc_map(&[(
            TypedValue::new(1, ValueKind::ATOM),
            TypedValue::heap_ptr(child_ptr, ValueKind::LIST),
        )]);
        let mut forwarding = std::collections::HashMap::new();
        let copied = deep_copy_value(FzValue(map_bits), &src, &mut dst, &mut forwarding);
        let copied_map = crate::fz_value::map_addr_from_tagged(copied.0).unwrap();
        let (_, value) = unsafe { crate::fz_value::map_entry(copied_map as *const u8, 0) };
        assert_eq!(value.kind, ValueKind::LIST);
        assert_ne!(value.raw as *mut HeapHeader, child_ptr);
        let copied_list = unsafe { &*(value.raw as *const ListCons) };
        assert_eq!(copied_list.head_kind(), ValueKind::INT);
        assert_eq!(copied_list.head as i64, 7);
    }

    #[test]
    fn gc_map_count_twelve_does_not_collide_with_forwarding_tag() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let entries: Vec<(TypedValue, TypedValue)> = (0..12)
            .map(|i| {
                (
                    TypedValue::new(i as u64, ValueKind::INT),
                    TypedValue::new((i * 2) as u64, ValueKind::INT),
                )
            })
            .collect();
        let bits = h.alloc_map(&entries);
        let old = crate::fz_value::map_addr_from_tagged(bits).unwrap();
        let mut root = std::ptr::null_mut();
        let mut roots = [FzValue(bits)];
        h.gc_with_extra_roots(&mut root, &mut roots);
        let new_p = crate::fz_value::map_addr_from_tagged(roots[0].0).unwrap();
        assert_ne!(new_p, old);
        assert_eq!(
            unsafe { crate::fz_value::map_count(new_p as *const u8) },
            12
        );
    }

    /// Vec<i64> with 100 elements (~824-byte total) — past the old 64-byte cap
    /// and forces a grow because the initial 1 KiB block also holds garbage.
    #[test]
    fn alloc_large_vec_i64_round_trips_through_gc() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let elems: Vec<i64> = (0..100).collect();
        let p = h.alloc_vec_i64(&elems);
        let mut root = p as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.live_count(), 1);
        let new_p = root as *mut HeapHeader;
        assert_eq!(Heap::vec_len(new_p), 100);
        unsafe {
            let payload = (new_p as *const u8).add(24) as *const i64;
            for (i, expected) in elems.iter().enumerate() {
                assert_eq!(std::ptr::read(payload.add(i)), *expected);
            }
        }
    }

    /// Acceptance: ≥10 GC cycles with the same small live working set
    /// keep the arena bounded. Block size may grow once to fit per-cycle
    /// garbage but does not increase without bound; no abandoned blocks
    /// remain post-GC; live_count stays at the rooted chain length.
    /// (§6.4 / fz-siu.8 acceptance.)
    #[test]
    fn gc_keeps_arena_bounded_across_many_cycles() {
        let mut h = Heap::new(1024, empty_registry());
        // Rooted [1, 2, 3] — the live working set across every cycle.
        let n3 = h.alloc_list_cons(FzValue::from_int(3), FzValue::EMPTY_LIST);
        let n2 = h.alloc_list_cons(FzValue::from_int(2), FzValue(n3));
        let n1 = h.alloc_list_cons(FzValue::from_int(1), FzValue(n2));
        let mut root = std::ptr::null_mut();
        let mut roots = [FzValue(n1)];
        for _ in 0..15 {
            // Per-cycle garbage that overflows the 1 KiB initial block,
            // forcing grow → abandon → reclaim at next gc().
            for _ in 0..100 {
                let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
            }
            h.gc_with_extra_roots(&mut root, &mut roots);
            // Post-gc invariants.
            assert_eq!(h.live_count(), 3, "rooted chain survives");
            assert_eq!(h.abandoned_blocks.len(), 0, "abandoned blocks reclaimed");
        }
        // After the working-set-fits-in-block point, block_size stays put.
        // Generous upper bound: 32× initial guards against runaway growth.
        assert!(
            h.block_size <= 1024 * 32,
            "block_size grew unboundedly: {}",
            h.block_size
        );
    }

    /// Cycle (a.0 = b, b.0 = a) doesn't loop the collector: forwarding
    /// pointers in from-space short-circuit revisits.
    #[test]
    fn gc_handles_cycle_via_forwarding() {
        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor {
                    offset: 0,
                    kind: FieldKind::FzValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::FzValue,
                },
            ],
        });
        let mut h = Heap::new(1024, reg.clone());
        let a = h.alloc_struct(pair_id);
        let b = h.alloc_struct(pair_id);
        h.write_field(a, 0, FzValue::from_ptr(b));
        h.write_field(a, 8, FzValue::NIL);
        h.write_field(b, 0, FzValue::from_ptr(a));
        h.write_field(b, 8, FzValue::NIL);
        let mut root = a as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.live_count(), 2);
    }

    // ===== fz-q8d.1 — ProcBin + intrusive MSO + post-Cheney sweep =========

    use crate::procbin::{
        ProcBin, SharedBinHandle, alloc_procbin, bitstring_bit_len, bitstring_byte_ptr, live_count,
    };

    /// Walk the heap's MSO chain and return the contained header pointers
    /// in chain order (head → tail).
    fn mso_chain(h: &Heap) -> Vec<*mut HeapHeader> {
        let mut out = Vec::new();
        let mut cur = h.mso_head;
        while !cur.is_null() {
            let pb = unsafe { ProcBin::from_raw(cur) };
            let next = pb.mso_next();
            out.push(cur);
            cur = next;
        }
        out
    }

    /// `alloc_procbin` writes a ProcBin header and pushes onto the chain.
    #[test]
    #[serial_test::serial]
    fn alloc_procbin_pushes_into_mso_chain_with_correct_header() {
        let baseline = live_count();
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let pb = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1, 2, 3, 4], 32));
            unsafe {
                assert_eq!((*pb.as_raw()).kind, HeapKind::ProcBin as u16);
                assert_eq!((*pb.as_raw()).size_bytes, 32);
            }
            assert_eq!(mso_chain(&h), vec![pb.as_raw()]);
        }
        assert_eq!(live_count(), baseline);
    }

    /// A rooted ProcBin survives Cheney: chain rewritten to to-space copy.
    #[test]
    #[serial_test::serial]
    fn procbin_survives_gc_via_mso_rewrite() {
        let baseline = live_count();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let pb = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[0xaa; 8], 64));
        let shared_p = pb.shared_raw();
        let from_pb = pb.as_raw();
        let mut root = from_pb as *mut u8;
        assert_eq!(live_count(), baseline + 1);
        h.gc(&mut root);
        let new_pb = root as *mut HeapHeader;
        assert_ne!(new_pb, from_pb, "ProcBin should have moved to to-space");
        assert_eq!(mso_chain(&h), vec![new_pb], "chain rewritten");
        assert_eq!(live_count(), baseline + 1, "shared bin unchanged across GC");
        let pb_to = unsafe { ProcBin::from_raw(new_pb) };
        assert_eq!(pb_to.shared_raw(), shared_p);
        drop(h);
        assert_eq!(live_count(), baseline);
    }

    /// Unrooted ProcBin: MSO sweep releases its SharedBin.
    #[test]
    #[serial_test::serial]
    fn procbin_dies_in_gc_and_sweep_releases_shared_bin() {
        let baseline = live_count();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[0x55; 16], 128));
        assert_eq!(live_count(), baseline + 1);
        let mut root: *mut u8 = std::ptr::null_mut();
        h.gc(&mut root);
        assert!(h.mso_head.is_null(), "dead ProcBin swept from MSO");
        assert_eq!(live_count(), baseline);
    }

    /// Heap::drop releases every chain entry's shared_ptr.
    #[test]
    #[serial_test::serial]
    fn heap_drop_releases_all_mso_shared_refs() {
        let baseline = live_count();
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1, 2], 16));
            let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[3, 4, 5], 24));
            assert_eq!(live_count(), baseline + 2);
            assert_eq!(mso_chain(&h).len(), 2);
        }
        assert_eq!(live_count(), baseline);
    }

    // ===== deep_copy_value handles ProcBin via retain =====================

    /// Cross-heap deep_copy of a ProcBin shares the SharedBin.
    #[test]
    #[serial_test::serial]
    fn deep_copy_procbin_shares_via_retain() {
        let baseline = live_count();
        let mut src = Heap::new(SIZE_TABLE[0], empty_registry());
        let mut dst = Heap::new(SIZE_TABLE[0], empty_registry());
        let src_pb = alloc_procbin(&mut src, SharedBinHandle::from_bytes(&[7, 8, 9, 10], 32));
        let shared_p = src_pb.shared_raw();
        let v = FzValue::from_ptr(src_pb.as_raw());
        let mut fwd = std::collections::HashMap::new();
        let copied = deep_copy_value(v, &src, &mut dst, &mut fwd);
        let dst_p = copied.unbox_ptr().unwrap();
        let dst_pb = unsafe { ProcBin::from_raw(dst_p) };
        assert_ne!(dst_p, src_pb.as_raw());
        assert_eq!(dst_pb.shared_raw(), shared_p);
        assert_eq!(mso_chain(&src).len(), 1);
        assert_eq!(mso_chain(&dst).len(), 1);
        unsafe {
            assert_eq!((*shared_p).refcount.load(crate::sync::Ordering::Relaxed), 2);
        }
        assert_eq!(live_count(), baseline + 1);
        drop(dst);
        unsafe {
            assert_eq!((*shared_p).refcount.load(crate::sync::Ordering::Relaxed), 1);
        }
        assert_eq!(mso_chain(&src).len(), 1);
        drop(src);
        assert_eq!(live_count(), baseline);
    }

    /// Shared structure: a tuple containing the same ProcBin twice
    /// deep-copies to a single retained reference (refcount 2, not 3).
    #[test]
    #[serial_test::serial]
    fn deep_copy_procbin_dedup_via_forwarding_map() {
        let baseline = live_count();
        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor {
                    offset: 0,
                    kind: FieldKind::FzValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::FzValue,
                },
            ],
        });
        let mut src = Heap::new(SIZE_TABLE[0], reg.clone());
        let mut dst = Heap::new(SIZE_TABLE[0], reg);
        let src_pb = alloc_procbin(&mut src, SharedBinHandle::from_bytes(&[0xab, 0xcd], 16));
        let shared_p = src_pb.shared_raw();
        let pair = src.alloc_struct(pair_id);
        src.write_field(pair, 0, FzValue::from_ptr(src_pb.as_raw()));
        src.write_field(pair, 8, FzValue::from_ptr(src_pb.as_raw()));
        let mut fwd = std::collections::HashMap::new();
        let _ = deep_copy_value(FzValue::from_ptr(pair), &src, &mut dst, &mut fwd);
        assert_eq!(mso_chain(&dst).len(), 1, "dedup");
        unsafe {
            assert_eq!((*shared_p).refcount.load(crate::sync::Ordering::Relaxed), 2);
        }
        drop(dst);
        drop(src);
        assert_eq!(live_count(), baseline);
    }

    // ===== alloc_bitstring threshold + dispatch ===========================

    #[test]
    fn alloc_bitstring_small_stays_inline() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let bytes: Vec<u8> = (0..32u8).collect();
        let p = h.alloc_bitstring(&bytes, 256);
        unsafe {
            assert_eq!((*p).kind, HeapKind::Bitstring as u16);
            assert_eq!(bitstring_bit_len(p), 256);
            let pay = bitstring_byte_ptr(p);
            for i in 0..32 {
                assert_eq!(*pay.add(i), bytes[i]);
            }
        }
        assert!(h.mso_head.is_null());
    }

    #[test]
    #[serial_test::serial]
    fn alloc_bitstring_large_routes_to_shared_zone() {
        let baseline = live_count();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let bytes: Vec<u8> = (0..128u8).collect();
        let p = h.alloc_bitstring(&bytes, 1024);
        unsafe {
            assert_eq!((*p).kind, HeapKind::ProcBin as u16);
            assert_eq!(bitstring_bit_len(p), 1024);
            let pay = bitstring_byte_ptr(p);
            for i in 0..128 {
                assert_eq!(*pay.add(i), bytes[i]);
            }
        }
        assert_eq!(mso_chain(&h).len(), 1);
        assert_eq!(live_count(), baseline + 1);
        drop(h);
        assert_eq!(live_count(), baseline);
    }

    /// Full spawn-and-share scenario at the heap layer.
    #[test]
    #[serial_test::serial]
    fn shared_heap_acceptance_spawn_and_share() {
        const N: usize = 4;
        let baseline = live_count();
        let payload: Vec<u8> = (0..128u8).collect();
        let mut sender = Heap::new(SIZE_TABLE[0], empty_registry());
        let bs_in_sender = sender.alloc_bitstring(&payload, 1024);
        assert_eq!(live_count(), baseline + 1);

        let mut receivers: Vec<Heap> = (0..N)
            .map(|_| Heap::new(SIZE_TABLE[0], empty_registry()))
            .collect();
        let mut receiver_roots: Vec<*mut HeapHeader> = Vec::with_capacity(N);
        for r in receivers.iter_mut() {
            let mut fwd = std::collections::HashMap::new();
            let copied = deep_copy_value(FzValue::from_ptr(bs_in_sender), &sender, r, &mut fwd);
            receiver_roots.push(copied.unbox_ptr().unwrap());
        }
        let sender_pb = unsafe { ProcBin::from_raw(bs_in_sender) };
        let shared_p = sender_pb.shared_raw();
        unsafe {
            assert_eq!(
                (*shared_p).refcount.load(crate::sync::Ordering::Relaxed),
                1 + N
            );
        }
        assert_eq!(live_count(), baseline + 1);

        for (r, root_ptr) in receivers.iter_mut().zip(receiver_roots.iter_mut()) {
            let mut root_u8 = (*root_ptr) as *mut u8;
            r.gc(&mut root_u8);
            *root_ptr = root_u8 as *mut HeapHeader;
            let chain = mso_chain(r);
            assert_eq!(chain.len(), 1);
            assert_eq!(chain[0], *root_ptr);
        }
        assert_eq!(live_count(), baseline + 1);

        for root_ptr in &receiver_roots {
            unsafe {
                assert_eq!(bitstring_bit_len(*root_ptr), 1024);
                let bp = bitstring_byte_ptr(*root_ptr);
                for (i, expected) in payload.iter().enumerate() {
                    assert_eq!(*bp.add(i), *expected);
                }
            }
        }

        let _ = receiver_roots;
        drop(receivers);
        unsafe {
            assert_eq!((*shared_p).refcount.load(crate::sync::Ordering::Relaxed), 1);
        }
        assert_eq!(live_count(), baseline + 1);

        drop(sender);
        assert_eq!(live_count(), baseline);
    }

    // ===== fz-q8d.4 — heap fragments ======================================

    /// Oversized allocations land in the fragment list, bypass the bump
    /// arena, and report their size via `bytes_used()`.
    #[test]
    fn alloc_oversized_routes_to_fragment_list() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let want = SIZE_TABLE[SIZE_TABLE.len() - 1] + 16;
        let p = h.alloc(want);
        assert!(!p.is_null());
        assert_eq!(h.fragments.len(), 1);
        assert_eq!(h.fragments[0].size, (want + 15) & !15);
        // bytes_used includes the fragment size.
        assert!(h.bytes_used() >= h.fragments[0].size);
    }

    /// Rooted oversized struct survives GC; mark bit cycles back to false.
    #[test]
    fn rooted_fragment_survives_gc() {
        let reg = empty_registry();
        // A schema large enough that alloc_struct routes to fragments.
        let n_fields = (FRAGMENT_THRESHOLD + 256) / 8; // payload size > threshold
        let mut fields = Vec::with_capacity(n_fields);
        for i in 0..n_fields {
            fields.push(FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::FzValue,
            });
        }
        let id = reg.borrow_mut().register(Schema {
            name: "Big".into(),
            size: (n_fields * 8) as u32,
            fields,
        });
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let big = h.alloc_struct(id);
        assert_eq!(h.fragments.len(), 1);
        let frag_ptr = h.fragments[0].ptr;
        let mut root = big as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.fragments.len(), 1, "fragment survives");
        assert_eq!(h.fragments[0].ptr, frag_ptr, "fragment did not move");
        assert!(!h.fragments[0].mark, "mark reset post-GC");
        // Root is unchanged because the fragment did not move.
        assert_eq!(root as *mut HeapHeader, big);
    }

    /// Unrooted oversized object is freed by GC; fragment list shrinks.
    #[test]
    fn unrooted_fragment_is_freed_by_gc() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let _ = h.alloc(FRAGMENT_THRESHOLD + 16);
        assert_eq!(h.fragments.len(), 1);
        let mut root: *mut u8 = std::ptr::null_mut();
        h.gc(&mut root);
        assert!(h.fragments.is_empty(), "unrooted fragment freed");
    }

    /// Three fragments, two rooted: the unrooted one is reclaimed.
    #[test]
    fn mixed_fragment_liveness() {
        let reg = empty_registry();
        let n_fields = (FRAGMENT_THRESHOLD + 256) / 8;
        let mut fields = Vec::with_capacity(n_fields);
        for i in 0..n_fields {
            fields.push(FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::FzValue,
            });
        }
        let id = reg.borrow_mut().register(Schema {
            name: "Big".into(),
            size: (n_fields * 8) as u32,
            fields,
        });
        let mut h = Heap::new(SIZE_TABLE[0], reg.clone());
        let a = h.alloc_struct(id);
        let _b_dead = h.alloc_struct(id);
        let c = h.alloc_struct(id);
        assert_eq!(h.fragments.len(), 3);
        // We can only thread one root pointer through `gc`; package a
        // pair {a, c} into a tuple in the bump arena (a Struct with
        // FzValue fields) — that becomes a root containing both.
        let pair_id = reg.borrow_mut().register(Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor {
                    offset: 0,
                    kind: FieldKind::FzValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::FzValue,
                },
            ],
        });
        let pair = h.alloc_struct(pair_id);
        h.write_field(pair, 0, FzValue::from_ptr(a));
        h.write_field(pair, 8, FzValue::from_ptr(c));
        let mut root = pair as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.fragments.len(), 2, "the unrooted fragment was reclaimed");
    }

    /// Fragment → fragment edge: the head fragment holds a pointer at
    /// payload offset 0 to a second fragment. Rooting the head must
    /// keep both alive.
    #[test]
    fn fragment_to_fragment_edge_survives_gc() {
        let reg = empty_registry();
        let n_fields = (FRAGMENT_THRESHOLD + 256) / 8;
        let mut fields = Vec::with_capacity(n_fields);
        for i in 0..n_fields {
            fields.push(FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::FzValue,
            });
        }
        let id = reg.borrow_mut().register(Schema {
            name: "Big".into(),
            size: (n_fields * 8) as u32,
            fields,
        });
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let head = h.alloc_struct(id);
        let tail = h.alloc_struct(id);
        h.write_field(head, 0, FzValue::from_ptr(tail));
        let mut root = head as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.fragments.len(), 2, "both fragments survive");
    }

    /// Fragment → to-space edge: a fragment holds a pointer to a
    /// normal heap-resident List cons. Rooting the fragment must
    /// preserve the cons and move it to to-space.
    #[test]
    fn fragment_to_block_edge_promotes_block_object() {
        let reg = empty_registry();
        let n_fields = (FRAGMENT_THRESHOLD + 256) / 8;
        let mut fields = Vec::with_capacity(n_fields);
        for i in 0..n_fields {
            fields.push(FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::FzValue,
            });
        }
        let id = reg.borrow_mut().register(Schema {
            name: "Big".into(),
            size: (n_fields * 8) as u32,
            fields,
        });
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let cons = h.alloc_list_cons(FzValue::from_int(7), FzValue::EMPTY_LIST);
        let big = h.alloc_struct(id);
        h.write_field(big, 0, FzValue(cons));
        let mut root = big as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.fragments.len(), 1, "fragment survives");
        // cons survives in to-space; read child from fragment payload.
        let child_bits = unsafe { std::ptr::read((big as *const u8).add(16) as *const u64) };
        let child = crate::fz_value::list_addr_from_tagged(child_bits).unwrap();
        unsafe {
            let cons = &*(child as *const ListCons);
            assert_eq!(cons.head_kind(), crate::fz_value::ValueKind::INT);
            assert_eq!(cons.head as i64, 7);
        }
    }

    /// Heap::drop with live fragments deallocates them (no leak).
    /// Verified indirectly: drop without panic, and a follow-up alloc
    /// at the same allocator gets a fresh pointer.
    #[test]
    fn heap_drop_releases_fragments_without_leak() {
        // Two heaps in sequence: first holds a fragment then drops; the
        // drop frees the fragment. Second heap can allocate without
        // tripping anything in the allocator's reuse path.
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let _ = h.alloc(FRAGMENT_THRESHOLD + 16);
            assert_eq!(h.fragments.len(), 1);
        }
        let mut h2 = Heap::new(SIZE_TABLE[0], empty_registry());
        let p = h2.alloc(FRAGMENT_THRESHOLD + 16);
        assert!(!p.is_null());
    }

    #[test]
    fn procbin_round_trips_through_bitstring_dispatchers() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let bytes: Vec<u8> = (0..100u8).collect();
        let p = h.alloc_bitstring(&bytes, 800);
        let bl = unsafe { bitstring_bit_len(p) };
        let bp = unsafe { bitstring_byte_ptr(p) };
        assert_eq!(bl, 800);
        let recovered: Vec<u8> = (0..100).map(|i| unsafe { *bp.add(i) }).collect();
        assert_eq!(recovered, bytes);
    }
}
