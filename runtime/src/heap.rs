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

#![allow(dead_code)]

use crate::fz_value::{AnyValue, ListCons, ValueKind};
use crate::procbin::{ProcBin, SharedBinHandle, alloc_procbin, mso_drop_all, mso_sweep};
use crate::tagged_value_ref::{
    TaggedRefPacking, TaggedValueRef, TaggedValueRefError, TaggedValueTag,
};
use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Copy)]
struct CopiedObject {
    ptr: *mut u8,
    tag: u64,
}

/// Facts from one Cheney collection. These are runtime telemetry: the GC
/// records what it actually copied and which layout-local slots it treated as
/// child edges. Scalar slots are still copied as bytes inside their containing
/// live object; they are counted here only to prove the collector did not
/// follow their payload as a pointer.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GcStats {
    pub copied_objects: u64,
    pub copied_bytes: u64,
    pub fragment_survivors: u64,
    pub fragment_live_bytes: u64,
    pub live_objects: u64,
    pub live_bytes: u64,
    pub from_space_capacity_bytes: u64,
    pub to_space_capacity_bytes: u64,
    pub size_class: u8,
    pub root_heap_edges: u64,
    pub root_scalar_slots: u64,
    pub list_head_heap_edges: u64,
    pub list_head_scalar_slots: u64,
    pub list_tail_edges: u64,
    pub struct_heap_edges: u64,
    pub struct_scalar_slots: u64,
    pub map_heap_edges: u64,
    pub map_scalar_slots: u64,
    pub closure_heap_edges: u64,
    pub closure_scalar_slots: u64,
    pub resource_heap_edges: u64,
    pub resource_scalar_slots: u64,
}

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
    /// Dynamic field stored as a raw payload plus compact kind metadata.
    /// GC traces heap-kind payloads.
    AnyValue,
    /// 8 bytes of raw f64 payload. GC tracer skips this slot. Introduced by
    /// fz-ul4.27.5.2 to let typed-float entry-frame params live as raw f64
    /// instead of as a tagged heap object.
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
    /// fz-ul4.38 — canonical `Tuple{N}` schema. N typed any values at offsets
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
                    kind: FieldKind::AnyValue,
                })
                .collect(),
        }
    }

    pub fn value_field_count(&self) -> usize {
        self.fields
            .iter()
            .filter(|field| field.kind == FieldKind::AnyValue)
            .count()
    }

    pub fn allocation_payload_size(&self) -> usize {
        let kind_bytes = (self.value_field_count() + 7) & !7;
        self.size as usize + kind_bytes
    }

    pub fn value_field_kind_offset(&self, field_offset: u32) -> u32 {
        let mut index = 0u32;
        for field in &self.fields {
            if field.kind == FieldKind::AnyValue {
                if field.offset == field_offset {
                    return self.size + index;
                }
                index += 1;
            }
        }
        panic!(
            "schema {} has no AnyValue field at offset {}",
            self.name, field_offset
        );
    }

    pub fn fz_value_fields_with_kind_offsets(
        &self,
    ) -> impl Iterator<Item = (&FieldDescriptor, u32)> {
        let mut index = 0u32;
        self.fields.iter().filter_map(move |field| {
            if field.kind != FieldKind::AnyValue {
                return None;
            }
            let kind_offset = self.size + index;
            index += 1;
            Some((field, kind_offset))
        })
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
    pub pending_dtors: std::collections::VecDeque<(u64, u64, u8)>,
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
            last_gc_stats: GcStats::default(),
            abandoned_blocks: Vec::new(),
            schemas,
            pressure: std::sync::atomic::AtomicBool::new(false),
            // Default: half the block. Tunable per-Process for tests that
            // want to force the park-time GC hook to fire.
            gc_threshold_bytes: block_size / 2,
            gc_run_count: 0,
            alloc_count: 0,
            mso_head: 0,
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
    pub fn alloc(&mut self, size: usize) -> *mut u8 {
        let size = (size + 15) & !15;
        assert!(
            size >= 16,
            "alloc must reserve at least one 16-byte object slot"
        );
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
            return ptr;
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
            crate::yield_flag::request();
        }
        p
    }

    pub fn alloc_struct(&mut self, schema_id: u32) -> *mut u8 {
        let payload_size = self
            .schemas
            .borrow()
            .get(schema_id)
            .allocation_payload_size();
        let total = crate::fz_value::struct_size_for_payload(payload_size);
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(p as *mut u32, schema_id);
            std::ptr::write(p.add(4) as *mut u32, 0);
            // Zero payload.
            std::ptr::write_bytes(p.add(8), 0, total - 8);
        }
        p
    }

    fn alloc_list_cons_value(&mut self, head: TaggedValueRef, tail_bits: u64) -> u64 {
        let p = self.alloc(16);
        unsafe {
            let cons = &mut *(p as *mut ListCons);
            write_ref_to_storage(&mut cons.head, None, head);
            cons.link = crate::fz_value::list_tail_addr_from_bits(tail_bits)
                | crate::fz_value::value_kind_from_ref_tag(head.tag())
                    .expect("list head kind")
                    .tag() as u64;
        }
        crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::LIST)
    }

    pub fn alloc_list_cons_slot(&mut self, head: AnyValue, tail_bits: u64) -> u64 {
        let p = self.alloc(16);
        unsafe {
            let cons = &mut *(p as *mut ListCons);
            write_any_value_to_storage(&mut cons.head, None, head);
            cons.link =
                crate::fz_value::list_tail_addr_from_bits(tail_bits) | head.kind().tag() as u64;
        }
        crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::LIST)
    }

    pub fn alloc_list_cons_ref(
        &mut self,
        head: TaggedValueRef,
        tail: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        reject_scalar_ref_write("alloc_list_cons_ref head", head);
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_value(head, tail_bits);
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("new list addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr)
    }

    pub fn alloc_list_cons_int(
        &mut self,
        head: i64,
        tail: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_slot(AnyValue::int(head), tail_bits);
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("new list addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr)
    }

    pub fn alloc_list_cons_float(
        &mut self,
        head: f64,
        tail: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_slot(AnyValue::float(head), tail_bits);
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("new list addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr)
    }

    pub fn alloc_list_cons_atom(
        &mut self,
        atom_id: u32,
        tail: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_slot(AnyValue::atom(atom_id), tail_bits);
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("new list addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr)
    }

    pub fn current_heap_tagged_addr(&self, bits: u64) -> Option<(ValueKind, *mut u8)> {
        let kind = crate::fz_value::heap_kind_from_tagged(bits)?;
        let p = (bits & !crate::fz_value::TAG_MASK) as *mut u8;
        (!p.is_null() && self.contains_heap_addr(p)).then_some((kind, p))
    }

    pub fn current_heap_addr_for_kind(&self, bits: u64, kind: ValueKind) -> Option<*mut u8> {
        self.current_heap_tagged_addr(bits)
            .and_then(|(actual, p)| (actual == kind).then_some(p))
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
    pub fn alloc_map_refs_bits(&mut self, entries: &[(TaggedValueRef, TaggedValueRef)]) -> u64 {
        let total = crate::fz_value::map_size_for_count(entries.len());
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(p as *mut u64, entries.len() as u64);
            let tag_p = crate::fz_value::map_tag_ptr(p);
            std::ptr::write_bytes(tag_p, 0, crate::fz_value::map_tag_bytes_len(entries.len()));
            let keys = crate::fz_value::map_keys_ptr(p, entries.len());
            let values = crate::fz_value::map_values_ptr(p, entries.len());
            for (i, (key, value)) in entries.iter().copied().enumerate() {
                let key_kind =
                    crate::fz_value::value_kind_from_ref_tag(key.tag()).expect("key kind");
                let value_kind =
                    crate::fz_value::value_kind_from_ref_tag(value.tag()).expect("value kind");
                std::ptr::write(
                    tag_p.add(i),
                    crate::fz_value::map_pack_tag(key_kind, value_kind),
                );
                write_ref_to_storage(keys.add(i), None, key);
                write_ref_to_storage(values.add(i), None, value);
            }
        }
        crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::MAP)
    }

    pub fn alloc_map_slots(&mut self, entries: &[(AnyValue, AnyValue)]) -> u64 {
        let total = crate::fz_value::map_size_for_count(entries.len());
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(p as *mut u64, entries.len() as u64);
            let tag_p = crate::fz_value::map_tag_ptr(p);
            std::ptr::write_bytes(tag_p, 0, crate::fz_value::map_tag_bytes_len(entries.len()));
            let keys = crate::fz_value::map_keys_ptr(p, entries.len());
            let values = crate::fz_value::map_values_ptr(p, entries.len());
            for (i, (key, value)) in entries.iter().copied().enumerate() {
                std::ptr::write(
                    tag_p.add(i),
                    crate::fz_value::map_pack_tag(key.kind(), value.kind()),
                );
                write_any_value_to_storage(keys.add(i), None, key);
                write_any_value_to_storage(values.add(i), None, value);
            }
        }
        crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::MAP)
    }

    pub fn alloc_map_refs(
        &mut self,
        entries: &[(TaggedValueRef, TaggedValueRef)],
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let map_bits = self.alloc_map_refs_bits(entries);
        let map_addr = crate::fz_value::map_addr_from_tagged(map_bits).expect("new map addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::Map, map_addr)
    }

    pub fn map_put_ref(
        &mut self,
        map: TaggedValueRef,
        key: TaggedValueRef,
        value: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        reject_scalar_ref_write("map_put_ref value", value);
        self.map_put_value(map, key, value)
    }

    pub fn map_put_int(
        &mut self,
        map: TaggedValueRef,
        key: TaggedValueRef,
        value: i64,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let value = value as u64;
        let value = TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &value)?;
        self.map_put_value(map, key, value)
    }

    pub fn map_put_float(
        &mut self,
        map: TaggedValueRef,
        key: TaggedValueRef,
        value: f64,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let value = value.to_bits();
        let value = TaggedValueRef::from_scalar_slot(TaggedValueTag::Float, &value)?;
        self.map_put_value(map, key, value)
    }

    pub fn map_put_atom(
        &mut self,
        map: TaggedValueRef,
        key: TaggedValueRef,
        atom_id: u32,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let atom_id = atom_id as u64;
        let value = TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, &atom_id)?;
        self.map_put_value(map, key, value)
    }

    fn map_put_value(
        &mut self,
        map: TaggedValueRef,
        key: TaggedValueRef,
        value: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let map_addr = map.map_addr()?;
        let map_bits = self.map_put_value_bits(map_addr, key, value);
        let map_addr = crate::fz_value::map_addr_from_tagged(map_bits).expect("new map addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::Map, map_addr)
    }

    fn map_put_value_bits(
        &mut self,
        map_addr: *mut u8,
        key: TaggedValueRef,
        value: TaggedValueRef,
    ) -> u64 {
        let count = unsafe { crate::fz_value::map_count(map_addr) };
        let mut entries = Vec::with_capacity(count + 1);
        let mut replaced = false;

        for i in 0..count {
            let (entry_key, entry_value) = unsafe { map_entry_refs(map_addr, i) };
            if !replaced && same_value_ref(entry_key, key) {
                entries.push((key, value));
                replaced = true;
            } else {
                entries.push((entry_key, entry_value));
            }
        }
        if !replaced {
            entries.push((key, value));
        }

        entries.sort_by(|a, b| map_key_cmp_refs(a.0, b.0));
        self.alloc_map_refs_bits(&entries)
    }

    pub fn map_put_slot_bits(&mut self, map_bits: u64, key: AnyValue, value: AnyValue) -> u64 {
        let map_addr = crate::fz_value::map_addr_from_tagged(map_bits);
        let count = map_addr.map_or(0, |addr| unsafe { crate::fz_value::map_count(addr) });
        let mut entries = Vec::with_capacity(count + 1);
        let mut replaced = false;
        if let Some(map_addr) = map_addr {
            for i in 0..count {
                let (entry_key, entry_value) = unsafe { crate::fz_value::map_entry(map_addr, i) };
                if !replaced && same_any_value(entry_key, key) {
                    entries.push((key, value));
                    replaced = true;
                } else {
                    entries.push((entry_key, entry_value));
                }
            }
        }
        if !replaced {
            entries.push((key, value));
        }
        entries.sort_by(|a, b| map_key_cmp_any(a.0, b.0));
        self.alloc_map_slots(&entries)
    }

    /// Strict inline Bitstring layout: bit_len: u64 + bytes (padded to 16).
    /// Caller supplies a fully-built byte buffer + bit_len; this performs the
    /// heap copy.
    ///
    /// fz-cty.5 — payloads larger than `SHARED_BIN_THRESHOLD_BYTES` route
    /// through the shared zone: a SharedBin is allocated off-heap and the
    /// per-process heap gets a 16-byte tagged ProcBin stub referencing
    /// it. Render and bit-match dispatch via
    /// `bitstring_bit_len` / `bitstring_byte_ptr`.
    pub fn alloc_bitstring(&mut self, bytes: &[u8], bit_len: u64) -> *mut u8 {
        if bytes.len() > SHARED_BIN_THRESHOLD_BYTES {
            let handle = SharedBinHandle::from_bytes(bytes, bit_len);
            return alloc_procbin(self, handle).as_raw();
        }
        // fz-wu9 — reserve at least 1 byte past the payload for the
        // invisible trailing NUL. The pad-zeroing below guarantees it reads
        // as 0; bytes_len / bit_len are unchanged.
        let total = crate::fz_value::bitstring_size_for_bit_len(bit_len);
        let p = self.alloc(total);
        unsafe {
            let bit_len_p = p as *mut u64;
            std::ptr::write(bit_len_p, bit_len);
            let bytes_p = p.add(8);
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), bytes_p, bytes.len());
            // Zero the trailing padding so renders / debug aren't garbage.
            let pad_start = 8 + bytes.len();
            if pad_start < total {
                std::ptr::write_bytes(p.add(pad_start), 0, total - pad_start);
            }
        }
        p
    }

    /// Strict Closure layout:
    ///   `schema_id: u32, flags: u32, fn_ptr: u64,
    ///    capture_raw: [u64; n], capture_kind: [u8; n]`.
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
                p.add(4) as *mut u32,
                crate::fz_value::closure_flags_pack(captured_count as u16, halt_kind) as u32,
            );
            std::ptr::write(p.add(8) as *mut u64, 0);
            if total > 16 {
                std::ptr::write_bytes(p.add(16), 0, total - 16);
            }
        }
        crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::CLOSURE)
    }

    pub fn alloc_closure(
        &mut self,
        schema_id: u32,
        captured_count: usize,
        halt_kind: u16,
        fn_ptr: u64,
        captures: &[AnyValue],
    ) -> u64 {
        assert!(
            captures.len() <= captured_count,
            "too many closure captures"
        );
        let bits = self.alloc_closure_slots(schema_id, captured_count, halt_kind);
        let p = crate::fz_value::closure_addr_from_tagged(bits).expect("new closure ptr");
        unsafe {
            std::ptr::write(p.add(8) as *mut u64, fn_ptr);
            for (i, capture) in captures.iter().enumerate() {
                crate::fz_value::closure_capture_set(p, i, *capture);
            }
        }
        bits
    }

    /// # Safety
    ///
    /// `closure_addr` must point to a live closure allocation with a capture
    /// slot at `idx`.
    pub unsafe fn write_closure_capture_value(
        &mut self,
        closure_addr: *mut u8,
        idx: usize,
        value: AnyValue,
    ) {
        unsafe { crate::fz_value::closure_capture_set(closure_addr, idx, value) };
    }

    pub fn write_closure_capture_ref(
        &mut self,
        closure: TaggedValueRef,
        idx: usize,
        value: TaggedValueRef,
    ) -> Result<(), TaggedValueRefError> {
        let closure = closure.closure_addr()?;
        unsafe { crate::fz_value::closure_capture_set(closure, idx, any_value_from_ref(value)?) };
        Ok(())
    }

    /// # Safety
    ///
    /// `closure_addr` must point to a live closure allocation with a capture
    /// slot at `idx`.
    pub unsafe fn read_closure_capture_value(
        &self,
        closure_addr: *const u8,
        idx: usize,
    ) -> AnyValue {
        unsafe { crate::fz_value::closure_capture_value(closure_addr, idx) }
    }

    /// Write a canonical value into a Struct's generic payload slot.
    pub fn write_field_slot(&mut self, obj: *mut u8, field_offset: u32, value: AnyValue) {
        self.write_struct_field_value(obj, field_offset, value);
    }

    pub fn write_struct_field_ref(
        &mut self,
        obj: TaggedValueRef,
        field_offset: u32,
        value: TaggedValueRef,
    ) -> Result<(), TaggedValueRefError> {
        let obj = obj.struct_addr()?;
        self.write_struct_field_value(obj, field_offset, any_value_from_ref(value)?);
        Ok(())
    }

    fn write_struct_field_value(&self, obj: *mut u8, field_offset: u32, value: AnyValue) {
        let schema_id = unsafe { crate::fz_value::struct_schema_id(obj as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        let raw = value.raw();
        unsafe {
            std::ptr::write(
                crate::fz_value::struct_field_raw_slot(obj as *const u8, field_offset),
                raw,
            );
            std::ptr::write(
                crate::fz_value::struct_field_kind_slot(obj as *const u8, kind_offset),
                value.kind().tag(),
            );
        }
    }

    /// Read a canonical value from a Struct's generic payload slot.
    pub fn read_field_slot(&self, obj: *mut u8, field_offset: u32) -> AnyValue {
        let schema_id = unsafe { crate::fz_value::struct_schema_id(obj as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        unsafe {
            let raw = std::ptr::read(crate::fz_value::struct_field_raw_slot(
                obj as *const u8,
                field_offset,
            ));
            let kind = std::ptr::read(crate::fz_value::struct_field_kind_slot(
                obj as *const u8,
                kind_offset,
            ));
            AnyValue::decode_parts(raw, kind).expect("struct field kind")
        }
    }

    pub fn read_list_head_ref(
        &self,
        list: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let addr = list.list_addr()?;
        let cons = unsafe { &*(addr as *const ListCons) };
        tagged_ref_from_storage(&cons.head as *const u64, cons.head_kind())
    }

    pub fn read_list_tail_ref(
        &self,
        list: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let addr = list.list_addr()?;
        let cons = unsafe { &*(addr as *const ListCons) };
        let tail_addr = cons.tail_addr();
        if tail_addr == 0 {
            Ok(TaggedValueRef::empty_list())
        } else {
            TaggedValueRef::from_heap_object(TaggedValueTag::List, tail_addr as *const u8)
        }
    }

    pub fn read_map_value_ref(
        &self,
        map: TaggedValueRef,
        key: TaggedValueRef,
    ) -> Result<Option<TaggedValueRef>, TaggedValueRefError> {
        let addr = map.map_addr()?;
        self.read_map_addr_value_ref(addr, key)
    }

    fn read_map_addr_value_ref(
        &self,
        addr: *mut u8,
        key: TaggedValueRef,
    ) -> Result<Option<TaggedValueRef>, TaggedValueRefError> {
        let count = unsafe { crate::fz_value::map_count(addr) };

        for i in 0..count {
            let (entry_key, entry_value) = unsafe { map_entry_refs(addr, i) };
            if !same_value_ref(entry_key, key) {
                continue;
            }
            return Ok(Some(entry_value));
        }
        Ok(None)
    }

    pub fn read_map_value_for_any_key(
        &self,
        map: TaggedValueRef,
        key: AnyValue,
    ) -> Result<Option<TaggedValueRef>, TaggedValueRefError> {
        let addr = map.map_addr()?;
        let count = unsafe { crate::fz_value::map_count(addr) };
        for i in 0..count {
            let (entry_key, _) = unsafe { crate::fz_value::map_entry(addr, i) };
            if !same_any_value(entry_key, key) {
                continue;
            }
            let (_, entry_value) = unsafe { map_entry_refs(addr, i) };
            return Ok(Some(entry_value));
        }
        Ok(None)
    }

    pub fn read_struct_field_ref(
        &self,
        obj: TaggedValueRef,
        field_offset: u32,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let addr = obj.struct_addr()?;
        let schema_id = unsafe { crate::fz_value::struct_schema_id(addr as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        let raw_slot =
            unsafe { crate::fz_value::struct_field_raw_slot(addr as *const u8, field_offset) };
        let kind = unsafe {
            std::ptr::read(crate::fz_value::struct_field_kind_slot(
                addr as *const u8,
                kind_offset,
            ))
        };
        tagged_ref_from_storage(
            raw_slot as *const u64,
            ValueKind::new(kind).expect("struct field kind"),
        )
    }

    pub fn read_closure_capture_ref(
        &self,
        closure: TaggedValueRef,
        idx: usize,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let addr = closure.closure_addr()?;
        let raw_slot = unsafe { crate::fz_value::closure_capture_raw_slot(addr as *const u8, idx) };
        let kind_slot =
            unsafe { crate::fz_value::closure_capture_kind_slot(addr as *const u8, idx) };
        let kind = unsafe { std::ptr::read(kind_slot) };
        tagged_ref_from_storage(
            raw_slot as *const u64,
            ValueKind::new(kind).expect("closure capture kind"),
        )
    }

    /// Register a schema in this heap's registry, returning its id. Codegen
    /// uses this to register tuple-arity / closure / record schemas at JIT
    /// compile time so the tracer can walk their typed fields.
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

    /// Always zero under bump-only. Retained for tests asserting freelist
    /// invariants; .8 / .9 may remove entirely.
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

    /// Park-time Cheney GC (§6.4). The caller passes a primary closure root
    /// by mutable pointer; on return it is updated to the to-space copy (or
    /// left null on entry — nothing to trace, just recycle blocks).
    ///
    /// Algorithm: standard Cheney two-finger BFS. Allocate a to-space block
    /// at the chosen size_class (§6.3 / §6.5 picker), copy the root, then
    /// scan to-space objects breadth-first, forwarding each from-space
    /// child pointer to its newly-copied address. Off-heap pointers
    /// (static-closure / halt-cont singletons) are detected by an
    /// in-from-space range check and left untouched.
    pub fn gc(&mut self, root_slot: &mut *mut u8) -> GcStats {
        self.gc_with_extra_root_slots(root_slot, &mut [])
    }

    /// Cheney GC with an optional slice of extra typed roots. Each element is
    /// forwarded in-place.
    pub fn gc_with_extra_root_slots(
        &mut self,
        root_slot: &mut *mut u8,
        extra_roots: &mut [AnyValue],
    ) -> GcStats {
        self.gc_with_extra_roots(root_slot, extra_roots, &mut [])
    }

    pub fn gc_with_tagged_ref_roots(
        &mut self,
        root_slot: &mut *mut u8,
        ref_roots: &mut [TaggedValueRef],
    ) -> GcStats {
        self.gc_with_extra_roots(root_slot, &mut [], ref_roots)
    }

    pub fn gc_with_value_and_tagged_ref_roots(
        &mut self,
        root_slot: &mut *mut u8,
        extra_roots: &mut [AnyValue],
        ref_roots: &mut [TaggedValueRef],
    ) -> GcStats {
        self.gc_with_extra_roots(root_slot, extra_roots, ref_roots)
    }

    fn gc_with_extra_roots(
        &mut self,
        root_slot: &mut *mut u8,
        extra_roots: &mut [AnyValue],
        ref_roots: &mut [TaggedValueRef],
    ) -> GcStats {
        // Snapshot from-space block ranges before we allocate to-space.
        let mut from_ranges: Vec<(*mut u8, *mut u8)> =
            Vec::with_capacity(1 + self.abandoned_blocks.len());
        from_ranges.push((self.block_start, self.block_end));
        for &(p, sc) in &self.abandoned_blocks {
            from_ranges.push((p, unsafe { p.add(SIZE_TABLE[sc as usize]) }));
        }
        let from_space_capacity_bytes: usize = from_ranges
            .iter()
            .map(|(start, end)| unsafe { end.offset_from(*start) as usize })
            .sum();

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
        let mut frag_queue: Vec<CopiedObject> = Vec::new();
        let mut copied_objects: Vec<CopiedObject> = Vec::new();
        let mut stats = GcStats {
            from_space_capacity_bytes: from_space_capacity_bytes as u64,
            to_space_capacity_bytes: to_size as u64,
            size_class,
            ..GcStats::default()
        };

        if !root_slot.is_null() {
            stats.root_heap_edges += 1;
            let root_bits = *root_slot as u64;
            if let Some(new_root) = cheney_forward_strict_bits(
                root_bits,
                &from_ranges,
                &mut self.fragments,
                &mut frag_queue,
                &mut free,
                to_end,
                &self.schemas.borrow(),
                &mut copied_objects,
                &mut stats,
            ) {
                *root_slot = new_root as *mut u8;
            }
        }

        // Forward extra roots (mid-flight args, mailbox items).
        for value in extra_roots.iter_mut() {
            if !value.kind().is_heap() || value.raw() == 0 {
                stats.root_scalar_slots += 1;
                continue;
            }
            stats.root_heap_edges += 1;
            let bits = value
                .heap_object_word()
                .expect("heap root should encode as tagged bits");
            if let Some(new_bits) = cheney_forward_strict_bits(
                bits,
                &from_ranges,
                &mut self.fragments,
                &mut frag_queue,
                &mut free,
                to_end,
                &self.schemas.borrow(),
                &mut copied_objects,
                &mut stats,
            ) {
                *value = AnyValue::heap_ptr(
                    (new_bits & !crate::fz_value::TAG_MASK) as *mut u8,
                    value.kind(),
                );
            }
        }

        for value in ref_roots.iter_mut() {
            forward_tagged_ref_root(
                value,
                &from_ranges,
                &mut self.fragments,
                &mut frag_queue,
                &mut free,
                to_end,
                &self.schemas.borrow(),
                &mut copied_objects,
                &mut stats,
            );
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
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_MAP => cheney_trace_map(
                        copied.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_CLOSURE => cheney_trace_closure(
                        copied.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_STRUCT => cheney_trace_struct(
                        copied.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_BITSTRING | crate::fz_value::TAG_PROCBIN => {}
                    crate::fz_value::TAG_RESOURCE => cheney_trace_resource(
                        copied.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    tag => panic!("Cheney scan: invalid copied object tag {tag:#x}"),
                }
            }
            // Drain fragment queue. Each fragment's children may forward
            // either into to-space (which extends `free`, picked up by
            // the loop above on the next iteration) or into another
            // fragment (re-pushes to frag_queue).
            if let Some(frag) = frag_queue.pop() {
                match frag.tag {
                    crate::fz_value::TAG_LIST => cheney_trace_list(
                        frag.ptr as *mut ListCons,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_MAP => cheney_trace_map(
                        frag.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_CLOSURE => cheney_trace_closure(
                        frag.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_STRUCT => cheney_trace_struct(
                        frag.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_BITSTRING | crate::fz_value::TAG_PROCBIN => {}
                    crate::fz_value::TAG_RESOURCE => cheney_trace_resource(
                        frag.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    tag => panic!("Cheney scan: invalid fragment object tag {tag:#x}"),
                }
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
        let mut fragment_live_bytes = 0usize;
        let mut i = 0;
        while i < self.fragments.len() {
            if self.fragments[i].mark {
                self.fragments[i].mark = false;
                fragment_live_bytes += self.fragments[i].size;
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
        stats.fragment_survivors = live_count.saturating_sub(copied_objects.len() as u64);
        stats.fragment_live_bytes = fragment_live_bytes as u64;
        stats.live_objects = live_count;
        stats.live_bytes = self.last_gc_live_bytes as u64 + stats.fragment_live_bytes;
        self.last_gc_stats = stats;
        stats
    }

    /// Cheney with a scheduler-owned primary closure root plus persistent
    /// process roots. This is the closure-shaped mid-flight path: the
    /// continuation closure captures the live loop state, while mailbox
    /// entries remain process-owned roots until consumed.
    pub fn gc_process_roots(
        &mut self,
        primary_root: &mut *mut u8,
        mailbox: &mut std::collections::VecDeque<TaggedValueRef>,
    ) -> GcStats {
        let mut mb_roots: Vec<TaggedValueRef> = mailbox.drain(..).collect();
        let stats = self.gc_with_extra_roots(primary_root, &mut [], &mut mb_roots);

        for v in mb_roots {
            mailbox.push_back(v);
        }
        stats
    }

    /// Cheney with interpreter-owned typed roots plus persistent process roots.
    /// The interpreter has no parked continuation closure while it is
    /// synchronously executing a tail-recursive loop, so its current argument
    /// vector is the root set.
    pub fn gc_any_value_roots_with_process_roots(
        &mut self,
        roots: &mut [AnyValue],
        mailbox: &mut std::collections::VecDeque<TaggedValueRef>,
    ) -> GcStats {
        let mut null_root: *mut u8 = std::ptr::null_mut();
        let mut mb_roots: Vec<TaggedValueRef> = mailbox.drain(..).collect();
        let mut all_extras: Vec<AnyValue> = roots.to_vec();

        let stats = self.gc_with_extra_roots(&mut null_root, &mut all_extras, &mut mb_roots);

        let roots_end = roots.len();
        roots.copy_from_slice(&all_extras[..roots_end]);
        for v in mb_roots {
            mailbox.push_back(v);
        }
        stats
    }
}

pub fn deep_copy_tagged_ref(
    value: TaggedValueRef,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> TaggedValueRef {
    match value.tag() {
        TaggedValueTag::Null | TaggedValueTag::EmptyList => value,
        tag if tag.is_scalar() => {
            let src = value_ref_addr(value);
            let dst = dst_heap.alloc(8);
            unsafe {
                std::ptr::write(dst as *mut u64, std::ptr::read(src as *const u64));
            }
            TaggedValueRef::from_scalar_slot(tag, dst as *const u64)
                .expect("deep-copied scalar ref")
        }
        tag if tag.is_heap_object() => {
            let bits = value_ref_heap_bits(value);
            let copied = deep_copy_tagged_bits(bits, src_heap, dst_heap, forwarding);
            let addr = (copied & !crate::fz_value::TAG_MASK) as *const u8;
            TaggedValueRef::from_heap_object(tag, addr).expect("deep-copied heap ref")
        }
        _ => unreachable!("TaggedValueRef tag set is exhaustive"),
    }
}

pub fn deep_copy_tagged_bits(
    bits: u64,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> u64 {
    let copied = deep_copy_fz_value(
        AnyValue::decode_tagged_heap_bits(bits).expect("deep_copy_tagged_bits expects heap bits"),
        src_heap,
        dst_heap,
        forwarding,
    );
    copied
        .heap_object_word()
        .expect("deep_copy_tagged_bits copied heap bits")
}

/// Compute the 75%-of-block watermark pointer.
fn watermark_for(block_start: *mut u8, block_size: usize) -> *mut u8 {
    let offset = (block_size * 3) / 4;
    unsafe { block_start.add(offset) }
}

#[allow(clippy::too_many_arguments)]
fn cheney_forward_strict_bits(
    bits: u64,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> Option<u64> {
    let kind = crate::fz_value::heap_kind_from_tagged(bits)?;
    let addr = bits & !crate::fz_value::TAG_MASK;
    if addr == 0 {
        return None;
    }
    let p = addr as *mut u8;
    let in_block = ptr_in_from_space(p, from_ranges);
    let in_frag = classify_fragment(p, fragments).is_some();
    if !in_block && !in_frag {
        return None;
    }
    let new_p = cheney_forward_object(
        kind,
        bits,
        p,
        fragments,
        frag_queue,
        free,
        to_end,
        schemas,
        copied_objects,
        stats,
    );
    Some((new_p as u64) | kind.tag() as u64)
}

#[allow(clippy::too_many_arguments)]
fn forward_tagged_ref_root(
    value: &mut TaggedValueRef,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    match value.tag() {
        TaggedValueTag::Null | TaggedValueTag::EmptyList => {
            stats.root_scalar_slots += 1;
        }
        tag if tag.is_scalar() => {
            stats.root_scalar_slots += 1;
            let p = value_ref_addr(*value);
            if !is_active_from_space_object(p, from_ranges, fragments) {
                return;
            }
            let dst = copy_scalar_box_to_space(p, free, to_end, stats);
            *value = TaggedValueRef::from_scalar_slot(tag, dst as *const u64)
                .expect("forwarded scalar root ref");
        }
        tag if tag.is_heap_object() => {
            stats.root_heap_edges += 1;
            let bits = value_ref_heap_bits(*value);
            if let Some(new_bits) = cheney_forward_strict_bits(
                bits,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
                stats,
            ) {
                let new_addr = (new_bits & !crate::fz_value::TAG_MASK) as *const u8;
                *value =
                    TaggedValueRef::from_heap_object(tag, new_addr).expect("forwarded heap root");
            }
        }
        _ => unreachable!("TaggedValueRef tag set is exhaustive"),
    }
}

fn value_ref_addr(value: TaggedValueRef) -> *mut u8 {
    (value.raw_word() & TaggedRefPacking::current().address_mask()) as *mut u8
}

fn value_ref_heap_bits(value: TaggedValueRef) -> u64 {
    let addr = value_ref_addr(value) as u64;
    let tag = match value.tag() {
        TaggedValueTag::List => crate::fz_value::TAG_LIST,
        TaggedValueTag::Map => crate::fz_value::TAG_MAP,
        TaggedValueTag::Struct => crate::fz_value::TAG_STRUCT,
        TaggedValueTag::Closure => crate::fz_value::TAG_CLOSURE,
        TaggedValueTag::Bitstring => crate::fz_value::TAG_BITSTRING,
        TaggedValueTag::ProcBin => crate::fz_value::TAG_PROCBIN,
        TaggedValueTag::Resource => crate::fz_value::TAG_RESOURCE,
        tag => panic!("expected heap-object ref, got {tag:?}"),
    };
    addr | tag
}

fn copy_scalar_box_to_space(
    p: *mut u8,
    free: &mut *mut u8,
    to_end: *mut u8,
    stats: &mut GcStats,
) -> *mut u8 {
    let dst = copy_object_to_space(p, 16, free, to_end);
    stats.copied_objects += 1;
    stats.copied_bytes += 16;
    dst
}

fn strict_object_size(bits: u64, schemas: &SchemaRegistry) -> usize {
    crate::fz_value::object_size_with_struct_payload(bits, |schema_id| {
        schemas.get(schema_id).allocation_payload_size()
    })
}

fn tagged_ref_from_storage(
    raw_slot: *const u64,
    kind: ValueKind,
) -> Result<TaggedValueRef, TaggedValueRefError> {
    let raw = unsafe { std::ptr::read(raw_slot) };
    match tagged_ref_tag_from_value_kind(raw, kind) {
        TaggedValueTag::Null => Ok(TaggedValueRef::null()),
        TaggedValueTag::EmptyList => Ok(TaggedValueRef::empty_list()),
        tag if tag.is_scalar() => TaggedValueRef::from_scalar_slot(tag, raw_slot),
        tag => TaggedValueRef::from_heap_object(tag, raw as *const u8),
    }
}

fn tagged_ref_tag_from_value_kind(raw: u64, kind: ValueKind) -> TaggedValueTag {
    match kind.tag() as u64 {
        crate::fz_value::TAG_NULL => TaggedValueTag::Null,
        crate::fz_value::TAG_KIND_INT => TaggedValueTag::Int,
        crate::fz_value::TAG_KIND_FLOAT => TaggedValueTag::Float,
        crate::fz_value::TAG_KIND_ATOM => TaggedValueTag::Atom,
        crate::fz_value::TAG_LIST if raw == 0 => TaggedValueTag::EmptyList,
        crate::fz_value::TAG_LIST => TaggedValueTag::List,
        crate::fz_value::TAG_MAP => TaggedValueTag::Map,
        crate::fz_value::TAG_STRUCT => TaggedValueTag::Struct,
        crate::fz_value::TAG_CLOSURE => TaggedValueTag::Closure,
        crate::fz_value::TAG_BITSTRING => TaggedValueTag::Bitstring,
        crate::fz_value::TAG_PROCBIN => TaggedValueTag::ProcBin,
        crate::fz_value::TAG_RESOURCE => TaggedValueTag::Resource,
        _ => unreachable!("unknown ValueKind"),
    }
}

pub fn any_value_from_ref(value: TaggedValueRef) -> Result<AnyValue, TaggedValueRefError> {
    Ok(match value.tag() {
        TaggedValueTag::Null => AnyValue::null(),
        TaggedValueTag::EmptyList => AnyValue::empty_list(),
        TaggedValueTag::Int => AnyValue::int(value.load_int()?),
        TaggedValueTag::Float => AnyValue::Float(value.load_float()?.to_bits()),
        TaggedValueTag::Atom => AnyValue::atom(value.load_atom()? as u32),
        tag if tag.is_heap_object() => AnyValue::HeapRef(value),
        _ => unreachable!("TaggedValueRef tag set is exhaustive"),
    })
}

fn write_ref_to_storage(raw_slot: *mut u64, kind_slot: Option<*mut u8>, value: TaggedValueRef) {
    let raw = match value.tag() {
        TaggedValueTag::Null | TaggedValueTag::EmptyList => 0,
        TaggedValueTag::Int => value.load_int().expect("int ref") as u64,
        TaggedValueTag::Float => value.load_float().expect("float ref").to_bits(),
        TaggedValueTag::Atom => value.load_atom().expect("atom ref"),
        TaggedValueTag::List => value.list_addr().expect("list ref") as u64,
        TaggedValueTag::Map => value.map_addr().expect("map ref") as u64,
        TaggedValueTag::Struct => value.struct_addr().expect("struct ref") as u64,
        TaggedValueTag::Closure => value.closure_addr().expect("closure ref") as u64,
        TaggedValueTag::Bitstring => value.bitstring_addr().expect("bitstring ref") as u64,
        TaggedValueTag::ProcBin => value.procbin_addr().expect("procbin ref") as u64,
        TaggedValueTag::Resource => value.resource_addr().expect("resource ref") as u64,
    };
    unsafe { std::ptr::write(raw_slot, raw) };
    if let Some(kind_slot) = kind_slot {
        let kind = crate::fz_value::value_kind_from_ref_tag(value.tag()).expect("value kind");
        unsafe { std::ptr::write(kind_slot, kind.tag()) };
    }
}

fn write_any_value_to_storage(raw_slot: *mut u64, kind_slot: Option<*mut u8>, value: AnyValue) {
    unsafe { std::ptr::write(raw_slot, value.raw()) };
    if let Some(kind_slot) = kind_slot {
        unsafe { std::ptr::write(kind_slot, value.kind().tag()) };
    }
}

unsafe fn map_entry_refs(addr: *mut u8, index: usize) -> (TaggedValueRef, TaggedValueRef) {
    let count = unsafe { crate::fz_value::map_count(addr) };
    let tag = unsafe { std::ptr::read(crate::fz_value::map_tag_ptr(addr).add(index)) };
    let keys = unsafe { crate::fz_value::map_keys_ptr(addr, count) };
    let values = unsafe { crate::fz_value::map_values_ptr(addr, count) };
    let key = tagged_ref_from_storage(
        unsafe { keys.add(index) },
        crate::fz_value::map_key_kind(tag),
    )
    .expect("map key ref");
    let value = tagged_ref_from_storage(
        unsafe { values.add(index) },
        crate::fz_value::map_value_kind(tag),
    )
    .expect("map value ref");
    (key, value)
}

fn reject_scalar_ref_write(context: &str, value: TaggedValueRef) {
    let tag = value.tag();
    if tag.is_scalar() {
        panic!("{context} requires a heap/sentinel ref; use the typed scalar write path");
    }
}

fn list_tail_bits_from_ref(value: TaggedValueRef) -> Result<u64, TaggedValueRefError> {
    match value.tag() {
        TaggedValueTag::EmptyList => Ok(crate::fz_value::EMPTY_LIST),
        TaggedValueTag::List => Ok(value.list_addr()? as u64 | crate::fz_value::TAG_LIST),
        found => Err(TaggedValueRefError::ExpectedTag {
            expected: TaggedValueTag::List,
            found,
        }),
    }
}

fn same_value_ref(a: TaggedValueRef, b: TaggedValueRef) -> bool {
    if matches!(a.tag(), TaggedValueTag::Bitstring | TaggedValueTag::ProcBin)
        && matches!(b.tag(), TaggedValueTag::Bitstring | TaggedValueTag::ProcBin)
    {
        let a_bits = value_ref_heap_bits(a);
        let b_bits = value_ref_heap_bits(b);
        return unsafe {
            crate::procbin::bitstring_like_eq(a_bits as *const u8, b_bits as *const u8)
        };
    }
    a.tag() == b.tag() && value_ref_sort_payload(a) == value_ref_sort_payload(b)
}

fn same_any_value(a: AnyValue, b: AnyValue) -> bool {
    if matches!(a.kind(), ValueKind::BITSTRING | ValueKind::PROCBIN)
        && matches!(b.kind(), ValueKind::BITSTRING | ValueKind::PROCBIN)
    {
        let ap = a.heap_object_word().expect("bitstring lhs") as *const u8;
        let bp = b.heap_object_word().expect("bitstring rhs") as *const u8;
        return unsafe { crate::procbin::bitstring_like_eq(ap, bp) };
    }
    a.kind() == b.kind() && a.raw() == b.raw()
}

fn map_key_cmp_any(a: AnyValue, b: AnyValue) -> std::cmp::Ordering {
    map_key_category_any(a)
        .cmp(&map_key_category_any(b))
        .then_with(|| a.kind().tag().cmp(&b.kind().tag()))
        .then_with(|| {
            if a.kind() == ValueKind::INT {
                (a.raw() as i64).cmp(&(b.raw() as i64))
            } else {
                a.raw().cmp(&b.raw())
            }
        })
}

fn map_key_category_any(value: AnyValue) -> u8 {
    match value.kind() {
        ValueKind::INT => 0,
        ValueKind::ATOM => 1,
        ValueKind::NULL => 2,
        kind if kind.is_heap() => 3,
        ValueKind::FLOAT => 4,
        _ => 5,
    }
}

fn map_key_category_ref(value: TaggedValueRef) -> u8 {
    match value.tag() {
        TaggedValueTag::Int => 0,
        TaggedValueTag::Atom => 1,
        TaggedValueTag::Null => 2,
        TaggedValueTag::Float => 4,
        _ => 3,
    }
}

fn map_key_cmp_refs(a: TaggedValueRef, b: TaggedValueRef) -> std::cmp::Ordering {
    map_key_category_ref(a)
        .cmp(&map_key_category_ref(b))
        .then_with(|| (a.tag() as u8).cmp(&(b.tag() as u8)))
        .then_with(|| {
            if a.tag() == TaggedValueTag::Int {
                a.load_int()
                    .expect("int key")
                    .cmp(&b.load_int().expect("int key"))
            } else {
                value_ref_sort_payload(a).cmp(&value_ref_sort_payload(b))
            }
        })
}

fn value_ref_sort_payload(value: TaggedValueRef) -> u64 {
    match value.tag() {
        TaggedValueTag::Null | TaggedValueTag::EmptyList => 0,
        TaggedValueTag::Int => value.load_int().expect("int") as u64,
        TaggedValueTag::Float => value.load_float().expect("float").to_bits(),
        TaggedValueTag::Atom => value.load_atom().expect("atom"),
        TaggedValueTag::List => value.list_addr().expect("list") as u64,
        TaggedValueTag::Map => value.map_addr().expect("map") as u64,
        TaggedValueTag::Struct => value.struct_addr().expect("struct") as u64,
        TaggedValueTag::Closure => value.closure_addr().expect("closure") as u64,
        TaggedValueTag::Bitstring => value.bitstring_addr().expect("bitstring") as u64,
        TaggedValueTag::ProcBin => value.procbin_addr().expect("procbin") as u64,
        TaggedValueTag::Resource => value.resource_addr().expect("resource") as u64,
    }
}

#[allow(clippy::too_many_arguments)]
fn cheney_forward_object(
    kind: ValueKind,
    bits: u64,
    p: *mut u8,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    match kind {
        ValueKind::LIST => cheney_forward_list(
            p,
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
            stats,
        ),
        ValueKind::PROCBIN => cheney_forward_procbin(
            p,
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
            stats,
        ),
        ValueKind::RESOURCE => cheney_forward_resource(
            p,
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
            stats,
        ),
        kind if kind.is_heap() => cheney_forward_headerless(
            p,
            kind.tag() as u64,
            bits,
            schemas,
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
            stats,
        ),
        _ => unreachable!("Cheney forwarding requires a heap kind"),
    }
}

fn cheney_forward_list(
    p: *mut u8,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    if mark_fragment_for_tracing(p, crate::fz_value::TAG_LIST, fragments, frag_queue) {
        return p;
    }
    if let Some(fwd) = is_forwarded_list(p) {
        return fwd as *mut u8;
    }
    copy_to_space_with_confirmed_forwarding(
        p,
        16,
        crate::fz_value::TAG_LIST,
        free,
        to_end,
        copied_objects,
        stats,
    )
}

fn cheney_forward_headerless(
    p: *mut u8,
    tag: u64,
    bits: u64,
    schemas: &SchemaRegistry,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    if mark_fragment_for_tracing(p, tag, fragments, frag_queue) {
        return p;
    }
    if let Some(fwd) = is_forwarded_headerless(p) {
        return fwd as *mut u8;
    }
    let size = strict_object_size(bits, schemas);
    copy_to_space_with_confirmed_forwarding(p, size, tag, free, to_end, copied_objects, stats)
}

fn cheney_forward_procbin(
    p: *mut u8,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    if mark_fragment_for_tracing(p, crate::fz_value::TAG_PROCBIN, fragments, frag_queue) {
        return p;
    }
    if let Some(fwd) = is_forwarded_procbin(p) {
        return fwd as *mut u8;
    }
    copy_to_space_with_first_word_forwarding(
        p,
        16,
        crate::fz_value::TAG_PROCBIN,
        free,
        to_end,
        copied_objects,
        stats,
    )
}

fn cheney_forward_resource(
    p: *mut u8,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    if mark_fragment_for_tracing(p, crate::fz_value::TAG_RESOURCE, fragments, frag_queue) {
        return p;
    }
    if let Some(fwd) = is_forwarded_resource(p) {
        return fwd as *mut u8;
    }
    copy_to_space_with_first_word_forwarding(
        p,
        32,
        crate::fz_value::TAG_RESOURCE,
        free,
        to_end,
        copied_objects,
        stats,
    )
}

fn mark_fragment_for_tracing(
    p: *mut u8,
    tag: u64,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
) -> bool {
    let Some(idx) = classify_fragment(p, fragments) else {
        return false;
    };
    if !fragments[idx].mark {
        fragments[idx].mark = true;
        frag_queue.push(CopiedObject { ptr: p, tag });
    }
    true
}

fn copy_to_space_with_confirmed_forwarding(
    p: *mut u8,
    size: usize,
    tag: u64,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    let dst = copy_object_to_space(p, size, free, to_end);
    stats.copied_objects += 1;
    stats.copied_bytes += size as u64;
    write_forwarding_marker(p, dst);
    unsafe {
        std::ptr::write(p.add(8) as *mut u64, crate::fz_value::TAG_FWD);
    }
    copied_objects.push(CopiedObject { ptr: dst, tag });
    dst
}

fn copy_to_space_with_first_word_forwarding(
    p: *mut u8,
    size: usize,
    tag: u64,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    let dst = copy_object_to_space(p, size, free, to_end);
    stats.copied_objects += 1;
    stats.copied_bytes += size as u64;
    write_forwarding_marker(p, dst);
    copied_objects.push(CopiedObject { ptr: dst, tag });
    dst
}

fn copy_object_to_space(p: *mut u8, size: usize, free: &mut *mut u8, to_end: *mut u8) -> *mut u8 {
    let dst = *free;
    let new_top = unsafe { dst.add(size) };
    assert!(new_top <= to_end, "Cheney: to-space exhausted");
    unsafe {
        std::ptr::copy_nonoverlapping(p, dst, size);
    }
    *free = new_top;
    dst
}

fn write_forwarding_marker(from: *mut u8, to: *mut u8) {
    unsafe {
        std::ptr::write(
            from as *mut u64,
            (to as u64 & !crate::fz_value::TAG_MASK) | crate::fz_value::TAG_FWD,
        );
    }
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

fn is_forwarded_procbin(addr: *const u8) -> Option<*const u8> {
    let marker = unsafe { std::ptr::read(addr as *const u64) };
    let forwarded = marker & !crate::fz_value::TAG_MASK;
    if marker & crate::fz_value::TAG_MASK == crate::fz_value::TAG_FWD && forwarded != 0 {
        Some(forwarded as *const u8)
    } else {
        None
    }
}

fn is_forwarded_resource(addr: *const u8) -> Option<*const u8> {
    is_forwarded_procbin(addr)
}

/// Return the index of the fragment containing `p`, if any.
fn classify_fragment(p: *mut u8, fragments: &[Fragment]) -> Option<usize> {
    fragments
        .iter()
        .position(|f| p >= f.ptr && p < unsafe { f.ptr.add(f.size) })
}

#[allow(clippy::too_many_arguments)]
fn cheney_trace_list(
    obj: *mut ListCons,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    let cons = unsafe { &mut *obj };
    if cons.head_kind().is_heap() {
        stats.list_head_heap_edges += 1;
        let head = forward_heap_value(
            cons.head_value(),
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            schemas,
            copied_objects,
            stats,
        );
        cons.head = head.raw();
    } else {
        stats.list_head_scalar_slots += 1;
    }

    let tail_addr = cons.tail_addr();
    if tail_addr != 0 {
        stats.list_tail_edges += 1;
        let tail = forward_heap_value(
            AnyValue::heap_ptr(tail_addr as *mut u8, ValueKind::LIST),
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            schemas,
            copied_objects,
            stats,
        );
        cons.link = tail.raw() | cons.head_kind().tag() as u64;
    }
}

#[allow(clippy::too_many_arguments)]
fn cheney_trace_struct(
    obj: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    let schema_id = unsafe { crate::fz_value::struct_schema_id(obj as *const u8) };
    let schema = schemas.get(schema_id);
    for (field, kind_offset) in schema.fz_value_fields_with_kind_offsets() {
        let value = unsafe {
            let raw = std::ptr::read(crate::fz_value::struct_field_raw_slot(
                obj as *const u8,
                field.offset,
            ));
            let kind = std::ptr::read(crate::fz_value::struct_field_kind_slot(
                obj as *const u8,
                kind_offset,
            ));
            AnyValue::decode_parts(raw, kind).expect("struct field kind")
        };
        if value.kind().is_heap() {
            stats.struct_heap_edges += 1;
            let forwarded = forward_heap_value(
                value,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
                stats,
            );
            let raw = forwarded.raw() & !crate::fz_value::TAG_MASK;
            unsafe {
                std::ptr::write(
                    crate::fz_value::struct_field_raw_slot(obj as *const u8, field.offset),
                    raw,
                );
                std::ptr::write(
                    crate::fz_value::struct_field_kind_slot(obj as *const u8, kind_offset),
                    forwarded.kind().tag(),
                );
            }
        } else {
            stats.struct_scalar_slots += 1;
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cheney_trace_resource(
    obj: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    let resource = unsafe { crate::resource::ResourceStub::from_raw(obj) };
    let closure = resource.closure_value();
    if closure.kind().is_heap() {
        stats.resource_heap_edges += 1;
        let forwarded = forward_heap_value(
            closure,
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            schemas,
            copied_objects,
            stats,
        );
        resource.closure_value_set(forwarded);
    } else {
        stats.resource_scalar_slots += 1;
    }
}

#[allow(clippy::too_many_arguments)]
fn cheney_trace_map(
    obj: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    let count = unsafe { crate::fz_value::map_count(obj as *const u8) };
    let tags = unsafe { crate::fz_value::map_tag_ptr(obj as *const u8) };
    let keys = unsafe { crate::fz_value::map_keys_ptr(obj as *const u8, count) };
    let values = unsafe { crate::fz_value::map_values_ptr(obj as *const u8, count) };
    for i in 0..count {
        let tag = unsafe { std::ptr::read(tags.add(i)) };
        let key_kind = crate::fz_value::map_key_kind(tag);
        if key_kind.is_heap() {
            stats.map_heap_edges += 1;
            let key =
                AnyValue::heap_ptr(unsafe { std::ptr::read(keys.add(i)) } as *mut u8, key_kind);
            let forwarded = forward_heap_value(
                key,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
                stats,
            );
            unsafe { std::ptr::write(keys.add(i), forwarded.raw()) };
        } else {
            stats.map_scalar_slots += 1;
        }
        let value_kind = crate::fz_value::map_value_kind(tag);
        if value_kind.is_heap() {
            stats.map_heap_edges += 1;
            let value = AnyValue::heap_ptr(
                unsafe { std::ptr::read(values.add(i)) } as *mut u8,
                value_kind,
            );
            let forwarded = forward_heap_value(
                value,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
                stats,
            );
            unsafe { std::ptr::write(values.add(i), forwarded.raw()) };
        } else {
            stats.map_scalar_slots += 1;
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cheney_trace_closure(
    obj: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    let count = unsafe { crate::fz_value::closure_captured_count(obj as *const u8) };
    for i in 0..count {
        if unsafe { crate::fz_value::closure_capture_kind_tag(obj as *const u8, i) }
            == crate::fz_value::TAG_CAPTURE_REF
        {
            let raw = unsafe { crate::fz_value::closure_capture_ref_word(obj as *const u8, i) };
            let mut value = TaggedValueRef::from_raw_word(raw).expect("closure capture ref word");
            forward_tagged_ref_root(
                &mut value,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
                stats,
            );
            unsafe {
                crate::fz_value::closure_capture_set_ref_word(obj as *const u8, i, value.raw_word())
            };
            continue;
        }
        let value = unsafe { crate::fz_value::closure_capture_value(obj as *const u8, i) };
        if value.kind().is_heap() {
            stats.closure_heap_edges += 1;
            let forwarded = forward_heap_value(
                value,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
                stats,
            );
            unsafe { crate::fz_value::closure_capture_set(obj as *const u8, i, forwarded) };
        } else {
            stats.closure_scalar_slots += 1;
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn forward_heap_value(
    value: AnyValue,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> AnyValue {
    let kind = value.kind();
    let Some(p) = value.heap_addr() else {
        return value;
    };
    if !is_active_from_space_object(p, from_ranges, fragments) {
        return value;
    }
    let new = cheney_forward_object(
        kind,
        value.heap_object_word().expect("heap object word"),
        p,
        fragments,
        frag_queue,
        free,
        to_end,
        schemas,
        copied_objects,
        stats,
    );
    AnyValue::heap_ptr(new, kind)
}

fn is_active_from_space_object(
    p: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &[Fragment],
) -> bool {
    !p.is_null() && (ptr_in_from_space(p, from_ranges) || classify_fragment(p, fragments).is_some())
}

fn ptr_in_from_space(p: *mut u8, from_ranges: &[(*mut u8, *mut u8)]) -> bool {
    from_ranges
        .iter()
        .any(|&(start, end)| p >= start && p < end)
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

/// fz-ul4.19.3: Deep-copy `src` from `src_heap` into `dst_heap`.
/// Shares of the same source object are preserved in the destination via a
/// forwarding map (caller-supplied so multiple copies during a single send can
/// share state for nested message construction).
///
/// Strict heap-kind coverage:
///   - List, Map, Struct, Closure, Bitstring, ProcBin, Resource: supported.
///   - VecI64 / VecF64 / VecU8 / VecBit: supported (raw payload copy).
///
/// Scalar leaves (Int, Atom, Special) pass through unchanged.
pub fn deep_copy_fz_value(
    src: AnyValue,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    let Some(sp) = src.heap_addr() else {
        return src;
    };
    if sp.is_null() || !src_heap.contains_heap_addr(sp) {
        return src;
    }

    match src.kind() {
        ValueKind::MAP => {
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::MAP);
            }
            let count = unsafe { crate::fz_value::map_count(sp as *const u8) };
            forwarding.insert(sp, std::ptr::null_mut());
            let mut copied_entries: Vec<(AnyValue, AnyValue)> = Vec::with_capacity(count);
            for i in 0..count {
                let (key, value) = unsafe { crate::fz_value::map_entry(sp as *const u8, i) };
                let new_key = if key.kind().is_heap() {
                    deep_copy_fz_value(key, src_heap, dst_heap, forwarding)
                } else {
                    key
                };
                let new_value = if value.kind().is_heap() {
                    deep_copy_fz_value(value, src_heap, dst_heap, forwarding)
                } else {
                    value
                };
                copied_entries.push((new_key, new_value));
            }
            let new_bits = dst_heap.alloc_map_slots(&copied_entries);
            let new_p = crate::fz_value::map_addr_from_tagged(new_bits).expect("new map ptr");
            forwarding.insert(sp, new_p);
            AnyValue::heap_ptr(new_p, ValueKind::MAP)
        }
        ValueKind::LIST => {
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::LIST);
            }
            let bits =
                dst_heap.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
            let dp = crate::fz_value::list_addr_from_tagged(bits).expect("new list ptr");
            forwarding.insert(sp, dp);
            let cons = unsafe { &*(sp as *const ListCons) };
            let new_head = if cons.head_kind().is_heap() {
                deep_copy_fz_value(cons.head_value(), src_heap, dst_heap, forwarding)
            } else {
                cons.head_value()
            };
            let new_tail = if cons.tail_addr() == 0 {
                AnyValue::empty_list()
            } else {
                deep_copy_fz_value(
                    AnyValue::heap_ptr(cons.tail_addr() as *mut u8, ValueKind::LIST),
                    src_heap,
                    dst_heap,
                    forwarding,
                )
            };
            unsafe {
                std::ptr::write(
                    dp as *mut ListCons,
                    ListCons::new(
                        new_head.raw(),
                        new_head.kind(),
                        if new_tail.kind() == ValueKind::LIST && new_tail.raw() == 0 {
                            crate::fz_value::EMPTY_LIST
                        } else {
                            new_tail.heap_object_word().expect("list tail")
                        },
                    ),
                );
            }
            AnyValue::heap_ptr(dp, ValueKind::LIST)
        }
        ValueKind::CLOSURE => deep_copy_strict_closure(sp, src_heap, dst_heap, forwarding),
        ValueKind::STRUCT => deep_copy_strict_struct(sp, src_heap, dst_heap, forwarding),
        ValueKind::BITSTRING => {
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::BITSTRING);
            }
            let bit_len = unsafe { crate::fz_value::bitstring_bit_len(sp as *const u8) };
            let bytes_len = (bit_len as usize).div_ceil(8);
            let bytes = unsafe {
                std::slice::from_raw_parts(
                    crate::fz_value::bitstring_bytes_ptr(sp as *const u8),
                    bytes_len,
                )
            };
            let new_p = dst_heap.alloc_bitstring(bytes, bit_len);
            forwarding.insert(sp, new_p);
            AnyValue::heap_ptr(new_p, ValueKind::BITSTRING)
        }
        ValueKind::PROCBIN => {
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::PROCBIN);
            }
            let src_pb = unsafe { ProcBin::from_raw(sp) };
            let handle = unsafe { SharedBinHandle::retain_from_raw(src_pb.shared_raw()) };
            let new_p = alloc_procbin(dst_heap, handle).as_raw();
            forwarding.insert(sp, new_p);
            AnyValue::heap_ptr(new_p, ValueKind::PROCBIN)
        }
        ValueKind::RESOURCE => {
            use crate::resource::{ResourceHandle, ResourceStub, alloc_resource};
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::RESOURCE);
            }
            let src_rs = unsafe { ResourceStub::from_raw(sp) };
            let handle = unsafe { ResourceHandle::retain_from_raw(src_rs.shared_raw()) };
            forwarding.insert(sp, std::ptr::null_mut());
            let src_closure = src_rs.closure_value();
            let dst_closure = if src_closure.kind().is_heap() {
                deep_copy_fz_value(src_closure, src_heap, dst_heap, forwarding)
            } else {
                src_closure
            };
            let new_p = alloc_resource(dst_heap, handle, dst_closure).as_raw();
            forwarding.insert(sp, new_p);
            AnyValue::heap_ptr(new_p, ValueKind::RESOURCE)
        }
        _ => src,
    }
}

fn deep_copy_strict_closure(
    sp: *mut u8,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    if let Some(&dp) = forwarding.get(&sp) {
        return AnyValue::heap_ptr(dp, ValueKind::CLOSURE);
    }
    let captured_count = unsafe { crate::fz_value::closure_captured_count(sp as *const u8) };
    let halt_kind = unsafe { crate::fz_value::closure_halt_kind(sp as *const u8) };
    let schema_id = unsafe { crate::fz_value::closure_schema_id(sp as *const u8) };
    let fn_ptr = unsafe { crate::fz_value::closure_fn_ptr(sp as *const u8) };
    let new_bits = dst_heap.alloc_closure_slots(schema_id, captured_count, halt_kind);
    let dp = crate::fz_value::closure_addr_from_tagged(new_bits).expect("new closure ptr");
    forwarding.insert(sp, dp);
    unsafe { std::ptr::write(dp.add(8) as *mut u64, fn_ptr) };
    for i in 0..captured_count {
        if unsafe { crate::fz_value::closure_capture_kind_tag(sp as *const u8, i) }
            == crate::fz_value::TAG_CAPTURE_REF
        {
            let raw = unsafe { crate::fz_value::closure_capture_ref_word(sp as *const u8, i) };
            let value = TaggedValueRef::from_raw_word(raw).expect("closure capture ref word");
            let copied = deep_copy_tagged_ref(value, src_heap, dst_heap, forwarding);
            unsafe {
                crate::fz_value::closure_capture_set_ref_word(dp as *const u8, i, copied.raw_word())
            };
            continue;
        }
        let cv = unsafe { crate::fz_value::closure_capture_value(sp as *const u8, i) };
        let copied = if cv.kind().is_heap() {
            deep_copy_fz_value(cv, src_heap, dst_heap, forwarding)
        } else {
            cv
        };
        unsafe { crate::fz_value::closure_capture_set(dp as *const u8, i, copied) };
    }
    AnyValue::heap_ptr(dp, ValueKind::CLOSURE)
}

fn deep_copy_strict_struct(
    sp: *mut u8,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    if let Some(&dp) = forwarding.get(&sp) {
        return AnyValue::heap_ptr(dp, ValueKind::STRUCT);
    }
    let schema_id = unsafe { crate::fz_value::struct_schema_id(sp as *const u8) };
    let dp = dst_heap.alloc_struct(schema_id);
    forwarding.insert(sp, dp);
    let registry = src_heap.schemas.borrow();
    let schema = registry.get(schema_id);
    for (f, _) in schema.fz_value_fields_with_kind_offsets() {
        let child = src_heap.read_field_slot(sp, f.offset);
        let copied = if child.kind().is_heap() {
            deep_copy_fz_value(child, src_heap, dst_heap, forwarding)
        } else {
            child
        };
        dst_heap.write_field_slot(dp, f.offset, copied);
    }
    for f in &schema.fields {
        match f.kind {
            FieldKind::AnyValue => {}
            FieldKind::RawF64 | FieldKind::RawI64 | FieldKind::RawBytes(_) => unsafe {
                let width = match f.kind {
                    FieldKind::RawBytes(n) => n as usize,
                    _ => 8,
                };
                std::ptr::copy_nonoverlapping(
                    sp.add(8 + f.offset as usize),
                    dp.add(8 + f.offset as usize),
                    width,
                );
            },
        }
    }
    AnyValue::heap_ptr(dp, ValueKind::STRUCT)
}

pub fn deep_copy_slot(
    src: AnyValue,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    deep_copy_fz_value(src, src_heap, dst_heap, forwarding)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_value::ValueKind;

    fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
        Rc::new(RefCell::new(SchemaRegistry::new()))
    }

    fn heap_root(bits: u64) -> AnyValue {
        AnyValue::decode_tagged_heap_bits(bits).expect("tagged heap root")
    }

    fn root_bits(value: AnyValue) -> u64 {
        crate::fz_value::value
            .heap_object_word()
            .expect("heap root bits")
    }

    fn tagged_bits(value: AnyValue) -> u64 {
        crate::fz_value::value
            .heap_object_word()
            .expect("tagged heap bits")
    }

    fn alloc_int_list_cons(heap: &mut Heap, head: i64, tail_bits: u64) -> u64 {
        heap.alloc_list_cons_slot(AnyValue::int(head), tail_bits)
    }

    #[test]
    fn tagged_ref_list_reads_scalar_head_and_heap_tail() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let tail_bits = h.alloc_list_cons_slot(AnyValue::atom(9), crate::fz_value::EMPTY_LIST_BITS);
        let tail_addr = crate::fz_value::list_addr_from_tagged(tail_bits).expect("tail addr");
        let list_bits = h.alloc_list_cons_slot(AnyValue::int(42), tail_bits);
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("list addr");
        let list_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr).expect("list ref");

        assert_eq!(h.read_list_head_ref(list_ref).unwrap().load_int(), Ok(42));
        assert_eq!(
            h.read_list_tail_ref(list_ref).unwrap().list_addr(),
            Ok(tail_addr)
        );
        assert_eq!(
            h.read_list_tail_ref(
                TaggedValueRef::from_heap_object(TaggedValueTag::List, tail_addr)
                    .expect("tail ref")
            )
            .unwrap()
            .tag(),
            TaggedValueTag::EmptyList
        );
    }

    #[test]
    fn tagged_ref_list_reads_heap_object_head() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let child_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
        let child_addr = crate::fz_value::map_addr_from_tagged(child_bits).expect("map addr");
        let list_bits = h.alloc_list_cons_slot(
            AnyValue::heap_ptr(child_addr, ValueKind::MAP),
            crate::fz_value::EMPTY_LIST_BITS,
        );
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("list addr");
        let list_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr).expect("list ref");

        assert_eq!(
            h.read_list_head_ref(list_ref).unwrap().map_addr(),
            Ok(child_addr)
        );
    }

    #[test]
    fn tagged_ref_map_lookup_reads_scalar_and_heap_values() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let child_bits =
            h.alloc_list_cons_slot(AnyValue::atom(1), crate::fz_value::EMPTY_LIST_BITS);
        let child_addr = crate::fz_value::list_addr_from_tagged(child_bits).expect("child addr");
        let map_bits = h.alloc_map_slots(&[
            (AnyValue::int(1), AnyValue::int(10)),
            (
                AnyValue::atom(2),
                AnyValue::heap_ptr(child_addr, ValueKind::LIST),
            ),
        ]);
        let map_addr = crate::fz_value::map_addr_from_tagged(map_bits).expect("map addr");
        let map_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Map, map_addr).expect("map ref");
        let int_key_slot = 1u64;
        let atom_key_slot = 2u64;
        let missing_key_slot = 3u64;

        let scalar = h
            .read_map_value_ref(
                map_ref,
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &int_key_slot)
                    .expect("int key"),
            )
            .unwrap()
            .expect("present int key");
        assert_eq!(scalar.load_int(), Ok(10));

        let heap_value = h
            .read_map_value_ref(
                map_ref,
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, &atom_key_slot)
                    .expect("atom key"),
            )
            .unwrap()
            .expect("present atom key");
        assert_eq!(heap_value.list_addr(), Ok(child_addr));

        assert_eq!(
            h.read_map_value_ref(
                map_ref,
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, &missing_key_slot)
                    .expect("missing key"),
            )
            .unwrap(),
            None
        );
    }

    #[test]
    fn tagged_ref_struct_reads_scalar_and_heap_fields() {
        let reg = empty_registry();
        let schema_id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let child_bits =
            h.alloc_list_cons_slot(AnyValue::atom(1), crate::fz_value::EMPTY_LIST_BITS);
        let child_addr = crate::fz_value::list_addr_from_tagged(child_bits).expect("child addr");
        let obj = h.alloc_struct(schema_id);
        h.write_field_slot(obj, 0, AnyValue::float(2.5));
        h.write_field_slot(obj, 8, AnyValue::heap_ptr(child_addr, ValueKind::LIST));
        let obj_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Struct, obj).expect("struct ref");

        assert_eq!(
            h.read_struct_field_ref(obj_ref, 0).unwrap().load_float(),
            Ok(2.5)
        );
        assert_eq!(
            h.read_struct_field_ref(obj_ref, 8).unwrap().list_addr(),
            Ok(child_addr)
        );
    }

    #[test]
    fn tagged_ref_closure_capture_reads_are_ported() {
        let reg = empty_registry();
        let schema_id = reg.borrow_mut().register(Schema::tuple_of_arity(0));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let child_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
        let child_addr = crate::fz_value::map_addr_from_tagged(child_bits).expect("child addr");
        let closure_bits = h.alloc_closure(
            schema_id,
            2,
            0,
            0xfeed,
            &[
                AnyValue::atom(7),
                AnyValue::heap_ptr(child_addr, ValueKind::MAP),
            ],
        );
        let closure_addr =
            crate::fz_value::closure_addr_from_tagged(closure_bits).expect("closure addr");
        let closure_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Closure, closure_addr)
            .expect("closure ref");

        assert_eq!(
            h.read_closure_capture_ref(closure_ref, 0)
                .unwrap()
                .load_atom(),
            Ok(7)
        );
        assert_eq!(
            h.read_closure_capture_ref(closure_ref, 1)
                .unwrap()
                .map_addr(),
            Ok(child_addr)
        );
    }

    #[test]
    fn typed_list_construction_writes_scalar_head_and_heap_tail() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let tail_bits = h.alloc_list_cons_slot(AnyValue::atom(1), crate::fz_value::EMPTY_LIST_BITS);
        let tail_addr = crate::fz_value::list_addr_from_tagged(tail_bits).expect("tail addr");
        let tail_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, tail_addr).expect("tail ref");

        let list_ref = h.alloc_list_cons_int(42, tail_ref).expect("list ref");

        assert_eq!(h.read_list_head_ref(list_ref).unwrap().load_int(), Ok(42));
        assert_eq!(
            h.read_list_tail_ref(list_ref).unwrap().list_addr(),
            Ok(tail_addr)
        );
    }

    #[test]
    #[should_panic(
        expected = "alloc_list_cons_ref head requires a heap/sentinel ref; use the typed scalar write path"
    )]
    fn list_ref_construction_rejects_scalar_head() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let head_slot = 42u64;
        let head_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &head_slot).expect("head ref");

        let _ = h.alloc_list_cons_ref(head_ref, TaggedValueRef::empty_list());
    }

    #[test]
    fn tagged_ref_list_construction_rejects_non_list_tail() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let head_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
        let head_addr = crate::fz_value::map_addr_from_tagged(head_bits).expect("head addr");
        let tail_slot = 2u64;
        let head_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Map, head_addr).expect("head ref");
        let tail_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &tail_slot).expect("tail ref");

        assert_eq!(
            h.alloc_list_cons_ref(head_ref, tail_ref),
            Err(TaggedValueRefError::ExpectedTag {
                expected: TaggedValueTag::List,
                found: TaggedValueTag::Int
            })
        );
    }

    #[test]
    fn tagged_ref_map_construction_and_put_write_scalar_and_heap_values() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let child_bits =
            h.alloc_list_cons_slot(AnyValue::atom(1), crate::fz_value::EMPTY_LIST_BITS);
        let child_addr = crate::fz_value::list_addr_from_tagged(child_bits).expect("child addr");
        let child_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, child_addr).expect("child ref");
        let int_key_slot = 1u64;
        let atom_key_slot = 2u64;
        let int_any_value = 10u64;
        let int_key =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &int_key_slot).expect("int key");
        let atom_key = TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, &atom_key_slot)
            .expect("atom key");

        let map_ref = h
            .alloc_map_refs(&[(
                int_key,
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &int_any_value)
                    .expect("int value"),
            )])
            .expect("map ref");
        assert_eq!(
            h.read_map_value_ref(map_ref, int_key)
                .unwrap()
                .expect("int key")
                .load_int(),
            Ok(10)
        );
        assert_eq!(
            h.read_map_value_ref(map_ref, AnyValue::int(1))
                .unwrap()
                .expect("int key by slot")
                .load_int(),
            Ok(10)
        );

        let map_ref = h
            .map_put_ref(map_ref, atom_key, child_ref)
            .expect("put child");
        assert_eq!(
            h.read_map_value_ref(map_ref, atom_key)
                .unwrap()
                .expect("atom key")
                .list_addr(),
            Ok(child_addr)
        );
        assert_eq!(
            h.read_map_value_ref(map_ref, AnyValue::atom(2))
                .unwrap()
                .expect("atom key by slot")
                .list_addr(),
            Ok(child_addr)
        );

        let map_ref = h
            .map_put_int(map_ref, int_key, 11)
            .expect("replace int key");
        assert_eq!(
            h.read_map_value_ref(map_ref, int_key)
                .unwrap()
                .expect("int key")
                .load_int(),
            Ok(11)
        );
    }

    #[test]
    #[should_panic(
        expected = "map_put_ref value requires a heap/sentinel ref; use the typed scalar write path"
    )]
    fn map_put_ref_rejects_scalar_value() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let key_slot = 1u64;
        let any_value = 2u64;
        let key_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &key_slot).expect("key ref");
        let value_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &any_value).expect("value ref");
        let map_bits = h.alloc_map_slots(&[]);
        let map_addr = crate::fz_value::map_addr_from_tagged(map_bits).expect("map addr");
        let map_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Map, map_addr).expect("map ref");

        let _ = h.map_put_ref(map_ref, key_ref, value_ref);
    }

    #[test]
    fn tagged_ref_struct_and_closure_writes_store_scalar_and_heap_values() {
        let reg = empty_registry();
        let struct_schema = reg.borrow_mut().register(Schema::tuple_of_arity(2));
        let closure_schema = reg.borrow_mut().register(Schema::tuple_of_arity(0));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let child_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
        let child_addr = crate::fz_value::map_addr_from_tagged(child_bits).expect("child addr");
        let child_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Map, child_addr).expect("child ref");
        let scalar_slot = 99u64;
        let scalar_ref = TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, &scalar_slot)
            .expect("scalar ref");

        let struct_addr = h.alloc_struct(struct_schema);
        let struct_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Struct, struct_addr)
            .expect("struct ref");
        h.write_struct_field_ref(struct_ref, 0, scalar_ref)
            .expect("write scalar field");
        h.write_struct_field_ref(struct_ref, 8, child_ref)
            .expect("write heap field");
        assert_eq!(
            h.read_struct_field_ref(struct_ref, 0).unwrap().load_atom(),
            Ok(99)
        );
        assert_eq!(
            h.read_struct_field_ref(struct_ref, 8).unwrap().map_addr(),
            Ok(child_addr)
        );

        let closure_bits = h.alloc_closure_slots(closure_schema, 2, 0);
        let closure_addr =
            crate::fz_value::closure_addr_from_tagged(closure_bits).expect("closure addr");
        let closure_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Closure, closure_addr)
            .expect("closure ref");
        h.write_closure_capture_ref(closure_ref, 0, scalar_ref)
            .expect("write scalar capture");
        h.write_closure_capture_ref(closure_ref, 1, child_ref)
            .expect("write heap capture");
        assert_eq!(
            h.read_closure_capture_ref(closure_ref, 0)
                .unwrap()
                .load_atom(),
            Ok(99)
        );
        assert_eq!(
            h.read_closure_capture_ref(closure_ref, 1)
                .unwrap()
                .map_addr(),
            Ok(child_addr)
        );
    }

    #[test]
    fn tagged_ref_heap_writes_are_traced_by_gc() {
        let reg = empty_registry();
        let struct_schema = reg.borrow_mut().register(Schema::tuple_of_arity(1));
        let closure_schema = reg.borrow_mut().register(Schema::tuple_of_arity(0));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let key_slot = 1u64;
        let key_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &key_slot).expect("key ref");

        let child_map_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
        let child_map_addr =
            crate::fz_value::map_addr_from_tagged(child_map_bits).expect("child map addr");
        let child_map_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Map, child_map_addr)
            .expect("child map ref");
        let list_ref = h
            .alloc_list_cons_ref(child_map_ref, TaggedValueRef::empty_list())
            .expect("list ref");

        let child_list_bits =
            h.alloc_list_cons_slot(AnyValue::atom(3), crate::fz_value::EMPTY_LIST_BITS);
        let child_list_addr =
            crate::fz_value::list_addr_from_tagged(child_list_bits).expect("child list addr");
        let child_list_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, child_list_addr)
                .expect("child list ref");
        let map_ref = h
            .alloc_map_refs(&[(key_ref, child_list_ref)])
            .expect("map ref");

        let struct_addr = h.alloc_struct(struct_schema);
        let struct_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Struct, struct_addr)
            .expect("struct ref");
        h.write_struct_field_ref(struct_ref, 0, child_list_ref)
            .expect("write struct field");

        let closure_bits = h.alloc_closure_slots(closure_schema, 1, 0);
        let closure_addr =
            crate::fz_value::closure_addr_from_tagged(closure_bits).expect("closure addr");
        let closure_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Closure, closure_addr)
            .expect("closure ref");
        h.write_closure_capture_ref(closure_ref, 0, child_map_ref)
            .expect("write closure capture");

        let mut root = std::ptr::null_mut();
        let mut roots = [
            AnyValue::heap_ptr(list_ref.list_addr().unwrap(), ValueKind::LIST),
            AnyValue::heap_ptr(map_ref.map_addr().unwrap(), ValueKind::MAP),
            AnyValue::heap_ptr(struct_ref.struct_addr().unwrap(), ValueKind::STRUCT),
            AnyValue::heap_ptr(closure_ref.closure_addr().unwrap(), ValueKind::CLOSURE),
        ];

        h.gc_with_extra_root_slots(&mut root, &mut roots);

        let moved_list_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, roots[0].raw() as *const u8)
                .expect("moved list ref");
        let moved_list_head = h.read_list_head_ref(moved_list_ref).unwrap().map_addr();

        let moved_map_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Map, roots[1].raw() as *const u8)
                .expect("moved map ref");
        let moved_map_value = h
            .read_map_value_ref(moved_map_ref, key_ref)
            .unwrap()
            .expect("map value")
            .list_addr();

        let moved_struct_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Struct, roots[2].raw() as *const u8)
                .expect("moved struct ref");
        let moved_struct_field = h
            .read_struct_field_ref(moved_struct_ref, 0)
            .unwrap()
            .list_addr();

        let moved_closure_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Closure, roots[3].raw() as *const u8)
                .expect("moved closure ref");
        let moved_closure_capture = h
            .read_closure_capture_ref(moved_closure_ref, 0)
            .unwrap()
            .map_addr();

        assert_eq!(moved_list_head, moved_closure_capture);
        assert_eq!(moved_map_value, moved_struct_field);
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
                    kind: FieldKind::AnyValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::AnyValue,
                },
            ],
        });
        assert_eq!(id_a, 0);
        assert_eq!(id_b, 1);
        assert_eq!(reg.get(id_a).name, "A");
        assert_eq!(reg.get(id_b).name, "Pair");
    }

    /// fz-wu9 / fz-3ld.9 — every strict inline Bitstring allocation reserves
    /// at least one zero byte past its payload at offset
    /// `bytes_ptr + ceil(bit_len/8)`. Mirrors the SharedBin invariant covered
    /// by procbin.rs::shared_bin_alloc_has_trailing_nul.
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
                assert_eq!(crate::fz_value::bitstring_bit_len(p), bit_len);
                assert_eq!(
                    crate::fz_value::bitstring_size_for_bit_len(bit_len),
                    crate::fz_value::object_size(crate::fz_value::heap_object_word(
                        p,
                        crate::fz_value::ValueKind::BITSTRING
                    ))
                );
                let payload = crate::fz_value::bitstring_bytes_ptr(p);
                for (i, expected) in bytes.iter().enumerate().take(n) {
                    assert_eq!(
                        *payload.add(i),
                        *expected,
                        "payload byte {} at len {}",
                        i,
                        n
                    );
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
        let p = h.alloc_list_cons_slot(AnyValue::int(1), crate::fz_value::EMPTY_LIST);
        assert!(crate::fz_value::list_addr_from_tagged(p).is_some());
        assert_eq!(h.live_count(), 1);
        assert_eq!(h.bytes_used(), 16);
    }

    #[test]
    fn heap_pointers_are_16_aligned() {
        let mut h = Heap::new(1024, empty_registry());
        for _ in 0..10 {
            let p = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
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
            let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
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
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        assert!(!h.should_gc(), "1 cell at 16 bytes under 64");
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        assert!(!h.should_gc(), "2 cells at 32 bytes under 64");
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        assert!(h.should_gc(), "4 cells at 64 bytes at threshold");
        h.clear_should_gc_flag();
        assert!(!h.should_gc());
    }

    /// With a null root, Cheney recycles the arena: from-space is freed,
    /// to-space is a fresh empty block, live_count goes to zero.
    #[test]
    fn gc_with_null_root_recycles_arena() {
        let mut h = Heap::new(1024, empty_registry());
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
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
        let n3 = alloc_int_list_cons(&mut h, 3, crate::fz_value::EMPTY_LIST);
        let n2 = alloc_int_list_cons(&mut h, 2, n3);
        let n1 = alloc_int_list_cons(&mut h, 1, n2);
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(n1)];
        let old_n1 = n1 as usize;
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        let root_ptr = crate::fz_value::list_addr_from_tagged(root_bits(roots[0])).unwrap();
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

    #[test]
    fn any_value_roots_forward_only_heap_values() {
        let mut h = Heap::new(1024, empty_registry());
        let list_bits = alloc_int_list_cons(&mut h, 1, crate::fz_value::EMPTY_LIST);
        let old_list = crate::fz_value::list_addr_from_tagged(list_bits).unwrap();
        let mut roots = [
            AnyValue::int(i64::MAX),
            AnyValue::float(1.5),
            AnyValue::decode_tagged_heap_bits(list_bits).unwrap(),
        ];
        let mut mailbox = std::collections::VecDeque::new();

        h.gc_any_value_roots_with_process_roots(&mut roots, &mut mailbox);

        assert_eq!(roots[0], AnyValue::int(i64::MAX));
        assert_eq!(roots[1], AnyValue::float(1.5));
        let new_list = roots[2].raw() as *mut u8;
        assert_ne!(new_list, old_list);
        let head = unsafe { (*(new_list as *const crate::fz_value::ListCons)).head_value() };
        assert_eq!(head.kind, ValueKind::INT);
        assert_eq!(head.raw as i64, 1);
    }

    #[test]
    fn tagged_ref_root_gc_forwards_heap_ref() {
        let mut h = Heap::new(1024, empty_registry());
        let list_bits = alloc_int_list_cons(&mut h, 1, crate::fz_value::EMPTY_LIST);
        let old_list = crate::fz_value::list_addr_from_tagged(list_bits).unwrap();
        let mut roots =
            [TaggedValueRef::from_heap_object(TaggedValueTag::List, old_list).expect("list ref")];
        let mut root = std::ptr::null_mut();

        let stats = h.gc_with_tagged_ref_roots(&mut root, &mut roots);

        let new_list = roots[0].list_addr().expect("forwarded list ref");
        assert_ne!(new_list, old_list);
        let head = unsafe { (*(new_list as *const crate::fz_value::ListCons)).head_value() };
        assert_eq!(head, AnyValue::int(1));
        assert_eq!(stats.root_heap_edges, 1);
        assert_eq!(stats.root_scalar_slots, 0);
    }

    #[test]
    fn tagged_ref_root_gc_copies_scalar_box_without_tracing_payload() {
        let mut h = Heap::new(1024, empty_registry());
        let decoy_bits = alloc_int_list_cons(&mut h, 99, crate::fz_value::EMPTY_LIST);
        let decoy_addr = crate::fz_value::list_addr_from_tagged(decoy_bits).unwrap();
        let scalar = h.alloc(8);
        unsafe {
            std::ptr::write(scalar as *mut u64, decoy_addr as u64);
        }
        let mut roots =
            [
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, scalar as *const u64)
                    .expect("scalar root ref"),
            ];
        let mut root = std::ptr::null_mut();

        let stats = h.gc_with_tagged_ref_roots(&mut root, &mut roots);

        assert_ne!(value_ref_addr(roots[0]), scalar);
        assert_eq!(roots[0].load_int().unwrap(), decoy_addr as i64);
        assert_eq!(stats.root_scalar_slots, 1);
        assert_eq!(stats.root_heap_edges, 0);
        assert_eq!(stats.copied_objects, 1);
        assert_eq!(stats.copied_bytes, 16);
    }

    #[test]
    fn tagged_ref_root_gc_preserves_static_scalar_ref() {
        static STATIC_INT: u64 = 42;
        let mut h = Heap::new(1024, empty_registry());
        let original = TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &STATIC_INT)
            .expect("static scalar ref");
        let mut roots = [original];
        let mut root = std::ptr::null_mut();

        let stats = h.gc_with_tagged_ref_roots(&mut root, &mut roots);

        assert_eq!(roots[0], original);
        assert_eq!(roots[0].load_int().unwrap(), 42);
        assert_eq!(stats.root_scalar_slots, 1);
        assert_eq!(stats.copied_objects, 0);
    }

    #[test]
    fn gc_stats_prove_scalar_list_head_is_copied_but_not_traced() {
        let mut h = Heap::new(1024, empty_registry());
        let decoy_bits = alloc_int_list_cons(&mut h, 99, crate::fz_value::EMPTY_LIST);
        let decoy_addr = crate::fz_value::list_addr_from_tagged(decoy_bits).unwrap();
        let live_bits = h.alloc_list_cons_slot(
            AnyValue::new(decoy_addr as u64, ValueKind::INT),
            crate::fz_value::EMPTY_LIST,
        );
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(live_bits)];

        let stats = h.gc_with_extra_root_slots(&mut root, &mut roots);

        assert_eq!(stats.copied_objects, 1);
        assert_eq!(stats.copied_bytes, 16);
        assert_eq!(stats.live_objects, 1);
        assert_eq!(stats.list_head_scalar_slots, 1);
        assert_eq!(stats.list_head_heap_edges, 0);
        assert_eq!(h.last_gc_stats, stats);
        let moved =
            crate::fz_value::list_addr_from_tagged(root_bits(roots[0])).expect("moved live list");
        let moved_head = unsafe { (*(moved as *const ListCons)).head_value() };
        assert_eq!(moved_head.kind(), ValueKind::INT);
        assert_eq!(moved_head.raw(), decoy_addr as u64);
    }

    #[test]
    fn gc_stats_count_struct_slots_by_layout_kind() {
        let reg = empty_registry();
        let schema_id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
        let mut h = Heap::new(1024, reg);
        let decoy_bits = alloc_int_list_cons(&mut h, 1, crate::fz_value::EMPTY_LIST);
        let decoy_addr = crate::fz_value::list_addr_from_tagged(decoy_bits).unwrap();
        let child_bits = alloc_int_list_cons(&mut h, 2, crate::fz_value::EMPTY_LIST);
        let child_addr = crate::fz_value::list_addr_from_tagged(child_bits).unwrap();
        let tuple = h.alloc_struct(schema_id);
        h.write_field_slot(tuple, 0, AnyValue::new(decoy_addr as u64, ValueKind::INT));
        h.write_field_slot(tuple, 8, AnyValue::heap_ptr(child_addr, ValueKind::LIST));
        let mut root =
            crate::fz_value::heap_object_word(tuple, crate::fz_value::ValueKind::STRUCT) as *mut u8;

        let stats = h.gc(&mut root);

        assert_eq!(stats.copied_objects, 2);
        assert_eq!(stats.struct_scalar_slots, 1);
        assert_eq!(stats.struct_heap_edges, 1);
        assert_eq!(stats.list_head_scalar_slots, 1);
        assert_eq!(h.live_count(), 2);
        let moved = crate::fz_value::struct_addr_from_tagged(root as u64).expect("moved struct");
        assert_eq!(h.read_field_slot(moved, 0).raw(), decoy_addr as u64);
        assert_ne!(h.read_field_slot(moved, 8).raw() as *mut u8, child_addr);
    }

    #[test]
    fn gc_stats_count_map_and_closure_slots_by_layout_kind() {
        let mut h = Heap::new(1024, empty_registry());
        let map_child_bits = alloc_int_list_cons(&mut h, 3, crate::fz_value::EMPTY_LIST);
        let map_child_addr = crate::fz_value::list_addr_from_tagged(map_child_bits).unwrap();
        let closure_child_bits = alloc_int_list_cons(&mut h, 4, crate::fz_value::EMPTY_LIST);
        let closure_child_addr =
            crate::fz_value::list_addr_from_tagged(closure_child_bits).unwrap();
        let map_bits = h.alloc_map_slots(&[(
            AnyValue::atom(7),
            AnyValue::heap_ptr(map_child_addr, ValueKind::LIST),
        )]);
        let closure_bits = h.alloc_closure(
            0,
            2,
            0,
            0,
            &[
                AnyValue::int(5),
                AnyValue::heap_ptr(closure_child_addr, ValueKind::LIST),
            ],
        );
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(map_bits), heap_root(closure_bits)];

        let stats = h.gc_with_extra_root_slots(&mut root, &mut roots);

        assert_eq!(stats.copied_objects, 4);
        assert_eq!(stats.root_heap_edges, 2);
        assert_eq!(stats.map_scalar_slots, 1);
        assert_eq!(stats.map_heap_edges, 1);
        assert_eq!(stats.closure_scalar_slots, 1);
        assert_eq!(stats.closure_heap_edges, 1);
        assert_eq!(stats.list_head_scalar_slots, 2);
        let moved_map = crate::fz_value::map_addr_from_tagged(root_bits(roots[0])).unwrap();
        let moved_closure = crate::fz_value::closure_addr_from_tagged(root_bits(roots[1])).unwrap();
        let (_, moved_map_value) = unsafe { crate::fz_value::map_entry(moved_map, 0) };
        let moved_capture = unsafe { crate::fz_value::closure_capture_value(moved_closure, 1) };
        assert_ne!(moved_map_value.raw() as *mut u8, map_child_addr);
        assert_ne!(moved_capture.raw() as *mut u8, closure_child_addr);
    }

    #[test]
    fn process_root_gc_forwards_runnable_closure_and_process_roots() {
        let mut h = Heap::new(1024, empty_registry());
        let captured_bits = alloc_int_list_cons(&mut h, 10, crate::fz_value::EMPTY_LIST);
        let mailbox_bits = alloc_int_list_cons(&mut h, 20, crate::fz_value::EMPTY_LIST);
        let closure_bits = h.alloc_closure_slots(0, 1, 0);
        let old_closure = crate::fz_value::closure_addr_from_tagged(closure_bits).unwrap();
        let old_capture = crate::fz_value::list_addr_from_tagged(captured_bits).unwrap();
        let old_mailbox = crate::fz_value::list_addr_from_tagged(mailbox_bits).unwrap();
        let closure_addr = crate::fz_value::closure_addr_from_tagged(closure_bits).unwrap();
        unsafe {
            crate::fz_value::closure_capture_set(
                closure_addr,
                0,
                AnyValue::decode_tagged_heap_bits(captured_bits).unwrap(),
            );
        }
        let mut root = closure_bits as *mut u8;
        let mut mailbox = std::collections::VecDeque::from([TaggedValueRef::from_heap_object(
            TaggedValueTag::List,
            crate::fz_value::list_addr_from_tagged(mailbox_bits).unwrap(),
        )
        .expect("mailbox list ref")]);
        h.gc_process_roots(&mut root, &mut mailbox);

        let new_closure = crate::fz_value::closure_addr_from_tagged(root as u64).unwrap();
        assert_ne!(new_closure, old_closure);
        let new_capture = unsafe { crate::fz_value::closure_capture_value(new_closure, 0) };
        assert_ne!(new_capture.raw() as *mut u8, old_capture);
        assert_ne!(mailbox[0].list_addr().unwrap(), old_mailbox);
    }

    /// Cheney drops unreachable objects: a cell allocated alongside the
    /// root chain but not pointed to by it is discarded. live_count
    /// shrinks to the chain length.
    #[test]
    fn gc_drops_unreachable_objects() {
        let mut h = Heap::new(1024, empty_registry());
        let _orphan = alloc_int_list_cons(&mut h, 99, crate::fz_value::EMPTY_LIST);
        let kept = alloc_int_list_cons(&mut h, 7, crate::fz_value::EMPTY_LIST);
        assert_eq!(h.live_count(), 2);
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(kept)];
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        assert_eq!(h.live_count(), 1, "orphan dropped, kept survives");
        let new_cons =
            crate::fz_value::list_addr_from_tagged(root_bits(roots[0])).unwrap() as *mut ListCons;
        let head = unsafe { (*new_cons).head };
        assert_eq!(head as i64, 7);
    }

    #[test]
    fn list_head_can_be_a_tagged_list_without_int_collision() {
        let mut h = Heap::new(1024, empty_registry());
        let child_bits = alloc_int_list_cons(&mut h, 7, crate::fz_value::EMPTY_LIST);
        let parent_bits =
            h.alloc_list_cons_slot(heap_root(child_bits), crate::fz_value::EMPTY_LIST);
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
        let child_bits = alloc_int_list_cons(&mut src, 7, crate::fz_value::EMPTY_LIST);
        let parent_bits =
            src.alloc_list_cons_slot(heap_root(child_bits), crate::fz_value::EMPTY_LIST);
        let mut forwarding = std::collections::HashMap::new();

        let copied = deep_copy_slot(heap_root(parent_bits), &src, &mut dst, &mut forwarding);
        let copied_parent = crate::fz_value::list_addr_from_tagged(tagged_bits(copied))
            .expect("copied parent list ptr");
        let parent = unsafe { &*(copied_parent as *const ListCons) };
        assert_eq!(parent.head_kind(), ValueKind::LIST);

        let copied_child = parent.head as *mut u8;
        assert_ne!(
            copied_child,
            crate::fz_value::list_addr_from_tagged(child_bits).unwrap()
        );
        let child = unsafe { &*(copied_child as *const ListCons) };
        assert_eq!(child.head_kind(), ValueKind::INT);
        assert_eq!(child.head as i64, 7);
        assert_eq!(child.tail_bits(), crate::fz_value::EMPTY_LIST);
    }

    #[test]
    #[serial_test::serial]
    fn deep_copy_strict_heap_kinds_dispatch_from_pointer_tags() {
        use crate::resource::{ResourceHandle, ResourceStub, alloc_resource};

        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
        let mut src = Heap::new(SIZE_TABLE[0], reg.clone());
        let mut dst = Heap::new(SIZE_TABLE[0], reg);

        let list_bits = alloc_int_list_cons(&mut src, 7, crate::fz_value::EMPTY_LIST);

        let struct_p = src.alloc_struct(pair_id);
        src.write_field_slot(struct_p, 0, heap_root(list_bits));
        src.write_field_slot(struct_p, 8, AnyValue::int(11));

        let closure_bits = src.alloc_closure(pair_id, 1, 0, 0x1234, &[heap_root(list_bits)]);

        let bitstring_p = src.alloc_bitstring(b"abc", 24);

        let procbin = alloc_procbin(&mut src, SharedBinHandle::from_bytes(&[1, 2, 3, 4], 32));

        let resource_closure = heap_root(closure_bits);
        let resource = alloc_resource(
            &mut src,
            ResourceHandle::new(
                0xfeed,
                crate::fz_value::ValueKind::INT.tag(),
                crate::resource::fz_resource_destructor_noop,
            ),
            resource_closure,
        );

        let entries = [
            (
                AnyValue::new(1, ValueKind::ATOM),
                AnyValue::heap_ptr(
                    crate::fz_value::list_addr_from_tagged(list_bits).unwrap(),
                    ValueKind::LIST,
                ),
            ),
            (
                AnyValue::new(2, ValueKind::ATOM),
                AnyValue::heap_ptr(struct_p, ValueKind::STRUCT),
            ),
            (
                AnyValue::new(3, ValueKind::ATOM),
                AnyValue::heap_ptr(
                    crate::fz_value::closure_addr_from_tagged(closure_bits).unwrap(),
                    ValueKind::CLOSURE,
                ),
            ),
            (
                AnyValue::new(4, ValueKind::ATOM),
                AnyValue::heap_ptr(bitstring_p, ValueKind::BITSTRING),
            ),
            (
                AnyValue::new(5, ValueKind::ATOM),
                AnyValue::heap_ptr(procbin.as_raw(), ValueKind::PROCBIN),
            ),
            (
                AnyValue::new(7, ValueKind::ATOM),
                AnyValue::heap_ptr(resource.as_raw(), ValueKind::RESOURCE),
            ),
        ];
        let map_bits = src.alloc_map_slots(&entries);
        let mut forwarding = std::collections::HashMap::new();

        let copied = deep_copy_slot(heap_root(map_bits), &src, &mut dst, &mut forwarding);
        let copied_map = crate::fz_value::map_addr_from_tagged(tagged_bits(copied)).unwrap();

        let copied_values = (0..entries.len())
            .map(|i| unsafe { crate::fz_value::map_entry(copied_map as *const u8, i).1 })
            .collect::<Vec<_>>();
        for (i, value) in copied_values.iter().enumerate() {
            assert_eq!(value.kind, entries[i].1.kind);
            assert_ne!(
                value.raw & !crate::fz_value::TAG_MASK,
                entries[i].1.raw & !crate::fz_value::TAG_MASK,
                "heap entry {} moved/copied",
                i
            );
        }

        let copied_struct = copied_values[1].raw as *mut u8;
        let copied_struct_list = dst.read_field_slot(copied_struct, 0);
        assert_eq!(copied_struct_list.kind(), ValueKind::LIST);
        assert!(!copied_struct_list.heap_addr().unwrap().is_null());

        let copied_closure = copied_values[2].raw as *mut u8;
        let copied_capture =
            unsafe { crate::fz_value::closure_capture_value(copied_closure as *const u8, 0) };
        assert!(crate::fz_value::list_addr_from_tagged(tagged_bits(copied_capture)).is_some());

        let copied_resource = unsafe { ResourceStub::from_raw(copied_values[5].raw as *mut u8) };
        assert_eq!(copied_resource.payload(), 0xfeed);
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
            let mut tail = crate::fz_value::EMPTY_LIST;
            for i in 0..len {
                tail = alloc_int_list_cons(&mut h, i as i64, tail);
            }
            let mut root = std::ptr::null_mut();
            let mut roots = [heap_root(tail)];
            h.gc_with_extra_root_slots(&mut root, &mut roots);
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
        let n3 = alloc_int_list_cons(&mut h, 3, crate::fz_value::EMPTY_LIST);
        let n2 = alloc_int_list_cons(&mut h, 2, n3);
        let n1 = alloc_int_list_cons(&mut h, 1, n2);
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(n1)];
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        assert_eq!(h.last_gc_live_bytes, 3 * 16, "three cons cells = 48 bytes");

        // Second GC with same live set: to-space sizing = 48 * 2 = 96,
        // clamped to SIZE_TABLE[0]. live bytes stay the same.
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        assert_eq!(h.last_gc_live_bytes, 3 * 16, "live bytes unchanged");
        assert_eq!(h.size_class, 0, "tiny live set stays at smallest class");
    }

    /// Watermark is set to 75% of block. After alloc crossing watermark,
    /// FZ_SHOULD_YIELD is set; it can be cleared externally.
    #[test]
    fn watermark_is_75_percent_of_block() {
        crate::yield_flag::clear();
        let h = Heap::new(SIZE_TABLE[0], empty_registry());
        let expected = unsafe { h.block_start.add(SIZE_TABLE[0] * 3 / 4) };
        assert_eq!(h.gc_watermark, expected);
        crate::yield_flag::clear(); // cleanup
    }

    /// Large struct (200-byte payload, well past the old 64-byte cap)
    /// allocates without panic; grow promotes to a larger size_class as needed.
    #[test]
    fn alloc_large_struct_succeeds_and_grows_size_class() {
        let reg = empty_registry();
        // Build a schema whose payload is 200 bytes of typed value fields.
        let n_fields = 200 / 8; // 25 any values
        let mut fields = Vec::with_capacity(n_fields);
        for i in 0..n_fields {
            fields.push(FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::AnyValue,
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
            assert_eq!(crate::fz_value::struct_schema_id(p), id);
            // total = 8 + 200 = 208, rounded to 208.
            assert_eq!(crate::fz_value::struct_size_for_payload(200), 208);
        }
    }

    #[test]
    fn struct_layout_size_correct() {
        let reg = empty_registry();
        let id = reg.borrow_mut().register(Schema::tuple_of_arity(3));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let before = h.bytes_used();

        let p = h.alloc_struct(id);

        assert_eq!(Schema::tuple_of_arity(3).allocation_payload_size(), 32);
        assert_eq!(h.bytes_used() - before, 48);
        unsafe {
            assert_eq!(crate::fz_value::struct_schema_id(p), id);
            assert_eq!(crate::fz_value::struct_flags(p), 0);
        }
    }

    #[test]
    fn struct_field_read_at_new_offset() {
        let reg = empty_registry();
        let id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let p = h.alloc_struct(id);

        h.write_field_slot(p, 0, AnyValue::int(11));
        h.write_field_slot(p, 8, AnyValue::int(22));

        unsafe {
            assert_eq!(std::ptr::read(p.add(8) as *const u64), 11);
            assert_eq!(std::ptr::read(p.add(16) as *const u64), 22);
            assert_eq!(std::ptr::read(p.add(24) as *const u8), ValueKind::INT.tag());
            assert_eq!(std::ptr::read(p.add(25) as *const u8), ValueKind::INT.tag());
        }
        assert_eq!(h.read_field_slot(p, 0), AnyValue::int(11));
        assert_eq!(h.read_field_slot(p, 8), AnyValue::int(22));
    }

    #[test]
    fn struct_forwarding_marker_through_gc() {
        let reg = empty_registry();
        let id = reg.borrow_mut().register(Schema::tuple_of_arity(1));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let p = h.alloc_struct(id);
        let old_addr = p;
        h.write_field_slot(p, 0, AnyValue::int(9));
        let mut root =
            crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::STRUCT) as *mut u8;

        h.gc(&mut root);

        let new_p = crate::fz_value::struct_addr_from_tagged(root as u64).expect("forwarded root");
        assert_ne!(new_p as *const u8, old_addr);
        assert_eq!(h.read_field_slot(new_p, 0), AnyValue::int(9));
        assert_eq!(
            crate::fz_value::is_forwarded(old_addr),
            Some(new_p as *const u8)
        );
    }

    /// Map with 5 entries exercises both alloc and the Cheney trace path
    /// (Map walks each entry's typed children).
    #[test]
    fn alloc_large_map_round_trips_through_gc() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let entries: Vec<(AnyValue, AnyValue)> = (0..5)
            .map(|i| {
                (
                    AnyValue::new(i as u64, ValueKind::INT),
                    AnyValue::new((i * 10) as u64, ValueKind::INT),
                )
            })
            .collect();
        let bits = h.alloc_map_slots(&entries);
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(bits)];
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        assert_eq!(h.live_count(), 1, "map survives GC");
        let new_p = crate::fz_value::map_addr_from_tagged(root_bits(roots[0])).unwrap();
        unsafe {
            let count = crate::fz_value::map_count(new_p as *const u8);
            assert_eq!(count, 5);
        }
    }

    #[test]
    fn map_layout_size_correct() {
        for count in [0usize, 1, 2, 3, 7, 8, 9] {
            let entries: Vec<(AnyValue, AnyValue)> = (0..count)
                .map(|i| {
                    (
                        AnyValue::new(i as u64, ValueKind::INT),
                        AnyValue::new((i + 10) as u64, ValueKind::INT),
                    )
                })
                .collect();
            let mut h = Heap::new(1024, empty_registry());
            let bits = h.alloc_map_slots(&entries);
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
        assert_eq!(unsafe { crate::fz_value::closure_schema_id(p) }, 42);
        assert_eq!(unsafe { crate::fz_value::closure_halt_kind(p) }, 2);
        assert_eq!(unsafe { crate::fz_value::closure_fn_ptr(p) }, 0xfeed_beef);
    }

    #[test]
    fn closure_layout_n_captures() {
        let mut h = Heap::new(1024, empty_registry());
        let captures = [AnyValue::int(10), AnyValue::int(20)];
        let bits = h.alloc_closure(7, captures.len(), 1, 0x1234, &captures);
        assert_eq!(crate::fz_value::object_size(bits), 48);
        let p = crate::fz_value::closure_addr_from_tagged(bits).unwrap();
        assert_eq!(unsafe { crate::fz_value::closure_captured_count(p) }, 2);
        for (i, expected) in captures.iter().enumerate() {
            let got = unsafe { crate::fz_value::closure_capture_value(p, i) };
            assert_eq!(got, *expected);
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
        let confirm = unsafe { std::ptr::read(old.add(8) as *const u64) };
        assert_eq!(confirm, crate::fz_value::TAG_FWD);
    }

    #[test]
    fn strict_heap_decoder_accepts_static_closure_pointer() {
        let mut storage = crate::process::AlignedClosureStorage::zeroed();
        let bits = crate::fz_value::heap_object_word(
            storage.as_ptr() as *const u8,
            crate::fz_value::ValueKind::CLOSURE,
        );

        let value = heap_root(bits);

        assert_eq!(value.kind(), ValueKind::CLOSURE);
        assert_eq!(value.raw(), storage.as_ptr() as u64);
    }

    #[test]
    fn closure_fn_id_preserved_in_schema_id() {
        let mut h = Heap::new(1024, empty_registry());
        let bits = h.alloc_closure_slots(99, 0, 0);
        let p = crate::fz_value::closure_addr_from_tagged(bits).unwrap();
        assert_eq!(unsafe { crate::fz_value::closure_schema_id(p) }, 99);
    }

    #[test]
    fn map_packed_tags_round_trip() {
        let cases = [1usize, 2, 3, 7, 8, 9];
        for count in cases {
            let entries: Vec<(AnyValue, AnyValue)> = (0..count)
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
                        AnyValue::new(i as u64, key_kind),
                        AnyValue::new((100 + i) as u64, value_kind),
                    )
                })
                .collect();
            let mut h = Heap::new(1024, empty_registry());
            let bits = h.alloc_map_slots(&entries);
            let p = crate::fz_value::map_addr_from_tagged(bits).unwrap();
            for (i, expected) in entries.iter().enumerate() {
                let got = unsafe { crate::fz_value::map_entry(p, i) };
                assert_eq!(got, *expected);
            }
        }
    }

    #[test]
    fn map_float_value_is_unboxed_raw_bits() {
        let mut h = Heap::new(1024, empty_registry());
        let f = std::f64::consts::PI;
        let bits = h.alloc_map_slots(&[(
            AnyValue::new(0, ValueKind::ATOM),
            AnyValue::new(f.to_bits(), ValueKind::FLOAT),
        )]);
        let p = crate::fz_value::map_addr_from_tagged(bits).unwrap();
        let (_, value) = unsafe { crate::fz_value::map_entry(p, 0) };
        assert_eq!(value.kind, ValueKind::FLOAT);
        assert_eq!(value.raw, f.to_bits());
        assert_eq!(h.live_count(), 1, "map allocation should not box the float");
    }

    #[test]
    fn map_int_value_stores_full_i64_range() {
        let mut h = Heap::new(1024, empty_registry());
        let value = i64::MIN;
        let bits = h.alloc_map_slots(&[(
            AnyValue::new(1, ValueKind::ATOM),
            AnyValue::new(value as u64, ValueKind::INT),
        )]);
        let p = crate::fz_value::map_addr_from_tagged(bits).unwrap();
        let (_, got) = unsafe { crate::fz_value::map_entry(p, 0) };
        assert_eq!(got.kind, ValueKind::INT);
        assert_eq!(got.raw as i64, value);
    }

    #[test]
    fn deep_copy_tagged_map_preserves_nested_list_value() {
        let mut src = Heap::new(1024, empty_registry());
        let mut dst = Heap::new(1024, empty_registry());
        let child_bits = alloc_int_list_cons(&mut src, 7, crate::fz_value::EMPTY_LIST);
        let child_ptr = crate::fz_value::list_addr_from_tagged(child_bits).unwrap();
        let map_bits = src.alloc_map_slots(&[(
            AnyValue::new(1, ValueKind::ATOM),
            AnyValue::heap_ptr(child_ptr, ValueKind::LIST),
        )]);
        let mut forwarding = std::collections::HashMap::new();
        let copied = deep_copy_slot(heap_root(map_bits), &src, &mut dst, &mut forwarding);
        let copied_map = crate::fz_value::map_addr_from_tagged(tagged_bits(copied)).unwrap();
        let (_, value) = unsafe { crate::fz_value::map_entry(copied_map as *const u8, 0) };
        assert_eq!(value.kind, ValueKind::LIST);
        assert_ne!(value.raw as *mut u8, child_ptr);
        let copied_list = unsafe { &*(value.raw as *const ListCons) };
        assert_eq!(copied_list.head_kind(), ValueKind::INT);
        assert_eq!(copied_list.head as i64, 7);
    }

    #[test]
    fn gc_map_count_twelve_does_not_collide_with_forwarding_tag() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let entries: Vec<(AnyValue, AnyValue)> = (0..12)
            .map(|i| {
                (
                    AnyValue::new(i as u64, ValueKind::INT),
                    AnyValue::new((i * 2) as u64, ValueKind::INT),
                )
            })
            .collect();
        let bits = h.alloc_map_slots(&entries);
        let old = crate::fz_value::map_addr_from_tagged(bits).unwrap();
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(bits)];
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        let new_p = crate::fz_value::map_addr_from_tagged(root_bits(roots[0])).unwrap();
        assert_ne!(new_p, old);
        assert_eq!(
            unsafe { crate::fz_value::map_count(new_p as *const u8) },
            12
        );
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
        let n3 = alloc_int_list_cons(&mut h, 3, crate::fz_value::EMPTY_LIST);
        let n2 = alloc_int_list_cons(&mut h, 2, n3);
        let n1 = alloc_int_list_cons(&mut h, 1, n2);
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(n1)];
        for _ in 0..15 {
            // Per-cycle garbage that overflows the 1 KiB initial block,
            // forcing grow → abandon → reclaim at next gc().
            for _ in 0..100 {
                let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
            }
            h.gc_with_extra_root_slots(&mut root, &mut roots);
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
                    kind: FieldKind::AnyValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::AnyValue,
                },
            ],
        });
        let mut h = Heap::new(1024, reg.clone());
        let a = h.alloc_struct(pair_id);
        let b = h.alloc_struct(pair_id);
        h.write_field_slot(a, 0, AnyValue::heap_ptr(b, ValueKind::STRUCT));
        h.write_field_slot(a, 8, AnyValue::nil_atom());
        h.write_field_slot(b, 0, AnyValue::heap_ptr(a, ValueKind::STRUCT));
        h.write_field_slot(b, 8, AnyValue::nil_atom());
        let mut root =
            crate::fz_value::heap_object_word(a as *const u8, crate::fz_value::ValueKind::STRUCT)
                as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.live_count(), 2);
    }

    // ===== fz-q8d.1 — ProcBin + intrusive MSO + post-Cheney sweep =========

    use crate::procbin::{
        ProcBin, SharedBinHandle, alloc_procbin, bitstring_bit_len, bitstring_byte_ptr, live_count,
    };

    /// Walk the heap's MSO chain and return the contained tagged pointers
    /// in chain order (head → tail).
    fn mso_chain(h: &Heap) -> Vec<u64> {
        let mut out = Vec::new();
        let mut cur_bits = h.mso_head;
        while cur_bits != 0 {
            let addr = (cur_bits & !crate::fz_value::TAG_MASK) as *mut u8;
            let next = match cur_bits & crate::fz_value::TAG_MASK {
                crate::fz_value::TAG_PROCBIN => unsafe { ProcBin::from_raw(addr).mso_next() },
                crate::fz_value::TAG_RESOURCE => unsafe {
                    crate::resource::ResourceStub::from_raw(addr).mso_next()
                },
                tag => panic!("unexpected MSO tag {tag:#x}"),
            };
            out.push(cur_bits);
            cur_bits = next;
        }
        out
    }

    /// `alloc_procbin` writes a strict 16-byte ProcBin and pushes onto the chain.
    #[test]
    #[serial_test::serial]
    fn alloc_procbin_pushes_into_mso_chain_with_strict_layout() {
        let baseline = live_count();
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let pb = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1, 2, 3, 4], 32));
            let tagged = crate::fz_value::heap_object_word(
                pb.as_raw() as *const u8,
                crate::fz_value::ValueKind::PROCBIN,
            );
            assert_eq!(
                tagged & crate::fz_value::TAG_MASK,
                crate::fz_value::TAG_PROCBIN
            );
            assert_eq!(crate::fz_value::object_size(tagged), 16);
            assert_eq!(mso_chain(&h), vec![tagged]);
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
        let mut root = crate::fz_value::heap_object_word(
            from_pb as *const u8,
            crate::fz_value::ValueKind::PROCBIN,
        ) as *mut u8;
        assert_eq!(live_count(), baseline + 1);
        h.gc(&mut root);
        let new_pb = crate::fz_value::procbin_addr_from_tagged(root as u64).unwrap();
        assert_ne!(new_pb, from_pb, "ProcBin should have moved to to-space");
        assert_eq!(
            mso_chain(&h),
            vec![crate::fz_value::heap_object_word(
                new_pb as *const u8,
                crate::fz_value::ValueKind::PROCBIN
            )],
            "chain rewritten"
        );
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
        assert_eq!(h.mso_head, 0, "dead ProcBin swept from MSO");
        assert_eq!(live_count(), baseline);
    }

    /// Mixed live/dead ProcBins: sweep must read the next link from
    /// from-space while reading the survivor's shared_ptr from to-space.
    #[test]
    #[serial_test::serial]
    fn procbin_mso_chain_intact_through_gc_partial_survival() {
        let baseline = live_count();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let _dead_tail = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1], 8));
        let live = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[2], 8));
        let _dead_head = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[3], 8));
        let live_from = live.as_raw();
        let live_shared = live.shared_raw();
        assert_eq!(mso_chain(&h).len(), 3);
        assert_eq!(live_count(), baseline + 3);

        let mut root = crate::fz_value::heap_object_word(
            live_from as *const u8,
            crate::fz_value::ValueKind::PROCBIN,
        ) as *mut u8;
        h.gc(&mut root);

        let live_to = crate::fz_value::procbin_addr_from_tagged(root as u64).unwrap();
        assert_ne!(live_to, live_from);
        assert_eq!(
            mso_chain(&h),
            vec![crate::fz_value::heap_object_word(
                live_to as *const u8,
                crate::fz_value::ValueKind::PROCBIN
            )]
        );
        assert_eq!(
            unsafe { ProcBin::from_raw(live_to).shared_raw() },
            live_shared
        );
        assert_eq!(live_count(), baseline + 1);
        drop(h);
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

    // ===== deep_copy_slot handles ProcBin via retain =====================

    /// Cross-heap deep_copy of a ProcBin shares the SharedBin.
    #[test]
    #[serial_test::serial]
    fn deep_copy_procbin_shares_via_retain() {
        let baseline = live_count();
        let mut src = Heap::new(SIZE_TABLE[0], empty_registry());
        let mut dst = Heap::new(SIZE_TABLE[0], empty_registry());
        let src_pb = alloc_procbin(&mut src, SharedBinHandle::from_bytes(&[7, 8, 9, 10], 32));
        let shared_p = src_pb.shared_raw();
        let mut fwd = std::collections::HashMap::new();
        let copied = deep_copy_slot(
            AnyValue::heap_ptr(src_pb.as_raw(), ValueKind::PROCBIN),
            &src,
            &mut dst,
            &mut fwd,
        );
        let dst_p = crate::fz_value::procbin_addr_from_tagged(tagged_bits(copied)).unwrap();
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
                    kind: FieldKind::AnyValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::AnyValue,
                },
            ],
        });
        let mut src = Heap::new(SIZE_TABLE[0], reg.clone());
        let mut dst = Heap::new(SIZE_TABLE[0], reg);
        let src_pb = alloc_procbin(&mut src, SharedBinHandle::from_bytes(&[0xab, 0xcd], 16));
        let shared_p = src_pb.shared_raw();
        let proc_bits = crate::fz_value::heap_object_word(
            src_pb.as_raw() as *const u8,
            crate::fz_value::ValueKind::PROCBIN,
        );
        let pair = src.alloc_struct(pair_id);
        let proc_value = heap_root(proc_bits);
        src.write_field_slot(pair, 0, proc_value);
        src.write_field_slot(pair, 8, proc_value);
        let mut fwd = std::collections::HashMap::new();
        let _ = deep_copy_slot(
            AnyValue::heap_ptr(pair, ValueKind::STRUCT),
            &src,
            &mut dst,
            &mut fwd,
        );
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
        let tagged = crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::BITSTRING);
        unsafe {
            assert_eq!(
                tagged & crate::fz_value::TAG_MASK,
                crate::fz_value::TAG_BITSTRING
            );
            assert_eq!(bitstring_bit_len(tagged as *const u8), 256);
            let pay = bitstring_byte_ptr(tagged as *const u8);
            for (i, expected) in bytes.iter().enumerate().take(32) {
                assert_eq!(*pay.add(i), *expected);
            }
        }
        assert_eq!(h.mso_head, 0);
    }

    #[test]
    #[serial_test::serial]
    fn alloc_bitstring_large_routes_to_shared_zone() {
        let baseline = live_count();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let bytes: Vec<u8> = (0..128u8).collect();
        let p = h.alloc_bitstring(&bytes, 1024);
        let tagged = crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::PROCBIN);
        unsafe {
            assert_eq!(
                tagged & crate::fz_value::TAG_MASK,
                crate::fz_value::TAG_PROCBIN
            );
            assert_eq!(crate::fz_value::object_size(tagged), 16);
            assert_eq!(bitstring_bit_len(tagged as *const u8), 1024);
            let pay = bitstring_byte_ptr(tagged as *const u8);
            for (i, expected) in bytes.iter().enumerate().take(128) {
                assert_eq!(*pay.add(i), *expected);
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
        let sender_bits = crate::fz_value::heap_object_word(
            bs_in_sender as *const u8,
            crate::fz_value::ValueKind::PROCBIN,
        );
        let mut receiver_roots: Vec<u64> = Vec::with_capacity(N);
        for r in receivers.iter_mut() {
            let mut fwd = std::collections::HashMap::new();
            let copied = deep_copy_slot(heap_root(sender_bits), &sender, r, &mut fwd);
            receiver_roots.push(tagged_bits(copied));
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
            let mut root_u8 = *root_ptr as *mut u8;
            r.gc(&mut root_u8);
            *root_ptr = root_u8 as u64;
            let chain = mso_chain(r);
            assert_eq!(chain.len(), 1);
            assert_eq!(chain[0], *root_ptr);
        }
        assert_eq!(live_count(), baseline + 1);

        for root_ptr in &receiver_roots {
            unsafe {
                assert_eq!(bitstring_bit_len(*root_ptr as *const u8), 1024);
                let bp = bitstring_byte_ptr(*root_ptr as *const u8);
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
                kind: FieldKind::AnyValue,
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
        let mut root =
            crate::fz_value::heap_object_word(big as *const u8, crate::fz_value::ValueKind::STRUCT)
                as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.fragments.len(), 1, "fragment survives");
        assert_eq!(h.fragments[0].ptr, frag_ptr, "fragment did not move");
        assert!(!h.fragments[0].mark, "mark reset post-GC");
        // Root is unchanged because the fragment did not move.
        assert_eq!(
            crate::fz_value::struct_addr_from_tagged(root as u64),
            Some(big)
        );
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
                kind: FieldKind::AnyValue,
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
        // pair {a, c} into a typed tuple in the bump arena; that becomes a
        // root containing both.
        let pair_id = reg.borrow_mut().register(Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor {
                    offset: 0,
                    kind: FieldKind::AnyValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::AnyValue,
                },
            ],
        });
        let pair = h.alloc_struct(pair_id);
        h.write_field_slot(pair, 0, AnyValue::heap_ptr(a, ValueKind::STRUCT));
        h.write_field_slot(pair, 8, AnyValue::heap_ptr(c, ValueKind::STRUCT));
        let mut root = crate::fz_value::heap_object_word(
            pair as *const u8,
            crate::fz_value::ValueKind::STRUCT,
        ) as *mut u8;
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
                kind: FieldKind::AnyValue,
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
        h.write_field_slot(head, 0, AnyValue::heap_ptr(tail, ValueKind::STRUCT));
        let mut root = crate::fz_value::heap_object_word(
            head as *const u8,
            crate::fz_value::ValueKind::STRUCT,
        ) as *mut u8;
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
                kind: FieldKind::AnyValue,
            });
        }
        let id = reg.borrow_mut().register(Schema {
            name: "Big".into(),
            size: (n_fields * 8) as u32,
            fields,
        });
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let cons = alloc_int_list_cons(&mut h, 7, crate::fz_value::EMPTY_LIST);
        let big = h.alloc_struct(id);
        h.write_field_slot(big, 0, heap_root(cons));
        let mut root =
            crate::fz_value::heap_object_word(big as *const u8, crate::fz_value::ValueKind::STRUCT)
                as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.fragments.len(), 1, "fragment survives");
        let child_value = h.read_field_slot(big, 0);
        assert_eq!(child_value.kind(), crate::fz_value::ValueKind::LIST);
        let child = child_value.raw() as *mut u8;
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
    #[serial_test::serial]
    fn procbin_round_trips_through_bitstring_dispatchers() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let bytes: Vec<u8> = (0..100u8).collect();
        let p = h.alloc_bitstring(&bytes, 800);
        let tagged = crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::PROCBIN);
        let bl = unsafe { bitstring_bit_len(tagged as *const u8) };
        let bp = unsafe { bitstring_byte_ptr(tagged as *const u8) };
        assert_eq!(bl, 800);
        let recovered: Vec<u8> = (0..100).map(|i| unsafe { *bp.add(i) }).collect();
        assert_eq!(recovered, bytes);
    }
}
