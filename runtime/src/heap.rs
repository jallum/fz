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
//! Forwarding marker: a copied from-space object gets `(to_addr & !0xF) |
//! TAG_FWD` written into word 0. Strict pointer tags carry the object kind.

#![allow(dead_code)]

use crate::fz_value::{
    FzValue, ListCons, MailboxSlot, PackedValueWord, ValueKind, packed_word_from_value,
};
use crate::procbin::{ProcBin, SharedBinHandle, alloc_procbin, mso_drop_all, mso_sweep};
use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Copy)]
struct CopiedObject {
    ptr: *mut u8,
    tag: u64,
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
    /// Packed scalar word bits. GC tracer follows this slot.
    FzValue,
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
    /// fz-ul4.38 — canonical `Tuple{N}` schema. N PackedValueWord slots at offsets
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

    pub fn value_field_count(&self) -> usize {
        self.fields
            .iter()
            .filter(|field| field.kind == FieldKind::FzValue)
            .count()
    }

    pub fn allocation_payload_size(&self) -> usize {
        let kind_bytes = (self.value_field_count() + 7) & !7;
        self.size as usize + kind_bytes
    }

    pub fn value_field_kind_offset(&self, field_offset: u32) -> u32 {
        let mut index = 0u32;
        for field in &self.fields {
            if field.kind == FieldKind::FzValue {
                if field.offset == field_offset {
                    return self.size + index;
                }
                index += 1;
            }
        }
        panic!(
            "schema {} has no FzValue field at offset {}",
            self.name, field_offset
        );
    }

    pub fn fz_value_fields_with_kind_offsets(
        &self,
    ) -> impl Iterator<Item = (&FieldDescriptor, u32)> {
        let mut index = 0u32;
        self.fields.iter().filter_map(move |field| {
            if field.kind != FieldKind::FzValue {
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
            crate::yield_flag::FZ_SHOULD_YIELD.store(1, std::sync::atomic::Ordering::Relaxed);
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

    pub fn alloc_list_cons(&mut self, head: PackedValueWord, tail: PackedValueWord) -> u64 {
        let p = self.alloc(16);
        let head = self.value_from_packed_word(head);
        unsafe {
            std::ptr::write(p as *mut ListCons, ListCons::new(head, tail.0));
        }
        crate::fz_value::tagged_list_bits(p)
    }

    pub fn value_from_packed_word(&self, value: PackedValueWord) -> FzValue {
        if let Some((kind, p)) = self.current_heap_tagged_addr(value.0) {
            return FzValue::heap_ptr(p, kind);
        }
        if matches!(
            value.tag(),
            crate::fz_value::PackedValueTag::Int | crate::fz_value::PackedValueTag::Atom
        ) {
            return FzValue::from_packed_word_bits(value.0);
        }
        if let Some(kind) = ValueKind::new((value.0 & crate::fz_value::TAG_MASK) as u8)
            && kind.is_heap()
        {
            let p = (value.0 & !crate::fz_value::TAG_MASK) as *mut u8;
            if !p.is_null() && self.contains_heap_addr(p) {
                return FzValue::heap_ptr(p, kind);
            }
            if (p as usize) >= 4096 {
                return FzValue::heap_ptr(p, kind);
            }
        }
        FzValue::from_packed_word_bits(value.0)
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

    pub fn packed_word_from_value(&mut self, value: FzValue) -> PackedValueWord {
        let value = if value.kind.is_heap() {
            FzValue::heap_ptr(
                (value.raw & !crate::fz_value::TAG_MASK) as *mut u8,
                value.kind,
            )
        } else {
            value
        };
        packed_word_from_value(value)
    }

    pub fn mailbox_slot_from_packed_word(&self, value: PackedValueWord) -> MailboxSlot {
        MailboxSlot::from_value(self.value_from_packed_word(value))
    }

    pub fn packed_word_from_mailbox_slot(&mut self, slot: MailboxSlot) -> PackedValueWord {
        self.packed_word_from_value(slot.value())
    }

    /// Read a generic value slot in the current object layout.
    ///
    /// Today this is the quarantined single-word compatibility layout. The
    /// closure/struct metadata tickets replace the implementation without
    /// changing callers that only care about canonical `FzValue`.
    ///
    /// # Safety
    /// `slot` must point at an initialized generic value slot in this heap.
    pub unsafe fn read_current_object_value_slot(&self, slot: *const PackedValueWord) -> FzValue {
        let word = unsafe { std::ptr::read(slot) };
        self.value_from_packed_word(word)
    }

    /// Write a generic value slot in the current object layout.
    ///
    /// # Safety
    /// `slot` must point at a writable generic value slot in this heap.
    pub unsafe fn write_current_object_value_slot(
        &mut self,
        slot: *mut PackedValueWord,
        value: FzValue,
    ) {
        let word = self.packed_word_from_value(value);
        unsafe { std::ptr::write(slot, word) };
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
    pub fn alloc_map(&mut self, entries: &[(FzValue, FzValue)]) -> u64 {
        let total = crate::fz_value::map_size_for_count(entries.len());
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(p as *mut u64, entries.len() as u64);
            let tag_p = crate::fz_value::map_tag_ptr(p);
            std::ptr::write_bytes(tag_p, 0, crate::fz_value::map_tag_bytes_len(entries.len()));
            let keys = crate::fz_value::map_keys_ptr(p, entries.len());
            let values = crate::fz_value::map_values_ptr(p, entries.len());
            for (i, (k, v)) in entries.iter().enumerate() {
                std::ptr::write(tag_p.add(i), crate::fz_value::map_pack_tag(k.kind, v.kind));
                std::ptr::write(keys.add(i), k.raw);
                std::ptr::write(values.add(i), v.raw);
            }
        }
        crate::fz_value::tagged_map_bits(p)
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
        crate::fz_value::tagged_closure_bits(p)
    }

    pub fn alloc_closure(
        &mut self,
        schema_id: u32,
        captured_count: usize,
        halt_kind: u16,
        fn_ptr: u64,
        captures: &[PackedValueWord],
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
                let value = self.value_from_packed_word(*capture);
                crate::fz_value::closure_capture_set(p, i, value);
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
        value: FzValue,
    ) {
        unsafe { crate::fz_value::closure_capture_set(closure_addr, idx, value) };
    }

    /// # Safety
    ///
    /// `closure_addr` must point to a live closure allocation with a capture
    /// slot at `idx`.
    pub unsafe fn read_closure_capture_value(
        &self,
        closure_addr: *const u8,
        idx: usize,
    ) -> FzValue {
        unsafe { crate::fz_value::closure_capture_value(closure_addr, idx) }
    }

    /// Strict Vec layout: len: u64 + raw payload (16-byte aligned).
    /// Payload is monotyped raw data, so there are no per-element tags.
    fn alloc_vec_raw(&mut self, len: u64, payload_bytes: usize) -> *mut u8 {
        let total = (8 + payload_bytes + 15) & !15;
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(p as *mut u64, len);
            // Zero payload + any 16-alignment trailing pad.
            std::ptr::write_bytes(p.add(8), 0, total - 8);
        }
        p
    }

    pub fn alloc_vec_i64(&mut self, elements: &[i64]) -> *mut u8 {
        let p = self.alloc_vec_raw(elements.len() as u64, elements.len() * 8);
        unsafe {
            let payload = p.add(8) as *mut i64;
            std::ptr::copy_nonoverlapping(elements.as_ptr(), payload, elements.len());
        }
        p
    }

    pub fn alloc_vec_f64(&mut self, elements: &[f64]) -> *mut u8 {
        let p = self.alloc_vec_raw(elements.len() as u64, elements.len() * 8);
        unsafe {
            let payload = p.add(8) as *mut f64;
            std::ptr::copy_nonoverlapping(elements.as_ptr(), payload, elements.len());
        }
        p
    }

    pub fn alloc_vec_u8(&mut self, elements: &[u8]) -> *mut u8 {
        let p = self.alloc_vec_raw(elements.len() as u64, elements.len());
        unsafe {
            let payload = p.add(8);
            std::ptr::copy_nonoverlapping(elements.as_ptr(), payload, elements.len());
        }
        p
    }

    /// Pack `bits` MSB-first into bytes (matches `bitstr::BitWriter`).
    pub fn alloc_vec_bit(&mut self, bits: &[bool]) -> *mut u8 {
        let nbytes = bits.len().div_ceil(8);
        let p = self.alloc_vec_raw(bits.len() as u64, nbytes);
        unsafe {
            let payload = p.add(8);
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

    /// Read the element count from a strict tagged or older heap vec.
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    pub fn vec_len(p: *const u8) -> u32 {
        if (p as u64) & crate::fz_value::TAG_MASK != 0 {
            let addr = ((p as u64) & !crate::fz_value::TAG_MASK) as *const u8;
            return unsafe { crate::fz_value::vec_len(addr) as u32 };
        }
        unsafe { std::ptr::read(p.add(16) as *const u32) }
    }

    pub fn vec_payload_ptr(p: *const u8) -> *const u8 {
        if (p as u64) & crate::fz_value::TAG_MASK != 0 {
            let addr = ((p as u64) & !crate::fz_value::TAG_MASK) as *const u8;
            return unsafe { crate::fz_value::vec_payload_ptr(addr) };
        }
        p.wrapping_add(24)
    }

    /// Write a canonical value into a Struct's generic payload slot.
    pub fn write_field_value(&mut self, obj: *mut u8, field_offset: u32, value: FzValue) {
        self.write_struct_field_value(obj, field_offset, value);
    }

    fn write_struct_field_value(&self, obj: *mut u8, field_offset: u32, value: FzValue) {
        let schema_id = unsafe { crate::fz_value::struct_schema_id(obj as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        let raw = struct_field_raw_word(value);
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
    pub fn read_field_value(&self, obj: *mut u8, field_offset: u32) -> FzValue {
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
            FzValue::decode_parts(raw, kind).expect("struct field kind")
        }
    }

    /// Compatibility wrapper for callers that still speak single-word values.
    pub fn write_field(&self, obj: *mut u8, field_offset: u32, value: PackedValueWord) {
        let value = self.value_from_packed_word(value);
        self.write_struct_field_value(obj, field_offset, value);
    }

    /// Compatibility wrapper for callers that still speak single-word values.
    pub fn read_field(&self, obj: *mut u8, field_offset: u32) -> PackedValueWord {
        packed_word_from_value(self.read_field_value(obj, field_offset))
    }

    /// Register a schema in this heap's registry, returning its id. Codegen
    /// uses this to register tuple-arity / closure / record schemas at JIT
    /// compile time so the tracer can walk their PackedValueWord fields.
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
        extra_roots: &mut [crate::fz_value::PackedValueWord],
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
        let mut frag_queue: Vec<CopiedObject> = Vec::new();
        let mut copied_objects: Vec<CopiedObject> = Vec::new();

        if !root_slot.is_null() {
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
            ) {
                *root_slot = new_root as *mut u8;
            }
        }

        // Forward extra roots (mid-flight args, mailbox items).
        for v in extra_roots.iter_mut() {
            if let Some(new_bits) = cheney_forward_strict_bits(
                v.0,
                &from_ranges,
                &mut self.fragments,
                &mut frag_queue,
                &mut free,
                to_end,
                &self.schemas.borrow(),
                &mut copied_objects,
            ) {
                *v = crate::fz_value::PackedValueWord(new_bits);
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
                        &schemas,
                        &mut copied_objects,
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
                    ),
                    crate::fz_value::TAG_BITSTRING
                    | crate::fz_value::TAG_PROCBIN
                    | crate::fz_value::TAG_VEC_I64
                    | crate::fz_value::TAG_VEC_F64
                    | crate::fz_value::TAG_VEC_U8
                    | crate::fz_value::TAG_VEC_BIT => {}
                    crate::fz_value::TAG_RESOURCE => cheney_trace_resource(
                        copied.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
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
                    ),
                    crate::fz_value::TAG_BITSTRING
                    | crate::fz_value::TAG_PROCBIN
                    | crate::fz_value::TAG_VEC_I64
                    | crate::fz_value::TAG_VEC_F64
                    | crate::fz_value::TAG_VEC_U8
                    | crate::fz_value::TAG_VEC_BIT => {}
                    crate::fz_value::TAG_RESOURCE => cheney_trace_resource(
                        frag.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
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
        roots: &mut [u64],
        root_tags: &mut [u8],
        mailbox: &mut std::collections::VecDeque<MailboxSlot>,
    ) {
        use crate::fz_value::{PackedValueWord, ValueKind};
        let mut null_root: *mut u8 = std::ptr::null_mut();
        // Collect mailbox into a temporary vec for forwarding, then write back.
        let mb_vec: Vec<MailboxSlot> = mailbox.drain(..).collect();
        let mb_roots: Vec<PackedValueWord> = mb_vec
            .iter()
            .map(|slot| self.packed_word_from_mailbox_slot(*slot))
            .collect();
        let root_count = roots.len().min(root_tags.len());
        let mut root_indices = Vec::new();
        let mut all_extras: Vec<PackedValueWord> = roots
            .iter()
            .copied()
            .zip(root_tags.iter().copied())
            .take(root_count)
            .enumerate()
            .filter_map(|(i, (value, tag))| {
                let kind = ValueKind::new(tag & crate::fz_value::TAG_MASK as u8)?;
                if kind.is_heap() {
                    root_indices.push(i);
                    Some(PackedValueWord(value))
                } else {
                    None
                }
            })
            .chain(mb_roots.iter().copied())
            .collect();
        self.gc_with_extra_roots(&mut null_root, &mut all_extras);
        // Write forwarded values back to roots slab and mailbox.
        let n = root_indices.len();
        for (idx, value) in root_indices.into_iter().zip(all_extras.iter().take(n)) {
            roots[idx] = value.0;
        }
        for v in &all_extras[n..] {
            mailbox.push_back(self.mailbox_slot_from_packed_word(*v));
        }
    }
}

pub fn deep_copy_mailbox_slot(
    slot: MailboxSlot,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> MailboxSlot {
    let kind = slot.kind();
    if kind == ValueKind::LIST && (slot.value & crate::fz_value::TAG_MASK) == 0 {
        return slot;
    }
    if !kind.is_heap() {
        return slot;
    }
    let tagged = PackedValueWord((slot.value & !crate::fz_value::TAG_MASK) | kind.tag() as u64);
    let copied = deep_copy_value(tagged, src_heap, dst_heap, forwarding);
    dst_heap.mailbox_slot_from_packed_word(copied)
}

pub fn deep_copy_tagged_bits(
    bits: u64,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> u64 {
    let copied = deep_copy_fz_value(
        src_heap.value_from_packed_word(PackedValueWord(bits)),
        src_heap,
        dst_heap,
        forwarding,
    );
    packed_word_from_value(copied).0
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
    );
    Some((new_p as u64) | kind.tag() as u64)
}

fn strict_object_size(bits: u64, schemas: &SchemaRegistry) -> usize {
    crate::fz_value::object_size_with_struct_payload(bits, |schema_id| {
        schemas.get(schema_id).allocation_payload_size()
    })
}

#[inline]
fn struct_field_raw_word(value: FzValue) -> u64 {
    if value.kind().is_heap() {
        value.raw() & !crate::fz_value::TAG_MASK
    } else {
        value.raw()
    }
}

fn tagged_heap_bits_from_value(value: FzValue) -> u64 {
    value
        .tagged_heap_bits()
        .expect("heap value must have tagged heap bits")
}

fn list_tail_bits_from_value(value: FzValue) -> u64 {
    if value.kind() == ValueKind::LIST && value.raw() == 0 {
        crate::fz_value::EMPTY_LIST
    } else {
        tagged_heap_bits_from_value(value)
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
) -> *mut u8 {
    match kind {
        ValueKind::LIST => {
            cheney_forward_list(p, fragments, frag_queue, free, to_end, copied_objects)
        }
        ValueKind::PROCBIN => {
            cheney_forward_procbin(p, fragments, frag_queue, free, to_end, copied_objects)
        }
        ValueKind::RESOURCE => {
            cheney_forward_resource(p, fragments, frag_queue, free, to_end, copied_objects)
        }
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
) -> *mut u8 {
    if mark_fragment_for_tracing(p, tag, fragments, frag_queue) {
        return p;
    }
    if let Some(fwd) = is_forwarded_headerless(p) {
        return fwd as *mut u8;
    }
    let size = strict_object_size(bits, schemas);
    copy_to_space_with_confirmed_forwarding(p, size, tag, free, to_end, copied_objects)
}

fn cheney_forward_procbin(
    p: *mut u8,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
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
    )
}

fn cheney_forward_resource(
    p: *mut u8,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
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
) -> *mut u8 {
    let dst = copy_object_to_space(p, size, free, to_end);
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
) -> *mut u8 {
    let dst = copy_object_to_space(p, size, free, to_end);
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
) {
    let cons = unsafe { &mut *obj };
    if cons.head_kind().is_heap() {
        let head = forward_heap_value(
            cons.head_value(),
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            schemas,
            copied_objects,
        );
        cons.head = head.raw();
    }

    let tail_addr = cons.tail_addr();
    if tail_addr != 0 {
        let tail = forward_heap_value(
            FzValue::heap_ptr(tail_addr as *mut u8, ValueKind::LIST),
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            schemas,
            copied_objects,
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
            FzValue::decode_parts(raw, kind).expect("struct field kind")
        };
        if value.kind().is_heap() {
            let forwarded = forward_heap_value(
                value,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
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
) {
    let resource = unsafe { crate::resource::ResourceStub::from_raw(obj) };
    let closure = resource.closure_value();
    if closure.kind().is_heap() {
        let forwarded = forward_heap_value(
            closure,
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            schemas,
            copied_objects,
        );
        resource.closure_value_set(forwarded);
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
) {
    let count = unsafe { crate::fz_value::map_count(obj as *const u8) };
    let tags = unsafe { crate::fz_value::map_tag_ptr(obj as *const u8) };
    let keys = unsafe { crate::fz_value::map_keys_ptr(obj as *const u8, count) };
    let values = unsafe { crate::fz_value::map_values_ptr(obj as *const u8, count) };
    for i in 0..count {
        let tag = unsafe { std::ptr::read(tags.add(i)) };
        let key_kind = crate::fz_value::map_key_kind(tag);
        if key_kind.is_heap() {
            let key =
                FzValue::heap_ptr(unsafe { std::ptr::read(keys.add(i)) } as *mut u8, key_kind);
            let forwarded = forward_heap_value(
                key,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
            );
            unsafe { std::ptr::write(keys.add(i), forwarded.raw()) };
        }
        let value_kind = crate::fz_value::map_value_kind(tag);
        if value_kind.is_heap() {
            let value = FzValue::heap_ptr(
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
            );
            unsafe { std::ptr::write(values.add(i), forwarded.raw()) };
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
) {
    let count = unsafe { crate::fz_value::closure_captured_count(obj as *const u8) };
    for i in 0..count {
        let value = unsafe { crate::fz_value::closure_capture_value(obj as *const u8, i) };
        if value.kind().is_heap() {
            let forwarded = forward_heap_value(
                value,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
            );
            unsafe { crate::fz_value::closure_capture_set(obj as *const u8, i, forwarded) };
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn forward_heap_value(
    value: FzValue,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
) -> FzValue {
    let kind = value.kind();
    let Some(p) = value.heap_addr() else {
        return value;
    };
    if !is_active_from_space_object(p, from_ranges, fragments) {
        return value;
    }
    let new = cheney_forward_object(
        kind,
        tagged_heap_bits_from_value(value),
        p,
        fragments,
        frag_queue,
        free,
        to_end,
        schemas,
        copied_objects,
    );
    FzValue::heap_ptr(new, kind)
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
    src: FzValue,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> FzValue {
    let Some(sp) = src.heap_addr() else {
        return src;
    };
    if sp.is_null() || !src_heap.contains_heap_addr(sp) {
        return src;
    }

    match src.kind() {
        ValueKind::MAP => {
            if let Some(&dp) = forwarding.get(&sp) {
                return FzValue::heap_ptr(dp, ValueKind::MAP);
            }
            let count = unsafe { crate::fz_value::map_count(sp as *const u8) };
            forwarding.insert(sp, std::ptr::null_mut());
            let mut copied_entries: Vec<(FzValue, FzValue)> = Vec::with_capacity(count);
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
            let new_bits = dst_heap.alloc_map(&copied_entries);
            let new_p = crate::fz_value::map_addr_from_tagged(new_bits).expect("new map ptr");
            forwarding.insert(sp, new_p);
            FzValue::heap_ptr(new_p, ValueKind::MAP)
        }
        ValueKind::LIST => {
            if let Some(&dp) = forwarding.get(&sp) {
                return FzValue::heap_ptr(dp, ValueKind::LIST);
            }
            let bits = dst_heap.alloc_list_cons(PackedValueWord::NIL, PackedValueWord::EMPTY_LIST);
            let dp = crate::fz_value::list_addr_from_tagged(bits).expect("new list ptr");
            forwarding.insert(sp, dp);
            let cons = unsafe { &*(sp as *const ListCons) };
            let new_head = if cons.head_kind().is_heap() {
                deep_copy_fz_value(cons.head_value(), src_heap, dst_heap, forwarding)
            } else {
                cons.head_value()
            };
            let new_tail = if cons.tail_addr() == 0 {
                FzValue::empty_list()
            } else {
                deep_copy_fz_value(
                    FzValue::heap_ptr(cons.tail_addr() as *mut u8, ValueKind::LIST),
                    src_heap,
                    dst_heap,
                    forwarding,
                )
            };
            unsafe {
                std::ptr::write(
                    dp as *mut ListCons,
                    ListCons::new(new_head, list_tail_bits_from_value(new_tail)),
                );
            }
            FzValue::heap_ptr(dp, ValueKind::LIST)
        }
        ValueKind::CLOSURE => deep_copy_strict_closure(sp, src_heap, dst_heap, forwarding),
        ValueKind::STRUCT => deep_copy_strict_struct(sp, src_heap, dst_heap, forwarding),
        ValueKind::BITSTRING => {
            if let Some(&dp) = forwarding.get(&sp) {
                return FzValue::heap_ptr(dp, ValueKind::BITSTRING);
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
            FzValue::heap_ptr(new_p, ValueKind::BITSTRING)
        }
        ValueKind::PROCBIN => {
            if let Some(&dp) = forwarding.get(&sp) {
                return FzValue::heap_ptr(dp, ValueKind::PROCBIN);
            }
            let src_pb = unsafe { ProcBin::from_raw(sp) };
            let handle = unsafe { SharedBinHandle::retain_from_raw(src_pb.shared_raw()) };
            let new_p = alloc_procbin(dst_heap, handle).as_raw();
            forwarding.insert(sp, new_p);
            FzValue::heap_ptr(new_p, ValueKind::PROCBIN)
        }
        ValueKind::RESOURCE => {
            use crate::resource::{ResourceHandle, ResourceStub, alloc_resource};
            if let Some(&dp) = forwarding.get(&sp) {
                return FzValue::heap_ptr(dp, ValueKind::RESOURCE);
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
            FzValue::heap_ptr(new_p, ValueKind::RESOURCE)
        }
        kind @ (ValueKind::VEC_I64
        | ValueKind::VEC_F64
        | ValueKind::VEC_U8
        | ValueKind::VEC_BIT) => {
            if let Some(&dp) = forwarding.get(&sp) {
                return FzValue::heap_ptr(dp, kind);
            }
            let len = unsafe { crate::fz_value::vec_len(sp as *const u8) as usize };
            let payload = unsafe { crate::fz_value::vec_payload_ptr(sp as *const u8) };
            let new_p = match kind {
                ValueKind::VEC_I64 => {
                    let elems = unsafe { std::slice::from_raw_parts(payload as *const i64, len) };
                    dst_heap.alloc_vec_i64(elems)
                }
                ValueKind::VEC_F64 => {
                    let elems = unsafe { std::slice::from_raw_parts(payload as *const f64, len) };
                    dst_heap.alloc_vec_f64(elems)
                }
                ValueKind::VEC_U8 => {
                    let elems = unsafe { std::slice::from_raw_parts(payload, len) };
                    dst_heap.alloc_vec_u8(elems)
                }
                ValueKind::VEC_BIT => {
                    let bits = (0..len)
                        .map(|i| {
                            let byte_idx = i / 8;
                            let bit_idx = 7 - (i % 8);
                            let byte = unsafe { *payload.add(byte_idx) };
                            ((byte >> bit_idx) & 1) == 1
                        })
                        .collect::<Vec<bool>>();
                    dst_heap.alloc_vec_bit(&bits)
                }
                _ => unreachable!("vec kind checked above"),
            };
            forwarding.insert(sp, new_p);
            FzValue::heap_ptr(new_p, kind)
        }
        _ => src,
    }
}

fn deep_copy_strict_closure(
    sp: *mut u8,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> FzValue {
    if let Some(&dp) = forwarding.get(&sp) {
        return FzValue::heap_ptr(dp, ValueKind::CLOSURE);
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
        let cv = unsafe { crate::fz_value::closure_capture_value(sp as *const u8, i) };
        let copied = if cv.kind().is_heap() {
            deep_copy_fz_value(cv, src_heap, dst_heap, forwarding)
        } else {
            cv
        };
        unsafe { crate::fz_value::closure_capture_set(dp as *const u8, i, copied) };
    }
    FzValue::heap_ptr(dp, ValueKind::CLOSURE)
}

fn deep_copy_strict_struct(
    sp: *mut u8,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> FzValue {
    if let Some(&dp) = forwarding.get(&sp) {
        return FzValue::heap_ptr(dp, ValueKind::STRUCT);
    }
    let schema_id = unsafe { crate::fz_value::struct_schema_id(sp as *const u8) };
    let dp = dst_heap.alloc_struct(schema_id);
    forwarding.insert(sp, dp);
    let registry = src_heap.schemas.borrow();
    let schema = registry.get(schema_id);
    for (f, _) in schema.fz_value_fields_with_kind_offsets() {
        let child = src_heap.read_field_value(sp, f.offset);
        let copied = if child.kind().is_heap() {
            deep_copy_fz_value(child, src_heap, dst_heap, forwarding)
        } else {
            child
        };
        dst_heap.write_field_value(dp, f.offset, copied);
    }
    for f in &schema.fields {
        match f.kind {
            FieldKind::FzValue => {}
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
    FzValue::heap_ptr(dp, ValueKind::STRUCT)
}

pub fn deep_copy_value(
    src: PackedValueWord,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut std::collections::HashMap<*mut u8, *mut u8>,
) -> PackedValueWord {
    let copied = deep_copy_fz_value(
        src_heap.value_from_packed_word(src),
        src_heap,
        dst_heap,
        forwarding,
    );
    packed_word_from_value(copied)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_value::{PackedValueWord, ValueKind};

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

    #[test]
    fn current_object_value_slot_round_trips_canonical_values() {
        use crate::procbin::{SharedBinHandle, alloc_procbin};
        use crate::resource::{ResourceHandle, alloc_resource, fz_resource_destructor_noop};

        let mut h = Heap::new(1024, empty_registry());
        let bitstring = h.alloc_bitstring(&[1, 2, 3], 24);
        let procbin = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[4, 5, 6], 24));
        let resource = alloc_resource(
            &mut h,
            ResourceHandle::new(
                0x55,
                crate::fz_value::ValueKind::INT.tag(),
                fz_resource_destructor_noop,
            ),
            FzValue::nil_atom(),
        );

        let values = [
            FzValue::int(-7),
            FzValue::atom(3),
            FzValue::empty_list(),
            FzValue::heap_ptr(bitstring, ValueKind::BITSTRING),
            FzValue::heap_ptr(procbin.as_raw(), ValueKind::PROCBIN),
            FzValue::heap_ptr(resource.as_raw(), ValueKind::RESOURCE),
        ];

        for value in values {
            let mut slot = PackedValueWord::NIL;
            unsafe {
                h.write_current_object_value_slot(&mut slot, value);
                let got = h.read_current_object_value_slot(&slot);
                assert_eq!(got, value);
            }
        }
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
                    crate::fz_value::object_size(crate::fz_value::tagged_bitstring_bits(p))
                );
                let payload = crate::fz_value::bitstring_bytes_ptr(p);
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
        let p = h.alloc_list_cons(PackedValueWord::from_int(1), PackedValueWord::NIL);
        assert!(crate::fz_value::list_addr_from_tagged(p).is_some());
        assert_eq!(h.live_count(), 1);
        assert_eq!(h.bytes_used(), 16);
    }

    #[test]
    fn alloc_vec_i64_writes_header_len_and_payload() {
        let mut h = Heap::new(1024, empty_registry());
        let p = h.alloc_vec_i64(&[10, 20, 30]);
        let tagged = crate::fz_value::tagged_vec_bits(p, ValueKind::VEC_I64);
        assert_eq!(crate::fz_value::object_size(tagged), 32);
        assert_eq!(Heap::vec_len(tagged as *const u8), 3);
        unsafe {
            let payload = Heap::vec_payload_ptr(tagged as *const u8) as *const i64;
            assert_eq!(std::ptr::read(payload), 10);
            assert_eq!(std::ptr::read(payload.add(1)), 20);
            assert_eq!(std::ptr::read(payload.add(2)), 30);
        }
    }

    #[test]
    fn alloc_vec_u8_packs_bytes() {
        let mut h = Heap::new(1024, empty_registry());
        let p = h.alloc_vec_u8(&[0xff, 0xab, 0x12]);
        let tagged = crate::fz_value::tagged_vec_bits(p, ValueKind::VEC_U8);
        assert_eq!(crate::fz_value::object_size(tagged), 16);
        assert_eq!(Heap::vec_len(tagged as *const u8), 3);
        unsafe {
            let payload = Heap::vec_payload_ptr(tagged as *const u8);
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
        let tagged = crate::fz_value::tagged_vec_bits(p, ValueKind::VEC_BIT);
        assert_eq!(crate::fz_value::object_size(tagged), 16);
        assert_eq!(Heap::vec_len(tagged as *const u8), 7);
        unsafe {
            let payload = Heap::vec_payload_ptr(tagged as *const u8);
            assert_eq!(*payload, 0b1011_0010);
        }
    }

    #[test]
    fn heap_pointers_are_16_aligned() {
        let mut h = Heap::new(1024, empty_registry());
        for _ in 0..10 {
            let p = h.alloc_list_cons(PackedValueWord::NIL, PackedValueWord::NIL);
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
            let _ = h.alloc_list_cons(PackedValueWord::NIL, PackedValueWord::NIL);
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
        let _ = h.alloc_list_cons(PackedValueWord::NIL, PackedValueWord::NIL);
        assert!(!h.should_gc(), "1 cell at 16 bytes under 64");
        let _ = h.alloc_list_cons(PackedValueWord::NIL, PackedValueWord::NIL);
        assert!(!h.should_gc(), "2 cells at 32 bytes under 64");
        let _ = h.alloc_list_cons(PackedValueWord::NIL, PackedValueWord::NIL);
        let _ = h.alloc_list_cons(PackedValueWord::NIL, PackedValueWord::NIL);
        assert!(h.should_gc(), "4 cells at 64 bytes at threshold");
        h.clear_should_gc_flag();
        assert!(!h.should_gc());
    }

    /// With a null root, Cheney recycles the arena: from-space is freed,
    /// to-space is a fresh empty block, live_count goes to zero.
    #[test]
    fn gc_with_null_root_recycles_arena() {
        let mut h = Heap::new(1024, empty_registry());
        let _ = h.alloc_list_cons(PackedValueWord::NIL, PackedValueWord::NIL);
        let _ = h.alloc_list_cons(PackedValueWord::NIL, PackedValueWord::NIL);
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
        let n3 = h.alloc_list_cons(PackedValueWord::from_int(3), PackedValueWord::EMPTY_LIST);
        let n2 = h.alloc_list_cons(PackedValueWord::from_int(2), PackedValueWord(n3));
        let n1 = h.alloc_list_cons(PackedValueWord::from_int(1), PackedValueWord(n2));
        let mut root = std::ptr::null_mut();
        let mut roots = [PackedValueWord(n1)];
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

    #[test]
    fn mid_flight_slab_mixed_tags_forward_only_heap_roots() {
        let mut h = Heap::new(1024, empty_registry());
        let list_bits =
            h.alloc_list_cons(PackedValueWord::from_int(1), PackedValueWord::EMPTY_LIST);
        let old_list = crate::fz_value::list_addr_from_tagged(list_bits).unwrap();
        let mut roots = [i64::MAX as u64, 1.5f64.to_bits(), list_bits];
        let mut tags = [
            ValueKind::INT.tag(),
            ValueKind::FLOAT.tag(),
            ValueKind::LIST.tag(),
        ];
        let mut mailbox = std::collections::VecDeque::new();

        h.gc_mid_flight(&mut roots, &mut tags, &mut mailbox);

        assert_eq!(roots[0], i64::MAX as u64);
        assert_eq!(roots[1], 1.5f64.to_bits());
        let new_list = crate::fz_value::list_addr_from_tagged(roots[2]).unwrap();
        assert_ne!(new_list, old_list);
        let head = unsafe { (*(new_list as *const crate::fz_value::ListCons)).head_value() };
        assert_eq!(head.kind, ValueKind::INT);
        assert_eq!(head.raw as i64, 1);
    }

    /// Cheney drops unreachable objects: a cell allocated alongside the
    /// root chain but not pointed to by it is discarded. live_count
    /// shrinks to the chain length.
    #[test]
    fn gc_drops_unreachable_objects() {
        let mut h = Heap::new(1024, empty_registry());
        let _orphan = h.alloc_list_cons(PackedValueWord::from_int(99), PackedValueWord::EMPTY_LIST);
        let kept = h.alloc_list_cons(PackedValueWord::from_int(7), PackedValueWord::EMPTY_LIST);
        assert_eq!(h.live_count(), 2);
        let mut root = std::ptr::null_mut();
        let mut roots = [PackedValueWord(kept)];
        h.gc_with_extra_roots(&mut root, &mut roots);
        assert_eq!(h.live_count(), 1, "orphan dropped, kept survives");
        let new_cons = crate::fz_value::list_addr_from_tagged(roots[0].0).unwrap() as *mut ListCons;
        let head = unsafe { (*new_cons).head };
        assert_eq!(head as i64, 7);
    }

    #[test]
    fn list_head_can_be_a_tagged_list_without_int_collision() {
        let mut h = Heap::new(1024, empty_registry());
        let child_bits =
            h.alloc_list_cons(PackedValueWord::from_int(7), PackedValueWord::EMPTY_LIST);
        let parent_bits =
            h.alloc_list_cons(PackedValueWord(child_bits), PackedValueWord::EMPTY_LIST);
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
        let child_bits =
            src.alloc_list_cons(PackedValueWord::from_int(7), PackedValueWord::EMPTY_LIST);
        let parent_bits =
            src.alloc_list_cons(PackedValueWord(child_bits), PackedValueWord::EMPTY_LIST);
        let mut forwarding = std::collections::HashMap::new();

        let copied = deep_copy_value(
            PackedValueWord(parent_bits),
            &src,
            &mut dst,
            &mut forwarding,
        );
        let copied_parent =
            crate::fz_value::list_addr_from_tagged(copied.0).expect("copied parent list ptr");
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
        assert_eq!(child.tail_bits(), PackedValueWord::EMPTY_LIST.0);
    }

    #[test]
    #[serial_test::serial]
    fn deep_copy_strict_heap_kinds_dispatch_from_pointer_tags() {
        use crate::resource::{ResourceHandle, ResourceStub, alloc_resource};

        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
        let mut src = Heap::new(SIZE_TABLE[0], reg.clone());
        let mut dst = Heap::new(SIZE_TABLE[0], reg);

        let list_bits =
            src.alloc_list_cons(PackedValueWord::from_int(7), PackedValueWord::EMPTY_LIST);

        let struct_p = src.alloc_struct(pair_id);
        src.write_field(struct_p, 0, PackedValueWord(list_bits));
        src.write_field(struct_p, 8, PackedValueWord::from_int(11));

        let closure_bits = src.alloc_closure(pair_id, 1, 0, 0x1234, &[PackedValueWord(list_bits)]);

        let bitstring_p = src.alloc_bitstring(b"abc", 24);

        let procbin = alloc_procbin(&mut src, SharedBinHandle::from_bytes(&[1, 2, 3, 4], 32));

        let vec_p = src.alloc_vec_i64(&[10, 20, 30]);

        let resource_closure = src.value_from_packed_word(PackedValueWord(closure_bits));
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
                FzValue::new(1, ValueKind::ATOM),
                FzValue::heap_ptr(
                    crate::fz_value::list_addr_from_tagged(list_bits).unwrap(),
                    ValueKind::LIST,
                ),
            ),
            (
                FzValue::new(2, ValueKind::ATOM),
                FzValue::heap_ptr(struct_p, ValueKind::STRUCT),
            ),
            (
                FzValue::new(3, ValueKind::ATOM),
                FzValue::heap_ptr(
                    crate::fz_value::closure_addr_from_tagged(closure_bits).unwrap(),
                    ValueKind::CLOSURE,
                ),
            ),
            (
                FzValue::new(4, ValueKind::ATOM),
                FzValue::heap_ptr(bitstring_p, ValueKind::BITSTRING),
            ),
            (
                FzValue::new(5, ValueKind::ATOM),
                FzValue::heap_ptr(procbin.as_raw(), ValueKind::PROCBIN),
            ),
            (
                FzValue::new(6, ValueKind::ATOM),
                FzValue::heap_ptr(vec_p, ValueKind::VEC_I64),
            ),
            (
                FzValue::new(7, ValueKind::ATOM),
                FzValue::heap_ptr(resource.as_raw(), ValueKind::RESOURCE),
            ),
        ];
        let map_bits = src.alloc_map(&entries);
        let mut forwarding = std::collections::HashMap::new();

        let copied = deep_copy_value(PackedValueWord(map_bits), &src, &mut dst, &mut forwarding);
        let copied_map = crate::fz_value::map_addr_from_tagged(copied.0).unwrap();

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
        let copied_struct_list = dst.read_field(copied_struct, 0);
        assert!(crate::fz_value::list_addr_from_tagged(copied_struct_list.0).is_some());

        let copied_closure = copied_values[2].raw as *mut u8;
        let copied_capture =
            unsafe { crate::fz_value::closure_capture_value(copied_closure as *const u8, 0) };
        assert!(
            crate::fz_value::list_addr_from_tagged(
                crate::fz_value::packed_word_from_value(copied_capture).0
            )
            .is_some()
        );

        let copied_resource = unsafe { ResourceStub::from_raw(copied_values[6].raw as *mut u8) };
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
            let mut tail = PackedValueWord::NIL;
            for i in 0..len {
                let cell = h.alloc_list_cons(PackedValueWord::from_int(i as i64), tail);
                tail = PackedValueWord(cell);
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
        let n3 = h.alloc_list_cons(PackedValueWord::from_int(3), PackedValueWord::EMPTY_LIST);
        let n2 = h.alloc_list_cons(PackedValueWord::from_int(2), PackedValueWord(n3));
        let n1 = h.alloc_list_cons(PackedValueWord::from_int(1), PackedValueWord(n2));
        let mut root = std::ptr::null_mut();
        let mut roots = [PackedValueWord(n1)];
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
        // Build a schema whose payload is 200 bytes of PackedValueWord fields.
        let n_fields = 200 / 8; // 25 PackedValueWord slots
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

        h.write_field(p, 0, PackedValueWord::from_int(11));
        h.write_field(p, 8, PackedValueWord::from_int(22));

        unsafe {
            assert_eq!(std::ptr::read(p.add(8) as *const u64), 11);
            assert_eq!(std::ptr::read(p.add(16) as *const u64), 22);
            assert_eq!(std::ptr::read(p.add(24) as *const u8), ValueKind::INT.tag());
            assert_eq!(std::ptr::read(p.add(25) as *const u8), ValueKind::INT.tag());
        }
        assert_eq!(h.read_field(p, 0).unbox_int(), Some(11));
        assert_eq!(h.read_field(p, 8).unbox_int(), Some(22));
    }

    #[test]
    fn struct_forwarding_marker_through_gc() {
        let reg = empty_registry();
        let id = reg.borrow_mut().register(Schema::tuple_of_arity(1));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let p = h.alloc_struct(id);
        let old_addr = p;
        h.write_field(p, 0, PackedValueWord::from_int(9));
        let mut root = crate::fz_value::tagged_struct_bits(p) as *mut u8;

        h.gc(&mut root);

        let new_p = crate::fz_value::struct_addr_from_tagged(root as u64).expect("forwarded root");
        assert_ne!(new_p as *const u8, old_addr);
        assert_eq!(h.read_field(new_p, 0).unbox_int(), Some(9));
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
        let entries: Vec<(FzValue, FzValue)> = (0..5)
            .map(|i| {
                (
                    FzValue::new(i as u64, ValueKind::INT),
                    FzValue::new((i * 10) as u64, ValueKind::INT),
                )
            })
            .collect();
        let bits = h.alloc_map(&entries);
        let mut root = std::ptr::null_mut();
        let mut roots = [PackedValueWord(bits)];
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
            let entries: Vec<(FzValue, FzValue)> = (0..count)
                .map(|i| {
                    (
                        FzValue::new(i as u64, ValueKind::INT),
                        FzValue::new((i + 10) as u64, ValueKind::INT),
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
        assert_eq!(unsafe { crate::fz_value::closure_schema_id(p) }, 42);
        assert_eq!(unsafe { crate::fz_value::closure_halt_kind(p) }, 2);
        assert_eq!(unsafe { crate::fz_value::closure_fn_ptr(p) }, 0xfeed_beef);
    }

    #[test]
    fn closure_layout_n_captures() {
        let mut h = Heap::new(1024, empty_registry());
        let captures = [PackedValueWord::from_int(10), PackedValueWord::from_int(20)];
        let bits = h.alloc_closure(7, captures.len(), 1, 0x1234, &captures);
        assert_eq!(crate::fz_value::object_size(bits), 48);
        let p = crate::fz_value::closure_addr_from_tagged(bits).unwrap();
        assert_eq!(unsafe { crate::fz_value::closure_captured_count(p) }, 2);
        for (i, expected) in captures.iter().enumerate() {
            let got = unsafe { crate::fz_value::closure_capture_value(p, i) };
            assert_eq!(got, h.value_from_packed_word(*expected));
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
    fn legacy_bridge_accepts_strict_static_closure_pointer() {
        let h = Heap::new(1024, empty_registry());
        let mut storage = crate::process::AlignedClosureStorage::zeroed();
        let bits = crate::fz_value::tagged_closure_bits(storage.as_ptr() as *const u8);

        let value = h.value_from_packed_word(PackedValueWord(bits));

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
            let entries: Vec<(FzValue, FzValue)> = (0..count)
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
                        FzValue::new(i as u64, key_kind),
                        FzValue::new((100 + i) as u64, value_kind),
                    )
                })
                .collect();
            let mut h = Heap::new(1024, empty_registry());
            let bits = h.alloc_map(&entries);
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
        let f = 3.14f64;
        let bits = h.alloc_map(&[(
            FzValue::new(0, ValueKind::ATOM),
            FzValue::new(f.to_bits(), ValueKind::FLOAT),
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
        let bits = h.alloc_map(&[(
            FzValue::new(1, ValueKind::ATOM),
            FzValue::new(value as u64, ValueKind::INT),
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
        let child_bits =
            src.alloc_list_cons(PackedValueWord::from_int(7), PackedValueWord::EMPTY_LIST);
        let child_ptr = crate::fz_value::list_addr_from_tagged(child_bits).unwrap();
        let map_bits = src.alloc_map(&[(
            FzValue::new(1, ValueKind::ATOM),
            FzValue::heap_ptr(child_ptr, ValueKind::LIST),
        )]);
        let mut forwarding = std::collections::HashMap::new();
        let copied = deep_copy_value(PackedValueWord(map_bits), &src, &mut dst, &mut forwarding);
        let copied_map = crate::fz_value::map_addr_from_tagged(copied.0).unwrap();
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
        let entries: Vec<(FzValue, FzValue)> = (0..12)
            .map(|i| {
                (
                    FzValue::new(i as u64, ValueKind::INT),
                    FzValue::new((i * 2) as u64, ValueKind::INT),
                )
            })
            .collect();
        let bits = h.alloc_map(&entries);
        let old = crate::fz_value::map_addr_from_tagged(bits).unwrap();
        let mut root = std::ptr::null_mut();
        let mut roots = [PackedValueWord(bits)];
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
        let mut root = crate::fz_value::tagged_vec_bits(p, ValueKind::VEC_I64) as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.live_count(), 1);
        let new_p = root as *mut u8;
        assert_eq!(Heap::vec_len(new_p), 100);
        unsafe {
            let payload = Heap::vec_payload_ptr(new_p) as *const i64;
            for (i, expected) in elems.iter().enumerate() {
                assert_eq!(std::ptr::read(payload.add(i)), *expected);
            }
        }
    }

    #[test]
    fn vec_f64_forwarding_marker_through_gc() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let p = h.alloc_vec_f64(&[1.0, 2.5, 3.0]);
        let mut root = crate::fz_value::tagged_vec_bits(p, ValueKind::VEC_F64) as *mut u8;
        h.gc(&mut root);
        let new_p = root as *mut u8;
        assert_eq!(Heap::vec_len(new_p), 3);
        let payload = Heap::vec_payload_ptr(new_p) as *const f64;
        unsafe {
            assert_eq!(std::ptr::read(payload), 1.0);
            assert_eq!(std::ptr::read(payload.add(1)), 2.5);
            assert_eq!(std::ptr::read(payload.add(2)), 3.0);
        }
    }

    #[test]
    fn vec_u8_forwarding_marker_through_gc() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let p = h.alloc_vec_u8(&[0xff, 0xab, 0x12]);
        let mut root = crate::fz_value::tagged_vec_bits(p, ValueKind::VEC_U8) as *mut u8;
        h.gc(&mut root);
        let new_p = root as *mut u8;
        assert_eq!(Heap::vec_len(new_p), 3);
        let payload = Heap::vec_payload_ptr(new_p);
        unsafe {
            assert_eq!(*payload, 0xff);
            assert_eq!(*payload.add(1), 0xab);
            assert_eq!(*payload.add(2), 0x12);
        }
    }

    #[test]
    fn vec_bit_forwarding_marker_through_gc() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let p = h.alloc_vec_bit(&[true, false, true, true]);
        let mut root = crate::fz_value::tagged_vec_bits(p, ValueKind::VEC_BIT) as *mut u8;
        h.gc(&mut root);
        let new_p = root as *mut u8;
        assert_eq!(Heap::vec_len(new_p), 4);
        let payload = Heap::vec_payload_ptr(new_p);
        unsafe {
            assert_eq!(*payload, 0b1011_0000);
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
        let n3 = h.alloc_list_cons(PackedValueWord::from_int(3), PackedValueWord::EMPTY_LIST);
        let n2 = h.alloc_list_cons(PackedValueWord::from_int(2), PackedValueWord(n3));
        let n1 = h.alloc_list_cons(PackedValueWord::from_int(1), PackedValueWord(n2));
        let mut root = std::ptr::null_mut();
        let mut roots = [PackedValueWord(n1)];
        for _ in 0..15 {
            // Per-cycle garbage that overflows the 1 KiB initial block,
            // forcing grow → abandon → reclaim at next gc().
            for _ in 0..100 {
                let _ = h.alloc_list_cons(PackedValueWord::NIL, PackedValueWord::NIL);
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
        h.write_field(
            a,
            0,
            PackedValueWord(crate::fz_value::tagged_struct_bits(b as *const u8)),
        );
        h.write_field(a, 8, PackedValueWord::NIL);
        h.write_field(
            b,
            0,
            PackedValueWord(crate::fz_value::tagged_struct_bits(a as *const u8)),
        );
        h.write_field(b, 8, PackedValueWord::NIL);
        let mut root = crate::fz_value::tagged_struct_bits(a as *const u8) as *mut u8;
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
            let tagged = crate::fz_value::tagged_procbin_bits(pb.as_raw() as *const u8);
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
        let mut root = crate::fz_value::tagged_procbin_bits(from_pb as *const u8) as *mut u8;
        assert_eq!(live_count(), baseline + 1);
        h.gc(&mut root);
        let new_pb = crate::fz_value::procbin_addr_from_tagged(root as u64).unwrap();
        assert_ne!(new_pb, from_pb, "ProcBin should have moved to to-space");
        assert_eq!(
            mso_chain(&h),
            vec![crate::fz_value::tagged_procbin_bits(new_pb as *const u8)],
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

        let mut root = crate::fz_value::tagged_procbin_bits(live_from as *const u8) as *mut u8;
        h.gc(&mut root);

        let live_to = crate::fz_value::procbin_addr_from_tagged(root as u64).unwrap();
        assert_ne!(live_to, live_from);
        assert_eq!(
            mso_chain(&h),
            vec![crate::fz_value::tagged_procbin_bits(live_to as *const u8)]
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
        let v = PackedValueWord(crate::fz_value::tagged_procbin_bits(
            src_pb.as_raw() as *const u8
        ));
        let mut fwd = std::collections::HashMap::new();
        let copied = deep_copy_value(v, &src, &mut dst, &mut fwd);
        let dst_p = crate::fz_value::procbin_addr_from_tagged(copied.0).unwrap();
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
        let proc_bits = crate::fz_value::tagged_procbin_bits(src_pb.as_raw() as *const u8);
        let pair = src.alloc_struct(pair_id);
        src.write_field(pair, 0, PackedValueWord(proc_bits));
        src.write_field(pair, 8, PackedValueWord(proc_bits));
        let mut fwd = std::collections::HashMap::new();
        let _ = deep_copy_value(
            PackedValueWord(crate::fz_value::tagged_struct_bits(pair as *const u8)),
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
        let tagged = crate::fz_value::tagged_bitstring_bits(p);
        unsafe {
            assert_eq!(
                tagged & crate::fz_value::TAG_MASK,
                crate::fz_value::TAG_BITSTRING
            );
            assert_eq!(bitstring_bit_len(tagged as *const u8), 256);
            let pay = bitstring_byte_ptr(tagged as *const u8);
            for i in 0..32 {
                assert_eq!(*pay.add(i), bytes[i]);
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
        let tagged = crate::fz_value::tagged_procbin_bits(p);
        unsafe {
            assert_eq!(
                tagged & crate::fz_value::TAG_MASK,
                crate::fz_value::TAG_PROCBIN
            );
            assert_eq!(crate::fz_value::object_size(tagged), 16);
            assert_eq!(bitstring_bit_len(tagged as *const u8), 1024);
            let pay = bitstring_byte_ptr(tagged as *const u8);
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
        let sender_bits = crate::fz_value::tagged_procbin_bits(bs_in_sender as *const u8);
        let mut receiver_roots: Vec<u64> = Vec::with_capacity(N);
        for r in receivers.iter_mut() {
            let mut fwd = std::collections::HashMap::new();
            let copied = deep_copy_value(PackedValueWord(sender_bits), &sender, r, &mut fwd);
            receiver_roots.push(copied.0);
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
        let mut root = crate::fz_value::tagged_struct_bits(big as *const u8) as *mut u8;
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
        // PackedValueWord fields) — that becomes a root containing both.
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
        h.write_field(
            pair,
            0,
            PackedValueWord(crate::fz_value::tagged_struct_bits(a as *const u8)),
        );
        h.write_field(
            pair,
            8,
            PackedValueWord(crate::fz_value::tagged_struct_bits(c as *const u8)),
        );
        let mut root = crate::fz_value::tagged_struct_bits(pair as *const u8) as *mut u8;
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
        h.write_field(
            head,
            0,
            PackedValueWord(crate::fz_value::tagged_struct_bits(tail as *const u8)),
        );
        let mut root = crate::fz_value::tagged_struct_bits(head as *const u8) as *mut u8;
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
        let cons = h.alloc_list_cons(PackedValueWord::from_int(7), PackedValueWord::EMPTY_LIST);
        let big = h.alloc_struct(id);
        h.write_field(big, 0, PackedValueWord(cons));
        let mut root = crate::fz_value::tagged_struct_bits(big as *const u8) as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.fragments.len(), 1, "fragment survives");
        let child_value = h.read_field_value(big, 0);
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
        let tagged = crate::fz_value::tagged_procbin_bits(p);
        let bl = unsafe { bitstring_bit_len(tagged as *const u8) };
        let bp = unsafe { bitstring_byte_ptr(tagged as *const u8) };
        assert_eq!(bl, 800);
        let recovered: Vec<u8> = (0..100).map(|i| unsafe { *bp.add(i) }).collect();
        assert_eq!(recovered, bytes);
    }
}
