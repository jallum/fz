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

use crate::fz_value::{FzValue, HeapHeader, HeapKind, ListCons};
use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;
use std::rc::Rc;

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
        1024, 1536, 2560, 4096, 6656, 10752,
        17408, 28160, 45568, 73728, 119296, 192768,
    ];
    let mut i = 0;
    while i < 12 {
        t[i] = prefix[i];
        i += 1;
    }
    while i < 32 {
        // next ≈ ceil(prev * 1.2) then aligned up to 16. Integer-only:
        //   ceil(prev * 6 / 5) = (prev * 6 + 4) / 5.
        let raw = (t[i - 1] * 6 + 4) / 5;
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
        Self { free_lists: [const { Vec::new() }; SIZE_TABLE.len()] }
    }

    fn alloc(&mut self, size_class: u8) -> *mut u8 {
        let idx = size_class as usize;
        let size = SIZE_TABLE[idx];
        if let Some(p) = self.free_lists[idx].pop() {
            // Recycled blocks: zero before returning. Cheney + Heap::new
            // expect zero pages.
            unsafe { std::ptr::write_bytes(p, 0, size); }
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
                unsafe { dealloc(p, layout); }
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
        unsafe { dealloc(p, layout); }
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
                unsafe { dealloc(p, layout); }
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

pub struct SchemaRegistry {
    schemas: Vec<Schema>,
}

impl SchemaRegistry {
    pub fn new() -> Self {
        Self { schemas: Vec::new() }
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
}

impl Default for SchemaRegistry {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Heap {
    block_start: *mut u8,
    bump_top: *mut u8,
    block_end: *mut u8,
    block_size: usize,
    /// Index into SIZE_TABLE (§6.3, wired in fz-siu.9). Tracked here so
    /// shrink hysteresis (§6.5) can read/adjust it without growing the API.
    pub size_class: u8,
    /// Counter for shrink hysteresis (§6.5): bumps when a GC reports
    /// live < 25% of current block size; resets otherwise.
    pub low_live_streak: u8,
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
}

impl Heap {
    pub fn new(capacity: usize, schemas: Rc<RefCell<SchemaRegistry>>) -> Self {
        assert!(capacity > 0 && capacity % 16 == 0, "capacity must be 16-aligned");
        let size_class = pick_size_class(capacity);
        let block_size = SIZE_TABLE[size_class as usize];
        let block_start = pool_alloc(size_class);
        Self {
            block_start,
            bump_top: block_start,
            block_end: unsafe { block_start.add(block_size) },
            block_size,
            size_class,
            low_live_streak: 0,
            abandoned_blocks: Vec::new(),
            schemas,
            pressure: std::sync::atomic::AtomicBool::new(false),
            // Default: half the block. Tunable per-Process for tests that
            // want to force the park-time GC hook to fire.
            gc_threshold_bytes: block_size / 2,
            gc_run_count: 0,
            alloc_count: 0,
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
    pub fn alloc(&mut self, size: usize) -> *mut HeapHeader {
        let size = (size + 15) & !15;
        assert!(size >= 16, "alloc must include at least the 16-byte header");
        let new_top = unsafe { self.bump_top.add(size) };
        if new_top > self.block_end {
            // Grow: pick the smallest size_class > current that also fits
            // `size`. Allocate via the pool; abandon the current block
            // for Cheney/Drop to return.
            let want_for_alloc = pick_size_class(size);
            let bumped = self.size_class.saturating_add(1).min((SIZE_TABLE.len() - 1) as u8);
            let new_class = want_for_alloc.max(bumped);
            let new_size = SIZE_TABLE[new_class as usize];
            self.abandoned_blocks.push((self.block_start, self.size_class));
            let new_block = pool_alloc(new_class);
            self.block_start = new_block;
            self.bump_top = new_block;
            self.block_end = unsafe { new_block.add(new_size) };
            self.block_size = new_size;
            self.size_class = new_class;
        }
        let p = self.bump_top;
        self.bump_top = unsafe { self.bump_top.add(size) };
        self.alloc_count += 1;
        self.note_alloc_pressure();
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

    pub fn alloc_list_cons(&mut self, head: FzValue, tail: FzValue) -> *mut HeapHeader {
        let p = self.alloc(32);
        unsafe {
            std::ptr::write(
                p as *mut ListCons,
                ListCons {
                    header: HeapHeader {
                        kind: HeapKind::List as u16,
                        flags: 0,
                        size_bytes: 32,
                        schema_id: 0,
                        _reserved: 0,
                    },
                    head,
                    tail,
                },
            );
        }
        p
    }

    /// Map layout: HeapHeader (16) + entry_count: u64 (8) + entries
    /// [(key: FzValue (8), val: FzValue (8)); N]. Caller supplies a
    /// canonically-sorted entry slice; this performs the heap copy.
    pub fn alloc_map(&mut self, entries: &[(FzValue, FzValue)]) -> *mut HeapHeader {
        let total = (16 + 8 + entries.len() * 16 + 15) & !15;
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(
                p,
                HeapHeader {
                    kind: HeapKind::Map as u16,
                    flags: 0,
                    size_bytes: total as u32,
                    schema_id: 0,
                    _reserved: 0,
                },
            );
            let count_p = (p as *mut u8).add(16) as *mut u64;
            std::ptr::write(count_p, entries.len() as u64);
            let mut cursor = (p as *mut u8).add(24) as *mut FzValue;
            for (k, v) in entries {
                std::ptr::write(cursor, *k);
                cursor = cursor.add(1);
                std::ptr::write(cursor, *v);
                cursor = cursor.add(1);
            }
        }
        p
    }

    /// Bitstring layout: HeapHeader (16) + bit_len: u64 (8) + bytes (padded
    /// to 16). Caller supplies a fully-built byte buffer + bit_len; this
    /// performs the heap copy.
    pub fn alloc_bitstring(&mut self, bytes: &[u8], bit_len: u64) -> *mut HeapHeader {
        let total = (16 + 8 + bytes.len() + 15) & !15;
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
                std::ptr::write_bytes(
                    (p as *mut u8).add(pad_start),
                    0,
                    total - pad_start,
                );
            }
        }
        p
    }

    /// Closure layout (fz-ul4.29.5):
    ///   `HeapHeader (16) + stub_fp (8) + captures: [FzValue; n] (+pad)`
    ///
    /// Header fields (closure-specific use):
    ///   - `flags` = captured count (same as pre-.29.5)
    ///   - `schema_id` = 0 (no registered Schema; layout is uniform — flags
    ///     gives the count, all capture slots are tagged FzValue)
    ///   - `_reserved` = callee body FnId, used by ir_interp's closure
    ///     dispatch and (in principle) by introspection. fz_spawn no
    ///     longer reads this — it dispatches via stub_fp at offset 16.
    ///
    /// Caller writes `stub_fp` at payload offset 0 (heap offset 16) and
    /// captures at payload offsets 8..(8+n*8) (heap offsets 24+). Captures
    /// are always tagged FzValue regardless of the callee's typed entry-
    /// slot kinds; the stub does the tagged→raw conversion when writing
    /// the callee frame.
    pub fn alloc_closure(&mut self, callee_fn_id: u32, captured_count: usize) -> *mut HeapHeader {
        assert!(captured_count <= u16::MAX as usize, "closure captured count overflow");
        let payload = 8 + captured_count * 8;
        let total = (16 + payload + 15) & !15;
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(
                p,
                HeapHeader {
                    kind: HeapKind::Closure as u16,
                    flags: captured_count as u16,
                    size_bytes: total as u32,
                    schema_id: 0,
                    _reserved: callee_fn_id,
                },
            );
            std::ptr::write_bytes((p as *mut u8).add(16), 0, total - 16);
        }
        p
    }

    /// Vec layout (all kinds): `HeapHeader (16) + len: u32 (4) + pad: u32 (4)
    /// + raw_payload (16-byte aligned)`. Kind in the header, payload pure
    /// raw data so SIMD codegen can address it uniformly. Returns the
    /// header pointer with header + len written; payload is zeroed and the
    /// caller writes element bytes directly at offset 24.
    fn alloc_vec_raw(
        &mut self,
        kind: HeapKind,
        len: u32,
        payload_bytes: usize,
    ) -> *mut HeapHeader {
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
        let abandoned: usize = self.abandoned_blocks
            .iter()
            .map(|(_, sc)| SIZE_TABLE[*sc as usize])
            .sum();
        current + abandoned
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
        // Snapshot from-space ranges before we allocate to-space.
        let mut from_ranges: Vec<(*mut u8, *mut u8)> = Vec::with_capacity(
            1 + self.abandoned_blocks.len(),
        );
        from_ranges.push((self.block_start, self.block_end));
        for &(p, sc) in &self.abandoned_blocks {
            from_ranges.push((p, unsafe { p.add(SIZE_TABLE[sc as usize]) }));
        }

        // Pre-pass: compute reachable bytes from the root (cycles tracked
        // via HashSet). Determines the to-space size_class per §6.3 / §6.4
        // — smallest class fitting `live_bytes + slack` where slack is
        // live_bytes itself (target ~50% post-gc occupancy). Null root
        // shrinks to the minimum class.
        let live_bytes = if root_slot.is_null() {
            0
        } else {
            let schemas = self.schemas.borrow();
            count_live_bytes_from(
                *root_slot as *mut HeapHeader,
                &from_ranges,
                &schemas,
            )
        };
        // §6.5 hysteresis: growth is eager (size up the moment live + slack
        // exceeds the current class), but shrink waits for two consecutive
        // low-live (<25%) cycles. The streak counter is updated post-Cheney
        // below; here we read it.
        let live_after_slack = live_bytes.saturating_mul(2);
        let want_class = pick_size_class(live_after_slack);
        let prev_class = self.size_class;
        let size_class = if want_class > prev_class {
            want_class
        } else if self.low_live_streak >= 2 && prev_class > 0 {
            prev_class - 1
        } else {
            prev_class
        };
        let consumed_streak = size_class < prev_class;
        let to_size = SIZE_TABLE[size_class as usize];
        let to_start = pool_alloc(size_class);
        let to_end = unsafe { to_start.add(to_size) };
        let mut free = to_start;
        let mut live_count: u64 = 0;

        if !root_slot.is_null() {
            let new_root = cheney_forward(
                *root_slot as *mut HeapHeader,
                &from_ranges,
                &mut free,
                to_end,
            );
            *root_slot = new_root as *mut u8;
            live_count += 1;

            // Scan loop: process to-space objects breadth-first.
            let schemas = self.schemas.borrow();
            let mut scan = to_start;
            while scan < free {
                let h = scan as *mut HeapHeader;
                let obj_size = unsafe { (*h).size_bytes as usize };
                let before_trace = free;
                cheney_trace_children(h, &from_ranges, &mut free, to_end, &schemas);
                // Every child that triggered a copy contributes one live obj.
                let added = unsafe { free.offset_from(before_trace) } as usize;
                if added > 0 {
                    live_count += count_objects_in_range(before_trace, free) as u64;
                }
                scan = unsafe { scan.add(obj_size) };
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
        // Reset gc_threshold to half the new block. Per-test overrides
        // are sticky across cycles only if the test reasserts them.
        self.gc_threshold_bytes = to_size / 2;
        // §6.5 shrink hysteresis bookkeeping. A "low live" pass is one
        // where surviving bytes fall below 25% of the just-installed block.
        // When the streak we observed at gc-entry was consumed to shrink,
        // reset to 0 — otherwise we'd cascade-shrink on every cycle.
        let live_bytes_postgc = unsafe { free.offset_from(to_start) } as usize;
        if consumed_streak {
            self.low_live_streak = 0;
        } else if live_bytes_postgc * 4 < to_size {
            self.low_live_streak = self.low_live_streak.saturating_add(1);
        } else {
            self.low_live_streak = 0;
        }
    }
}

/// Pre-pass for §6.4: sum `size_bytes` over every from-space object
/// reachable from `root`. Used by gc() to pick the to-space size_class
/// before allocating. Tracks visited pointers in a HashSet so cycles
/// terminate cleanly.
fn count_live_bytes_from(
    root: *mut HeapHeader,
    from_ranges: &[(*mut u8, *mut u8)],
    schemas: &SchemaRegistry,
) -> usize {
    use std::collections::HashSet;
    let mut visited: HashSet<*mut HeapHeader> = HashSet::new();
    let mut stack: Vec<*mut HeapHeader> = vec![root];
    let mut total = 0usize;
    while let Some(p) = stack.pop() {
        if !visited.insert(p) {
            continue;
        }
        let h = unsafe { &*p };
        total += h.size_bytes as usize;
        let kind = HeapKind::from_u16(h.kind).unwrap_or_else(|| {
            panic!("count_live_bytes_from: invalid HeapKind {:#x}", h.kind)
        });
        let push = |slot: *const FzValue, stack: &mut Vec<*mut HeapHeader>| {
            let v = unsafe { std::ptr::read(slot) };
            if let Some(cp) = v.unbox_ptr() {
                if !cp.is_null() && ptr_in_from_space(cp as *mut u8, from_ranges) {
                    stack.push(cp);
                }
            }
        };
        match kind {
            HeapKind::Struct => {
                let schema = schemas.get(h.schema_id);
                for f in &schema.fields {
                    if let FieldKind::FzValue = f.kind {
                        let slot = unsafe {
                            (p as *const u8).add(16).add(f.offset as usize) as *const FzValue
                        };
                        push(slot, &mut stack);
                    }
                }
            }
            HeapKind::List => {
                let head = unsafe { (p as *const u8).add(16) as *const FzValue };
                let tail = unsafe { (p as *const u8).add(24) as *const FzValue };
                push(head, &mut stack);
                push(tail, &mut stack);
            }
            HeapKind::Closure => {
                let count = h.flags as usize;
                for i in 0..count {
                    let slot = unsafe {
                        (p as *const u8).add(24).add(i * 8) as *const FzValue
                    };
                    push(slot, &mut stack);
                }
            }
            HeapKind::Map => {
                let count = unsafe {
                    std::ptr::read((p as *const u8).add(16) as *const u64) as usize
                };
                for i in 0..count {
                    let k = unsafe { (p as *const u8).add(24).add(i * 16) as *const FzValue };
                    let v = unsafe { (p as *const u8).add(24).add(i * 16 + 8) as *const FzValue };
                    push(k, &mut stack);
                    push(v, &mut stack);
                }
            }
            HeapKind::Bitstring | HeapKind::Float
            | HeapKind::VecI64 | HeapKind::VecF64
            | HeapKind::VecU8 | HeapKind::VecBit => {}
        }
    }
    total
}

/// Copy a single from-space object to `*free` and install a forwarding
/// pointer in the from-header. If the from-header already has
/// `FORWARDED_KIND`, returns the existing forwarded pointer instead.
/// Caller must ensure `p` is in from-space (per `ptr_in_from_space`).
fn cheney_forward(
    p: *mut HeapHeader,
    _from_ranges: &[(*mut u8, *mut u8)],
    free: &mut *mut u8,
    to_end: *mut u8,
) -> *mut HeapHeader {
    let h = unsafe { &*p };
    if h.kind == FORWARDED_KIND {
        // Forwarding pointer was written at offset 8 (replacing schema_id +
        // _reserved). Read it back.
        let fwd = unsafe {
            std::ptr::read((p as *const u8).add(8) as *const u64)
        };
        return fwd as *mut HeapHeader;
    }
    let size = h.size_bytes as usize;
    let dst = *free;
    let new_top = unsafe { dst.add(size) };
    assert!(new_top <= to_end, "Cheney: to-space exhausted");
    // Copy the whole object verbatim.
    unsafe { std::ptr::copy_nonoverlapping(p as *const u8, dst, size); }
    *free = new_top;
    // Install forwarding marker in from-header.
    unsafe {
        std::ptr::write(p as *mut u16, FORWARDED_KIND);
        std::ptr::write((p as *mut u8).add(8) as *mut u64, dst as u64);
    }
    dst as *mut HeapHeader
}

/// Trace every FzValue child of a to-space object, forwarding each
/// from-space pointer it contains. Off-heap (static-closure / halt-cont)
/// pointers are detected by range and left untouched.
fn cheney_trace_children(
    obj: *mut HeapHeader,
    from_ranges: &[(*mut u8, *mut u8)],
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
) {
    let kind = HeapKind::from_u16(unsafe { (*obj).kind })
        .unwrap_or_else(|| panic!(
            "Cheney scan: invalid HeapKind {:#x}",
            unsafe { (*obj).kind },
        ));
    match kind {
        HeapKind::Struct => {
            let schema_id = unsafe { (*obj).schema_id };
            let schema = schemas.get(schema_id);
            for f in &schema.fields {
                if let FieldKind::FzValue = f.kind {
                    let slot = unsafe {
                        (obj as *mut u8).add(16).add(f.offset as usize) as *mut FzValue
                    };
                    forward_field(slot, from_ranges, free, to_end);
                }
            }
        }
        HeapKind::List => {
            let head_slot = unsafe { (obj as *mut u8).add(16) as *mut FzValue };
            let tail_slot = unsafe { (obj as *mut u8).add(24) as *mut FzValue };
            forward_field(head_slot, from_ranges, free, to_end);
            forward_field(tail_slot, from_ranges, free, to_end);
        }
        HeapKind::Closure => {
            // Layout: stub_fp (8) at offset 16 — a code pointer, skip.
            // Captures at offset 24+i*8 — FzValue each. `flags` is count.
            let count = unsafe { (*obj).flags } as usize;
            for i in 0..count {
                let slot = unsafe {
                    (obj as *mut u8).add(24).add(i * 8) as *mut FzValue
                };
                forward_field(slot, from_ranges, free, to_end);
            }
        }
        HeapKind::Map => {
            let count = unsafe {
                std::ptr::read((obj as *const u8).add(16) as *const u64) as usize
            };
            for i in 0..count {
                let key_slot = unsafe {
                    (obj as *mut u8).add(24).add(i * 16) as *mut FzValue
                };
                let val_slot = unsafe {
                    (obj as *mut u8).add(24).add(i * 16 + 8) as *mut FzValue
                };
                forward_field(key_slot, from_ranges, free, to_end);
                forward_field(val_slot, from_ranges, free, to_end);
            }
        }
        HeapKind::Bitstring
        | HeapKind::Float
        | HeapKind::VecI64
        | HeapKind::VecF64
        | HeapKind::VecU8
        | HeapKind::VecBit => {
            // Raw payload, no FzValue children.
        }
    }
}

/// For one FzValue slot in a to-space object: if it holds a Ptr-tagged
/// pointer into from-space, copy the target (or follow an existing
/// forwarding) and rewrite the slot. Off-heap and scalar values pass through.
fn forward_field(
    slot: *mut FzValue,
    from_ranges: &[(*mut u8, *mut u8)],
    free: &mut *mut u8,
    to_end: *mut u8,
) {
    let v = unsafe { std::ptr::read(slot) };
    let p = match v.unbox_ptr() {
        Some(p) => p,
        None => return, // scalar / nil
    };
    if p.is_null() {
        return;
    }
    if !ptr_in_from_space(p as *mut u8, from_ranges) {
        return; // off-heap singleton (static closure / halt cont)
    }
    let new = cheney_forward(p, from_ranges, free, to_end);
    unsafe { std::ptr::write(slot, FzValue::from_ptr(new)); }
}

fn ptr_in_from_space(p: *mut u8, from_ranges: &[(*mut u8, *mut u8)]) -> bool {
    from_ranges.iter().any(|&(start, end)| p >= start && p < end)
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
    let kind = HeapKind::from_u16(h.kind)
        .unwrap_or_else(|| panic!("deep_copy: invalid HeapKind {:#x} at {:?}", h.kind, sp));
    // Allocate the destination object up-front per-kind. Some kinds
    // (List, Struct, Map, Closure) need a placeholder so we can record
    // forwarding before recursing into children.
    let dp: *mut HeapHeader = match kind {
        HeapKind::List => {
            // Placeholder cons; head/tail are filled below.
            dst_heap.alloc_list_cons(FzValue::NIL, FzValue::NIL)
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
            let bytes =
                unsafe { std::slice::from_raw_parts((sp as *const u8).add(24), bytes_len) };
            let new_p = dst_heap.alloc_bitstring(bytes, bit_len);
            forwarding.insert(sp, new_p);
            return FzValue(new_p as u64);
        }
        HeapKind::Map => {
            // Collect (k, v) pairs from src, deep-copy each, then alloc
            // a Map in dst with the copied entries.
            let count = unsafe { std::ptr::read((sp as *const u8).add(16) as *const u64) } as usize;
            let cursor = unsafe { (sp as *const u8).add(24) as *const u64 };
            let mut copied_entries: Vec<(FzValue, FzValue)> = Vec::with_capacity(count);
            // Pre-register a placeholder forwarding so cycles don't loop;
            // we don't actually have the dst ptr yet so use null as a
            // sentinel. (Cycles through Maps require mutation, which fz
            // doesn't have today; this is just defensive.)
            let placeholder = std::ptr::null_mut();
            forwarding.insert(sp, placeholder);
            for i in 0..count {
                let k_bits = unsafe { std::ptr::read(cursor.add(i * 2)) };
                let v_bits = unsafe { std::ptr::read(cursor.add(i * 2 + 1)) };
                let nk = deep_copy_value(FzValue(k_bits), src_heap, dst_heap, forwarding);
                let nv = deep_copy_value(FzValue(v_bits), src_heap, dst_heap, forwarding);
                copied_entries.push((nk, nv));
            }
            let new_p = dst_heap.alloc_map(&copied_entries);
            forwarding.insert(sp, new_p);
            return FzValue(new_p as u64);
        }
        HeapKind::Closure => {
            // fz-ul4.29.5: stub_fp at offset 16, captures (FzValue) at
            // offset 24+. Copy stub_fp as raw bytes (it's a code pointer,
            // valid across heaps); deep-copy each captured FzValue.
            let captured_count = h.flags as usize;
            let new_p = dst_heap.alloc_closure(h._reserved, captured_count);
            forwarding.insert(sp, new_p);
            // Copy stub_fp (raw 8 bytes).
            unsafe {
                let fp = std::ptr::read((sp as *const u8).add(16) as *const u64);
                std::ptr::write((new_p as *mut u8).add(16) as *mut u64, fp);
            }
            let src_cursor = unsafe { (sp as *const u8).add(24) as *const FzValue };
            let dst_cursor = unsafe { (new_p as *mut u8).add(24) as *mut FzValue };
            for i in 0..captured_count {
                let child = unsafe { std::ptr::read(src_cursor.add(i)) };
                let nc = deep_copy_value(child, src_heap, dst_heap, forwarding);
                unsafe { std::ptr::write(dst_cursor.add(i), nc); }
            }
            return FzValue(new_p as u64);
        }
        HeapKind::VecI64 => {
            let len = Heap::vec_len(sp) as usize;
            let payload = unsafe { (sp as *const u8).add(24) as *const i64 };
            let v: Vec<i64> = (0..len).map(|i| unsafe { std::ptr::read(payload.add(i)) }).collect();
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
    };
    forwarding.insert(sp, dp);
    // Recurse into fields, writing copied children into dst slots.
    match kind {
        HeapKind::List => {
            let cons = unsafe { &*(sp as *const ListCons) };
            let new_head = deep_copy_value(cons.head, src_heap, dst_heap, forwarding);
            let new_tail = deep_copy_value(cons.tail, src_heap, dst_heap, forwarding);
            unsafe {
                let cd = dp as *mut ListCons;
                (*cd).head = new_head;
                (*cd).tail = new_tail;
            }
        }
        HeapKind::Struct => {
            let registry = src_heap.schemas.borrow();
            let schema = registry.get(h.schema_id);
            for f in &schema.fields {
                if let FieldKind::FzValue = f.kind {
                    let off = 16 + f.offset as usize;
                    let child = unsafe {
                        std::ptr::read((sp as *const u8).add(off) as *const FzValue)
                    };
                    let copied = deep_copy_value(child, src_heap, dst_heap, forwarding);
                    unsafe {
                        std::ptr::write(
                            (dp as *mut u8).add(off) as *mut FzValue,
                            copied,
                        );
                    }
                }
            }
        }
        _ => unreachable!("scalar-only kinds returned early"),
    }
    FzValue(dp as u64)
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
        let id_a = reg.register(Schema { name: "A".into(), size: 0, fields: vec![] });
        let id_b = reg.register(Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor { offset: 0, kind: FieldKind::FzValue },
                FieldDescriptor { offset: 8, kind: FieldKind::FzValue },
            ],
        });
        assert_eq!(id_a, 0);
        assert_eq!(id_b, 1);
        assert_eq!(reg.get(id_a).name, "A");
        assert_eq!(reg.get(id_b).name, "Pair");
    }

    #[test]
    fn alloc_bumps_and_tracks() {
        let mut h = Heap::new(1024, empty_registry());
        let p = h.alloc_list_cons(FzValue::from_int(1), FzValue::NIL);
        assert!(!p.is_null());
        assert_eq!(h.live_count(), 1);
        assert_eq!(h.bytes_used(), 32);
    }

    #[test]
    fn alloc_float_round_trips_payload() {
        let mut h = Heap::new(1024, empty_registry());
        let p = h.alloc_float(3.14);
        unsafe {
            assert_eq!((*p).kind, HeapKind::Float as u16);
            assert_eq!((*p).size_bytes, 32);
        }
        assert_eq!(Heap::read_float(p), 3.14);
    }

    #[test]
    fn alloc_vec_i64_writes_header_len_and_payload() {
        let mut h = Heap::new(1024, empty_registry());
        let p = h.alloc_vec_i64(&[10, 20, 30]);
        unsafe { assert_eq!((*p).kind, HeapKind::VecI64 as u16); }
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
            assert_eq!((p as usize) & 15, 0);
        }
    }

    /// Bump overflow triggers a grow at the next size_class. Old block is
    /// abandoned; new block holds further allocations. `bytes_used`
    /// covers both. The next gc() returns both blocks to the pool.
    #[test]
    fn alloc_grows_to_next_size_class_on_overflow() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        // SIZE_TABLE[0] = 1024 bytes → 32 cons cells fit exactly. Allocate
        // 40 to force grow.
        let initial_block = h.block_start;
        let initial_class = h.size_class;
        for _ in 0..40 {
            let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        }
        assert_ne!(h.block_start, initial_block, "grow must move block_start");
        assert!(h.size_class > initial_class, "grow must bump size_class");
        assert_eq!(h.block_size, SIZE_TABLE[h.size_class as usize]);
        assert!(h.abandoned_blocks.len() >= 1);
        assert_eq!(h.live_count(), 40);
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
        assert!(!h.should_gc(), "1 cell at 32 bytes — under 64");
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        assert!(h.should_gc(), "2 cells at 64 bytes — at threshold");
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
        let n3 = h.alloc_list_cons(FzValue::from_int(3), FzValue::NIL);
        let n2 = h.alloc_list_cons(FzValue::from_int(2), FzValue::from_ptr(n3));
        let n1 = h.alloc_list_cons(FzValue::from_int(1), FzValue::from_ptr(n2));
        let mut root = n1 as *mut u8;
        let old_n1 = n1 as usize;
        h.gc(&mut root);
        assert_ne!(root as usize, old_n1, "root should be rewritten to to-space");
        assert_eq!(h.live_count(), 3, "all three cells copied");
        // Walk the new list and verify integers match.
        let mut cur = root as *mut ListCons;
        let mut sum = 0i64;
        let mut count = 0;
        while !cur.is_null() {
            let h = unsafe { &(*cur).header };
            if h.kind != HeapKind::List as u16 { break; }
            let head = unsafe { (*cur).head };
            sum += head.unbox_int().unwrap();
            count += 1;
            cur = unsafe { (*cur).tail }.unbox_ptr().unwrap_or(std::ptr::null_mut())
                as *mut ListCons;
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
        let _orphan = h.alloc_list_cons(FzValue::from_int(99), FzValue::NIL);
        let kept = h.alloc_list_cons(FzValue::from_int(7), FzValue::NIL);
        assert_eq!(h.live_count(), 2);
        let mut root = kept as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.live_count(), 1, "orphan dropped, kept survives");
        let new_cons = root as *mut ListCons;
        let head = unsafe { (*new_cons).head };
        assert_eq!(head.unbox_int(), Some(7));
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
        assert_eq!(pool_total_cached_blocks(), 1, "pool stayed at 1 cached block");

        pool_drain_for_test();
    }

    #[test]
    fn size_table_first_entry_is_1k() {
        assert_eq!(SIZE_TABLE[0], 1024);
    }

    #[test]
    fn size_table_is_monotonic_and_16_aligned() {
        for i in 1..SIZE_TABLE.len() {
            assert!(SIZE_TABLE[i] > SIZE_TABLE[i - 1],
                "non-monotonic at {}: {} <= {}",
                i, SIZE_TABLE[i], SIZE_TABLE[i - 1]);
            assert_eq!(SIZE_TABLE[i] % 16, 0,
                "entry {} ({}) not 16-aligned", i, SIZE_TABLE[i]);
        }
    }

    #[test]
    fn size_table_tail_is_geometric_ish() {
        // Tail entries grow ~×1.2 (after the Fibonacci low end). Sample
        // index 20 → 21: ratio in [1.18, 1.23].
        let ratio = SIZE_TABLE[21] as f64 / SIZE_TABLE[20] as f64;
        assert!(ratio > 1.18 && ratio < 1.23,
            "tail ratio out of expected range: {}", ratio);
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
                tail = FzValue::from_ptr(cell);
            }
            let head = tail.unbox_ptr().unwrap();
            let mut root = head as *mut u8;
            h.gc(&mut root);
            let live_bytes = len * 32;
            let expected_min = pick_size_class(live_bytes); // without slack
            assert!(h.size_class >= expected_min,
                "size_class {} should fit live_bytes {}", h.size_class, live_bytes);
            assert!((h.size_class as i32) > last_class || last_class < 0,
                "size_class did not climb: prev={}, now={}",
                last_class, h.size_class);
            last_class = h.size_class as i32;
            // Drop the root so next iteration starts fresh.
            let _ = root; // reachable until here
        }
    }

    /// Acceptance (fz-siu.11 / §6.5): a spike-then-settle workload ends
    /// with a smaller heap than peak. After building a large chain
    /// (size_class climbs), we drop it and gc with a tiny working set
    /// repeatedly. Hysteresis demotes size_class one step per pair of
    /// low-live cycles until it bottoms out.
    #[test]
    fn shrink_hysteresis_settles_below_peak() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        // Spike: build a large rooted chain (push size_class up).
        let mut tail = FzValue::NIL;
        for i in 0..2048 {
            let cell = h.alloc_list_cons(FzValue::from_int(i), tail);
            tail = FzValue::from_ptr(cell);
        }
        let head = tail.unbox_ptr().unwrap();
        let mut root = head as *mut u8;
        h.gc(&mut root);
        let peak_class = h.size_class;
        assert!(peak_class >= 4, "spike should drive size_class up; got {}", peak_class);

        // Settle: shrink the working set to one cell, gc repeatedly.
        // Hysteresis requires two consecutive low-live cycles per shrink
        // step, so 2 × peak_class iterations is a safe upper bound.
        let lone_cell = h.alloc_list_cons(FzValue::from_int(42), FzValue::NIL);
        let mut root = lone_cell as *mut u8;
        for _ in 0..(peak_class as usize * 2 + 4) {
            h.gc(&mut root);
        }
        assert!(
            h.size_class < peak_class,
            "size_class did not shrink: peak={}, settled={}",
            peak_class, h.size_class
        );
        assert!(
            h.block_size < SIZE_TABLE[peak_class as usize],
            "block_size did not shrink: peak={}, settled={}",
            SIZE_TABLE[peak_class as usize], h.block_size
        );
    }

    /// Hysteresis defers shrink: one low-live cycle alone must NOT
    /// demote size_class — only two consecutive cycles do. Guards
    /// against thrashing from a single dip.
    #[test]
    fn one_low_live_cycle_does_not_shrink() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        // Climb to a non-zero class.
        let mut tail = FzValue::NIL;
        for i in 0..512 {
            let c = h.alloc_list_cons(FzValue::from_int(i), tail);
            tail = FzValue::from_ptr(c);
        }
        let head = tail.unbox_ptr().unwrap();
        let mut root = head as *mut u8;
        h.gc(&mut root);
        let class_after_spike = h.size_class;
        assert!(class_after_spike >= 2);

        // One gc with small live set: streak goes from 0 → 1. No shrink.
        let small = h.alloc_list_cons(FzValue::from_int(1), FzValue::NIL);
        let mut root = small as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.size_class, class_after_spike,
            "single low-live cycle must not shrink");
        assert_eq!(h.low_live_streak, 1);
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
        let n3 = h.alloc_list_cons(FzValue::from_int(3), FzValue::NIL);
        let n2 = h.alloc_list_cons(FzValue::from_int(2), FzValue::from_ptr(n3));
        let n1 = h.alloc_list_cons(FzValue::from_int(1), FzValue::from_ptr(n2));
        let mut root = n1 as *mut u8;
        for _ in 0..15 {
            // Per-cycle garbage that overflows the 1 KiB initial block,
            // forcing grow → abandon → reclaim at next gc().
            for _ in 0..100 {
                let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
            }
            h.gc(&mut root);
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
                FieldDescriptor { offset: 0, kind: FieldKind::FzValue },
                FieldDescriptor { offset: 8, kind: FieldKind::FzValue },
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
}
