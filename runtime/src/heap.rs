//! Per-process bump arena (cps-in-clif §6.1).
//!
//! One block per `Process`. Allocation is pure bump: `bump_top += size`. When
//! `bump_top` would cross `block_end`, we allocate a fresh (larger) block and
//! park the old one in `abandoned_blocks` for `Drop` to free — a leak path
//! that the .8 Cheney collector replaces with a copying GC rooted at
//! `process.parked_cont`.
//!
//! GC is *not* synchronous on allocation. `note_alloc_pressure` sets a flag
//! when occupancy crosses `gc_threshold_bytes`; the scheduler reads the flag
//! at park-time (next quantum boundary) and calls `gc()` — currently a stub
//! that increments `gc_run_count`. Real Cheney body lands in fz-siu.8.

#![allow(dead_code)]

use crate::fz_value::{FzValue, HeapHeader, HeapKind, ListCons};
use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;
use std::rc::Rc;

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
    /// Old blocks abandoned by `grow`. `Drop` frees them. Cheney (.8)
    /// replaces this leak path with a fresh-block copy.
    abandoned_blocks: Vec<(*mut u8, usize)>,
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
        let block_start = Self::alloc_block(capacity);
        Self {
            block_start,
            bump_top: block_start,
            block_end: unsafe { block_start.add(capacity) },
            block_size: capacity,
            size_class: 0,
            low_live_streak: 0,
            abandoned_blocks: Vec::new(),
            schemas,
            pressure: std::sync::atomic::AtomicBool::new(false),
            // Default: half the block. Tunable per-Process for tests that
            // want to force the park-time GC hook to fire.
            gc_threshold_bytes: capacity / 2,
            gc_run_count: 0,
            alloc_count: 0,
        }
    }

    fn alloc_block(size: usize) -> *mut u8 {
        assert!(size > 0 && size % 16 == 0, "block size must be 16-aligned");
        let layout = Layout::from_size_align(size, 16).expect("bad heap layout");
        let p = unsafe { alloc_zeroed(layout) };
        assert!(!p.is_null(), "heap block allocation failed");
        p
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
    /// On overflow, abandons the current block and allocates a fresh one
    /// twice the size (the .8 Cheney collector replaces this leak path
    /// with a copying GC). Caller initializes the `HeapHeader` at the
    /// returned pointer.
    pub fn alloc(&mut self, size: usize) -> *mut HeapHeader {
        let size = (size + 15) & !15;
        assert!(size >= 16, "alloc must include at least the 16-byte header");
        let new_top = unsafe { self.bump_top.add(size) };
        if new_top > self.block_end {
            // Grow: abandon current block, allocate a fresh one at least
            // 2× the current size or large enough to fit `size`, whichever
            // is larger.
            let next_size = std::cmp::max(self.block_size * 2, size.next_power_of_two().max(1024));
            // Round up to 16-align.
            let next_size = (next_size + 15) & !15;
            self.abandoned_blocks.push((self.block_start, self.block_size));
            let new_block = Self::alloc_block(next_size);
            self.block_start = new_block;
            self.bump_top = new_block;
            self.block_end = unsafe { new_block.add(next_size) };
            self.block_size = next_size;
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
        let abandoned: usize = self.abandoned_blocks.iter().map(|(_, s)| *s).sum();
        current + abandoned
    }

    /// Park-time GC. Stub in fz-siu.7: just increments `gc_run_count`.
    /// Real body — Cheney copy from `process.parked_cont` per §6.4 —
    /// lands in fz-siu.8. `roots` is the planned root set; ignored here.
    pub fn gc(&mut self, _roots: &[FzValue]) {
        self.gc_run_count += 1;
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        let layout = Layout::from_size_align(self.block_size, 16).expect("bad heap layout");
        unsafe { dealloc(self.block_start, layout) };
        for (p, size) in self.abandoned_blocks.drain(..) {
            let layout = Layout::from_size_align(size, 16).expect("bad abandoned-block layout");
            unsafe { dealloc(p, layout) };
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

    /// Bump overflow triggers a grow: old block is abandoned (not freed
    /// until Drop), new block holds further allocations. `bytes_used`
    /// covers both. Cheney (.8) replaces this leak path.
    #[test]
    fn alloc_grows_block_on_overflow() {
        // 64-byte initial block: two 32-byte cons cells fit; third forces grow.
        let mut h = Heap::new(64, empty_registry());
        let _a = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        let _b = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        let initial_block = h.block_start;
        let initial_size = h.block_size;
        let _c = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        assert_ne!(h.block_start, initial_block, "grow must move block_start");
        assert!(h.block_size >= initial_size * 2, "grow doubles at minimum");
        assert_eq!(h.abandoned_blocks.len(), 1);
        assert_eq!(h.live_count(), 3);
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

    /// `gc()` is a stub in fz-siu.7: increments the counter, no reclaim.
    /// Cheney body lands in .8.
    #[test]
    fn gc_stub_only_bumps_counter() {
        let mut h = Heap::new(1024, empty_registry());
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        assert_eq!(h.gc_run_count, 0);
        h.gc(&[]);
        assert_eq!(h.gc_run_count, 1);
        // Stub doesn't reclaim: live_count and bytes_used unchanged.
        assert_eq!(h.live_count(), 1);
        assert_eq!(h.bytes_used(), 32);
    }
}
