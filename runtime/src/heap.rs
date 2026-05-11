//! Heap with mark-sweep GC and schema-driven generic tracer.
//!
//! Single contiguous 16-aligned region (raw alloc/dealloc; non-moving).
//! Live allocations tracked in `allocs` — sweep filters them and pushes freed
//! ranges to `freelist`. Free blocks have `kind = FREE_KIND` written into the
//! header for debug visibility (and to make a future linear-walk sweep easy).
//!
//! Roots come from explicit `gc(roots: &[FzValue])`. Real root sets land with
//! CPS codegen in fz-ul4.11.9.

#![allow(dead_code)]

use crate::fz_value::{FzValue, HeapHeader, HeapKind, ListCons};
use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

/// Sentinel kind written into freed objects' headers. Outside HeapKind's valid
/// range (0..=7). Used for debug visibility and to support a future linear-walk
/// sweep variant.
pub const FREE_KIND: u16 = 0xFFFF;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldKind {
    FzValue,
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
    base: *mut u8,
    capacity: usize,
    bump: usize,
    freelist: Vec<(usize, usize)>,
    allocs: Vec<usize>,
    pub(crate) schemas: Rc<RefCell<SchemaRegistry>>,
    /// fz-ul4.11.31: soft over-threshold flag set by alloc_* when occupancy
    /// crosses gc_threshold_bytes. Trampoline reads + clears at next tick.
    /// AtomicBool because the libdispatch worker pool (fz-ul4.19.1) may
    /// inspect this from a different thread than the one that set it
    /// (though one task only runs on one worker at a time, the flag
    /// itself is observed at scheduler boundaries).
    over_threshold: std::sync::atomic::AtomicBool,
    pub gc_threshold_bytes: usize,
    /// Count of full mark-sweep GC runs (fz-ul4.11.31 instrumentation).
    /// Tests assert `>= 1` to confirm a safepoint fired.
    pub gc_run_count: u64,
}

impl Heap {
    pub fn new(capacity: usize, schemas: Rc<RefCell<SchemaRegistry>>) -> Self {
        assert!(capacity > 0 && capacity % 16 == 0, "capacity must be 16-aligned");
        let layout = Layout::from_size_align(capacity, 16).expect("bad heap layout");
        let base = unsafe { alloc_zeroed(layout) };
        assert!(!base.is_null(), "heap allocation failed");
        Self {
            base,
            capacity,
            bump: 0,
            freelist: Vec::new(),
            allocs: Vec::new(),
            schemas,
            over_threshold: std::sync::atomic::AtomicBool::new(false),
            // Default: half the heap. Tunable per-Process post-.19.1.
            gc_threshold_bytes: capacity / 2,
            gc_run_count: 0,
        }
    }

    pub fn should_gc(&self) -> bool {
        self.over_threshold.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub fn clear_should_gc_flag(&self) {
        self.over_threshold
            .store(false, std::sync::atomic::Ordering::Relaxed);
    }

    fn note_alloc(&self) {
        if self.bytes_used() >= self.gc_threshold_bytes {
            self.over_threshold
                .store(true, std::sync::atomic::Ordering::Relaxed);
        }
    }

    /// Allocate `size` bytes, rounded up to 16. Returns a pointer suitable for
    /// writing a HeapHeader. Caller must initialize the header.
    pub fn alloc(&mut self, size: usize) -> *mut HeapHeader {
        let size = (size + 15) & !15;
        assert!(size >= 16, "alloc must include at least the 16-byte header");
        // First-fit on freelist.
        for i in 0..self.freelist.len() {
            let (off, fsz) = self.freelist[i];
            if fsz >= size {
                self.freelist.remove(i);
                if fsz > size {
                    self.freelist.push((off + size, fsz - size));
                }
                self.allocs.push(off);
                self.note_alloc();
                return unsafe { self.base.add(off) as *mut HeapHeader };
            }
        }
        if self.bump + size > self.capacity {
            panic!(
                "out of heap (capacity={}, bump={}, requested={})",
                self.capacity, self.bump, size
            );
        }
        let off = self.bump;
        self.bump += size;
        self.allocs.push(off);
        self.note_alloc();
        unsafe { self.base.add(off) as *mut HeapHeader }
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

    /// Closure layout: `HeapHeader (16) + captured: [FzValue; n]`.
    /// `header.kind = HeapKind::Closure`. `header.schema_id` is repurposed
    /// to hold the IR fn id of the lambda body — the trampoline never sees
    /// closure headers (closures are values inside frames, not frames),
    /// so reusing schema_id is safe and skips a per-fn closure schema
    /// registration. Captured count is recoverable as
    /// `(size_bytes - 16) / 8`.
    pub fn alloc_closure(&mut self, fn_id: u32, captured: &[FzValue]) -> *mut HeapHeader {
        let total = (16 + captured.len() * 8 + 15) & !15;
        assert!(captured.len() <= u16::MAX as usize, "closure captured count overflow");
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(
                p,
                HeapHeader {
                    kind: HeapKind::Closure as u16,
                    flags: captured.len() as u16,
                    size_bytes: total as u32,
                    schema_id: fn_id,
                    _reserved: 0,
                },
            );
            let mut cursor = (p as *mut u8).add(16) as *mut FzValue;
            for v in captured {
                std::ptr::write(cursor, *v);
                cursor = cursor.add(1);
            }
            // Zero any trailing 16-alignment padding so renders stay clean.
            let used = 16 + captured.len() * 8;
            if used < total {
                std::ptr::write_bytes(
                    (p as *mut u8).add(used),
                    0,
                    total - used,
                );
            }
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

    pub fn live_count(&self) -> usize {
        self.allocs.len()
    }

    pub fn freelist_len(&self) -> usize {
        self.freelist.len()
    }

    pub fn bytes_used(&self) -> usize {
        self.bump - self.freelist.iter().map(|(_, s)| *s).sum::<usize>()
    }

    pub fn gc(&mut self, roots: &[FzValue]) {
        let mut visitor = MarkVisitor { marked: HashSet::new() };
        {
            let registry = self.schemas.borrow();
            for r in roots {
                walk_heap(*r, &registry, &mut visitor);
            }
        }
        let marked = visitor.marked;
        let mut new_allocs = Vec::with_capacity(self.allocs.len());
        for &off in &self.allocs {
            let p = unsafe { self.base.add(off) as *mut HeapHeader };
            if marked.contains(&p) {
                new_allocs.push(off);
            } else {
                let size = unsafe { (*p).size_bytes as usize };
                unsafe {
                    (*p).kind = FREE_KIND;
                }
                self.freelist.push((off, size));
            }
        }
        self.allocs = new_allocs;
        self.gc_run_count += 1;
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        let layout = Layout::from_size_align(self.capacity, 16).expect("bad heap layout");
        unsafe { dealloc(self.base, layout) };
    }
}

/// fz-ul4.11.31: Visitor protocol for heap traversal. GC mark, message
/// deep-copy (.19.3), and arena-membership check (.19.5) all share this
/// core. `visit` is called per UNIQUE object (the walker tracks revisits via
/// `WalkDecision`); return `Recurse` to process children, `Skip` to suppress
/// recursion (e.g. already-copied object in CopyVisitor), `Stop` to halt.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WalkDecision {
    Recurse,
    Skip,
    Stop,
}

pub trait HeapVisitor {
    fn visit(&mut self, p: *mut HeapHeader, kind: HeapKind) -> WalkDecision;
}

/// Walk the heap object reachable from `root`, calling `visitor.visit(p,
/// kind)` for each pointer encountered. Children are descended only when
/// the visitor returns `Recurse`. Atom / int / nil / boxed scalar leaves
/// (non-Ptr-tagged FzValues) skip the visit entirely.
pub fn walk_heap<V: HeapVisitor>(root: FzValue, reg: &SchemaRegistry, visitor: &mut V) {
    let _ = walk_inner(root, reg, visitor);
}

fn walk_inner<V: HeapVisitor>(
    v: FzValue,
    reg: &SchemaRegistry,
    visitor: &mut V,
) -> WalkDecision {
    let p = match v.unbox_ptr() {
        Some(p) => p,
        None => return WalkDecision::Skip,
    };
    let h = unsafe { &*p };
    let kind = match HeapKind::from_u16(h.kind) {
        Some(k) => k,
        None => {
            // FREE_KIND or unknown: must not be reachable from a live root.
            panic!(
                "walk_heap reached object with invalid HeapKind ({:#x}) at {:?}",
                h.kind, p
            );
        }
    };
    let decision = visitor.visit(p, kind);
    if decision != WalkDecision::Recurse {
        return decision;
    }
    match kind {
        HeapKind::Struct => {
            let schema = reg.get(h.schema_id);
            for f in &schema.fields {
                if let FieldKind::FzValue = f.kind {
                    let child = unsafe {
                        std::ptr::read(
                            (p as *mut u8).add(16).add(f.offset as usize) as *const FzValue,
                        )
                    };
                    if walk_inner(child, reg, visitor) == WalkDecision::Stop {
                        return WalkDecision::Stop;
                    }
                }
            }
        }
        HeapKind::List => {
            let cons = unsafe { &*(p as *mut ListCons) };
            if walk_inner(cons.head, reg, visitor) == WalkDecision::Stop {
                return WalkDecision::Stop;
            }
            if walk_inner(cons.tail, reg, visitor) == WalkDecision::Stop {
                return WalkDecision::Stop;
            }
        }
        HeapKind::Bitstring
        | HeapKind::VecI64
        | HeapKind::VecF64
        | HeapKind::VecU8
        | HeapKind::VecBit
        | HeapKind::Float => {
            // Raw payloads: no FzValue children.
        }
        HeapKind::Closure => {
            let captured_count = h.flags as usize;
            let cursor = unsafe { (p as *const u8).add(16) as *const FzValue };
            for i in 0..captured_count {
                let child = unsafe { std::ptr::read(cursor.add(i)) };
                if walk_inner(child, reg, visitor) == WalkDecision::Stop {
                    return WalkDecision::Stop;
                }
            }
        }
        HeapKind::Map => {
            let count = unsafe {
                std::ptr::read((p as *const u8).add(16) as *const u64) as usize
            };
            let mut cursor = unsafe { (p as *const u8).add(24) as *const FzValue };
            for _ in 0..count {
                let k = unsafe { std::ptr::read(cursor) };
                let val = unsafe { std::ptr::read(cursor.add(1)) };
                cursor = unsafe { cursor.add(2) };
                if walk_inner(k, reg, visitor) == WalkDecision::Stop {
                    return WalkDecision::Stop;
                }
                if walk_inner(val, reg, visitor) == WalkDecision::Stop {
                    return WalkDecision::Stop;
                }
            }
        }
    }
    WalkDecision::Recurse
}

/// MarkVisitor: the GC mark phase. Inserts each visited pointer into the
/// marked set; returns Recurse for fresh objects, Skip for repeats.
struct MarkVisitor {
    marked: HashSet<*mut HeapHeader>,
}

impl HeapVisitor for MarkVisitor {
    fn visit(&mut self, p: *mut HeapHeader, _kind: HeapKind) -> WalkDecision {
        if self.marked.insert(p) {
            WalkDecision::Recurse
        } else {
            WalkDecision::Skip
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
            // Captured FzValues at offset 16; count is in header.flags.
            let captured_count = h.flags as usize;
            let cursor = unsafe { (sp as *const u8).add(16) as *const FzValue };
            let mut copied: Vec<FzValue> = Vec::with_capacity(captured_count);
            // Defensive placeholder for cycles.
            forwarding.insert(sp, std::ptr::null_mut());
            for i in 0..captured_count {
                let child = unsafe { std::ptr::read(cursor.add(i)) };
                let nc = deep_copy_value(child, src_heap, dst_heap, forwarding);
                copied.push(nc);
            }
            let new_p = dst_heap.alloc_closure(h.schema_id, &copied);
            forwarding.insert(sp, new_p);
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

/// fz-ul4.11.31: Walk a frame chain rooted at `cur` (raw *mut HeapHeader of
/// the currently-running frame), emitting every FzValue slot found in any
/// frame's schema. Frames link via cont_ptr at frame[16]; the first field
/// (offset 0) is structural and skipped. Remaining fields are user-Var
/// FzValues per the build_frame_schema invariant.
///
/// A frame's schema_id is the fn's FnId.0; the per-fn frame schemas live in
/// CompiledModule. The caller passes the SchemaRegistry that maps those ids
/// — for v1 the user-data and frame schemas share one registry (Heap's
/// owned Rc); this could split in the future without changing this fn.
pub fn collect_roots_from_frame_chain(
    cur: *mut HeapHeader,
    frame_schemas: &[Schema],
) -> Vec<FzValue> {
    let mut roots = Vec::new();
    let mut visited: HashSet<*mut HeapHeader> = HashSet::new();
    let mut p = cur;
    while !p.is_null() {
        if !visited.insert(p) {
            // Defensive cycle guard. Frames don't structurally cycle, but a
            // bug elsewhere shouldn't lock the walker.
            break;
        }
        let h = unsafe { &*p };
        let schema = match frame_schemas.get(h.schema_id as usize) {
            Some(s) => s,
            None => break,
        };
        // Field 0 = cont_ptr (chain link, handled below). Fields 1..N are
        // user-Var FzValue slots.
        for f in schema.fields.iter().skip(1) {
            if let FieldKind::FzValue = f.kind {
                let slot_addr = unsafe { (p as *const u8).add(16 + f.offset as usize) };
                let bits = unsafe { std::ptr::read(slot_addr as *const u64) };
                roots.push(FzValue(bits));
            }
        }
        // Chain to next frame via cont_ptr at frame[16] (offset 0 of payload).
        let next = unsafe { std::ptr::read((p as *const u8).add(16) as *const *mut HeapHeader) };
        p = next;
    }
    roots
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_value::FzValue;

    fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
        Rc::new(RefCell::new(SchemaRegistry::new()))
    }

    fn pair_schema() -> Schema {
        Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor { offset: 0, kind: FieldKind::FzValue },
                FieldDescriptor { offset: 8, kind: FieldKind::FzValue },
            ],
        }
    }

    #[test]
    fn schema_registry_register_and_get() {
        let mut reg = SchemaRegistry::new();
        let id_a = reg.register(Schema { name: "A".into(), size: 0, fields: vec![] });
        let id_b = reg.register(pair_schema());
        assert_eq!(id_a, 0);
        assert_eq!(id_b, 1);
        assert_eq!(reg.get(id_a).name, "A");
        assert_eq!(reg.get(id_b).name, "Pair");
    }

    #[test]
    fn alloc_bumps_and_tracks() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let p = h.alloc_list_cons(FzValue::from_int(1), FzValue::NIL);
        assert!(!p.is_null());
        assert_eq!(h.live_count(), 1);
        assert_eq!(h.bytes_used(), 32);
    }

    #[test]
    fn gc_keeps_rooted_object() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let p = h.alloc_list_cons(FzValue::from_int(7), FzValue::NIL);
        let v = FzValue::from_ptr(p);
        h.gc(&[v]);
        assert_eq!(h.live_count(), 1);
        assert_eq!(h.freelist_len(), 0);
    }

    #[test]
    fn gc_frees_unrooted_object() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let _p = h.alloc_list_cons(FzValue::from_int(7), FzValue::NIL);
        h.gc(&[]);
        assert_eq!(h.live_count(), 0);
        assert_eq!(h.freelist_len(), 1);
    }

    #[test]
    fn gc_traces_through_cons_chain() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        // [1, 2, 3]
        let n3 = h.alloc_list_cons(FzValue::from_int(3), FzValue::NIL);
        let n2 = h.alloc_list_cons(FzValue::from_int(2), FzValue::from_ptr(n3));
        let n1 = h.alloc_list_cons(FzValue::from_int(1), FzValue::from_ptr(n2));
        h.gc(&[FzValue::from_ptr(n1)]);
        assert_eq!(h.live_count(), 3);
        assert_eq!(h.freelist_len(), 0);
    }

    #[test]
    fn gc_frees_dropped_tail() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let n3 = h.alloc_list_cons(FzValue::from_int(3), FzValue::NIL);
        let n2 = h.alloc_list_cons(FzValue::from_int(2), FzValue::from_ptr(n3));
        let _n1 = h.alloc_list_cons(FzValue::from_int(1), FzValue::from_ptr(n2));
        // Root only n2 → n1 should be freed; n2 and n3 retained.
        h.gc(&[FzValue::from_ptr(n2)]);
        assert_eq!(h.live_count(), 2);
        assert_eq!(h.freelist_len(), 1);
    }

    #[test]
    fn gc_traces_through_struct_fields() {
        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(pair_schema());
        let mut h = Heap::new(1024, reg.clone());

        let leaf = h.alloc_list_cons(FzValue::from_int(99), FzValue::NIL);
        let parent = h.alloc_struct(pair_id);
        h.write_field(parent, 0, FzValue::from_ptr(leaf));
        h.write_field(parent, 8, FzValue::NIL);

        h.gc(&[FzValue::from_ptr(parent)]);
        assert_eq!(h.live_count(), 2);
    }

    #[test]
    fn gc_frees_struct_and_unique_child_when_root_lost() {
        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(pair_schema());
        let mut h = Heap::new(1024, reg.clone());

        let leaf = h.alloc_list_cons(FzValue::from_int(99), FzValue::NIL);
        let parent = h.alloc_struct(pair_id);
        h.write_field(parent, 0, FzValue::from_ptr(leaf));
        h.write_field(parent, 8, FzValue::NIL);

        h.gc(&[]);
        assert_eq!(h.live_count(), 0);
        assert_eq!(h.freelist_len(), 2);
    }

    #[test]
    fn gc_handles_cycle() {
        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(pair_schema());
        let mut h = Heap::new(1024, reg.clone());

        let a = h.alloc_struct(pair_id);
        let b = h.alloc_struct(pair_id);
        // a.0 = b, b.0 = a (cycle)
        h.write_field(a, 0, FzValue::from_ptr(b));
        h.write_field(a, 8, FzValue::NIL);
        h.write_field(b, 0, FzValue::from_ptr(a));
        h.write_field(b, 8, FzValue::NIL);

        // Either root keeps both alive.
        h.gc(&[FzValue::from_ptr(a)]);
        assert_eq!(h.live_count(), 2);

        h.gc(&[FzValue::from_ptr(b)]);
        assert_eq!(h.live_count(), 2);

        // No roots → both freed despite cycle.
        h.gc(&[]);
        assert_eq!(h.live_count(), 0);
        assert_eq!(h.freelist_len(), 2);
    }

    #[test]
    fn alloc_float_round_trips_payload() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let p = h.alloc_float(3.14);
        unsafe {
            assert_eq!((*p).kind, HeapKind::Float as u16);
            assert_eq!((*p).size_bytes, 32);
        }
        assert_eq!(Heap::read_float(p), 3.14);
    }

    #[test]
    fn gc_frees_float_when_unrooted() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let _p = h.alloc_float(2.71);
        h.gc(&[]);
        assert_eq!(h.live_count(), 0);
        assert_eq!(h.freelist_len(), 1);
    }

    #[test]
    fn alloc_vec_i64_writes_header_len_and_payload() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
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
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
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
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        // 1 0 1 1 0 0 1 _ -> 0b1011_0010 = 0xB2 (high 7 bits) + low bit pad 0
        // Per MSB-first packing: bit0 -> high bit. So 1,0,1,1,0,0,1 = 1011001x
        // -> 0xB2 (= 0b10110010, the trailing zero is unused in 7-bit slice).
        let p = h.alloc_vec_bit(&[true, false, true, true, false, false, true]);
        assert_eq!(Heap::vec_len(p), 7);
        unsafe {
            let payload = (p as *const u8).add(24);
            assert_eq!(*payload, 0b1011_0010);
        }
    }

    #[test]
    fn gc_frees_vec_i64_when_unrooted() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let _v = h.alloc_vec_i64(&[1, 2, 3]);
        h.gc(&[]);
        assert_eq!(h.live_count(), 0);
        assert_eq!(h.freelist_len(), 1);
    }

    #[test]
    fn gc_keeps_vec_address_stable_when_rooted() {
        // Non-moving GC: a rooted vec keeps its exact address across a GC.
        // Critical for SIMD codegen which holds payload pointers.
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let p_before = h.alloc_vec_i64(&[100, 200, 300]);
        let root = FzValue::from_ptr(p_before);
        h.gc(&[root]);
        // After GC: root still alive at same address; payload still readable.
        assert_eq!(h.live_count(), 1);
        let p_after = root.unbox_ptr().unwrap();
        assert_eq!(p_before, p_after, "non-moving GC must preserve addresses");
        assert_eq!(Heap::vec_len(p_after), 3);
        unsafe {
            let payload = (p_after as *const u8).add(24) as *const i64;
            assert_eq!(std::ptr::read(payload.add(1)), 200);
        }
    }

    #[test]
    fn gc_traces_closure_captured() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        // captured[0] = leaf list cell. If closure is the only root, leaf
        // must survive GC.
        let leaf = h.alloc_list_cons(FzValue::from_int(7), FzValue::NIL);
        let cl = h.alloc_closure(42, &[FzValue::from_ptr(leaf)]);
        h.gc(&[FzValue::from_ptr(cl)]);
        assert_eq!(h.live_count(), 2);
    }

    #[test]
    fn gc_frees_closure_when_unrooted() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let leaf = h.alloc_list_cons(FzValue::from_int(7), FzValue::NIL);
        let _cl = h.alloc_closure(42, &[FzValue::from_ptr(leaf)]);
        h.gc(&[]);
        assert_eq!(h.live_count(), 0);
        assert_eq!(h.freelist_len(), 2);
    }

    #[test]
    fn alloc_reuses_freelist() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let _a = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        let bump_after_first = h.bump;
        h.gc(&[]);
        assert_eq!(h.freelist_len(), 1);
        let _b = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        // Second alloc should reuse the freelist slot, not bump further.
        assert_eq!(h.bump, bump_after_first);
        assert_eq!(h.freelist_len(), 0);
    }

    #[test]
    fn freed_object_kind_is_free_sentinel() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let p = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        h.gc(&[]);
        unsafe {
            assert_eq!((*p).kind, FREE_KIND);
        }
    }

    #[test]
    fn heap_pointers_are_16_aligned() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        for _ in 0..10 {
            let p = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
            assert_eq!((p as usize) & 15, 0);
        }
    }

    #[test]
    #[should_panic(expected = "out of heap")]
    fn alloc_panics_when_oom() {
        let reg = empty_registry();
        let mut h = Heap::new(64, reg);
        // Each cons is 32 bytes; 64 capacity → 2 fit, third should OOM.
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
    }
}
