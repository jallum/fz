//! Runtime helpers for the fz JIT — the `extern "C"` fns the generated
//! Cranelift code calls into. Lifted out of ir_codegen.rs by fz-ul4.23.4
//! so that ir_codegen can become purely codegen and a future AOT backend
//! can link against the same FFI surface without dragging the JIT module
//! along.
//!
//! This file holds the **arith / cmp / eq** cluster (fz-ul4.23.4.1)
//! and the **alloc** cluster (fz-ul4.23.4.7). Other clusters land in
//! sibling tickets:
//!   .8  map     (fz_map_*, fz_key_*)
//!   .9  bitstring (fz_bs_*, decode_*/encode_* bit helpers)
//!   .10 vec     (fz_vec_*)
//!   .11 closure (fz_closure_*, fz_tail_closure)
//!   .12 concurrency (fz_spawn, fz_self, fz_send, fz_receive_attempt)
//!   .13 halt/print (fz_halt, fz_print_value)
//!
//! All fns here have unstable `extern "C"` ABI — they're called by
//! Cranelift-emitted code via the symbol-binding list in
//! `ir_codegen::compile`. Do not reorder args or change return types
//! without updating the matching `declare_function` signatures.

use crate::ir_codegen::current_process;

// ===== Map cluster (fz-ul4.23.4.8) =====
//
// Maps use a heap-backed sorted-array layout. Build-time semantics: codegen
// emits begin -> push (per pair) -> finalize. MapUpdate emits clone(base) ->
// push (per override) -> finalize. The thread-local builder accumulates
// pairs as `(key_bits, val_bits)`; finalize sorts canonically (later writes
// win on duplicate keys) and allocates one heap Map.
//
// Key total ordering for canonical layout: Int < Atom < Special < Ptr;
// within each category, by raw bits (Int compares signed). Keys compare
// equal iff their u64 bits are equal — pointer-equal heap keys for v1.

fn fz_key_category(bits: u64) -> u8 {
    match bits & 0b111 {
        0b001 => 0,
        0b010 => 1,
        0b011 => 2,
        0b000 => 3,
        _ => 4,
    }
}

fn fz_key_cmp(a: u64, b: u64) -> std::cmp::Ordering {
    let ca = fz_key_category(a);
    let cb = fz_key_category(b);
    ca.cmp(&cb).then_with(|| {
        if ca == 0 {
            ((a as i64) >> 3).cmp(&((b as i64) >> 3))
        } else {
            a.cmp(&b)
        }
    })
}

pub(crate) extern "C" fn fz_map_begin() {
    current_process().map_builder = Some(Vec::new());
}

pub(crate) extern "C" fn fz_map_clone(base_bits: u64) {
    use crate::fz_value::{FzValue, HeapKind};
    let mut entries: Vec<(u64, u64)> = Vec::new();
    let p = FzValue(base_bits)
        .unbox_ptr()
        .expect("fz_map_clone base not a heap ptr");
    let header = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Map) {
        panic!("fz_map_clone base is not a Map");
    }
    let count =
        unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) as usize };
    let mut cursor = unsafe { (p as *const u8).add(24) as *const u64 };
    for _ in 0..count {
        let k = unsafe { std::ptr::read(cursor) };
        let v = unsafe { std::ptr::read(cursor.add(1)) };
        cursor = unsafe { cursor.add(2) };
        entries.push((k, v));
    }
    current_process().map_builder = Some(entries);
}

pub(crate) extern "C" fn fz_map_push(key_bits: u64, val_bits: u64) {
    current_process()
        .map_builder
        .as_mut()
        .expect("fz_map_push without begin/clone")
        .push((key_bits, val_bits));
}

pub(crate) extern "C" fn fz_map_finalize() -> u64 {
    use crate::fz_value::FzValue;
    let raw = current_process()
        .map_builder
        .take()
        .expect("fz_map_finalize without begin");
    // Last write wins on duplicate keys: walk in order, dedupe-overwriting.
    let mut by_key: Vec<(u64, u64)> = Vec::with_capacity(raw.len());
    for (k, v) in raw {
        if let Some(slot) = by_key.iter_mut().find(|(ek, _)| fz_key_cmp(*ek, k).is_eq())
        {
            slot.1 = v;
        } else {
            by_key.push((k, v));
        }
    }
    by_key.sort_by(|a, b| fz_key_cmp(a.0, b.0));
    let entries: Vec<(FzValue, FzValue)> =
        by_key.into_iter().map(|(k, v)| (FzValue(k), FzValue(v))).collect();
    let p = current_process().heap.alloc_map(&entries);
    p as u64
}

pub(crate) extern "C" fn fz_map_get(map_bits: u64, key_bits: u64) -> u64 {
    use crate::fz_value::{FzValue, HeapKind};
    let p = FzValue(map_bits)
        .unbox_ptr()
        .expect("fz_map_get on non-ptr");
    let header = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Map) {
        panic!("fz_map_get on non-Map");
    }
    let count =
        unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) as usize };
    let cursor = unsafe { (p as *const u8).add(24) as *const u64 };
    // v1: linear scan. Sorted layout exists primarily so equality and
    // rendering have a deterministic shape; binary search comes alongside
    // a HAMT migration for large maps (separate ticket).
    for i in 0..count {
        let k = unsafe { std::ptr::read(cursor.add(i * 2)) };
        if fz_key_cmp(k, key_bits).is_eq() {
            return unsafe { std::ptr::read(cursor.add(i * 2 + 1)) };
        }
    }
    FzValue::NIL.0
}

// ===== Alloc cluster (fz-ul4.23.4.7) =====

pub(crate) extern "C" fn fz_alloc_list_cons(head_bits: u64, tail_bits: u64) -> u64 {
    use crate::fz_value::FzValue;
    let p = current_process()
        .heap
        .alloc_list_cons(FzValue(head_bits), FzValue(tail_bits));
    // Heap returns 16-byte-aligned pointers (low 4 bits zero), so the raw
    // pointer doubles as the FzValue ptr-tagged encoding (tag bits = 000).
    p as u64
}

/// Allocate a heap-typed Struct. `schema_id` must already be registered in
/// the current Process's heap SchemaRegistry (shared with CompiledModule).
/// Returns the FzValue ptr-bits (heap-aligned, so tag = 000). Caller is
/// responsible for writing field values into payload slots after allocation.
pub(crate) extern "C" fn fz_alloc_struct(schema_id: u32) -> u64 {
    let p = current_process().heap.alloc_struct(schema_id);
    p as u64
}

pub(crate) extern "C" fn fz_alloc_float(bits: u64) -> u64 {
    let f = f64::from_bits(bits);
    let p = current_process().heap.alloc_float(f);
    p as u64
}

/// Allocate a frame for fn `fn_id`, looking up its size in the current
/// Process's frame_sizes table populated at make_process() time.
pub(crate) extern "C" fn fz_alloc_frame_dyn(fn_id: u32) -> *mut u8 {
    let size = *current_process()
        .frame_sizes
        .get(fn_id as usize)
        .unwrap_or_else(|| panic!("frame_sizes has no entry for fn_id {}", fn_id));
    fz_alloc_frame(fn_id, size)
}

/// Public wrapper around the internal frame allocator. Used by the
/// Runtime in src/runtime.rs to spawn a task's entry frame and by
/// ir_codegen for the synchronous run path.
pub(crate) fn fz_alloc_frame_for_test(schema_id: u32, total_size: u32) -> *mut u8 {
    fz_alloc_frame(schema_id, total_size)
}

pub(crate) extern "C" fn fz_alloc_frame(schema_id: u32, total_size: u32) -> *mut u8 {
    use std::alloc::{alloc_zeroed, Layout};
    // Round size up to a multiple of 16 to keep allocator happy and ensure
    // the resulting block aligns whatever follows.
    let rounded = ((total_size as usize) + 15) & !15;
    let layout = Layout::from_size_align(rounded, 16).expect("bad frame layout");
    let p = unsafe { alloc_zeroed(layout) };
    if p.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    unsafe {
        let hp = p as *mut crate::fz_value::HeapHeader;
        (*hp) = crate::fz_value::HeapHeader {
            kind: 0, // Struct
            flags: 0,
            size_bytes: total_size,
            schema_id,
            _reserved: 0,
        };
    }
    p
}

// ===== Arith / cmp / eq cluster (fz-ul4.23.4.1) =====

/// Decode an FzValue (Int or boxed Float) into f64. Panics on other tags.
pub(crate) fn fz_to_f64(bits: u64) -> f64 {
    use crate::fz_value::{FzValue, HeapKind, Tag};
    let v = FzValue(bits);
    match v.tag() {
        Tag::Int => v.unbox_int().unwrap() as f64,
        Tag::Ptr => {
            let p = v.unbox_ptr().unwrap();
            let kind = unsafe { (*p).kind };
            match HeapKind::from_u16(kind) {
                Some(HeapKind::Float) => crate::heap::Heap::read_float(p),
                _ => panic!("arithmetic on non-numeric heap kind {}", kind),
            }
        }
        _ => panic!("arithmetic on non-numeric tag {:?}", v.tag()),
    }
}

pub(crate) fn box_float(f: f64) -> u64 {
    let p = current_process().heap.alloc_float(f);
    p as u64
}

pub(crate) extern "C" fn fz_arith_add(a: u64, b: u64) -> u64 { box_float(fz_to_f64(a) + fz_to_f64(b)) }
pub(crate) extern "C" fn fz_arith_sub(a: u64, b: u64) -> u64 { box_float(fz_to_f64(a) - fz_to_f64(b)) }
pub(crate) extern "C" fn fz_arith_mul(a: u64, b: u64) -> u64 { box_float(fz_to_f64(a) * fz_to_f64(b)) }
pub(crate) extern "C" fn fz_arith_div(a: u64, b: u64) -> u64 { box_float(fz_to_f64(a) / fz_to_f64(b)) }
pub(crate) extern "C" fn fz_arith_mod(a: u64, b: u64) -> u64 { box_float(fz_to_f64(a) % fz_to_f64(b)) }

/// Comparison helpers return FzValue TRUE/FALSE bits. Like the arithmetic
/// helpers, these handle mixed-type operands by promoting Int→f64.
pub(crate) fn cmp_to_fz(b: bool) -> u64 {
    use crate::fz_value::FzValue;
    if b { FzValue::TRUE.0 } else { FzValue::FALSE.0 }
}
pub(crate) extern "C" fn fz_cmp_lt(a: u64, b: u64) -> u64 { cmp_to_fz(fz_to_f64(a) <  fz_to_f64(b)) }
pub(crate) extern "C" fn fz_cmp_le(a: u64, b: u64) -> u64 { cmp_to_fz(fz_to_f64(a) <= fz_to_f64(b)) }
pub(crate) extern "C" fn fz_cmp_gt(a: u64, b: u64) -> u64 { cmp_to_fz(fz_to_f64(a) >  fz_to_f64(b)) }
pub(crate) extern "C" fn fz_cmp_ge(a: u64, b: u64) -> u64 { cmp_to_fz(fz_to_f64(a) >= fz_to_f64(b)) }

/// Structural Eq for two Tag::Ptr FzValues. Both args MUST be Tag::Ptr —
/// the JIT-side dispatch (`both_ptr` test) guarantees this, so the unwraps
/// are infallible. Returns FzValue TRUE/FALSE bits.
///
/// Recursion: List/Struct/Map fields are themselves FzValues that may be
/// scalars or other heap values, so the recursive call dispatches on the
/// child's tag. For scalar children we can short-circuit on raw bit
/// equality before calling back into this fn — `eq_fz` handles that.
pub(crate) extern "C" fn fz_value_eq(a: u64, b: u64) -> u64 {
    cmp_to_fz(eq_fz(a, b))
}

/// Internal recursive equality for FzValues of any tag. Scalars short-
/// circuit on bit-eq; heap-typed pairs of the same kind recurse per kind.
fn eq_fz(a: u64, b: u64) -> bool {
    use crate::fz_value::{FzValue, HeapKind, Tag};
    if a == b { return true; } // covers all scalar same-tag cases + ptr-identity
    let av = FzValue(a);
    let bv = FzValue(b);
    if !matches!((av.tag(), bv.tag()), (Tag::Ptr, Tag::Ptr)) {
        // At least one side is a scalar with different bits -> inequal.
        return false;
    }
    let ap = av.unbox_ptr().unwrap();
    let bp = bv.unbox_ptr().unwrap();
    if ap.is_null() || bp.is_null() {
        return ap == bp;
    }
    let ah = unsafe { &*ap };
    let bh = unsafe { &*bp };
    if ah.kind != bh.kind {
        return false;
    }
    match HeapKind::from_u16(ah.kind) {
        Some(HeapKind::Float) => {
            crate::heap::Heap::read_float(ap) == crate::heap::Heap::read_float(bp)
        }
        Some(HeapKind::List) => eq_list(ap, bp),
        Some(HeapKind::Struct) => eq_struct(ap, bp, ah.schema_id, bh.schema_id),
        Some(HeapKind::Bitstring) => eq_bitstring(ap, bp),
        Some(HeapKind::Map) => eq_map(ap, bp),
        // Closures + Vecs: ticket scope is List/Struct/Bitstring/Map only.
        // Fall back to ptr-identity (already false here, since a != b).
        _ => false,
    }
}

fn eq_list(ap: *mut crate::fz_value::HeapHeader, bp: *mut crate::fz_value::HeapHeader) -> bool {
    use crate::fz_value::{HeapKind, ListCons};
    // Walk both chains in lockstep. NIL terminates both at the same step.
    let mut a = ap as *const u8;
    let mut b = bp as *const u8;
    loop {
        let ac = unsafe { &*(a as *const ListCons) };
        let bc = unsafe { &*(b as *const ListCons) };
        if !eq_fz(ac.head.0, bc.head.0) {
            return false;
        }
        // Decide each tail: NIL => done; Ptr to List => recurse; else mismatch.
        let at = ac.tail.0;
        let bt = bc.tail.0;
        if at == bt {
            return true; // both NIL (same scalar bits) — common terminator
        }
        // If either tail is non-list, the chains diverge.
        let av = crate::fz_value::FzValue(at);
        let bv = crate::fz_value::FzValue(bt);
        let (Some(anp), Some(bnp)) = (av.unbox_ptr(), bv.unbox_ptr()) else {
            return false;
        };
        let ak = unsafe { (*anp).kind };
        let bk = unsafe { (*bnp).kind };
        if HeapKind::from_u16(ak) != Some(HeapKind::List)
            || HeapKind::from_u16(bk) != Some(HeapKind::List)
        {
            return false;
        }
        a = anp as *const u8;
        b = bnp as *const u8;
    }
}

fn eq_struct(
    ap: *mut crate::fz_value::HeapHeader,
    bp: *mut crate::fz_value::HeapHeader,
    a_schema: u32,
    b_schema: u32,
) -> bool {
    if a_schema != b_schema {
        return false;
    }
    // Schema in current Process's heap registry tells us field count.
    let n_fields = {
        let reg = current_process().heap.schemas_registry();
        let registry = reg.borrow();
        registry.get(a_schema).fields.len()
    };
    for i in 0..n_fields {
        let off = (i * 8) as isize;
        let av = unsafe {
            std::ptr::read((ap as *const u8).offset(16 + off) as *const u64)
        };
        let bv = unsafe {
            std::ptr::read((bp as *const u8).offset(16 + off) as *const u64)
        };
        if !eq_fz(av, bv) {
            return false;
        }
    }
    true
}

fn eq_bitstring(
    ap: *mut crate::fz_value::HeapHeader,
    bp: *mut crate::fz_value::HeapHeader,
) -> bool {
    let a_bits = unsafe { std::ptr::read((ap as *const u8).add(16) as *const u64) };
    let b_bits = unsafe { std::ptr::read((bp as *const u8).add(16) as *const u64) };
    if a_bits != b_bits {
        return false;
    }
    let bit_len = a_bits as usize;
    let full_bytes = bit_len / 8;
    let trailing = bit_len % 8;
    let a_pay = unsafe { (ap as *const u8).add(24) };
    let b_pay = unsafe { (bp as *const u8).add(24) };
    for i in 0..full_bytes {
        if unsafe { *a_pay.add(i) != *b_pay.add(i) } {
            return false;
        }
    }
    if trailing > 0 {
        let mask: u8 = 0xFFu8 << (8 - trailing);
        let a_last = unsafe { *a_pay.add(full_bytes) } & mask;
        let b_last = unsafe { *b_pay.add(full_bytes) } & mask;
        if a_last != b_last {
            return false;
        }
    }
    true
}

fn eq_map(
    ap: *mut crate::fz_value::HeapHeader,
    bp: *mut crate::fz_value::HeapHeader,
) -> bool {
    let a_count = unsafe { std::ptr::read((ap as *const u8).add(16) as *const u64) } as usize;
    let b_count = unsafe { std::ptr::read((bp as *const u8).add(16) as *const u64) } as usize;
    if a_count != b_count {
        return false;
    }
    // Both maps store entries in canonical sort order (.11.13), so a
    // pairwise walk suffices — same key-position implies same key.
    let a_cur = unsafe { (ap as *const u8).add(24) as *const u64 };
    let b_cur = unsafe { (bp as *const u8).add(24) as *const u64 };
    for i in 0..a_count {
        let ak = unsafe { std::ptr::read(a_cur.add(i * 2)) };
        let bk = unsafe { std::ptr::read(b_cur.add(i * 2)) };
        if !eq_fz(ak, bk) {
            return false;
        }
        let av = unsafe { std::ptr::read(a_cur.add(i * 2 + 1)) };
        let bv = unsafe { std::ptr::read(b_cur.add(i * 2 + 1)) };
        if !eq_fz(av, bv) {
            return false;
        }
    }
    true
}
