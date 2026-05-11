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

// ===== Vec cluster (fz-ul4.23.4.10) =====
//
// Vecs are heap objects with raw element-payload (no FzValues inside).
// Construction stages elements in TLS via begin(kind) -> push(v) ×n ->
// finalize(); per-kind decoding happens at push (for U8/Bit) or finalize
// (Bit packs at the end). VecF64 is gated behind .11.20/.11.23.

#[derive(Debug)]
pub enum VecBuild {
    I64(Vec<i64>),
    U8(Vec<u8>),
    Bit(Vec<bool>),
}

/// kind tag matches `HeapKind as u16`: VecI64=3, VecU8=5, VecBit=6.
pub(crate) extern "C" fn fz_vec_begin(kind_tag: u32) {
    use crate::fz_value::HeapKind;
    let b = match HeapKind::from_u16(kind_tag as u16) {
        Some(HeapKind::VecI64) => VecBuild::I64(Vec::new()),
        Some(HeapKind::VecU8) => VecBuild::U8(Vec::new()),
        Some(HeapKind::VecBit) => VecBuild::Bit(Vec::new()),
        Some(HeapKind::VecF64) => panic!("VecF64 deferred to fz-ul4.11.23"),
        _ => panic!("fz_vec_begin: invalid kind tag {}", kind_tag),
    };
    current_process().vec_builder = Some(b);
}

pub(crate) extern "C" fn fz_vec_push(value_bits: u64) {
    use crate::fz_value::FzValue;
    let n = FzValue(value_bits)
        .unbox_int()
        .expect("fz_vec_push: vec element not Int");
    match current_process()
        .vec_builder
        .as_mut()
        .expect("fz_vec_push without begin")
    {
        VecBuild::I64(v) => v.push(n),
        VecBuild::U8(v) => v.push(n as u8),
        VecBuild::Bit(v) => v.push(n != 0),
    }
}

pub(crate) extern "C" fn fz_vec_finalize() -> u64 {
    let b = current_process()
        .vec_builder
        .take()
        .expect("fz_vec_finalize without begin");
    let heap = &mut current_process().heap;
    let p = match b {
        VecBuild::I64(v) => heap.alloc_vec_i64(&v),
        VecBuild::U8(v) => heap.alloc_vec_u8(&v),
        VecBuild::Bit(v) => heap.alloc_vec_bit(&v),
    };
    p as u64
}

/// vec_get(vec, index) -> element as FzValue Int (for I64/U8/Bit).
/// Out-of-bounds returns FzValue::NIL (mirrors Map's missing-key behavior).
pub(crate) extern "C" fn fz_vec_get(vec_bits: u64, index_bits: u64) -> u64 {
    use crate::fz_value::{FzValue, HeapKind};
    let p = FzValue(vec_bits)
        .unbox_ptr()
        .expect("fz_vec_get: vec not a heap ptr");
    let header = unsafe { &*p };
    let i = FzValue(index_bits)
        .unbox_int()
        .expect("fz_vec_get: index not Int") as usize;
    let len = crate::heap::Heap::vec_len(p) as usize;
    if i >= len {
        return FzValue::NIL.0;
    }
    let payload = unsafe { (p as *const u8).add(24) };
    let n: i64 = match HeapKind::from_u16(header.kind) {
        Some(HeapKind::VecI64) => unsafe {
            std::ptr::read((payload as *const i64).add(i))
        },
        Some(HeapKind::VecU8) => unsafe { *payload.add(i) as i64 },
        Some(HeapKind::VecBit) => {
            let byte_idx = i / 8;
            let bit_idx = 7 - (i % 8);
            let byte = unsafe { *payload.add(byte_idx) };
            ((byte >> bit_idx) & 1) as i64
        }
        Some(HeapKind::VecF64) => panic!("VecF64 deferred to fz-ul4.11.23"),
        _ => panic!("fz_vec_get on non-vec heap kind"),
    };
    FzValue::from_int(n).0
}

// ===== Bitstring cluster (fz-ul4.23.4.9) =====

pub(crate) extern "C" fn fz_bs_begin() {
    current_process().bs_builder = Some(crate::bitstr::BitWriter::new());
}

/// Write one field into the active builder. Field-type tags match the order
/// in `crate::ast::BitType`: Integer=0, Float=1, Binary=2, Bits=3, Utf8=4,
/// Utf16=5, Utf32=6. `size_present` distinguishes None (0) vs Some (1);
/// `size_value` is in size-units (multiplied by `unit` internally).
#[allow(clippy::too_many_arguments)]
pub(crate) extern "C" fn fz_bs_write_field(
    value_bits: u64,
    ty_tag: u32,
    size_present: u32,
    size_value: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
) {
    use crate::ast::BitType;
    use crate::fz_value::{FzValue, HeapKind, Tag};
    let ty = decode_bit_type(ty_tag);
    let size = if size_present != 0 { Some(size_value) } else { None };
    let endian = decode_endian(endian_tag);
    // `signed` is irrelevant on write: two's-complement truncation produces
    // the same bit pattern for signed and unsigned at fixed width. The flag
    // is consumed on read (fz_bs_read_field) for sign extension.
    let _ = signed;
    {
        let w = current_process()
            .bs_builder
            .as_mut()
            .expect("fz_bs_write_field called without fz_bs_begin");
        match ty {
            BitType::Integer => {
                let n = FzValue(value_bits)
                    .unbox_int()
                    .expect("integer bit field expects boxed int");
                let total = size.unwrap_or(8) * unit;
                assert!(total <= 64, "integer field too wide: {}", total);
                let masked = if total < 64 {
                    (n as u64) & ((1u64 << total) - 1)
                } else {
                    n as u64
                };
                let bswap = crate::bitstr::apply_endian_for_write(masked, total, endian);
                w.write_bits(bswap, total as usize);
            }
            BitType::Binary | BitType::Bits => {
                // Source must be a heap Bitstring (Vec(U8) lands in .11.14;
                // until then both Binary and Bits read from a Bitstring).
                let v = FzValue(value_bits);
                let p = match v.tag() {
                    Tag::Ptr => v.unbox_ptr().expect("binary field: bad ptr"),
                    _ => panic!("binary/bits bit field expects heap bitstring"),
                };
                let header = unsafe { &*p };
                if HeapKind::from_u16(header.kind) != Some(HeapKind::Bitstring) {
                    panic!("binary/bits bit field source is not a Bitstring");
                }
                let src_bit_len = unsafe {
                    std::ptr::read((p as *const u8).add(16) as *const u64)
                } as usize;
                let src_bytes_ptr = unsafe { (p as *const u8).add(24) };
                let needed_bits = match (ty, size) {
                    (BitType::Binary, None) => src_bit_len,
                    (BitType::Binary, Some(n)) => (n * unit) as usize,
                    (BitType::Bits, None) => src_bit_len,
                    (BitType::Bits, Some(n)) => (n * unit) as usize,
                    _ => unreachable!(),
                };
                assert!(needed_bits <= src_bit_len, "binary/bits field exceeds source");
                let src_bytes = unsafe {
                    std::slice::from_raw_parts(src_bytes_ptr, src_bit_len.div_ceil(8))
                };
                if needed_bits % 8 == 0 && w.bit_len % 8 == 0 {
                    w.bytes.extend_from_slice(&src_bytes[..needed_bits / 8]);
                    w.bit_len += needed_bits;
                } else {
                    let mut r = crate::bitstr::BitReader {
                        bytes: src_bytes,
                        bit_len: src_bit_len,
                        pos: 0,
                    };
                    for _ in 0..needed_bits {
                        w.append_bit(r.read_bit().unwrap());
                    }
                }
            }
            BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => {
                let cp = FzValue(value_bits)
                    .unbox_int()
                    .expect("utf field expects integer codepoint")
                    as u32;
                let bytes = match ty {
                    BitType::Utf8 => crate::bitstr::encode_utf8(cp),
                    BitType::Utf16 => crate::bitstr::encode_utf16(cp, endian),
                    BitType::Utf32 => crate::bitstr::encode_utf32(cp, endian),
                    _ => unreachable!(),
                };
                let bytes = bytes.expect("invalid codepoint");
                w.write_bytes(&bytes);
            }
            BitType::Float => {
                use crate::bitstr::apply_endian_for_write;
                let total = size.unwrap_or(64) * unit;
                if total != 32 && total != 64 {
                    panic!("float bit field size must be 32 or 64, got {}", total);
                }
                // Decode the FzValue: Int unboxes to i64 then casts to f64;
                // boxed Float reads payload directly. Then bit-cast and write.
                let f = fz_to_f64(value_bits);
                let raw: u64 = if total == 32 {
                    (f as f32).to_bits() as u64
                } else {
                    f.to_bits()
                };
                let raw = apply_endian_for_write(raw, total, endian);
                w.write_bits(raw, total as usize);
            }
        }
    }
}

pub(crate) extern "C" fn fz_bs_finalize() -> u64 {
    let w = current_process()
        .bs_builder
        .take()
        .expect("fz_bs_finalize without fz_bs_begin");
    let bit_len = w.bit_len as u64;
    let bytes = w.bytes;
    let p = current_process().heap.alloc_bitstring(&bytes, bit_len);
    p as u64
}

fn decode_bit_type(t: u32) -> crate::ast::BitType {
    use crate::ast::BitType;
    match t {
        0 => BitType::Integer,
        1 => BitType::Float,
        2 => BitType::Binary,
        3 => BitType::Bits,
        4 => BitType::Utf8,
        5 => BitType::Utf16,
        6 => BitType::Utf32,
        _ => panic!("unknown bit type tag {}", t),
    }
}

fn decode_endian(e: u32) -> crate::ast::Endian {
    use crate::ast::Endian;
    match e {
        0 => Endian::Big,
        1 => Endian::Little,
        2 => Endian::Native,
        _ => panic!("unknown endian tag {}", e),
    }
}

/// Allocate a 3-tuple reader `[bs_ptr, bit_len_int, pos_int]` for an input
/// bitstring. Schema id is set by compile() into BS_TUPLE_ARITY3_SCHEMA.
pub(crate) extern "C" fn fz_bs_reader_init(bs_bits: u64) -> u64 {
    use crate::fz_value::{FzValue, HeapKind, Tag};
    let v = FzValue(bs_bits);
    let p = match v.tag() {
        Tag::Ptr => v.unbox_ptr().expect("reader_init: bad ptr"),
        _ => panic!("reader_init expects heap value"),
    };
    let header = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Bitstring) {
        panic!("reader_init source is not a Bitstring");
    }
    let bit_len = unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) } as i64;
    let arity3 = current_process()
        .bs_tuple_arity3_schema
        .expect("bs_tuple_arity3_schema not set");
    let tuple_p = current_process().heap.alloc_struct(arity3);
    unsafe {
        let base = (tuple_p as *mut u8).add(16);
        // [bs_ptr, bit_len_boxed, 0_boxed]
        std::ptr::write(base as *mut u64, bs_bits);
        std::ptr::write(base.add(8) as *mut u64, ((bit_len as u64) << 3) | 0b001);
        std::ptr::write(base.add(16) as *mut u64, ((0i64 as u64) << 3) | 0b001);
    }
    tuple_p as u64
}

#[allow(clippy::too_many_arguments)]
pub(crate) extern "C" fn fz_bs_read_field(
    reader_bits: u64,
    ty_tag: u32,
    size_present: u32,
    size_value: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
    is_last: u32,
) -> u64 {
    use crate::ast::BitType;
    use crate::bitstr::{apply_endian_for_read, sign_extend};
    use crate::fz_value::{FzValue, HeapKind};
    let ty = decode_bit_type(ty_tag);
    let size = if size_present != 0 { Some(size_value) } else { None };
    let endian = decode_endian(endian_tag);
    let signed_b = signed != 0;
    let is_last_b = is_last != 0;

    // Decode reader tuple.
    let v = FzValue(reader_bits);
    let rp = v.unbox_ptr().expect("read_field: reader is not a ptr");
    let bs_bits = unsafe { std::ptr::read((rp as *const u8).add(16) as *const u64) };
    let bit_len = (FzValue(unsafe {
        std::ptr::read((rp as *const u8).add(24) as *const u64)
    }))
    .unbox_int()
    .unwrap() as usize;
    let pos = (FzValue(unsafe {
        std::ptr::read((rp as *const u8).add(32) as *const u64)
    }))
    .unbox_int()
    .unwrap() as usize;

    // Bytes pointer from bs.
    let bs_v = FzValue(bs_bits);
    let bsp = bs_v.unbox_ptr().expect("read_field: reader bs not a ptr");
    let bs_header = unsafe { &*bsp };
    if HeapKind::from_u16(bs_header.kind) != Some(HeapKind::Bitstring) {
        panic!("read_field reader bs is not a Bitstring");
    }
    let bytes_ptr = unsafe { (bsp as *const u8).add(24) };
    let bytes = unsafe { std::slice::from_raw_parts(bytes_ptr, bit_len.div_ceil(8)) };

    // Failure path: alloc 1-tuple [false].
    let arity1 = current_process()
        .bs_tuple_arity1_schema
        .expect("bs_tuple_arity1_schema not set");
    let arity3 = current_process()
        .bs_tuple_arity3_schema
        .expect("bs_tuple_arity3_schema not set");
    let fail = || -> u64 {
        let p = current_process().heap.alloc_struct(arity1);
        unsafe {
            let base = (p as *mut u8).add(16);
            std::ptr::write(base as *mut u64, FzValue::FALSE.0);
        }
        p as u64
    };

    let mut r = crate::bitstr::BitReader { bytes, bit_len, pos };

    let (extracted_bits, consumed) = match ty {
        BitType::Integer => {
            let total = size.unwrap_or(8) * unit;
            if total > 64 { return fail(); }
            let raw = match r.read_bits(total as usize) {
                Some(v) => v,
                None => return fail(),
            };
            let raw = apply_endian_for_read(raw, total, endian);
            let n: i64 = if signed_b { sign_extend(raw, total) } else { raw as i64 };
            (FzValue::from_int(n).0, total as usize)
        }
        BitType::Binary | BitType::Bits => {
            let needed_bits = match (ty, size, is_last_b) {
                (BitType::Binary, None, true) | (BitType::Bits, None, true) => bit_len - pos,
                (BitType::Binary, None, false) => return fail(), // size required
                (BitType::Bits, None, false) => return fail(),
                (BitType::Binary, Some(n), _) => (n * unit) as usize,
                (BitType::Bits, Some(n), _) => (n * unit) as usize,
                _ => unreachable!(),
            };
            if pos + needed_bits > bit_len { return fail(); }
            // Build a fresh Bitstring from the slice. Always copy for v1
            // (zero-copy slicing deferred — see ticket "Open").
            let mut sub_bytes = Vec::with_capacity(needed_bits.div_ceil(8));
            let mut w = crate::bitstr::BitWriter::new();
            for _ in 0..needed_bits {
                w.append_bit(r.read_bit().unwrap());
            }
            sub_bytes.extend_from_slice(&w.bytes);
            let new_bs = current_process()
                .heap
                .alloc_bitstring(&sub_bytes, needed_bits as u64);
            let new_bs_bits = new_bs as u64;
            (new_bs_bits, needed_bits)
        }
        BitType::Float => {
            let total = size.unwrap_or(64) * unit;
            if total != 32 && total != 64 {
                return fail();
            }
            let raw = match r.read_bits(total as usize) {
                Some(v) => v,
                None => return fail(),
            };
            let raw = apply_endian_for_read(raw, total, endian);
            let f = if total == 32 {
                f32::from_bits(raw as u32) as f64
            } else {
                f64::from_bits(raw)
            };
            let p = current_process().heap.alloc_float(f);
            (p as u64, total as usize)
        }
        BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => {
            // UTF: read uses crate::bitstr::decode_utf*; not exercised by
            // ticket tests, so panic to surface intent rather than partial.
            panic!(
                "BitReadField for {:?} not yet wired in JIT (lands with UTF support)",
                ty
            );
        }
    };

    // Allocate fresh reader tuple [bs_bits, bit_len_boxed, new_pos_boxed].
    let new_pos = (pos + consumed) as i64;
    let new_reader_p = current_process().heap.alloc_struct(arity3);
    unsafe {
        let base = (new_reader_p as *mut u8).add(16);
        std::ptr::write(base as *mut u64, bs_bits);
        std::ptr::write(base.add(8) as *mut u64, ((bit_len as u64) << 3) | 0b001);
        std::ptr::write(base.add(16) as *mut u64, ((new_pos as u64) << 3) | 0b001);
    }

    // Allocate result tuple [true, extracted, new_reader].
    let result_p = current_process().heap.alloc_struct(arity3);
    unsafe {
        let base = (result_p as *mut u8).add(16);
        std::ptr::write(base as *mut u64, FzValue::TRUE.0);
        std::ptr::write(base.add(8) as *mut u64, extracted_bits);
        std::ptr::write(base.add(16) as *mut u64, new_reader_p as u64);
    }
    result_p as u64
}

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
