//! A construction whose every segment is a whole number of bytes, built in
//! place.
//!
//! `fz_bs_build` is the definition of a construction: it sizes the segments,
//! allocates once and writes each segment once. When every segment starts on a
//! byte boundary and spans whole bytes, compiled code does the same work with
//! a few instructions and no call to the builder:
//!
//! 1. The total is the segments' fixed bytes plus the length of each unsized
//!    binary, read from its header word.
//! 2. A total of at most `SHARED_BIN_THRESHOLD_BYTES` is placed inline through
//!    `place_inline_bitstring`, the object `Heap::alloc_bitstring_with` makes.
//!    A larger one asks the runtime for a binary whose payload is unwritten
//!    (`fz_bs_alloc_unfilled`), because the runtime owns shared buffers.
//! 3. Each integer is stored at its offset, byte-swapped when its order is not
//!    the machine's, and each binary is copied with one `memcpy`.
//!
//! The result is placed before any binary's bytes are read. Placing only finds
//! room: no collection runs inside it, so a binary's address read afterwards is
//! the address it had before. Any other construction calls `fz_bs_build`.
//!
//! A construction that starts with an unsized binary is an append. The runtime
//! writes into a view's own buffer when it has room, where an inline copy would
//! copy a growing accumulator whole at every step, so a leading view asks the
//! runtime for the longer binary (`fz_bs_append_unfilled`) and this code writes
//! the rest after the leading bytes. A leading inline binary is copied by
//! whichever side builds the result, so it is built here while the total fits
//! inline; a larger total asks the runtime, which gives the result room to grow
//! and so makes the next step an append in place.
//!
//! The segments a construction's contract check admits make the reads safe: an
//! unsized `binary` is a bitstring of whole bytes and a sized one is at least as
//! long as its size, so a header word gives the bytes to copy.

use super::binary_slice::bytes_address;
use super::clif::kind_field;
use super::place::place_inline_bitstring;
use super::prim::bit_len_of_header;
use super::recipe::constant_of;
use super::recipe::header_word;
use super::*;
use crate::ast::{BitType, Endian};
use crate::fz_ir::{BitFieldIr, BitSizeIr};
use cranelift_codegen::ir::{self, InstBuilder, MemFlagsData, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Linkage;
use fz_runtime::any_value::{BITSTRING_BYTES_OFFSET, ValueKind};
use fz_runtime::bits::BINVIEW_BYTES_PTR_OFFSET;
use fz_runtime::heap::SHARED_BIN_THRESHOLD_BYTES;
use fz_runtime::ir_runtime::{fz_bs_alloc_unfilled, fz_bs_append_unfilled, fz_bs_field_spec};

/// What a segment writes, when it is whole bytes at a whole-byte offset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum AlignedSegment {
    /// The low `bytes` bytes (1, 2, 4 or 8) of an integer, most significant
    /// byte first when `big_endian`.
    Integer { bytes: u8, big_endian: bool },
    /// The first `bytes` bytes of a binary, or all of it when `bytes` is
    /// `None`.
    Binary { bytes: Option<u64> },
}

/// The segment `field` writes, or `None` when it is not whole bytes of a kind
/// compiled code writes: a mid-byte size, a size read at run time, `bits`,
/// `float` and `utf`.
pub(super) fn aligned_segment(field: &BitFieldIr) -> Option<AlignedSegment> {
    let unit = u64::from(field.unit.unwrap_or(field.ty.default_unit()));
    let literal = match &field.size {
        None => None,
        Some(BitSizeIr::Literal(n)) => Some(u64::from(*n)),
        Some(BitSizeIr::Var(_) | BitSizeIr::ByteSizeOf(_)) => return None,
    };
    match field.ty {
        BitType::Integer => {
            let bits = literal.unwrap_or(8) * unit;
            let bytes = u8::try_from(bits / 8).ok().filter(|b| matches!(b, 1 | 2 | 4 | 8))?;
            (bits % 8 == 0).then_some(AlignedSegment::Integer {
                bytes,
                big_endian: wants_big_endian(field.endian),
            })
        }
        BitType::Binary => match literal {
            None => (unit % 8 == 0).then_some(AlignedSegment::Binary { bytes: None }),
            Some(n) => (n * unit % 8 == 0).then_some(AlignedSegment::Binary {
                bytes: Some(n * unit / 8),
            }),
        },
        BitType::Float | BitType::Bits | BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => None,
    }
}

/// Every field of a construction as a segment, or `None` when one is not.
pub(super) fn aligned_segments(fields: &[BitFieldIr]) -> Option<Vec<AlignedSegment>> {
    fields.iter().map(aligned_segment).collect()
}

/// Whether the first segment is a binary with no size, which makes the
/// construction an append to it.
pub(super) fn starts_with_unsized_binary(segments: &[AlignedSegment]) -> bool {
    matches!(segments.first(), Some(AlignedSegment::Binary { bytes: None }))
}

fn wants_big_endian(endian: Endian) -> bool {
    match endian {
        Endian::Big => true,
        Endian::Little => false,
        Endian::Native => cfg!(target_endian = "big"),
    }
}

/// The `fz_bs_field_spec` word a descriptor of `field` carries, whether or not
/// its size is written.
pub(super) fn descriptor_spec(field: &BitFieldIr, size_present: u32) -> u64 {
    fz_bs_field_spec(
        field.ty.runtime_tag(),
        size_present,
        field.unit.unwrap_or(field.ty.default_unit()),
        encode_endian(field.endian),
        0,
        0,
    )
}

/// The ref word of the binary the segments spell, built in place. `values`
/// pairs each segment with, an integer's raw word or a binary's ref word.
pub(super) fn emit_aligned_construction<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    segments: &[(AlignedSegment, ir::Value)],
) -> ir::Value {
    let total = total_bytes(body, segments);
    let (result, destination) = place_result(body, total);
    write_segments(body, Cursor::at(destination), segments);
    result
}

/// Write each segment at the cursor, one after another.
fn write_segments<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    mut cursor: Cursor,
    segments: &[(AlignedSegment, ir::Value)],
) {
    for &(segment, value) in segments {
        match segment {
            AlignedSegment::Integer { bytes, big_endian } => {
                store_integer(body, &cursor, value, bytes, big_endian);
                cursor.advance_fixed(u64::from(bytes));
            }
            AlignedSegment::Binary { bytes: Some(bytes) } => {
                let length = body.b.ins().iconst(types::I64, bytes as i64);
                copy_binary(body, &cursor, value, length);
                cursor.advance_fixed(bytes);
            }
            AlignedSegment::Binary { bytes: None } => {
                let length = binary_byte_len(body.b, value);
                copy_binary(body, &cursor, value, length);
                cursor.advance_dynamic(body.b, length);
            }
        }
    }
}

/// The ref word of the binary that starts with the unsized binary `segments[0]`
/// followed by the other segments: an append. Only the runtime extends a view in
/// place, so a leading view, and a total too large for an inline result, ask it
/// for the longer binary (`fz_bs_append_unfilled`) and write the rest after the
/// leading bytes. A leading inline binary with an inline total is copied as in
/// any other construction: it is at most `SHARED_BIN_THRESHOLD_BYTES`, and the
/// runtime would copy it too.
pub(super) fn emit_append<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    segments: &[(AlignedSegment, ir::Value)],
) -> ir::Value {
    let leading = segments[0].1;
    let kind = kind_field(body.b, leading);
    let is_view = body
        .b
        .ins()
        .icmp_imm_s(ir::condcodes::IntCC::Equal, kind, i64::from(ValueKind::BINVIEW.tag()));
    let total = total_bytes(body, segments);
    let large = body.b.ins().icmp_imm_u(
        ir::condcodes::IntCC::UnsignedGreaterThan,
        total,
        SHARED_BIN_THRESHOLD_BYTES as i64,
    );
    let by_runtime = body.b.ins().bor(is_view, large);
    let (extend, inline, done) = (body.b.create_block(), body.b.create_block(), body.b.create_block());
    body.b.append_block_param(done, types::I64);
    body.b.ins().brif(by_runtime, extend, &[], inline, &[]);

    body.b.switch_to_block(extend);
    body.b.seal_block(extend);
    let left_len = binary_byte_len(body.b, leading);
    let right_len = body.b.ins().isub(total, left_len);
    let process = body.process_arg();
    let result = runtime_call1!(body, fz_bs_append_unfilled, [process, leading, right_len]);
    let payload = bytes_address(body.b, result);
    let rest_at = body.b.ins().iadd(payload, left_len);
    write_segments(body, Cursor::at(rest_at), &segments[1..]);
    body.b.ins().jump(done, &[result.into()]);

    body.b.switch_to_block(inline);
    body.b.seal_block(inline);
    let built = emit_aligned_construction(body, segments);
    body.b.ins().jump(done, &[built.into()]);

    body.b.switch_to_block(done);
    body.b.seal_block(done);
    body.b.block_params(done)[0]
}

/// The bytes the segments add up to: a constant when no binary is unsized.
fn total_bytes<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    segments: &[(AlignedSegment, ir::Value)],
) -> ir::Value {
    let mut fixed = 0u64;
    let mut unsized_lengths = Vec::new();
    for &(segment, value) in segments {
        match segment {
            AlignedSegment::Integer { bytes, .. } => fixed += u64::from(bytes),
            AlignedSegment::Binary { bytes: Some(bytes) } => fixed += bytes,
            AlignedSegment::Binary { bytes: None } => unsized_lengths.push(binary_byte_len(body.b, value)),
        }
    }
    let Some((&first, rest)) = unsized_lengths.split_first() else {
        return body.b.ins().iconst(types::I64, fixed as i64);
    };
    let mut total = first;
    for &length in rest {
        total = body.b.ins().iadd(total, length);
    }
    if fixed == 0 {
        total
    } else {
        body.b.ins().iadd_imm_s(total, fixed as i64)
    }
}

/// The bytes of the binary `word` names: its header's bit length, divided by 8.
fn binary_byte_len(b: &mut FunctionBuilder<'_>, word: ir::Value) -> ir::Value {
    let header = header_word(b, word);
    let bits = bit_len_of_header(b, header);
    b.ins().ushr_imm_u(bits, 3)
}

/// The result's ref word and the address of its first payload byte, for a
/// result of `total` bytes: placed inline when it is at most the sharing
/// threshold, else asked of the runtime. A total known now chooses at emit
/// time.
fn place_result<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    total: ir::Value,
) -> (ir::Value, ir::Value) {
    match constant_of(body.b, total) {
        Some(known) if known as usize <= SHARED_BIN_THRESHOLD_BYTES => place_inline(body, total),
        Some(_) => place_shared(body, total),
        None => {
            let inline = body.b.create_block();
            let shared = body.b.create_block();
            let done = body.b.create_block();
            body.b.append_block_param(done, types::I64);
            body.b.append_block_param(done, types::I64);
            let small = body.b.ins().icmp_imm_u(
                ir::condcodes::IntCC::UnsignedLessThanOrEqual,
                total,
                SHARED_BIN_THRESHOLD_BYTES as i64,
            );
            body.b.ins().brif(small, inline, &[], shared, &[]);
            body.b.switch_to_block(inline);
            body.b.seal_block(inline);
            let (result, destination) = place_inline(body, total);
            body.b.ins().jump(done, &[result.into(), destination.into()]);
            body.b.switch_to_block(shared);
            body.b.seal_block(shared);
            let (result, destination) = place_shared(body, total);
            body.b.ins().jump(done, &[result.into(), destination.into()]);
            body.b.switch_to_block(done);
            body.b.seal_block(done);
            let params = body.b.block_params(done);
            (params[0], params[1])
        }
    }
}

fn place_inline<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    total: ir::Value,
) -> (ir::Value, ir::Value) {
    let address = place_inline_bitstring(body, total, 0);
    let result = body.heap_ref_word_from_addr(address, ValueKind::BITSTRING);
    let payload = body.b.ins().iadd_imm_s(address, BITSTRING_BYTES_OFFSET as i64);
    (result, payload)
}

fn place_shared<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    total: ir::Value,
) -> (ir::Value, ir::Value) {
    let process = body.process_arg();
    let result = runtime_call1!(body, fz_bs_alloc_unfilled, [process, total]);
    let view = address_field(body.b, result);
    let payload = body.b.ins().load(
        types::I64,
        MemFlagsData::trusted(),
        view,
        BINVIEW_BYTES_PTR_OFFSET as i32,
    );
    (result, payload)
}

/// Where the next segment goes: `base` plus a constant. A binary of a length
/// known only at run time moves the base.
struct Cursor {
    base: ir::Value,
    offset: u64,
}

impl Cursor {
    fn at(base: ir::Value) -> Self {
        Self { base, offset: 0 }
    }

    fn advance_fixed(&mut self, bytes: u64) {
        self.offset += bytes;
    }

    fn advance_dynamic(&mut self, b: &mut FunctionBuilder<'_>, bytes: ir::Value) {
        let here = b.ins().iadd_imm_s(self.base, self.offset as i64);
        self.base = b.ins().iadd(here, bytes);
        self.offset = 0;
    }

    fn address<M: cranelift_module::Module>(&self, body: &mut CodegenFn<'_, '_, M>) -> ir::Value {
        if self.offset == 0 {
            self.base
        } else {
            body.b.ins().iadd_imm_s(self.base, self.offset as i64)
        }
    }
}

fn store_integer<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    cursor: &Cursor,
    value: ir::Value,
    bytes: u8,
    big_endian: bool,
) {
    let ty = match bytes {
        1 => types::I8,
        2 => types::I16,
        4 => types::I32,
        _ => types::I64,
    };
    let narrow = if ty == types::I64 {
        value
    } else {
        body.b.ins().ireduce(ty, value)
    };
    let swapped = big_endian != cfg!(target_endian = "big");
    let word = if swapped && bytes > 1 {
        body.b.ins().bswap(narrow)
    } else {
        narrow
    };
    body.b
        .ins()
        .store(MemFlagsData::new(), word, cursor.base, cursor.offset as i32);
}

/// Copy `length` bytes of the binary `source` to the cursor, with one `memcpy`.
fn copy_binary<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    cursor: &Cursor,
    source: ir::Value,
    length: ir::Value,
) {
    if constant_of(body.b, length) == Some(0) {
        return;
    }
    let from = bytes_address(body.b, source);
    let to = cursor.address(body);
    let mut signature = body.jmod.make_signature();
    signature.params = vec![ir::AbiParam::new(types::I64); 3];
    signature.returns = vec![ir::AbiParam::new(types::I64)];
    let id = body
        .jmod
        .declare_function("memcpy", Linkage::Import, &signature)
        .unwrap_or_else(|error| panic!("declare memcpy: {error}"));
    let callee = body.func_ref(id);
    body.b.ins().call(callee, &[to, from, length]);
}

#[cfg(test)]
#[path = "construction_test.rs"]
mod construction_test;
