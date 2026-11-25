//! Where an inline allocation gets its room.
//!
//! Compiled code places an object by bumping the heap's tip: load `bump_top`
//! and `block_end`, add the size, compare, store the new top. A tip with no
//! room sends the code to one cold block, which calls the runtime's
//! `fz_heap_room` and gets back an address; both paths join at one `placed`
//! block, so each kind writes its object once, after the join. The runtime
//! only finds room and writes nothing into the object.
//!
//! The process register is read afresh in each block that uses it, as the
//! pinned register is a copy that costs one move. A value held across the
//! cold call would have to live in a register the call's argument and result
//! also claim; read per block, the address is in the call's result register
//! on both paths and the join needs no move.
//!
//! `emit_place` is the one emitter of that bump. Every inline allocation site
//! places through it, and it counts the site after the join, so a placement
//! the runtime made room for is counted by the same site as one the tip took.
//!
//! `place_inline_bitstring` places the object `Heap::alloc_bitstring_with`
//! makes for a payload of up to the sharing threshold: the header, the payload
//! the caller writes, and zeros after it. Its size is one of five classes, so
//! a length known when the code is emitted places one object and any other
//! length chooses among them.

use super::recipe::constant_of;
use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlagsData, condcodes::IntCC, types};
use fz_runtime::alloc_site::AllocSite;
use fz_runtime::any_value::{BITSTRING_BIT_LEN_SHIFT, BITSTRING_BYTES_OFFSET, bitstring_size_for_bit_len};
use fz_runtime::heap::{HeapAllocKind, INLINE_ALLOC_LAYOUT, SHARED_BIN_THRESHOLD_BYTES};
use fz_runtime::ir_runtime::fz_heap_room;
use fz_runtime::process_abi::PROCESS_HEAP_OFFSET;

/// Place `size` bytes (a multiple of 16) on the heap and answer the address
/// the object starts at. The caller writes every word of the object.
pub(super) fn emit_place<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    kind: HeapAllocKind,
    size: usize,
) -> ir::Value {
    let layout = INLINE_ALLOC_LAYOUT;
    let flags = MemFlagsData::trusted();
    let field = |offset: usize| PROCESS_HEAP_OFFSET + offset as i32;
    let process = body.process_arg();
    let top = body.b.ins().load(types::I64, flags, process, field(layout.bump_top));
    let end = body.b.ins().load(types::I64, flags, process, field(layout.block_end));
    let new_top = body.b.ins().iadd_imm_s(top, size as i64);
    let fits = body.b.ins().icmp(IntCC::UnsignedLessThanOrEqual, new_top, end);
    let inline = body.b.create_block();
    let room = body.b.create_block();
    let placed = body.b.create_block();
    body.b.append_block_param(placed, types::I64);
    body.b.ins().brif(fits, inline, &[], room, &[]);

    body.b.switch_to_block(room);
    body.b.seal_block(room);
    body.b.set_cold_block(room);
    let process = body.process_arg();
    let bytes = body.b.ins().iconst(types::I64, size as i64);
    let from_runtime = runtime_call1!(body, fz_heap_room, [process, bytes]);
    body.b.ins().jump(placed, &[from_runtime.into()]);

    body.b.switch_to_block(inline);
    body.b.seal_block(inline);
    let process = body.process_arg();
    body.b.ins().store(flags, new_top, process, field(layout.bump_top));
    body.b.ins().jump(placed, &[top.into()]);

    body.b.switch_to_block(placed);
    body.b.seal_block(placed);
    let scope = body.scope;
    scope.sites.borrow_mut().count_alloc(
        body,
        AllocSite {
            kind,
            bytes: size as u32,
            function: scope.function.to_owned(),
        },
    );
    body.b.block_params(placed)[0]
}

const WORD: usize = 8;

/// The sizes of an inline bitstring of 0 to `SHARED_BIN_THRESHOLD_BYTES`
/// bytes, in 16-byte units.
const SIZE_CLASSES: usize = bitstring_size_for_bit_len(SHARED_BIN_THRESHOLD_BYTES as u64 * 8) / 16;

/// Place the inline bitstring of `byte_len` whole bytes, at most
/// `SHARED_BIN_THRESHOLD_BYTES`, and answer its address. The header is written
/// and every word after the payload that the caller does not write is zeroed;
/// the caller writes the `byte_len` payload bytes at `BITSTRING_BYTES_OFFSET`
/// and nothing else. `written_words` is how many words from the payload's start
/// the caller stores whole (a last word holding fewer than eight payload bytes
/// counts when the caller stores it zero-padded), and those are not zeroed.
pub(super) fn place_inline_bitstring<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    byte_len: ir::Value,
    written_words: usize,
) -> ir::Value {
    let flags = MemFlagsData::trusted();
    let header_shift = i64::from(BITSTRING_BIT_LEN_SHIFT) + 3;
    if let Some(known) = constant_of(body.b, byte_len) {
        let known = known as u64;
        let address = place_zeroed(body, bitstring_size_for_bit_len(known * 8), written_words);
        let header = body.b.ins().iconst(types::I64, (known << header_shift) as i64);
        body.b.ins().store(flags, header, address, 0);
        return address;
    }
    let filled = body.b.create_block();
    body.b.append_block_param(filled, types::I64);
    for index in 0..SIZE_CLASSES {
        let size = (index + 1) * 16;
        if index + 1 < SIZE_CLASSES {
            let largest_bytes = size - BITSTRING_BYTES_OFFSET - 1;
            let fits = body
                .b
                .ins()
                .icmp_imm_u(IntCC::UnsignedLessThanOrEqual, byte_len, largest_bytes as i64);
            let class = body.b.create_block();
            let next = body.b.create_block();
            body.b.ins().brif(fits, class, &[], next, &[]);
            body.b.switch_to_block(class);
            body.b.seal_block(class);
            let address = place_zeroed(body, size, written_words);
            body.b.ins().jump(filled, &[BlockArg::Value(address)]);
            body.b.switch_to_block(next);
            body.b.seal_block(next);
        } else {
            let address = place_zeroed(body, size, written_words);
            body.b.ins().jump(filled, &[BlockArg::Value(address)]);
        }
    }
    body.b.switch_to_block(filled);
    body.b.seal_block(filled);
    let address = body.b.block_params(filled)[0];
    let header = body.b.ins().ishl_imm_u(byte_len, header_shift);
    body.b.ins().store(flags, header, address, 0);
    address
}

/// Place a bitstring object of `size` bytes and zero the last two words, which
/// hold every byte after the payload, except the header (the caller writes it)
/// and the first `written_words` words after it (the caller writes those).
fn place_zeroed<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    size: usize,
    written_words: usize,
) -> ir::Value {
    let address = emit_place(body, HeapAllocKind::Bitstring, size);
    let zero = body.b.ins().iconst(types::I64, 0);
    let flags = MemFlagsData::trusted();
    for word in [size / WORD - 2, size / WORD - 1] {
        if word > written_words {
            body.b.ins().store(flags, zero, address, (word * WORD) as i32);
        }
    }
    address
}

#[cfg(test)]
#[path = "place_test.rs"]
mod place_test;
