//! A proven window of a binary, sliced in place when it is a small copy.
//!
//! The row's runtime function, `fz_bs_slice_ref`, takes the process, a binary
//! and a window the caller has proved lies inside it, and answers what
//! `Heap::slice` makes of that window: the source itself when the window is all
//! of it, a view of its buffer when the window is byte-aligned and longer than
//! the shared-binary threshold, and otherwise a copy.
//!
//! Compiled code places the copy itself when the window is whole bytes
//! starting on a byte boundary, is at most the threshold long, and is not the
//! whole source. It places an inline bitstring through `emit_place`, writes the
//! header, copies the bytes and zeroes the padding after them, which is the
//! object `Heap::alloc_bitstring` writes. A window of a length known when the
//! code is emitted is a straight run of loads and stores, with the object's size
//! a constant. Any other length places one of the five sizes a copy of at most
//! the threshold can have, and copies in a loop. Every other window is the call,
//! on a cold path.

use super::place::emit_place;
use super::prim::bit_len_of_header;
use super::recipe::{constant_of, header_word};
use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlagsData, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use fz_runtime::any_value::{BITSTRING_BIT_LEN_SHIFT, BITSTRING_BYTES_OFFSET, ValueKind, bitstring_size_for_bit_len};
use fz_runtime::bits::BINVIEW_BYTES_PTR_OFFSET;
use fz_runtime::heap::{HeapAllocKind, SHARED_BIN_THRESHOLD_BYTES};
use fz_runtime::ir_runtime::fz_bs_slice_ref;

const WORD: usize = 8;

/// The bits of the longest window that is copied.
const MAX_COPY_BITS: u64 = SHARED_BIN_THRESHOLD_BYTES as u64 * 8;

/// The sizes of an inline bitstring of 0 to `SHARED_BIN_THRESHOLD_BYTES`
/// bytes, in 16-byte units.
const SIZE_CLASSES: usize = bitstring_size_for_bit_len(MAX_COPY_BITS) / 16;

/// The binary `args[1]` windowed from bit `args[2]` for `args[3]` bits. The
/// process is `args[0]`, which `emit_place` reads from the pinned register.
pub(super) fn emit_binary_slice<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    args: &[ir::Value],
) -> ir::Value {
    let &[_process, source, pos, bit_len] = args else {
        panic!("a binary slice row takes 4 arguments, got {}", args.len());
    };
    let known_len = constant_of(body.b, bit_len).map(|bits| bits as u64);
    if known_len.is_some_and(|bits| bits % 8 != 0 || bits > MAX_COPY_BITS) {
        return call_slice(body, args);
    }
    let (copy, call, done) = (body.b.create_block(), body.b.create_block(), body.b.create_block());
    body.b.append_block_param(done, types::I64);

    let header = header_word(body.b, source);
    let source_bits = bit_len_of_header(body.b, header);
    let is_whole = window_is_whole_source(body.b, pos, bit_len, source_bits);
    let on_boundary = whole_bytes_from_a_boundary(body.b, pos, bit_len, known_len.is_some());
    let small = known_len.is_none().then(|| {
        body.b
            .ins()
            .icmp_imm_u(IntCC::UnsignedLessThanOrEqual, bit_len, MAX_COPY_BITS as i64)
    });
    let mut copies = body.b.ins().band_not(on_boundary, is_whole);
    if let Some(small) = small {
        copies = body.b.ins().band(copies, small);
    }
    body.b.ins().brif(copies, copy, &[], call, &[]);

    body.b.switch_to_block(call);
    body.b.seal_block(call);
    body.b.set_cold_block(call);
    let called = call_slice(body, args);
    body.b.ins().jump(done, &[BlockArg::Value(called)]);

    body.b.switch_to_block(copy);
    body.b.seal_block(copy);
    let bytes = bytes_address(body.b, source);
    let first_byte = body.b.ins().ushr_imm_u(pos, 3);
    let from = body.b.ins().iadd(bytes, first_byte);
    let copied = match known_len {
        Some(bits) => place_known(body, from, bits as usize / 8),
        None => place_unknown(body, from, bit_len),
    };
    body.b.ins().jump(done, &[BlockArg::Value(copied)]);

    body.b.switch_to_block(done);
    body.b.seal_block(done);
    body.b.block_params(done)[0]
}

fn call_slice<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>, args: &[ir::Value]) -> ir::Value {
    let &[process, source, pos, bit_len] = args else {
        unreachable!("a binary slice row takes 4 arguments");
    };
    let call = runtime_call!(body, fz_bs_slice_ref, [process, source, pos, bit_len]);
    body.sole_result(call)
}

/// Whether the window starts at the first bit of the source and spans all of it.
fn window_is_whole_source(
    b: &mut FunctionBuilder<'_>,
    pos: ir::Value,
    bit_len: ir::Value,
    source_bits: ir::Value,
) -> ir::Value {
    let differing = b.ins().bxor(bit_len, source_bits);
    let not_whole = b.ins().bor(pos, differing);
    b.ins().icmp_imm_s(IntCC::Equal, not_whole, 0)
}

/// Whether the window starts on a byte boundary and, when its length is not a
/// constant, is a whole number of bytes. A constant length is checked when the
/// code is emitted.
fn whole_bytes_from_a_boundary(
    b: &mut FunctionBuilder<'_>,
    pos: ir::Value,
    bit_len: ir::Value,
    length_is_constant: bool,
) -> ir::Value {
    let misaligned = if length_is_constant {
        pos
    } else {
        b.ins().bor(pos, bit_len)
    };
    let low_bits = b.ins().band_imm_u(misaligned, 7);
    b.ins().icmp_imm_s(IntCC::Equal, low_bits, 0)
}

/// The address of the first byte of the binary `source` names: the bytes that
/// follow an inline bitstring's header, or the pointer a view holds in its
/// second word. Both words are read, so no branch picks one; the second word
/// of an inline bitstring is its first bytes or padding, inside the object.
fn bytes_address(b: &mut FunctionBuilder<'_>, source: ir::Value) -> ir::Value {
    const _: () = assert!(BITSTRING_BYTES_OFFSET == BINVIEW_BYTES_PTR_OFFSET);
    let object = address_field(b, source);
    let kind = kind_field(b, source);
    let is_view = b
        .ins()
        .icmp_imm_s(IntCC::Equal, kind, i64::from(ValueKind::BINVIEW.tag()));
    let viewed = b.ins().load(
        types::I64,
        MemFlagsData::trusted(),
        object,
        BINVIEW_BYTES_PTR_OFFSET as i32,
    );
    let inline = b.ins().iadd_imm_s(object, BITSTRING_BYTES_OFFSET as i64);
    b.ins().select(is_view, viewed, inline)
}

/// Place a copy of the `byte_len` bytes at `from`, a length known now: the
/// object's words are built and stored straight.
fn place_known<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    from: ir::Value,
    byte_len: usize,
) -> ir::Value {
    let size = bitstring_size_for_bit_len(byte_len as u64 * 8);
    let address = emit_place(body, HeapAllocKind::Bitstring, size);
    let flags = MemFlagsData::trusted();
    let header = body
        .b
        .ins()
        .iconst(types::I64, ((byte_len as u64 * 8) << BITSTRING_BIT_LEN_SHIFT) as i64);
    body.b.ins().store(flags, header, address, 0);
    let (whole_words, tail_bytes) = (byte_len / WORD, byte_len % WORD);
    let zero = body.b.ins().iconst(types::I64, 0);
    for word in 0..size / WORD - 1 {
        let value = if word < whole_words {
            body.b
                .ins()
                .load(types::I64, MemFlagsData::new(), from, (word * WORD) as i32)
        } else if word == whole_words && tail_bytes > 0 {
            tail_word(body.b, from, word * WORD, tail_bytes)
        } else {
            zero
        };
        body.b.ins().store(flags, value, address, ((word + 1) * WORD) as i32);
    }
    body.heap_ref_word_from_addr(address, ValueKind::BITSTRING)
}

/// The `bytes` (1 to 7) bytes at `from + offset` as the low bytes of a word,
/// first byte lowest, as a little-endian load of them all would give.
fn tail_word(b: &mut FunctionBuilder<'_>, from: ir::Value, offset: usize, bytes: usize) -> ir::Value {
    let mut word = None;
    let mut at = 0;
    while at < bytes {
        let (ty, width) = match bytes - at {
            4.. => (types::I32, 4),
            2..=3 => (types::I16, 2),
            _ => (types::I8, 1),
        };
        let loaded = b.ins().load(ty, MemFlagsData::new(), from, (offset + at) as i32);
        let wide = b.ins().uextend(types::I64, loaded);
        word = Some(match word {
            None => wide,
            Some(low) => {
                let shifted = b.ins().ishl_imm_u(wide, at as i64 * 8);
                b.ins().bor(low, shifted)
            }
        });
        at += width;
    }
    word.expect("a tail has at least one byte")
}

/// Place a copy of the `bit_len / 8` bytes at `from`, a length known only when
/// the code runs, no more than the threshold. The size of the object is one of
/// `SIZE_CLASSES`; each class places its own object and the bytes are copied
/// after the join.
fn place_unknown<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    from: ir::Value,
    bit_len: ir::Value,
) -> ir::Value {
    let byte_len = body.b.ins().ushr_imm_u(bit_len, 3);
    let filled = body.b.create_block();
    body.b.append_block_param(filled, types::I64);
    let class_blocks: Vec<ir::Block> = (0..SIZE_CLASSES).map(|_| body.b.create_block()).collect();
    for (index, &class) in class_blocks.iter().enumerate() {
        let next = if index + 1 < SIZE_CLASSES {
            body.b.create_block()
        } else {
            class
        };
        if index + 1 < SIZE_CLASSES {
            let largest_bytes = (index + 1) * 16 - BITSTRING_BYTES_OFFSET - 1;
            let fits = body
                .b
                .ins()
                .icmp_imm_u(IntCC::UnsignedLessThanOrEqual, byte_len, largest_bytes as i64);
            body.b.ins().brif(fits, class, &[], next, &[]);
        } else {
            body.b.ins().jump(class, &[]);
        }
        body.b.switch_to_block(class);
        body.b.seal_block(class);
        let size = (index + 1) * 16;
        let address = emit_place(body, HeapAllocKind::Bitstring, size);
        let zero = body.b.ins().iconst(types::I64, 0);
        let flags = MemFlagsData::trusted();
        body.b.ins().store(flags, zero, address, (size - 2 * WORD) as i32);
        body.b.ins().store(flags, zero, address, (size - WORD) as i32);
        body.b.ins().jump(filled, &[BlockArg::Value(address)]);
        if next != class {
            body.b.switch_to_block(next);
            body.b.seal_block(next);
        }
    }
    body.b.switch_to_block(filled);
    body.b.seal_block(filled);
    let address = body.b.block_params(filled)[0];
    let header = body.b.ins().ishl_imm_u(bit_len, i64::from(BITSTRING_BIT_LEN_SHIFT));
    body.b.ins().store(MemFlagsData::trusted(), header, address, 0);
    let to = body.b.ins().iadd_imm_s(address, BITSTRING_BYTES_OFFSET as i64);
    copy_bytes(body.b, to, from, byte_len);
    body.heap_ref_word_from_addr(address, ValueKind::BITSTRING)
}

/// Copy `len` bytes from `from` to `to`: eight at a time while eight remain,
/// then one at a time.
fn copy_bytes(b: &mut FunctionBuilder<'_>, to: ir::Value, from: ir::Value, len: ir::Value) {
    let zero = b.ins().iconst(types::I64, 0);
    let words = b.create_block();
    let words_body = b.create_block();
    let bytes = b.create_block();
    let bytes_body = b.create_block();
    let done = b.create_block();
    for block in [words, bytes] {
        b.append_block_param(block, types::I64);
    }
    b.ins().jump(words, &[BlockArg::Value(zero)]);

    b.switch_to_block(words);
    let at = b.block_params(words)[0];
    let after = b.ins().iadd_imm_s(at, WORD as i64);
    let room = b.ins().icmp(IntCC::UnsignedLessThanOrEqual, after, len);
    b.ins().brif(room, words_body, &[], bytes, &[BlockArg::Value(at)]);

    b.switch_to_block(words_body);
    b.seal_block(words_body);
    let source_word = b.ins().iadd(from, at);
    let word = b.ins().load(types::I64, MemFlagsData::new(), source_word, 0);
    let target_word = b.ins().iadd(to, at);
    b.ins().store(MemFlagsData::new(), word, target_word, 0);
    b.ins().jump(words, &[BlockArg::Value(after)]);
    b.seal_block(words);

    b.switch_to_block(bytes);
    let at = b.block_params(bytes)[0];
    let more = b.ins().icmp(IntCC::UnsignedLessThan, at, len);
    b.ins().brif(more, bytes_body, &[], done, &[]);

    b.switch_to_block(bytes_body);
    b.seal_block(bytes_body);
    let source_byte = b.ins().iadd(from, at);
    let byte = b.ins().load(types::I8, MemFlagsData::new(), source_byte, 0);
    let target_byte = b.ins().iadd(to, at);
    b.ins().store(MemFlagsData::new(), byte, target_byte, 0);
    let next = b.ins().iadd_imm_s(at, 1);
    b.ins().jump(bytes, &[BlockArg::Value(next)]);
    b.seal_block(bytes);

    b.switch_to_block(done);
    b.seal_block(done);
}
