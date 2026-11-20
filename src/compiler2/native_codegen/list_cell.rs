//! A list cell written in place.
//!
//! A cell is two words: the head's payload, and a link word holding the tail's
//! address with the head's kind in the bits a ref word keeps its kind in.
//! Compiled code places the cell with `emit_place` and writes both words
//! itself; the runtime is asked only to share a list or struct head, which
//! the cell's holder may not write through again.
//!
//! The rows of the recipe table that name `fz_list_cons_*` are emitted here,
//! one per way the head reaches the cell:
//!
//! - an int, a float or an atom is a scalar the call site already holds
//!   unboxed. The cell's kind is a constant and nothing needs sharing.
//! - a ref word is decoded as `AnyValue::from_ref` decodes it: a boxed scalar
//!   (int, float, reference) is read from its box, any other word is its
//!   payload. The kind is the word's own. A list or struct head is shared by
//!   the runtime before the cell is placed.
//!
//! A new cell carries no alias bit: only a second holder sets one.

use super::place::emit_place;
use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlagsData, types};
use cranelift_frontend::FunctionBuilder;
use fz_runtime::any_value::{AnyValueRefPacking, ValueKind};
use fz_runtime::heap::HeapAllocKind;

/// How a cell's head reaches it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HeadLane {
    Int,
    Float,
    Atom,
    Ref,
}

/// A cell is one 16-byte object.
const CELL_BYTES: usize = 16;

/// The head as the cell stores it: its payload word and its kind.
pub(super) struct Head {
    pub(super) raw: ir::Value,
    pub(super) kind: HeadKind,
}

#[derive(Clone, Copy)]
pub(super) enum HeadKind {
    Known(ValueKind),
    Read(ir::Value),
}

/// Place a cell whose head is `args[1]` and whose tail is the list ref
/// `args[2]`, and answer its ref word. `args[0]` is the process, which
/// `emit_place` reads from the pinned register.
pub(super) fn emit_list_cell<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    lane: HeadLane,
    args: &[ir::Value],
) -> ir::Value {
    let &[_process, head, tail] = args else {
        panic!(
            "a list cell row takes a process, a head and a tail, got {} arguments",
            args.len()
        );
    };
    let head = match lane {
        HeadLane::Int => Head::known(head, ValueKind::INT),
        HeadLane::Float => {
            let bits = body.b.ins().bitcast(types::I64, MemFlagsData::new(), head);
            Head::known(bits, ValueKind::FLOAT)
        }
        HeadLane::Atom => Head::known(head, ValueKind::ATOM),
        HeadLane::Ref => {
            body.share(CodegenValue::AnyRef(head));
            decode(body, head)
        }
    };
    let tail_address = address_field(body.b, tail);
    place_cell(body, &head, tail_address)
}

/// The link word a cell holds: the tail's address with the head's kind above it.
pub(super) fn link_word<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    head: &Head,
    tail_address: ir::Value,
) -> ir::Value {
    match head.kind {
        HeadKind::Known(kind) => {
            let kind_bits = (u64::from(kind.tag()) << AnyValueRefPacking::current().tag_shift()) as i64;
            body.b.ins().bor_imm_u(tail_address, kind_bits)
        }
        HeadKind::Read(kind) => {
            let kind_bits = body
                .b
                .ins()
                .ishl_imm_u(kind, i64::from(AnyValueRefPacking::current().tag_shift()));
            body.b.ins().bor(tail_address, kind_bits)
        }
    }
}

/// Place a cell holding `head`, which is already shared, over the tail at
/// `tail_address`, and answer its ref word.
pub(super) fn place_cell<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    head: &Head,
    tail_address: ir::Value,
) -> ir::Value {
    let link = link_word(body, head, tail_address);
    let address = emit_place(body, HeapAllocKind::ListCons, CELL_BYTES);
    let flags = MemFlagsData::trusted();
    body.b.ins().store(flags, head.raw, address, 0);
    body.b.ins().store(flags, link, address, 8);
    body.heap_ref_word_from_addr(address, ValueKind::LIST)
}

impl Head {
    pub(super) fn known(raw: ir::Value, kind: ValueKind) -> Self {
        Self {
            raw,
            kind: HeadKind::Known(kind),
        }
    }
}

/// The head a ref word names, as a cell stores it.
pub(super) fn decode<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>, head_ref: ir::Value) -> Head {
    let kind = kind_field(body.b, head_ref);
    let raw = payload_of(body, head_ref, kind);
    Head {
        raw,
        kind: HeadKind::Read(kind),
    }
}

/// The payload word a container stores for the value `word` names: what a
/// boxed scalar's box holds, and for any other kind the word's address field
/// with its literal bit.
pub(crate) fn payload_of<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    word: ir::Value,
    kind: ir::Value,
) -> ir::Value {
    let boxed = kind_is_one_of(body.b, kind, ValueKind::is_boxed_scalar);
    let in_box = body.b.create_block();
    let in_word = body.b.create_block();
    let joined = body.b.create_block();
    body.b.append_block_param(joined, types::I64);
    body.b.ins().brif(boxed, in_box, &[], in_word, &[]);

    body.b.switch_to_block(in_box);
    body.b.seal_block(in_box);
    let box_address = address_field(body.b, word);
    let stored = body.b.ins().load(types::I64, MemFlagsData::trusted(), box_address, 0);
    body.b.ins().jump(joined, &[BlockArg::Value(stored)]);

    body.b.switch_to_block(in_word);
    body.b.seal_block(in_word);
    let payload = payload_field(body.b, word);
    body.b.ins().jump(joined, &[BlockArg::Value(payload)]);

    body.b.switch_to_block(joined);
    body.b.seal_block(joined);
    body.b.block_params(joined)[0]
}

/// An `I8` condition: whether the kind value `kind` is one `member` admits.
/// One bit of a constant mask is read by shifting it down by the kind.
fn kind_is_one_of(b: &mut FunctionBuilder<'_>, kind: ir::Value, member: impl Fn(ValueKind) -> bool) -> ir::Value {
    let mask: u64 = (0..=u8::MAX)
        .filter_map(ValueKind::new)
        .filter(|kind| member(*kind))
        .fold(0, |mask, kind| mask | 1 << kind.tag());
    let mask = b.ins().iconst(types::I64, mask as i64);
    let bit = b.ins().ushr(mask, kind);
    b.ins().band_imm_u(bit, 1)
}
