//! A list cell written in place.
//!
//! A cell is two words: the head's payload, and a link word holding the tail's
//! address with the head's kind in the bits a ref word keeps its kind in.
//! Compiled code places the cell with `emit_place` and writes both words
//! itself; the runtime is asked only to share a list or struct head, which
//! the cell's holder may not write through again.
//!
//! The tail reaches a row as its stored word and kind, as every entry takes
//! a value, and an inline row is for a tail whose kind is the constant `LIST`:
//! the word is then the address of the next cell, 0 for `[]`. A tail of any
//! other kind ends the list in a terminator cell, which only the runtime
//! entry places; compiled code calls that entry for any tail its type does
//! not prove a list.
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
use super::recipe::constant_of;
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

/// Place a cell whose head is `args[1]` and whose tail is the list at the
/// address `args[2]`, and answer its ref word. `args[3]` is the tail's kind,
/// a constant `LIST`. `args[0]` is the process, which `emit_place` reads from
/// the pinned register.
pub(super) fn emit_list_cell<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    lane: HeadLane,
    args: &[ir::Value],
) -> ir::Value {
    let &[_process, head, tail_address, tail_kind] = args else {
        panic!(
            "a list cell row takes a process, a head and a tail word and kind, got {} arguments",
            args.len()
        );
    };
    assert_tail_is_list(body, tail_kind);
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
    place_cell(body, &head, tail_address)
}

/// An inline row links a list. A tail of another kind is the runtime's to
/// place, so a row asked for one is a bug at the call site.
pub(super) fn assert_tail_is_list<M: cranelift_module::Module>(body: &CodegenFn<'_, '_, M>, tail_kind: ir::Value) {
    let kind = constant_of(body.b, tail_kind);
    assert_eq!(
        kind,
        Some(i64::from(ValueKind::LIST.tag())),
        "an inline list row takes a tail whose kind is the constant LIST"
    );
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
    let [raw, kind] = stored_parts_of_ref(body.b, head_ref);
    Head {
        raw,
        kind: HeadKind::Read(kind),
    }
}

/// The word a container stores for the value `word` names, and its kind, as
/// two `I64`s read at run time.
pub(crate) fn stored_parts_of_ref(b: &mut FunctionBuilder<'_>, word: ir::Value) -> [ir::Value; 2] {
    let kind = kind_field(b, word);
    [payload_of(b, word, kind), kind]
}

/// The payload word a container stores for the value `word` names: what a
/// boxed scalar's box holds, and for any other kind the word's address field
/// with its literal bit.
fn payload_of(b: &mut FunctionBuilder<'_>, word: ir::Value, kind: ir::Value) -> ir::Value {
    let boxed = kind_is_one_of(b, kind, ValueKind::is_boxed_scalar);
    let in_box = b.create_block();
    let in_word = b.create_block();
    let joined = b.create_block();
    b.append_block_param(joined, types::I64);
    b.ins().brif(boxed, in_box, &[], in_word, &[]);

    b.switch_to_block(in_box);
    b.seal_block(in_box);
    let box_address = address_field(b, word);
    let stored = b.ins().load(types::I64, MemFlagsData::trusted(), box_address, 0);
    b.ins().jump(joined, &[BlockArg::Value(stored)]);

    b.switch_to_block(in_word);
    b.seal_block(in_word);
    let payload = payload_field(b, word);
    b.ins().jump(joined, &[BlockArg::Value(payload)]);

    b.switch_to_block(joined);
    b.seal_block(joined);
    b.block_params(joined)[0]
}
