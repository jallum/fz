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
//! - a head held as its stored word and kind. An int, a float or an atom the
//!   call site holds unboxed is such a head whose kind is a constant: the
//!   cell's kind is then a constant and nothing needs sharing. Any other kind
//!   is shared as its ref would be, and is read from the register that holds it.
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
    /// The head's stored word and its kind.
    Stored,
    /// The head's ref word.
    Ref,
}

impl HeadLane {
    /// The arguments a row of this lane takes: the process, the head as the
    /// lane carries it, and the tail's word and kind.
    pub(super) const fn arity(self) -> usize {
        match self {
            Self::Stored => 5,
            Self::Ref => 4,
        }
    }
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

/// Place a cell whose head `args` carry as `lane` says, over the list at the
/// tail address, and answer its ref word. The tail's kind is a constant `LIST`.
/// The process, which `emit_place` reads from the pinned register, comes first.
pub(super) fn emit_list_cell<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    lane: HeadLane,
    args: &[ir::Value],
) -> ir::Value {
    assert_eq!(
        args.len(),
        lane.arity(),
        "a {lane:?} list cell row takes {} arguments, got {}",
        lane.arity(),
        args.len()
    );
    let (head, tail_address) = match (lane, args) {
        (HeadLane::Stored, &[_process, word, kind, tail_address, tail_kind]) => {
            assert_tail_is_list(body, tail_kind);
            (stored_head(body, word, kind), tail_address)
        }
        (HeadLane::Ref, &[_process, head_ref, tail_address, tail_kind]) => {
            assert_tail_is_list(body, tail_kind);
            body.share(CodegenValue::AnyRef(head_ref));
            (decode(body, head_ref), tail_address)
        }
        _ => unreachable!("the arity was checked"),
    };
    place_cell(body, &head, tail_address)
}

/// The head a stored word and kind name, as a cell stores it. A scalar of a
/// constant kind needs no sharing and no read of the kind; any other head is
/// shared as the ref it spells would be.
fn stored_head<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>, word: ir::Value, kind: ir::Value) -> Head {
    let constant = constant_of(body.b, kind).and_then(|tag| ValueKind::new(u8::try_from(tag).ok()?));
    match constant {
        Some(kind) if kind.is_scalar() => Head::known(word, kind),
        _ => {
            body.share(CodegenValue::Stored { word, kind });
            Head {
                raw: word,
                kind: HeadKind::Read(kind),
            }
        }
    }
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
