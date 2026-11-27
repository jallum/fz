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
//!
//! This module is the one home of the cell's layout. Every read and write of
//! a cell's two words, from here, from cons reuse and from the share barrier,
//! goes through the functions below.

use super::place::emit_place;
use super::recipe::constant_of;
use super::runtime_call::{RuntimeCaller, runtime_call1};
use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlagsData, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use fz_runtime::any_value::{
    AnyValueRefPacking, LIST_CONS_HEAD_OFFSET, LIST_CONS_LINK_OFFSET, LIST_LINK_ALIAS_MASK, LIST_LINK_TERMINATOR_MASK,
    TAG_BITS, ValueKind,
};
use fz_runtime::heap::HeapAllocKind;
use fz_runtime::ir_runtime::fz_list_tail_ref;

/// How a cell's head reaches it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HeadLane {
    /// The head's stored word and its kind.
    Stored,
    /// The head's ref word.
    Ref,
}

/// What the type of a list says about where it ends.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ListShape {
    /// The list ends in `[]`: the link of a cell never holds the terminator flag.
    Proper,
    /// The list may end in a value that is not a list.
    MayEndInAValue,
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
    store_cell(body.b, address, head.raw, link);
    body.heap_ref_word_from_addr(address, ValueKind::LIST)
}

/// The address of the cell a list ref names; zero for `[]`.
pub(super) fn cell_address(b: &mut FunctionBuilder<'_>, list_ref: ir::Value) -> ir::Value {
    address_field(b, list_ref)
}

/// The head word of the cell at `cell`, as an `I64` or an `F64`: an integer
/// head is the integer, a float head its bits.
pub(super) fn load_head(b: &mut FunctionBuilder<'_>, cell: ir::Value, ty: ir::Type) -> ir::Value {
    b.ins()
        .load(ty, MemFlagsData::trusted(), cell, LIST_CONS_HEAD_OFFSET as i32)
}

/// The link word of the cell at `cell`: the tail's address, the head's kind,
/// the alias bit and the terminator flag.
pub(super) fn load_link(b: &mut FunctionBuilder<'_>, cell: ir::Value) -> ir::Value {
    b.ins()
        .load(types::I64, MemFlagsData::trusted(), cell, LIST_CONS_LINK_OFFSET as i32)
}

/// Write both words of the cell at `cell`.
pub(super) fn store_cell(b: &mut FunctionBuilder<'_>, cell: ir::Value, head: ir::Value, link: ir::Value) {
    let flags = MemFlagsData::trusted();
    b.ins().store(flags, head, cell, LIST_CONS_HEAD_OFFSET as i32);
    b.ins().store(flags, link, cell, LIST_CONS_LINK_OFFSET as i32);
}

/// Nonzero when `link` marks its cell as held twice, so that it may not be
/// written through.
pub(super) fn link_is_shared(b: &mut FunctionBuilder<'_>, link: ir::Value) -> ir::Value {
    b.ins().band_imm_u(link, LIST_LINK_ALIAS_MASK as i64)
}

/// Whether two link words name the same tail and head kind, whether or not
/// either cell is shared.
pub(super) fn links_agree_but_for_sharing(b: &mut FunctionBuilder<'_>, old: ir::Value, new: ir::Value) -> ir::Value {
    let difference = b.ins().bxor(old, new);
    let without_sharing = b.ins().band_imm_u(difference, !LIST_LINK_ALIAS_MASK as i64);
    b.ins().icmp_imm_s(IntCC::Equal, without_sharing, 0)
}

/// Nonzero when `link` ends its list in a value that is not a list, which a
/// terminator cell holds.
pub(super) fn link_is_terminated(b: &mut FunctionBuilder<'_>, link: ir::Value) -> ir::Value {
    b.ins().band_imm_u(link, LIST_LINK_TERMINATOR_MASK as i64)
}

/// The ref word of the list that follows a cell whose link is `link`, which
/// the caller knows is not terminated: the next cell's address under the kind
/// of a list, `[]` when the address is zero.
pub(super) fn tail_of_link(b: &mut FunctionBuilder<'_>, link: ir::Value) -> ir::Value {
    let packing = AnyValueRefPacking::current();
    let address = b.ins().band_imm_u(link, packing.address_mask() as i64);
    let list_kind = u64::from(ValueKind::LIST.tag()) << packing.tag_shift();
    b.ins().bor_imm_u(address, list_kind as i64)
}

/// The ref word of the head of the cell `list_ref` names.
pub(super) fn emit_head_ref<C: RuntimeCaller>(caller: &mut C, list_ref: ir::Value) -> ir::Value {
    caller.with_builder(|b| {
        let cell = cell_address(b, list_ref);
        let link = load_link(b, cell);
        head_ref(b, cell, link)
    })
}

/// The ref word of what follows the cell `list_ref` names. A list that is
/// proper is read with a load and a mask; any other list tests its link for
/// the terminator flag first, and only a terminated one asks the runtime for
/// the value it ends in.
pub(super) fn emit_tail_ref<C: RuntimeCaller>(caller: &mut C, list_ref: ir::Value, shape: ListShape) -> ir::Value {
    let (link, terminated, done) = caller.with_builder(|b| {
        let cell = cell_address(b, list_ref);
        let link = load_link(b, cell);
        if shape == ListShape::Proper {
            return (link, None, None);
        }
        let next = b.create_block();
        let terminated = b.create_block();
        let done = b.create_block();
        b.append_block_param(done, types::I64);
        let flag = link_is_terminated(b, link);
        b.ins().brif(flag, terminated, &[], next, &[]);
        b.switch_to_block(next);
        b.seal_block(next);
        (link, Some(terminated), Some(done))
    });
    let tail = caller.with_builder(|b| tail_of_link(b, link));
    let (Some(terminated), Some(done)) = (terminated, done) else {
        return tail;
    };
    caller.with_builder(|b| {
        b.ins().jump(done, &[BlockArg::Value(tail)]);
        b.switch_to_block(terminated);
        b.seal_block(terminated);
    });
    let value = runtime_call1!(caller, fz_list_tail_ref, [list_ref]);
    caller.with_builder(|b| {
        b.ins().jump(done, &[BlockArg::Value(value)]);
        b.switch_to_block(done);
        b.seal_block(done);
        b.block_params(done)[0]
    })
}

/// The ref word of the head of the cell at `cell` whose link is `link`, as
/// the runtime's head read answers it: a boxed scalar is a reference to the
/// head word in the cell, any other kind is the head word itself under the
/// kind the link holds.
pub(super) fn head_ref(b: &mut FunctionBuilder<'_>, cell: ir::Value, link: ir::Value) -> ir::Value {
    let packing = AnyValueRefPacking::current();
    let shifted = b.ins().ushr_imm_u(link, i64::from(packing.tag_shift()));
    let kind = b.ins().band_imm_u(shifted, ((1u64 << TAG_BITS) - 1) as i64);
    let word = load_head(b, cell, types::I64);
    let payload = payload_field(b, word);
    let boxed = kind_is_one_of(b, kind, ValueKind::is_boxed_scalar);
    let address = b.ins().select(boxed, cell, payload);
    let kind_bits = b.ins().ishl_imm_u(kind, i64::from(packing.tag_shift()));
    b.ins().bor(address, kind_bits)
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
