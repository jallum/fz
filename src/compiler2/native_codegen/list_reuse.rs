//! A list cell reused in place, or replaced by a new one.
//!
//! A construction that rebuilds a list cell from the cell it took apart asks
//! `fz_list_reuse_or_cons_parts` (its head given as a payload word and a kind,
//! or as a ref word) which cell
//! holds its answer. Compiled code makes that decision where it stands, in
//! the order the runtime function does:
//!
//! 1. The attempt is counted.
//! 2. A cell whose head word, head kind and tail already are the new ones is
//!    the answer. The hit is counted and nothing is written.
//! 3. The head is shared, because the cell that holds it is a second holder.
//!    A head that is the source cell itself marks the source, so the source's
//!    alias bit is read after this step and not before.
//! 4. A cell the construction may rewrite, and whose alias bit is clear, is
//!    the answer after its head word and link word are stored. The hit is
//!    counted. Its alias bit is clear, so the link word written is exactly the
//!    one a new cell holds.
//! 5. Otherwise a new cell is placed through `list_cell`, and is the answer.
//!
//! Whether the construction may rewrite, and the head's kind when the call
//! site knows it, are constants the call site passes; the row reads them when
//! the code is emitted.

use super::list_cell::{Head, decode, link_word, place_cell};
use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlagsData, condcodes::IntCC, types};
use fz_runtime::any_value::{LIST_CONS_LINK_OFFSET, LIST_LINK_ALIAS_MASK, ValueKind};
use fz_runtime::process_abi::{PROCESS_LIST_RETENTION_ATTEMPTS_OFFSET, PROCESS_LIST_RETENTION_HITS_OFFSET};

/// How the replacement head reaches the row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReuseLane {
    /// The head is a ref word.
    Ref,
    /// The head is a payload word and a kind constant.
    Parts,
}

/// The kinds whose objects carry a mark a holder must set.
const MARKED_KINDS: [ValueKind; 4] = [
    ValueKind::LIST,
    ValueKind::STRUCT,
    ValueKind::BITSTRING,
    ValueKind::BINVIEW,
];

/// Answer the ref word of the cell that holds the rebuilt list. `args` are
/// the runtime function's: the process, the source cell's ref, the head (a
/// ref word, or a payload word and its kind), the tail's ref and the rewrite
/// permission.
pub(super) fn emit_list_reuse<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    lane: ReuseLane,
    args: &[ir::Value],
    constant: impl Fn(&CodegenFn<'_, '_, M>, ir::Value) -> i64,
) -> ir::Value {
    let (source, tail, rewrite, head) = match (lane, args) {
        (ReuseLane::Ref, &[_process, source, head, tail, rewrite]) => (source, tail, rewrite, Replacement::Ref(head)),
        (ReuseLane::Parts, &[_process, source, raw, kind, tail, rewrite]) => {
            let kind = u8::try_from(constant(body, kind)).expect("a head kind fits a byte");
            let kind = ValueKind::new(kind).expect("a head kind");
            (source, tail, rewrite, Replacement::Parts { raw, kind })
        }
        _ => panic!(
            "a list reuse row is given the wrong number of arguments: {}",
            args.len()
        ),
    };
    let may_rewrite = constant(body, rewrite) != 0;
    body.bump_process_counter(PROCESS_LIST_RETENTION_ATTEMPTS_OFFSET);

    let replacement = head.decode(body);
    let source_address = address_field(body.b, source);
    let tail_address = address_field(body.b, tail);
    let link = link_word(body, &replacement, tail_address);
    let flags = MemFlagsData::trusted();
    let old_head = body.b.ins().load(types::I64, flags, source_address, 0);
    let old_link = body
        .b
        .ins()
        .load(types::I64, flags, source_address, LIST_CONS_LINK_OFFSET as i32);
    let same_head = body.b.ins().icmp(IntCC::Equal, old_head, replacement.raw);
    let link_difference = body.b.ins().bxor(old_link, link);
    let link_without_alias = body.b.ins().band_imm_u(link_difference, !LIST_LINK_ALIAS_MASK as i64);
    let same_link = body.b.ins().icmp_imm_s(IntCC::Equal, link_without_alias, 0);
    let unchanged = body.b.ins().band(same_head, same_link);

    let done = body.b.create_block();
    body.b.append_block_param(done, types::I64);
    let keep = body.b.create_block();
    let changed = body.b.create_block();
    body.b.ins().brif(unchanged, keep, &[], changed, &[]);

    body.b.switch_to_block(keep);
    body.b.seal_block(keep);
    body.bump_process_counter(PROCESS_LIST_RETENTION_HITS_OFFSET);
    body.b.ins().jump(done, &[BlockArg::Value(source)]);

    body.b.switch_to_block(changed);
    body.b.seal_block(changed);
    head.share(body);
    let fresh = body.b.create_block();
    if may_rewrite {
        let rewrite = body.b.create_block();
        let current = body
            .b
            .ins()
            .load(types::I64, flags, source_address, LIST_CONS_LINK_OFFSET as i32);
        let aliased = body.b.ins().band_imm_u(current, LIST_LINK_ALIAS_MASK as i64);
        body.b.ins().brif(aliased, fresh, &[], rewrite, &[]);
        body.b.switch_to_block(rewrite);
        body.b.seal_block(rewrite);
        body.b.ins().store(flags, replacement.raw, source_address, 0);
        body.b
            .ins()
            .store(flags, link, source_address, LIST_CONS_LINK_OFFSET as i32);
        body.bump_process_counter(PROCESS_LIST_RETENTION_HITS_OFFSET);
        body.b.ins().jump(done, &[BlockArg::Value(source)]);
    } else {
        body.b.ins().jump(fresh, &[]);
    }

    body.b.switch_to_block(fresh);
    body.b.seal_block(fresh);
    let cell = place_cell(body, &replacement, tail_address);
    body.b.ins().jump(done, &[BlockArg::Value(cell)]);

    body.b.switch_to_block(done);
    body.b.seal_block(done);
    body.b.block_params(done)[0]
}

/// The head as the row receives it.
#[derive(Clone, Copy)]
enum Replacement {
    Ref(ir::Value),
    Parts { raw: ir::Value, kind: ValueKind },
}

impl Replacement {
    fn decode<M: cranelift_module::Module>(self, body: &mut CodegenFn<'_, '_, M>) -> Head {
        match self {
            Self::Ref(head) => decode(body, head),
            Self::Parts { raw, kind } => Head::known(raw, kind),
        }
    }

    /// Share the head the cell is about to hold.
    fn share<M: cranelift_module::Module>(self, body: &mut CodegenFn<'_, '_, M>) {
        match self {
            Self::Ref(head) => body.share(CodegenValue::AnyRef(head)),
            Self::Parts { raw, kind } if MARKED_KINDS.contains(&kind) => {
                let reference = body.heap_ref_word_from_addr(raw, kind);
                body.share_kind(reference, kind);
            }
            Self::Parts { .. } => {}
        }
    }
}
