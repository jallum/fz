//! Binary comparison, decided in place unless the bytes must be read.
//!
//! The six `fz_op_*_bb` functions take the process and the tagged words of two
//! binaries. The instructions answer without a call when the words are the
//! same word (the same object, so equal), and, for `==` and `!=`, when the two
//! bit lengths differ, which both header words hold in either binary form.
//! Anything else calls the runtime function, which reads the bytes, and the
//! call is a cold block. The answer is an `I8` condition; no boolean atom is
//! made. `===` and `!==` of two binaries are `==` and `!=`, so they share the
//! same functions and rows.
//!
//! A door that holds two values it has not proven to be binaries asks
//! [`emit_comparison_of_refs`], which tests both kinds and takes the same
//! instructions for two binaries, and its own comparison otherwise.

use super::recipe::header_word;
use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, condcodes::IntCC, types};
use fz_runtime::any_value::{BITSTRING_HEADER_LEN_MASK, ValueKind};
use fz_runtime::ir_runtime::{fz_op_eq_bb, fz_op_gt_bb, fz_op_gte_bb, fz_op_lt_bb, fz_op_lte_bb, fz_op_neq_bb};

/// Which comparison of two binaries a row answers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BinaryCompare {
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
}

impl BinaryCompare {
    /// Two words that are the same word name one binary, which equals itself.
    fn same_object_answer(self) -> bool {
        matches!(self, Self::Eq | Self::Lte | Self::Gte)
    }

    /// The answer when the bit lengths differ, for the comparisons that bit
    /// lengths alone settle.
    fn differing_length_answer(self) -> Option<bool> {
        match self {
            Self::Eq => Some(false),
            Self::Neq => Some(true),
            Self::Lt | Self::Lte | Self::Gt | Self::Gte => None,
        }
    }

    fn call<B: RuntimeCaller>(self, body: &mut B, args: [ir::Value; 3]) -> ir::Inst {
        let [process, left, right] = args;
        match self {
            Self::Eq => runtime_call!(body, fz_op_eq_bb, [process, left, right]),
            Self::Neq => runtime_call!(body, fz_op_neq_bb, [process, left, right]),
            Self::Lt => runtime_call!(body, fz_op_lt_bb, [process, left, right]),
            Self::Lte => runtime_call!(body, fz_op_lte_bb, [process, left, right]),
            Self::Gt => runtime_call!(body, fz_op_gt_bb, [process, left, right]),
            Self::Gte => runtime_call!(body, fz_op_gte_bb, [process, left, right]),
        }
    }
}

/// The condition that `which` holds of the binaries in `args`: the process,
/// then the left and right tagged words.
pub(crate) fn emit_binary_compare<B: RuntimeCaller>(
    body: &mut B,
    which: BinaryCompare,
    args: &[ir::Value],
) -> ir::Value {
    let &[process, left, right] = args else {
        panic!("a binary comparison row takes 3 arguments, got {}", args.len());
    };
    let done = body.with_builder(|b| {
        let bytes = b.create_block();
        let done = b.create_block();
        b.append_block_param(done, types::I8);

        let same_object = b.ins().icmp(IntCC::Equal, left, right);
        let same_answer = b.ins().iconst(types::I8, i64::from(which.same_object_answer()));
        let next = if which.differing_length_answer().is_some() {
            b.create_block()
        } else {
            bytes
        };
        b.ins()
            .brif(same_object, done, &[BlockArg::Value(same_answer)], next, &[]);

        if let Some(answer) = which.differing_length_answer() {
            b.switch_to_block(next);
            b.seal_block(next);
            let left_header = header_word(b, left);
            let right_header = header_word(b, right);
            let differing = b.ins().bxor(left_header, right_header);
            let length_differs = b.ins().band_imm_u(differing, BITSTRING_HEADER_LEN_MASK as i64);
            let differing_answer = b.ins().iconst(types::I8, i64::from(answer));
            b.ins()
                .brif(length_differs, done, &[BlockArg::Value(differing_answer)], bytes, &[]);
        }

        b.switch_to_block(bytes);
        b.seal_block(bytes);
        b.set_cold_block(bytes);
        done
    });
    let call = which.call(body, [process, left, right]);
    let word = body.sole_result(call);
    body.with_builder(|b| {
        let compared = b.ins().icmp_imm_s(IntCC::NotEqual, word, 0);
        b.ins().jump(done, &[BlockArg::Value(compared)]);
        b.switch_to_block(done);
        b.seal_block(done);
        b.block_params(done)[0]
    })
}

/// The condition that `which` holds of the values `left` and `right` (ref words) when
/// both are binaries or bitstrings; otherwise `otherwise`'s answer, which the
/// caller emits.
pub(crate) fn emit_comparison_of_refs<B: RuntimeCaller>(
    body: &mut B,
    process: ir::Value,
    which: BinaryCompare,
    left: ir::Value,
    right: ir::Value,
    otherwise: impl FnOnce(&mut B) -> ir::Value,
) -> ir::Value {
    let (binaries, others, done) = body.with_builder(|b| {
        let both = b.create_block();
        let binaries = b.create_block();
        let others = b.create_block();
        let done = b.create_block();
        b.append_block_param(done, types::I8);
        let left_is = is_binary_ref(b, left);
        b.ins().brif(left_is, both, &[], others, &[]);
        b.switch_to_block(both);
        b.seal_block(both);
        let right_is = is_binary_ref(b, right);
        b.ins().brif(right_is, binaries, &[], others, &[]);
        (binaries, others, done)
    });
    body.with_builder(|b| {
        b.switch_to_block(binaries);
        b.seal_block(binaries);
    });
    let equal = emit_binary_compare(body, which, &[process, left, right]);
    body.with_builder(|b| {
        b.ins().jump(done, &[BlockArg::Value(equal)]);
        b.switch_to_block(others);
        b.seal_block(others);
    });
    let generic = otherwise(body);
    body.with_builder(|b| {
        b.ins().jump(done, &[BlockArg::Value(generic)]);
        b.switch_to_block(done);
        b.seal_block(done);
        b.block_params(done)[0]
    })
}

/// Whether a ref word names a binary or bitstring, of either layout.
fn is_binary_ref(b: &mut cranelift_frontend::FunctionBuilder<'_>, word: ir::Value) -> ir::Value {
    let kind = kind_field(b, word);
    let inline = b
        .ins()
        .icmp_imm_s(IntCC::Equal, kind, i64::from(ValueKind::BITSTRING.tag()));
    let view = b
        .ins()
        .icmp_imm_s(IntCC::Equal, kind, i64::from(ValueKind::BINVIEW.tag()));
    b.ins().bor(inline, view)
}
