//! Atom ordering, decided in place unless the names must be read.
//!
//! `fz_value_cmp_ref` orders any two values. Where both operands are known
//! atoms (each kind argument is the constant atom kind) the stored words are
//! atom ids. Atoms order by name and the id says nothing about it, but each
//! atom's table entry keeps the first eight bytes of its name as one
//! big-endian word, so two atoms whose words differ order as those words do,
//! as unsigned integers. The instructions read both words through
//! `Process::atom_name_prefixes` and answer -1 or 1 from them. Two atoms whose
//! words tie either are the same atom, which the ids say, or share their first
//! eight bytes, which only the names can order: `fz_atom_names_cmp` is called
//! then, in a cold block. Any other pair is the runtime function's.
//!
//! `==`, `!=`, `===` and `!==` of two known atoms are one comparison of the two
//! ids and are plain rows in `recipe.rs`.

use super::clif::word_at;
use super::recipe::{Emitted, both_atoms};
use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlagsData, condcodes::IntCC, types};
use fz_runtime::ir_runtime::fz_atom_names_cmp;
use fz_runtime::process_abi::PROCESS_ATOM_NAME_PREFIXES_OFFSET;

/// `Kernel.compare` of two atoms: -1, 0 or 1 by their names, or `None` when an
/// operand is not a known atom. `args` are the process, then each operand's
/// stored word and kind.
pub(crate) fn emit_atom_compare<B: RuntimeCaller>(body: &mut B, args: &[ir::Value]) -> Option<Emitted> {
    let &[process, left, left_kind, right, right_kind] = args else {
        panic!("an atom ordering row takes 5 arguments, got {}", args.len());
    };
    if !body.with_builder(|b| both_atoms(b, left_kind, right_kind)) {
        return None;
    }
    let done = body.with_builder(|b| {
        let tie = b.create_block();
        let names = b.create_block();
        let done = b.create_block();
        b.append_block_param(done, types::I64);

        let flags = MemFlagsData::trusted();
        let at = b
            .ins()
            .load(types::I64, flags, process, PROCESS_ATOM_NAME_PREFIXES_OFFSET);
        let prefixes = b.ins().load(types::I64, flags, at, 0);
        let left_slot = word_at(b, prefixes, left);
        let left_prefix = b.ins().load(types::I64, flags, left_slot, 0);
        let right_slot = word_at(b, prefixes, right);
        let right_prefix = b.ins().load(types::I64, flags, right_slot, 0);
        let less = b.ins().icmp(IntCC::UnsignedLessThan, left_prefix, right_prefix);
        let before = b.ins().iconst(types::I64, -1);
        let after = b.ins().iconst(types::I64, 1);
        let differing = b.ins().select(less, before, after);
        let tied = b.ins().icmp(IntCC::Equal, left_prefix, right_prefix);
        b.ins().brif(tied, tie, &[], done, &[BlockArg::Value(differing)]);

        b.switch_to_block(tie);
        b.seal_block(tie);
        b.set_cold_block(tie);
        let same_atom = b.ins().icmp(IntCC::Equal, left, right);
        let equal = b.ins().iconst(types::I64, 0);
        b.ins().brif(same_atom, done, &[BlockArg::Value(equal)], names, &[]);

        b.switch_to_block(names);
        b.seal_block(names);
        b.set_cold_block(names);
        done
    });
    let call = runtime_call!(body, fz_atom_names_cmp, [process, left, right]);
    let word = body.sole_result(call);
    let answer = body.with_builder(|b| {
        b.ins().jump(done, &[BlockArg::Value(word)]);
        b.switch_to_block(done);
        b.seal_block(done);
        b.block_params(done)[0]
    });
    Some(Emitted::Value(answer))
}
