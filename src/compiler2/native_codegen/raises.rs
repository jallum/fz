//! Which machine functions can leave by a raise.
//!
//! A raise is a `Term::Raise`, `Term::Reraise` or `Term::RaiseUndefined`, or a
//! call of an extern declared never to return. A machine function may raise
//! when its code holds one, or when it calls, or tail-calls, a machine function
//! that may. A caller checks the process for an unwind only after a call to a
//! machine function that may raise, since nothing else can leave it set.

use super::super::artifact::{NativeEntryAbi, NativeProgram};
use crate::fast_hash::HashSet;
use crate::fz_ir::{DirectCallTarget, ExternTy, FnId, FnIr, Module, Prim, Term};

/// The machine functions of `program` that may raise.
pub(super) fn raising_machines(program: &NativeProgram) -> HashSet<FnId> {
    let machines = program
        .bodies
        .iter()
        .filter(|body| matches!(body.entry_abi, NativeEntryAbi::Machine))
        .map(|body| program.module.fn_by_id(body.fn_id))
        .collect::<Vec<_>>();
    let mut raising = HashSet::default();
    loop {
        let before = raising.len();
        for function in &machines {
            if !raising.contains(&function.id) && may_raise(&program.module, function, &raising) {
                raising.insert(function.id);
            }
        }
        if raising.len() == before {
            return raising;
        }
    }
}

fn may_raise(module: &Module, function: &FnIr, raising: &HashSet<FnId>) -> bool {
    function.blocks.iter().any(|block| {
        let calls_raiser = |callee: &FnId| raising.contains(callee);
        let stmt_raises = block.stmts.iter().any(|stmt| match stmt.prim() {
            Prim::MachineCall(callee, _) => calls_raiser(callee),
            Prim::Extern(_, eid, _) => module.extern_by_id(*eid).ret == ExternTy::Never,
            _ => false,
        });
        stmt_raises
            || match &block.terminator {
                Term::Raise { .. } | Term::Reraise { .. } | Term::RaiseUndefined { .. } => true,
                Term::TailCall {
                    callee: DirectCallTarget::Local(callee),
                    ..
                } => calls_raiser(callee),
                _ => false,
            }
    })
}
