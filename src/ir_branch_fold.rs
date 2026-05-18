//! fz-fyq.4 — dead-branch fold.
//!
//! Consumer of `ModuleTypes::dead_branches` (fz-fyq.2). For each
//! `Term::If` the typer proved one-sided-dead under cross-spec consensus,
//! rewrite the terminator to a `Term::Goto` jumping to the live successor.
//! Standard `ir_dce::dce_module` (which already runs after this in
//! `ir_codegen::compile`) then removes the unused TypeTest stmt (its dest
//! is no longer read) and the orphaned dead-side blocks.
//!
//! Sibling of `ir_fold::fold_module` — that pass folds prims; this one
//! folds terminators. The cond-singleton case `ir_fold` used to handle
//! (`Term::If(cond, T, E)` when `cond : :true`/`:false`) is subsumed:
//! cond becoming singleton makes one branch's narrowing empty, which is
//! exactly what `find_emptied_var` detects when computing
//! `dead_branches`.
//!
//! Soundness rests on the producer's cross-spec consensus rule. The
//! rewrite is mechanical; no per-spec reasoning happens here.

use crate::fz_ir::{BlockId, DeadBranch, FnId, Module, Term};
use crate::ir_typer::ModuleTypes;
use std::collections::HashMap;

/// Apply the fold to every fn in the module in-place.
pub fn fold_module(m: &mut Module, mt: &ModuleTypes) {
    // Group entries by fn so we can do one pass per FnIr.
    let mut by_fn: HashMap<FnId, Vec<(BlockId, DeadBranch)>> = HashMap::new();
    for ((fid, bid), which) in &mt.dead_branches {
        by_fn.entry(*fid).or_default().push((*bid, *which));
    }
    for f in &mut m.fns {
        let Some(entries) = by_fn.get(&f.id) else {
            continue;
        };
        for (bid, which) in entries {
            let Some(block) = f.blocks.iter_mut().find(|b| b.id == *bid) else {
                continue;
            };
            let Term::If {
                then_b, else_b, ..
            } = block.terminator
            else {
                continue;
            };
            let live = match which {
                DeadBranch::Then => else_b,
                DeadBranch::Else => then_b,
            };
            block.terminator = Term::Goto(live, vec![]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BranchOrigin, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term, Var};

    /// Sanity: a Term::If with DeadBranch::Else becomes Goto(then_b).
    #[test]
    fn fold_else_dead_rewrites_to_goto_then() {
        // entry(x): c = IsEmptyList(x); if c then halt_b else dead_b
        let mut b = FnBuilder::new(FnId(0), "main");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let c = b.let_(entry, Prim::Const(Const::True));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::if_user(c, then_b, else_b));
        b.set_terminator(then_b, Term::Halt(x));
        b.set_terminator(else_b, Term::Halt(x));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();
        let mt = crate::ir_typer::type_module(&m);
        fold_module(&mut m, &mt);
        // If the typer proved else dead, the entry block now ends in Goto(then_b).
        match &m.fns[0].block(entry).terminator {
            Term::Goto(target, _) => assert_eq!(*target, then_b),
            Term::If { else_b: e, .. } => {
                // If the typer didn't prove anything here, the IR is unchanged.
                // For this synthetic shape, `c : :true` should make the else dead.
                panic!("expected fold; got If with else={:?}", e);
            }
            other => panic!("unexpected terminator: {:?}", other),
        }
    }

    /// Non-User origins are still folded — the diagnostic origin filter
    /// is for warnings only; the fold acts on every dead branch regardless.
    #[test]
    fn fold_acts_on_synthesized_origin() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let c = b.let_(entry, Prim::Const(Const::True));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(
            entry,
            Term::If {
                cond: c,
                then_b,
                else_b,
                origin: BranchOrigin::PatternBind,
            },
        );
        b.set_terminator(then_b, Term::Halt(x));
        b.set_terminator(else_b, Term::Halt(x));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();
        let mt = crate::ir_typer::type_module(&m);
        fold_module(&mut m, &mt);
        match &m.fns[0].block(entry).terminator {
            Term::Goto(target, _) => assert_eq!(*target, then_b),
            other => panic!("expected Goto(then_b); got {:?}", other),
        }
    }

    /// If the typer didn't prove anything dead, the fold is a no-op.
    #[test]
    fn fold_noop_when_no_dead_branches() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let c = b.let_(entry, Prim::IsEmptyList(x));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::if_user(c, then_b, else_b));
        b.set_terminator(then_b, Term::Return(x));
        b.set_terminator(else_b, Term::Return(x));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();
        let mt = crate::ir_typer::type_module(&m);
        fold_module(&mut m, &mt);
        // x : any — neither branch provably dead; If untouched.
        assert!(matches!(m.fns[0].block(entry).terminator, Term::If { .. }));
        let _ = Var(0);
    }
}
