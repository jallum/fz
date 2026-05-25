//! fz-ul4.dce.3 — Singleton fold pass.
//!
//! After type_module proves a prim result or branch condition is a singleton,
//! replace it in-place. Downstream ir_dce then removes the now-dead stmts.
//!
//! Folds performed:
//!   - BinOp  result :: {n:int}          → Const(Int(n))
//!   - TypeTest result :: :true/:false   → Const(True/False)
//!   - Term::If cond  :: :true           → Term::Goto(then_b, [])
//!   - Term::If cond  :: :false | nil    → Term::Goto(else_b, [])

use crate::fz_ir::{Const, DeadBranch, FnIr, Module, Prim, Stmt, Term};
use crate::ir_typer::{FnTypes, ModuleTypes};
use crate::types::Types;
use std::collections::HashMap;

pub fn fold_module(m: &mut Module, types: &ModuleTypes) {
    let mut t = crate::types::ConcreteTypes;
    for f in &mut m.fns {
        fold_fn(&mut t, f, types);
    }
}

/// Return the best available FnTypes for `f`.
///
/// Prefers the any-key spec (most general). Falls back to the sole narrow spec
/// when there is exactly one — common for continuation functions that are only
/// ever called with one concrete type. Bails when multiple narrow specs exist,
/// since picking one arbitrarily could mis-fold the others.
fn best_fn_types<'a>(f: &FnIr, types: &'a ModuleTypes) -> Option<&'a FnTypes> {
    if let Some(ft) = types.any_key_spec(f.id) {
        return Some(ft);
    }
    let mut iter = types.specs.iter().filter(|((fid, _), _)| *fid == f.id);
    let first = iter.next()?.1;
    if iter.next().is_none() {
        Some(first)
    } else {
        None
    }
}

fn fold_fn<T: Types<Ty = crate::types::Ty>>(t: &mut T, f: &mut FnIr, types: &ModuleTypes) {
    let Some(fn_types) = best_fn_types(f, types) else {
        return;
    };
    fold_fn_with_types(t, f, fn_types);
}

/// fz-ul4.43.B — per-spec fold entry point.
///
/// Codegen calls this on a cloned FnIr per spec, passing that spec's
/// FnTypes directly, so each spec gets folded against its own narrowed
/// env. Avoids `fold_fn`'s `best_fn_types` fallback which bails when
/// multiple narrow specs exist — exactly the case where per-spec fold
/// is most valuable.
pub fn fold_fn_with_types<T: Types<Ty = crate::types::Ty>>(
    t: &mut T,
    f: &mut FnIr,
    fn_types: &FnTypes,
) {
    let true_t = t.bool_lit(true);
    let false_t = t.bool_lit(false);
    let nil_t = t.nil();
    for block in &mut f.blocks {
        for stmt in &mut block.stmts {
            let Stmt::Let(dest, prim) = stmt;
            let d = match prim {
                Prim::BinOp(..) | Prim::TypeTest(..) => {
                    fn_types.vars.get(dest).cloned().unwrap_or_else(|| t.any())
                }
                _ => continue,
            };
            if let Prim::BinOp(..) = prim {
                if let Some(n) = t.as_int_singleton(&d) {
                    *stmt = Stmt::Let(*dest, Prim::Const(Const::Int(n)));
                } else if t.is_subtype(&d, &true_t) {
                    // fz-ul4.43.D.1 — BinOp::Eq/Neq result narrowed to :true.
                    *stmt = Stmt::Let(*dest, Prim::Const(Const::True));
                } else if t.is_subtype(&d, &false_t) {
                    *stmt = Stmt::Let(*dest, Prim::Const(Const::False));
                }
            } else if let Prim::TypeTest(..) = prim {
                if t.is_subtype(&d, &true_t) {
                    *stmt = Stmt::Let(*dest, Prim::Const(Const::True));
                } else if t.is_subtype(&d, &false_t) {
                    *stmt = Stmt::Let(*dest, Prim::Const(Const::False));
                }
            }
        }

        // Per-spec cond-singleton `Term::If` fold. Acts on this spec's
        // own `fn_types.vars`, so it catches singleton-cond cases that
        // hold for THIS spec even when other specs leave the cond
        // generic — exactly the case `ir_branch_fold` (cross-spec
        // consensus) must skip for soundness. Sibling to the BinOp /
        // TypeTest folds above, which are also strictly per-spec.
        let new_term = if let Term::If {
            cond,
            then_b,
            else_b,
            ..
        } = &block.terminator
        {
            match verified_dead_branch(t, block, fn_types) {
                Some(DeadBranch::Then) => Some(Term::Goto(*else_b, vec![])),
                Some(DeadBranch::Else) => Some(Term::Goto(*then_b, vec![])),
                None => {
                    let ct = fn_types.vars.get(cond).cloned().unwrap_or_else(|| t.any());
                    if t.is_subtype(&ct, &true_t) {
                        Some(Term::Goto(*then_b, vec![]))
                    } else if t.is_subtype(&ct, &false_t) || t.is_subtype(&ct, &nil_t) {
                        Some(Term::Goto(*else_b, vec![]))
                    } else {
                        None
                    }
                }
            }
        } else {
            None
        };
        if let Some(t) = new_term {
            block.terminator = t;
        }
    }
}

fn verified_dead_branch<T: Types<Ty = crate::types::Ty>>(
    t: &mut T,
    block: &crate::fz_ir::Block,
    fn_types: &FnTypes,
) -> Option<DeadBranch> {
    let Term::If { cond, .. } = block.terminator else {
        return None;
    };
    if !fn_types.dead_branches.contains_key(&block.id) {
        return None;
    }

    let mut env: HashMap<crate::fz_ir::Var, crate::types::Ty> = fn_types
        .block_envs
        .get(&block.id)
        .cloned()
        .unwrap_or_default();
    for stmt in &block.stmts {
        let Stmt::Let(v, _) = stmt;
        if let Some(ty) = fn_types.vars.get(v).cloned() {
            env.insert(*v, ty);
        }
    }

    let (then_env, else_env) = crate::ir_typer::narrow_for_if(t, &env, cond, &block.stmts);
    let mut then_dead = crate::ir_typer::find_emptied_var(t, &env, &then_env).is_some();
    let mut else_dead = crate::ir_typer::find_emptied_var(t, &env, &else_env).is_some();

    let ct = env.get(&cond).cloned().unwrap_or_else(|| t.any());
    let true_t = t.bool_lit(true);
    let false_t = t.bool_lit(false);
    let nil_t = t.nil();
    if t.is_subtype(&ct, &true_t) {
        else_dead = true;
    } else if t.is_subtype(&ct, &false_t) || t.is_subtype(&ct, &nil_t) {
        then_dead = true;
    }

    match (then_dead, else_dead) {
        (true, false) => Some(DeadBranch::Then),
        (false, true) => Some(DeadBranch::Else),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term};
    use crate::types::Types;

    fn run_fold(f: crate::fz_ir::FnIr) -> crate::fz_ir::Module {
        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();
        let types = crate::ir_typer::type_module(
            &mut crate::types::ConcreteTypes,
            &m,
            &crate::telemetry::NullTelemetry,
        );
        // fz-fyq.4 — `ir_codegen::compile` runs `ir_branch_fold` before
        // `ir_fold`; mirror that order in the test pipeline so the
        // If-fold tests below (which used to depend on `ir_fold`'s own
        // cond-singleton fold) see the same end-state as production.
        crate::ir_branch_fold::fold_module_with_telemetry(
            &mut m,
            &types,
            &crate::telemetry::NullTelemetry,
        );
        fold_module(&mut m, &types);
        m
    }

    // ── BinOp fold ───────────────────────────────────────────────────────────

    #[test]
    fn binop_singleton_folded_to_const() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let c41 = b.let_(entry, Prim::Const(Const::Int(41)));
        let c1 = b.let_(entry, Prim::Const(Const::Int(1)));
        let sum = b.let_(entry, Prim::BinOp(BinOp::Add, c41, c1));
        b.set_terminator(entry, Term::Return(sum));
        let m = run_fold(b.build());
        match &m.fns[0].block(m.fns[0].entry).stmts[2] {
            Stmt::Let(_, Prim::Const(Const::Int(42))) => {}
            other => panic!("expected Const(Int(42)), got {:?}", other),
        }
    }

    #[test]
    fn binop_non_singleton_unchanged() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let param = b.fresh_var();
        let entry = b.block(vec![param]);
        let c1 = b.let_(entry, Prim::Const(Const::Int(1)));
        let sum = b.let_(entry, Prim::BinOp(BinOp::Add, param, c1));
        b.set_terminator(entry, Term::Return(sum));
        let m = run_fold(b.build());
        match &m.fns[0].block(m.fns[0].entry).stmts[1] {
            Stmt::Let(_, Prim::BinOp(..)) => {}
            other => panic!("expected BinOp unchanged, got {:?}", other),
        }
    }

    #[test]
    fn non_binop_unchanged() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let c41 = b.let_(entry, Prim::Const(Const::Int(41)));
        b.set_terminator(entry, Term::Return(c41));
        let m = run_fold(b.build());
        match &m.fns[0].block(m.fns[0].entry).stmts[0] {
            Stmt::Let(_, Prim::Const(Const::Int(41))) => {}
            other => panic!("expected Const(Int(41)) unchanged, got {:?}", other),
        }
    }

    // ── TypeTest fold ────────────────────────────────────────────────────────
    //
    // TypeTest(Const::Int(42), integer): typer proves result :: atom_lit("true").
    // TypeTest(Const::Nil, integer):     typer proves result :: atom_lit("false").
    // TypeTest(param :: any, integer):   typer gives result :: bool_t() — no fold.

    #[test]
    fn typetest_on_known_int_folded_to_const_true() {
        let mut t = crate::types::ConcreteTypes;
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let c42 = b.let_(entry, Prim::Const(Const::Int(42)));
        let tt = b.let_(entry, Prim::TypeTest(c42, Box::new(t.int())));
        b.set_terminator(entry, Term::Return(tt));
        let m = run_fold(b.build());
        match &m.fns[0].block(m.fns[0].entry).stmts[1] {
            Stmt::Let(_, Prim::Const(Const::True)) => {}
            other => panic!("expected Const(True), got {:?}", other),
        }
    }

    #[test]
    fn typetest_on_nil_folded_to_const_false() {
        let mut t = crate::types::ConcreteTypes;
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let nil = b.let_(entry, Prim::Const(Const::Nil));
        let tt = b.let_(entry, Prim::TypeTest(nil, Box::new(t.int())));
        b.set_terminator(entry, Term::Return(tt));
        let m = run_fold(b.build());
        match &m.fns[0].block(m.fns[0].entry).stmts[1] {
            Stmt::Let(_, Prim::Const(Const::False)) => {}
            other => panic!("expected Const(False), got {:?}", other),
        }
    }

    #[test]
    fn typetest_on_unknown_param_unchanged() {
        let mut t = crate::types::ConcreteTypes;
        let mut b = FnBuilder::new(FnId(0), "main");
        let param = b.fresh_var();
        let entry = b.block(vec![param]);
        let tt = b.let_(entry, Prim::TypeTest(param, Box::new(t.int())));
        b.set_terminator(entry, Term::Return(tt));
        let m = run_fold(b.build());
        match &m.fns[0].block(m.fns[0].entry).stmts[0] {
            Stmt::Let(_, Prim::TypeTest(..)) => {}
            other => panic!("expected TypeTest unchanged, got {:?}", other),
        }
    }

    // ── Term::If fold ────────────────────────────────────────────────────────
    //
    // Build a 3-block function: entry (with TypeTest on a constant) → If(tt, then_b, else_b).
    // The typer resolves the TypeTest to a singleton, fold rewrites If → Goto.

    #[test]
    fn if_always_true_cond_goto_then() {
        let mut t = crate::types::ConcreteTypes;
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        // TypeTest(42, integer) → always true
        let c42 = b.let_(entry, Prim::Const(Const::Int(42)));
        let tt = b.let_(entry, Prim::TypeTest(c42, Box::new(t.int())));
        b.set_terminator(entry, Term::if_user(tt, then_b, else_b));
        let nil1 = b.let_(then_b, Prim::Const(Const::Nil));
        b.set_terminator(then_b, Term::Return(nil1));
        let nil2 = b.let_(else_b, Prim::Const(Const::Nil));
        b.set_terminator(else_b, Term::Return(nil2));
        let m = run_fold(b.build());
        match &m.fns[0].block(entry).terminator {
            Term::Goto(t, args) if *t == then_b && args.is_empty() => {}
            other => panic!("expected Goto(then_b, []), got {:?}", other),
        }
    }

    #[test]
    fn if_always_false_cond_goto_else() {
        let mut t = crate::types::ConcreteTypes;
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        // TypeTest(nil, integer) → always false
        let nil_c = b.let_(entry, Prim::Const(Const::Nil));
        let tt = b.let_(entry, Prim::TypeTest(nil_c, Box::new(t.int())));
        b.set_terminator(entry, Term::if_user(tt, then_b, else_b));
        let nil1 = b.let_(then_b, Prim::Const(Const::Nil));
        b.set_terminator(then_b, Term::Return(nil1));
        let nil2 = b.let_(else_b, Prim::Const(Const::Nil));
        b.set_terminator(else_b, Term::Return(nil2));
        let m = run_fold(b.build());
        match &m.fns[0].block(entry).terminator {
            Term::Goto(t, args) if *t == else_b && args.is_empty() => {}
            other => panic!("expected Goto(else_b, []), got {:?}", other),
        }
    }

    #[test]
    fn if_nil_cond_directly_goto_else() {
        // Cond is Const::Nil directly (not via TypeTest) — typed as nil() → falsy.
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        let nil_c = b.let_(entry, Prim::Const(Const::Nil));
        b.set_terminator(entry, Term::if_user(nil_c, then_b, else_b));
        let n1 = b.let_(then_b, Prim::Const(Const::Nil));
        b.set_terminator(then_b, Term::Return(n1));
        let n2 = b.let_(else_b, Prim::Const(Const::Nil));
        b.set_terminator(else_b, Term::Return(n2));
        let m = run_fold(b.build());
        match &m.fns[0].block(entry).terminator {
            Term::Goto(t, args) if *t == else_b && args.is_empty() => {}
            other => panic!("expected Goto(else_b, []), got {:?}", other),
        }
    }

    #[test]
    fn if_unknown_cond_unchanged() {
        let mut t = crate::types::ConcreteTypes;
        // Cond is a param (any type) → bool_t() from TypeTest → no fold.
        let mut b = FnBuilder::new(FnId(0), "main");
        let param = b.fresh_var();
        let entry = b.block(vec![param]);
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        let tt = b.let_(entry, Prim::TypeTest(param, Box::new(t.int())));
        b.set_terminator(entry, Term::if_user(tt, then_b, else_b));
        let n1 = b.let_(then_b, Prim::Const(Const::Nil));
        b.set_terminator(then_b, Term::Return(n1));
        let n2 = b.let_(else_b, Prim::Const(Const::Nil));
        b.set_terminator(else_b, Term::Return(n2));
        let m = run_fold(b.build());
        match &m.fns[0].block(entry).terminator {
            Term::If {
                then_b: t,
                else_b: e,
                ..
            } if *t == then_b && *e == else_b => {}
            other => panic!("expected Term::If unchanged, got {:?}", other),
        }
    }
}
