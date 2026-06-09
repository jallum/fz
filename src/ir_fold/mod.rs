//! Planned-body singleton fold pass.
//!
//! After `plan_module_with_role` proves a prim result or branch condition is a singleton,
//! `PlannedProgram` materialization folds the per-spec body clone. The canonical
//! `Module` is not mutated with planner facts.
//!
//! Folds performed:
//!   - BinOp  result :: {n:int}          → Const(Int(n))
//!   - TypeTest result :: :true/:false   → Const(True/False)
//!   - Term::If cond  :: :true           → Term::Goto(then_b, [])
//!   - Term::If cond  :: :false | nil    → Term::Goto(else_b, [])

use crate::fz_ir::{Block, Const, DeadBranch, FnIr, Prim, Stmt, Term, Var};
use crate::ir_planner::{SpecPlan, find_emptied_var, narrow_for_if};
use crate::types::{Ty, Types};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct FoldStats {
    pub prim_count: usize,
    pub branch_count: usize,
}

/// fz-ul4.43.B — per-spec planned-body fold entry point.
///
/// Planned-program materialization calls this on one cloned `FnIr` per spec,
/// passing that spec's exact `SpecPlan`, so each body folds against its own
/// narrowed env. Avoids shared canonical-body mutation.
pub(crate) fn fold_planned_body<T: Types<Ty = Ty>>(t: &mut T, f: &mut FnIr, fn_types: &SpecPlan) -> FoldStats {
    let true_t = t.bool_lit(true);
    let false_t = t.bool_lit(false);
    let nil_t = t.nil();
    let mut stats = FoldStats::default();
    for block in &mut f.blocks {
        for stmt in &mut block.stmts {
            let Stmt::Let(dest, prim) = stmt;
            let d = match prim {
                Prim::BinOp(..) | Prim::TypeTest(..) | Prim::RuntimeTypeTestShim(..) => {
                    fn_types.vars.get(dest).cloned().unwrap_or_else(|| t.any())
                }
                _ => continue,
            };
            if let Prim::BinOp(..) = prim {
                if let Some(n) = t.as_int_singleton(&d) {
                    *stmt = Stmt::Let(*dest, Prim::Const(Const::Int(n)));
                    stats.prim_count += 1;
                } else if t.is_subtype(&d, &true_t) {
                    *stmt = Stmt::Let(*dest, Prim::Const(Const::True));
                    stats.prim_count += 1;
                } else if t.is_subtype(&d, &false_t) {
                    *stmt = Stmt::Let(*dest, Prim::Const(Const::False));
                    stats.prim_count += 1;
                }
            } else if matches!(prim, Prim::TypeTest(..) | Prim::RuntimeTypeTestShim(..)) {
                if t.is_subtype(&d, &true_t) {
                    *stmt = Stmt::Let(*dest, Prim::Const(Const::True));
                    stats.prim_count += 1;
                } else if t.is_subtype(&d, &false_t) {
                    *stmt = Stmt::Let(*dest, Prim::Const(Const::False));
                    stats.prim_count += 1;
                }
            }
        }

        let new_term = if let Term::If {
            cond, then_b, else_b, ..
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
            stats.branch_count += 1;
        }
    }
    stats
}

fn verified_dead_branch<T: Types<Ty = Ty>>(t: &mut T, block: &Block, fn_types: &SpecPlan) -> Option<DeadBranch> {
    let Term::If { cond, .. } = block.terminator else {
        return None;
    };
    if !fn_types.dead_branches.contains_key(&block.id) {
        return None;
    }

    let mut env: HashMap<Var, Ty> = fn_types.block_envs.get(&block.id).cloned().unwrap_or_default();
    for stmt in &block.stmts {
        let Stmt::Let(v, _) = stmt;
        if let Some(ty) = fn_types.vars.get(v).cloned() {
            env.insert(*v, ty);
        }
    }

    let (then_env, else_env) = narrow_for_if(t, &env, cond, &block.stmts);
    let mut then_dead = find_emptied_var(t, &env, &then_env).is_some();
    let mut else_dead = find_emptied_var(t, &env, &else_env).is_some();

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
