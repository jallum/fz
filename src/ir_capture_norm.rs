//! Normalize continuation captures after lowering.
//!
//! Lowering is allowed to be conservative while it is splitting source
//! expressions into CPS continuations. This pass is the canonical boundary that
//! turns that conservative shape into an honest ABI: a continuation captures
//! each caller `Var` at most once, and only when the continuation body actually
//! reads the corresponding entry param.

use crate::fz_ir::{Cont, FnId, Module, Stmt, Term, Var};
use crate::ir_dce::collect_used;
use crate::ir_fuse::{subst_stmt, subst_term};
use std::collections::{HashMap, HashSet};

pub fn normalize_continuation_captures(module: &mut Module) {
    loop {
        let sites = continuation_sites(module);
        let mut changed = false;
        for site in sites {
            if site.site_count != 1 {
                continue;
            }
            let Some(plan) = plan_site(module, &site) else {
                continue;
            };
            if !plan.changed {
                continue;
            }
            apply_plan(module, site, plan);
            changed = true;
            break;
        }
        if !changed {
            break;
        }
    }
}

#[derive(Debug, Clone)]
struct ContinuationSite {
    caller_fn_idx: usize,
    caller_block_idx: usize,
    cont: Cont,
    site_count: usize,
}

#[derive(Debug, Clone)]
struct NormalizePlan {
    new_captured: Vec<Var>,
    entry_params: Vec<Var>,
    subst: HashMap<Var, Var>,
    changed: bool,
}

fn continuation_sites(module: &Module) -> Vec<ContinuationSite> {
    let mut counts: HashMap<FnId, usize> = HashMap::new();
    let mut raw = Vec::new();
    for (fi, f) in module.fns.iter().enumerate() {
        for (bi, block) in f.blocks.iter().enumerate() {
            let cont = match &block.terminator {
                Term::Call { continuation, .. }
                | Term::CallClosure { continuation, .. }
                | Term::Receive { continuation, .. } => continuation.clone(),
                _ => continue,
            };
            *counts.entry(cont.fn_id).or_insert(0) += 1;
            raw.push((fi, bi, cont));
        }
    }

    raw.into_iter()
        .map(|(caller_fn_idx, caller_block_idx, cont)| ContinuationSite {
            caller_fn_idx,
            caller_block_idx,
            site_count: counts.get(&cont.fn_id).copied().unwrap_or(0),
            cont,
        })
        .collect()
}

fn plan_site(module: &Module, site: &ContinuationSite) -> Option<NormalizePlan> {
    let cont_idx = *module.fn_idx.get(&site.cont.fn_id)?;
    let cont_fn = &module.fns[cont_idx];
    let entry = cont_fn.blocks.iter().find(|b| b.id == cont_fn.entry)?;
    if entry.params.len() != site.cont.captured.len() + 1 {
        return None;
    }
    if site.cont.captured.is_empty() {
        return None;
    }

    let used = collect_used(cont_fn);
    let captured_params = &entry.params[1..];
    let mut groups: Vec<CaptureGroup> = Vec::new();
    let mut group_by_outer: HashMap<Var, usize> = HashMap::new();

    for (i, (&outer, &param)) in site
        .cont
        .captured
        .iter()
        .zip(captured_params.iter())
        .enumerate()
    {
        let group_idx = match group_by_outer.get(&outer).copied() {
            Some(idx) => idx,
            None => {
                let idx = groups.len();
                group_by_outer.insert(outer, idx);
                groups.push(CaptureGroup {
                    outer,
                    representative_param: param,
                    positions: Vec::new(),
                });
                idx
            }
        };
        groups[group_idx].positions.push(CapturePosition {
            index: i,
            param,
            used: used.contains(&param),
        });
    }

    let mut live_indices: HashSet<usize> = HashSet::new();
    let mut new_captured = Vec::new();
    let mut subst = HashMap::new();

    for group in groups {
        if !group.positions.iter().any(|pos| pos.used) {
            continue;
        }
        live_indices.insert(group.positions[0].index);
        new_captured.push(group.outer);
        for pos in group.positions.iter().skip(1) {
            subst.insert(pos.param, group.representative_param);
        }
    }

    let mut entry_params = Vec::with_capacity(1 + new_captured.len());
    entry_params.push(entry.params[0]);
    for (i, &param) in captured_params.iter().enumerate() {
        if live_indices.contains(&i) {
            entry_params.push(param);
        }
    }

    let changed = new_captured != site.cont.captured || !subst.is_empty();
    Some(NormalizePlan {
        new_captured,
        entry_params,
        subst,
        changed,
    })
}

#[derive(Debug, Clone)]
struct CaptureGroup {
    outer: Var,
    representative_param: Var,
    positions: Vec<CapturePosition>,
}

#[derive(Debug, Clone)]
struct CapturePosition {
    index: usize,
    param: Var,
    used: bool,
}

fn apply_plan(module: &mut Module, site: ContinuationSite, plan: NormalizePlan) {
    let cont_idx = *module
        .fn_idx
        .get(&site.cont.fn_id)
        .expect("continuation fn exists");
    let cont_fn = &mut module.fns[cont_idx];
    if !plan.subst.is_empty() {
        for block in &mut cont_fn.blocks {
            let stmts: Vec<Stmt> = block
                .stmts
                .iter()
                .map(|stmt| subst_stmt(stmt, &plan.subst))
                .collect();
            block.stmts = stmts;
            block.terminator = subst_term(&block.terminator, &plan.subst);
        }
    }
    let entry = cont_fn
        .blocks
        .iter_mut()
        .find(|block| block.id == cont_fn.entry)
        .expect("continuation entry block exists");
    entry.params = plan.entry_params;
    cont_fn.ignored_entry_params = vec![false; entry.params.len()];

    let term = &mut module.fns[site.caller_fn_idx].blocks[site.caller_block_idx].terminator;
    match term {
        Term::Call { continuation, .. }
        | Term::CallClosure { continuation, .. }
        | Term::Receive { continuation, .. } => {
            continuation.captured = plan.new_captured;
        }
        _ => unreachable!("captured site no longer points at a continuation term"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BlockId, Const, FnBuilder, FnId, ModuleBuilder, Prim};

    fn build_module_with_cont(captured: Vec<Var>, captured_params: Vec<Var>, used: Var) -> Module {
        let caller_id = FnId(0);
        let cont_id = FnId(1);

        let mut caller = FnBuilder::new(caller_id, "caller");
        let entry = caller.block(vec![]);
        let callee_arg = caller.let_(entry, Prim::Const(Const::Int(0)));
        caller.set_terminator(
            entry,
            Term::Call {
                ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
                callee: FnId(99),
                args: vec![callee_arg],
                continuation: Cont {
                    fn_id: cont_id,
                    captured,
                },
            },
        );

        let mut cont =
            FnBuilder::new(cont_id, "k_1").with_category(crate::fz_ir::FnCategory::CpsCont);
        let result = Var(0);
        let mut params = vec![result];
        params.extend(captured_params);
        let entry = cont.block(params);
        cont.set_terminator(entry, Term::Return(used));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(caller.build());
        mb.add_fn(cont.build());
        mb.build()
    }

    #[test]
    fn drops_unused_continuation_captures() {
        let mut module =
            build_module_with_cont(vec![Var(10), Var(11)], vec![Var(1), Var(2)], Var(2));

        normalize_continuation_captures(&mut module);

        let caller = module.fn_by_id(FnId(0));
        let Term::Call { continuation, .. } = &caller.block(BlockId(0)).terminator else {
            panic!("expected call terminator");
        };
        assert_eq!(continuation.captured, vec![Var(11)]);

        let cont = module.fn_by_id(FnId(1));
        assert_eq!(cont.block(BlockId(0)).params, vec![Var(0), Var(2)]);
    }

    #[test]
    fn deduplicates_same_outer_var_and_rewrites_body() {
        let mut module =
            build_module_with_cont(vec![Var(10), Var(10)], vec![Var(1), Var(2)], Var(2));

        normalize_continuation_captures(&mut module);

        let caller = module.fn_by_id(FnId(0));
        let Term::Call { continuation, .. } = &caller.block(BlockId(0)).terminator else {
            panic!("expected call terminator");
        };
        assert_eq!(continuation.captured, vec![Var(10)]);

        let cont = module.fn_by_id(FnId(1));
        let entry = cont.block(BlockId(0));
        assert_eq!(entry.params, vec![Var(0), Var(1)]);
        assert!(matches!(entry.terminator, Term::Return(Var(1))));
    }
}
