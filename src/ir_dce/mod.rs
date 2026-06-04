//! Function-local liveness helpers and DCE.
//!
//! Dead stmts: removes pure stmts whose dest var is not used anywhere in the fn.
//! Fixed-point loop handles chains of dead stmts.
//!
//! Dead blocks: after stmt DCE, prunes blocks unreachable from the entry block.
//! Only Goto and If create intra-function block edges; all other terminators
//! exit to a separate FnIr or terminate execution.
//!
//! The module does not own module-level reachability. Planner/materialization
//! produce reachable executable bodies; this module only answers local liveness
//! questions and removes local dead IR.

use crate::fz_ir::{BlockId, FnIr, PhysicalCapability, Prim, Stmt, Term, Var};
use crate::telemetry::Telemetry;
use std::collections::HashSet;

pub fn dce_fn_with_telemetry(module_path: &str, f: &mut FnIr, tel: &dyn Telemetry) {
    loop {
        let used = collect_used(f);
        let mut changed = false;
        for block in &mut f.blocks {
            let before = block.stmts.len();
            block.stmts.retain(|s| {
                let Stmt::Let(dest, prim) = s;
                used.contains(dest) || is_impure(prim)
            });
            changed |= block.stmts.len() != before;
        }
        if !changed {
            break;
        }
    }
    prune_dead_owned_cons_capabilities(f);

    // Dead block elimination: compute reachable set BEFORE retaining so that
    // f.block(id) — which panics on unknown id — is still safe to call.
    let reachable = reachable_from_entry(f);
    for block in &f.blocks {
        if !reachable.contains(&block.id) {
            tel.execute(
                &["fz", "ir", "dce", "block_pruned"],
                &crate::measurements! {
                    fn_id: f.id.0 as u64,
                    block_id: block.id.0 as u64,
                },
                &crate::metadata! {
                    module_path: module_path.to_owned(),
                    fn_name: f.name.clone(),
                    reason: "unreachable",
                },
            );
        }
    }
    f.blocks.retain(|b| reachable.contains(&b.id));
    prune_dead_owned_cons_capabilities(f);
}

fn reachable_from_entry(f: &FnIr) -> HashSet<BlockId> {
    let mut seen = HashSet::new();
    let mut work = vec![f.entry];
    while let Some(bid) = work.pop() {
        if !seen.insert(bid) {
            continue;
        }
        match &f.block(bid).terminator {
            Term::Goto(t, _) => work.push(*t),
            Term::If { then_b, else_b, .. } => {
                work.push(*then_b);
                work.push(*else_b);
            }
            _ => {}
        }
    }
    seen
}

/// Returns `(if_only_conds, all_used)` in a single pass.
///
/// `if_only_conds`: vars used exclusively as Term::If conditions — no prim
/// arg, no other terminator use. Boolean-producing prims whose dest is in
/// this set can skip emitting a tagged form entirely (fz-cg2.3).
///
/// `all_used`: every var referenced in any prim arg or terminator arg;
/// equivalent to the previous `collect_used` return value.
pub fn classify_var_uses(f: &FnIr) -> (HashSet<Var>, HashSet<Var>) {
    let mut if_conds: HashSet<Var> = HashSet::new();
    let mut other_uses: HashSet<Var> = HashSet::new();
    for block in &f.blocks {
        for stmt in &block.stmts {
            let Stmt::Let(_, prim) = stmt;
            collect_prim_vars(prim, &mut other_uses);
        }
        match &block.terminator {
            Term::If { cond, .. } => {
                if_conds.insert(*cond);
            }
            t => collect_term_vars(t, &mut other_uses),
        }
    }
    let mut all_used = other_uses.clone();
    all_used.extend(if_conds.iter().cloned());
    let if_only_conds: HashSet<Var> = if_conds.into_iter().filter(|v| !other_uses.contains(v)).collect();
    (if_only_conds, all_used)
}

pub fn collect_used(f: &FnIr) -> HashSet<Var> {
    let semantic_used = classify_var_uses(f).1;
    let mut used = semantic_used.clone();
    for fact in &f.physical_capabilities {
        match fact.capability {
            PhysicalCapability::OwnedConsReuse { head } if semantic_used.contains(&head) => {
                used.insert(fact.source);
            }
            _ => {}
        }
    }
    used
}

fn prune_dead_owned_cons_capabilities(f: &mut FnIr) {
    let semantic_used = classify_var_uses(f).1;
    f.physical_capabilities.retain(|fact| match fact.capability {
        PhysicalCapability::OwnedConsReuse { head } => semantic_used.contains(&head),
    });
    let live_sources: HashSet<Var> = f.physical_capabilities.iter().map(|fact| fact.source).collect();
    let entry_params: HashSet<Var> = f.block(f.entry).params.iter().copied().collect();
    f.physical_entry_params
        .retain(|param| entry_params.contains(param) && live_sources.contains(param));
    f.dedup_physical_facts();
}

fn collect_prim_vars(p: &Prim, used: &mut HashSet<Var>) {
    debug_assert!(
        !matches!(p, Prim::Brand(_, _)),
        "Prim::Brand reached DCE — erasure should run inside lower_program_full"
    );
    p.collect_used_vars(used);
}

fn collect_term_vars(t: &Term, used: &mut HashSet<Var>) {
    match t {
        Term::Goto(_, args) => {
            for v in args {
                used.insert(*v);
            }
        }
        Term::If { cond, .. } => {
            used.insert(*cond);
        }
        Term::Call {
            ident: _,
            args,
            continuation,
            ..
        } => {
            for v in args {
                used.insert(*v);
            }
            for v in &continuation.captured {
                used.insert(*v);
            }
        }
        Term::TailCall { args, .. } => {
            for v in args {
                used.insert(*v);
            }
        }
        Term::CallClosure {
            ident: _,
            closure,
            args,
            continuation,
        } => {
            used.insert(*closure);
            for v in args {
                used.insert(*v);
            }
            for v in &continuation.captured {
                used.insert(*v);
            }
        }
        Term::TailCallClosure {
            closure,
            args,
            ident: _,
        } => {
            used.insert(*closure);
            for v in args {
                used.insert(*v);
            }
        }
        Term::Return(a) | Term::Halt(a) => {
            used.insert(*a);
        }
        // fz-yxs — Vars referenced by ReceiveMatched: pinned and captures
        // are live (passed to matcher / clause-body fns), as is the
        // computed timeout Var if there's an after clause.
        Term::ReceiveMatched {
            pinned,
            captures,
            after,
            ..
        } => {
            for (_, v) in pinned {
                used.insert(*v);
            }
            for v in captures {
                used.insert(*v);
            }
            if let Some(a) = after {
                used.insert(a.timeout);
            }
        }
    }
}

fn is_impure(p: &Prim) -> bool {
    matches!(
        p,
        Prim::Extern(..)
            | Prim::DestTupleBegin { .. }
            | Prim::DestTupleSet { .. }
            | Prim::DestFreeze { .. }
            | Prim::DestListBegin { .. }
            | Prim::DestListCons { .. }
            | Prim::DestListFreeze { .. }
            | Prim::DestMapBegin { .. }
            | Prim::DestMapPut { .. }
            | Prim::DestMapFreeze { .. }
            | Prim::BitReaderInit(_)
            | Prim::BitReadField { .. }
            | Prim::BitReaderDone(_)
    )
}

#[cfg(test)]
mod ir_dce_test;
