//! Normalize continuation captures after lowering.
//!
//! Lowering emits capture candidates while it splits source expressions into
//! CPS continuations. This pass is the canonical boundary that turns those
//! candidates into the ABI: a continuation captures each caller `Var` at most
//! once, and only when the continuation body actually reads the corresponding
//! entry param.

use crate::fz_ir::{Cont, FnCategory, FnId, FnIr, Module, Stmt, Term, Var};
use crate::ir_dce::{collect_used, dce_fn};
use crate::ir_fuse::{subst_stmt, subst_term};
use crate::telemetry::Telemetry;
use std::collections::{HashMap, HashSet};

pub fn normalize_continuation_captures(module: &mut Module, tel: &dyn Telemetry) {
    loop {
        let sites = continuation_sites(module);
        let tail_call_sites = tail_call_continuation_sites(module);
        let receive_matched_sites = receive_matched_sites(module);
        let mut changed = false;
        for site in sites {
            if site.site_count != 1 {
                continue;
            }
            let Some(plan) = plan_site(module, &site, tel) else {
                continue;
            };
            if !plan.changed {
                continue;
            }
            emit_call_pruned_event(module, &site, &plan, tel);
            apply_plan(module, site, plan, tel);
            changed = true;
            break;
        }
        if changed {
            continue;
        }
        for site in shared_continuation_sites(module) {
            let Some(plan) = plan_shared_continuation_site(module, &site, tel) else {
                continue;
            };
            if !plan.changed {
                continue;
            }
            emit_shared_call_pruned_event(module, &site, &plan, tel);
            apply_shared_continuation_plan(module, site, plan, tel);
            changed = true;
            break;
        }
        if changed {
            continue;
        }
        for site in tail_call_sites {
            let Some(plan) = plan_tail_call_continuation_site(module, &site, tel) else {
                continue;
            };
            if !plan.changed {
                continue;
            }
            emit_tail_call_pruned_event(module, &site, &plan, tel);
            apply_tail_call_continuation_plan(module, site, plan, tel);
            changed = true;
            break;
        }
        if changed {
            continue;
        }
        for site in receive_matched_sites {
            if !site.outcomes.iter().all(|outcome| outcome.site_count == 1) {
                continue;
            }
            let Some(plan) = plan_receive_matched_site(module, &site, tel) else {
                continue;
            };
            if !plan.changed {
                continue;
            }
            emit_receive_matched_pruned_event(module, &site, &plan, tel);
            apply_receive_matched_plan(module, site, plan, tel);
            changed = true;
            break;
        }
        if !changed {
            break;
        }
    }
}

fn emit_call_pruned_event(module: &Module, site: &ContinuationSite, plan: &NormalizePlan, tel: &dyn Telemetry) {
    let cont = module.fn_by_id(site.cont.fn_id);
    tel.execute(
        &["fz", "ir", "capture_norm", "captures_pruned"],
        &crate::measurements! {
            fn_id: site.cont.fn_id.0 as u64,
            before_captures: site.cont.captured.len() as u64,
            after_captures: plan.new_captured.len() as u64,
            pruned_captures: site.cont.captured.len().saturating_sub(plan.new_captured.len()) as u64,
            deduplicated_captures: plan.subst.len() as u64,
        },
        &crate::metadata! {
            module_path: module.module_path().to_owned(),
            fn_name: cont.name.clone(),
            producer: site.producer,
        },
    );
}

fn emit_shared_call_pruned_event(
    module: &Module,
    site: &SharedContinuationSite,
    plan: &SharedContinuationPlan,
    tel: &dyn Telemetry,
) {
    let cont = module.fn_by_id(site.cont_fn_id);
    let before = site.sites.first().map(|site| site.cont.captured.len()).unwrap_or(0);
    let after = plan.live_indices.len();
    tel.execute(
        &["fz", "ir", "capture_norm", "captures_pruned"],
        &crate::measurements! {
            fn_id: site.cont_fn_id.0 as u64,
            before_captures: before as u64,
            after_captures: after as u64,
            pruned_captures: before.saturating_sub(after) as u64,
            caller_count: site.sites.len() as u64,
        },
        &crate::metadata! {
            module_path: module.module_path().to_owned(),
            fn_name: cont.name.clone(),
            producer: "shared_call_continuation",
        },
    );
}

fn emit_tail_call_pruned_event(
    module: &Module,
    site: &TailCallContinuationSite,
    plan: &TailCallContinuationPlan,
    tel: &dyn Telemetry,
) {
    let cont = module.fn_by_id(site.callee);
    let before = site.callers.first().map(|caller| caller.args.len()).unwrap_or(0);
    let after = plan.entry_params.len();
    tel.execute(
        &["fz", "ir", "capture_norm", "captures_pruned"],
        &crate::measurements! {
            fn_id: site.callee.0 as u64,
            before_captures: before as u64,
            after_captures: after as u64,
            pruned_captures: before.saturating_sub(after) as u64,
            caller_count: site.callers.len() as u64,
        },
        &crate::metadata! {
            module_path: module.module_path().to_owned(),
            fn_name: cont.name.clone(),
            producer: "tail_call_continuation",
        },
    );
}

fn emit_receive_matched_pruned_event(
    module: &Module,
    site: &ReceiveMatchedSite,
    plan: &ReceiveMatchedPlan,
    tel: &dyn Telemetry,
) {
    let caller = &module.fns[site.caller_fn_idx];
    let deduplicated: usize = plan.outcomes.iter().map(|outcome| outcome.subst.len()).sum();
    tel.execute(
        &["fz", "ir", "capture_norm", "captures_pruned"],
        &crate::measurements! {
            fn_id: caller.id.0 as u64,
            before_captures: site.captures.len() as u64,
            after_captures: plan.new_captured.len() as u64,
            pruned_captures: site.captures.len().saturating_sub(plan.new_captured.len()) as u64,
            deduplicated_captures: deduplicated as u64,
            outcome_count: site.outcomes.len() as u64,
        },
        &crate::metadata! {
            module_path: module.module_path().to_owned(),
            fn_name: caller.name.clone(),
            producer: "receive_matched",
        },
    );
}

#[derive(Debug, Clone)]
struct ContinuationSite {
    caller_fn_idx: usize,
    caller_block_idx: usize,
    cont: Cont,
    producer: &'static str,
    site_count: usize,
}

#[derive(Debug, Clone)]
struct NormalizePlan {
    new_captured: Vec<Var>,
    entry_params: Vec<Var>,
    subst: HashMap<Var, Var>,
    changed: bool,
}

#[derive(Debug, Clone)]
struct SharedContinuationSite {
    cont_fn_id: FnId,
    sites: Vec<ContinuationSite>,
}

#[derive(Debug, Clone)]
struct SharedContinuationPlan {
    live_indices: Vec<usize>,
    entry_params: Vec<Var>,
    changed: bool,
}

#[derive(Debug, Clone)]
struct TailCallContinuationSite {
    callee: FnId,
    callers: Vec<TailCallCaller>,
}

#[derive(Debug, Clone)]
struct TailCallCaller {
    caller_fn_idx: usize,
    caller_block_idx: usize,
    args: Vec<Var>,
}

#[derive(Debug, Clone)]
struct TailCallContinuationPlan {
    entry_params: Vec<Var>,
    ignored_entry_params: Vec<bool>,
    callers: Vec<TailCallCallerPlan>,
    changed: bool,
}

#[derive(Debug, Clone)]
struct TailCallCallerPlan {
    caller_fn_idx: usize,
    caller_block_idx: usize,
    args: Vec<Var>,
}

#[derive(Debug, Clone)]
struct ReceiveMatchedSite {
    caller_fn_idx: usize,
    caller_block_idx: usize,
    captures: Vec<Var>,
    outcomes: Vec<ReceiveOutcome>,
}

#[derive(Debug, Clone)]
struct ReceiveOutcome {
    fn_id: FnId,
    bound_count: usize,
    site_count: usize,
}

#[derive(Debug, Clone)]
struct ReceiveMatchedPlan {
    new_captured: Vec<Var>,
    outcomes: Vec<ReceiveOutcomePlan>,
    changed: bool,
}

#[derive(Debug, Clone)]
struct ReceiveOutcomePlan {
    fn_id: FnId,
    entry_params: Vec<Var>,
    subst: HashMap<Var, Var>,
}

#[derive(Debug, Clone)]
struct ReceiveCaptureGroup {
    outer: Var,
    positions: Vec<ReceiveCapturePosition>,
}

#[derive(Debug, Clone)]
struct ReceiveCapturePosition {
    index: usize,
    used: bool,
}

fn continuation_sites(module: &Module) -> Vec<ContinuationSite> {
    let mut counts: HashMap<FnId, usize> = HashMap::new();
    let mut raw = Vec::new();
    for (fi, f) in module.fns.iter().enumerate() {
        for (bi, block) in f.blocks.iter().enumerate() {
            let (cont, producer) = match &block.terminator {
                Term::Call { continuation, .. } | Term::CallClosure { continuation, .. } => {
                    (continuation.clone(), "call_continuation")
                }
                _ => continue,
            };
            *counts.entry(cont.fn_id).or_insert(0) += 1;
            raw.push((fi, bi, cont, producer));
        }
    }

    raw.into_iter()
        .map(|(caller_fn_idx, caller_block_idx, cont, producer)| ContinuationSite {
            caller_fn_idx,
            caller_block_idx,
            site_count: counts.get(&cont.fn_id).copied().unwrap_or(0),
            cont,
            producer,
        })
        .collect()
}

fn shared_continuation_sites(module: &Module) -> Vec<SharedContinuationSite> {
    let mut by_cont: HashMap<FnId, Vec<ContinuationSite>> = HashMap::new();
    for site in continuation_sites(module) {
        if site.site_count > 1 {
            by_cont.entry(site.cont.fn_id).or_default().push(site);
        }
    }
    by_cont
        .into_iter()
        .map(|(cont_fn_id, sites)| SharedContinuationSite { cont_fn_id, sites })
        .collect()
}

fn tail_call_continuation_sites(module: &Module) -> Vec<TailCallContinuationSite> {
    let mut callers_by_callee: HashMap<FnId, Vec<TailCallCaller>> = HashMap::new();
    for (fi, f) in module.fns.iter().enumerate() {
        for (bi, block) in f.blocks.iter().enumerate() {
            let Term::TailCall {
                callee,
                args,
                is_back_edge,
                ..
            } = &block.terminator
            else {
                continue;
            };
            if *is_back_edge || !is_tail_call_continuation(module, *callee) {
                continue;
            }
            callers_by_callee.entry(*callee).or_default().push(TailCallCaller {
                caller_fn_idx: fi,
                caller_block_idx: bi,
                args: args.clone(),
            });
        }
    }

    callers_by_callee
        .into_iter()
        .map(|(callee, callers)| TailCallContinuationSite { callee, callers })
        .collect()
}

fn is_tail_call_continuation(module: &Module, callee: FnId) -> bool {
    let Some(&idx) = module.fn_idx.get(&callee) else {
        return false;
    };
    matches!(
        module.fns[idx].category,
        FnCategory::ControlFlowCont | FnCategory::MultiClauseCont
    )
}

fn receive_matched_sites(module: &Module) -> Vec<ReceiveMatchedSite> {
    let mut counts: HashMap<FnId, usize> = HashMap::new();
    let mut raw = Vec::new();
    for (fi, f) in module.fns.iter().enumerate() {
        for (bi, block) in f.blocks.iter().enumerate() {
            let Term::ReceiveMatched {
                clauses,
                after,
                captures,
                ..
            } = &block.terminator
            else {
                continue;
            };
            let mut outcomes = Vec::new();
            for clause in clauses {
                outcomes.push((clause.body, clause.bound_names.len()));
                *counts.entry(clause.body).or_insert(0) += 1;
                if let Some(guard) = clause.guard {
                    outcomes.push((guard, clause.bound_names.len()));
                    *counts.entry(guard).or_insert(0) += 1;
                }
            }
            if let Some(after) = after {
                outcomes.push((after.body, 0));
                *counts.entry(after.body).or_insert(0) += 1;
            }
            raw.push((fi, bi, captures.clone(), outcomes));
        }
    }

    raw.into_iter()
        .map(
            |(caller_fn_idx, caller_block_idx, captures, outcomes)| ReceiveMatchedSite {
                caller_fn_idx,
                caller_block_idx,
                captures,
                outcomes: outcomes
                    .into_iter()
                    .map(|(fn_id, bound_count)| ReceiveOutcome {
                        fn_id,
                        bound_count,
                        site_count: counts.get(&fn_id).copied().unwrap_or(0),
                    })
                    .collect(),
            },
        )
        .collect()
}

fn plan_site(module: &Module, site: &ContinuationSite, tel: &dyn Telemetry) -> Option<NormalizePlan> {
    let cont_idx = *module.fn_idx.get(&site.cont.fn_id)?;
    let cont_fn = &module.fns[cont_idx];
    let entry = cont_fn.blocks.iter().find(|b| b.id == cont_fn.entry)?;
    if entry.params.len() != site.cont.captured.len() + 1 {
        return None;
    }
    if site.cont.captured.is_empty() {
        return None;
    }

    let used = live_vars_after_local_dce(cont_fn, tel);
    let captured_params = &entry.params[1..];
    let mut groups: Vec<CaptureGroup> = Vec::new();
    let mut group_by_outer: HashMap<Var, usize> = HashMap::new();

    for (i, (&outer, &param)) in site.cont.captured.iter().zip(captured_params.iter()).enumerate() {
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

fn plan_shared_continuation_site(
    module: &Module,
    site: &SharedContinuationSite,
    tel: &dyn Telemetry,
) -> Option<SharedContinuationPlan> {
    let cont_idx = *module.fn_idx.get(&site.cont_fn_id)?;
    let cont_fn = &module.fns[cont_idx];
    let entry = cont_fn.blocks.iter().find(|b| b.id == cont_fn.entry)?;
    let first = site.sites.first()?;
    let captured_len = first.cont.captured.len();
    if captured_len == 0 || entry.params.len() != captured_len + 1 {
        return None;
    }
    if site.sites.iter().any(|site| site.cont.captured.len() != captured_len) {
        return None;
    }

    let used = live_vars_after_local_dce(cont_fn, tel);
    let live_indices: Vec<usize> = entry.params[1..]
        .iter()
        .enumerate()
        .filter_map(|(i, param)| used.contains(param).then_some(i))
        .collect();
    if live_indices.len() == captured_len {
        return None;
    }

    let mut entry_params = Vec::with_capacity(1 + live_indices.len());
    entry_params.push(entry.params[0]);
    entry_params.extend(live_indices.iter().map(|&i| entry.params[i + 1]));
    Some(SharedContinuationPlan {
        live_indices,
        entry_params,
        changed: true,
    })
}

fn plan_tail_call_continuation_site(
    module: &Module,
    site: &TailCallContinuationSite,
    tel: &dyn Telemetry,
) -> Option<TailCallContinuationPlan> {
    let callee_idx = *module.fn_idx.get(&site.callee)?;
    let callee = &module.fns[callee_idx];
    let entry = callee.blocks.iter().find(|b| b.id == callee.entry)?;
    if entry.params.is_empty() || site.callers.is_empty() {
        return None;
    }
    if site
        .callers
        .iter()
        .any(|caller| caller.args.len() != entry.params.len())
    {
        return None;
    }

    let used = live_vars_after_local_dce(callee, tel);
    let live_indices: Vec<usize> = entry
        .params
        .iter()
        .enumerate()
        .filter_map(|(i, param)| used.contains(param).then_some(i))
        .collect();
    if live_indices.len() == entry.params.len() {
        return None;
    }

    let entry_params = live_indices.iter().map(|&i| entry.params[i]).collect();
    let ignored_entry_params = live_indices
        .iter()
        .map(|&i| callee.ignored_entry_params.get(i).copied().unwrap_or(false))
        .collect();
    let callers = site
        .callers
        .iter()
        .map(|caller| TailCallCallerPlan {
            caller_fn_idx: caller.caller_fn_idx,
            caller_block_idx: caller.caller_block_idx,
            args: live_indices.iter().map(|&i| caller.args[i]).collect(),
        })
        .collect();

    Some(TailCallContinuationPlan {
        entry_params,
        ignored_entry_params,
        callers,
        changed: true,
    })
}

fn plan_receive_matched_site(
    module: &Module,
    site: &ReceiveMatchedSite,
    tel: &dyn Telemetry,
) -> Option<ReceiveMatchedPlan> {
    if site.captures.is_empty() {
        return None;
    }

    let mut outcome_entries = Vec::new();
    let mut used_by_outcome = Vec::new();
    for outcome in &site.outcomes {
        let fn_idx = *module.fn_idx.get(&outcome.fn_id)?;
        let f = &module.fns[fn_idx];
        let entry = f.blocks.iter().find(|b| b.id == f.entry)?;
        if entry.params.len() != outcome.bound_count + site.captures.len() {
            return None;
        }
        outcome_entries.push((outcome.fn_id, outcome.bound_count, entry.params.clone()));
        used_by_outcome.push(live_vars_after_local_dce(f, tel));
    }

    let mut groups: Vec<ReceiveCaptureGroup> = Vec::new();
    let mut group_by_outer: HashMap<Var, usize> = HashMap::new();
    for (i, &outer) in site.captures.iter().enumerate() {
        let group_idx = match group_by_outer.get(&outer).copied() {
            Some(idx) => idx,
            None => {
                let idx = groups.len();
                group_by_outer.insert(outer, idx);
                groups.push(ReceiveCaptureGroup {
                    outer,
                    positions: Vec::new(),
                });
                idx
            }
        };
        let used = outcome_entries
            .iter()
            .zip(&used_by_outcome)
            .any(|((_, bound_count, params), used)| used.contains(&params[*bound_count + i]));
        groups[group_idx]
            .positions
            .push(ReceiveCapturePosition { index: i, used });
    }

    let mut representative_index: HashMap<usize, usize> = HashMap::new();
    let mut new_captured = Vec::new();
    for group in groups {
        if !group.positions.iter().any(|pos| pos.used) {
            continue;
        }
        let representative = group.positions[0].index;
        for pos in &group.positions {
            representative_index.insert(pos.index, representative);
        }
        new_captured.push(group.outer);
    }

    let mut outcome_plans = Vec::new();
    for (fn_id, bound_count, params) in outcome_entries {
        let mut entry_params = Vec::with_capacity(bound_count + new_captured.len());
        entry_params.extend_from_slice(&params[..bound_count]);

        let mut representative_by_outer: HashMap<Var, Var> = HashMap::new();
        let mut subst = HashMap::new();
        for (i, &outer) in site.captures.iter().enumerate() {
            let param = params[bound_count + i];
            let Some(&representative_index) = representative_index.get(&i) else {
                continue;
            };
            if i == representative_index {
                representative_by_outer.insert(outer, param);
                entry_params.push(param);
            } else if let Some(representative) = representative_by_outer.get(&outer).copied() {
                subst.insert(param, representative);
            }
        }
        outcome_plans.push(ReceiveOutcomePlan {
            fn_id,
            entry_params,
            subst,
        });
    }

    let changed = new_captured != site.captures || outcome_plans.iter().any(|plan| !plan.subst.is_empty());
    Some(ReceiveMatchedPlan {
        new_captured,
        outcomes: outcome_plans,
        changed,
    })
}

fn live_vars_after_local_dce(f: &FnIr, tel: &dyn Telemetry) -> HashSet<Var> {
    let mut pruned = f.clone();
    dce_fn("", &mut pruned, tel);
    collect_used(&pruned)
}

fn subst_physical_entry_params(f: &mut FnIr, subst: &HashMap<Var, Var>) {
    f.physical_entry_params = f
        .physical_entry_params
        .iter()
        .map(|param| subst.get(param).copied().unwrap_or(*param))
        .collect();
    f.physical_capabilities = f
        .physical_capabilities
        .iter()
        .map(|fact| fact.map_vars(|var| subst.get(&var).copied().unwrap_or(var)))
        .collect();
    f.dedup_physical_facts();
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

fn apply_plan(module: &mut Module, site: ContinuationSite, plan: NormalizePlan, tel: &dyn Telemetry) {
    let cont_idx = *module.fn_idx.get(&site.cont.fn_id).expect("continuation fn exists");
    let cont_fn = &mut module.fns[cont_idx];
    if !plan.subst.is_empty() {
        for block in &mut cont_fn.blocks {
            let stmts: Vec<Stmt> = block.stmts.iter().map(|stmt| subst_stmt(stmt, &plan.subst)).collect();
            block.stmts = stmts;
            block.terminator = subst_term(&block.terminator, &plan.subst);
        }
        subst_physical_entry_params(cont_fn, &plan.subst);
    }
    let entry = cont_fn
        .blocks
        .iter_mut()
        .find(|block| block.id == cont_fn.entry)
        .expect("continuation entry block exists");
    entry.params = plan.entry_params;
    cont_fn.ignored_entry_params = vec![false; entry.params.len()];
    dce_fn("", cont_fn, tel);

    let term = &mut module.fns[site.caller_fn_idx].blocks[site.caller_block_idx].terminator;
    match term {
        Term::Call { continuation, .. } | Term::CallClosure { continuation, .. } => {
            continuation.captured = plan.new_captured;
        }
        _ => unreachable!("captured site no longer points at a continuation term"),
    }
}

fn apply_shared_continuation_plan(
    module: &mut Module,
    site: SharedContinuationSite,
    plan: SharedContinuationPlan,
    tel: &dyn Telemetry,
) {
    let cont_idx = *module
        .fn_idx
        .get(&site.cont_fn_id)
        .expect("shared continuation fn exists");
    let cont_fn = &mut module.fns[cont_idx];
    let entry = cont_fn
        .blocks
        .iter_mut()
        .find(|block| block.id == cont_fn.entry)
        .expect("shared continuation entry block exists");
    entry.params = plan.entry_params;
    cont_fn.ignored_entry_params = vec![false; entry.params.len()];
    dce_fn("", cont_fn, tel);

    for call_site in site.sites {
        let term = &mut module.fns[call_site.caller_fn_idx].blocks[call_site.caller_block_idx].terminator;
        let new_captured: Vec<Var> = plan.live_indices.iter().map(|&i| call_site.cont.captured[i]).collect();
        match term {
            Term::Call { continuation, .. } | Term::CallClosure { continuation, .. } => {
                continuation.captured = new_captured;
            }
            _ => unreachable!("shared captured site no longer points at a continuation term"),
        }
    }
}

fn apply_tail_call_continuation_plan(
    module: &mut Module,
    site: TailCallContinuationSite,
    plan: TailCallContinuationPlan,
    tel: &dyn Telemetry,
) {
    let callee_idx = *module
        .fn_idx
        .get(&site.callee)
        .expect("tail-call continuation fn exists");
    let callee = &mut module.fns[callee_idx];
    let entry = callee
        .blocks
        .iter_mut()
        .find(|block| block.id == callee.entry)
        .expect("tail-call continuation entry block exists");
    entry.params = plan.entry_params;
    callee.ignored_entry_params = plan.ignored_entry_params;
    dce_fn("", callee, tel);

    for caller in plan.callers {
        let term = &mut module.fns[caller.caller_fn_idx].blocks[caller.caller_block_idx].terminator;
        let Term::TailCall { args, .. } = term else {
            unreachable!("tail-call continuation site no longer points at TailCall")
        };
        *args = caller.args;
    }
}

fn apply_receive_matched_plan(
    module: &mut Module,
    site: ReceiveMatchedSite,
    plan: ReceiveMatchedPlan,
    tel: &dyn Telemetry,
) {
    for outcome in plan.outcomes {
        let fn_idx = *module.fn_idx.get(&outcome.fn_id).expect("receive outcome fn exists");
        let f = &mut module.fns[fn_idx];
        if !outcome.subst.is_empty() {
            for block in &mut f.blocks {
                let stmts: Vec<Stmt> = block
                    .stmts
                    .iter()
                    .map(|stmt| subst_stmt(stmt, &outcome.subst))
                    .collect();
                block.stmts = stmts;
                block.terminator = subst_term(&block.terminator, &outcome.subst);
            }
            subst_physical_entry_params(f, &outcome.subst);
        }
        let entry = f
            .blocks
            .iter_mut()
            .find(|block| block.id == f.entry)
            .expect("receive outcome entry block exists");
        entry.params = outcome.entry_params;
        f.ignored_entry_params = vec![false; entry.params.len()];
        dce_fn("", f, tel);
    }

    let term = &mut module.fns[site.caller_fn_idx].blocks[site.caller_block_idx].terminator;
    let Term::ReceiveMatched { captures, .. } = term else {
        unreachable!("receive matched site no longer points at ReceiveMatched")
    };
    *captures = plan.new_captured;
}

#[cfg(test)]
mod ir_capture_norm_test;
