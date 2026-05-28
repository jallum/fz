//! Normalize continuation captures after lowering.
//!
//! Lowering emits capture candidates while it splits source expressions into
//! CPS continuations. This pass is the canonical boundary that turns those
//! candidates into the ABI: a continuation captures each caller `Var` at most
//! once, and only when the continuation body actually reads the corresponding
//! entry param.

use crate::fz_ir::{Cont, FnId, Module, Stmt, Term, Var};
use crate::ir_dce::{classify_var_uses, dce_fn_with_telemetry};
use crate::ir_fuse::{subst_stmt, subst_term};
use std::collections::{HashMap, HashSet};

pub fn normalize_continuation_captures_with_telemetry(
    module: &mut Module,
    tel: &dyn crate::telemetry::Telemetry,
) {
    loop {
        let sites = continuation_sites(module);
        let tail_call_sites = tail_call_continuation_sites(module);
        let receive_matched_sites = receive_matched_sites(module);
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
            emit_call_pruned_event(module, &site, &plan, tel);
            apply_plan(module, site, plan);
            changed = true;
            break;
        }
        if changed {
            continue;
        }
        for site in shared_continuation_sites(module) {
            let Some(plan) = plan_shared_continuation_site(module, &site) else {
                continue;
            };
            if !plan.changed {
                continue;
            }
            emit_shared_call_pruned_event(module, &site, &plan, tel);
            apply_shared_continuation_plan(module, site, plan);
            changed = true;
            break;
        }
        if changed {
            continue;
        }
        for site in tail_call_sites {
            let Some(plan) = plan_tail_call_continuation_site(module, &site) else {
                continue;
            };
            if !plan.changed {
                continue;
            }
            emit_tail_call_pruned_event(module, &site, &plan, tel);
            apply_tail_call_continuation_plan(module, site, plan);
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
            let Some(plan) = plan_receive_matched_site(module, &site) else {
                continue;
            };
            if !plan.changed {
                continue;
            }
            emit_receive_matched_pruned_event(module, &site, &plan, tel);
            apply_receive_matched_plan(module, site, plan);
            changed = true;
            break;
        }
        if !changed {
            break;
        }
    }
}

fn emit_call_pruned_event(
    module: &Module,
    site: &ContinuationSite,
    plan: &NormalizePlan,
    tel: &dyn crate::telemetry::Telemetry,
) {
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
    tel: &dyn crate::telemetry::Telemetry,
) {
    let cont = module.fn_by_id(site.cont_fn_id);
    let before = site
        .sites
        .first()
        .map(|site| site.cont.captured.len())
        .unwrap_or(0);
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
    tel: &dyn crate::telemetry::Telemetry,
) {
    let cont = module.fn_by_id(site.callee);
    let before = site
        .callers
        .first()
        .map(|caller| caller.args.len())
        .unwrap_or(0);
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
    tel: &dyn crate::telemetry::Telemetry,
) {
    let caller = &module.fns[site.caller_fn_idx];
    let deduplicated: usize = plan
        .outcomes
        .iter()
        .map(|outcome| outcome.subst.len())
        .sum();
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
                Term::Receive { continuation, .. } => {
                    (continuation.clone(), "receive_continuation")
                }
                _ => continue,
            };
            *counts.entry(cont.fn_id).or_insert(0) += 1;
            raw.push((fi, bi, cont, producer));
        }
    }

    raw.into_iter()
        .map(
            |(caller_fn_idx, caller_block_idx, cont, producer)| ContinuationSite {
                caller_fn_idx,
                caller_block_idx,
                site_count: counts.get(&cont.fn_id).copied().unwrap_or(0),
                cont,
                producer,
            },
        )
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
            callers_by_callee
                .entry(*callee)
                .or_default()
                .push(TailCallCaller {
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
        crate::fz_ir::FnCategory::ControlFlowCont | crate::fz_ir::FnCategory::MultiClauseCont
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

    let used = live_vars_after_local_dce(cont_fn);
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

fn plan_shared_continuation_site(
    module: &Module,
    site: &SharedContinuationSite,
) -> Option<SharedContinuationPlan> {
    let cont_idx = *module.fn_idx.get(&site.cont_fn_id)?;
    let cont_fn = &module.fns[cont_idx];
    let entry = cont_fn.blocks.iter().find(|b| b.id == cont_fn.entry)?;
    let first = site.sites.first()?;
    let captured_len = first.cont.captured.len();
    if captured_len == 0 || entry.params.len() != captured_len + 1 {
        return None;
    }
    if site
        .sites
        .iter()
        .any(|site| site.cont.captured.len() != captured_len)
    {
        return None;
    }

    let used = live_vars_after_local_dce(cont_fn);
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

    let used = live_vars_after_local_dce(callee);
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
        used_by_outcome.push(live_vars_after_local_dce(f));
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

    let changed =
        new_captured != site.captures || outcome_plans.iter().any(|plan| !plan.subst.is_empty());
    Some(ReceiveMatchedPlan {
        new_captured,
        outcomes: outcome_plans,
        changed,
    })
}

fn live_vars_after_local_dce(f: &crate::fz_ir::FnIr) -> HashSet<Var> {
    let mut pruned = f.clone();
    let credits = pruned.owned_cons_reuse_credits.clone();
    pruned.owned_cons_reuse_credits.clear();
    dce_fn_with_telemetry("", &mut pruned, &crate::telemetry::NullTelemetry);
    let mut used = classify_var_uses(&pruned).1;
    for credit in credits {
        if used.contains(&credit.head) {
            used.insert(credit.source_cons);
        }
    }
    used
}

fn dce_after_capture_prune(f: &mut crate::fz_ir::FnIr) {
    let credits = std::mem::take(&mut f.owned_cons_reuse_credits);
    dce_fn_with_telemetry("", f, &crate::telemetry::NullTelemetry);
    let semantically_used = classify_var_uses(f).1;
    f.owned_cons_reuse_credits = credits
        .into_iter()
        .filter(|credit| semantically_used.contains(&credit.head))
        .collect();
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
    dce_after_capture_prune(cont_fn);

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

fn apply_shared_continuation_plan(
    module: &mut Module,
    site: SharedContinuationSite,
    plan: SharedContinuationPlan,
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
    dce_after_capture_prune(cont_fn);

    for call_site in site.sites {
        let term =
            &mut module.fns[call_site.caller_fn_idx].blocks[call_site.caller_block_idx].terminator;
        let new_captured: Vec<Var> = plan
            .live_indices
            .iter()
            .map(|&i| call_site.cont.captured[i])
            .collect();
        match term {
            Term::Call { continuation, .. }
            | Term::CallClosure { continuation, .. }
            | Term::Receive { continuation, .. } => {
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
    dce_after_capture_prune(callee);

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
) {
    for outcome in plan.outcomes {
        let fn_idx = *module
            .fn_idx
            .get(&outcome.fn_id)
            .expect("receive outcome fn exists");
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
        }
        let entry = f
            .blocks
            .iter_mut()
            .find(|block| block.id == f.entry)
            .expect("receive outcome entry block exists");
        entry.params = outcome.entry_params;
        f.ignored_entry_params = vec![false; entry.params.len()];
        dce_after_capture_prune(f);
    }

    let term = &mut module.fns[site.caller_fn_idx].blocks[site.caller_block_idx].terminator;
    let Term::ReceiveMatched { captures, .. } = term else {
        unreachable!("receive matched site no longer points at ReceiveMatched")
    };
    *captures = plan.new_captured;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{
        BinOp, BlockId, Const, FnBuilder, FnId, ModuleBuilder, Prim, ReceiveAfter, ReceiveClause,
    };
    use crate::matcher::{Matcher, MatcherLeaf, MatcherNode};
    use crate::telemetry::Value;
    use std::sync::Arc;

    fn build_module_with_call_cont(
        captured: Vec<Var>,
        captured_params: Vec<Var>,
        used: Var,
    ) -> Module {
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

    fn build_module_with_receive_cont(
        captured: Vec<Var>,
        captured_params: Vec<Var>,
        used: Var,
    ) -> Module {
        let caller_id = FnId(0);
        let cont_id = FnId(1);

        let mut caller = FnBuilder::new(caller_id, "receiver");
        let entry = caller.block(vec![]);
        caller.set_terminator(
            entry,
            Term::Receive {
                ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
                continuation: Cont {
                    fn_id: cont_id,
                    captured,
                },
            },
        );

        let mut cont =
            FnBuilder::new(cont_id, "k_receive_1").with_category(crate::fz_ir::FnCategory::CpsCont);
        let message = Var(0);
        let mut params = vec![message];
        params.extend(captured_params);
        let entry = cont.block(params);
        cont.set_terminator(entry, Term::Return(used));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(caller.build());
        mb.add_fn(cont.build());
        mb.build()
    }

    fn build_module_with_callclosure_dead_transitive_capture() -> Module {
        let caller_id = FnId(0);
        let cont_id = FnId(1);

        let mut caller = FnBuilder::new(caller_id, "caller");
        let entry = caller.block(vec![]);
        let closure = caller.let_(entry, Prim::Const(Const::Atom(1)));
        let arg = caller.let_(entry, Prim::Const(Const::Int(0)));
        caller.set_terminator(
            entry,
            Term::CallClosure {
                ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
                closure,
                args: vec![arg],
                continuation: Cont {
                    fn_id: cont_id,
                    captured: vec![Var(10), Var(11)],
                },
            },
        );

        let mut cont =
            FnBuilder::new(cont_id, "k_resume").with_category(crate::fz_ir::FnCategory::CpsCont);
        let result = cont.fresh_var();
        let live = cont.fresh_var();
        let dead = cont.fresh_var();
        let entry = cont.block(vec![result, live, dead]);
        let _unused = cont.let_(entry, Prim::BinOp(BinOp::Add, dead, result));
        cont.set_terminator(entry, Term::Return(live));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(caller.build());
        mb.add_fn(cont.build());
        mb.build()
    }

    fn build_module_with_shared_cont_site() -> Module {
        let cont_id = FnId(2);
        let mut mb = ModuleBuilder::new();

        for caller_raw in [0, 1] {
            let caller_id = FnId(caller_raw);
            let mut caller = FnBuilder::new(caller_id, format!("caller_{}", caller_raw));
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
                        captured: vec![Var(10), Var(11)],
                    },
                },
            );
            mb.add_fn(caller.build());
        }

        let mut cont =
            FnBuilder::new(cont_id, "shared_k").with_category(crate::fz_ir::FnCategory::CpsCont);
        let entry = cont.block(vec![Var(0), Var(1), Var(2)]);
        cont.set_terminator(entry, Term::Return(Var(2)));
        mb.add_fn(cont.build());
        mb.build()
    }

    fn build_module_with_tail_call_cont_site() -> Module {
        let cont_id = FnId(2);
        let mut mb = ModuleBuilder::new();

        for (caller_raw, live_arg, dead_arg) in [(0, Var(10), Var(11)), (1, Var(20), Var(21))] {
            let caller_id = FnId(caller_raw);
            let mut caller = FnBuilder::new(caller_id, format!("branch_{}", caller_raw));
            let entry = caller.block(vec![]);
            caller.set_terminator(
                entry,
                Term::TailCall {
                    ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
                    callee: cont_id,
                    args: vec![live_arg, dead_arg],
                    is_back_edge: false,
                },
            );
            mb.add_fn(caller.build());
        }

        let mut cont = FnBuilder::new(cont_id, "if_join")
            .with_category(crate::fz_ir::FnCategory::ControlFlowCont);
        let entry = cont.block(vec![Var(0), Var(1)]);
        cont.set_terminator(entry, Term::Return(Var(0)));
        mb.add_fn(cont.build());
        mb.build()
    }

    fn empty_matcher() -> Arc<Matcher> {
        Arc::new(Matcher::new(
            vec![],
            MatcherNode::Leaf(MatcherLeaf {
                body_id: 0,
                bindings: vec![],
                span: crate::diag::Span::DUMMY,
            }),
        ))
    }

    fn build_module_with_receive_matched(captures: Vec<Var>) -> Module {
        let mut caller = FnBuilder::new(FnId(0), "receiver");
        let entry = caller.block(vec![]);
        caller.set_terminator(
            entry,
            Term::ReceiveMatched {
                ident: crate::fz_ir::CallsiteIdent::from_source(crate::diag::Span::DUMMY),
                clauses: vec![ReceiveClause {
                    bound_names: vec!["msg".to_string()],
                    guard: None,
                    body: FnId(1),
                    span: crate::diag::Span::DUMMY,
                }],
                matcher: empty_matcher(),
                after: Some(ReceiveAfter {
                    timeout: Var(99),
                    body: FnId(2),
                    span: crate::diag::Span::DUMMY,
                }),
                pinned: vec![],
                captures,
            },
        );

        let mut body =
            FnBuilder::new(FnId(1), "rx_body").with_category(crate::fz_ir::FnCategory::CpsCont);
        let entry = body.block(vec![Var(0), Var(1), Var(2)]);
        body.set_terminator(entry, Term::Return(Var(0)));

        let mut after =
            FnBuilder::new(FnId(2), "rx_after").with_category(crate::fz_ir::FnCategory::CpsCont);
        let entry = after.block(vec![Var(3), Var(4)]);
        after.set_terminator(entry, Term::Return(Var(4)));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(caller.build());
        mb.add_fn(body.build());
        mb.add_fn(after.build());
        mb.build()
    }

    fn normalize_with_capture(module: &mut Module) -> crate::telemetry::Capture {
        let tel = crate::telemetry::ConfiguredTelemetry::new();
        let cap = crate::telemetry::Capture::new();
        tel.attach(&[], cap.handler());
        normalize_continuation_captures_with_telemetry(module, &tel);
        cap
    }

    fn assert_pruned_event(
        cap: &crate::telemetry::Capture,
        producer: &str,
        before: u64,
        after: u64,
        pruned: u64,
    ) -> crate::telemetry::capture::OwnedEvent {
        let ev = cap
            .last(&["fz", "ir", "capture_norm", "captures_pruned"])
            .expect("captures_pruned event");
        assert!(matches!(
            ev.metadata.get("producer"),
            Some(Value::Str(s)) if s.as_ref() == producer
        ));
        assert!(matches!(
            ev.measurements.get("before_captures"),
            Some(Value::U64(n)) if *n == before
        ));
        assert!(matches!(
            ev.measurements.get("after_captures"),
            Some(Value::U64(n)) if *n == after
        ));
        assert!(matches!(
            ev.measurements.get("pruned_captures"),
            Some(Value::U64(n)) if *n == pruned
        ));
        ev
    }

    #[test]
    fn drops_unused_continuation_captures() {
        let mut module =
            build_module_with_call_cont(vec![Var(10), Var(11)], vec![Var(1), Var(2)], Var(2));

        let cap = normalize_with_capture(&mut module);
        let ev = assert_pruned_event(&cap, "call_continuation", 2, 1, 1);
        assert!(matches!(
            ev.measurements.get("deduplicated_captures"),
            Some(Value::U64(0))
        ));

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
            build_module_with_call_cont(vec![Var(10), Var(10)], vec![Var(1), Var(2)], Var(2));

        let cap = normalize_with_capture(&mut module);
        let ev = assert_pruned_event(&cap, "call_continuation", 2, 1, 1);
        assert!(matches!(
            ev.measurements.get("deduplicated_captures"),
            Some(Value::U64(1))
        ));

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

    #[test]
    fn normalizes_receive_continuation_captures() {
        let mut module =
            build_module_with_receive_cont(vec![Var(10), Var(11)], vec![Var(1), Var(2)], Var(0));

        let cap = normalize_with_capture(&mut module);
        assert_pruned_event(&cap, "receive_continuation", 2, 0, 2);

        let caller = module.fn_by_id(FnId(0));
        let Term::Receive { continuation, .. } = &caller.block(BlockId(0)).terminator else {
            panic!("expected receive terminator");
        };
        assert!(continuation.captured.is_empty());

        let cont = module.fn_by_id(FnId(1));
        assert_eq!(cont.block(BlockId(0)).params, vec![Var(0)]);
    }

    #[test]
    fn prunes_dead_positions_from_shared_continuation_sites() {
        let mut module = build_module_with_shared_cont_site();

        let cap = normalize_with_capture(&mut module);
        let ev = assert_pruned_event(&cap, "shared_call_continuation", 2, 1, 1);
        assert!(matches!(
            ev.measurements.get("caller_count"),
            Some(Value::U64(2))
        ));

        for caller_id in [FnId(0), FnId(1)] {
            let caller = module.fn_by_id(caller_id);
            let Term::Call { continuation, .. } = &caller.block(BlockId(0)).terminator else {
                panic!("expected call terminator");
            };
            assert_eq!(continuation.captured, vec![Var(11)]);
        }

        let cont = module.fn_by_id(FnId(2));
        assert_eq!(cont.block(BlockId(0)).params, vec![Var(0), Var(2)]);
    }

    #[test]
    fn leaves_shared_continuation_sites_unchanged_when_all_positions_live() {
        let mut module = build_module_with_shared_cont_site();
        {
            let cont_idx = *module.fn_idx.get(&FnId(2)).expect("cont exists");
            let cont = &mut module.fns[cont_idx];
            let block = cont
                .blocks
                .iter_mut()
                .find(|block| block.id == BlockId(0))
                .expect("entry block exists");
            block
                .stmts
                .push(Stmt::Let(Var(3), Prim::BinOp(BinOp::Add, Var(1), Var(2))));
            block.terminator = Term::Return(Var(3));
        }

        let cap = normalize_with_capture(&mut module);
        assert_eq!(
            cap.count(&["fz", "ir", "capture_norm", "captures_pruned"]),
            0
        );

        for caller_id in [FnId(0), FnId(1)] {
            let caller = module.fn_by_id(caller_id);
            let Term::Call { continuation, .. } = &caller.block(BlockId(0)).terminator else {
                panic!("expected call terminator");
            };
            assert_eq!(continuation.captured, vec![Var(10), Var(11)]);
        }

        let cont = module.fn_by_id(FnId(2));
        assert_eq!(cont.block(BlockId(0)).params, vec![Var(0), Var(1), Var(2)]);
    }

    #[test]
    fn prunes_callclosure_capture_used_only_by_dead_pure_stmt() {
        let mut module = build_module_with_callclosure_dead_transitive_capture();

        let cap = normalize_with_capture(&mut module);
        let ev = assert_pruned_event(&cap, "call_continuation", 2, 1, 1);
        assert!(matches!(
            ev.measurements.get("deduplicated_captures"),
            Some(Value::U64(0))
        ));

        let caller = module.fn_by_id(FnId(0));
        let Term::CallClosure { continuation, .. } = &caller.block(BlockId(0)).terminator else {
            panic!("expected call-closure terminator");
        };
        assert_eq!(continuation.captured, vec![Var(10)]);

        let cont = module.fn_by_id(FnId(1));
        assert_eq!(cont.block(BlockId(0)).params, vec![Var(0), Var(1)]);
    }

    #[test]
    fn normalizes_tail_call_continuation_args_across_all_callers() {
        let mut module = build_module_with_tail_call_cont_site();

        let cap = normalize_with_capture(&mut module);
        let ev = assert_pruned_event(&cap, "tail_call_continuation", 2, 1, 1);
        assert!(matches!(
            ev.measurements.get("caller_count"),
            Some(Value::U64(2))
        ));

        for (caller_id, expected_arg) in [(FnId(0), Var(10)), (FnId(1), Var(20))] {
            let caller = module.fn_by_id(caller_id);
            let Term::TailCall { args, .. } = &caller.block(BlockId(0)).terminator else {
                panic!("expected tail-call terminator");
            };
            assert_eq!(args, &vec![expected_arg]);
        }

        let cont = module.fn_by_id(FnId(2));
        assert_eq!(cont.block(BlockId(0)).params, vec![Var(0)]);
    }

    #[test]
    fn normalizes_receive_matched_shared_captures() {
        let mut module = build_module_with_receive_matched(vec![Var(10), Var(11)]);

        let cap = normalize_with_capture(&mut module);
        let ev = assert_pruned_event(&cap, "receive_matched", 2, 1, 1);
        assert!(matches!(
            ev.measurements.get("outcome_count"),
            Some(Value::U64(2))
        ));

        let caller = module.fn_by_id(FnId(0));
        let Term::ReceiveMatched { captures, .. } = &caller.block(BlockId(0)).terminator else {
            panic!("expected receive matched terminator");
        };
        assert_eq!(captures, &vec![Var(11)]);

        let body = module.fn_by_id(FnId(1));
        assert_eq!(body.block(BlockId(0)).params, vec![Var(0), Var(2)]);

        let after = module.fn_by_id(FnId(2));
        assert_eq!(after.block(BlockId(0)).params, vec![Var(4)]);
    }
}
