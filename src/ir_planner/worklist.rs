use super::closures::resolve_closure_return;
use super::diagnostics::{compute_dead_branches, module_type_stats};
use super::fn_types::{
    CallsiteFnConsts, EffectSummary, EmitsByCaller, EmitterSiteSet, HoldersMap, ModulePlan,
    PLAN_MODULE_CALLS, ProducesMap, ReturnReaders, SpecKey, SpecKeySet, SpecPlan, TYPE_FN_CALLS,
    VISIT_HARD_BOUND, WALK_CALLS, WORKLIST_POPS, build_any_key_index, key_precedence_order,
    recursive_direct_spec_key, spec_key_for_fn_id, spec_key_input_tys,
};
use super::reachable::env_at_terminator;
use super::type_fn::type_fn;
use super::walk::{WalkResult, walk_spec_for_discovery};
use crate::fz_ir::{Block, FnId, Module, Prim, Term};
use crate::ir_callgraph::{build_call_graph, entry_seeds};
use std::collections::HashMap;

/// fz-5j5.3 — type a module via one worklist over `(FnId, Vec<crate::types::Ty>)`
/// specs. The worklist drives spec registration, body typing, and
/// effective-return propagation as a single unified data-flow LFP.
///
/// Two triggers add a spec back to the worklist:
///   1. The spec is freshly discovered (newly-emitted pending key).
///   2. A callee whose effective return this spec reads has *changed*
///      that return. Tracked via the `return_readers` reverse index
///      populated during walks at every cont-site slot-0 lookup.
///
/// `type_fn` is pure in `(FnIr, entry_key)`; once a spec's `SpecPlan`
/// is computed, it's cached and reused across worklist visits — only
/// the walk + return-recompute re-run when triggered.
///
/// MakeClosure-side any-key registration is folded in as a separate
/// post-drain sweep (it depends on the converged `opaque_consumer_arities`,
/// a global computation). After the sweep enqueues any-keys for
/// opaque-consumed lambdas, the worklist re-drains; over-specialized
/// stale specs that the walks accumulate are pruned by a final
/// reachability sweep keyed off the converged effective_returns.
///
/// ## Termination (fz-rh5.7)
///
/// The worklist terminates because:
///
///   (a) `effective_returns` is updated only via `union`,
///       which is monotone w.r.t. lattice inclusion. So
///       `effective_returns` is monotonically non-decreasing in
///       the product type lattice.
///
///   (b) The type lattice has finite height H, bounded by the
///       count of distinct type-axis values in the program
///       (atoms, ints, floats, tuple shapes, list shapes, etc —
///       all finite for a closed program).
///
///   (c) A spec is enqueued only on:
///         (i)   First emission — happens at most once per spec key.
///         (ii)  A callee's effective return that this spec reads
///               has changed — happens at most H× per
///               (spec, return-edge) pair, by (a) and (b).
///
///   (d) SCC-internal recursive direct-call spec keys are normalized
///       immediately via recursive spec-key widening. Numeric literal
///       chains therefore collapse at the recursive boundary instead of
///       depending on traversal timing.
///
/// Therefore total worklist pops is bounded by
///   O(|specs| · (1 + H · |return-edges per spec|))
/// which is finite. `VISIT_HARD_BOUND` below is a debug-only
/// tripwire for invariant violation, NOT a release safety net.
pub fn plan_module<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    m: &Module,
    tel: &dyn crate::telemetry::Telemetry,
) -> ModulePlan {
    // fz-mm2.7 — verified: body has no direct concrete operations. The seam
    // handle is threaded into the worklist driver (process_worklist),
    // which fans it out to type_fn and the per-call typing work.
    PLAN_MODULE_CALLS.with(|c| c.set(c.get() + 1));
    WORKLIST_POPS.with(|c| c.set(0));
    TYPE_FN_CALLS.with(|c| c.set(0));
    WALK_CALLS.with(|c| c.set(0));

    let call_graph = build_call_graph(m);
    let mut sccs = super::scc::tarjan_scc(&call_graph);
    sccs.reverse();
    let mut scc_of: HashMap<FnId, usize> = HashMap::new();
    for (i, scc) in sccs.iter().enumerate() {
        for fid in scc {
            scc_of.insert(*fid, i);
        }
    }
    let mut recursive_fns: std::collections::HashSet<FnId> = std::collections::HashSet::new();
    for scc in &sccs {
        if scc.len() > 1 {
            recursive_fns.extend(scc.iter().copied());
        } else if let Some(fid) = scc.first()
            && call_graph.get(fid).is_some_and(|succs| succs.contains(fid))
        {
            recursive_fns.insert(*fid);
        }
    }

    let mut specs: HashMap<SpecKey, SpecPlan> = HashMap::new();
    let mut effective_returns: HashMap<SpecKey, crate::types::Ty> = HashMap::new();
    let mut callsite_fn_consts: CallsiteFnConsts = HashMap::new();
    let mut return_readers: ReturnReaders = HashMap::new();
    let mut visit_count: HashMap<SpecKey, usize> = HashMap::new();

    // fz-rh5.6 — provenance state.
    let mut produces: ProducesMap = HashMap::new();
    let mut holders: HoldersMap = HashMap::new();
    let mut emits_by_caller: EmitsByCaller = HashMap::new();
    let mut closure_handles: std::collections::HashSet<(FnId, Vec<crate::types::Ty>)> =
        std::collections::HashSet::new();

    let mut work: std::collections::VecDeque<SpecKey> = entry_seeds(t, m)
        .into_iter()
        .map(|(fid, key)| spec_key_for_fn_id(m, fid, key))
        .collect();
    let mut in_work: SpecKeySet = work.iter().cloned().collect();

    process_worklist(
        t,
        m,
        &recursive_fns,
        &mut work,
        &mut in_work,
        &mut specs,
        &mut effective_returns,
        &mut callsite_fn_consts,
        &mut return_readers,
        &mut visit_count,
        &mut produces,
        &mut holders,
        &mut emits_by_caller,
        &mut closure_handles,
    );

    // Forward reachability from entry_seeds via emits_by_caller +
    // produces. Specs not reached are orphans — their holders chain
    // ends in a spec that itself fell out of reach, or they form a
    // recursive cycle without an entry_seed anchor.
    let mut reachable: SpecKeySet = entry_seeds(t, m)
        .into_iter()
        .map(|(fid, key)| spec_key_for_fn_id(m, fid, key))
        .collect();
    let mut bfs: std::collections::VecDeque<SpecKey> = reachable.iter().cloned().collect();
    while let Some(spec) = bfs.pop_front() {
        if let Some(sites) = emits_by_caller.get(&spec) {
            for site in sites {
                if let Some(target) = produces.get(site).cloned()
                    && reachable.insert(target.clone())
                {
                    bfs.push_back(target);
                }
            }
        }
    }
    specs.retain(|k, _| reachable.contains(k));
    effective_returns.retain(|k, _| reachable.contains(k));

    let any_key_specs = build_any_key_index(t, m, &specs);
    let spec_precedence = key_precedence_order(&specs, &any_key_specs);

    let mut mt = ModulePlan {
        specs,
        effective_returns,
        any_key_specs,
        spec_precedence,
        effect_summaries: HashMap::new(),
        scc_of,
        dead_branches: HashMap::new(),
        closure_handles,
    };
    mt.dead_branches = compute_dead_branches(t, m, &mt);
    mt.effect_summaries = compute_effect_summaries(m, &mt);
    {
        let pops = WORKLIST_POPS.with(|c| c.get()) as u64;
        let walks = WALK_CALLS.with(|c| c.get()) as u64;
        let type_fns = TYPE_FN_CALLS.with(|c| c.get()) as u64;
        let stats = module_type_stats(m, &mt);
        tel.execute(
            &["fz", "typer", "typed"],
            &crate::measurements! {
                worklist_pops: pops,
                walk_calls: walks,
                type_fn_calls: type_fns,
                spec_count: mt.specs.len() as u64,
                matcher_spec_count: stats.matcher_spec_count as u64,
                spec_var_count: stats.spec_var_count as u64,
                spec_block_count: stats.spec_block_count as u64,
                spec_stmt_count: stats.spec_stmt_count as u64,
                dispatch_count: stats.dispatch_count as u64,
                direct_call_count: stats.direct_call_count as u64,
                tail_call_count: stats.tail_call_count as u64,
                if_count: stats.if_count as u64,
                receive_count: stats.receive_count as u64,
                receive_matched_count: stats.receive_matched_count as u64,
            },
            &crate::metadata! {
                module_path: m.module_path().to_owned(),
                module: crate::telemetry::value::opaque(m),
                module_types: crate::telemetry::value::opaque(&mt),
            },
        );
    }
    mt
}

fn compute_effect_summaries(m: &Module, mt: &ModulePlan) -> HashMap<SpecKey, EffectSummary> {
    let mut summaries: HashMap<SpecKey, EffectSummary> = mt
        .specs
        .keys()
        .map(|key| (key.clone(), local_effect_summary(m, key, mt)))
        .collect();
    loop {
        let mut changed = false;
        for (key, ft) in &mt.specs {
            let mut summary = *summaries.get(key).unwrap_or(&EffectSummary::default());
            for target in ft.dispatches.values() {
                if let Some(target_summary) = summaries.get(target).copied() {
                    changed |= summary.union_with(target_summary);
                }
            }
            if summaries.get(key).copied() != Some(summary) {
                summaries.insert(key.clone(), summary);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    summaries
}

fn local_effect_summary(m: &Module, key: &SpecKey, mt: &ModulePlan) -> EffectSummary {
    let Some(ft) = mt.specs.get(key) else {
        return EffectSummary::default();
    };
    let Some(&idx) = m.fn_idx.get(&key.fn_id) else {
        return EffectSummary::default();
    };
    let f = &m.fns[idx];
    let mut summary = EffectSummary::default();
    for b in &f.blocks {
        if !ft.reachable_blocks.contains(&b.id) {
            continue;
        }
        for crate::fz_ir::Stmt::Let(_, prim) in &b.stmts {
            summary.union_with(prim_effect_summary(m, prim));
        }
        summary.union_with(term_local_effect_summary(&b.terminator));
    }
    summary
}

fn prim_effect_summary(m: &Module, prim: &Prim) -> EffectSummary {
    match prim {
        Prim::MakeTuple(_)
        | Prim::DestTupleBegin { .. }
        | Prim::DestTupleSet { .. }
        | Prim::DestFreeze { .. }
        | Prim::MakeList(_, _)
        | Prim::DestListBegin { .. }
        | Prim::DestListCons { .. }
        | Prim::DestListFreeze { .. }
        | Prim::MakeClosure(_, _, _)
        | Prim::MakeMap(_)
        | Prim::MapUpdate(_, _)
        | Prim::DestMapBegin { .. }
        | Prim::DestMapPut { .. }
        | Prim::DestMapFreeze { .. }
        | Prim::MakeBitstring(_)
        | Prim::ConstBitstring(_, _)
        | Prim::BitReaderInit(_) => EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        },
        Prim::Extern(eid, _) => {
            let decl = m.extern_by_id(*eid);
            let reads_allocation_stats = decl.symbol == "fz_process_heap_alloc_stats";
            let scheduler_visible = matches!(
                decl.symbol.as_str(),
                "fz_send" | "fz_spawn" | "fz_spawn_opt" | "fz_self"
            );
            EffectSummary {
                observable: true,
                reads_allocation_stats,
                scheduler_visible,
                halts: decl.ret == crate::fz_ir::ExternTy::Never,
                ..EffectSummary::default()
            }
        }
        _ => EffectSummary::default(),
    }
}

fn term_local_effect_summary(term: &Term) -> EffectSummary {
    match term {
        Term::Receive { .. } | Term::ReceiveMatched { .. } => EffectSummary {
            observable: true,
            scheduler_visible: true,
            ..EffectSummary::default()
        },
        Term::Halt(_) => EffectSummary {
            observable: true,
            halts: true,
            ..EffectSummary::default()
        },
        _ => EffectSummary::default(),
    }
}

/// fz-rh5.6 — worklist driver with provenance.
///
/// Each pop:
///   1. type_fn the spec if new (cached by spec_key).
///   2. Walk for discovery → fills `WalkResult`.
///   3. Diff `result.emits` against the spec's prior emits
///      (`emits_by_caller[spec_key]`). Transition `produces` and
///      `holders`. Enqueue new target specs.
///   4. Fold `result.closure_handles` into the module-level handle
///      set (fz-try B1+B2).
///   5. Recompute this spec's effective return. If changed, enqueue
///      every spec in `return_readers[spec]`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn process_worklist<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    m: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    work: &mut std::collections::VecDeque<SpecKey>,
    in_work: &mut SpecKeySet,
    specs: &mut HashMap<SpecKey, SpecPlan>,
    effective_returns: &mut HashMap<SpecKey, crate::types::Ty>,
    callsite_fn_consts: &mut CallsiteFnConsts,
    return_readers: &mut ReturnReaders,
    visit_count: &mut HashMap<SpecKey, usize>,
    produces: &mut ProducesMap,
    holders: &mut HoldersMap,
    emits_by_caller: &mut EmitsByCaller,
    closure_handles: &mut std::collections::HashSet<(FnId, Vec<crate::types::Ty>)>,
) {
    while let Some(spec_key) = work.pop_front() {
        in_work.remove(&spec_key);
        WORKLIST_POPS.with(|c| c.set(c.get() + 1));

        let Some(&j) = m.fn_idx.get(&spec_key.fn_id) else {
            continue;
        };

        // type_fn is pure in (FnIr, entry_key) — cache by spec_key.
        if !specs.contains_key(&spec_key) {
            TYPE_FN_CALLS.with(|c| c.set(c.get() + 1));
            let input_tys = spec_key_input_tys(t, &spec_key);
            let mut ft = type_fn(t, &m.fns[j], m, Some(&input_tys));
            if let Some(arg_consts) = callsite_fn_consts.get(&spec_key) {
                let entry = m.fns[j].entry;
                let entry_params = &m.fns[j].block(entry).params;
                for (slot, p) in entry_params.iter().enumerate() {
                    if let Some(Some(fid_const)) = arg_consts.get(slot) {
                        ft.fn_constants.insert(*p, *fid_const);
                    }
                }
            }
            specs.insert(spec_key.clone(), ft);
        }

        let count = visit_count.entry(spec_key.clone()).or_insert(0);
        *count += 1;
        // fz-rh5.7 — termination invariant tripwire. See proof in
        // `plan_module`'s doc comment.
        assert!(
            *count < VISIT_HARD_BOUND,
            "spec {:?} visited {} times — termination invariant violated",
            spec_key,
            *count
        );
        // Walk → emits + return_reads + closure_handles.
        let caller_ft = specs.get(&spec_key).unwrap();
        let mut result = WalkResult::default();
        walk_spec_for_discovery(
            t,
            &m.fns[j],
            caller_ft,
            m,
            effective_returns,
            recursive_fns,
            &spec_key,
            callsite_fn_consts,
            &mut result,
        );

        // Diff emits against this caller's prior emit set. Transitions
        // update produces + holders + emits_by_caller.
        //
        // fz-uwq.3 — install this spec's `SpecPlan.dispatches` from
        // `result.dispatch_targets`, which uses the same
        // recursively-normalized key as `result.emits`.
        let prev_sites = emits_by_caller.remove(&spec_key).unwrap_or_default();
        let mut new_sites: EmitterSiteSet = std::collections::HashSet::new();
        for (site, target) in result.emits {
            new_sites.insert(site.clone());
            match produces.get(&site).cloned() {
                Some(prev_target) if prev_target == target => {
                    // Stable — no transition.
                }
                Some(prev_target) => {
                    // Retarget: detach from old, attach to new.
                    if let Some(h) = holders.get_mut(&prev_target) {
                        h.remove(&site);
                    }
                    holders
                        .entry(target.clone())
                        .or_default()
                        .insert(site.clone());
                    produces.insert(site, target.clone());
                }
                None => {
                    holders
                        .entry(target.clone())
                        .or_default()
                        .insert(site.clone());
                    produces.insert(site, target.clone());
                }
            }
            if !specs.contains_key(&target) && in_work.insert(target.clone()) {
                work.push_back(target);
            }
        }
        if let Some(ft) = specs.get_mut(&spec_key) {
            ft.dispatches = result.dispatch_targets;
            ft.return_uses = result.return_uses;
            ft.return_context_plans = result.return_context_plans;
        }
        // Sites present in prev but absent in new: this walk no longer
        // emits them. Detach from holders; clear produces.
        for site in prev_sites.difference(&new_sites) {
            if let Some(prev_target) = produces.remove(site)
                && let Some(h) = holders.get_mut(&prev_target)
            {
                h.remove(site);
            }
        }
        emits_by_caller.insert(spec_key.clone(), new_sites);

        // fz-try B1+B2 — accumulate handle registrations from this walk.
        for handle in result.closure_handles {
            closure_handles.insert(handle);
        }

        // Recompute effective return. compute_return_for_spec records
        // every callee return it consults; together with the walk's
        // return_reads, that's the full set of edges whose change
        // affects this spec.
        let mut compute_reads: Vec<SpecKey> = Vec::new();
        let new_ret = compute_return_for_spec(
            t,
            m,
            &spec_key,
            recursive_fns,
            specs,
            effective_returns,
            &mut compute_reads,
        );
        for callee_key in result.return_reads.into_iter().chain(compute_reads) {
            return_readers
                .entry(callee_key)
                .or_default()
                .insert(spec_key.clone());
        }
        let changed = match effective_returns.get(&spec_key) {
            Some(prev) => !t.is_equivalent(&new_ret, prev),
            None => true,
        };
        if changed {
            effective_returns.insert(spec_key.clone(), new_ret);
            if let Some(readers) = return_readers.get(&spec_key).cloned() {
                for reader in readers {
                    if specs.contains_key(&reader) && in_work.insert(reader.clone()) {
                        work.push_back(reader);
                    }
                }
            }
        }
    }
}

/// fz-5j5.3 — single-spec effective-return computation. Joins every
/// reachable Return / TailCall / TailCallClosure / cont-bearing
/// terminator into a type using `effective_returns` for downstream
/// reads. Missing entries contribute `none()` (Kleene bottom)
/// so partial state doesn't spuriously widen.
///
/// Every (callee_key) whose return is consulted is pushed into
/// `reads`. The worklist driver folds these into `return_readers`
/// so callee-return changes re-enqueue this spec.
pub(crate) fn compute_return_for_spec<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    spec_key: &SpecKey,
    recursive_fns: &std::collections::HashSet<FnId>,
    specs: &HashMap<SpecKey, SpecPlan>,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    reads: &mut Vec<SpecKey>,
) -> T::Ty {
    let Some(&j) = module.fn_idx.get(&spec_key.fn_id) else {
        return t.none();
    };
    let Some(ft) = specs.get(spec_key) else {
        return t.none();
    };
    let f = &module.fns[j];

    let mut joined = t.none();
    for b in &f.blocks {
        if !ft.reachable_blocks.contains(&b.id) {
            continue;
        }
        let term_env = env_at_terminator(t, ft, b, module);
        match &b.terminator {
            Term::Return(rv) => {
                let dy = term_env.get(rv).cloned().unwrap_or_else(|| t.any());
                joined = t.union(joined, dy);
            }
            Term::TailCall { callee, args, .. } => {
                let arg_tys: Vec<crate::types::Ty> = args
                    .iter()
                    .map(|av| term_env.get(av).cloned().unwrap_or_else(|| t.any()))
                    .collect();
                let mut key = recursive_direct_spec_key(
                    t,
                    module,
                    recursive_fns,
                    spec_key.fn_id,
                    *callee,
                    arg_tys,
                );
                key.demand = spec_key.demand.clone();
                let d = effective_returns.get(&key);
                reads.push(key);
                let dy = d.cloned().unwrap_or_else(|| t.none());
                joined = t.union(joined, dy);
            }
            Term::TailCallClosure {
                closure,
                args,
                ident: _,
            } => {
                if let Some(&target) = ft.fn_constants.get(closure) {
                    let target_fn = module.fn_by_id(target);
                    let np = target_fn.block(target_fn.entry).params.len();
                    let mut ad: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|av| term_env.get(av).cloned().unwrap_or_else(|| t.any()))
                        .collect();
                    while ad.len() < np {
                        ad.push(t.any());
                    }
                    ad.truncate(np);
                    let mut key = recursive_direct_spec_key(
                        t,
                        module,
                        recursive_fns,
                        spec_key.fn_id,
                        target,
                        ad,
                    );
                    key.demand = spec_key.demand.clone();
                    let d = effective_returns.get(&key);
                    reads.push(key);
                    let dy = d.cloned().unwrap_or_else(|| t.none());
                    joined = t.union(joined, dy);
                } else if let Some(cv_ty) = term_env.get(closure) {
                    let clauses = t.callable_clauses(cv_ty);
                    let mut all_lit = clauses.is_some();
                    let mut acc = t.none();
                    if let Some(clauses) = clauses {
                        for clause in clauses {
                            let Some(crate::types::ClosureLitInfo { target, captures }) =
                                clause.closure
                            else {
                                all_lit = false;
                                break;
                            };
                            let fn_id: FnId = target.into();
                            let target_fn = module.fn_by_id(fn_id);
                            let np = target_fn.block(target_fn.entry).params.len();
                            let mut full_key: Vec<crate::types::Ty> = captures.clone();
                            for av in args.iter() {
                                full_key.push(term_env.get(av).cloned().unwrap_or_else(|| t.any()));
                            }
                            while full_key.len() < np {
                                full_key.push(t.any());
                            }
                            full_key.truncate(np);
                            let mut key = recursive_direct_spec_key(
                                t,
                                module,
                                recursive_fns,
                                spec_key.fn_id,
                                fn_id,
                                full_key,
                            );
                            key.demand = spec_key.demand.clone();
                            let d = effective_returns.get(&key);
                            reads.push(key);
                            let dy = d.cloned().unwrap_or_else(|| t.none());
                            acc = t.union(acc, dy);
                        }
                    }
                    if all_lit {
                        joined = t.union(joined, acc);
                    } else {
                        let any_ty = t.any();
                        joined = t.union(joined, any_ty);
                    }
                } else {
                    let any_ty = t.any();
                    joined = t.union(joined, any_ty);
                }
            }
            Term::Call { continuation, .. }
            | Term::CallClosure { continuation, .. }
            | Term::Receive {
                continuation,
                ident: _,
            } => {
                let key = b
                    .terminator
                    .ident()
                    .and_then(|ident| {
                        ft.dispatches
                            .get(&crate::fz_ir::CallsiteId {
                                caller: spec_key.fn_id,
                                ident: ident.clone(),
                                slot: crate::fz_ir::EmitSlot::Cont,
                            })
                            .cloned()
                    })
                    .unwrap_or_else(|| {
                        let cont_k = cont_key_for_spec(
                            t,
                            b,
                            continuation,
                            ft,
                            module,
                            recursive_fns,
                            spec_key.fn_id,
                            effective_returns,
                        );
                        spec_key_for_fn_id(module, continuation.fn_id, cont_k)
                    });
                let d = effective_returns.get(&key);
                reads.push(key);
                let dy = d.cloned().unwrap_or_else(|| t.none());
                joined = t.union(joined, dy);
            }
            // fz-yxs — selective receive: union over each outcome body's
            // return type. Receive outcomes resume from an opaque closure
            // env, so their callable key is the all-`any` shape pinned by
            // `receive_outcome_spec_key` rather than the caller's current
            // capture types.
            Term::ReceiveMatched {
                clauses,
                after,
                captures: _,
                ..
            } => {
                let any = t.any();
                for c in clauses {
                    let body_fn = module.fn_by_id(c.body);
                    let np = body_fn.block(body_fn.entry).params.len();
                    let key = crate::fz_ir::receive_outcome_spec_key(&any, np);
                    let lookup_key = spec_key_for_fn_id(module, c.body, key);
                    let d = effective_returns.get(&lookup_key);
                    reads.push(lookup_key);
                    let dy = d.cloned().unwrap_or_else(|| t.none());
                    joined = t.union(joined, dy);
                }
                if let Some(a) = after {
                    let body_fn = module.fn_by_id(a.body);
                    let np = body_fn.block(body_fn.entry).params.len();
                    let key = crate::fz_ir::receive_outcome_spec_key(&any, np);
                    let lookup_key = spec_key_for_fn_id(module, a.body, key);
                    let d = effective_returns.get(&lookup_key);
                    reads.push(lookup_key);
                    let dy = d.cloned().unwrap_or_else(|| t.none());
                    joined = t.union(joined, dy);
                }
            }
            Term::Halt(_) | Term::Goto(_, _) | Term::If { .. } => {}
        }
    }
    joined
}

/// fz-5j5.3 — reconstruct the cont's input-type key at this block's
/// terminator using current `effective_returns` for slot 0. Mirrors
/// the walker's cont-key construction so the keys we look up are
/// structurally aligned with the registered specs.
pub(crate) fn cont_key_for_spec<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    block: &Block,
    cont: &crate::fz_ir::Cont,
    ft: &SpecPlan,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    caller: FnId,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
) -> Vec<crate::types::Ty> {
    use crate::types::Ty;
    let Some(_) = module.fn_idx.get(&cont.fn_id) else {
        return vec![];
    };
    let any_t = t.any();
    let cont_fn = module.fn_by_id(cont.fn_id);
    let n_params = cont_fn.block(cont_fn.entry).params.len();
    let mut key: Vec<Ty> = vec![any_t.clone(); n_params];

    let env = env_at_terminator(t, ft, block, module);
    let slot0: Ty = match &block.terminator {
        Term::Call { callee, args, .. } => {
            let arg_tys: Vec<Ty> = args
                .iter()
                .map(|av| env.get(av).cloned().unwrap_or_else(|| any_t.clone()))
                .collect();
            let lookup_key =
                recursive_direct_spec_key(t, module, recursive_fns, caller, *callee, arg_tys);
            effective_returns
                .get(&lookup_key)
                .cloned()
                .unwrap_or_else(|| any_t.clone())
        }
        Term::CallClosure { closure, args, .. } => {
            if let Some(&target) = ft.fn_constants.get(closure) {
                let target_fn = module.fn_by_id(target);
                let np = target_fn.block(target_fn.entry).params.len();
                let mut ad: Vec<Ty> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| any_t.clone()))
                    .collect();
                while ad.len() < np {
                    ad.push(any_t.clone());
                }
                ad.truncate(np);
                let lookup_key =
                    recursive_direct_spec_key(t, module, recursive_fns, caller, target, ad);
                effective_returns
                    .get(&lookup_key)
                    .cloned()
                    .unwrap_or_else(|| any_t.clone())
            } else if let Some(cv_descr) = env.get(closure) {
                // fz-5j5.3 — mirror walker's closure_lit slot-0 path
                // (resolve_closure_return). Without this, sweep computes
                // [any] where walker computed the closure's real return,
                // diverging from registered cont keys.
                let arg_tys: Vec<Ty> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| any_t.clone()))
                    .collect();
                resolve_closure_return(t, cv_descr, effective_returns, &arg_tys)
                    .unwrap_or_else(|| any_t.clone())
            } else {
                any_t.clone()
            }
        }
        _ => any_t.clone(),
    };
    if !key.is_empty() {
        key[0] = slot0;
    }
    for (k, cv) in cont.captured.iter().enumerate() {
        if let Some(p) = key.get_mut(k + 1) {
            *p = env.get(cv).cloned().unwrap_or_else(|| any_t.clone());
        }
    }
    key
}
