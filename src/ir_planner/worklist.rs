use super::closures::resolve_closure_return;
use super::diagnostics::{compute_dead_branches, module_plan_stats};
use super::effects::{prim_effect_summary, term_local_effect_summary};
use super::fn_types::{
    CallsiteCallableCapabilities, CapabilityPlan, EffectSummary, EmitsByCaller, EmitterSiteSet,
    FnEffects, HoldersMap, ModulePlan, PLAN_MODULE_CALLS, ProducesMap, ReturnReaders, SpecKey,
    SpecKeySet, SpecPlan, TYPE_FN_CALLS, VISIT_HARD_BOUND, WALK_CALLS, WORKLIST_POPS,
    build_any_key_index, key_precedence_order, recursive_direct_spec_key,
    recursive_direct_spec_key_for_arity, spec_key_for_fn_id, spec_key_input_tys,
};
use super::reachable::{cont_key_from_slot0, env_at_terminator};
use super::type_fn::type_fn;
use super::walk::{WalkResult, walk_spec_for_discovery};
use crate::fz_ir::{Block, FnId, Module, Term};
use crate::ir_callgraph::{build_call_graph, entry_seeds};
use std::collections::HashMap;

/// Type a module via one worklist over `SpecKey`s. The worklist drives spec
/// registration, body typing, and effective-return propagation as a single
/// unified data-flow LFP.
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
/// Discovery walks emit direct calls, closure calls, continuations, receive
/// outcomes, and any-key body specs reachable through `MakeClosure`. After the
/// worklist drains, a forward reachability sweep prunes specs no longer rooted
/// at an entry seed.
///
/// ## Termination
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
    PLAN_MODULE_CALLS.with(|c| c.set(c.get() + 1));
    WORKLIST_POPS.with(|c| c.set(0));
    TYPE_FN_CALLS.with(|c| c.set(0));
    WALK_CALLS.with(|c| c.set(0));

    let out = discover_specs(t, m);

    let any_key_specs = build_any_key_index(t, m, &out.specs);
    let spec_precedence = key_precedence_order(&out.specs, &any_key_specs);

    let mut mt = ModulePlan {
        specs: out.specs,
        effective_returns: out.effective_returns,
        any_key_specs,
        spec_precedence,
        fn_effects: out.fn_effects,
        dead_branches: HashMap::new(),
        #[cfg(test)]
        closure_handles: out.closure_handles,
    };
    mt.dead_branches = compute_dead_branches(t, m, &mt);
    {
        let pops = WORKLIST_POPS.with(|c| c.get()) as u64;
        let walks = WALK_CALLS.with(|c| c.get()) as u64;
        let type_fns = TYPE_FN_CALLS.with(|c| c.get()) as u64;
        let stats = module_plan_stats(m, &mt);
        tel.execute(
            &["fz", "planner", "planned"],
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
                // `plan_module` derives the one authoritative plan codegen (or a
                // single-plan consumer like the frontend) commits to. The label
                // is explicit so the dump-budget parser keys the committed plan's
                // shape on it instead of guessing from event order — and so a
                // future re-derivation, were one ever reintroduced, would be
                // visibly distinct rather than silently skewing the budgets.
                role: "authoritative",
                module_path: m.module_path().to_owned(),
                module: crate::telemetry::value::opaque(m),
                module_plan: crate::telemetry::value::opaque(&mt),
            },
        );
    }
    mt
}

/// Capability + effect facts for the pre-plan transforms (closure
/// devirtualization + inlining).
///
/// `rewrite_known_target_closures` and `inline_module_with_plan` read only
/// per-spec `callable_capabilities` (and `fn_effects`) — never effective
/// returns, call edges, dead branches, or precedence. So this runs the shared
/// spec-discovery worklist and then keeps *only* the capability slice: the
/// returned `CapabilityPlan` carries no types, call edges, or returns and is
/// not a codegen plan. It emits no `planner.planned` event, because the one
/// authoritative plan is derived once, later, by `plan_module`.
///
/// The worklist (including the effective-return fixpoint) is reused rather than
/// replaced by a fixpoint-free pass: capability precision is load-bearing.
/// A var's callable capability narrows as its type narrows under return
/// refinement, and the consensus `KnownFn` that drives a devirtualization can
/// be lost if returns stay coarse — empirically, dropping the fixpoint
/// regresses `apply2`, `enum_sort`, `higher_order`, and
/// `multi_caller_spec_divergent`. The redundancy removed is run A's
/// authoritative-plan *shape* (the full `ModulePlan` with dead-branch and
/// precedence finalization, and its `planner.planned` event), not the
/// worklist compute, which the capabilities genuinely require. The analysis is
/// interprocedural over the linked working module — the reason the pretyped
/// frontend's shallow `_pre_types` cannot serve here.
pub fn plan_callable_capabilities<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    m: &Module,
) -> CapabilityPlan {
    let out = discover_specs(t, m);
    let spec_capabilities = out
        .specs
        .into_iter()
        .map(|(key, ft)| (key.fn_id, ft.callable_capabilities))
        .collect();
    CapabilityPlan {
        spec_capabilities,
        fn_effects: out.fn_effects,
    }
}

/// Outcome of the shared worklist core: the discovered specs (each carrying its
/// callable capabilities, call edges, and types), their effective returns, the
/// per-FnId effect summary, and the closure-handle registry. `plan_module`
/// finalizes this into a `ModulePlan` (any-key index, precedence, dead
/// branches, telemetry); `plan_callable_capabilities` keeps only the
/// per-spec capabilities.
struct DiscoverOutput {
    specs: HashMap<SpecKey, SpecPlan>,
    effective_returns: HashMap<SpecKey, crate::types::Ty>,
    fn_effects: FnEffects,
    #[cfg_attr(not(test), allow(dead_code))]
    closure_handles: std::collections::HashSet<(FnId, Vec<crate::types::Ty>)>,
}

/// Drive the worklist to discover every reachable spec from the module's entry
/// seeds (running the effective-return fixpoint), then prune orphans. Shared by
/// `plan_module` and `plan_callable_capabilities`.
fn discover_specs<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    m: &Module,
) -> DiscoverOutput {
    let call_graph = build_call_graph(m);
    let mut sccs = super::scc::tarjan_scc(&call_graph);
    sccs.reverse();
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
    let mut callsite_callable_capabilities: CallsiteCallableCapabilities = HashMap::new();
    let mut return_readers: ReturnReaders = HashMap::new();
    let mut visit_count: HashMap<SpecKey, usize> = HashMap::new();

    let mut produces: ProducesMap = HashMap::new();
    let mut holders: HoldersMap = HashMap::new();
    let mut emits_by_caller: EmitsByCaller = HashMap::new();
    let mut closure_handles: std::collections::HashSet<(FnId, Vec<crate::types::Ty>)> =
        std::collections::HashSet::new();

    let fn_effects = compute_fn_effects(m);

    let mut work: std::collections::VecDeque<SpecKey> = entry_seeds(t, m)
        .into_iter()
        .map(|(fid, key)| spec_key_for_fn_id(m, fid, key))
        .collect();
    let mut in_work: SpecKeySet = work.iter().cloned().collect();

    process_worklist(
        t,
        m,
        &fn_effects,
        &recursive_fns,
        &mut work,
        &mut in_work,
        &mut specs,
        &mut effective_returns,
        &mut callsite_callable_capabilities,
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

    DiscoverOutput {
        specs,
        effective_returns,
        fn_effects,
        closure_handles,
    }
}

/// One per-FnId effect fact over the static call graph.
///
/// A function's effects are independent of any caller's return demand, so this
/// is computed once — before the worklist — and read by the destination-
/// planning barrier as a cached fact (replacing an on-demand body re-walk) and
/// stored on `ModulePlan` for downstream passes.
///
/// The fact is the least fixed point of: each function's local effects (every
/// block, no reachability pruning — a barrier must be conservative across all
/// paths) unioned with the effects of every function it reaches through a
/// `Call` (callee and continuation) or `TailCall` (callee). Calls through a
/// value contribute `calls_opaque` locally and are not followed, because the
/// target is not statically known here. A terminal `Halt` is transparent (see
/// the loop body). Effects only grow under `union_with`, so the fixed point
/// converges in finite steps over a closed module.
fn compute_fn_effects(m: &Module) -> FnEffects {
    let mut facts: FnEffects = HashMap::with_capacity(m.fns.len());
    let mut edges: HashMap<FnId, Vec<FnId>> = HashMap::with_capacity(m.fns.len());
    for f in &m.fns {
        let mut local = EffectSummary::default();
        let mut callees = Vec::new();
        for b in &f.blocks {
            for crate::fz_ir::Stmt::Let(_, prim) in &b.stmts {
                local.union_with(prim_effect_summary(m, prim));
            }
            // A terminal `Halt` returns the process's final value to the
            // scheduler; nothing executes after it, so it cannot observe — or
            // be disturbed by — relocating an allocation that builds the
            // returned value. It is transparent to the return-context-motion
            // barrier (fz-w34.2 generalizes this to position-scoping). Every
            // other terminator contributes its local effects: closure calls
            // are opaque, receive is a scheduler boundary.
            if !matches!(b.terminator, Term::Halt(_)) {
                local.union_with(term_local_effect_summary(&b.terminator));
            }
            match &b.terminator {
                Term::Call {
                    callee,
                    continuation,
                    ..
                } => {
                    callees.push(*callee);
                    callees.push(continuation.fn_id);
                }
                Term::TailCall { callee, .. } => callees.push(*callee),
                _ => {}
            }
        }
        facts.insert(f.id, local);
        edges.insert(f.id, callees);
    }
    loop {
        let mut changed = false;
        for f in &m.fns {
            let mut summary = facts[&f.id];
            for callee in &edges[&f.id] {
                if let Some(callee_summary) = facts.get(callee).copied() {
                    changed |= summary.union_with(callee_summary);
                }
            }
            facts.insert(f.id, summary);
        }
        if !changed {
            break;
        }
    }
    facts
}

/// Worklist driver with provenance.
///
/// Each pop:
///   1. type_fn the spec if new (cached by spec_key).
///   2. Walk for discovery → fills `WalkResult`.
///   3. Diff `result.emits` against the spec's prior emits
///      (`emits_by_caller[spec_key]`). Transition `produces` and
///      `holders`. Enqueue new target specs.
///   4. Install call-edge plans.
///   5. Fold `result.closure_handles` into the module-level handle set.
///   6. Recompute this spec's effective return. If changed, enqueue
///      every spec in `return_readers[spec]`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn process_worklist<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    m: &Module,
    fn_effects: &FnEffects,
    recursive_fns: &std::collections::HashSet<FnId>,
    work: &mut std::collections::VecDeque<SpecKey>,
    in_work: &mut SpecKeySet,
    specs: &mut HashMap<SpecKey, SpecPlan>,
    effective_returns: &mut HashMap<SpecKey, crate::types::Ty>,
    callsite_callable_capabilities: &mut CallsiteCallableCapabilities,
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
        ensure_spec_typed(t, m, j, &spec_key, callsite_callable_capabilities, specs);
        check_visit_bound(&spec_key, visit_count);
        let result = discover_spec_outputs(
            t,
            m,
            fn_effects,
            j,
            &spec_key,
            specs,
            effective_returns,
            recursive_fns,
            callsite_callable_capabilities,
        );
        let WalkResult {
            emits,
            call_edges,
            return_reads,
            closure_handles: discovered_handles,
        } = result;
        apply_emit_diff(
            &spec_key,
            emits,
            specs,
            work,
            in_work,
            produces,
            holders,
            emits_by_caller,
        );
        install_walk_result(specs, &spec_key, call_edges);
        closure_handles.extend(discovered_handles);
        update_effective_return_and_enqueue_readers(
            t,
            m,
            &spec_key,
            recursive_fns,
            specs,
            effective_returns,
            return_readers,
            work,
            in_work,
            return_reads,
        );
    }
}

fn ensure_spec_typed<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    m: &Module,
    fn_idx: usize,
    spec_key: &SpecKey,
    callsite_callable_capabilities: &CallsiteCallableCapabilities,
    specs: &mut HashMap<SpecKey, SpecPlan>,
) {
    if specs.contains_key(spec_key) {
        return;
    }
    TYPE_FN_CALLS.with(|c| c.set(c.get() + 1));
    let input_tys = spec_key_input_tys(t, spec_key);
    let mut ft = type_fn(t, &m.fns[fn_idx], m, Some(&input_tys));
    if let Some(arg_caps) = callsite_callable_capabilities.get(spec_key) {
        let entry = m.fns[fn_idx].entry;
        let entry_params = &m.fns[fn_idx].block(entry).params;
        for (slot, p) in entry_params.iter().enumerate() {
            if let Some(Some(capability)) = arg_caps.get(slot) {
                ft.callable_capabilities.insert(*p, capability.clone());
            }
        }
    }
    specs.insert(spec_key.clone(), ft);
}

fn check_visit_bound(spec_key: &SpecKey, visit_count: &mut HashMap<SpecKey, usize>) {
    let count = visit_count.entry(spec_key.clone()).or_insert(0);
    *count += 1;
    assert!(
        *count < VISIT_HARD_BOUND,
        "spec {:?} visited {} times — termination invariant violated",
        spec_key,
        *count
    );
}

fn discover_spec_outputs<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    m: &Module,
    fn_effects: &FnEffects,
    fn_idx: usize,
    spec_key: &SpecKey,
    specs: &HashMap<SpecKey, SpecPlan>,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    recursive_fns: &std::collections::HashSet<FnId>,
    callsite_callable_capabilities: &mut CallsiteCallableCapabilities,
) -> WalkResult {
    let caller_ft = specs.get(spec_key).unwrap();
    let mut result = WalkResult::default();
    walk_spec_for_discovery(
        t,
        &m.fns[fn_idx],
        caller_ft,
        m,
        fn_effects,
        effective_returns,
        recursive_fns,
        spec_key,
        callsite_callable_capabilities,
        &mut result,
    );
    result
}

#[allow(clippy::too_many_arguments)]
fn apply_emit_diff(
    spec_key: &SpecKey,
    emits: Vec<(super::fn_types::EmitterSite, SpecKey)>,
    specs: &HashMap<SpecKey, SpecPlan>,
    work: &mut std::collections::VecDeque<SpecKey>,
    in_work: &mut SpecKeySet,
    produces: &mut ProducesMap,
    holders: &mut HoldersMap,
    emits_by_caller: &mut EmitsByCaller,
) {
    let prev_sites = emits_by_caller.remove(spec_key).unwrap_or_default();
    let mut new_sites: EmitterSiteSet = std::collections::HashSet::new();
    for (site, target) in emits {
        new_sites.insert(site.clone());
        transition_emit_site(produces, holders, site, target.clone());
        if !specs.contains_key(&target) && in_work.insert(target.clone()) {
            work.push_back(target);
        }
    }
    remove_stale_emit_sites(produces, holders, &prev_sites, &new_sites);
    emits_by_caller.insert(spec_key.clone(), new_sites);
}

fn transition_emit_site(
    produces: &mut ProducesMap,
    holders: &mut HoldersMap,
    site: super::fn_types::EmitterSite,
    target: SpecKey,
) {
    match produces.get(&site).cloned() {
        Some(prev_target) if prev_target == target => {}
        Some(prev_target) => {
            if let Some(h) = holders.get_mut(&prev_target) {
                h.remove(&site);
            }
            holders
                .entry(target.clone())
                .or_default()
                .insert(site.clone());
            produces.insert(site, target);
        }
        None => {
            holders
                .entry(target.clone())
                .or_default()
                .insert(site.clone());
            produces.insert(site, target);
        }
    }
}

fn remove_stale_emit_sites(
    produces: &mut ProducesMap,
    holders: &mut HoldersMap,
    prev_sites: &EmitterSiteSet,
    new_sites: &EmitterSiteSet,
) {
    for site in prev_sites.difference(new_sites) {
        if let Some(prev_target) = produces.remove(site)
            && let Some(h) = holders.get_mut(&prev_target)
        {
            h.remove(site);
        }
    }
}

fn install_walk_result(
    specs: &mut HashMap<SpecKey, SpecPlan>,
    spec_key: &SpecKey,
    call_edges: HashMap<crate::fz_ir::CallsiteId, super::fn_types::CallEdgePlan>,
) {
    if let Some(ft) = specs.get_mut(spec_key) {
        ft.install_call_edges(call_edges);
    }
}

#[allow(clippy::too_many_arguments)]
fn update_effective_return_and_enqueue_readers<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    m: &Module,
    spec_key: &SpecKey,
    recursive_fns: &std::collections::HashSet<FnId>,
    specs: &HashMap<SpecKey, SpecPlan>,
    effective_returns: &mut HashMap<SpecKey, crate::types::Ty>,
    return_readers: &mut ReturnReaders,
    work: &mut std::collections::VecDeque<SpecKey>,
    in_work: &mut SpecKeySet,
    walk_return_reads: Vec<SpecKey>,
) {
    let mut compute_reads = Vec::new();
    let new_ret = compute_return_for_spec(
        t,
        m,
        spec_key,
        recursive_fns,
        specs,
        effective_returns,
        &mut compute_reads,
    );
    record_return_reads(return_readers, spec_key, walk_return_reads, compute_reads);
    let changed = effective_returns
        .get(spec_key)
        .is_none_or(|prev| !t.is_equivalent(&new_ret, prev));
    if changed {
        effective_returns.insert(spec_key.clone(), new_ret);
        enqueue_return_readers(spec_key, specs, return_readers, work, in_work);
    }
}

fn record_return_reads(
    return_readers: &mut ReturnReaders,
    spec_key: &SpecKey,
    walk_return_reads: Vec<SpecKey>,
    compute_reads: Vec<SpecKey>,
) {
    for callee_key in walk_return_reads.into_iter().chain(compute_reads) {
        return_readers
            .entry(callee_key)
            .or_default()
            .insert(spec_key.clone());
    }
}

fn enqueue_return_readers(
    spec_key: &SpecKey,
    specs: &HashMap<SpecKey, SpecPlan>,
    return_readers: &ReturnReaders,
    work: &mut std::collections::VecDeque<SpecKey>,
    in_work: &mut SpecKeySet,
) {
    let Some(readers) = return_readers.get(spec_key).cloned() else {
        return;
    };
    for reader in readers {
        if specs.contains_key(&reader) && in_work.insert(reader.clone()) {
            work.push_back(reader);
        }
    }
}

/// Compute one spec's effective return by joining every reachable
/// return-producing terminator. Missing downstream returns contribute
/// `none()` so partial worklist state does not spuriously widen.
///
/// Every callee key whose return is consulted is pushed into `reads`; the
/// worklist folds those into `return_readers` so callee-return changes
/// re-enqueue this spec.
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
        let contribution = match &b.terminator {
            Term::Return(rv) => Some(term_env.get(rv).cloned().unwrap_or_else(|| t.any())),
            Term::TailCall { callee, args, .. } => Some(direct_tail_return_contribution(
                t,
                module,
                recursive_fns,
                spec_key,
                effective_returns,
                reads,
                &term_env,
                *callee,
                args,
            )),
            Term::TailCallClosure {
                closure,
                args,
                ident: _,
            } => Some(tail_closure_return_contribution(
                t,
                module,
                recursive_fns,
                spec_key,
                ft,
                effective_returns,
                reads,
                &term_env,
                *closure,
                args,
            )),
            Term::Call { continuation, .. }
            | Term::CallClosure { continuation, .. }
            | Term::Receive {
                continuation,
                ident: _,
            } => Some(continuation_return_contribution(
                t,
                module,
                recursive_fns,
                spec_key,
                ft,
                effective_returns,
                reads,
                b,
                continuation,
            )),
            Term::ReceiveMatched { clauses, after, .. } => {
                Some(receive_matched_return_contribution(
                    t,
                    module,
                    effective_returns,
                    reads,
                    clauses,
                    after,
                ))
            }
            Term::Halt(_) | Term::Goto(_, _) | Term::If { .. } => None,
        };
        if let Some(dy) = contribution {
            joined = t.union(joined, dy);
        }
    }
    joined
}

#[allow(clippy::too_many_arguments)]
fn direct_tail_return_contribution<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    spec_key: &SpecKey,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    reads: &mut Vec<SpecKey>,
    term_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
    callee: FnId,
    args: &[crate::fz_ir::Var],
) -> crate::types::Ty {
    let arg_tys = arg_tys(t, term_env, args);
    let mut key =
        recursive_direct_spec_key(t, module, recursive_fns, spec_key.fn_id, callee, arg_tys);
    key.demand = spec_key.demand.clone();
    lookup_return_read(t, effective_returns, reads, key)
}

#[allow(clippy::too_many_arguments)]
fn tail_closure_return_contribution<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    spec_key: &SpecKey,
    ft: &SpecPlan,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    reads: &mut Vec<SpecKey>,
    term_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
    closure: crate::fz_ir::Var,
    args: &[crate::fz_ir::Var],
) -> crate::types::Ty {
    if let Some(target) = ft.known_fn(&closure) {
        return known_tail_closure_return_contribution(
            t,
            module,
            recursive_fns,
            spec_key,
            effective_returns,
            reads,
            term_env,
            target,
            args,
        );
    }
    let Some(cv_ty) = term_env.get(&closure) else {
        return t.any();
    };
    literal_tail_closure_return_contribution(
        t,
        module,
        recursive_fns,
        spec_key,
        effective_returns,
        reads,
        term_env,
        cv_ty,
        args,
    )
}

#[allow(clippy::too_many_arguments)]
fn known_tail_closure_return_contribution<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    spec_key: &SpecKey,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    reads: &mut Vec<SpecKey>,
    term_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
    target: FnId,
    args: &[crate::fz_ir::Var],
) -> crate::types::Ty {
    let target_fn = module.fn_by_id(target);
    let np = target_fn.block(target_fn.entry).params.len();
    let ad = arg_tys(t, term_env, args);
    let key = recursive_direct_spec_key_for_arity(
        t,
        module,
        recursive_fns,
        spec_key.fn_id,
        target,
        ad,
        np,
        Some(spec_key.demand.clone()),
    );
    lookup_return_read(t, effective_returns, reads, key)
}

#[allow(clippy::too_many_arguments)]
fn literal_tail_closure_return_contribution<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    spec_key: &SpecKey,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    reads: &mut Vec<SpecKey>,
    term_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
    cv_ty: &crate::types::Ty,
    args: &[crate::fz_ir::Var],
) -> crate::types::Ty {
    let clauses = t.callable_clauses(cv_ty);
    let mut all_lit = clauses.is_some();
    let mut acc = t.none();
    if let Some(clauses) = clauses {
        for clause in clauses {
            let Some(crate::types::ClosureLitInfo { target, captures }) = clause.closure else {
                all_lit = false;
                break;
            };
            let fn_id: FnId = target.into();
            let target_fn = module.fn_by_id(fn_id);
            let np = target_fn.block(target_fn.entry).params.len();
            let mut full_key = captures.clone();
            full_key.extend(arg_tys(t, term_env, args));
            let key = recursive_direct_spec_key_for_arity(
                t,
                module,
                recursive_fns,
                spec_key.fn_id,
                fn_id,
                full_key,
                np,
                Some(spec_key.demand.clone()),
            );
            let dy = lookup_return_read(t, effective_returns, reads, key);
            acc = t.union(acc, dy);
        }
    }
    if all_lit { acc } else { t.any() }
}

#[allow(clippy::too_many_arguments)]
fn continuation_return_contribution<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    spec_key: &SpecKey,
    ft: &SpecPlan,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    reads: &mut Vec<SpecKey>,
    block: &Block,
    continuation: &crate::fz_ir::Cont,
) -> crate::types::Ty {
    let key = block
        .terminator
        .ident()
        .and_then(|ident| {
            ft.local_call_target(&crate::fz_ir::CallsiteId::new(
                spec_key.fn_id,
                ident,
                crate::fz_ir::EmitSlot::Cont,
            ))
            .cloned()
        })
        .unwrap_or_else(|| {
            let cont_k = cont_key_for_spec(
                t,
                block,
                continuation,
                ft,
                module,
                recursive_fns,
                spec_key.fn_id,
                effective_returns,
            );
            spec_key_for_fn_id(module, continuation.fn_id, cont_k)
        });
    lookup_return_read(t, effective_returns, reads, key)
}

fn receive_matched_return_contribution<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    reads: &mut Vec<SpecKey>,
    clauses: &[crate::fz_ir::ReceiveClause],
    after: &Option<crate::fz_ir::ReceiveAfter>,
) -> crate::types::Ty {
    let any = t.any();
    let mut joined = t.none();
    for fid in clauses
        .iter()
        .map(|c| c.body)
        .chain(after.iter().map(|a| a.body))
    {
        let dy =
            receive_outcome_return_contribution(t, module, effective_returns, reads, fid, &any);
        joined = t.union(joined, dy);
    }
    joined
}

fn receive_outcome_return_contribution<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    reads: &mut Vec<SpecKey>,
    fid: FnId,
    any: &crate::types::Ty,
) -> crate::types::Ty {
    let body_fn = module.fn_by_id(fid);
    let np = body_fn.block(body_fn.entry).params.len();
    let key = crate::fz_ir::receive_outcome_spec_key(any, np);
    let lookup_key = spec_key_for_fn_id(module, fid, key);
    lookup_return_read(t, effective_returns, reads, lookup_key)
}

fn lookup_return_read<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    reads: &mut Vec<SpecKey>,
    key: SpecKey,
) -> crate::types::Ty {
    let dy = effective_returns
        .get(&key)
        .cloned()
        .unwrap_or_else(|| t.none());
    reads.push(key);
    dy
}

fn arg_tys<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    term_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
    args: &[crate::fz_ir::Var],
) -> Vec<crate::types::Ty> {
    args.iter()
        .map(|av| term_env.get(av).cloned().unwrap_or_else(|| t.any()))
        .collect()
}

/// Reconstruct the cont's input-type key at this block's terminator using
/// current `effective_returns` for slot 0.
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
            if let Some(target) = ft.known_fn(closure) {
                let target_fn = module.fn_by_id(target);
                let np = target_fn.block(target_fn.entry).params.len();
                let ad: Vec<Ty> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| any_t.clone()))
                    .collect();
                let lookup_key = recursive_direct_spec_key_for_arity(
                    t,
                    module,
                    recursive_fns,
                    caller,
                    target,
                    ad,
                    np,
                    None,
                );
                effective_returns
                    .get(&lookup_key)
                    .cloned()
                    .unwrap_or_else(|| any_t.clone())
            } else if let Some(cv_descr) = env.get(closure) {
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
    cont_key_from_slot0(&any_t, n_params, slot0, &cont.captured, &env)
}
