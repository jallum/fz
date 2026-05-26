use super::closures::resolve_closure_return;
use super::fn_types::{
    CallsiteFnConsts, EffectSummary, EmitterSite, FnTypes, ReturnContextPlan, ReturnContextPlanKey,
    ReturnDemand, ReturnUse, SpecKey, WALK_CALLS, recursive_direct_spec_key, spec_key_for_fn,
};
use crate::callsite_walk::{BlockCallsite, CallsiteKind, ContSource, block_callsites};
use crate::fz_ir::{EmitSlot, FnId, FnIr, Module, Prim, Stmt, Term, Var};
use std::collections::{HashMap, HashSet};

/// fz-rh5.6 — output of one discovery walk. The driver folds this
/// into worklist state.
#[derive(Default)]
pub(crate) struct WalkResult {
    /// Every `(site, target_spec_key)` this walk emits. The driver
    /// diffs against `produces[site]` to detect transitions.
    ///
    /// fz-uwq.3+ note: `target` here is the worklist key. Recursive
    /// direct calls are normalized before emission, so this key agrees
    /// with the dispatch fact consumed by codegen.
    pub(crate) emits: Vec<(EmitterSite, SpecKey)>,
    /// fz-uwq.3+ — per-callsite **dispatch fact**: the
    /// `(callee_fn, callee_key)` the typer resolved at this site after
    /// recursive-key normalization. This is the same key emitted above,
    /// so `FnTypes.dispatches` and the codegen path agree by construction.
    ///
    /// Only populated for dispatch-shaped slots
    /// (`Direct` / `ClosureLit` / `CallClosureKnown`). `Cont` slot
    /// inputs are tracked through `cont_input_key` and aren't widened.
    pub(crate) dispatch_targets: HashMap<crate::fz_ir::CallsiteId, SpecKey>,
    /// Per-callsite typed return-use facts for this caller spec. These facts
    /// describe the result hole reached by the call result; they do not imply
    /// whole-caller demand inheritance.
    pub(crate) return_uses: HashMap<crate::fz_ir::CallsiteId, ReturnUse>,
    /// Typed return-context lowering plans, keyed by caller spec and callsite.
    pub(crate) return_context_plans: HashMap<ReturnContextPlanKey, ReturnContextPlan>,
    /// `callee_key`s whose `effective_return` was consulted (for
    /// cont slot-0 keying or closure_lit return-join). Driver folds
    /// into the `return_readers` reverse index so changes
    /// re-enqueue this caller.
    pub(crate) return_reads: Vec<SpecKey>,
    /// fz-try B1+B2 — closure handles produced by MakeClosure in this
    /// walk, as `(lambda FnId, capture-types)`. Driver folds into
    /// `ModuleTypes.closure_handles`.
    pub(crate) closure_handles: HashSet<(FnId, Vec<crate::types::Ty>)>,
}

/// fz-rh5.6 — discovery walk for one spec. Walks the spec's body and
/// records every spec it currently emits into `out.emits`, tagged by
/// `EmitterSite`. The driver diffs against the spec's previous emits
/// (via `produces`/`holders`/`emits_by_caller`) and transitions
/// provenance.
///
/// Emit kinds:
///   - `EmitSlot::Direct` for `Term::Call` / `Term::TailCall`.
///   - `EmitSlot::ClosureCall` for `Term::CallClosure` / `Term::TailCallClosure`
///     callsites. Pre-fz-try.11 this was split into `CallClosureKnown`
///     (fn_constants resolved) and `ClosureLit(c, s)` (per closure-lit
///     clause); now both paths share the uniform structural slot and
///     dispatch variation lives on the Dispatch enum at row time.
///   - `EmitSlot::Cont` for the continuation of Call/CallClosure/Receive.
///
/// `Prim::MakeClosure` is *not* an emit kind — it constructs a closure
/// value (a *handle*), recorded in `out.closure_handles`. The lambda's
/// compiled body is the any-key body spec (SpecId.0 == FnId.0); codegen
/// resolves it directly without indirection through a MakeClosure-side
/// padded spec.
///
/// `recursive_fns`: calls into recursive functions are normalized
/// immediately with `widen_for_recursive_spec_key`, including the first
/// external entry into the recursive component. The dispatch fact and
/// emitted spec key both use that normalized key, so codegen cannot
/// resolve a different narrow spec from the one the worklist typed.
/// Cont keys are not normalized: they model dataflow from a concrete
/// producer, not a recursive function-entry fixed point.
#[allow(clippy::too_many_arguments)]
pub(crate) fn walk_spec_for_discovery<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    f: &FnIr,
    caller_ft: &FnTypes,
    m: &Module,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    recursive_fns: &std::collections::HashSet<FnId>,
    caller_spec_key: &SpecKey,
    callsite_fn_consts: &mut CallsiteFnConsts,
    out: &mut WalkResult,
) {
    WALK_CALLS.with(|c| c.set(c.get() + 1));
    let any_ty = t.any();
    fn has_bottom_arg<T: crate::types::Types<Ty = crate::types::Ty>>(
        t: &mut T,
        key: &[crate::types::Ty],
    ) -> bool {
        // A call key containing bottom describes an impossible callsite.
        // If later facts make it inhabited, return-readers requeue the
        // caller and discovery emits the real key then.
        let none_ty = t.none();
        key.iter().any(|ty| t.is_equivalent(ty, &none_ty))
    }

    let emit = |slot: EmitSlot,
                ident: crate::fz_ir::CallsiteIdent,
                target: SpecKey,
                out: &mut WalkResult| {
        out.emits.push((
            EmitterSite {
                caller: caller_spec_key.clone(),
                ident,
                slot,
            },
            target,
        ));
    };

    let tuple_return_demand_for_call = |callee: FnId, cont: &crate::fz_ir::Cont| -> ReturnDemand {
        let Some(arity) = continuation_tuple_field_arity(m, cont) else {
            return ReturnDemand::value();
        };
        if fn_returns_tuple_fields_without_material_value(m, callee, arity) {
            ReturnDemand::tuple_fields(arity)
        } else {
            ReturnDemand::value()
        }
    };
    let return_demand_for_call = |t: &mut T,
                                  env: &HashMap<Var, crate::types::Ty>,
                                  callee: FnId,
                                  cont: &crate::fz_ir::Cont|
     -> ReturnDemand {
        let demand = tuple_return_demand_for_call(callee, cont);
        if demand.tuple_field_arity().is_some() {
            return demand;
        }
        let Some(tail_ty) = continuation_list_tail_context(t, m, cont, env) else {
            return ReturnDemand::value();
        };
        if fn_can_return_list_tail(m, callee) {
            ReturnDemand::list_tail(tail_ty)
        } else {
            ReturnDemand::value()
        }
    };

    for b in &f.blocks {
        if !caller_ft.reachable_blocks.contains(&b.id) {
            continue;
        }
        let mut env: HashMap<Var, crate::types::Ty> =
            caller_ft.block_envs.get(&b.id).cloned().unwrap_or_default();

        // Stmt-level work: MakeClosure handle registration (fz-try
        // B1+B2). No stmt-level emits — closure construction is a
        // value event, not a body-spec dispatch.
        for stmt in b.stmts.iter() {
            let Stmt::Let(v, prim) = stmt;
            // fz-try B1+B2 — MakeClosure is closure-value construction. Two
            // effects:
            //   (a) Register a handle `(lam_fn_id, captures)` — closure-value
            //       identity, disjoint from body specs.
            //   (b) Emit the lambda's any-key body spec onto the worklist —
            //       uniform across every MakeClosure site of the same lambda,
            //       no captures-padding. The emit drives the typer to type
            //       the body; codegen registers one compiled body per
            //       closure-target at SpecId.0 == FnId.0. The closure-target
            //       ABI seam speaks ValueRef (fz-try.15), so no per-capture
            //       body specialization is needed for wire-format
            //       synchronization.
            if let Prim::MakeClosure(mk_ident, lam_fn_id, captured) = prim
                && let Some(&jj) = m.fn_idx.get(lam_fn_id)
            {
                let lam = &m.fns[jj];
                let n_params = lam.block(lam.entry).params.len();
                let captures: Vec<crate::types::Ty> = captured
                    .iter()
                    .map(|cv| {
                        env.get(cv)
                            .cloned()
                            .expect("MakeClosure: captured var unbound")
                    })
                    .collect();
                out.closure_handles.insert((*lam_fn_id, captures));
                let any_key = spec_key_for_fn(lam, vec![any_ty.clone(); n_params]);
                let site = EmitterSite {
                    caller: caller_spec_key.clone(),
                    ident: mk_ident.clone(),
                    slot: EmitSlot::MakeClosure,
                };
                out.emits.push((site, any_key));
            }
            {
                let pt_ty = super::prim::type_prim(t, prim, &env, m, &HashSet::new());
                env.insert(*v, pt_ty);
            }
        }

        // fz-9pr.17 — opaque-arity detection for unresolved closure
        // fz-9pr.17 — terminator-derived callsites. One match site
        // (callsite_walk::block_callsites) replaces the four arms that
        // used to live here (Direct, CallClosureKnown, ClosureLit,
        // Cont). Per-spec key building and callsite_fn_consts tracking
        // stay typer-side because they depend on caller_ft.block_envs
        // and caller_ft.fn_constants.
        // fz-kgk — every slot in `block_callsites` shares the
        // terminator's intrinsic ident; non-call terminators have no
        // callsites and don't reach here.
        let term_ident = match b.terminator.ident() {
            Some(i) => i.clone(),
            None => continue,
        };
        let cs_list = block_callsites(t, &b.terminator, &env, &caller_ft.fn_constants);
        for BlockCallsite { slot, kind } in cs_list {
            match kind {
                CallsiteKind::Direct { callee, args } => {
                    let Some(&j) = m.fn_idx.get(&callee) else {
                        continue;
                    };
                    let callee_fn = &m.fns[j];
                    let n_params = callee_fn.block(callee_fn.entry).params.len();
                    let mut dispatch_key: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                        .collect();
                    while dispatch_key.len() < n_params {
                        dispatch_key.push(any_ty.clone());
                    }
                    dispatch_key.truncate(n_params);
                    if has_bottom_arg(t, &dispatch_key) {
                        continue;
                    }
                    let mut entry_key = recursive_direct_spec_key(
                        t,
                        m,
                        recursive_fns,
                        caller_spec_key.fn_id,
                        callee,
                        dispatch_key,
                    );
                    let cid = crate::fz_ir::CallsiteId {
                        caller: caller_spec_key.fn_id,
                        ident: term_ident.clone(),
                        slot,
                    };
                    if let Term::Call { continuation, .. } = &b.terminator {
                        let mut list_tail_plan = None;
                        entry_key.demand = if let Some((pivot, tail, tail_ty)) =
                            cons_then_direct_list_tail_plan(
                                m,
                                caller_spec_key,
                                callee,
                                args,
                                continuation,
                            ) {
                            list_tail_plan = Some(ReturnContextPlan::ConsThenDirect {
                                continuation: continuation.fn_id,
                                pivot,
                                tail,
                                tail_ty: tail_ty.clone(),
                            });
                            if caller_spec_key.demand.tuple_field_arity().is_none() {
                                ReturnDemand::list_tail(tail_ty)
                            } else {
                                return_demand_for_call(t, &env, callee, continuation)
                            }
                        } else {
                            return_demand_for_call(t, &env, callee, continuation)
                        };
                        out.return_uses
                            .insert(cid.clone(), ReturnUse::from_demand(&entry_key.demand));
                        if let Some(plan) = list_tail_plan {
                            out.return_context_plans.insert(
                                ReturnContextPlanKey {
                                    caller: caller_spec_key.clone(),
                                    callsite: cid.clone(),
                                },
                                plan,
                            );
                        } else if let Some(tail_ty) = entry_key.demand.list_tail_ty() {
                            if caller_spec_key.demand.tuple_field_arity().is_some()
                                && caller_spec_key.demand.list_tail_ty().is_some()
                            {
                                let mut captures = continuation.captured.iter().copied();
                                if let (Some(pivot), Some(tail)) =
                                    (captures.next(), captures.next())
                                {
                                    out.return_context_plans.insert(
                                        ReturnContextPlanKey {
                                            caller: caller_spec_key.clone(),
                                            callsite: cid.clone(),
                                        },
                                        ReturnContextPlan::ContinuationListTailBridge {
                                            continuation: continuation.fn_id,
                                            pivot,
                                            tail,
                                            tail_ty: tail_ty.clone(),
                                        },
                                    );
                                }
                            } else {
                                let cont_fn = m.fn_by_id(continuation.fn_id);
                                if let Some(result_param) =
                                    cont_fn.block(cont_fn.entry).params.first().copied()
                                {
                                    out.return_context_plans.insert(
                                        ReturnContextPlanKey {
                                            caller: caller_spec_key.clone(),
                                            callsite: cid.clone(),
                                        },
                                        ReturnContextPlan::DirectContinuation {
                                            continuation: continuation.fn_id,
                                            result_param,
                                            tail_ty: tail_ty.clone(),
                                        },
                                    );
                                }
                            }
                        }
                    } else if matches!(&b.terminator, Term::TailCall { .. }) {
                        entry_key.demand = caller_spec_key.demand.clone();
                        out.return_uses
                            .insert(cid.clone(), ReturnUse::from_demand(&entry_key.demand));
                        if let Some(tail_ty) = entry_key.demand.list_tail_ty()
                            && args.len() >= 2
                        {
                            out.return_context_plans.insert(
                                ReturnContextPlanKey {
                                    caller: caller_spec_key.clone(),
                                    callsite: cid.clone(),
                                },
                                ReturnContextPlan::TailCallDestination {
                                    callee,
                                    source: args[0],
                                    tail: args[1],
                                    tail_ty: tail_ty.clone(),
                                },
                            );
                        }
                    }
                    out.dispatch_targets.insert(cid, entry_key.clone());
                    let mut per_arg: Vec<Option<FnId>> = args
                        .iter()
                        .map(|av| caller_ft.fn_constants.get(av).copied())
                        .collect();
                    while per_arg.len() < n_params {
                        per_arg.push(None);
                    }
                    per_arg.truncate(n_params);
                    match callsite_fn_consts.get(&entry_key) {
                        None => {
                            callsite_fn_consts.insert(entry_key.clone(), per_arg);
                        }
                        Some(prev) => {
                            let merged: Vec<Option<FnId>> = prev
                                .iter()
                                .zip(per_arg.iter())
                                .map(|(a, b)| if a == b { *a } else { None })
                                .collect();
                            callsite_fn_consts.insert(entry_key.clone(), merged);
                        }
                    }
                    emit(slot, term_ident.clone(), entry_key, out);
                }
                CallsiteKind::CallClosureKnown { target, args } => {
                    let Some(&j) = m.fn_idx.get(&target) else {
                        continue;
                    };
                    let target_fn = &m.fns[j];
                    let n_params = target_fn.block(target_fn.entry).params.len();
                    let mut dispatch_key: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                        .collect();
                    while dispatch_key.len() < n_params {
                        dispatch_key.push(any_ty.clone());
                    }
                    dispatch_key.truncate(n_params);
                    if has_bottom_arg(t, &dispatch_key) {
                        continue;
                    }
                    let mut target_key = recursive_direct_spec_key(
                        t,
                        m,
                        recursive_fns,
                        caller_spec_key.fn_id,
                        target,
                        dispatch_key,
                    );
                    if matches!(&b.terminator, Term::TailCallClosure { .. }) {
                        target_key.demand = caller_spec_key.demand.clone();
                    }
                    out.dispatch_targets.insert(
                        crate::fz_ir::CallsiteId {
                            caller: caller_spec_key.fn_id,
                            ident: term_ident.clone(),
                            slot,
                        },
                        target_key.clone(),
                    );
                    emit(slot, term_ident.clone(), target_key, out);
                }
                CallsiteKind::ClosureLit {
                    fn_id,
                    captures,
                    args,
                } => {
                    let Some(&j) = m.fn_idx.get(&fn_id) else {
                        continue;
                    };
                    let target_fn = &m.fns[j];
                    let n_params = target_fn.block(target_fn.entry).params.len();
                    let mut dispatch_key: Vec<crate::types::Ty> = captures.clone();
                    let arg_tys = args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(|| any_ty.clone()));
                    dispatch_key.extend(arg_tys);
                    while dispatch_key.len() < n_params {
                        dispatch_key.push(any_ty.clone());
                    }
                    dispatch_key.truncate(n_params);
                    if has_bottom_arg(t, &dispatch_key) {
                        continue;
                    }
                    let mut target_key = recursive_direct_spec_key(
                        t,
                        m,
                        recursive_fns,
                        caller_spec_key.fn_id,
                        fn_id,
                        dispatch_key,
                    );
                    if matches!(&b.terminator, Term::TailCallClosure { .. }) {
                        target_key.demand = caller_spec_key.demand.clone();
                    }
                    out.dispatch_targets.insert(
                        crate::fz_ir::CallsiteId {
                            caller: caller_spec_key.fn_id,
                            ident: term_ident.clone(),
                            slot,
                        },
                        target_key.clone(),
                    );
                    emit(slot, term_ident.clone(), target_key, out);
                }
                CallsiteKind::Cont { cont, source } => {
                    // slot 0 derivation by Cont source. Receive is
                    // opaque (`any`); Call reads effective_returns;
                    // CallClosure either reads effective_returns of
                    // the fn_constants-resolved target or resolves
                    // via the closure-lit lattice.
                    let slot0_ty: Option<crate::types::Ty> = match source {
                        ContSource::Call { callee, args } => {
                            let direct_cid = crate::fz_ir::CallsiteId {
                                caller: caller_spec_key.fn_id,
                                ident: term_ident.clone(),
                                slot: crate::fz_ir::EmitSlot::Direct,
                            };
                            let callee_key = out
                                .dispatch_targets
                                .get(&direct_cid)
                                .cloned()
                                .unwrap_or_else(|| {
                                    let arg_tys: Vec<crate::types::Ty> = args
                                        .iter()
                                        .map(|av| {
                                            env.get(av).cloned().unwrap_or_else(|| any_ty.clone())
                                        })
                                        .collect();
                                    recursive_direct_spec_key(
                                        t,
                                        m,
                                        recursive_fns,
                                        caller_spec_key.fn_id,
                                        callee,
                                        arg_tys,
                                    )
                                });
                            out.return_reads.push(callee_key.clone());
                            effective_returns.get(&callee_key).cloned()
                        }
                        ContSource::CallClosure { closure, args } => {
                            if let Some(&target) = caller_ft.fn_constants.get(&closure) {
                                let target_fn = m.fn_by_id(target);
                                let n_params = target_fn.block(target_fn.entry).params.len();
                                let mut arg_tys: Vec<crate::types::Ty> = args
                                    .iter()
                                    .map(|av| {
                                        env.get(av).cloned().unwrap_or_else(|| any_ty.clone())
                                    })
                                    .collect();
                                while arg_tys.len() < n_params {
                                    arg_tys.push(any_ty.clone());
                                }
                                arg_tys.truncate(n_params);
                                let callee_key = recursive_direct_spec_key(
                                    t,
                                    m,
                                    recursive_fns,
                                    caller_spec_key.fn_id,
                                    target,
                                    arg_tys,
                                );
                                out.return_reads.push(callee_key.clone());
                                effective_returns.get(&callee_key).cloned()
                            } else if let Some(cv_descr) = env.get(&closure) {
                                let arg_tys: Vec<crate::types::Ty> = args
                                    .iter()
                                    .map(|av| {
                                        env.get(av).cloned().unwrap_or_else(|| any_ty.clone())
                                    })
                                    .collect();
                                if let Some(clauses) = t.callable_clauses(cv_descr) {
                                    for clause in clauses {
                                        if let Some(crate::types::ClosureLitInfo {
                                            target,
                                            captures,
                                        }) = clause.closure
                                            && clause.args.len() == arg_tys.len()
                                        {
                                            let mut full_key: Vec<crate::types::Ty> =
                                                captures.clone();
                                            full_key.extend_from_slice(&arg_tys);
                                            let callee_key = recursive_direct_spec_key(
                                                t,
                                                m,
                                                recursive_fns,
                                                caller_spec_key.fn_id,
                                                target.into(),
                                                full_key,
                                            );
                                            out.return_reads.push(callee_key);
                                        }
                                    }
                                }
                                resolve_closure_return(t, cv_descr, effective_returns, &arg_tys)
                            } else {
                                Some(any_ty.clone())
                            }
                        }
                        ContSource::Receive => Some(any_ty.clone()),
                    };
                    let Some(slot0) = slot0_ty else {
                        // Deferred: return_readers will re-enqueue
                        // this caller when the callee return arrives.
                        continue;
                    };
                    let none_ty = t.none();
                    if t.is_equivalent(&slot0, &none_ty) {
                        // Bottom means the continuation is unreachable
                        // unless the callee return grows later; the
                        // return_readers edge above will requeue us then.
                        continue;
                    }
                    let Some(&j) = m.fn_idx.get(&cont.fn_id) else {
                        continue;
                    };
                    let cont_fn = &m.fns[j];
                    let n_params = cont_fn.block(cont_fn.entry).params.len();
                    let mut key: Vec<crate::types::Ty> = vec![any_ty.clone(); n_params];
                    if !key.is_empty() {
                        key[0] = slot0;
                    }
                    for (k, cvv) in cont.captured.iter().enumerate() {
                        if let Some(p) = key.get_mut(k + 1) {
                            *p = env.get(cvv).cloned().unwrap_or_else(|| any_ty.clone());
                        }
                    }
                    if has_bottom_arg(t, &key) {
                        continue;
                    }
                    // fz-rh5.6 — do NOT widen cont keys. See pre-refactor
                    // commentary preserved in callsite_walk docs.
                    let mut per_param: Vec<Option<FnId>> = vec![None; n_params];
                    for (k, cvv) in cont.captured.iter().enumerate() {
                        if let Some(p) = per_param.get_mut(k + 1) {
                            *p = caller_ft.fn_constants.get(cvv).copied();
                        }
                    }
                    let demand = match source {
                        ContSource::Call { callee, .. } => {
                            if let Some(tail_ty) = caller_spec_key.demand.list_tail_ty()
                                && caller_spec_key.demand.tuple_field_arity().is_some()
                                && fn_can_return_list_tail(m, cont.fn_id)
                            {
                                ReturnDemand::list_tail(tail_ty.clone())
                            } else {
                                let tuple_demand = tuple_return_demand_for_call(callee, cont);
                                if let Some(arity) = tuple_demand.tuple_field_arity()
                                    && let Some(tail_ty) = caller_spec_key.demand.list_tail_ty()
                                    && fn_can_return_list_tail(m, cont.fn_id)
                                {
                                    ReturnDemand::tuple_fields_list_tail(arity, tail_ty.clone())
                                } else {
                                    tuple_demand
                                }
                            }
                        }
                        _ => ReturnDemand::value(),
                    };
                    let mut entry_key = spec_key_for_fn(cont_fn, key.clone());
                    entry_key.demand = demand.clone();
                    if caller_spec_key.demand.is_value()
                        && matches!(source, ContSource::Call { .. })
                        && let Some(arity) = demand.tuple_field_arity()
                        && fn_can_return_list_tail(m, cont.fn_id)
                    {
                        let any = t.any();
                        let tail_ty = t.list(any);
                        let mut target = entry_key.clone();
                        target.demand =
                            ReturnDemand::tuple_fields_list_tail(arity, tail_ty.clone());
                        out.return_context_plans.insert(
                            ReturnContextPlanKey {
                                caller: caller_spec_key.clone(),
                                callsite: crate::fz_ir::CallsiteId {
                                    caller: caller_spec_key.fn_id,
                                    ident: term_ident.clone(),
                                    slot,
                                },
                            },
                            ReturnContextPlan::ContinuationEmptyTail {
                                continuation: cont.fn_id,
                                target,
                                tail_ty,
                            },
                        );
                    }
                    match callsite_fn_consts.get(&entry_key) {
                        None => {
                            callsite_fn_consts.insert(entry_key.clone(), per_param);
                        }
                        Some(prev) => {
                            let merged: Vec<Option<FnId>> = prev
                                .iter()
                                .zip(per_param.iter())
                                .map(|(a, b)| if a == b { *a } else { None })
                                .collect();
                            callsite_fn_consts.insert(entry_key.clone(), merged);
                        }
                    }
                    // fz-uwq.5+ — Cont keys aren't widened, so the
                    // dispatch fact equals the emit key. Record it for
                    // codegen's `resolve_cont_sid` to read.
                    out.dispatch_targets.insert(
                        crate::fz_ir::CallsiteId {
                            caller: caller_spec_key.fn_id,
                            ident: term_ident.clone(),
                            slot,
                        },
                        entry_key.clone(),
                    );
                    emit(slot, term_ident.clone(), entry_key, out);
                }
            }
        }

        // fz-70q.3 — selective-receive bodies aren't expressed in
        // `block_callsites` (they're FnId fields on the terminator,
        // not Cont structs). Walk them inline so the typer's spec
        // worklist seeds (FnId, key) for each clause body / guard /
        // after; without this codegen never sees their FuncIds and
        // the park-site fn_addr lookup faults.
        //
        // Key shape mirrors `compute_return_for_spec`'s lookup:
        // receive outcomes resume from an opaque closure env, so the
        // body key is all-`any` at the body's entry-block arity.
        if let Term::ReceiveMatched {
            clauses,
            after,
            captures: _,
            ..
        } = &b.terminator
        {
            let mut enq = |fid: FnId, _bound_arity: usize, ident: crate::fz_ir::CallsiteIdent| {
                let Some(&j) = m.fn_idx.get(&fid) else {
                    return;
                };
                let body = &m.fns[j];
                let np = body.block(body.entry).params.len();
                let key = crate::fz_ir::receive_outcome_spec_key(&any_ty, np);
                emit(EmitSlot::Cont, ident, spec_key_for_fn(body, key), out);
            };
            // EmitterSite is keyed (caller, ident, slot); a single
            // ReceiveMatched term has N clause/after sub-targets but
            // shares one term_ident, so we synthesize per-target
            // idents from each body fn's span. Without this the
            // `produces` HashMap collapses to the last emit and
            // earlier targets fall out of reachability.
            for c in clauses {
                enq(
                    c.body,
                    c.bound_names.len(),
                    crate::fz_ir::CallsiteIdent::from_source(c.span),
                );
                if let Some(g) = c.guard {
                    enq(
                        g,
                        c.bound_names.len(),
                        crate::fz_ir::CallsiteIdent::from_source(c.span),
                    );
                }
            }
            if let Some(a) = after {
                enq(a.body, 0, crate::fz_ir::CallsiteIdent::from_source(a.span));
            }
        }
    }
}

fn continuation_tuple_field_arity(m: &Module, cont: &crate::fz_ir::Cont) -> Option<usize> {
    let cont_fn = m.fn_by_id(cont.fn_id);
    let entry = cont_fn.block(cont_fn.entry);
    let tuple_param = *entry.params.first()?;
    let mut max_idx: Option<u32> = None;
    let mut seen = std::collections::HashSet::new();
    let mut tuple_value_used = false;

    for b in &cont_fn.blocks {
        for Stmt::Let(_, prim) in &b.stmts {
            match prim {
                Prim::TupleField(v, idx) if *v == tuple_param => {
                    seen.insert(*idx);
                    max_idx = Some(max_idx.map_or(*idx, |m| m.max(*idx)));
                }
                Prim::TypeTest(v, _) if *v == tuple_param => {}
                other if prim_uses_var(other, tuple_param) => tuple_value_used = true,
                _ => {}
            }
        }
        if term_uses_var(&b.terminator, tuple_param) {
            tuple_value_used = true;
        }
    }
    if tuple_value_used {
        return None;
    }
    let arity = max_idx? as usize + 1;
    if arity == 0 || seen.len() != arity {
        return None;
    }
    Some(arity)
}

fn fn_returns_tuple_fields_without_material_value(m: &Module, fn_id: FnId, arity: usize) -> bool {
    fn go(
        m: &Module,
        fn_id: FnId,
        arity: usize,
        visiting: &mut std::collections::HashSet<FnId>,
    ) -> bool {
        if !visiting.insert(fn_id) {
            return true;
        }
        let f = m.fn_by_id(fn_id);
        let mut returned = false;
        for b in &f.blocks {
            match &b.terminator {
                Term::Return(v) => {
                    returned = true;
                    if !return_var_is_tuple_arity(b, *v, arity) {
                        return false;
                    }
                }
                Term::TailCall { callee, .. } if go(m, *callee, arity, visiting) => {}
                Term::Goto(_, _) | Term::If { .. } | Term::Halt(_) => {}
                _ => return false,
            }
        }
        visiting.remove(&fn_id);
        returned
            || f.blocks
                .iter()
                .any(|b| matches!(b.terminator, Term::TailCall { .. }))
    }
    go(m, fn_id, arity, &mut std::collections::HashSet::new())
}

fn continuation_list_tail_context<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    m: &Module,
    cont: &crate::fz_ir::Cont,
    caller_env: &HashMap<Var, crate::types::Ty>,
) -> Option<crate::types::Ty> {
    let cont_fn = m.fn_by_id(cont.fn_id);
    let entry = cont_fn.block(cont_fn.entry);
    let result_param = *entry.params.first()?;
    list_tail_context_for_hole(
        t,
        m,
        cont.fn_id,
        result_param,
        Some(caller_env),
        &mut HashSet::new(),
    )
}

fn list_tail_context_for_hole<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    m: &Module,
    fn_id: FnId,
    hole: Var,
    local_env: Option<&HashMap<Var, crate::types::Ty>>,
    visiting: &mut HashSet<(FnId, Var)>,
) -> Option<crate::types::Ty> {
    if !visiting.insert((fn_id, hole)) {
        let any = t.any();
        return Some(t.list(any));
    }
    let f = m.fn_by_id(fn_id);
    if fn_blocks_return_context_motion(m, fn_id, &mut HashSet::new()) {
        visiting.remove(&(fn_id, hole));
        return None;
    }
    let mut found = None;
    for b in &f.blocks {
        for Stmt::Let(_, prim) in &b.stmts {
            if prim_uses_var(prim, hole) {
                visiting.remove(&(fn_id, hole));
                return None;
            }
        }
        match &b.terminator {
            Term::TailCall { callee, args, .. }
                if args.first().copied() == Some(hole) && args.len() >= 2 =>
            {
                if !fn_can_return_list_tail(m, *callee) {
                    visiting.remove(&(fn_id, hole));
                    return None;
                }
                found = Some(list_tail_ty_for_var(t, local_env, args[1]));
            }
            Term::Call {
                args, continuation, ..
            } if !args.contains(&hole) => {
                let Some(capture_idx) = continuation.captured.iter().position(|v| *v == hole)
                else {
                    continue;
                };
                let next_fn = m.fn_by_id(continuation.fn_id);
                let next_entry = next_fn.block(next_fn.entry);
                let next_hole = *next_entry.params.get(capture_idx + 1)?;
                let next = list_tail_context_for_hole(
                    t,
                    m,
                    continuation.fn_id,
                    next_hole,
                    None,
                    visiting,
                )?;
                found = Some(next);
            }
            term if term_uses_var(term, hole) => {
                visiting.remove(&(fn_id, hole));
                return None;
            }
            _ => {}
        }
    }
    visiting.remove(&(fn_id, hole));
    found
}

fn fn_blocks_return_context_motion(m: &Module, fn_id: FnId, visiting: &mut HashSet<FnId>) -> bool {
    if !visiting.insert(fn_id) {
        return false;
    }
    let f = m.fn_by_id(fn_id);
    for b in &f.blocks {
        for Stmt::Let(_, prim) in &b.stmts {
            if prim_blocks_return_context_motion(m, prim) {
                visiting.remove(&fn_id);
                return true;
            }
        }
        match &b.terminator {
            Term::Call {
                callee,
                continuation,
                ..
            } => {
                if fn_blocks_return_context_motion(m, *callee, visiting)
                    || fn_blocks_return_context_motion(m, continuation.fn_id, visiting)
                {
                    visiting.remove(&fn_id);
                    return true;
                }
            }
            Term::TailCall { callee, .. } => {
                if fn_blocks_return_context_motion(m, *callee, visiting) {
                    visiting.remove(&fn_id);
                    return true;
                }
            }
            Term::CallClosure { .. }
            | Term::TailCallClosure { .. }
            | Term::Receive { .. }
            | Term::ReceiveMatched { .. } => {
                visiting.remove(&fn_id);
                return true;
            }
            Term::Goto(_, _) | Term::If { .. } | Term::Return(_) | Term::Halt(_) => {}
        }
    }
    visiting.remove(&fn_id);
    false
}

fn prim_blocks_return_context_motion(m: &Module, prim: &Prim) -> bool {
    prim_return_context_motion_effect(m, prim).blocks_return_context_motion()
}

fn prim_return_context_motion_effect(m: &Module, prim: &Prim) -> EffectSummary {
    let Prim::Extern(eid, _) = prim else {
        return EffectSummary::default();
    };
    let decl = m.extern_by_id(*eid);
    EffectSummary {
        observable: decl.symbol.contains("print"),
        reads_allocation_stats: decl.symbol == "fz_process_heap_alloc_stats",
        scheduler_visible: matches!(
            decl.symbol.as_str(),
            "fz_send" | "fz_spawn" | "fz_spawn_opt" | "fz_self"
        ),
        halts: decl.ret == crate::fz_ir::ExternTy::Never,
        ..EffectSummary::default()
    }
}

fn cons_then_direct_list_tail_plan(
    m: &Module,
    caller_spec_key: &SpecKey,
    callee: FnId,
    args: &[Var],
    continuation: &crate::fz_ir::Cont,
) -> Option<(Var, Var, crate::types::Ty)> {
    let tail_ty = caller_spec_key.demand.list_tail_ty()?.clone();
    if args.len() != 1 || !fn_can_return_list_tail(m, callee) {
        return None;
    }
    let caller_fn = m.fn_by_id(caller_spec_key.fn_id);
    let caller_entry = caller_fn.block(caller_fn.entry);
    let mut captures = continuation.captured.iter().copied();
    let pivot = captures.next()?;
    let tail = captures.next()?;
    (caller_entry.params.first().copied() == Some(tail)).then_some((pivot, tail, tail_ty))
}

fn list_tail_ty_for_var<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    local_env: Option<&HashMap<Var, crate::types::Ty>>,
    var: Var,
) -> crate::types::Ty {
    if let Some(ty) = local_env.and_then(|env| env.get(&var)).cloned() {
        return ty;
    }
    let any = t.any();
    t.list(any)
}

fn fn_can_return_list_tail(m: &Module, fn_id: FnId) -> bool {
    fn go(m: &Module, fn_id: FnId, visiting: &mut HashSet<FnId>) -> bool {
        if !visiting.insert(fn_id) {
            return true;
        }
        let f = m.fn_by_id(fn_id);
        let mut saw_return_or_tail = false;
        for b in &f.blocks {
            match &b.terminator {
                Term::Return(v) => {
                    saw_return_or_tail = true;
                    if !return_var_is_list_material(f, b, *v) {
                        visiting.remove(&fn_id);
                        return false;
                    }
                }
                Term::TailCall { callee, .. } => {
                    saw_return_or_tail = true;
                    if !go(m, *callee, visiting) {
                        visiting.remove(&fn_id);
                        return false;
                    }
                }
                Term::Call { continuation, .. } => {
                    saw_return_or_tail = true;
                    if !go(m, continuation.fn_id, visiting) {
                        visiting.remove(&fn_id);
                        return false;
                    }
                }
                Term::Goto(_, _) | Term::If { .. } | Term::Halt(_) => {}
                _ => {
                    visiting.remove(&fn_id);
                    return false;
                }
            }
        }
        visiting.remove(&fn_id);
        saw_return_or_tail
    }
    go(m, fn_id, &mut HashSet::new())
}

fn return_var_is_list_material(f: &FnIr, b: &crate::fz_ir::Block, ret: Var) -> bool {
    if f.block(f.entry).params.contains(&ret) {
        return true;
    }
    for Stmt::Let(dst, prim) in b.stmts.iter().rev() {
        if *dst != ret {
            continue;
        }
        return matches!(
            prim,
            Prim::MakeList(_, _) | Prim::DestListFreeze { .. } | Prim::ListTail(_)
        );
    }
    false
}

fn return_var_is_tuple_arity(b: &crate::fz_ir::Block, ret: Var, arity: usize) -> bool {
    for Stmt::Let(dst, prim) in b.stmts.iter().rev() {
        if *dst != ret {
            continue;
        }
        return match prim {
            Prim::MakeTuple(elems) => elems.len() == arity,
            Prim::DestFreeze { dest, .. } => b.stmts.iter().any(|Stmt::Let(v, p)| {
                *v == *dest && matches!(p, Prim::DestTupleBegin { arity: a, .. } if *a == arity)
            }),
            _ => false,
        };
    }
    false
}

fn prim_uses_var(prim: &Prim, needle: Var) -> bool {
    match prim {
        Prim::Const(_) | Prim::DestTupleBegin { .. } | Prim::DestListBegin { .. } => false,
        Prim::BinOp(_, a, b) => *a == needle || *b == needle,
        Prim::UnOp(_, a)
        | Prim::ListHead(a)
        | Prim::ListTail(a)
        | Prim::IsEmptyList(a)
        | Prim::DestFreeze { dest: a, .. }
        | Prim::DestListFreeze { list: a, .. }
        | Prim::TupleField(a, _)
        | Prim::TypeTest(a, _)
        | Prim::IsMatcherMapMiss(a)
        | Prim::BitReaderInit(a)
        | Prim::BitReaderDone(a)
        | Prim::Brand(a, _) => *a == needle,
        Prim::Extern(_, args) | Prim::MakeTuple(args) | Prim::MakeList(args, None) => {
            args.contains(&needle)
        }
        Prim::MakeList(args, Some(tail)) => args.contains(&needle) || *tail == needle,
        Prim::MakeClosure(_, _, caps) => caps.contains(&needle),
        Prim::DestTupleSet { dest, value, .. } => *dest == needle || *value == needle,
        Prim::DestListCons { head, tail, .. } => {
            *head == needle || tail.is_some_and(|tail| tail == needle)
        }
        Prim::MakeMap(entries) => entries.iter().any(|(k, v)| *k == needle || *v == needle),
        Prim::MapUpdate(base, entries) => {
            *base == needle || entries.iter().any(|(k, v)| *k == needle || *v == needle)
        }
        Prim::DestMapBegin { base, .. } => base.is_some_and(|base| base == needle),
        Prim::DestMapPut {
            map, key, value, ..
        } => *map == needle || *key == needle || *value == needle,
        Prim::DestMapFreeze { map, .. } => *map == needle,
        Prim::MapGet(map, key) | Prim::MatcherMapGet(map, key) => *map == needle || *key == needle,
        Prim::MakeBitstring(fields) => fields.iter().any(|f| {
            f.value == needle
                || matches!(&f.size, Some(crate::fz_ir::BitSizeIr::Var(v)) if *v == needle)
        }),
        Prim::BitReadField { reader, size, .. } => {
            *reader == needle
                || matches!(size, Some(crate::fz_ir::BitSizeIr::Var(v)) if *v == needle)
        }
        Prim::ConstBitstring(_, _) => false,
    }
}

fn term_uses_var(term: &Term, needle: Var) -> bool {
    match term {
        Term::Return(v) | Term::Halt(v) => *v == needle,
        Term::Goto(_, args) | Term::TailCall { args, .. } | Term::TailCallClosure { args, .. } => {
            args.contains(&needle)
        }
        Term::If { cond, .. } => *cond == needle,
        Term::Call {
            args, continuation, ..
        }
        | Term::CallClosure {
            args, continuation, ..
        } => args.contains(&needle) || continuation.captured.contains(&needle),
        Term::Receive { continuation, .. } => continuation.captured.contains(&needle),
        Term::ReceiveMatched { captures, .. } => captures.contains(&needle),
    }
}
