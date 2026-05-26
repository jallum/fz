use super::closures::resolve_closure_return;
use super::fn_types::{
    CallsiteFnConsts, EmitterSite, FnTypes, SpecKey, WALK_CALLS, recursive_direct_spec_key,
    spec_key_for_fn,
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
                    let entry_key = recursive_direct_spec_key(
                        t,
                        m,
                        recursive_fns,
                        caller_spec_key.fn_id,
                        callee,
                        dispatch_key,
                    );
                    out.dispatch_targets.insert(
                        crate::fz_ir::CallsiteId {
                            caller: caller_spec_key.fn_id,
                            ident: term_ident.clone(),
                            slot,
                        },
                        entry_key.clone(),
                    );
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
                    let target_key = recursive_direct_spec_key(
                        t,
                        m,
                        recursive_fns,
                        caller_spec_key.fn_id,
                        target,
                        dispatch_key,
                    );
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
                    let target_key = recursive_direct_spec_key(
                        t,
                        m,
                        recursive_fns,
                        caller_spec_key.fn_id,
                        fn_id,
                        dispatch_key,
                    );
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
                    let entry_key = spec_key_for_fn(cont_fn, key.clone());
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
                        spec_key_for_fn(cont_fn, key.clone()),
                    );
                    emit(slot, term_ident.clone(), spec_key_for_fn(cont_fn, key), out);
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
