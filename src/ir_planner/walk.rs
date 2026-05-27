use super::closures::resolve_closure_return;
use super::fn_types::{
    CallEdgePlan, CallEdgeTarget, CallsiteFnConsts, EmitterSite, ReturnContextPlan, ReturnDemand,
    SpecKey, SpecPlan, WALK_CALLS, padded_direct_input_tys, recursive_direct_spec_key,
    recursive_direct_spec_key_for_arity, spec_key_for_fn,
};
use super::reachable::cont_key_from_slot0;
use super::return_context::{
    continuation_empty_tail_plan, continuation_return_demand, direct_call_return_plan,
    tail_call_return_plan,
};
use crate::callsite_walk::{BlockCallsite, CallsiteKind, ContSource, block_callsites};
use crate::fz_ir::{
    CallsiteId, CallsiteIdent, EmitSlot, FnId, FnIr, Module, Prim, Stmt, Term, Var,
};
use std::collections::{HashMap, HashSet};

/// Output of one discovery walk. The driver folds this into worklist state.
#[derive(Default)]
pub(crate) struct WalkResult {
    /// Every `(site, target_spec_key)` this walk emits. The driver
    /// diffs against `produces[site]` to detect transitions.
    ///
    /// Recursive direct calls are normalized before emission, so this key
    /// agrees with the call-edge fact consumed by codegen.
    pub(crate) emits: Vec<(EmitterSite, SpecKey)>,
    /// Per-callsite capability selected for this spec. Populated for `Direct`,
    /// `ClosureCall`, and `Cont` slots. `MakeClosure` emits an any-key body spec
    /// but does not record a call edge.
    pub(crate) call_edges: HashMap<crate::fz_ir::CallsiteId, CallEdgePlan>,
    /// `callee_key`s whose `effective_return` was consulted (for
    /// cont slot-0 keying or closure_lit return-join). Driver folds
    /// into the `return_readers` reverse index so changes
    /// re-enqueue this caller.
    pub(crate) return_reads: Vec<SpecKey>,
    /// Closure handles produced by `MakeClosure` in this walk, as
    /// `(lambda FnId, capture-types)`. Driver folds into
    /// `ModulePlan.closure_handles`.
    pub(crate) closure_handles: HashSet<(FnId, Vec<crate::types::Ty>)>,
}

impl WalkResult {
    fn callsite_id(
        caller: &SpecKey,
        ident: &crate::fz_ir::CallsiteIdent,
        slot: EmitSlot,
    ) -> CallsiteId {
        CallsiteId::new(caller.fn_id, ident, slot)
    }

    fn record_dispatch(
        &mut self,
        caller: &SpecKey,
        ident: &crate::fz_ir::CallsiteIdent,
        slot: EmitSlot,
        target: SpecKey,
    ) -> CallsiteId {
        let cid = Self::callsite_id(caller, ident, slot);
        self.call_edges.insert(
            cid.clone(),
            CallEdgePlan {
                target: CallEdgeTarget::Local(target),
                return_use: None,
                return_context: None,
            },
        );
        cid
    }

    fn record_external_dispatch(
        &mut self,
        caller: &SpecKey,
        ident: &crate::fz_ir::CallsiteIdent,
        slot: EmitSlot,
        target: crate::modules::identity::ExportKey,
        input: Vec<crate::types::KeySlot>,
        demand: ReturnDemand,
    ) -> CallsiteId {
        let cid = Self::callsite_id(caller, ident, slot);
        self.call_edges.insert(
            cid.clone(),
            CallEdgePlan {
                target: CallEdgeTarget::External {
                    target,
                    input,
                    demand,
                },
                return_use: None,
                return_context: None,
            },
        );
        cid
    }

    fn record_return_use(
        &mut self,
        callsite: &CallsiteId,
        demand: ReturnDemand,
        plan: Option<ReturnContextPlan>,
    ) {
        let edge = self
            .call_edges
            .get_mut(callsite)
            .expect("return-use facts require an existing call edge");
        edge.return_use = Some(demand);
        if let Some(plan) = plan {
            edge.return_context = Some(plan);
        }
    }

    fn record_return_context_plan(&mut self, callsite: &CallsiteId, plan: ReturnContextPlan) {
        let edge = self
            .call_edges
            .get_mut(callsite)
            .expect("return-context plans require an existing call edge");
        edge.return_context = Some(plan);
    }
}

fn merge_callsite_fn_consts(
    callsite_fn_consts: &mut CallsiteFnConsts,
    key: &SpecKey,
    incoming: Vec<Option<FnId>>,
) {
    match callsite_fn_consts.get(key) {
        None => {
            callsite_fn_consts.insert(key.clone(), incoming);
        }
        Some(prev) => {
            let merged: Vec<Option<FnId>> = prev
                .iter()
                .zip(incoming.iter())
                .map(|(a, b)| if a == b { *a } else { None })
                .collect();
            callsite_fn_consts.insert(key.clone(), merged);
        }
    }
}

enum ProtocolDispatch {
    Local(SpecKey, usize),
    External {
        target: crate::modules::identity::ExportKey,
        input: Vec<crate::types::KeySlot>,
        demand: ReturnDemand,
    },
}

/// Discovery walk for one spec. Walks the spec's body and records every spec it
/// currently emits into `out.emits`, tagged by `EmitterSite`. The driver diffs
/// against the spec's previous emits and transitions provenance.
///
/// Emit kinds:
///   - `EmitSlot::Direct` for `Term::Call` / `Term::TailCall`.
///   - `EmitSlot::ClosureCall` for `Term::CallClosure` / `Term::TailCallClosure`
///     callsites, whether the target comes from `fn_constants` or a closure
///     literal clause.
///   - `EmitSlot::Cont` for the continuation of Call/CallClosure/Receive.
///   - `EmitSlot::MakeClosure` for the any-key body spec reachable through a
///     closure value.
///
/// `Prim::MakeClosure` also records a closure value handle in
/// `out.closure_handles`. Codegen resolves the lambda body directly through the
/// any-key body spec.
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
    caller_ft: &SpecPlan,
    m: &Module,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    recursive_fns: &std::collections::HashSet<FnId>,
    caller_spec_key: &SpecKey,
    callsite_fn_consts: &mut CallsiteFnConsts,
    out: &mut WalkResult,
) {
    WALK_CALLS.with(|c| c.set(c.get() + 1));
    let any_ty = t.any();
    DiscoveryWalk {
        t,
        caller_ft,
        m,
        effective_returns,
        recursive_fns,
        caller_spec_key,
        callsite_fn_consts,
        out,
        any_ty,
    }
    .walk_fn(f);
}

struct DiscoveryWalk<'a, T>
where
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
{
    t: &'a mut T,
    caller_ft: &'a SpecPlan,
    m: &'a Module,
    effective_returns: &'a HashMap<SpecKey, crate::types::Ty>,
    recursive_fns: &'a HashSet<FnId>,
    caller_spec_key: &'a SpecKey,
    callsite_fn_consts: &'a mut CallsiteFnConsts,
    out: &'a mut WalkResult,
    any_ty: crate::types::Ty,
}

impl<T> DiscoveryWalk<'_, T>
where
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
{
    fn walk_fn(&mut self, f: &FnIr) {
        for b in &f.blocks {
            if !self.caller_ft.reachable_blocks.contains(&b.id) {
                continue;
            }
            let mut env: HashMap<Var, crate::types::Ty> = self
                .caller_ft
                .block_envs
                .get(&b.id)
                .cloned()
                .unwrap_or_default();
            self.walk_statements(&b.stmts, &mut env);
            self.walk_terminator(&b.terminator, &env);
        }
    }

    fn walk_statements(&mut self, stmts: &[Stmt], env: &mut HashMap<Var, crate::types::Ty>) {
        for stmt in stmts {
            let Stmt::Let(v, prim) = stmt;
            self.record_make_closure_handle(prim, env);
            let pt_ty = super::prim::type_prim(self.t, prim, env, self.m, &HashSet::new());
            env.insert(*v, pt_ty);
        }
    }

    fn walk_terminator(&mut self, term: &Term, env: &HashMap<Var, crate::types::Ty>) {
        let Some(term_ident) = term.ident().cloned() else {
            return;
        };
        for BlockCallsite { slot, kind } in
            block_callsites(self.t, term, env, &self.caller_ft.fn_constants)
        {
            self.record_callsite(term, &term_ident, env, slot, kind);
        }
        self.seed_receive_matched_outcomes(term);
    }

    fn record_make_closure_handle(&mut self, prim: &Prim, env: &HashMap<Var, crate::types::Ty>) {
        let Prim::MakeClosure(mk_ident, lam_fn_id, captured) = prim else {
            return;
        };
        let Some(&jj) = self.m.fn_idx.get(lam_fn_id) else {
            return;
        };
        let lam = &self.m.fns[jj];
        let n_params = lam.block(lam.entry).params.len();
        let captures: Vec<crate::types::Ty> = captured
            .iter()
            .map(|cv| {
                env.get(cv)
                    .cloned()
                    .expect("MakeClosure: captured var unbound")
            })
            .collect();
        self.out.closure_handles.insert((*lam_fn_id, captures));
        let any_key = spec_key_for_fn(lam, vec![self.any_ty.clone(); n_params]);
        self.emit(EmitSlot::MakeClosure, mk_ident.clone(), any_key);
    }

    fn record_callsite(
        &mut self,
        term: &Term,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, crate::types::Ty>,
        slot: EmitSlot,
        kind: CallsiteKind,
    ) {
        match kind {
            CallsiteKind::Direct { callee, args } => {
                self.record_direct_call(term, term_ident, env, slot, callee, args);
            }
            CallsiteKind::CallClosureKnown { target, args } => {
                self.record_known_closure_call(term, term_ident, env, slot, target, args);
            }
            CallsiteKind::ClosureLit {
                fn_id,
                captures,
                args,
            } => {
                self.record_closure_literal_call(
                    term, term_ident, env, slot, fn_id, captures, args,
                );
            }
            CallsiteKind::Cont { cont, source } => {
                self.record_continuation(term_ident, env, slot, cont.clone(), source);
            }
        }
    }

    fn record_direct_call(
        &mut self,
        term: &Term,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, crate::types::Ty>,
        slot: EmitSlot,
        callee: FnId,
        args: &[Var],
    ) {
        if let Some(dispatch) = self.protocol_dispatch_key(callee, args, env) {
            let cid = WalkResult::callsite_id(self.caller_spec_key, term_ident, slot);
            let ProtocolDispatch::Local(mut entry_key, n_params) = dispatch else {
                if let ProtocolDispatch::External {
                    target,
                    input,
                    demand,
                } = dispatch
                {
                    self.out.record_external_dispatch(
                        self.caller_spec_key,
                        term_ident,
                        slot,
                        target,
                        input,
                        demand.clone(),
                    );
                    self.out.record_return_use(&cid, demand, None);
                }
                return;
            };
            if let Term::Call { continuation, .. } = term {
                let target_fn = entry_key.fn_id;
                let (demand, context_plan) = direct_call_return_plan(
                    self.t,
                    self.m,
                    self.caller_spec_key,
                    env,
                    target_fn,
                    args,
                    continuation,
                );
                entry_key.demand = demand;
                self.out
                    .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
                self.out
                    .record_return_use(&cid, entry_key.demand.clone(), context_plan);
            } else if matches!(term, Term::TailCall { .. }) {
                let target_fn = entry_key.fn_id;
                let (demand, context_plan) =
                    tail_call_return_plan(self.caller_spec_key, target_fn, args);
                entry_key.demand = demand;
                self.out
                    .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
                self.out
                    .record_return_use(&cid, entry_key.demand.clone(), context_plan);
            } else {
                self.out
                    .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
            }
            let per_arg = self.fn_constant_args(args, n_params);
            merge_callsite_fn_consts(self.callsite_fn_consts, &entry_key, per_arg);
            self.emit(slot, term_ident.clone(), entry_key);
            return;
        }
        let Some((mut entry_key, n_params)) = self.direct_call_key(callee, args, env) else {
            self.record_external_call(term, term_ident, env, slot, args);
            return;
        };
        let cid = WalkResult::callsite_id(self.caller_spec_key, term_ident, slot);
        if let Term::Call { continuation, .. } = term {
            let (demand, context_plan) = direct_call_return_plan(
                self.t,
                self.m,
                self.caller_spec_key,
                env,
                callee,
                args,
                continuation,
            );
            entry_key.demand = demand;
            self.out
                .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
            self.out
                .record_return_use(&cid, entry_key.demand.clone(), context_plan);
        } else if matches!(term, Term::TailCall { .. }) {
            let (demand, context_plan) = tail_call_return_plan(self.caller_spec_key, callee, args);
            entry_key.demand = demand;
            self.out
                .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
            self.out
                .record_return_use(&cid, entry_key.demand.clone(), context_plan);
        } else {
            self.out
                .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
        }
        let per_arg = self.fn_constant_args(args, n_params);
        merge_callsite_fn_consts(self.callsite_fn_consts, &entry_key, per_arg);
        self.emit(slot, term_ident.clone(), entry_key);
    }

    fn record_external_call(
        &mut self,
        term: &Term,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, crate::types::Ty>,
        slot: EmitSlot,
        args: &[Var],
    ) {
        let Some(target) = self.external_target(term_ident, slot) else {
            return;
        };
        let input = self.external_call_input(callee_from_term(term), args, env, target.arity);
        let demand = match term {
            Term::TailCall { .. } => self.caller_spec_key.demand.clone(),
            _ => ReturnDemand::value(),
        };
        let cid = self.out.record_external_dispatch(
            self.caller_spec_key,
            term_ident,
            slot,
            target,
            input,
            demand.clone(),
        );
        if matches!(term, Term::Call { .. } | Term::TailCall { .. }) {
            self.out.record_return_use(&cid, demand, None);
        }
    }

    fn record_known_closure_call(
        &mut self,
        term: &Term,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, crate::types::Ty>,
        slot: EmitSlot,
        target: FnId,
        args: &[Var],
    ) {
        let Some(mut target_key) = self.direct_call_key(target, args, env).map(|(key, _)| key)
        else {
            return;
        };
        self.inherit_tail_closure_demand(term, &mut target_key);
        self.out
            .record_dispatch(self.caller_spec_key, term_ident, slot, target_key.clone());
        self.emit(slot, term_ident.clone(), target_key);
    }

    fn record_closure_literal_call(
        &mut self,
        term: &Term,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, crate::types::Ty>,
        slot: EmitSlot,
        fn_id: FnId,
        captures: Vec<crate::types::Ty>,
        args: &[Var],
    ) {
        let Some(mut target_key) = self.closure_lit_key(fn_id, captures, args, env) else {
            return;
        };
        self.inherit_tail_closure_demand(term, &mut target_key);
        self.out
            .record_dispatch(self.caller_spec_key, term_ident, slot, target_key.clone());
        self.emit(slot, term_ident.clone(), target_key);
    }

    fn record_continuation(
        &mut self,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, crate::types::Ty>,
        slot: EmitSlot,
        cont: crate::fz_ir::Cont,
        source: ContSource,
    ) {
        let Some(slot0) = self.continuation_slot0(term_ident, env, &source) else {
            return;
        };
        let none_ty = self.t.none();
        if self.t.is_equivalent(&slot0, &none_ty) {
            return;
        }
        let Some(&j) = self.m.fn_idx.get(&cont.fn_id) else {
            return;
        };
        let cont_fn = &self.m.fns[j];
        let n_params = cont_fn.block(cont_fn.entry).params.len();
        let mut key = cont_key_from_slot0(&self.any_ty, n_params, slot0, &cont.captured, env);
        if self.has_bottom_arg(&key) {
            return;
        }
        let per_param = self.continuation_fn_constants(&cont, n_params);
        let demand = continuation_return_demand(self.m, self.caller_spec_key, &cont, &source);
        let mut entry_key = spec_key_for_fn(cont_fn, std::mem::take(&mut key));
        entry_key.demand = demand.clone();
        let context_plan = continuation_empty_tail_plan(
            self.t,
            self.m,
            self.caller_spec_key,
            &cont,
            &source,
            &demand,
            &entry_key,
        );
        merge_callsite_fn_consts(self.callsite_fn_consts, &entry_key, per_param);
        let cid =
            self.out
                .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
        if let Some(plan) = context_plan {
            self.out.record_return_context_plan(&cid, plan);
        }
        self.emit(slot, term_ident.clone(), entry_key);
    }

    fn continuation_slot0(
        &mut self,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, crate::types::Ty>,
        source: &ContSource,
    ) -> Option<crate::types::Ty> {
        match *source {
            ContSource::Call { callee, args } => {
                if self.external_target(term_ident, EmitSlot::Direct).is_some() {
                    return self.external_call_return_slot0(callee, args, env);
                }
                let callee_key = self.direct_return_key(term_ident, callee, args, env);
                let callee_arg_tys = crate::types::key_slots_to_tys(self.t, &callee_key.input);
                let declared = self.declared_call_return(callee, &callee_arg_tys);
                if declared.is_none() {
                    self.out.return_reads.push(callee_key.clone());
                }
                declared.or_else(|| self.effective_returns.get(&callee_key).cloned())
            }
            ContSource::CallClosure { closure, args } => {
                self.closure_return_slot0(closure, args, env)
            }
            ContSource::Receive => Some(self.any_ty.clone()),
        }
    }

    fn external_call_return_slot0(
        &mut self,
        callee: FnId,
        args: &[Var],
        env: &HashMap<Var, crate::types::Ty>,
    ) -> Option<crate::types::Ty> {
        let arg_tys = self.arg_tys(args, env);
        self.declared_call_return(callee, &arg_tys)
            .or_else(|| Some(self.any_ty.clone()))
    }

    fn external_call_input(
        &mut self,
        callee: Option<FnId>,
        args: &[Var],
        env: &HashMap<Var, crate::types::Ty>,
        arity: usize,
    ) -> Vec<crate::types::KeySlot> {
        if let Some(callee) = callee
            && let Some(spec) = self.m.declared_specs.get(&callee)
            && spec.params.len() == arity
        {
            return crate::types::key_slots_from_tys(spec.params.clone());
        }
        crate::types::key_slots_from_tys(padded_direct_input_tys(
            self.t,
            self.arg_tys(args, env),
            arity,
        ))
    }

    fn external_target(
        &self,
        term_ident: &CallsiteIdent,
        slot: EmitSlot,
    ) -> Option<crate::modules::identity::ExportKey> {
        let cid = WalkResult::callsite_id(self.caller_spec_key, term_ident, slot);
        self.m
            .external_call_edges
            .iter()
            .find(|edge| edge.callsite == cid)
            .map(|edge| edge.target.clone())
    }

    fn direct_return_key(
        &mut self,
        term_ident: &CallsiteIdent,
        callee: FnId,
        args: &[Var],
        env: &HashMap<Var, crate::types::Ty>,
    ) -> SpecKey {
        let direct_cid =
            WalkResult::callsite_id(self.caller_spec_key, term_ident, EmitSlot::Direct);
        self.out
            .call_edges
            .get(&direct_cid)
            .and_then(CallEdgePlan::local_target)
            .cloned()
            .unwrap_or_else(|| {
                let arg_tys = self.arg_tys(args, env);
                recursive_direct_spec_key(
                    self.t,
                    self.m,
                    self.recursive_fns,
                    self.caller_spec_key.fn_id,
                    callee,
                    arg_tys,
                )
            })
    }

    fn closure_return_slot0(
        &mut self,
        closure: Var,
        args: &[Var],
        env: &HashMap<Var, crate::types::Ty>,
    ) -> Option<crate::types::Ty> {
        if let Some(&target) = self.caller_ft.fn_constants.get(&closure) {
            return self.known_closure_return_slot0(target, args, env);
        }
        let Some(cv_descr) = env.get(&closure) else {
            return Some(self.any_ty.clone());
        };
        let arg_tys = self.arg_tys(args, env);
        self.record_closure_literal_return_reads(cv_descr, &arg_tys);
        resolve_closure_return(self.t, cv_descr, self.effective_returns, &arg_tys)
    }

    fn known_closure_return_slot0(
        &mut self,
        target: FnId,
        args: &[Var],
        env: &HashMap<Var, crate::types::Ty>,
    ) -> Option<crate::types::Ty> {
        let target_fn = self.m.fn_by_id(target);
        let n_params = target_fn.block(target_fn.entry).params.len();
        let callee_key = recursive_direct_spec_key_for_arity(
            self.t,
            self.m,
            self.recursive_fns,
            self.caller_spec_key.fn_id,
            target,
            self.arg_tys(args, env),
            n_params,
            None,
        );
        let callee_arg_tys = crate::types::key_slots_to_tys(self.t, &callee_key.input);
        let declared = self.declared_call_return(target, &callee_arg_tys);
        if declared.is_none() {
            self.out.return_reads.push(callee_key.clone());
        }
        declared.or_else(|| self.effective_returns.get(&callee_key).cloned())
    }

    fn record_closure_literal_return_reads(
        &mut self,
        cv_descr: &crate::types::Ty,
        arg_tys: &[crate::types::Ty],
    ) {
        let Some(clauses) = self.t.callable_clauses(cv_descr) else {
            return;
        };
        for clause in clauses {
            if let Some(crate::types::ClosureLitInfo { target, captures }) = clause.closure
                && clause.args.len() == arg_tys.len()
            {
                let mut full_key = captures.clone();
                full_key.extend_from_slice(arg_tys);
                let callee_key = recursive_direct_spec_key(
                    self.t,
                    self.m,
                    self.recursive_fns,
                    self.caller_spec_key.fn_id,
                    target.into(),
                    full_key,
                );
                self.out.return_reads.push(callee_key);
            }
        }
    }

    fn seed_receive_matched_outcomes(&mut self, term: &Term) {
        let Term::ReceiveMatched { clauses, after, .. } = term else {
            return;
        };
        for c in clauses {
            let ident = CallsiteIdent::from_source(c.span);
            self.emit_receive_outcome(c.body, ident.clone());
            if let Some(guard) = c.guard {
                self.emit_receive_outcome(guard, ident);
            }
        }
        if let Some(a) = after {
            self.emit_receive_outcome(a.body, CallsiteIdent::from_source(a.span));
        }
    }

    fn emit_receive_outcome(&mut self, fid: FnId, ident: CallsiteIdent) {
        let Some(&j) = self.m.fn_idx.get(&fid) else {
            return;
        };
        let body = &self.m.fns[j];
        let np = body.block(body.entry).params.len();
        let key = crate::fz_ir::receive_outcome_spec_key(&self.any_ty, np);
        self.emit(EmitSlot::Cont, ident, spec_key_for_fn(body, key));
    }

    fn direct_call_key(
        &mut self,
        callee: FnId,
        args: &[Var],
        env: &HashMap<Var, crate::types::Ty>,
    ) -> Option<(SpecKey, usize)> {
        let callee_fn = self.m.fn_idx.get(&callee).map(|j| &self.m.fns[*j])?;
        let n_params = callee_fn.block(callee_fn.entry).params.len();
        let dispatch_key = padded_direct_input_tys(self.t, self.arg_tys(args, env), n_params);
        if self.has_bottom_arg(&dispatch_key) {
            return None;
        }
        let key = recursive_direct_spec_key_for_arity(
            self.t,
            self.m,
            self.recursive_fns,
            self.caller_spec_key.fn_id,
            callee,
            dispatch_key,
            n_params,
            None,
        );
        Some((key, n_params))
    }

    fn protocol_dispatch_key(
        &mut self,
        callee: FnId,
        args: &[Var],
        env: &HashMap<Var, crate::types::Ty>,
    ) -> Option<ProtocolDispatch> {
        let target = self.m.protocol_call_targets.get(&callee)?.clone();
        let receiver_ty = args
            .first()
            .and_then(|receiver| env.get(receiver))
            .cloned()
            .unwrap_or_else(|| self.any_ty.clone());
        let mut matches = self
            .m
            .protocol_registry
            .impls
            .values()
            .filter(|fact| fact.protocol == target.protocol)
            .filter(|fact| {
                let target_ty = crate::protocols::impl_target_type(self.t, &fact.target);
                self.t.is_subtype(&receiver_ty, &target_ty)
            })
            .filter_map(|fact| {
                fact.callbacks
                    .get(&(target.callback.clone(), target.arity))
                    .cloned()
            })
            .collect::<Vec<_>>();
        matches.sort();
        matches.dedup();
        let export = matches.into_iter().next()?;
        let fn_name = format!("{}.{}", export.module, export.name);
        if let Some(impl_fn) = self.m.fn_by_name(&fn_name).map(|f| f.id) {
            return self
                .direct_call_key(impl_fn, args, env)
                .map(|(key, n_params)| ProtocolDispatch::Local(key, n_params));
        }
        let input = crate::types::key_slots_from_tys(padded_direct_input_tys(
            self.t,
            self.arg_tys(args, env),
            export.arity,
        ));
        Some(ProtocolDispatch::External {
            target: export,
            input,
            demand: ReturnDemand::value(),
        })
    }

    fn closure_lit_key(
        &mut self,
        fn_id: FnId,
        captures: Vec<crate::types::Ty>,
        args: &[Var],
        env: &HashMap<Var, crate::types::Ty>,
    ) -> Option<SpecKey> {
        let target_fn = self.m.fn_idx.get(&fn_id).map(|j| &self.m.fns[*j])?;
        let n_params = target_fn.block(target_fn.entry).params.len();
        let mut dispatch_key = captures;
        dispatch_key.extend(self.arg_tys(args, env));
        dispatch_key = padded_direct_input_tys(self.t, dispatch_key, n_params);
        if self.has_bottom_arg(&dispatch_key) {
            return None;
        }
        Some(recursive_direct_spec_key_for_arity(
            self.t,
            self.m,
            self.recursive_fns,
            self.caller_spec_key.fn_id,
            fn_id,
            dispatch_key,
            n_params,
            None,
        ))
    }

    fn fn_constant_args(&self, args: &[Var], n_params: usize) -> Vec<Option<FnId>> {
        let mut per_arg: Vec<Option<FnId>> = args
            .iter()
            .map(|av| self.caller_ft.fn_constants.get(av).copied())
            .collect();
        pad_and_truncate(&mut per_arg, n_params, &None);
        per_arg
    }

    fn continuation_fn_constants(
        &self,
        cont: &crate::fz_ir::Cont,
        n_params: usize,
    ) -> Vec<Option<FnId>> {
        let mut per_param = vec![None; n_params];
        for (k, cvv) in cont.captured.iter().enumerate() {
            if let Some(p) = per_param.get_mut(k + 1) {
                *p = self.caller_ft.fn_constants.get(cvv).copied();
            }
        }
        per_param
    }

    fn arg_tys(&self, args: &[Var], env: &HashMap<Var, crate::types::Ty>) -> Vec<crate::types::Ty> {
        args.iter()
            .map(|av| env.get(av).cloned().unwrap_or_else(|| self.any_ty.clone()))
            .collect()
    }

    fn inherit_tail_closure_demand(&self, term: &Term, key: &mut SpecKey) {
        if matches!(term, Term::TailCallClosure { .. }) {
            key.demand = self.caller_spec_key.demand.clone();
        }
    }

    fn has_bottom_arg(&mut self, key: &[crate::types::Ty]) -> bool {
        let none_ty = self.t.none();
        key.iter().any(|ty| self.t.is_equivalent(ty, &none_ty))
    }

    fn declared_call_return(
        &mut self,
        callee: FnId,
        arg_tys: &[crate::types::Ty],
    ) -> Option<crate::types::Ty> {
        let spec = self.m.declared_specs.get(&callee)?;
        if spec.params.len() != arg_tys.len() {
            return None;
        }
        let mut sigma = HashMap::new();
        for (pattern, witness) in spec.params.iter().zip(arg_tys.iter()) {
            self.t
                .collect_instantiation_subst(pattern, witness, &mut sigma);
        }
        for (var, bound) in &spec.constraints {
            let actual = sigma.get(var)?;
            if !self.t.is_subtype(actual, bound) {
                return None;
            }
        }
        for (pattern, witness) in spec.params.iter().zip(arg_tys.iter()) {
            let expected = self.t.instantiate(pattern, &sigma);
            if !self.t.has_vars(witness) && !self.t.is_subtype(witness, &expected) {
                return None;
            }
        }
        let ret = self.t.instantiate(&spec.result, &sigma);
        let owner = &self.m.fn_by_id(self.caller_spec_key.fn_id).owner_module;
        Some(
            self.t
                .mint_owned_resource_aliases(ret, owner, &self.m.opaque_inners),
        )
    }

    fn emit(&mut self, slot: EmitSlot, ident: CallsiteIdent, target: SpecKey) {
        self.out.emits.push((
            EmitterSite {
                caller: self.caller_spec_key.clone(),
                ident,
                slot,
            },
            target,
        ));
    }
}

fn pad_and_truncate<T: Clone>(items: &mut Vec<T>, n: usize, pad: &T) {
    while items.len() < n {
        items.push(pad.clone());
    }
    items.truncate(n);
}

fn callee_from_term(term: &Term) -> Option<FnId> {
    match term {
        Term::Call { callee, .. } | Term::TailCall { callee, .. } => Some(*callee),
        _ => None,
    }
}
