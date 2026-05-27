use super::closures::resolve_closure_return;
use super::fn_types::{
    CallsiteFnConsts, EmitterSite, ReturnContextPlan, ReturnContextPlanKey, ReturnDemand, SpecKey,
    SpecPlan, WALK_CALLS, padded_direct_input_tys, recursive_direct_spec_key,
    recursive_direct_spec_key_for_arity, spec_key_for_fn,
};
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
    /// agrees with the dispatch fact consumed by codegen.
    pub(crate) emits: Vec<(EmitterSite, SpecKey)>,
    /// Per-callsite dispatch fact: the spec key the planner resolved for this
    /// site after recursive-key normalization. This is the same key emitted
    /// above, so `SpecPlan.dispatches` and codegen agree by construction.
    ///
    /// Populated for `Direct`, `ClosureCall`, and `Cont` slots. `MakeClosure`
    /// emits an any-key body spec but does not record a dispatch fact.
    pub(crate) dispatch_targets: HashMap<crate::fz_ir::CallsiteId, SpecKey>,
    /// Per-callsite typed return-use facts for this caller spec. These facts
    /// describe the result hole reached by the call result; they do not imply
    /// whole-caller demand inheritance.
    pub(crate) return_uses: HashMap<crate::fz_ir::CallsiteId, ReturnDemand>,
    /// Typed return-context lowering plans, keyed by caller spec and callsite.
    pub(crate) return_context_plans: HashMap<ReturnContextPlanKey, ReturnContextPlan>,
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
        self.dispatch_targets.insert(cid.clone(), target);
        cid
    }

    fn record_return_use(
        &mut self,
        caller: &SpecKey,
        callsite: &CallsiteId,
        demand: ReturnDemand,
        plan: Option<ReturnContextPlan>,
    ) {
        self.return_uses.insert(callsite.clone(), demand);
        if let Some(plan) = plan {
            self.return_context_plans
                .insert(ReturnContextPlanKey::new(caller, callsite), plan);
        }
    }

    fn record_return_context_plan(
        &mut self,
        caller: &SpecKey,
        callsite: &CallsiteId,
        plan: ReturnContextPlan,
    ) {
        self.return_context_plans
            .insert(ReturnContextPlanKey::new(caller, callsite), plan);
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
        let Some((mut entry_key, n_params)) = self.direct_call_key(callee, args, env) else {
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
            self.out.record_return_use(
                self.caller_spec_key,
                &cid,
                entry_key.demand.clone(),
                context_plan,
            );
        } else if matches!(term, Term::TailCall { .. }) {
            let (demand, context_plan) = tail_call_return_plan(self.caller_spec_key, callee, args);
            entry_key.demand = demand;
            self.out.record_return_use(
                self.caller_spec_key,
                &cid,
                entry_key.demand.clone(),
                context_plan,
            );
        }
        self.out
            .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
        let per_arg = self.fn_constant_args(args, n_params);
        merge_callsite_fn_consts(self.callsite_fn_consts, &entry_key, per_arg);
        self.emit(slot, term_ident.clone(), entry_key);
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
        let mut key = self.continuation_key(&cont, env, n_params, slot0);
        if self.has_bottom_arg(&key) {
            return;
        }
        let per_param = self.continuation_fn_constants(&cont, n_params);
        let demand = continuation_return_demand(self.m, self.caller_spec_key, &cont, &source);
        let mut entry_key = spec_key_for_fn(cont_fn, std::mem::take(&mut key));
        entry_key.demand = demand.clone();
        if let Some(plan) = continuation_empty_tail_plan(
            self.t,
            self.m,
            self.caller_spec_key,
            &cont,
            &source,
            &demand,
            &entry_key,
        ) {
            let cid = WalkResult::callsite_id(self.caller_spec_key, term_ident, slot);
            self.out
                .record_return_context_plan(self.caller_spec_key, &cid, plan);
        }
        merge_callsite_fn_consts(self.callsite_fn_consts, &entry_key, per_param);
        self.out
            .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
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
                let callee_key = self.direct_return_key(term_ident, callee, args, env);
                self.out.return_reads.push(callee_key.clone());
                self.effective_returns.get(&callee_key).cloned()
            }
            ContSource::CallClosure { closure, args } => {
                self.closure_return_slot0(closure, args, env)
            }
            ContSource::Receive => Some(self.any_ty.clone()),
        }
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
            .dispatch_targets
            .get(&direct_cid)
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
        self.out.return_reads.push(callee_key.clone());
        self.effective_returns.get(&callee_key).cloned()
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

    fn continuation_key(
        &self,
        cont: &crate::fz_ir::Cont,
        env: &HashMap<Var, crate::types::Ty>,
        n_params: usize,
        slot0: crate::types::Ty,
    ) -> Vec<crate::types::Ty> {
        let mut key = vec![self.any_ty.clone(); n_params];
        if let Some(first) = key.first_mut() {
            *first = slot0;
        }
        for (k, cvv) in cont.captured.iter().enumerate() {
            if let Some(p) = key.get_mut(k + 1) {
                *p = env.get(cvv).cloned().unwrap_or_else(|| self.any_ty.clone());
            }
        }
        key
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
