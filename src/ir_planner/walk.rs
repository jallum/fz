use super::fn_types::{
    CallEdgePlan, CallEdgeTarget, CallableCapability, CallsiteCallableCapabilities, EmitterSite,
    FixedPointInputObservation, FixedPointSlotSummaries, FnEffects, ReturnContextPlan,
    ReturnDemand, SpecKey, SpecPlan, WALK_CALLS, fixed_point_input_tys_for_arity,
    forwarded_return_contract_for_target, normalize_result_correspondence_key,
    padded_direct_input_tys, return_contract_for_target, spec_key_for_fn, spec_key_for_fn_id,
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
    /// Recursive callee inputs observed before fixed-point summaries are applied.
    /// The summaries are consumed by spec-key normalization, so normalized spec
    /// keys cannot be the source of truth for widening them.
    pub(crate) fixed_point_inputs: Vec<FixedPointInputObservation>,
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
                return_contract: None,
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
                return_contract: None,
            },
        );
        cid
    }

    fn record_return_contract(
        &mut self,
        callsite: &CallsiteId,
        target: SpecKey,
        plan: Option<ReturnContextPlan>,
    ) {
        let edge = self
            .call_edges
            .get_mut(callsite)
            .expect("return contracts require an existing call edge");
        edge.return_contract = Some(
            return_contract_for_target(target.clone(), plan.clone()).unwrap_or_else(|| {
                panic!(
                    "return demand {:?} for {:?} requires a matching executable return strategy; plan={:?}",
                    target.demand, callsite, plan
                )
            }),
        );
    }

    fn record_forwarded_return_contract(&mut self, callsite: &CallsiteId, target: SpecKey) {
        let edge = self
            .call_edges
            .get_mut(callsite)
            .expect("return contracts require an existing call edge");
        edge.return_contract = Some(forwarded_return_contract_for_target(target));
    }
}

fn merge_callsite_callable_capabilities(
    callsite_callable_capabilities: &mut CallsiteCallableCapabilities,
    key: &SpecKey,
    incoming: Vec<Option<CallableCapability>>,
) {
    match callsite_callable_capabilities.get(key) {
        None => {
            callsite_callable_capabilities.insert(key.clone(), incoming);
        }
        Some(prev) => {
            let merged: Vec<Option<CallableCapability>> = prev
                .iter()
                .zip(incoming.iter())
                .map(|(a, b)| match (a, b) {
                    (None, None) => None,
                    (Some(a), Some(b)) if a == b => Some(a.clone()),
                    _ => Some(CallableCapability::OpaqueCallable),
                })
                .collect();
            callsite_callable_capabilities.insert(key.clone(), merged);
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
///     callsites, whether the target comes from a known callable capability or
///     a closure literal clause.
///   - `EmitSlot::Cont` for the continuation of Call/CallClosure/Receive.
///   - `EmitSlot::MakeClosure` for the any-key body spec reachable through a
///     closure value.
///
/// `Prim::MakeClosure` emits the lambda's any-key body spec. Closure values do
/// not add a separate planner artifact.
///
/// `recursive_fns`: calls into recursive functions are normalized
/// immediately with `widen_for_recursive_spec_key`, including the first
/// external entry into the recursive component. The dispatch fact and
/// emitted spec key both use that normalized key, so codegen cannot
/// resolve a different narrow spec from the one the worklist typed.
/// Cont keys are not normalized: they model dataflow from a concrete
/// producer, not a recursive function-entry fixed point.
#[allow(clippy::too_many_arguments)]
pub(super) fn walk_spec_for_discovery<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    f: &FnIr,
    caller_ft: &SpecPlan,
    m: &Module,
    fn_effects: &FnEffects,
    activation_returns: &super::worklist::ActivationReturnFacts,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &FixedPointSlotSummaries,
    caller_spec_key: &SpecKey,
    callsite_callable_capabilities: &mut CallsiteCallableCapabilities,
    out: &mut WalkResult,
) {
    WALK_CALLS.with(|c| c.set(c.get() + 1));
    let any_ty = t.any();
    DiscoveryWalk {
        t,
        caller_ft,
        m,
        fn_effects,
        activation_returns,
        recursive_fns,
        slot_summaries,
        caller_spec_key,
        callsite_callable_capabilities,
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
    fn_effects: &'a FnEffects,
    activation_returns: &'a super::worklist::ActivationReturnFacts,
    recursive_fns: &'a HashSet<FnId>,
    slot_summaries: &'a FixedPointSlotSummaries,
    caller_spec_key: &'a SpecKey,
    callsite_callable_capabilities: &'a mut CallsiteCallableCapabilities,
    out: &'a mut WalkResult,
    any_ty: crate::types::Ty,
}

enum Slot0Knowledge {
    Known(crate::types::Ty),
    Pending,
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
            self.record_make_closure_target(prim);
            let pt_ty = super::prim::type_prim(self.t, prim, env, self.m, &HashSet::new());
            env.insert(*v, pt_ty);
        }
    }

    fn walk_terminator(&mut self, term: &Term, env: &HashMap<Var, crate::types::Ty>) {
        let Some(term_ident) = term.ident().cloned() else {
            return;
        };
        let known_fns: HashMap<Var, FnId> = self
            .caller_ft
            .callable_capabilities
            .iter()
            .filter_map(|(var, cap)| cap.known_fn().map(|fid| (*var, fid)))
            .collect();
        for BlockCallsite { slot, kind } in block_callsites(self.t, term, env, &known_fns) {
            self.record_callsite(term, &term_ident, env, slot, kind);
        }
        self.seed_receive_matched_outcomes(term);
    }

    fn record_make_closure_target(&mut self, prim: &Prim) {
        let Prim::MakeClosure(mk_ident, lam_fn_id, _) = prim else {
            return;
        };
        let Some(&jj) = self.m.fn_idx.get(lam_fn_id) else {
            return;
        };
        let lam = &self.m.fns[jj];
        let n_params = lam.block(lam.entry).params.len();
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
        if self.external_target(term_ident, slot).is_some() {
            self.record_external_call(term, term_ident, env, slot, args);
            return;
        }
        if let Some(dispatch) = self.protocol_dispatch_key(callee, args, env) {
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
                        demand,
                    );
                }
                return;
            };
            let cid = WalkResult::callsite_id(self.caller_spec_key, term_ident, slot);
            if let Term::Call { continuation, .. } = term {
                let target_fn = entry_key.fn_id;
                let (demand, context_plan) = direct_call_return_plan(
                    self.t,
                    self.m,
                    self.fn_effects,
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
                    .record_return_contract(&cid, entry_key.clone(), context_plan);
            } else if matches!(term, Term::TailCall { .. }) {
                let target_fn = entry_key.fn_id;
                let (demand, context_plan) =
                    tail_call_return_plan(self.m, self.caller_spec_key, target_fn, args);
                entry_key.demand = demand;
                self.out
                    .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
                if let Some(context_plan) = context_plan {
                    self.out
                        .record_return_contract(&cid, entry_key.clone(), Some(context_plan));
                } else {
                    self.out
                        .record_forwarded_return_contract(&cid, entry_key.clone());
                }
            } else {
                self.out
                    .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
            }
            let per_arg = self.callable_capability_args(args, n_params);
            merge_callsite_callable_capabilities(
                self.callsite_callable_capabilities,
                &entry_key,
                per_arg,
            );
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
                self.fn_effects,
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
                .record_return_contract(&cid, entry_key.clone(), context_plan);
        } else if matches!(term, Term::TailCall { .. }) {
            let (demand, context_plan) =
                tail_call_return_plan(self.m, self.caller_spec_key, callee, args);
            entry_key.demand = demand;
            self.out
                .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
            if let Some(context_plan) = context_plan {
                self.out
                    .record_return_contract(&cid, entry_key.clone(), Some(context_plan));
            } else {
                self.out
                    .record_forwarded_return_contract(&cid, entry_key.clone());
            }
        } else {
            self.out
                .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
        }
        let per_arg = self.callable_capability_args(args, n_params);
        merge_callsite_callable_capabilities(
            self.callsite_callable_capabilities,
            &entry_key,
            per_arg,
        );
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
        self.out.record_external_dispatch(
            self.caller_spec_key,
            term_ident,
            slot,
            target,
            input,
            demand.clone(),
        );
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
        let slot0 = match slot0 {
            Slot0Knowledge::Known(ty) => ty,
            Slot0Knowledge::Pending => return,
        };
        let Some(&j) = self.m.fn_idx.get(&cont.fn_id) else {
            return;
        };
        let cont_fn = &self.m.fns[j];
        let n_params = cont_fn.block(cont_fn.entry).params.len();
        let mut key = cont_key_from_slot0(&self.any_ty, n_params, slot0, &cont.captured, env);
        key = normalize_result_correspondence_key(self.t, self.m, cont.fn_id, key);
        if self.has_bottom_arg(&key) {
            return;
        }
        let per_param_capabilities = self.continuation_callable_capabilities(&cont, n_params);
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
        merge_callsite_callable_capabilities(
            self.callsite_callable_capabilities,
            &entry_key,
            per_param_capabilities,
        );
        let cid =
            self.out
                .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
        if let Some(plan) = context_plan {
            let contract_target = match &plan {
                ReturnContextPlan::ContinuationEmptyTail { target, .. } => target.clone(),
                _ => entry_key.clone(),
            };
            self.out
                .record_return_contract(&cid, contract_target.clone(), Some(plan));
            if contract_target != entry_key {
                self.emit(slot, term_ident.clone(), contract_target);
            }
        }
        self.emit(slot, term_ident.clone(), entry_key);
    }

    fn continuation_slot0(
        &mut self,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, crate::types::Ty>,
        source: &ContSource,
    ) -> Option<Slot0Knowledge> {
        match *source {
            ContSource::Call { callee, args } => {
                let arg_tys = self.arg_tys(args, env);
                let direct_cid =
                    WalkResult::callsite_id(self.caller_spec_key, term_ident, EmitSlot::Direct);
                let target = self
                    .out
                    .call_edges
                    .get(&direct_cid)
                    .and_then(CallEdgePlan::local_target);
                let knowledge = super::worklist::direct_call_result_knowledge(
                    self.t,
                    self.m,
                    self.recursive_fns,
                    self.caller_spec_key,
                    term_ident,
                    callee,
                    &arg_tys,
                    self.activation_returns,
                    self.slot_summaries,
                    target,
                );
                match knowledge.slot0 {
                    super::worklist::ResultSlot0::Known(ty) => Some(Slot0Knowledge::Known(ty)),
                    super::worklist::ResultSlot0::Pending => Some(Slot0Knowledge::Pending),
                }
            }
            ContSource::CallClosure { closure, args } => {
                self.closure_return_slot0(term_ident, closure, args, env)
            }
            ContSource::Receive => Some(Slot0Knowledge::Known(self.any_ty.clone())),
        }
    }

    fn external_call_input(
        &mut self,
        callee: Option<FnId>,
        args: &[Var],
        env: &HashMap<Var, crate::types::Ty>,
        arity: usize,
    ) -> Vec<crate::types::KeySlot> {
        let arg_tys = self.arg_tys(args, env);
        if let Some(callee) = callee
            && let Some(spec_set) = self.m.declared_specs.get(&callee)
            && let Some(params) = crate::specs::unique_matching_params(self.t, spec_set, &arg_tys)
            && params.len() == arity
        {
            return crate::types::key_slots_from_tys(params);
        }
        crate::types::key_slots_from_tys(padded_direct_input_tys(self.t, arg_tys, arity))
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

    fn closure_return_slot0(
        &mut self,
        term_ident: &CallsiteIdent,
        closure: Var,
        args: &[Var],
        env: &HashMap<Var, crate::types::Ty>,
    ) -> Option<Slot0Knowledge> {
        if let Some(target) = self.caller_ft.known_fn(&closure) {
            let knowledge = super::worklist::known_closure_result_knowledge(
                self.t,
                self.m,
                self.recursive_fns,
                self.caller_spec_key,
                term_ident,
                target,
                &self.arg_tys(args, env),
                self.activation_returns,
                self.slot_summaries,
            );
            return Some(match knowledge.slot0 {
                super::worklist::ResultSlot0::Known(ty) => Slot0Knowledge::Known(ty),
                super::worklist::ResultSlot0::Pending => Slot0Knowledge::Pending,
            });
        }
        let Some(cv_descr) = env.get(&closure) else {
            return Some(Slot0Knowledge::Known(self.any_ty.clone()));
        };
        let knowledge = super::worklist::closure_value_result_knowledge(
            self.t,
            self.m,
            self.recursive_fns,
            self.caller_spec_key.fn_id,
            cv_descr,
            &self.arg_tys(args, env),
            self.activation_returns,
            self.slot_summaries,
        );
        Some(match knowledge.slot0 {
            super::worklist::ResultSlot0::Known(ty) => Slot0Knowledge::Known(ty),
            super::worklist::ResultSlot0::Pending => Slot0Knowledge::Pending,
        })
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
        let (observed, input_tys) = fixed_point_input_tys_for_arity(
            self.t,
            self.m,
            self.recursive_fns,
            self.slot_summaries,
            self.caller_spec_key.fn_id,
            callee,
            dispatch_key,
            n_params,
        );
        self.record_fixed_point_input_observation(callee, observed);
        let key = self
            .activation_returns
            .canonical_public_key(self.t, spec_key_for_fn_id(self.m, callee, input_tys));
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
                let target_ty = crate::frontend::protocols::impl_target_type(self.t, &fact.target);
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
        let (observed, input_tys) = fixed_point_input_tys_for_arity(
            self.t,
            self.m,
            self.recursive_fns,
            self.slot_summaries,
            self.caller_spec_key.fn_id,
            fn_id,
            dispatch_key,
            n_params,
        );
        self.record_fixed_point_input_observation(fn_id, observed);
        Some(
            self.activation_returns
                .canonical_public_key(self.t, spec_key_for_fn_id(self.m, fn_id, input_tys)),
        )
    }

    fn record_fixed_point_input_observation(
        &mut self,
        fn_id: FnId,
        input_tys: Vec<crate::types::Ty>,
    ) {
        if !self.recursive_fns.contains(&fn_id) {
            return;
        }
        let f = self.m.fn_by_id(fn_id);
        if f.category == crate::fz_ir::FnCategory::Matcher {
            return;
        }
        if super::fn_types::result_linked_param_slots(self.m, fn_id).is_empty() {
            return;
        }
        self.out
            .fixed_point_inputs
            .push(FixedPointInputObservation { fn_id, input_tys });
    }

    fn callable_capability_args(
        &self,
        args: &[Var],
        n_params: usize,
    ) -> Vec<Option<CallableCapability>> {
        let mut per_arg: Vec<Option<CallableCapability>> = args
            .iter()
            .map(|av| self.caller_ft.callable_capabilities.get(av).cloned())
            .collect();
        pad_and_truncate(&mut per_arg, n_params, &None);
        per_arg
    }

    fn continuation_callable_capabilities(
        &self,
        cont: &crate::fz_ir::Cont,
        n_params: usize,
    ) -> Vec<Option<CallableCapability>> {
        let mut per_param = vec![None; n_params];
        for (k, cvv) in cont.captured.iter().enumerate() {
            if let Some(p) = per_param.get_mut(k + 1) {
                *p = self.caller_ft.callable_capabilities.get(cvv).cloned();
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

fn callee_from_term(term: &Term) -> Option<FnId> {
    match term {
        Term::Call { callee, .. } | Term::TailCall { callee, .. } => Some(*callee),
        _ => None,
    }
}
