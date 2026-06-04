use super::fn_types::{
    CallEdgePlan, CallEdgeTarget, CallableCapability, FnEffects, IncomingParamCallableCapabilities, ReturnCapabilities,
    ReturnDemand, SpecKey, SpecPlan, WALK_CALLS, fixed_point_input_tys_for_arity, forwarded_return_contract_for_target,
    padded_direct_input_tys, return_contract_for_target, spec_key_for_fn, spec_key_for_fn_id,
};
use super::prim::type_prim;
use super::reachable::cont_key_from_slot0;
use super::return_context::{continuation_return_demand, direct_call_return_plan, tail_call_return_plan};
use super::type_fn::callable_capability_for_ty;
use super::worklist::{
    ActivationReturnFacts, ResultSlot0, closure_call_result_knowledge, direct_call_result_knowledge,
};
use crate::callsite_walk::{BlockCallsite, CallsiteKind, ContSource, block_callsites};
use crate::frontend::protocols::impl_target_type;
use crate::fz_ir::{
    BlockId, CallsiteId, CallsiteIdent, Cont, EmitSlot, FnId, FnIr, Module, Prim, Stmt, Term, Var,
    receive_outcome_spec_key,
};
use crate::modules::identity::ExportKey;
use crate::specs::unique_matching_params;
use crate::types::{ClosureTypes, KeySlot, Ty, Types, key_slots_from_tys};
use std::collections::{HashMap, HashSet};
use std::mem::take;

/// Output of one discovery walk. The driver folds this into worklist state.
#[derive(Default)]
pub(crate) struct WalkResult {
    /// Per-callsite capability selected for this spec. Populated for `Direct`,
    /// `ClosureCall`, `Cont`, and `CallableBoundary` slots.
    pub(crate) call_edges: HashMap<CallsiteId, CallEdgePlan>,
    /// Target specs whose incoming callable-capability facts changed while
    /// walking this caller. Their cached `SpecPlan`s depend on those facts, so
    /// the driver must revisit them.
    pub(crate) capability_updates: Vec<SpecKey>,
    /// Executable closure-entry obligations induced by surviving
    /// `MakeClosure` statements.
    pub(crate) callable_entry_targets: HashSet<SpecKey>,
}

impl WalkResult {
    fn callsite_id(caller: &SpecKey, ident: &CallsiteIdent, slot: EmitSlot) -> CallsiteId {
        CallsiteId::new(caller.fn_id, ident, slot)
    }

    fn record_dispatch(
        &mut self,
        caller: &SpecKey,
        ident: &CallsiteIdent,
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
        ident: &CallsiteIdent,
        slot: EmitSlot,
        target: ExportKey,
        input: Vec<KeySlot>,
        demand: ReturnDemand,
    ) -> CallsiteId {
        let cid = Self::callsite_id(caller, ident, slot);
        self.call_edges.insert(
            cid.clone(),
            CallEdgePlan {
                target: CallEdgeTarget::External { target, input, demand },
                return_contract: None,
            },
        );
        cid
    }

    fn record_return_contract(&mut self, callsite: &CallsiteId, target: SpecKey) {
        let edge = self
            .call_edges
            .get_mut(callsite)
            .expect("return contracts require an existing call edge");
        edge.return_contract = Some(return_contract_for_target(target));
    }

    fn record_forwarded_return_contract(&mut self, callsite: &CallsiteId, target: SpecKey) {
        let edge = self
            .call_edges
            .get_mut(callsite)
            .expect("return contracts require an existing call edge");
        edge.return_contract = Some(forwarded_return_contract_for_target(target));
    }
}

fn merge_incoming_param_callable_capabilities(
    incoming_param_callable_capabilities: &mut IncomingParamCallableCapabilities,
    key: &SpecKey,
    incoming: Vec<Option<CallableCapability>>,
) -> bool {
    // Incoming-param callable facts derive from the callsite args, not the
    // return-delivery shape, so they are keyed by the body identity: demand
    // siblings share one bucket.
    let body_key = key.body_key();
    match incoming_param_callable_capabilities.get(&body_key) {
        None => {
            incoming_param_callable_capabilities.insert(body_key, incoming);
            true
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
            if *prev == merged {
                return false;
            }
            incoming_param_callable_capabilities.insert(body_key, merged);
            true
        }
    }
}

struct ContinuationSlot0 {
    ty: Ty,
    capability: Option<CallableCapability>,
}

enum ProtocolDispatch {
    Local(SpecKey, usize),
    External {
        target: ExportKey,
        input: Vec<KeySlot>,
        demand: ReturnDemand,
    },
}

/// Discovery walk for one spec. Walks the spec's body and records selected
/// executable call edges, return reads, and recursive fixed-point observations.
///
/// Local spec discovery is derived later from those selected call edges rather
/// than from a parallel emit/provenance graph.
/// `recursive_fns`: calls into recursive functions are normalized
/// immediately with `widen_for_recursive_spec_key`, including the first
/// external entry into the recursive component. The dispatch fact and
/// emitted spec key both use that normalized key, so codegen cannot
/// resolve a different narrow spec from the one the worklist typed.
/// Cont keys are not normalized: they model dataflow from a concrete
/// producer, not a recursive function-entry fixed point.
#[allow(clippy::too_many_arguments)]
pub(super) fn walk_spec_for_discovery<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    f: &FnIr,
    caller_ft: &SpecPlan,
    m: &Module,
    fn_effects: &FnEffects,
    return_capabilities: &ReturnCapabilities,
    activation_returns: &ActivationReturnFacts,
    recursive_fns: &HashSet<FnId>,
    caller_spec_key: &SpecKey,
    incoming_param_callable_capabilities: &mut IncomingParamCallableCapabilities,
    out: &mut WalkResult,
) {
    WALK_CALLS.with(|c| c.set(c.get() + 1));
    let any_ty = t.any();
    DiscoveryWalk {
        t,
        caller_ft,
        m,
        fn_effects,
        return_capabilities,
        activation_returns,
        recursive_fns,
        caller_spec_key,
        incoming_param_callable_capabilities,
        out,
        any_ty,
        reachable_used_vars: collect_reachable_used_vars(f, &caller_ft.reachable_blocks),
    }
    .walk_fn(f);
}

fn collect_reachable_used_vars(f: &FnIr, reachable_blocks: &HashSet<BlockId>) -> HashSet<Var> {
    let mut used = HashSet::new();
    for block in &f.blocks {
        if !reachable_blocks.contains(&block.id) {
            continue;
        }
        for stmt in &block.stmts {
            let Stmt::Let(_, prim) = stmt;
            collect_prim_vars(prim, &mut used);
        }
        collect_term_vars(&block.terminator, &mut used);
    }
    used
}

fn collect_prim_vars(prim: &Prim, used: &mut HashSet<Var>) {
    use crate::fz_ir::BitSizeIr;

    match prim {
        Prim::Const(_) | Prim::MakeFnRef(_, _) => {}
        Prim::BinOp(_, a, b) => {
            used.insert(*a);
            used.insert(*b);
        }
        Prim::UnOp(_, a)
        | Prim::ListHead(a)
        | Prim::ListTail(a)
        | Prim::IsEmptyList(a)
        | Prim::IsListCons(a)
        | Prim::TupleField(a, _)
        | Prim::StructField(a, _)
        | Prim::IsMatcherMapMiss(a)
        | Prim::BitReaderInit(a)
        | Prim::BitReaderDone(a)
        | Prim::TypeTest(a, _) => {
            used.insert(*a);
        }
        Prim::Extern(_, _, args) => {
            for arg in args {
                used.insert(arg.var);
            }
        }
        Prim::MakeTuple(args) | Prim::MakeList(args, None) => {
            used.extend(args.iter().copied());
        }
        Prim::MakeStruct { fields, .. } => {
            for (_, value) in fields {
                used.insert(*value);
            }
        }
        Prim::DestTupleBegin { .. } | Prim::DestListBegin { .. } => {}
        Prim::DestTupleSet { dest, value, .. } => {
            used.insert(*dest);
            used.insert(*value);
        }
        Prim::DestFreeze { dest, .. } => {
            used.insert(*dest);
        }
        Prim::DestListCons { head, tail, .. } => {
            used.insert(*head);
            if let Some(tail) = tail {
                used.insert(*tail);
            }
        }
        Prim::DestListFreeze { list, .. } => {
            used.insert(*list);
        }
        Prim::MakeList(elements, Some(tail)) => {
            used.extend(elements.iter().copied());
            used.insert(*tail);
        }
        Prim::MakeClosure(_, _, captures) => {
            used.extend(captures.iter().copied());
        }
        Prim::MakeMap(entries) => {
            for (key, value) in entries {
                used.insert(*key);
                used.insert(*value);
            }
        }
        Prim::MapUpdate(base, entries) => {
            used.insert(*base);
            for (key, value) in entries {
                used.insert(*key);
                used.insert(*value);
            }
        }
        Prim::DestMapBegin { base, .. } => {
            if let Some(base) = base {
                used.insert(*base);
            }
        }
        Prim::DestMapPut { map, key, value, .. } => {
            used.insert(*map);
            used.insert(*key);
            used.insert(*value);
        }
        Prim::DestMapFreeze { map, .. } => {
            used.insert(*map);
        }
        Prim::MapGet(map, key) | Prim::MatcherMapGet(map, key) => {
            used.insert(*map);
            used.insert(*key);
        }
        Prim::MakeBitstring(fields) => {
            for field in fields {
                used.insert(field.value);
                if let Some(BitSizeIr::Var(size)) = &field.size {
                    used.insert(*size);
                }
            }
        }
        Prim::ConstBitstring(_, _) => {}
        Prim::BitReadField { reader, size, .. } => {
            used.insert(*reader);
            if let Some(BitSizeIr::Var(size)) = size {
                used.insert(*size);
            }
        }
        Prim::Brand(value, _) => {
            used.insert(*value);
        }
    }
}

fn collect_term_vars(term: &Term, used: &mut HashSet<Var>) {
    match term {
        Term::Goto(_, args) | Term::TailCall { args, .. } => {
            used.extend(args.iter().copied());
        }
        Term::If { cond, .. } => {
            used.insert(*cond);
        }
        Term::Call { args, continuation, .. } => {
            used.extend(args.iter().copied());
            used.extend(continuation.captured.iter().copied());
        }
        Term::CallClosure {
            closure,
            args,
            continuation,
            ..
        } => {
            used.insert(*closure);
            used.extend(args.iter().copied());
            used.extend(continuation.captured.iter().copied());
        }
        Term::TailCallClosure { closure, args, .. } => {
            used.insert(*closure);
            used.extend(args.iter().copied());
        }
        Term::Return(value) | Term::Halt(value) => {
            used.insert(*value);
        }
        Term::ReceiveMatched {
            pinned,
            captures,
            after,
            ..
        } => {
            for (_, value) in pinned {
                used.insert(*value);
            }
            used.extend(captures.iter().copied());
            if let Some(after) = after {
                used.insert(after.timeout);
            }
        }
    }
}

struct DiscoveryWalk<'a, T>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    t: &'a mut T,
    caller_ft: &'a SpecPlan,
    m: &'a Module,
    fn_effects: &'a FnEffects,
    return_capabilities: &'a ReturnCapabilities,
    activation_returns: &'a ActivationReturnFacts,
    recursive_fns: &'a HashSet<FnId>,
    caller_spec_key: &'a SpecKey,
    incoming_param_callable_capabilities: &'a mut IncomingParamCallableCapabilities,
    out: &'a mut WalkResult,
    any_ty: Ty,
    reachable_used_vars: HashSet<Var>,
}

impl<T> DiscoveryWalk<'_, T>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    fn walk_fn(&mut self, f: &FnIr) {
        for b in &f.blocks {
            if !self.caller_ft.reachable_blocks.contains(&b.id) {
                continue;
            }
            let mut env: HashMap<Var, Ty> = self.caller_ft.block_envs.get(&b.id).cloned().unwrap_or_default();
            self.walk_statements(b.id, &b.stmts, &mut env);
            self.walk_terminator(&b.terminator, &env);
        }
    }

    fn walk_statements(&mut self, _block_id: BlockId, stmts: &[Stmt], env: &mut HashMap<Var, Ty>) {
        for stmt in stmts {
            let Stmt::Let(v, prim) = stmt;
            let pt_ty = type_prim(self.t, prim, env, self.m, &HashSet::new());
            env.insert(*v, pt_ty);
            if self.reachable_used_vars.contains(v) {
                match stmt {
                    Stmt::Let(_, Prim::MakeFnRef(_, fn_id)) => self.record_make_closure_target(*fn_id, &[], env),
                    Stmt::Let(_, Prim::MakeClosure(_, fn_id, captured)) => {
                        self.record_make_closure_target(*fn_id, captured, env);
                    }
                    _ => {}
                }
            }
            if let Stmt::Let(_, Prim::Extern(ident, _, args)) = stmt {
                let arg_vars = args.iter().map(|arg| arg.var).collect::<Vec<_>>();
                self.record_external_callable_targets(&arg_vars, env, ident);
            }
        }
    }

    fn walk_terminator(&mut self, term: &Term, env: &HashMap<Var, Ty>) {
        let Some(term_ident) = term.ident().cloned() else {
            return;
        };
        let known_closure_targets: HashMap<Var, FnId> = self
            .caller_ft
            .callable_capabilities
            .iter()
            .filter_map(|(var, cap)| match cap {
                CallableCapability::KnownFn(fid) => Some((*var, *fid)),
                CallableCapability::KnownClosure { fn_id, .. } => Some((*var, *fn_id)),
                CallableCapability::OpaqueCallable => None,
            })
            .collect();
        for BlockCallsite { slot, kind } in block_callsites(self.t, term, env, &known_closure_targets) {
            self.record_callsite(term, &term_ident, env, slot, kind);
        }
        self.seed_receive_matched_outcomes(term);
    }

    fn record_callsite(
        &mut self,
        term: &Term,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, Ty>,
        slot: EmitSlot,
        kind: CallsiteKind,
    ) {
        match kind {
            CallsiteKind::Direct { callee, args } => {
                self.record_direct_call(term, term_ident, env, slot, callee, args);
            }
            CallsiteKind::CallClosureKnown { closure, target, args } => {
                self.record_known_closure_call(term, term_ident, env, slot, closure, target, args);
            }
            CallsiteKind::ClosureLit { fn_id, captures, args } => {
                self.record_closure_literal_call(term, term_ident, env, slot, fn_id, captures, args);
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
        env: &HashMap<Var, Ty>,
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
                if let ProtocolDispatch::External { target, input, demand } = dispatch {
                    self.out
                        .record_external_dispatch(self.caller_spec_key, term_ident, slot, target, input, demand);
                }
                return;
            };
            let cid = WalkResult::callsite_id(self.caller_spec_key, term_ident, slot);
            if let Term::Call { continuation, .. } = term {
                let target_fn = entry_key.fn_id;
                let demand = direct_call_return_plan(
                    self.t,
                    self.m,
                    self.fn_effects,
                    self.return_capabilities,
                    self.caller_spec_key,
                    env,
                    target_fn,
                    args,
                    continuation,
                );
                entry_key.demand = demand;
                entry_key = self.activation_returns.canonical_public_key(self.t, entry_key);
                self.out
                    .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
                self.out.record_return_contract(&cid, entry_key.clone());
            } else if matches!(term, Term::TailCall { .. }) {
                let target_fn = entry_key.fn_id;
                let demand = tail_call_return_plan(self.return_capabilities, self.caller_spec_key, target_fn, args);
                entry_key.demand = demand;
                entry_key = self.activation_returns.canonical_public_key(self.t, entry_key);
                self.out
                    .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
                self.out.record_forwarded_return_contract(&cid, entry_key.clone());
            } else {
                self.out
                    .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
            }
            let per_arg = self.callable_capability_args(args, n_params);
            if merge_incoming_param_callable_capabilities(
                self.incoming_param_callable_capabilities,
                &entry_key,
                per_arg,
            ) {
                self.out.capability_updates.push(entry_key.clone());
            }
            return;
        }
        let Some((mut entry_key, n_params)) = self.direct_call_key(callee, args, env) else {
            self.record_external_call(term, term_ident, env, slot, args);
            return;
        };
        let cid = WalkResult::callsite_id(self.caller_spec_key, term_ident, slot);
        if let Term::Call { continuation, .. } = term {
            let demand = direct_call_return_plan(
                self.t,
                self.m,
                self.fn_effects,
                self.return_capabilities,
                self.caller_spec_key,
                env,
                callee,
                args,
                continuation,
            );
            entry_key.demand = demand;
            entry_key = self.activation_returns.canonical_public_key(self.t, entry_key);
            self.out
                .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
            self.out.record_return_contract(&cid, entry_key.clone());
        } else if matches!(term, Term::TailCall { .. }) {
            let demand = tail_call_return_plan(self.return_capabilities, self.caller_spec_key, callee, args);
            entry_key.demand = demand;
            entry_key = self.activation_returns.canonical_public_key(self.t, entry_key);
            self.out
                .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
            self.out.record_forwarded_return_contract(&cid, entry_key.clone());
        } else {
            self.out
                .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
        }
        let per_arg = self.callable_capability_args(args, n_params);
        if merge_incoming_param_callable_capabilities(self.incoming_param_callable_capabilities, &entry_key, per_arg) {
            self.out.capability_updates.push(entry_key.clone());
        }
    }

    fn record_external_call(
        &mut self,
        term: &Term,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, Ty>,
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
        self.out
            .record_external_dispatch(self.caller_spec_key, term_ident, slot, target, input, demand.clone());
        self.record_external_callable_targets(args, env, term_ident);
    }

    fn record_external_callable_targets(&mut self, args: &[Var], env: &HashMap<Var, Ty>, term_ident: &CallsiteIdent) {
        for arg in args {
            for key in self.callable_boundary_keys(*arg, env) {
                self.out.record_dispatch(
                    self.caller_spec_key,
                    term_ident,
                    EmitSlot::CallableBoundary,
                    key.clone(),
                );
            }
        }
    }

    fn record_make_closure_target(&mut self, fn_id: FnId, captured: &[Var], env: &HashMap<Var, Ty>) {
        let Some(target_fn) = self.m.fn_idx.get(&fn_id).map(|j| &self.m.fns[*j]) else {
            return;
        };
        let n_params = target_fn.block(target_fn.entry).params.len();
        let mut input_tys = captured
            .iter()
            .map(|var| env.get(var).cloned().unwrap_or_else(|| self.any_ty.clone()))
            .collect::<Vec<_>>();
        input_tys = padded_direct_input_tys(self.t, input_tys, n_params);
        let target_key = self
            .activation_returns
            .canonical_public_key(self.t, spec_key_for_fn_id(self.m, fn_id, input_tys));
        self.out.callable_entry_targets.insert(target_key.clone());
        let mut per_param = captured
            .iter()
            .map(|var| self.caller_ft.callable_capabilities.get(var).cloned())
            .collect::<Vec<_>>();
        pad_and_truncate(&mut per_param, n_params, &None);
        if merge_incoming_param_callable_capabilities(self.incoming_param_callable_capabilities, &target_key, per_param)
        {
            self.out.capability_updates.push(target_key);
        }
    }

    fn callable_boundary_keys(&mut self, arg: Var, env: &HashMap<Var, Ty>) -> Vec<SpecKey> {
        let Some((fn_id, captures)) = (match self.caller_ft.callable_capabilities.get(&arg) {
            Some(CallableCapability::KnownFn(fn_id)) => Some((*fn_id, Vec::new())),
            Some(CallableCapability::KnownClosure { fn_id, captures, .. }) => Some((*fn_id, captures.clone())),
            Some(CallableCapability::OpaqueCallable) | None => None,
        }) else {
            return Vec::new();
        };
        let Some(value_ty) = env.get(&arg) else {
            return Vec::new();
        };
        let Some(clauses) = self.t.callable_clauses(value_ty) else {
            return Vec::new();
        };
        let Some(target_fn) = self.m.fn_idx.get(&fn_id).map(|j| &self.m.fns[*j]) else {
            return Vec::new();
        };
        let n_params = target_fn.block(target_fn.entry).params.len();
        let mut keys = Vec::new();
        for clause in clauses {
            let mut input_tys = captures.clone();
            input_tys.extend(clause.args);
            input_tys = padded_direct_input_tys(self.t, input_tys, n_params);
            if self.has_bottom_arg(&input_tys) {
                continue;
            }
            let (observed, input_tys) = fixed_point_input_tys_for_arity(
                self.t,
                self.m,
                self.recursive_fns,
                self.caller_spec_key.fn_id,
                fn_id,
                input_tys,
                n_params,
            );
            let _ = observed;
            keys.push(
                self.activation_returns
                    .canonical_public_key(self.t, spec_key_for_fn_id(self.m, fn_id, input_tys)),
            );
        }
        keys
    }

    fn record_known_closure_call(
        &mut self,
        term: &Term,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, Ty>,
        slot: EmitSlot,
        closure: Var,
        target: FnId,
        args: &[Var],
    ) {
        let Some((mut target_key, per_param)) = (match self.caller_ft.callable_capabilities.get(&closure) {
            Some(CallableCapability::KnownClosure {
                captures,
                capture_capabilities,
                ..
            }) => {
                let Some((key, n_params)) = self.closure_lit_key(target, captures.clone(), args, env) else {
                    return;
                };
                let mut per_param = capture_capabilities.clone();
                per_param.extend(
                    args.iter()
                        .map(|arg| self.caller_ft.callable_capabilities.get(arg).cloned()),
                );
                pad_and_truncate(&mut per_param, n_params, &None);
                Some((key, per_param))
            }
            Some(CallableCapability::KnownFn(_)) => self
                .direct_call_key(target, args, env)
                .map(|(key, n_params)| (key, self.callable_capability_args(args, n_params))),
            Some(CallableCapability::OpaqueCallable) | None => None,
        }) else {
            return;
        };
        self.inherit_tail_closure_demand(term, &mut target_key);
        target_key = self.activation_returns.canonical_public_key(self.t, target_key);
        self.out
            .record_dispatch(self.caller_spec_key, term_ident, slot, target_key.clone());
        if merge_incoming_param_callable_capabilities(self.incoming_param_callable_capabilities, &target_key, per_param)
        {
            self.out.capability_updates.push(target_key.clone());
        }
    }

    fn record_closure_literal_call(
        &mut self,
        term: &Term,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, Ty>,
        slot: EmitSlot,
        fn_id: FnId,
        captures: Vec<Ty>,
        args: &[Var],
    ) {
        let capture_capabilities = captures
            .iter()
            .map(|capture| callable_capability_for_ty(self.t, capture))
            .collect::<Vec<_>>();
        let Some((mut target_key, n_params)) = self.closure_lit_key(fn_id, captures, args, env) else {
            return;
        };
        self.inherit_tail_closure_demand(term, &mut target_key);
        target_key = self.activation_returns.canonical_public_key(self.t, target_key);
        self.out
            .record_dispatch(self.caller_spec_key, term_ident, slot, target_key.clone());
        let mut per_param = capture_capabilities;
        per_param.extend(
            args.iter()
                .map(|arg| self.caller_ft.callable_capabilities.get(arg).cloned()),
        );
        pad_and_truncate(&mut per_param, n_params, &None);
        if merge_incoming_param_callable_capabilities(self.incoming_param_callable_capabilities, &target_key, per_param)
        {
            self.out.capability_updates.push(target_key.clone());
        }
    }

    fn record_continuation(
        &mut self,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, Ty>,
        slot: EmitSlot,
        cont: Cont,
        source: ContSource,
    ) {
        let Some(slot0) = self.continuation_slot0(term_ident, env, &source) else {
            return;
        };
        let Some(&j) = self.m.fn_idx.get(&cont.fn_id) else {
            return;
        };
        let cont_fn = &self.m.fns[j];
        let n_params = cont_fn.block(cont_fn.entry).params.len();
        let mut key = cont_key_from_slot0(&self.any_ty, n_params, slot0.ty, &cont.captured, env);
        if self.has_bottom_arg(&key) {
            return;
        }
        let per_param_capabilities = self.continuation_callable_capabilities(&cont, n_params, slot0.capability);
        let demand = continuation_return_demand(self.m, self.caller_spec_key, self.return_capabilities, &cont, &source);
        let mut entry_key = spec_key_for_fn(cont_fn, take(&mut key));
        entry_key.demand = demand.clone();
        entry_key = self.activation_returns.canonical_public_key(self.t, entry_key);
        if merge_incoming_param_callable_capabilities(
            self.incoming_param_callable_capabilities,
            &entry_key,
            per_param_capabilities,
        ) {
            self.out.capability_updates.push(entry_key.clone());
        }
        self.out
            .record_dispatch(self.caller_spec_key, term_ident, slot, entry_key.clone());
    }

    fn continuation_slot0(
        &mut self,
        term_ident: &CallsiteIdent,
        env: &HashMap<Var, Ty>,
        source: &ContSource,
    ) -> Option<ContinuationSlot0> {
        match *source {
            ContSource::Call { callee, args } => {
                let arg_tys = self.arg_tys(args, env);
                let direct_cid = WalkResult::callsite_id(self.caller_spec_key, term_ident, EmitSlot::Direct);
                let selected_edge = self.out.call_edges.get(&direct_cid);
                let knowledge = direct_call_result_knowledge(
                    self.t,
                    self.m,
                    self.recursive_fns,
                    self.caller_spec_key,
                    term_ident,
                    callee,
                    &arg_tys,
                    self.activation_returns,
                    selected_edge,
                );
                Some(match knowledge.slot0 {
                    ResultSlot0::Known(ty) => ContinuationSlot0 {
                        capability: callable_capability_for_ty(self.t, &ty),
                        ty,
                    },
                    // Planner-visible continuations must stay coherent even when
                    // inference cannot yet prove a narrower slot-0 type.
                    ResultSlot0::Pending => ContinuationSlot0 {
                        ty: self.any_ty.clone(),
                        capability: None,
                    },
                })
            }
            ContSource::CallClosure { closure, args } => self.closure_return_slot0(term_ident, closure, args, env),
        }
    }

    fn external_call_input(
        &mut self,
        callee: Option<FnId>,
        args: &[Var],
        env: &HashMap<Var, Ty>,
        arity: usize,
    ) -> Vec<KeySlot> {
        let arg_tys = self.arg_tys(args, env);
        if let Some(callee) = callee
            && let Some(spec_set) = self.m.declared_specs.get(&callee)
            && let Some(params) = unique_matching_params(self.t, spec_set, &arg_tys)
            && params.len() == arity
        {
            return key_slots_from_tys(params);
        }
        key_slots_from_tys(padded_direct_input_tys(self.t, arg_tys, arity))
    }

    fn external_target(&self, term_ident: &CallsiteIdent, slot: EmitSlot) -> Option<ExportKey> {
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
        env: &HashMap<Var, Ty>,
    ) -> Option<ContinuationSlot0> {
        let arg_tys = self.arg_tys(args, env);
        let selected_target = self
            .out
            .call_edges
            .get(&WalkResult::callsite_id(
                self.caller_spec_key,
                term_ident,
                EmitSlot::ClosureCall,
            ))
            .and_then(CallEdgePlan::local_target);
        let knowledge = closure_call_result_knowledge(
            self.t,
            self.m,
            self.recursive_fns,
            self.caller_spec_key,
            term_ident,
            &arg_tys,
            self.activation_returns,
            selected_target,
            env.get(&closure),
        );
        Some(match knowledge.slot0 {
            ResultSlot0::Known(ty) => ContinuationSlot0 {
                capability: callable_capability_for_ty(self.t, &ty),
                ty,
            },
            ResultSlot0::Pending => ContinuationSlot0 {
                ty: self.any_ty.clone(),
                capability: None,
            },
        })
    }

    fn seed_receive_matched_outcomes(&mut self, term: &Term) {
        let Term::ReceiveMatched { clauses, after, .. } = term else {
            return;
        };
        for c in clauses {
            self.emit_receive_outcome(c.body, c.ident.clone());
            if let Some(guard) = c.guard {
                self.emit_receive_outcome(guard, c.ident.clone());
            }
        }
        if let Some(a) = after {
            self.emit_receive_outcome(a.body, a.ident.clone());
        }
    }

    fn emit_receive_outcome(&mut self, fid: FnId, ident: CallsiteIdent) {
        let Some(&j) = self.m.fn_idx.get(&fid) else {
            return;
        };
        let body = &self.m.fns[j];
        let np = body.block(body.entry).params.len();
        let key = receive_outcome_spec_key(&self.any_ty, np);
        self.out
            .record_dispatch(self.caller_spec_key, &ident, EmitSlot::Cont, spec_key_for_fn(body, key));
    }

    fn direct_call_key(&mut self, callee: FnId, args: &[Var], env: &HashMap<Var, Ty>) -> Option<(SpecKey, usize)> {
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
            self.caller_spec_key.fn_id,
            callee,
            dispatch_key,
            n_params,
        );
        let _ = observed;
        let key = self
            .activation_returns
            .canonical_public_key(self.t, spec_key_for_fn_id(self.m, callee, input_tys));
        Some((key, n_params))
    }

    fn protocol_dispatch_key(
        &mut self,
        callee: FnId,
        args: &[Var],
        env: &HashMap<Var, Ty>,
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
                let target_ty = impl_target_type(self.t, &fact.target);
                self.t.is_subtype(&receiver_ty, &target_ty)
            })
            .filter_map(|fact| fact.callbacks.get(&(target.callback.clone(), target.arity)).cloned())
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
        let input = key_slots_from_tys(padded_direct_input_tys(self.t, self.arg_tys(args, env), export.arity));
        Some(ProtocolDispatch::External {
            target: export,
            input,
            demand: ReturnDemand::value(),
        })
    }

    fn closure_lit_key(
        &mut self,
        fn_id: FnId,
        captures: Vec<Ty>,
        args: &[Var],
        env: &HashMap<Var, Ty>,
    ) -> Option<(SpecKey, usize)> {
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
            self.caller_spec_key.fn_id,
            fn_id,
            dispatch_key,
            n_params,
        );
        let _ = observed;
        Some((
            self.activation_returns
                .canonical_public_key(self.t, spec_key_for_fn_id(self.m, fn_id, input_tys)),
            n_params,
        ))
    }

    fn callable_capability_args(&self, args: &[Var], n_params: usize) -> Vec<Option<CallableCapability>> {
        let mut per_arg: Vec<Option<CallableCapability>> = args
            .iter()
            .map(|av| self.caller_ft.callable_capabilities.get(av).cloned())
            .collect();
        pad_and_truncate(&mut per_arg, n_params, &None);
        per_arg
    }

    fn continuation_callable_capabilities(
        &self,
        cont: &Cont,
        n_params: usize,
        slot0_capability: Option<CallableCapability>,
    ) -> Vec<Option<CallableCapability>> {
        let mut per_param = vec![None; n_params];
        if let Some(slot0) = per_param.get_mut(0) {
            *slot0 = slot0_capability;
        }
        for (k, cvv) in cont.captured.iter().enumerate() {
            if let Some(p) = per_param.get_mut(k + 1) {
                *p = self.caller_ft.callable_capabilities.get(cvv).cloned();
            }
        }
        per_param
    }

    fn arg_tys(&self, args: &[Var], env: &HashMap<Var, Ty>) -> Vec<Ty> {
        args.iter()
            .map(|av| env.get(av).cloned().unwrap_or_else(|| self.any_ty.clone()))
            .collect()
    }

    fn inherit_tail_closure_demand(&self, term: &Term, key: &mut SpecKey) {
        if matches!(term, Term::TailCallClosure { .. }) {
            key.demand = self.caller_spec_key.demand.clone();
        }
    }

    fn has_bottom_arg(&mut self, key: &[Ty]) -> bool {
        let none_ty = self.t.none();
        key.iter().any(|ty| self.t.is_equivalent(ty, &none_ty))
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
