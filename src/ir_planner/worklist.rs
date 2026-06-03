use super::callgraph::{build_recursion_graph, entry_seeds};
use super::closures::literal_closure_return_keys;
use super::diagnostics::{compute_dead_branches, module_plan_stats};
use super::effects::{prim_effects, term_effects};
use super::fn_types::{
    BodyKey, CallEdgePlan, CallEdgeTarget, CallableCapability, EffectSummary, FnEffects,
    IncomingParamCallableCapabilities, ModulePlan, ReturnDemand, SpecKey, SpecKeySet, SpecPlan, SpecReachabilityRole,
    TYPE_FN_CALLS, VISIT_HARD_BOUND, WALK_CALLS, WORKLIST_POPS, body_key_for_fn_id, build_any_key_index,
    fixed_point_spec_key_for_arity, key_precedence_order, spec_key_for_fn_id, spec_key_input_tys,
};
use super::scc::tarjan_scc;
use super::type_fn::type_fn;
use super::walk::{WalkResult, walk_spec_for_discovery};
use crate::concrete_types::ty_display;
use crate::fz_ir::{BlockId, CallsiteId, CallsiteIdent, DeadBranch, EmitSlot, FnId, FnIr, Module, Prim, Stmt, Term};
use crate::ir_planner::inventory::{body_callsite_inventory, plan_call_edge_inventory};
use crate::specs::{
    CallbackReturnDemand, CallbackReturnFact, CallbackReturnQuery, SpecApplicationOutcome, apply_spec_set,
    resolve_closure_return,
};
use crate::telemetry::Telemetry;
use crate::telemetry::value::opaque;
use crate::type_infer::{
    TypeInferActivationEdgeFact, TypeInferActivationFact, TypeInferActivationId, TypeInferDeadArmFact,
    TypeInferReturnState, TypeInferStatus, infer_from_entry,
};
use crate::types::{ClosureTarget, ClosureTypes, RenderTypes, Ty, Types, key_slots_observed};
use std::collections::{HashMap, HashSet, VecDeque};

pub(crate) enum ResultSlot0 {
    Known(Ty),
    Pending,
}

pub(crate) struct CallResultKnowledge {
    pub(crate) slot0: ResultSlot0,
}

#[derive(Clone, Debug)]
struct DeclaredReturnFact {
    ty: Option<Ty>,
}

pub(super) struct ActivationReturnFacts {
    bucket_returns: HashMap<BodyKey, TypeInferReturnState>,
    witness_returns: HashMap<TypeInferActivationId, TypeInferReturnState>,
    witness_public_keys: HashMap<TypeInferActivationId, BodyKey>,
    witness_ids_by_public_key: HashMap<BodyKey, Vec<TypeInferActivationId>>,
    observed_edges_by_witness: HashMap<TypeInferActivationId, HashSet<ObservedActivationEdge>>,
    observed_dead_arms_by_witness: HashMap<TypeInferActivationId, HashSet<ObservedDeadArm>>,
    callee_witnesses_by_caller_and_callsite: HashMap<(BodyKey, CallsiteId), HashSet<TypeInferActivationId>>,
    unsettled_buckets: HashMap<FnId, Vec<BodyKey>>,
    raw_fact_count: usize,
    complete_entry_count: usize,
    unresolved_entry_count: usize,
    invalid_entry_count: usize,
}

#[derive(Clone, Copy, Default)]
struct ActivationReturnTelemetry {
    fact_count: usize,
    key_count: usize,
    complete_entry_count: usize,
    unresolved_entry_count: usize,
    invalid_entry_count: usize,
    known_count: usize,
    unresolved_count: usize,
    no_return_count: usize,
    projected_count: usize,
    projection_gap_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ActivationProjectionKind {
    Exact,
    Union,
    DeclaredCallableEntry,
    UnsettledOverlap,
    Uncovered,
}

impl ActivationProjectionKind {
    fn as_str(&self) -> &'static str {
        match self {
            Self::Exact => "exact",
            Self::Union => "union",
            Self::DeclaredCallableEntry => "declared_callable_entry",
            Self::UnsettledOverlap => "unsettled_overlap",
            Self::Uncovered => "uncovered",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ActivationProjectionFact {
    spec_key: BodyKey,
    kind: ActivationProjectionKind,
    projected_state: Option<TypeInferReturnState>,
    covered_activations: Vec<CoveredActivation>,
    projected_call_edges: Vec<ObservedActivationEdge>,
    projected_dead_arms: Vec<ObservedDeadArm>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CoveredActivation {
    activation_id: TypeInferActivationId,
    public_key: BodyKey,
    state: TypeInferReturnState,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ObservedActivationEdge {
    callee: BodyKey,
    slot: EmitSlot,
    span_start: u64,
    span_end: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ObservedDeadArm {
    fn_id: FnId,
    block_id: BlockId,
    branch: DeadBranch,
}

fn render_type_infer_return_state<T: Types<Ty = Ty> + RenderTypes>(
    t: &mut T,
    state: Option<&TypeInferReturnState>,
) -> String {
    match state {
        Some(TypeInferReturnState::Known(ty)) => format!("known({})", t.display_for_diag(ty)),
        Some(TypeInferReturnState::Pending) => "pending".to_string(),
        Some(TypeInferReturnState::Unknown) => "unknown".to_string(),
        Some(TypeInferReturnState::NoReturn) => "no_return".to_string(),
        None => "<none>".to_string(),
    }
}

fn emit_slot_label(slot: EmitSlot) -> &'static str {
    match slot {
        EmitSlot::Direct => "direct",
        EmitSlot::Cont => "cont",
        EmitSlot::ClosureCall => "closure_call",
        EmitSlot::CallableBoundary => "callable_boundary",
    }
}

fn dead_branch_label(branch: DeadBranch) -> &'static str {
    match branch {
        DeadBranch::Then => "then",
        DeadBranch::Else => "else",
    }
}

fn activation_edge_inventory_entry(edge: &ObservedActivationEdge) -> String {
    format!(
        "{}@{}..{}->{:?}",
        emit_slot_label(edge.slot),
        edge.span_start,
        edge.span_end,
        edge.callee
    )
}

fn dead_arm_inventory_entry(dead_arm: &ObservedDeadArm) -> String {
    format!(
        "fn{}#b{}:{}",
        dead_arm.fn_id.0,
        dead_arm.block_id.0,
        dead_branch_label(dead_arm.branch)
    )
}

impl ActivationReturnFacts {
    fn empty() -> Self {
        Self {
            bucket_returns: HashMap::new(),
            witness_returns: HashMap::new(),
            witness_public_keys: HashMap::new(),
            witness_ids_by_public_key: HashMap::new(),
            observed_edges_by_witness: HashMap::new(),
            observed_dead_arms_by_witness: HashMap::new(),
            callee_witnesses_by_caller_and_callsite: HashMap::new(),
            unsettled_buckets: HashMap::new(),
            raw_fact_count: 0,
            complete_entry_count: 0,
            unresolved_entry_count: 0,
            invalid_entry_count: 0,
        }
    }

    fn from_entry_seeds<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
        t: &mut T,
        module: &Module,
        tel: &dyn Telemetry,
    ) -> Self {
        let seeds = entry_seeds(t, module);
        let mut facts = Self::empty();
        for (entry, input_tys) in seeds {
            let outcome = infer_from_entry(t, module, entry, &input_tys, tel);
            match outcome.status {
                TypeInferStatus::Complete => facts.complete_entry_count += 1,
                TypeInferStatus::Unresolved => {
                    facts.unresolved_entry_count += 1;
                }
                TypeInferStatus::Invalid => facts.invalid_entry_count += 1,
            }
            for activation in outcome.activations {
                facts.raw_fact_count += 1;
                facts.record_activation(t, module, activation);
            }
            for edge in &outcome.edges {
                facts.record_observed_edge(t, module, edge);
            }
            for dead_arm in &outcome.dead_arms {
                facts.record_observed_dead_arm(dead_arm);
            }
        }
        facts
    }

    fn record_activation<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        module: &Module,
        activation: TypeInferActivationFact,
    ) {
        let activation_id = activation.activation_id;
        let public_key = public_activation_body_key(t, module, activation.fn_id, activation.input_tys);
        let state = activation.return_state;
        self.witness_returns.insert(activation_id, state.clone());
        self.witness_public_keys.insert(activation_id, public_key.clone());
        self.witness_ids_by_public_key
            .entry(public_key.clone())
            .or_default()
            .push(activation_id);
        self.bucket_returns
            .entry(public_key.clone())
            .and_modify(|existing| {
                *existing = merge_activation_return_state(t, existing, &state);
            })
            .or_insert(state);
        if matches!(
            self.witness_returns.get(&activation_id),
            Some(TypeInferReturnState::Pending | TypeInferReturnState::Unknown)
        ) {
            self.insert_unsettled(public_key);
        }
    }

    fn insert_unsettled(&mut self, key: BodyKey) {
        let keys = self.unsettled_buckets.entry(key.fn_id).or_default();
        if !keys.contains(&key) {
            keys.push(key);
        }
    }

    /// Project an activation return state into the planner's return map shape.
    /// `type_infer` keeps unresolved facts as `Pending`/`Unknown`; `any` is only
    /// introduced here at the planner boundary for still-reachable specs.
    fn projected_return_for_key<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        module: &Module,
        recursive_fns: &HashSet<FnId>,
        callable_entry_specs: &SpecKeySet,
        key: &SpecKey,
    ) -> Ty {
        let state = self
            .return_state_for_key(t, key)
            .or_else(|| {
                callable_entry_specs
                    .contains(key)
                    .then(|| self.declared_callable_entry_return_state(t, module, recursive_fns, key))
                    .flatten()
            })
            .unwrap_or(TypeInferReturnState::Unknown);
        match state {
            TypeInferReturnState::Known(ty) => ty,
            TypeInferReturnState::NoReturn => t.none(),
            TypeInferReturnState::Pending | TypeInferReturnState::Unknown => t.any(),
        }
    }

    fn return_state_for_key<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        key: &SpecKey,
    ) -> Option<TypeInferReturnState> {
        let body_key = key.body_key();
        if let Some(exact) = self.bucket_returns.get(&body_key) {
            return Some(exact.clone());
        }
        if self.request_overlaps_unsettled(t, key) {
            return None;
        }
        let mut joined = None;
        for (candidate, state) in self
            .bucket_returns
            .iter()
            .filter(|(candidate, _)| candidate.fn_id == body_key.fn_id)
        {
            if activation_key_covers_requested(t, candidate, &body_key) {
                joined = Some(match joined {
                    Some(prev) => merge_activation_return_state(t, &prev, state),
                    None => state.clone(),
                });
            }
        }
        joined
    }

    pub(super) fn result_slot0_for_key<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        key: &SpecKey,
    ) -> ResultSlot0 {
        match self.return_state_for_key(t, key) {
            Some(TypeInferReturnState::Known(ty)) => ResultSlot0::Known(ty),
            Some(TypeInferReturnState::NoReturn) => ResultSlot0::Known(t.none()),
            Some(TypeInferReturnState::Pending | TypeInferReturnState::Unknown) | None => ResultSlot0::Pending,
        }
    }

    fn request_overlaps_unsettled<T: Types<Ty = Ty> + ClosureTypes>(&self, t: &mut T, requested: &SpecKey) -> bool {
        let requested = requested.body_key();
        self.unsettled_buckets
            .get(&requested.fn_id)
            .is_some_and(|keys| keys.iter().any(|key| activation_keys_overlap(t, key, &requested)))
    }

    fn project_effective_returns<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        module: &Module,
        recursive_fns: &HashSet<FnId>,
        reachable: &SpecKeySet,
        callable_entry_specs: &SpecKeySet,
        effective_returns: &mut HashMap<BodyKey, Ty>,
    ) {
        for key in reachable {
            let ret = self.projected_return_for_key(t, module, recursive_fns, callable_entry_specs, key);
            effective_returns.insert(key.body_key(), ret);
        }
    }

    fn telemetry<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        module: &Module,
        recursive_fns: &HashSet<FnId>,
        reachable: &SpecKeySet,
        callable_entry_specs: &SpecKeySet,
    ) -> ActivationReturnTelemetry {
        let mut stats = ActivationReturnTelemetry {
            fact_count: self.raw_fact_count,
            key_count: self.bucket_returns.len(),
            complete_entry_count: self.complete_entry_count,
            unresolved_entry_count: self.unresolved_entry_count,
            invalid_entry_count: self.invalid_entry_count,
            projected_count: reachable.len(),
            ..ActivationReturnTelemetry::default()
        };
        for state in self.bucket_returns.values() {
            match state {
                TypeInferReturnState::Known(_) => stats.known_count += 1,
                TypeInferReturnState::Pending | TypeInferReturnState::Unknown => {
                    stats.unresolved_count += 1;
                }
                TypeInferReturnState::NoReturn => stats.no_return_count += 1,
            }
        }
        stats.unresolved_count += self
            .unsettled_buckets
            .values()
            .flatten()
            .filter(|key| !self.bucket_returns.contains_key(*key))
            .count();
        for key in reachable {
            if callable_entry_specs.contains(key) {
                continue;
            }
            if self
                .projection_fact_for_key(t, module, recursive_fns, callable_entry_specs, key.clone())
                .projected_state
                .is_none()
            {
                stats.projection_gap_count += 1;
            }
        }
        stats
    }

    fn projection_gap_keys<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        module: &Module,
        recursive_fns: &HashSet<FnId>,
        reachable: &SpecKeySet,
        callable_entry_specs: &SpecKeySet,
    ) -> Vec<String> {
        let mut gaps = Vec::new();
        for key in reachable {
            if callable_entry_specs.contains(key) {
                continue;
            }
            if self
                .projection_fact_for_key(t, module, recursive_fns, callable_entry_specs, key.clone())
                .projected_state
                .is_none()
            {
                let name = module.fn_by_id(key.fn_id).name.clone();
                gaps.push(format!("{name} {key:?}"));
            }
        }
        gaps.sort();
        gaps
    }

    fn projection_facts<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        module: &Module,
        recursive_fns: &HashSet<FnId>,
        reachable: &SpecKeySet,
        callable_entry_specs: &SpecKeySet,
    ) -> Vec<ActivationProjectionFact> {
        let mut facts: Vec<_> = reachable
            .iter()
            .cloned()
            .map(|spec_key| self.projection_fact_for_key(t, module, recursive_fns, callable_entry_specs, spec_key))
            .collect();
        facts.sort_by(|left, right| format!("{:?}", left.spec_key).cmp(&format!("{:?}", right.spec_key)));
        facts
    }

    fn projection_fact_for_key<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        module: &Module,
        recursive_fns: &HashSet<FnId>,
        callable_entry_specs: &SpecKeySet,
        spec_key: SpecKey,
    ) -> ActivationProjectionFact {
        let body_key = spec_key.body_key();
        let (mut kind, covered_activations) = if self.bucket_returns.contains_key(&body_key) {
            (
                ActivationProjectionKind::Exact,
                self.covered_witnesses_for_public_key(&body_key),
            )
        } else {
            let covering = self.covered_activation_states_for_request(t, &body_key);
            if !covering.is_empty() {
                let kind = if covering.len() == 1 {
                    ActivationProjectionKind::Exact
                } else {
                    ActivationProjectionKind::Union
                };
                (kind, covering)
            } else {
                let unsettled = self.overlapping_unsettled_activation_states(t, &body_key);
                if unsettled.is_empty() {
                    (ActivationProjectionKind::Uncovered, Vec::new())
                } else {
                    (ActivationProjectionKind::UnsettledOverlap, unsettled)
                }
            }
        };
        let mut projected_call_edges = HashSet::new();
        let mut projected_dead_arms: Option<HashSet<ObservedDeadArm>> = None;
        for covered in &covered_activations {
            if let Some(edges) = self.observed_edges_by_witness.get(&covered.activation_id) {
                projected_call_edges.extend(edges.iter().cloned());
            }
            let dead_arms = self
                .observed_dead_arms_by_witness
                .get(&covered.activation_id)
                .cloned()
                .unwrap_or_default();
            match &mut projected_dead_arms {
                Some(existing) => existing.retain(|dead_arm| dead_arms.contains(dead_arm)),
                None => projected_dead_arms = Some(dead_arms),
            };
        }
        let mut projected_call_edges: Vec<_> = projected_call_edges.into_iter().collect();
        projected_call_edges
            .sort_by(|left, right| activation_edge_inventory_entry(left).cmp(&activation_edge_inventory_entry(right)));
        let mut projected_dead_arms: Vec<_> = projected_dead_arms.unwrap_or_default().into_iter().collect();
        projected_dead_arms.sort_by(|left, right| dead_arm_inventory_entry(left).cmp(&dead_arm_inventory_entry(right)));
        let mut projected_state = self.return_state_for_key(t, &spec_key);
        if projected_state.is_none()
            && callable_entry_specs.contains(&spec_key)
            && let Some(declared) = self.declared_callable_entry_return_state(t, module, recursive_fns, &spec_key)
        {
            projected_state = Some(declared);
            if covered_activations.is_empty() {
                kind = ActivationProjectionKind::DeclaredCallableEntry;
            }
        }
        if projected_state.is_none() {
            projected_state = Some(TypeInferReturnState::Unknown);
        }
        ActivationProjectionFact {
            projected_state,
            spec_key: body_key,
            kind,
            covered_activations,
            projected_call_edges,
            projected_dead_arms,
        }
    }

    fn declared_callable_entry_return_state<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        module: &Module,
        recursive_fns: &HashSet<FnId>,
        key: &SpecKey,
    ) -> Option<TypeInferReturnState> {
        let arg_tys = spec_key_input_tys(t, key);
        let owner = &module.fn_by_id(key.fn_id).owner_module;
        declared_call_return_fact(t, module, recursive_fns, key.fn_id, key.fn_id, &arg_tys, self, owner)
            .and_then(|fact| fact.ty)
            .map(TypeInferReturnState::Known)
    }

    fn covered_activation_states_for_request<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        requested: &BodyKey,
    ) -> Vec<CoveredActivation> {
        let mut covered = Vec::new();
        for (candidate, _) in self
            .bucket_returns
            .iter()
            .filter(|(candidate, _)| candidate.fn_id == requested.fn_id)
            .filter(|(candidate, _)| activation_key_covers_requested(t, candidate, requested))
        {
            covered.extend(self.covered_witnesses_for_public_key(candidate));
        }
        covered.sort_by(|left, right| {
            format!("{:?}", left.public_key)
                .cmp(&format!("{:?}", right.public_key))
                .then(left.activation_id.cmp(&right.activation_id))
        });
        covered
    }

    fn overlapping_unsettled_activation_states<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        requested: &BodyKey,
    ) -> Vec<CoveredActivation> {
        let Some(keys) = self.unsettled_buckets.get(&requested.fn_id) else {
            return Vec::new();
        };
        let mut overlapping = Vec::new();
        for key in keys.iter().filter(|key| activation_keys_overlap(t, key, requested)) {
            overlapping.extend(self.covered_witnesses_for_public_key(key));
        }
        overlapping.sort_by(|left, right| {
            format!("{:?}", left.public_key)
                .cmp(&format!("{:?}", right.public_key))
                .then(left.activation_id.cmp(&right.activation_id))
        });
        overlapping
    }

    fn record_observed_edge<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        module: &Module,
        edge: &TypeInferActivationEdgeFact,
    ) {
        let callee = public_activation_body_key(t, module, edge.callee_fn_id, edge.callee_input_tys.clone());
        self.observed_edges_by_witness
            .entry(edge.caller_activation_id)
            .or_default()
            .insert(ObservedActivationEdge {
                callee,
                slot: edge.callsite.callsite.slot,
                span_start: edge.callsite.span_start,
                span_end: edge.callsite.span_end,
            });
        let caller_public_key = public_activation_body_key(t, module, edge.caller_fn_id, edge.caller_input_tys.clone());
        self.callee_witnesses_by_caller_and_callsite
            .entry((caller_public_key, edge.callsite.callsite.clone()))
            .or_default()
            .insert(edge.callee_activation_id);
    }

    fn record_observed_dead_arm(&mut self, dead_arm: &TypeInferDeadArmFact) {
        if !self.witness_public_keys.contains_key(&dead_arm.activation_id) {
            return;
        }
        self.observed_dead_arms_by_witness
            .entry(dead_arm.activation_id)
            .or_default()
            .insert(ObservedDeadArm {
                fn_id: dead_arm.fn_id,
                block_id: dead_arm.block_id,
                branch: dead_arm.branch,
            });
    }

    fn covered_witnesses_for_public_key(&self, public_key: &BodyKey) -> Vec<CoveredActivation> {
        let mut covered = self
            .witness_ids_by_public_key
            .get(public_key)
            .into_iter()
            .flatten()
            .filter_map(|activation_id| {
                self.witness_returns
                    .get(activation_id)
                    .cloned()
                    .map(|state| CoveredActivation {
                        activation_id: *activation_id,
                        public_key: public_key.clone(),
                        state,
                    })
            })
            .collect::<Vec<_>>();
        covered.sort_by(|left, right| left.activation_id.cmp(&right.activation_id));
        covered
    }

    pub(super) fn canonical_public_key<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        requested: SpecKey,
    ) -> SpecKey {
        let requested = erase_closure_identity_from_spec_key(t, requested);
        let requested_body = requested.body_key();
        if self.bucket_returns.contains_key(&requested_body) {
            return requested;
        }
        let covering = self
            .bucket_returns
            .iter()
            .map(|(candidate, _)| candidate)
            .filter(|candidate| candidate.fn_id == requested_body.fn_id)
            .filter(|candidate| activation_key_covers_requested(t, candidate, &requested_body))
            .collect::<Vec<_>>();
        let mut most_specific = covering
            .iter()
            .copied()
            .filter(|candidate| {
                !covering.iter().copied().any(|other| {
                    other != *candidate
                        && activation_key_covers_requested(t, candidate, other)
                        && !activation_key_covers_requested(t, other, candidate)
                })
            })
            .collect::<Vec<_>>();
        most_specific.sort_by(|left, right| format!("{left:?}").cmp(&format!("{right:?}")));
        if most_specific.len() == 1 {
            return SpecKey {
                fn_id: most_specific[0].fn_id,
                input: most_specific[0].input.clone(),
                demand: requested.demand,
            };
        }
        requested
    }

    fn closure_return_map<T: Types<Ty = Ty>>(&self, t: &mut T) -> HashMap<(ClosureTarget, Vec<Ty>), Ty> {
        let mut index = HashMap::new();
        for (key, state) in &self.bucket_returns {
            if key.input.iter().any(Option::is_none) {
                continue;
            }
            let ret = match state {
                TypeInferReturnState::Known(ty) => ty.clone(),
                TypeInferReturnState::NoReturn => t.none(),
                TypeInferReturnState::Pending | TypeInferReturnState::Unknown => continue,
            };
            index.insert((key.fn_id.into(), key_slots_observed(&key.input)), ret);
        }
        index
    }

    fn callsite_result_slot0<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        caller_public_key: &SpecKey,
        callsite: CallsiteId,
    ) -> Option<ResultSlot0> {
        let caller_public_key = self.canonical_public_key(t, caller_public_key.clone()).body_key();
        let witness_ids = self
            .callee_witnesses_by_caller_and_callsite
            .get(&(caller_public_key, callsite))?;
        let mut joined = None;
        for witness_id in witness_ids {
            let state = self.witness_returns.get(witness_id)?;
            joined = Some(match joined {
                Some(prev) => merge_activation_return_state(t, &prev, state),
                None => state.clone(),
            });
        }
        match joined? {
            TypeInferReturnState::Known(ty) => Some(ResultSlot0::Known(ty)),
            TypeInferReturnState::NoReturn => Some(ResultSlot0::Known(t.none())),
            TypeInferReturnState::Pending | TypeInferReturnState::Unknown => Some(ResultSlot0::Pending),
        }
    }
}

fn public_activation_body_key<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    fn_id: FnId,
    input_tys: Vec<Ty>,
) -> BodyKey {
    erase_closure_identity_from_body_key(t, body_key_for_fn_id(module, fn_id, input_tys))
}

fn erase_closure_identity_from_spec_key<T: Types<Ty = Ty> + ClosureTypes>(t: &mut T, mut key: SpecKey) -> SpecKey {
    for slot in &mut key.input {
        if let Some(ty) = slot.take() {
            let erased = t.erase_closure_identity(&ty);
            *slot = Some(t.alpha_normalize_vars(&erased));
        }
    }
    key
}

fn erase_closure_identity_from_body_key<T: Types<Ty = Ty> + ClosureTypes>(t: &mut T, mut key: BodyKey) -> BodyKey {
    for slot in &mut key.input {
        if let Some(ty) = slot.take() {
            let erased = t.erase_closure_identity(&ty);
            *slot = Some(t.alpha_normalize_vars(&erased));
        }
    }
    key
}

fn activation_keys_overlap<T: Types<Ty = Ty> + ClosureTypes>(t: &mut T, left: &BodyKey, right: &BodyKey) -> bool {
    if left.fn_id != right.fn_id {
        return false;
    }
    if left.input.len() != right.input.len() {
        return false;
    }
    left.input
        .iter()
        .zip(&right.input)
        .all(|(left, right)| match (left, right) {
            (Some(left), Some(right)) => activation_tys_overlap(t, left, right),
            (None, _) | (_, None) => true,
        })
}

fn activation_tys_overlap<T: Types<Ty = Ty> + ClosureTypes>(t: &mut T, left: &Ty, right: &Ty) -> bool {
    if !t.is_disjoint(left, right) {
        return true;
    }
    let left = t.erase_closure_identity(left);
    let right = t.erase_closure_identity(right);
    !t.is_disjoint(&left, &right)
}

fn activation_key_covers_requested<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    candidate: &BodyKey,
    requested: &BodyKey,
) -> bool {
    if candidate.fn_id != requested.fn_id {
        return false;
    }
    if candidate.input.len() != requested.input.len() {
        return false;
    }
    candidate
        .input
        .iter()
        .zip(&requested.input)
        .all(|(candidate, requested)| match (candidate, requested) {
            (_, None) => true,
            (Some(candidate), Some(requested)) => activation_ty_covers_requested(t, candidate, requested),
            (None, Some(_)) => false,
        })
}

fn activation_ty_covers_requested<T: Types<Ty = Ty> + ClosureTypes>(t: &mut T, candidate: &Ty, requested: &Ty) -> bool {
    // Activation facts are upper-bound return facts only for the activation
    // keys they cover. A concrete fact for `list(int)` cannot justify a
    // `list(any)` planner key. Recursive convergence may produce a wider fact
    // (`bool` for a `true` request), and closure-literal identity may be more
    // concrete than the planner key; erasing that identity is only a comparison
    // step, not an ABI fact.
    if t.is_subtype(requested, candidate) {
        return true;
    }
    let candidate = t.erase_closure_identity(candidate);
    let requested = t.erase_closure_identity(requested);
    t.is_subtype(&requested, &candidate)
}

fn merge_activation_return_state<T: Types<Ty = Ty>>(
    t: &mut T,
    left: &TypeInferReturnState,
    right: &TypeInferReturnState,
) -> TypeInferReturnState {
    match (left, right) {
        (TypeInferReturnState::Pending, x) | (x, TypeInferReturnState::Pending) => x.clone(),
        (TypeInferReturnState::Unknown, _) | (_, TypeInferReturnState::Unknown) => TypeInferReturnState::Unknown,
        (TypeInferReturnState::NoReturn, x) | (x, TypeInferReturnState::NoReturn) => x.clone(),
        (TypeInferReturnState::Known(a), TypeInferReturnState::Known(b)) => {
            TypeInferReturnState::Known(t.refine_widen(a, b))
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn direct_call_result_knowledge<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    recursive_fns: &HashSet<FnId>,
    caller_spec_key: &SpecKey,
    ident: &CallsiteIdent,
    callee: FnId,
    arg_tys: &[Ty],
    activation_returns: &ActivationReturnFacts,
    selected_edge: Option<&CallEdgePlan>,
) -> CallResultKnowledge {
    if let Some(slot0) = selected_external_call_return_slot0(
        t,
        module,
        callee,
        arg_tys,
        activation_returns,
        &module.fn_by_id(caller_spec_key.fn_id).owner_module,
        selected_edge,
    ) {
        return CallResultKnowledge {
            slot0: ResultSlot0::Known(slot0),
        };
    }

    let callsite = CallsiteId::new(caller_spec_key.fn_id, ident, EmitSlot::Direct);
    if let Some(slot0) = activation_returns.callsite_result_slot0(t, caller_spec_key, callsite) {
        return CallResultKnowledge { slot0 };
    }

    let target_fn = module.fn_by_id(callee);
    let n_params = target_fn.block(target_fn.entry).params.len();
    let target = selected_edge
        .and_then(CallEdgePlan::local_target)
        .cloned()
        .unwrap_or_else(|| {
            fixed_point_spec_key_for_arity(
                t,
                module,
                recursive_fns,
                caller_spec_key.fn_id,
                callee,
                arg_tys.to_vec(),
                n_params,
                None,
            )
        });
    let declared_fact = declared_call_return_fact(
        t,
        module,
        recursive_fns,
        caller_spec_key.fn_id,
        callee,
        arg_tys,
        activation_returns,
        &module.fn_by_id(caller_spec_key.fn_id).owner_module,
    );
    let activation_slot0 = activation_returns.result_slot0_for_key(t, &target);
    let slot0 = call_result_slot0(t, declared_fact.as_ref(), activation_slot0);
    CallResultKnowledge { slot0 }
}

pub(super) fn closure_call_result_knowledge<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    recursive_fns: &HashSet<FnId>,
    caller_spec_key: &SpecKey,
    ident: &CallsiteIdent,
    arg_tys: &[Ty],
    activation_returns: &ActivationReturnFacts,
    selected_target: Option<&SpecKey>,
    closure_ty: Option<&Ty>,
) -> CallResultKnowledge {
    let callsite = CallsiteId::new(caller_spec_key.fn_id, ident, EmitSlot::ClosureCall);
    if let Some(slot0) = activation_returns.callsite_result_slot0(t, caller_spec_key, callsite) {
        return CallResultKnowledge { slot0 };
    }

    if let Some(target) = selected_target {
        let slot0 = activation_returns.result_slot0_for_key(t, target);
        return CallResultKnowledge { slot0 };
    }

    let Some(closure_ty) = closure_ty else {
        return CallResultKnowledge {
            slot0: ResultSlot0::Pending,
        };
    };

    if let Some(keys) = literal_closure_return_keys(
        t,
        module,
        recursive_fns,
        caller_spec_key.fn_id,
        closure_ty,
        arg_tys,
        None,
    ) {
        let mut joined = t.none();
        let mut complete = true;
        for key in &keys {
            match activation_returns.result_slot0_for_key(t, key) {
                ResultSlot0::Known(ret) => joined = t.union(joined, ret),
                ResultSlot0::Pending => complete = false,
            }
        }
        return CallResultKnowledge {
            slot0: if complete {
                ResultSlot0::Known(joined)
            } else {
                ResultSlot0::Pending
            },
        };
    }
    let closure_returns = activation_returns.closure_return_map(t);
    let slot0 = resolve_closure_return(t, closure_ty, &closure_returns, arg_tys)
        .map(ResultSlot0::Known)
        .unwrap_or(ResultSlot0::Pending);
    CallResultKnowledge { slot0 }
}

fn call_result_slot0<T: Types<Ty = Ty>>(
    t: &mut T,
    declared_fact: Option<&DeclaredReturnFact>,
    activation: ResultSlot0,
) -> ResultSlot0 {
    let declared = declared_fact.and_then(|fact| fact.ty.clone());
    match (declared, activation) {
        (Some(declared), ResultSlot0::Known(activation)) if t.is_subtype(&activation, &declared) => {
            ResultSlot0::Known(activation)
        }
        (Some(declared), _) => ResultSlot0::Known(declared),
        (None, ResultSlot0::Known(activation)) => ResultSlot0::Known(activation),
        (None, ResultSlot0::Pending) => ResultSlot0::Pending,
    }
}

/// Type a module via one worklist over `SpecKey`s. The worklist drives spec
/// registration, body typing, executable call-edge discovery, and incoming
/// callable-capability refinement. Continuation slot-0 facts come from
/// activation witness edges plus semantic activation buckets, not from a
/// second planner return engine. The committed
/// `ModulePlan::effective_returns` is projected from activation facts after
/// reachable executable specs settle.
///
/// Two triggers add a spec back to the worklist:
///   1. The spec is freshly discovered (newly-emitted pending key).
///   2. Incoming callable-capability facts for an existing spec change.
///
/// `type_fn` is pure in `(FnIr, entry_key)`; once a spec's `SpecPlan`
/// is computed, it's cached and reused across worklist visits unless the
/// spec's incoming callable capabilities change.
///
/// Discovery walks emit direct calls, closure calls, continuations, receive
/// outcomes, and callable-boundary obligations for known local closures that
/// cross an external/provider boundary. After the worklist drains, a forward
/// reachability sweep prunes specs no longer rooted at an entry seed.
///
/// ## Termination
///
/// The worklist terminates because:
///
///   (a) Spec keys are finite for a closed module under recursive key
///       normalization. Numeric literal chains collapse at recursive
///       boundaries instead of depending on traversal timing.
///
///   (b) Incoming callable-capability facts move monotonically from
///       unknown to a concrete capability or `OpaqueCallable`, and never
///       split once merged.
///
///   (c) A spec is enqueued only on:
///         (i)   First emission — happens at most once per spec key.
///         (ii)  A callable-capability merge changes an entry param.
///
/// Therefore total worklist pops is bounded by
///   O(|specs| * |entry params|)
/// up to the finite capability lattice. `VISIT_HARD_BOUND` below is a
/// debug-only tripwire for invariant violation, NOT a release safety net.
pub fn plan_module<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
    t: &mut T,
    m: &Module,
    tel: &dyn Telemetry,
) -> ModulePlan {
    plan_module_with_role(t, m, tel, "authoritative")
}

fn plan_module_with_role<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
    t: &mut T,
    m: &Module,
    tel: &dyn Telemetry,
    role: &'static str,
) -> ModulePlan {
    WORKLIST_POPS.with(|c| c.set(0));
    TYPE_FN_CALLS.with(|c| c.set(0));
    WALK_CALLS.with(|c| c.set(0));

    let out = discover_specs(t, m, tel);

    let any_key_specs = build_any_key_index(t, m, &out.specs);
    let spec_precedence = key_precedence_order(&out.specs, &any_key_specs);
    let activation_return_telemetry = out.activation_return_telemetry;
    let activation_return_projection_gaps = out.activation_return_projection_gaps;
    let activation_projection_facts = out.activation_projection_facts;
    let spec_roles = out.spec_roles;

    let mut mt = ModulePlan {
        specs: out.specs,
        reachable_specs: out.reachable_specs,
        spec_roles,
        effective_returns: out.effective_returns,
        any_key_specs,
        spec_precedence,
        fn_effects: out.fn_effects,
        dead_branches: HashMap::new(),
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
                activation_return_fact_count: activation_return_telemetry.fact_count as u64,
                activation_return_key_count: activation_return_telemetry.key_count as u64,
                activation_return_complete_entry_count: activation_return_telemetry.complete_entry_count as u64,
                activation_return_unresolved_entry_count: activation_return_telemetry.unresolved_entry_count as u64,
                activation_return_invalid_entry_count: activation_return_telemetry.invalid_entry_count as u64,
                activation_return_known_count: activation_return_telemetry.known_count as u64,
                activation_return_unresolved_count: activation_return_telemetry.unresolved_count as u64,
                activation_return_no_return_count: activation_return_telemetry.no_return_count as u64,
                activation_return_projected_count: activation_return_telemetry.projected_count as u64,
                activation_return_projection_gap_count: activation_return_telemetry.projection_gap_count as u64,
            },
            &crate::metadata! {
                // The label is explicit so consumers can key the committed
                // codegen/frontend plan's shape on it instead of guessing from
                // event order. Non-authoritative planning phases must be
                // visible too, with their own role, rather than hidden behind
                // NullTelemetry.
                role: role,
                type_kernel: "activation",
                module_path: m.module_path().to_owned(),
                activation_return_projection_gaps: activation_return_projection_gaps,
                module: opaque(m),
                module_plan: opaque(&mt),
            },
        );
        for (spec_key, ft) in &mt.specs {
            let body = m.fn_by_id(spec_key.fn_id);
            let (body_counts, body_callsites) = body_callsite_inventory(body);
            let plan_call_edges = plan_call_edge_inventory(ft, body.id);
            tel.execute(
                &["fz", "planner", "spec_pair_inventory"],
                &crate::measurements! {
                    non_tail_call_count: body_counts.non_tail_call_count,
                    non_tail_closure_call_count: body_counts.non_tail_closure_call_count,
                    tail_call_count: body_counts.tail_call_count,
                    tail_closure_call_count: body_counts.tail_closure_call_count,
                    receive_count: body_counts.receive_count,
                    call_edge_count: ft.call_edges.len() as u64,
                },
                &crate::metadata! {
                    role: role,
                    spec_key: format!("{:?}", spec_key),
                    body_fn_id: body.id.0 as u64,
                    body_name: body.name.clone(),
                    body_callsites: body_callsites,
                    plan_call_edges: plan_call_edges,
                },
            );
        }
        for fact in &activation_projection_facts {
            let body = m.fn_by_id(fact.spec_key.fn_id);
            let covered_known_count = fact
                .covered_activations
                .iter()
                .filter(|covered| matches!(covered.state, TypeInferReturnState::Known(_)))
                .count();
            let covered_unresolved_count = fact
                .covered_activations
                .iter()
                .filter(|covered| {
                    matches!(
                        covered.state,
                        TypeInferReturnState::Pending | TypeInferReturnState::Unknown
                    )
                })
                .count();
            let covered_no_return_count = fact
                .covered_activations
                .iter()
                .filter(|covered| matches!(covered.state, TypeInferReturnState::NoReturn))
                .count();
            tel.execute(
                &["fz", "planner", "activation_projection"],
                &crate::measurements! {
                    covered_activation_count: fact.covered_activations.len() as u64,
                    covered_known_count: covered_known_count as u64,
                    covered_unresolved_count: covered_unresolved_count as u64,
                    covered_no_return_count: covered_no_return_count as u64,
                    projected_call_edge_count: fact.projected_call_edges.len() as u64,
                    projected_dead_arm_count: fact.projected_dead_arms.len() as u64,
                    exact_coverage: matches!(fact.kind, ActivationProjectionKind::Exact) as u64,
                    projection_gap: fact.projected_state.is_none() as u64,
                },
                &crate::metadata! {
                    role: role,
                    spec_key: format!("{:?}", fact.spec_key),
                    spec_role: mt
                        .spec_roles
                        .iter()
                        .find_map(|(key, role)| (key.body_key() == fact.spec_key).then_some(*role))
                        .map(SpecReachabilityRole::as_str)
                        .unwrap_or("unknown"),
                    body_fn_id: body.id.0 as u64,
                    body_name: body.name.clone(),
                    projection_kind: fact.kind.as_str(),
                    projected_return_state: render_type_infer_return_state(t, fact.projected_state.as_ref()),
                    effective_return: mt
                        .effective_returns
                        .get(&fact.spec_key)
                        .map(ty_display)
                        .unwrap_or_else(|| "<missing>".to_string()),
                    covered_activations: fact
                        .covered_activations
                        .iter()
                        .map(|covered| {
                            let name = m.fn_by_id(covered.public_key.fn_id).name.clone();
                            format!(
                                "#{:?} {name} {:?} => {}",
                                covered.activation_id,
                                covered.public_key,
                                render_type_infer_return_state(t, Some(&covered.state))
                            )
                        })
                        .collect::<Vec<_>>(),
                    projected_call_edges: fact
                        .projected_call_edges
                        .iter()
                        .map(|edge| {
                            let callee_name = m.fn_by_id(edge.callee.fn_id).name.clone();
                            format!(
                                "{}@{}..{} -> {} {:?}",
                                emit_slot_label(edge.slot),
                                edge.span_start,
                                edge.span_end,
                                callee_name,
                                edge.callee
                            )
                        })
                        .collect::<Vec<_>>(),
                    projected_dead_arms: fact
                        .projected_dead_arms
                        .iter()
                        .map(|dead_arm| {
                            let fn_name = m.fn_by_id(dead_arm.fn_id).name.clone();
                            format!(
                                "{}#b{}:{}",
                                fn_name,
                                dead_arm.block_id.0,
                                dead_branch_label(dead_arm.branch)
                            )
                        })
                        .collect::<Vec<_>>(),
                },
            );
        }
    }
    mt
}

/// Outcome of the shared worklist core: the discovered specs (each carrying its
/// callable capabilities, call edges, and types), activation-projected returns,
/// and the per-FnId effect summary. `plan_module` finalizes this into a
/// `ModulePlan` (any-key index, precedence, dead branches, telemetry).
struct DiscoverOutput {
    specs: HashMap<SpecKey, SpecPlan>,
    reachable_specs: SpecKeySet,
    spec_roles: HashMap<SpecKey, SpecReachabilityRole>,
    effective_returns: HashMap<BodyKey, Ty>,
    fn_effects: FnEffects,
    activation_return_telemetry: ActivationReturnTelemetry,
    activation_return_projection_gaps: Vec<String>,
    activation_projection_facts: Vec<ActivationProjectionFact>,
}

/// Drive the worklist to discover every reachable executable spec from the
/// module's entry seeds, then prune orphans and project activation returns over
/// the reachable set.
fn discover_specs<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
    t: &mut T,
    m: &Module,
    tel: &dyn Telemetry,
) -> DiscoverOutput {
    let call_graph = build_recursion_graph(m);
    let mut sccs = tarjan_scc(&call_graph);
    sccs.reverse();
    let mut recursive_fns: HashSet<FnId> = HashSet::new();
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
    let mut incoming_param_callable_capabilities: IncomingParamCallableCapabilities = HashMap::new();
    let mut visit_count: HashMap<SpecKey, usize> = HashMap::new();
    let fn_effects = compute_fn_effects(m);
    let activation_returns = ActivationReturnFacts::from_entry_seeds(t, m, tel);

    let mut work: VecDeque<SpecKey> = entry_seeds(t, m)
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
        &activation_returns,
        &mut incoming_param_callable_capabilities,
        &mut visit_count,
    );

    let reachable: SpecKeySet = reachable_specs_from_call_edges(t, m, &specs);
    let callable_entry_specs: SpecKeySet = reachable
        .iter()
        .filter(|spec| specs.values().any(|plan| plan.callable_entry_targets.contains(*spec)))
        .cloned()
        .collect();
    specs.retain(|k, _| reachable.contains(k));
    let mut effective_returns: HashMap<BodyKey, Ty> = HashMap::new();
    activation_returns.project_effective_returns(
        t,
        m,
        &recursive_fns,
        &reachable,
        &callable_entry_specs,
        &mut effective_returns,
    );
    let activation_projection_facts =
        activation_returns.projection_facts(t, m, &recursive_fns, &reachable, &callable_entry_specs);
    let spec_roles = compute_spec_roles(t, m, &reachable, &callable_entry_specs, &activation_projection_facts);
    let activation_return_telemetry =
        activation_returns.telemetry(t, m, &recursive_fns, &reachable, &callable_entry_specs);
    let activation_return_projection_gaps =
        activation_returns.projection_gap_keys(t, m, &recursive_fns, &reachable, &callable_entry_specs);
    verify_closed_expectations(&reachable, &specs, &effective_returns);

    DiscoverOutput {
        specs,
        reachable_specs: reachable,
        spec_roles,
        effective_returns,
        fn_effects,
        activation_return_telemetry,
        activation_return_projection_gaps,
        activation_projection_facts,
    }
}

fn reachable_specs_from_call_edges<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    m: &Module,
    specs: &HashMap<SpecKey, SpecPlan>,
) -> SpecKeySet {
    let mut reachable: SpecKeySet = entry_seeds(t, m)
        .into_iter()
        .map(|(fid, key)| spec_key_for_fn_id(m, fid, key))
        .collect();
    let mut bfs: VecDeque<SpecKey> = reachable.iter().cloned().collect();
    while let Some(spec) = bfs.pop_front() {
        let Some(plan) = specs.get(&spec) else {
            continue;
        };
        for target in local_successor_targets(plan) {
            if reachable.insert(target.clone()) {
                bfs.push_back(target);
            }
        }
    }
    reachable
}

fn verify_closed_expectations(
    reachable: &SpecKeySet,
    specs: &HashMap<SpecKey, SpecPlan>,
    effective_returns: &HashMap<BodyKey, Ty>,
) {
    for spec in reachable {
        assert!(specs.contains_key(spec), "reachable spec {:?} has no typed body", spec);
        assert!(
            effective_returns.contains_key(&spec.body_key()),
            "reachable spec {:?} has no effective return",
            spec
        );
        let plan = specs
            .get(spec)
            .unwrap_or_else(|| panic!("reachable spec {:?} has no typed body", spec));
        for target in local_successor_targets(plan) {
            assert!(
                reachable.contains(&target),
                "reachable spec {:?} reaches unreachable target {:?}",
                spec,
                target
            );
            assert!(
                specs.contains_key(&target),
                "reachable target {:?} from {:?} has no typed body",
                target,
                spec
            );
        }
    }
}

fn compute_spec_roles<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    m: &Module,
    reachable: &SpecKeySet,
    callable_entry_specs: &SpecKeySet,
    activation_projection_facts: &[ActivationProjectionFact],
) -> HashMap<SpecKey, SpecReachabilityRole> {
    let entry_specs: SpecKeySet = entry_seeds(t, m)
        .into_iter()
        .map(|(fid, key)| spec_key_for_fn_id(m, fid, key))
        .collect();
    let activation_covered: HashSet<BodyKey> = activation_projection_facts
        .iter()
        .filter(|fact| !fact.covered_activations.is_empty())
        .map(|fact| fact.spec_key.clone())
        .collect();

    let mut roles = HashMap::new();
    for spec in reachable {
        let role = if entry_specs.contains(spec) {
            SpecReachabilityRole::Entry
        } else if activation_covered.contains(&spec.body_key()) {
            SpecReachabilityRole::Activation
        } else if callable_entry_specs.contains(spec) {
            SpecReachabilityRole::CallableEntry
        } else {
            SpecReachabilityRole::ProjectionGap
        };
        roles.insert(spec.clone(), role);
    }
    roles
}

/// One per-FnId effect fact over the static call graph.
///
/// A function's effects are independent of any caller's return delivery, so
/// this is computed once — before the worklist — and stored on `ModulePlan` for
/// downstream effect-sensitive passes.
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
            for Stmt::Let(_, prim) in &b.stmts {
                local.union_with(prim_effects(m, prim));
            }
            // A terminal `Halt` returns the process's final value to the
            // scheduler; nothing executes after it, so it contributes no
            // downstream observation point. Every other terminator contributes
            // its local effects: closure calls are opaque, receive is a
            // scheduler boundary.
            if !matches!(b.terminator, Term::Halt(_)) {
                local.union_with(term_effects(&b.terminator));
            }
            match &b.terminator {
                Term::Call {
                    callee, continuation, ..
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

/// Worklist driver over selected executable edges.
///
/// Each pop:
///   1. type_fn the spec if new (cached by spec_key).
///   2. Walk for discovery → fills `WalkResult`.
///   3. Install call-edge plans and enqueue newly discovered local targets.
#[allow(clippy::too_many_arguments)]
fn process_worklist<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    m: &Module,
    fn_effects: &FnEffects,
    recursive_fns: &HashSet<FnId>,
    work: &mut VecDeque<SpecKey>,
    in_work: &mut SpecKeySet,
    specs: &mut HashMap<SpecKey, SpecPlan>,
    activation_returns: &ActivationReturnFacts,
    incoming_param_callable_capabilities: &mut IncomingParamCallableCapabilities,
    visit_count: &mut HashMap<SpecKey, usize>,
) {
    while let Some(spec_key) = work.pop_front() {
        in_work.remove(&spec_key);
        WORKLIST_POPS.with(|c| c.set(c.get() + 1));

        let Some(&j) = m.fn_idx.get(&spec_key.fn_id) else {
            continue;
        };
        ensure_spec_typed(t, m, j, &spec_key, incoming_param_callable_capabilities, specs);
        check_visit_bound(&spec_key, visit_count);
        let result = discover_spec_outputs(
            t,
            m,
            fn_effects,
            j,
            &spec_key,
            specs,
            activation_returns,
            recursive_fns,
            incoming_param_callable_capabilities,
        );
        let WalkResult {
            call_edges,
            capability_updates,
            callable_entry_targets,
        } = result;
        install_walk_result(specs, &spec_key, call_edges, callable_entry_targets);
        enqueue_capability_updates(&capability_updates, work, in_work);
        enqueue_discovered_local_targets(&spec_key, specs, work, in_work);
    }
}

fn ensure_spec_typed<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    m: &Module,
    fn_idx: usize,
    spec_key: &SpecKey,
    incoming_param_callable_capabilities: &IncomingParamCallableCapabilities,
    specs: &mut HashMap<SpecKey, SpecPlan>,
) {
    if specs.get(spec_key).is_some_and(|ft| {
        entry_callable_capabilities_match(m, fn_idx, ft, incoming_param_callable_capabilities.get(spec_key))
    }) {
        return;
    }
    TYPE_FN_CALLS.with(|c| c.set(c.get() + 1));
    let input_tys = spec_key_input_tys(t, spec_key);
    let mut ft = type_fn(t, &m.fns[fn_idx], m, Some(&input_tys));
    if let Some(arg_caps) = incoming_param_callable_capabilities.get(spec_key) {
        let entry = m.fns[fn_idx].entry;
        let entry_params = &m.fns[fn_idx].block(entry).params;
        for (slot, p) in entry_params.iter().enumerate() {
            if let Some(Some(capability)) = arg_caps.get(slot) {
                ft.callable_capabilities.insert(*p, capability.clone());
            }
        }
    }
    refine_known_closure_capture_capabilities(&m.fns[fn_idx], &mut ft);
    specs.insert(spec_key.clone(), ft);
}

fn refine_known_closure_capture_capabilities(f: &FnIr, ft: &mut SpecPlan) {
    for blk in &f.blocks {
        for stmt in &blk.stmts {
            let Stmt::Let(v, prim) = stmt;
            let Prim::MakeClosure(_, _, captured) = prim else {
                continue;
            };
            let capture_capabilities = captured
                .iter()
                .map(|cv| ft.callable_capabilities.get(cv).cloned())
                .collect::<Vec<_>>();
            if let Some(CallableCapability::KnownClosure {
                capture_capabilities: existing,
                ..
            }) = ft.callable_capabilities.get_mut(v)
            {
                *existing = capture_capabilities;
            }
        }
    }
}

fn entry_callable_capabilities_match(
    m: &Module,
    fn_idx: usize,
    ft: &SpecPlan,
    incoming: Option<&Vec<Option<CallableCapability>>>,
) -> bool {
    let entry = m.fns[fn_idx].entry;
    let entry_params = &m.fns[fn_idx].block(entry).params;
    for (slot, p) in entry_params.iter().enumerate() {
        let expected = incoming.and_then(|caps| caps.get(slot)).and_then(|cap| cap.clone());
        let actual = ft.callable_capabilities.get(p).cloned();
        if actual != expected {
            return false;
        }
    }
    true
}

fn enqueue_capability_updates(capability_updates: &[SpecKey], work: &mut VecDeque<SpecKey>, in_work: &mut SpecKeySet) {
    for target in capability_updates {
        if in_work.insert(target.clone()) {
            work.push_back(target.clone());
        }
    }
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

fn discover_spec_outputs<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    m: &Module,
    fn_effects: &FnEffects,
    fn_idx: usize,
    spec_key: &SpecKey,
    specs: &HashMap<SpecKey, SpecPlan>,
    activation_returns: &ActivationReturnFacts,
    recursive_fns: &HashSet<FnId>,
    incoming_param_callable_capabilities: &mut IncomingParamCallableCapabilities,
) -> WalkResult {
    let caller_ft = specs.get(spec_key).unwrap();
    let mut result = WalkResult::default();
    walk_spec_for_discovery(
        t,
        &m.fns[fn_idx],
        caller_ft,
        m,
        fn_effects,
        activation_returns,
        recursive_fns,
        spec_key,
        incoming_param_callable_capabilities,
        &mut result,
    );
    result
}

fn install_walk_result(
    specs: &mut HashMap<SpecKey, SpecPlan>,
    spec_key: &SpecKey,
    call_edges: HashMap<CallsiteId, CallEdgePlan>,
    callable_entry_targets: HashSet<SpecKey>,
) {
    if let Some(ft) = specs.get_mut(spec_key) {
        ft.install_call_edges(call_edges);
        ft.install_callable_entry_targets(callable_entry_targets);
    }
}

fn local_successor_targets(spec: &SpecPlan) -> Vec<SpecKey> {
    let mut out = Vec::new();
    for edge in spec.call_edges.values() {
        if let Some(target) = edge.local_target() {
            out.push(target.clone());
        }
        if let Some(contract) = edge.return_contract.as_ref()
            && !out.contains(&contract.target)
        {
            out.push(contract.target.clone());
        }
    }
    for target in &spec.callable_entry_targets {
        if !out.contains(target) {
            out.push(target.clone());
        }
    }
    out
}

fn enqueue_discovered_local_targets(
    spec_key: &SpecKey,
    specs: &HashMap<SpecKey, SpecPlan>,
    work: &mut VecDeque<SpecKey>,
    in_work: &mut SpecKeySet,
) {
    let Some(plan) = specs.get(spec_key) else {
        return;
    };
    for target in local_successor_targets(plan) {
        if !specs.contains_key(&target) && in_work.insert(target.clone()) {
            work.push_back(target);
        }
    }
}

fn selected_external_call_return_slot0<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    callee: FnId,
    arg_tys: &[Ty],
    activation_returns: &ActivationReturnFacts,
    owner_module: &str,
    selected_edge: Option<&CallEdgePlan>,
) -> Option<Ty> {
    matches!(
        selected_edge.map(|edge| &edge.target),
        Some(CallEdgeTarget::External { .. })
    )
    .then(|| {
        declared_call_return_fact(
            t,
            module,
            &HashSet::new(),
            callee,
            callee,
            arg_tys,
            activation_returns,
            owner_module,
        )
        .and_then(|fact| fact.ty)
        .unwrap_or_else(|| t.any())
    })
}

#[allow(clippy::too_many_arguments)]
fn declared_call_return_fact<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    recursive_fns: &HashSet<FnId>,
    caller: FnId,
    callee: FnId,
    arg_tys: &[Ty],
    activation_returns: &ActivationReturnFacts,
    owner_module: &str,
) -> Option<DeclaredReturnFact> {
    let spec_set = module.declared_specs.get(&callee)?;
    let application = apply_spec_set(t, spec_set, arg_tys, |t, query: CallbackReturnQuery<'_>| {
        declared_callback_return_fact(t, module, recursive_fns, caller, activation_returns, query)
    });
    let mut fact = match application {
        SpecApplicationOutcome::Known(application) => DeclaredReturnFact {
            ty: (!t.has_vars(&application.result)).then_some(application.result),
        },
        SpecApplicationOutcome::Underconstrained(_application) => DeclaredReturnFact { ty: None },
        SpecApplicationOutcome::NoMatch => return None,
    };
    if let Some(ty) = fact.ty.take() {
        fact.ty = Some(t.mint_owned_resource_aliases(ty, owner_module, &module.opaque_inners));
    }
    Some(fact)
}

#[allow(clippy::too_many_arguments)]
fn declared_callback_return_fact<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    recursive_fns: &HashSet<FnId>,
    caller: FnId,
    activation_returns: &ActivationReturnFacts,
    query: CallbackReturnQuery<'_>,
) -> Option<CallbackReturnFact<SpecKey>> {
    let fn_id: FnId = query.target.into();
    let target_fn = module.fn_by_id(fn_id);
    let n_params = target_fn.block(target_fn.entry).params.len();
    let mut full_key = query.captures.to_vec();
    full_key.extend_from_slice(query.args);
    let key = fixed_point_spec_key_for_arity(
        t,
        module,
        recursive_fns,
        caller,
        fn_id,
        full_key,
        n_params,
        Some(callback_return_demand(query.demand)),
    );

    match activation_returns.result_slot0_for_key(t, &key) {
        ResultSlot0::Known(ret) => Some(CallbackReturnFact::Known {
            result: ret,
            read: key,
            complete: true,
        }),
        ResultSlot0::Pending => Some(CallbackReturnFact::Pending { read: key }),
    }
}

fn callback_return_demand(demand: CallbackReturnDemand) -> ReturnDemand {
    match demand {
        CallbackReturnDemand::Value => ReturnDemand::value(),
        CallbackReturnDemand::TupleFields(arity) => ReturnDemand::tuple_fields(arity),
    }
}
