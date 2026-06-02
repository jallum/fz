use super::closures::literal_closure_return_keys;
use super::diagnostics::{compute_dead_branches, module_plan_stats};
use super::effects::{prim_effects, term_effects};
use super::fn_types::{
    CallsiteCallableCapabilities, CapabilityPlan, EffectSummary, EmitsByCaller, EmitterSiteSet,
    FixedPointInputObservation, FixedPointSlotSummaries, FnEffects, HoldersMap, ModulePlan,
    ProducesMap, ReturnDemand, ReturnDepsByCaller, ReturnReaders, SpecKey, SpecKeySet, SpecPlan,
    SpecReachabilityRole, TYPE_FN_CALLS, VISIT_HARD_BOUND, WALK_CALLS, WORKLIST_POPS,
    build_any_key_index, fixed_point_spec_key_for_arity, key_precedence_order,
    normalize_result_correspondence_key, spec_key_for_fn_id, spec_key_input_tys,
};
use super::reachable::{cont_key_from_slot0, env_at_terminator};
use super::type_fn::type_fn;
use super::walk::{WalkResult, walk_spec_for_discovery};
use crate::fz_ir::{Block, FnId, Module, Term};
use crate::ir_callgraph::{build_recursion_graph, entry_seeds};
use crate::type_infer::{
    TypeInferActivationEdgeFact, TypeInferActivationFact, TypeInferActivationId,
    TypeInferDeadArmFact, TypeInferReturnState,
};
use std::collections::HashMap;

pub(crate) enum ResultSlot0 {
    Known(crate::types::Ty),
    Pending,
}

pub(crate) struct CallResultKnowledge {
    pub(crate) slot0: ResultSlot0,
}

#[derive(Clone, Debug)]
struct DeclaredReturnFact {
    ty: Option<crate::types::Ty>,
}

pub(super) struct ActivationReturnFacts {
    bucket_returns: HashMap<SpecKey, TypeInferReturnState>,
    witness_returns: HashMap<TypeInferActivationId, TypeInferReturnState>,
    witness_public_keys: HashMap<TypeInferActivationId, SpecKey>,
    witness_ids_by_public_key: HashMap<SpecKey, Vec<TypeInferActivationId>>,
    observed_edges_by_witness:
        HashMap<TypeInferActivationId, std::collections::HashSet<ObservedActivationEdge>>,
    observed_dead_arms_by_witness:
        HashMap<TypeInferActivationId, std::collections::HashSet<ObservedDeadArm>>,
    callee_witnesses_by_caller_and_callsite: HashMap<
        (SpecKey, crate::fz_ir::CallsiteId),
        std::collections::HashSet<TypeInferActivationId>,
    >,
    unsettled_buckets: HashMap<FnId, Vec<SpecKey>>,
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
    UnsettledOverlap,
    Uncovered,
}

impl ActivationProjectionKind {
    fn as_str(&self) -> &'static str {
        match self {
            Self::Exact => "exact",
            Self::Union => "union",
            Self::UnsettledOverlap => "unsettled_overlap",
            Self::Uncovered => "uncovered",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ActivationProjectionFact {
    spec_key: SpecKey,
    kind: ActivationProjectionKind,
    projected_state: Option<TypeInferReturnState>,
    covered_activations: Vec<CoveredActivation>,
    projected_call_edges: Vec<ObservedActivationEdge>,
    projected_dead_arms: Vec<ObservedDeadArm>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CoveredActivation {
    activation_id: TypeInferActivationId,
    public_key: SpecKey,
    state: TypeInferReturnState,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ObservedActivationEdge {
    callee: SpecKey,
    slot: crate::fz_ir::EmitSlot,
    span_start: u64,
    span_end: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ObservedDeadArm {
    fn_id: FnId,
    block_id: crate::fz_ir::BlockId,
    branch: crate::fz_ir::DeadBranch,
}

fn render_type_infer_return_state<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes,
>(
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

fn emit_slot_label(slot: crate::fz_ir::EmitSlot) -> &'static str {
    match slot {
        crate::fz_ir::EmitSlot::Direct => "direct",
        crate::fz_ir::EmitSlot::Cont => "cont",
        crate::fz_ir::EmitSlot::ClosureCall => "closure_call",
        crate::fz_ir::EmitSlot::CallableBoundary => "callable_boundary",
    }
}

fn dead_branch_label(branch: crate::fz_ir::DeadBranch) -> &'static str {
    match branch {
        crate::fz_ir::DeadBranch::Then => "then",
        crate::fz_ir::DeadBranch::Else => "else",
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

    fn from_entry_seeds<
        T: crate::types::Types<Ty = crate::types::Ty>
            + crate::types::ClosureTypes
            + crate::types::RenderTypes,
    >(
        t: &mut T,
        module: &Module,
        tel: &dyn crate::telemetry::Telemetry,
    ) -> Self {
        let seeds = entry_seeds(t, module);
        let mut facts = Self::empty();
        for (entry, input_tys) in seeds {
            let outcome = crate::type_infer::infer_from_entry(t, module, entry, &input_tys, tel);
            match outcome.status {
                crate::type_infer::TypeInferStatus::Complete => facts.complete_entry_count += 1,
                crate::type_infer::TypeInferStatus::Unresolved => {
                    facts.unresolved_entry_count += 1;
                }
                crate::type_infer::TypeInferStatus::Invalid => facts.invalid_entry_count += 1,
            }
            for activation in outcome.activations {
                facts.raw_fact_count += 1;
                facts.record_activation(t, module, activation);
            }
            for edge in &outcome.edges {
                facts.record_observed_edge(module, edge);
            }
            for dead_arm in &outcome.dead_arms {
                facts.record_observed_dead_arm(dead_arm);
            }
        }
        facts
    }

    fn record_activation<T: crate::types::Types<Ty = crate::types::Ty>>(
        &mut self,
        t: &mut T,
        module: &Module,
        activation: TypeInferActivationFact,
    ) {
        let activation_id = activation.activation_id;
        let public_key = spec_key_for_fn_id(module, activation.fn_id, activation.input_tys);
        let state = activation.return_state;
        self.witness_returns.insert(activation_id, state.clone());
        self.witness_public_keys
            .insert(activation_id, public_key.clone());
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

    fn insert_unsettled(&mut self, key: SpecKey) {
        let keys = self.unsettled_buckets.entry(key.fn_id).or_default();
        if !keys.contains(&key) {
            keys.push(key);
        }
    }

    /// Project an activation return state into the planner's return map shape.
    /// `type_infer` keeps unresolved facts as `Pending`/`Unknown`; `any` is only
    /// introduced here at the planner boundary for still-reachable specs.
    fn projected_return_for_key<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        key: &SpecKey,
    ) -> Option<crate::types::Ty> {
        match self.return_state_for_key(t, key)? {
            TypeInferReturnState::Known(ty) => Some(ty.clone()),
            TypeInferReturnState::NoReturn => Some(t.none()),
            TypeInferReturnState::Pending | TypeInferReturnState::Unknown => Some(t.any()),
        }
    }

    fn return_state_for_key<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        key: &SpecKey,
    ) -> Option<TypeInferReturnState> {
        if let Some(exact) = self.bucket_returns.get(key) {
            return Some(exact.clone());
        }
        if self.request_overlaps_unsettled(t, key) {
            return None;
        }
        let mut joined = None;
        for (candidate, state) in self
            .bucket_returns
            .iter()
            .filter(|(candidate, _)| candidate.fn_id == key.fn_id)
        {
            if activation_key_covers_requested(t, candidate, key) {
                joined = Some(match joined {
                    Some(prev) => merge_activation_return_state(t, &prev, state),
                    None => state.clone(),
                });
            }
        }
        joined
    }

    pub(super) fn result_slot0_for_key<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        key: &SpecKey,
    ) -> ResultSlot0 {
        match self.return_state_for_key(t, key) {
            Some(TypeInferReturnState::Known(ty)) => ResultSlot0::Known(ty),
            Some(TypeInferReturnState::NoReturn) => ResultSlot0::Known(t.none()),
            Some(TypeInferReturnState::Pending | TypeInferReturnState::Unknown) | None => {
                ResultSlot0::Pending
            }
        }
    }

    fn request_overlaps_unsettled<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        requested: &SpecKey,
    ) -> bool {
        self.unsettled_buckets
            .get(&requested.fn_id)
            .is_some_and(|keys| {
                keys.iter()
                    .any(|key| activation_keys_overlap(t, key, requested))
            })
    }

    fn project_effective_returns<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        reachable: &SpecKeySet,
        effective_returns: &mut HashMap<SpecKey, crate::types::Ty>,
    ) {
        effective_returns.clear();
        for key in reachable {
            let ret = if let Some(ret) = self.projected_return_for_key(t, key) {
                ret
            } else {
                t.any()
            };
            effective_returns.insert(key.clone(), ret);
        }
    }

    fn telemetry<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
        &self,
        t: &mut T,
        reachable: &SpecKeySet,
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
            if self.return_state_for_key(t, key).is_none() {
                stats.projection_gap_count += 1;
            }
        }
        stats
    }

    fn projection_gap_keys<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        module: &Module,
        reachable: &SpecKeySet,
    ) -> Vec<String> {
        let mut gaps = Vec::new();
        for key in reachable {
            if self.return_state_for_key(t, key).is_none() {
                let name = module.fn_by_id(key.fn_id).name.clone();
                gaps.push(format!("{name} {key:?}"));
            }
        }
        gaps.sort();
        gaps
    }

    fn projection_facts<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        reachable: &SpecKeySet,
    ) -> Vec<ActivationProjectionFact> {
        let mut facts: Vec<_> = reachable
            .iter()
            .cloned()
            .map(|spec_key| self.projection_fact_for_key(t, spec_key))
            .collect();
        facts.sort_by(|left, right| {
            format!("{:?}", left.spec_key).cmp(&format!("{:?}", right.spec_key))
        });
        facts
    }

    fn projection_fact_for_key<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        spec_key: SpecKey,
    ) -> ActivationProjectionFact {
        let (kind, covered_activations) = if self.bucket_returns.contains_key(&spec_key) {
            (
                ActivationProjectionKind::Exact,
                self.covered_witnesses_for_public_key(&spec_key),
            )
        } else {
            let covering = self.covered_activation_states_for_request(t, &spec_key);
            if !covering.is_empty() {
                let kind = if covering.len() == 1 {
                    ActivationProjectionKind::Exact
                } else {
                    ActivationProjectionKind::Union
                };
                (kind, covering)
            } else {
                let unsettled = self.overlapping_unsettled_activation_states(t, &spec_key);
                if unsettled.is_empty() {
                    (ActivationProjectionKind::Uncovered, Vec::new())
                } else {
                    (ActivationProjectionKind::UnsettledOverlap, unsettled)
                }
            }
        };
        let mut projected_call_edges = std::collections::HashSet::new();
        let mut projected_dead_arms: Option<std::collections::HashSet<ObservedDeadArm>> = None;
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
        projected_call_edges.sort_by(|left, right| {
            activation_edge_inventory_entry(left).cmp(&activation_edge_inventory_entry(right))
        });
        let mut projected_dead_arms: Vec<_> = projected_dead_arms
            .unwrap_or_default()
            .into_iter()
            .collect();
        projected_dead_arms.sort_by(|left, right| {
            dead_arm_inventory_entry(left).cmp(&dead_arm_inventory_entry(right))
        });
        ActivationProjectionFact {
            projected_state: self.return_state_for_key(t, &spec_key),
            spec_key,
            kind,
            covered_activations,
            projected_call_edges,
            projected_dead_arms,
        }
    }

    fn covered_activation_states_for_request<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        requested: &SpecKey,
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

    fn overlapping_unsettled_activation_states<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        requested: &SpecKey,
    ) -> Vec<CoveredActivation> {
        let Some(keys) = self.unsettled_buckets.get(&requested.fn_id) else {
            return Vec::new();
        };
        let mut overlapping = Vec::new();
        for key in keys
            .iter()
            .filter(|key| activation_keys_overlap(t, key, requested))
        {
            overlapping.extend(self.covered_witnesses_for_public_key(key));
        }
        overlapping.sort_by(|left, right| {
            format!("{:?}", left.public_key)
                .cmp(&format!("{:?}", right.public_key))
                .then(left.activation_id.cmp(&right.activation_id))
        });
        overlapping
    }

    fn record_observed_edge(&mut self, module: &Module, edge: &TypeInferActivationEdgeFact) {
        let callee = spec_key_for_fn_id(module, edge.callee_fn_id, edge.callee_input_tys.clone());
        self.observed_edges_by_witness
            .entry(edge.caller_activation_id)
            .or_default()
            .insert(ObservedActivationEdge {
                callee,
                slot: edge.callsite.callsite.slot,
                span_start: edge.callsite.span_start,
                span_end: edge.callsite.span_end,
            });
        let caller_public_key =
            spec_key_for_fn_id(module, edge.caller_fn_id, edge.caller_input_tys.clone());
        self.callee_witnesses_by_caller_and_callsite
            .entry((caller_public_key, edge.callsite.callsite.clone()))
            .or_default()
            .insert(edge.callee_activation_id);
    }

    fn record_observed_dead_arm(&mut self, dead_arm: &TypeInferDeadArmFact) {
        if !self
            .witness_public_keys
            .contains_key(&dead_arm.activation_id)
        {
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

    fn covered_witnesses_for_public_key(&self, public_key: &SpecKey) -> Vec<CoveredActivation> {
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

    pub(super) fn canonical_public_key<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        requested: SpecKey,
    ) -> SpecKey {
        if self.bucket_returns.contains_key(&requested) {
            return requested;
        }
        let covering = self
            .bucket_returns
            .iter()
            .map(|(candidate, _)| candidate)
            .filter(|candidate| candidate.fn_id == requested.fn_id)
            .filter(|candidate| {
                candidate.demand == requested.demand
                    && activation_key_covers_requested(t, candidate, &requested)
            })
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
            return most_specific[0].clone();
        }
        requested
    }

    fn closure_return_map<T: crate::types::Types<Ty = crate::types::Ty>>(
        &self,
        t: &mut T,
    ) -> HashMap<(crate::types::ClosureTarget, Vec<crate::types::Ty>), crate::types::Ty> {
        let mut index = HashMap::new();
        for (key, state) in &self.bucket_returns {
            if !key.demand.is_value() || key.input.iter().any(Option::is_none) {
                continue;
            }
            let ret = match state {
                TypeInferReturnState::Known(ty) => ty.clone(),
                TypeInferReturnState::NoReturn => t.none(),
                TypeInferReturnState::Pending | TypeInferReturnState::Unknown => continue,
            };
            index.insert(
                (
                    key.fn_id.into(),
                    crate::types::key_slots_observed(&key.input),
                ),
                ret,
            );
        }
        index
    }

    fn callsite_result_slot0<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &mut T,
        caller_public_key: &SpecKey,
        callsite: crate::fz_ir::CallsiteId,
    ) -> Option<ResultSlot0> {
        let caller_public_key = self.canonical_public_key(t, caller_public_key.clone());
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
            TypeInferReturnState::Pending | TypeInferReturnState::Unknown => {
                Some(ResultSlot0::Pending)
            }
        }
    }
}

fn activation_keys_overlap<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    left: &SpecKey,
    right: &SpecKey,
) -> bool {
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

fn activation_tys_overlap<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    left: &crate::types::Ty,
    right: &crate::types::Ty,
) -> bool {
    if !t.is_disjoint(left, right) {
        return true;
    }
    let left = t.erase_closure_identity(left);
    let right = t.erase_closure_identity(right);
    !t.is_disjoint(&left, &right)
}

fn activation_key_covers_requested<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    candidate: &SpecKey,
    requested: &SpecKey,
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
            (Some(candidate), Some(requested)) => {
                activation_ty_covers_requested(t, candidate, requested)
            }
            (None, Some(_)) => false,
        })
}

fn activation_ty_covers_requested<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    candidate: &crate::types::Ty,
    requested: &crate::types::Ty,
) -> bool {
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

fn merge_activation_return_state<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    left: &TypeInferReturnState,
    right: &TypeInferReturnState,
) -> TypeInferReturnState {
    match (left, right) {
        (TypeInferReturnState::Pending, x) | (x, TypeInferReturnState::Pending) => x.clone(),
        (TypeInferReturnState::Unknown, _) | (_, TypeInferReturnState::Unknown) => {
            TypeInferReturnState::Unknown
        }
        (TypeInferReturnState::NoReturn, x) | (x, TypeInferReturnState::NoReturn) => x.clone(),
        (TypeInferReturnState::Known(a), TypeInferReturnState::Known(b)) => {
            TypeInferReturnState::Known(t.refine_widen(a, b))
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn direct_call_result_knowledge<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    caller_spec_key: &SpecKey,
    ident: &crate::fz_ir::CallsiteIdent,
    callee: FnId,
    arg_tys: &[crate::types::Ty],
    activation_returns: &ActivationReturnFacts,
    slot_summaries: &FixedPointSlotSummaries,
    direct_target: Option<&SpecKey>,
) -> CallResultKnowledge {
    if let Some(slot0) = external_call_return_slot0_for_spec(
        t,
        module,
        caller_spec_key.fn_id,
        ident,
        callee,
        arg_tys,
        activation_returns,
        &module.fn_by_id(caller_spec_key.fn_id).owner_module,
    ) {
        return CallResultKnowledge {
            slot0: ResultSlot0::Known(slot0),
        };
    }

    let callsite =
        crate::fz_ir::CallsiteId::new(caller_spec_key.fn_id, ident, crate::fz_ir::EmitSlot::Direct);
    if let Some(slot0) = activation_returns.callsite_result_slot0(t, caller_spec_key, callsite) {
        return CallResultKnowledge { slot0 };
    }

    let target_fn = module.fn_by_id(callee);
    let n_params = target_fn.block(target_fn.entry).params.len();
    let target = direct_target.cloned().unwrap_or_else(|| {
        fixed_point_spec_key_for_arity(
            t,
            module,
            recursive_fns,
            slot_summaries,
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
        slot_summaries,
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

pub(super) fn known_closure_result_knowledge<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    caller_spec_key: &SpecKey,
    ident: &crate::fz_ir::CallsiteIdent,
    target: FnId,
    arg_tys: &[crate::types::Ty],
    activation_returns: &ActivationReturnFacts,
    slot_summaries: &FixedPointSlotSummaries,
) -> CallResultKnowledge {
    let callsite = crate::fz_ir::CallsiteId::new(
        caller_spec_key.fn_id,
        ident,
        crate::fz_ir::EmitSlot::ClosureCall,
    );
    if let Some(slot0) = activation_returns.callsite_result_slot0(t, caller_spec_key, callsite) {
        return CallResultKnowledge { slot0 };
    }

    let target_fn = module.fn_by_id(target);
    let n_params = target_fn.block(target_fn.entry).params.len();
    let key = fixed_point_spec_key_for_arity(
        t,
        module,
        recursive_fns,
        slot_summaries,
        caller_spec_key.fn_id,
        target,
        arg_tys.to_vec(),
        n_params,
        None,
    );
    let declared_fact = declared_call_return_fact(
        t,
        module,
        recursive_fns,
        slot_summaries,
        caller_spec_key.fn_id,
        target,
        arg_tys,
        activation_returns,
        &module.fn_by_id(caller_spec_key.fn_id).owner_module,
    );
    let activation_slot0 = activation_returns.result_slot0_for_key(t, &key);
    let slot0 = call_result_slot0(t, declared_fact.as_ref(), activation_slot0);
    CallResultKnowledge { slot0 }
}

pub(super) fn closure_value_result_knowledge<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    caller: FnId,
    closure_ty: &crate::types::Ty,
    arg_tys: &[crate::types::Ty],
    activation_returns: &ActivationReturnFacts,
    slot_summaries: &FixedPointSlotSummaries,
) -> CallResultKnowledge {
    if let Some(keys) = literal_closure_return_keys(
        t,
        module,
        recursive_fns,
        slot_summaries,
        caller,
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
    let slot0 = crate::specs::resolve_closure_return(t, closure_ty, &closure_returns, arg_tys)
        .map(ResultSlot0::Known)
        .unwrap_or(ResultSlot0::Pending);
    CallResultKnowledge { slot0 }
}

fn call_result_slot0<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    declared_fact: Option<&DeclaredReturnFact>,
    activation: ResultSlot0,
) -> ResultSlot0 {
    let declared = declared_fact.and_then(|fact| fact.ty.clone());
    match (declared, activation) {
        (Some(declared), ResultSlot0::Known(activation))
            if t.is_subtype(&activation, &declared) =>
        {
            ResultSlot0::Known(activation)
        }
        (Some(declared), _) => ResultSlot0::Known(declared),
        (None, ResultSlot0::Known(activation)) => ResultSlot0::Known(activation),
        (None, ResultSlot0::Pending) => ResultSlot0::Pending,
    }
}

/// Type a module via one worklist over `SpecKey`s. The worklist drives spec
/// registration, body typing, executable call-edge discovery, and recursive
/// key-slot convergence. Continuation slot-0 facts come from activation
/// witness edges plus semantic activation buckets, not from a second planner
/// return engine. The committed `ModulePlan::effective_returns` is projected
/// from activation facts after reachable executable specs settle.
///
/// Two triggers add a spec back to the worklist:
///   1. The spec is freshly discovered (newly-emitted pending key).
///   2. A recursive slot summary changes.
///      Activation-projected returns are final return authority; unresolved
///      activation returns do not keep edges alive by inventing `any`.
///
/// `type_fn` is pure in `(FnIr, entry_key)`; once a spec's `SpecPlan`
/// is computed, it's cached and reused across worklist visits — only
/// the walk + return-recompute re-run when triggered.
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
///   (a) fixed-point returns are updated only via `union`,
///       which is monotone w.r.t. lattice inclusion. So recursive
///       slot summaries are monotonically non-decreasing in the
///       product type lattice.
///       Discovery never turns a pending activation return into an opaque
///       continuation slot; pending stops that edge until the activation
///       authority has a fact.
///
///   (b) The type lattice has finite height H, bounded by the
///       count of distinct type-axis values in the program
///       (atoms, ints, floats, tuple shapes, list shapes, etc —
///       all finite for a closed program).
///
///   (c) A spec is enqueued only on:
///         (i)   First emission — happens at most once per spec key.
///         (ii)  A recursive slot summary changes, each monotonically bounded
///               by (a) and (b).
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
pub fn plan_module<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    tel: &dyn crate::telemetry::Telemetry,
) -> ModulePlan {
    plan_module_with_role(t, m, tel, "authoritative")
}

fn plan_module_with_role<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    tel: &dyn crate::telemetry::Telemetry,
    role: &'static str,
) -> ModulePlan {
    WORKLIST_POPS.with(|c| c.set(0));
    TYPE_FN_CALLS.with(|c| c.set(0));
    WALK_CALLS.with(|c| c.set(0));

    let out = discover_specs(t, m, PlannerTelemetry { tel, role });

    let any_key_specs = build_any_key_index(t, m, &out.specs);
    let spec_precedence = key_precedence_order(&out.specs, &any_key_specs);
    let activation_return_telemetry = out.activation_return_telemetry;
    let activation_return_projection_gaps = out.activation_return_projection_gaps;
    let activation_projection_facts = out.activation_projection_facts;
    let spec_roles = out.spec_roles;

    let mut mt = ModulePlan {
        specs: out.specs,
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
                module: crate::telemetry::value::opaque(m),
                module_plan: crate::telemetry::value::opaque(&mt),
            },
        );
        for (spec_key, ft) in &mt.specs {
            let body = m.fn_by_id(spec_key.fn_id);
            let (body_counts, body_callsites) =
                crate::ir_planner::inventory::body_callsite_inventory(body);
            let plan_call_edges =
                crate::ir_planner::inventory::plan_call_edge_inventory(ft, body.id);
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
                        .get(&fact.spec_key)
                        .copied()
                        .map(SpecReachabilityRole::as_str)
                        .unwrap_or("unknown"),
                    body_fn_id: body.id.0 as u64,
                    body_name: body.name.clone(),
                    projection_kind: fact.kind.as_str(),
                    projected_return_state: render_type_infer_return_state(t, fact.projected_state.as_ref()),
                    effective_return: mt
                        .effective_returns
                        .get(&fact.spec_key)
                        .map(crate::concrete_types::ty_display)
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
/// The worklist (including activation projection and recursive slot-summary
/// convergence) is reused rather than replaced by a one-shot pass: capability
/// precision is load-bearing. A var's callable capability narrows as its type
/// narrows under activation-backed return refinement, and the consensus
/// `KnownFn` that drives a devirtualization can be lost if returns stay coarse
/// — empirically, dropping that convergence
/// regresses `apply2`, `enum_sort`, `higher_order`, and
/// `multi_caller_spec_divergent`. The redundancy removed is run A's
/// authoritative-plan *shape* (the full `ModulePlan` with dead-branch and
/// precedence finalization, and its `planner.planned` event), not the
/// worklist compute, which the capabilities genuinely require. The analysis is
/// interprocedural over the linked working module — the reason the pretyped
/// frontend's shallow `_pre_types` cannot serve here.
pub fn plan_callable_capabilities<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
) -> CapabilityPlan {
    let null_tel = crate::telemetry::NullTelemetry;
    let out = discover_specs(
        t,
        m,
        PlannerTelemetry {
            tel: &null_tel,
            role: "capabilities",
        },
    );
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
/// callable capabilities, call edges, and types), activation-projected returns,
/// and the per-FnId effect summary. `plan_module` finalizes this into a
/// `ModulePlan` (any-key index, precedence, dead branches, telemetry);
/// `plan_callable_capabilities` keeps only the per-spec capabilities.
struct DiscoverOutput {
    specs: HashMap<SpecKey, SpecPlan>,
    spec_roles: HashMap<SpecKey, SpecReachabilityRole>,
    effective_returns: HashMap<SpecKey, crate::types::Ty>,
    fn_effects: FnEffects,
    activation_return_telemetry: ActivationReturnTelemetry,
    activation_return_projection_gaps: Vec<String>,
    activation_projection_facts: Vec<ActivationProjectionFact>,
}

#[derive(Clone, Copy)]
struct PlannerTelemetry<'a> {
    tel: &'a dyn crate::telemetry::Telemetry,
    role: &'static str,
}

/// Drive the worklist to discover every reachable executable spec from the
/// module's entry seeds, then prune orphans and project activation returns over
/// the reachable set. Shared by `plan_module` and `plan_callable_capabilities`.
fn discover_specs<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    tel: PlannerTelemetry<'_>,
) -> DiscoverOutput {
    let call_graph = build_recursion_graph(m);
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
    let mut complete_returns: SpecKeySet = std::collections::HashSet::new();
    let mut callsite_callable_capabilities: CallsiteCallableCapabilities = HashMap::new();
    let mut return_readers: ReturnReaders = HashMap::new();
    let mut return_deps_by_caller: ReturnDepsByCaller = HashMap::new();
    let mut visit_count: HashMap<SpecKey, usize> = HashMap::new();

    let mut produces: ProducesMap = HashMap::new();
    let mut holders: HoldersMap = HashMap::new();
    let mut emits_by_caller: EmitsByCaller = HashMap::new();
    let mut slot_summaries: FixedPointSlotSummaries = HashMap::new();
    let fn_effects = compute_fn_effects(m);
    let activation_returns = ActivationReturnFacts::from_entry_seeds(t, m, tel.tel);

    let mut work: std::collections::VecDeque<SpecKey> = entry_seeds(t, m)
        .into_iter()
        .map(|(fid, key)| spec_key_for_fn_id(m, fid, key))
        .collect();
    let mut in_work: SpecKeySet = work.iter().cloned().collect();

    process_worklist(
        t,
        m,
        tel,
        &fn_effects,
        &recursive_fns,
        &mut work,
        &mut in_work,
        &mut specs,
        &mut effective_returns,
        &mut complete_returns,
        &activation_returns,
        &mut callsite_callable_capabilities,
        &mut return_readers,
        &mut return_deps_by_caller,
        &mut visit_count,
        &mut produces,
        &mut holders,
        &mut emits_by_caller,
        &mut slot_summaries,
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
    activation_returns.project_effective_returns(t, &reachable, &mut effective_returns);
    let activation_projection_facts = activation_returns.projection_facts(t, &reachable);
    let spec_roles = compute_spec_roles(t, m, &reachable, &holders, &activation_projection_facts);
    let activation_return_telemetry = activation_returns.telemetry(t, &reachable);
    let activation_return_projection_gaps =
        activation_returns.projection_gap_keys(t, m, &reachable);
    verify_closed_expectations(
        &reachable,
        &specs,
        &effective_returns,
        &emits_by_caller,
        &produces,
    );

    DiscoverOutput {
        specs,
        spec_roles,
        effective_returns,
        fn_effects,
        activation_return_telemetry,
        activation_return_projection_gaps,
        activation_projection_facts,
    }
}

fn verify_closed_expectations(
    reachable: &SpecKeySet,
    specs: &HashMap<SpecKey, SpecPlan>,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    emits_by_caller: &EmitsByCaller,
    produces: &ProducesMap,
) {
    for spec in reachable {
        assert!(
            specs.contains_key(spec),
            "reachable spec {:?} has no typed body",
            spec
        );
        assert!(
            effective_returns.contains_key(spec),
            "reachable spec {:?} has no effective return",
            spec
        );
        if let Some(sites) = emits_by_caller.get(spec) {
            for site in sites {
                let target = produces.get(site).unwrap_or_else(|| {
                    panic!(
                        "reachable spec {:?} emits at {:?} without a produced target",
                        spec, site
                    )
                });
                assert!(
                    reachable.contains(target),
                    "reachable spec {:?} emits unreachable target {:?} at {:?}",
                    spec,
                    target,
                    site
                );
                assert!(
                    specs.contains_key(target),
                    "reachable emit target {:?} from {:?} at {:?} has no typed body",
                    target,
                    spec,
                    site
                );
            }
        }
    }
}

fn compute_spec_roles<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    m: &Module,
    reachable: &SpecKeySet,
    _holders: &HoldersMap,
    activation_projection_facts: &[ActivationProjectionFact],
) -> HashMap<SpecKey, SpecReachabilityRole> {
    let entry_specs: SpecKeySet = entry_seeds(t, m)
        .into_iter()
        .map(|(fid, key)| spec_key_for_fn_id(m, fid, key))
        .collect();
    let activation_covered: SpecKeySet = activation_projection_facts
        .iter()
        .filter(|fact| !fact.covered_activations.is_empty())
        .map(|fact| fact.spec_key.clone())
        .collect();

    let mut roles = HashMap::new();
    for spec in reachable {
        let role = if entry_specs.contains(spec) {
            SpecReachabilityRole::Entry
        } else if activation_covered.contains(spec) {
            SpecReachabilityRole::Activation
        } else {
            SpecReachabilityRole::ProjectionGap
        };
        roles.insert(spec.clone(), role);
    }
    roles
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
                local.union_with(prim_effects(m, prim));
            }
            // A terminal `Halt` returns the process's final value to the
            // scheduler; nothing executes after it, so it cannot observe — or
            // be disturbed by — relocating an allocation that builds the
            // returned value. It is transparent to the return-context-motion
            // barrier (fz-w34.2 generalizes this to position-scoping). Every
            // other terminator contributes its local effects: closure calls
            // are opaque, receive is a scheduler boundary.
            if !matches!(b.terminator, Term::Halt(_)) {
                local.union_with(term_effects(&b.terminator));
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
///   5. Recompute this spec's fixed-point return. If changed, enqueue
///      every spec in `return_readers[spec]`. Final return authority is the
///      activation projection after pruning.
#[allow(clippy::too_many_arguments)]
fn process_worklist<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    m: &Module,
    tel: PlannerTelemetry<'_>,
    fn_effects: &FnEffects,
    recursive_fns: &std::collections::HashSet<FnId>,
    work: &mut std::collections::VecDeque<SpecKey>,
    in_work: &mut SpecKeySet,
    specs: &mut HashMap<SpecKey, SpecPlan>,
    effective_returns: &mut HashMap<SpecKey, crate::types::Ty>,
    complete_returns: &mut SpecKeySet,
    activation_returns: &ActivationReturnFacts,
    callsite_callable_capabilities: &mut CallsiteCallableCapabilities,
    return_readers: &mut ReturnReaders,
    return_deps_by_caller: &mut ReturnDepsByCaller,
    visit_count: &mut HashMap<SpecKey, usize>,
    produces: &mut ProducesMap,
    holders: &mut HoldersMap,
    emits_by_caller: &mut EmitsByCaller,
    slot_summaries: &mut FixedPointSlotSummaries,
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
            activation_returns,
            recursive_fns,
            slot_summaries,
            callsite_callable_capabilities,
        );
        let WalkResult {
            emits,
            call_edges,
            return_reads,
            fixed_point_inputs,
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
        update_effective_return_and_enqueue_readers(
            t,
            m,
            tel,
            &spec_key,
            recursive_fns,
            specs,
            effective_returns,
            complete_returns,
            activation_returns,
            return_readers,
            return_deps_by_caller,
            work,
            in_work,
            slot_summaries,
            return_reads,
        );
        update_fixed_point_slot_summaries(
            t,
            m,
            tel,
            recursive_fns,
            slot_summaries,
            fixed_point_inputs,
            work,
            in_work,
            specs,
        );
    }
}

fn update_fixed_point_slot_summaries<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    m: &Module,
    tel: PlannerTelemetry<'_>,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &mut FixedPointSlotSummaries,
    observations: Vec<FixedPointInputObservation>,
    work: &mut std::collections::VecDeque<SpecKey>,
    in_work: &mut SpecKeySet,
    specs: &HashMap<SpecKey, SpecPlan>,
) -> bool {
    let mut changed = false;
    for observation in observations {
        changed |= update_fixed_point_slot_summary_from_observation(
            t,
            m,
            tel,
            recursive_fns,
            slot_summaries,
            observation,
            work.len(),
            specs.len(),
        );
    }

    if changed {
        for key in specs.keys() {
            if in_work.insert(key.clone()) {
                work.push_back(key.clone());
            }
        }
    }
    changed
}

fn update_fixed_point_slot_summary_from_observation<
    T: crate::types::Types<Ty = crate::types::Ty>,
>(
    t: &mut T,
    m: &Module,
    tel: PlannerTelemetry<'_>,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &mut FixedPointSlotSummaries,
    observation: FixedPointInputObservation,
    queue_len: usize,
    spec_count: usize,
) -> bool {
    if !recursive_fns.contains(&observation.fn_id) {
        return false;
    }
    let f = m.fn_by_id(observation.fn_id);
    if f.category == crate::fz_ir::FnCategory::Matcher {
        return false;
    }
    let result_linked = super::fn_types::result_linked_param_slots(m, observation.fn_id);
    if result_linked.is_empty() {
        return false;
    }

    let observed_key = spec_key_for_fn_id(m, observation.fn_id, observation.input_tys.clone());
    let mut changed = false;
    for idx in result_linked {
        let Some(ty) = observation.input_tys.get(idx) else {
            continue;
        };
        if t.has_vars(ty) {
            continue;
        }
        let widened = t.widen_for_recursive_spec_key(ty);
        match slot_summaries.get(&(observation.fn_id, idx)).cloned() {
            Some(prev) => {
                let merged = t.refine_widen(&prev, &widened);
                if !t.is_equivalent(&merged, &prev) {
                    emit_fixed_point_slot_summary_update(
                        tel,
                        &observed_key,
                        f,
                        idx,
                        Some(format!("{:?}", prev)),
                        format!("{:?}", widened),
                        format!("{:?}", merged),
                        queue_len,
                        spec_count,
                    );
                    slot_summaries.insert((observation.fn_id, idx), merged);
                    changed = true;
                }
            }
            None => {
                emit_fixed_point_slot_summary_update(
                    tel,
                    &observed_key,
                    f,
                    idx,
                    None,
                    format!("{:?}", widened),
                    format!("{:?}", widened),
                    queue_len,
                    spec_count,
                );
                slot_summaries.insert((observation.fn_id, idx), widened);
                changed = true;
            }
        }
    }
    changed
}

fn emit_fixed_point_slot_summary_update(
    tel: PlannerTelemetry<'_>,
    spec_key: &SpecKey,
    f: &crate::fz_ir::FnIr,
    slot_index: usize,
    prev: Option<String>,
    observed: String,
    merged: String,
    queue_len: usize,
    spec_count: usize,
) {
    tel.tel.execute(
        &["fz", "planner", "fixed_point_slot_summary_update"],
        &crate::measurements! {
            slot_index: slot_index as u64,
            queue_len: queue_len as u64,
            spec_count: spec_count as u64,
        },
        &crate::metadata! {
            role: tel.role,
            spec_key: format!("{:?}", spec_key),
            fn_id: spec_key.fn_id.0 as u64,
            fn_name: f.name.clone(),
            prev_summary: prev.unwrap_or_else(|| "<none>".to_string()),
            observed_summary: observed,
            merged_summary: merged,
        },
    );
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
    activation_returns: &ActivationReturnFacts,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &FixedPointSlotSummaries,
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
        activation_returns,
        recursive_fns,
        slot_summaries,
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
    tel: PlannerTelemetry<'_>,
    spec_key: &SpecKey,
    recursive_fns: &std::collections::HashSet<FnId>,
    specs: &HashMap<SpecKey, SpecPlan>,
    effective_returns: &mut HashMap<SpecKey, crate::types::Ty>,
    complete_returns: &mut SpecKeySet,
    activation_returns: &ActivationReturnFacts,
    return_readers: &mut ReturnReaders,
    return_deps_by_caller: &mut ReturnDepsByCaller,
    work: &mut std::collections::VecDeque<SpecKey>,
    in_work: &mut SpecKeySet,
    slot_summaries: &FixedPointSlotSummaries,
    walk_return_reads: Vec<SpecKey>,
) {
    let prev_ret = effective_returns.get(spec_key).cloned();
    let prev_complete = complete_returns.contains(spec_key);
    let walk_read_count = walk_return_reads.len();
    let mut compute_reads = Vec::new();
    let (computed_ret, complete) = compute_return_for_spec(
        t,
        m,
        spec_key,
        recursive_fns,
        specs,
        effective_returns,
        complete_returns,
        activation_returns,
        slot_summaries,
        &mut compute_reads,
    );
    let new_ret = match prev_ret.clone() {
        Some(prev) => t.union(prev, computed_ret),
        None => computed_ret,
    };
    let compute_read_count = compute_reads.len();
    sync_return_dependencies(
        spec_key,
        walk_return_reads,
        compute_reads,
        specs,
        return_readers,
        return_deps_by_caller,
        work,
        in_work,
    );
    let ret_changed = effective_returns
        .get(spec_key)
        .is_none_or(|prev| !t.is_equivalent(&new_ret, prev));
    let complete_changed = complete_returns.contains(spec_key) != complete;
    if ret_changed {
        effective_returns.insert(spec_key.clone(), new_ret.clone());
    }
    if complete {
        complete_returns.insert(spec_key.clone());
    } else {
        complete_returns.remove(spec_key);
    }
    if ret_changed || complete_changed {
        enqueue_return_readers(spec_key, specs, return_readers, work, in_work);
    }
    emit_return_fixpoint_step(
        m,
        tel,
        spec_key,
        specs,
        effective_returns,
        complete_returns,
        return_deps_by_caller,
        work,
        prev_ret.as_ref(),
        &new_ret,
        prev_complete,
        complete,
        ret_changed,
        complete_changed,
        walk_read_count,
        compute_read_count,
    );
}

fn sync_return_dependencies(
    spec_key: &SpecKey,
    walk_return_reads: Vec<SpecKey>,
    compute_reads: Vec<SpecKey>,
    specs: &HashMap<SpecKey, SpecPlan>,
    return_readers: &mut ReturnReaders,
    return_deps_by_caller: &mut ReturnDepsByCaller,
    work: &mut std::collections::VecDeque<SpecKey>,
    in_work: &mut SpecKeySet,
) {
    let new_reads: SpecKeySet = walk_return_reads.into_iter().chain(compute_reads).collect();
    let prev_reads = return_deps_by_caller.remove(spec_key).unwrap_or_default();

    for stale in prev_reads.difference(&new_reads) {
        if let Some(readers) = return_readers.get_mut(stale) {
            readers.remove(spec_key);
            if readers.is_empty() {
                return_readers.remove(stale);
            }
        }
    }

    for callee_key in &new_reads {
        return_readers
            .entry(callee_key.clone())
            .or_default()
            .insert(spec_key.clone());
        if !specs.contains_key(callee_key) && in_work.insert(callee_key.clone()) {
            work.push_back(callee_key.clone());
        }
    }

    return_deps_by_caller.insert(spec_key.clone(), new_reads);
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

#[allow(clippy::too_many_arguments)]
fn emit_return_fixpoint_step(
    m: &Module,
    tel: PlannerTelemetry<'_>,
    spec_key: &SpecKey,
    specs: &HashMap<SpecKey, SpecPlan>,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    complete_returns: &SpecKeySet,
    return_deps_by_caller: &ReturnDepsByCaller,
    work: &std::collections::VecDeque<SpecKey>,
    prev_ret: Option<&crate::types::Ty>,
    new_ret: &crate::types::Ty,
    prev_complete: bool,
    complete: bool,
    ret_changed: bool,
    complete_changed: bool,
    walk_read_count: usize,
    compute_read_count: usize,
) {
    let PlannerTelemetry { tel, role } = tel;
    let visit = WORKLIST_POPS.with(|c| c.get()) as u64;
    let deps = return_deps_by_caller
        .get(spec_key)
        .cloned()
        .unwrap_or_default();
    let dep_keys: Vec<String> = deps.iter().map(|key| format!("{:?}", key)).collect();
    let missing_specs = deps.iter().filter(|key| !specs.contains_key(*key)).count() as u64;
    let missing_returns = deps
        .iter()
        .filter(|key| !effective_returns.contains_key(*key))
        .count() as u64;
    let incomplete_deps = deps
        .iter()
        .filter(|key| !complete_returns.contains(*key))
        .count() as u64;
    let body_name = m.fn_by_id(spec_key.fn_id).name.clone();
    tel.execute(
        &["fz", "planner", "return_fixpoint_step"],
        &crate::measurements! {
            visit: visit,
            queue_len: work.len() as u64,
            spec_count: specs.len() as u64,
            walk_read_count: walk_read_count as u64,
            compute_read_count: compute_read_count as u64,
            dep_count: deps.len() as u64,
            missing_specs: missing_specs,
            missing_returns: missing_returns,
            incomplete_deps: incomplete_deps,
        },
        &crate::metadata! {
            role: role,
            spec_key: format!("{:?}", spec_key),
            fn_id: spec_key.fn_id.0 as u64,
            fn_name: body_name,
            ret_changed: ret_changed,
            complete_changed: complete_changed,
            prev_complete: prev_complete,
            complete: complete,
            prev_ret: prev_ret.map(crate::concrete_types::ty_display).unwrap_or_else(|| "<none>".to_string()),
            new_ret: crate::concrete_types::ty_display(new_ret),
            deps: dep_keys,
        },
    );
}

/// Compute one spec's fixed-point return by joining every reachable
/// return-producing terminator. A missing downstream return contributes
/// `none()` as a provisional value and marks the contribution incomplete;
/// an existing downstream return can still participate before it is complete,
/// so recursive SCCs can widen to their fixed point.
///
/// Every callee key whose return is consulted is pushed into `reads`; the
/// worklist folds those into `return_readers` so callee-return changes
/// re-enqueue this spec. The committed `ModulePlan` does not publish this as
/// return authority; it publishes activation-projected returns.
#[derive(Clone)]
struct ReturnContribution {
    ty: crate::types::Ty,
    complete: bool,
}

fn compute_return_for_spec<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    spec_key: &SpecKey,
    recursive_fns: &std::collections::HashSet<FnId>,
    specs: &HashMap<SpecKey, SpecPlan>,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    complete_returns: &SpecKeySet,
    activation_returns: &ActivationReturnFacts,
    slot_summaries: &FixedPointSlotSummaries,
    reads: &mut Vec<SpecKey>,
) -> (T::Ty, bool) {
    let Some(&j) = module.fn_idx.get(&spec_key.fn_id) else {
        return (t.none(), true);
    };
    let Some(ft) = specs.get(spec_key) else {
        return (t.none(), false);
    };
    let f = &module.fns[j];

    let mut joined = t.none();
    let mut complete = true;
    for b in &f.blocks {
        if !ft.reachable_blocks.contains(&b.id) {
            continue;
        }
        let term_env = env_at_terminator(t, ft, b, module);
        let contribution = match &b.terminator {
            Term::Return(rv) => Some(ReturnContribution {
                ty: term_env.get(rv).cloned().unwrap_or_else(|| t.any()),
                complete: true,
            }),
            Term::TailCall {
                callee,
                args,
                ident,
                ..
            } => Some(direct_tail_return_contribution(
                t,
                module,
                recursive_fns,
                spec_key,
                effective_returns,
                complete_returns,
                activation_returns,
                slot_summaries,
                reads,
                &term_env,
                ident,
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
                complete_returns,
                slot_summaries,
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
                complete_returns,
                activation_returns,
                slot_summaries,
                reads,
                b,
                continuation,
            )),
            Term::ReceiveMatched { clauses, after, .. } => {
                Some(receive_matched_return_contribution(
                    t,
                    module,
                    effective_returns,
                    complete_returns,
                    reads,
                    clauses,
                    after,
                ))
            }
            Term::Halt(_) | Term::Goto(_, _) | Term::If { .. } => None,
        };
        if let Some(contribution) = contribution {
            complete &= contribution.complete;
            joined = t.union(joined, contribution.ty);
        }
    }
    (joined, complete)
}

#[allow(clippy::too_many_arguments)]
fn direct_tail_return_contribution<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    spec_key: &SpecKey,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    complete_returns: &SpecKeySet,
    activation_returns: &ActivationReturnFacts,
    slot_summaries: &FixedPointSlotSummaries,
    reads: &mut Vec<SpecKey>,
    term_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
    ident: &crate::fz_ir::CallsiteIdent,
    callee: FnId,
    args: &[crate::fz_ir::Var],
) -> ReturnContribution {
    let arg_tys = arg_tys(t, term_env, args);
    if let Some(ty) = external_call_return_slot0_for_spec(
        t,
        module,
        spec_key.fn_id,
        ident,
        callee,
        &arg_tys,
        activation_returns,
        &module.fn_by_id(spec_key.fn_id).owner_module,
    ) {
        return ReturnContribution { ty, complete: true };
    }
    let target_fn = module.fn_by_id(callee);
    let n_params = target_fn.block(target_fn.entry).params.len();
    let key = fixed_point_spec_key_for_arity(
        t,
        module,
        recursive_fns,
        slot_summaries,
        spec_key.fn_id,
        callee,
        arg_tys,
        n_params,
        Some(spec_key.demand.clone()),
    );
    lookup_return_read(t, effective_returns, complete_returns, reads, key)
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
    complete_returns: &SpecKeySet,
    slot_summaries: &FixedPointSlotSummaries,
    reads: &mut Vec<SpecKey>,
    term_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
    closure: crate::fz_ir::Var,
    args: &[crate::fz_ir::Var],
) -> ReturnContribution {
    if let Some(target) = ft.known_fn(&closure) {
        return known_tail_closure_return_contribution(
            t,
            module,
            recursive_fns,
            spec_key,
            effective_returns,
            complete_returns,
            slot_summaries,
            reads,
            term_env,
            target,
            args,
        );
    }
    let Some(cv_ty) = term_env.get(&closure) else {
        return ReturnContribution {
            ty: t.any(),
            complete: true,
        };
    };
    literal_tail_closure_return_contribution(
        t,
        module,
        recursive_fns,
        spec_key,
        effective_returns,
        complete_returns,
        slot_summaries,
        reads,
        term_env,
        cv_ty,
        args,
    )
}

#[allow(clippy::too_many_arguments)]
fn known_tail_closure_return_contribution<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    spec_key: &SpecKey,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    complete_returns: &SpecKeySet,
    slot_summaries: &FixedPointSlotSummaries,
    reads: &mut Vec<SpecKey>,
    term_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
    target: FnId,
    args: &[crate::fz_ir::Var],
) -> ReturnContribution {
    let target_fn = module.fn_by_id(target);
    let np = target_fn.block(target_fn.entry).params.len();
    let ad = arg_tys(t, term_env, args);
    let key = fixed_point_spec_key_for_arity(
        t,
        module,
        recursive_fns,
        slot_summaries,
        spec_key.fn_id,
        target,
        ad,
        np,
        Some(spec_key.demand.clone()),
    );
    lookup_return_read(t, effective_returns, complete_returns, reads, key)
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
    complete_returns: &SpecKeySet,
    slot_summaries: &FixedPointSlotSummaries,
    reads: &mut Vec<SpecKey>,
    term_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
    cv_ty: &crate::types::Ty,
    args: &[crate::fz_ir::Var],
) -> ReturnContribution {
    let clauses = t.callable_clauses(cv_ty);
    let mut all_lit = clauses.is_some();
    let mut acc = t.none();
    let mut complete = true;
    let ad = arg_tys(t, term_env, args);
    if let Some(keys) = literal_closure_return_keys(
        t,
        module,
        recursive_fns,
        slot_summaries,
        spec_key.fn_id,
        cv_ty,
        &ad,
        Some(spec_key.demand.clone()),
    ) {
        for key in keys {
            let dy = lookup_return_read(t, effective_returns, complete_returns, reads, key);
            complete &= dy.complete;
            acc = t.union(acc, dy.ty);
        }
    } else if clauses.is_some() {
        all_lit = false;
    }
    if all_lit {
        ReturnContribution { ty: acc, complete }
    } else {
        ReturnContribution {
            ty: t.any(),
            complete: true,
        }
    }
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
    complete_returns: &SpecKeySet,
    activation_returns: &ActivationReturnFacts,
    slot_summaries: &FixedPointSlotSummaries,
    reads: &mut Vec<SpecKey>,
    block: &Block,
    continuation: &crate::fz_ir::Cont,
) -> ReturnContribution {
    let key = if let Some(key) = block.terminator.ident().and_then(|ident| {
        ft.local_call_target(&crate::fz_ir::CallsiteId::new(
            spec_key.fn_id,
            ident,
            crate::fz_ir::EmitSlot::Cont,
        ))
        .cloned()
    }) {
        key
    } else {
        let Some(cont_k) = cont_key_for_spec(
            t,
            block,
            continuation,
            ft,
            module,
            recursive_fns,
            spec_key,
            activation_returns,
            slot_summaries,
        ) else {
            return ReturnContribution {
                ty: t.none(),
                complete: false,
            };
        };
        spec_key_for_fn_id(module, continuation.fn_id, cont_k)
    };
    lookup_return_read(t, effective_returns, complete_returns, reads, key)
}

fn receive_matched_return_contribution<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    complete_returns: &SpecKeySet,
    reads: &mut Vec<SpecKey>,
    clauses: &[crate::fz_ir::ReceiveClause],
    after: &Option<crate::fz_ir::ReceiveAfter>,
) -> ReturnContribution {
    let any = t.any();
    let mut joined = t.none();
    let mut complete = true;
    for fid in clauses
        .iter()
        .map(|c| c.body)
        .chain(after.iter().map(|a| a.body))
    {
        let dy = receive_outcome_return_contribution(
            t,
            module,
            effective_returns,
            complete_returns,
            reads,
            fid,
            &any,
        );
        complete &= dy.complete;
        joined = t.union(joined, dy.ty);
    }
    ReturnContribution {
        ty: joined,
        complete,
    }
}

fn receive_outcome_return_contribution<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    complete_returns: &SpecKeySet,
    reads: &mut Vec<SpecKey>,
    fid: FnId,
    any: &crate::types::Ty,
) -> ReturnContribution {
    let body_fn = module.fn_by_id(fid);
    let np = body_fn.block(body_fn.entry).params.len();
    let key = crate::fz_ir::receive_outcome_spec_key(any, np);
    let lookup_key = spec_key_for_fn_id(module, fid, key);
    lookup_return_read(t, effective_returns, complete_returns, reads, lookup_key)
}

fn lookup_return_read<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    complete_returns: &SpecKeySet,
    reads: &mut Vec<SpecKey>,
    key: SpecKey,
) -> ReturnContribution {
    let dy = effective_returns
        .get(&key)
        .cloned()
        .unwrap_or_else(|| t.none());
    let complete = complete_returns.contains(&key);
    reads.push(key);
    ReturnContribution { ty: dy, complete }
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
/// activation-projected return facts for slot 0.
fn cont_key_for_spec<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    block: &Block,
    cont: &crate::fz_ir::Cont,
    ft: &SpecPlan,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    caller_spec_key: &SpecKey,
    activation_returns: &ActivationReturnFacts,
    slot_summaries: &FixedPointSlotSummaries,
) -> Option<Vec<crate::types::Ty>> {
    use crate::types::Ty;
    let Some(_) = module.fn_idx.get(&cont.fn_id) else {
        return Some(vec![]);
    };
    let any_t = t.any();
    let cont_fn = module.fn_by_id(cont.fn_id);
    let n_params = cont_fn.block(cont_fn.entry).params.len();

    let env = env_at_terminator(t, ft, block, module);
    let slot0: Ty = match &block.terminator {
        Term::Call { callee, args, .. } => {
            let direct_cid = block.terminator.ident().map(|ident| {
                crate::fz_ir::CallsiteId::new(
                    caller_spec_key.fn_id,
                    ident,
                    crate::fz_ir::EmitSlot::Direct,
                )
            });
            let arg_tys: Vec<Ty> = args
                .iter()
                .map(|av| env.get(av).cloned().unwrap_or_else(|| any_t.clone()))
                .collect();
            let target = direct_cid
                .as_ref()
                .and_then(|cid| ft.local_call_target(cid));
            let ident = block
                .terminator
                .ident()
                .expect("call terminator should carry ident");
            match direct_call_result_knowledge(
                t,
                module,
                recursive_fns,
                caller_spec_key,
                ident,
                *callee,
                &arg_tys,
                activation_returns,
                slot_summaries,
                target,
            )
            .slot0
            {
                ResultSlot0::Known(ty) => ty,
                ResultSlot0::Pending => return None,
            }
        }
        Term::CallClosure { closure, args, .. } => {
            let ident = block
                .terminator
                .ident()
                .expect("closure call terminator should carry ident");
            if let Some(target) = ft.known_fn(closure) {
                let ad: Vec<Ty> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| any_t.clone()))
                    .collect();
                match known_closure_result_knowledge(
                    t,
                    module,
                    recursive_fns,
                    caller_spec_key,
                    &ident,
                    target,
                    &ad,
                    activation_returns,
                    slot_summaries,
                )
                .slot0
                {
                    ResultSlot0::Known(ty) => ty,
                    ResultSlot0::Pending => return None,
                }
            } else if let Some(cv_descr) = env.get(closure) {
                let arg_tys: Vec<Ty> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| any_t.clone()))
                    .collect();
                match closure_value_result_knowledge(
                    t,
                    module,
                    recursive_fns,
                    caller_spec_key.fn_id,
                    cv_descr,
                    &arg_tys,
                    activation_returns,
                    slot_summaries,
                )
                .slot0
                {
                    ResultSlot0::Known(ty) => ty,
                    ResultSlot0::Pending => return None,
                }
            } else {
                any_t.clone()
            }
        }
        _ => any_t.clone(),
    };
    Some(normalize_result_correspondence_key(
        t,
        module,
        cont.fn_id,
        cont_key_from_slot0(&any_t, n_params, slot0, &cont.captured, &env),
    ))
}

fn external_call_return_slot0_for_spec<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    caller: FnId,
    ident: &crate::fz_ir::CallsiteIdent,
    callee: FnId,
    arg_tys: &[crate::types::Ty],
    activation_returns: &ActivationReturnFacts,
    owner_module: &str,
) -> Option<crate::types::Ty> {
    let callsite = crate::fz_ir::CallsiteId::new(caller, ident, crate::fz_ir::EmitSlot::Direct);
    module
        .external_call_edges
        .iter()
        .any(|edge| edge.callsite == callsite)
        .then(|| {
            declared_call_return_fact(
                t,
                module,
                &std::collections::HashSet::new(),
                &FixedPointSlotSummaries::new(),
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
fn declared_call_return_fact<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &FixedPointSlotSummaries,
    caller: FnId,
    callee: FnId,
    arg_tys: &[crate::types::Ty],
    activation_returns: &ActivationReturnFacts,
    owner_module: &str,
) -> Option<DeclaredReturnFact> {
    let spec_set = module.declared_specs.get(&callee)?;
    let application = crate::specs::apply_spec_set(
        t,
        spec_set,
        arg_tys,
        |t, query: crate::specs::CallbackReturnQuery<'_>| {
            declared_callback_return_fact(
                t,
                module,
                recursive_fns,
                slot_summaries,
                caller,
                activation_returns,
                query,
            )
        },
    );
    let mut fact = match application {
        crate::specs::SpecApplicationOutcome::Known(application) => DeclaredReturnFact {
            ty: (!t.has_vars(&application.result)).then_some(application.result),
        },
        crate::specs::SpecApplicationOutcome::Underconstrained(_application) => {
            DeclaredReturnFact { ty: None }
        }
        crate::specs::SpecApplicationOutcome::NoMatch => return None,
    };
    if let Some(ty) = fact.ty.take() {
        fact.ty = Some(t.mint_owned_resource_aliases(ty, owner_module, &module.opaque_inners));
    }
    Some(fact)
}

#[allow(clippy::too_many_arguments)]
fn declared_callback_return_fact<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &FixedPointSlotSummaries,
    caller: FnId,
    activation_returns: &ActivationReturnFacts,
    query: crate::specs::CallbackReturnQuery<'_>,
) -> Option<crate::specs::CallbackReturnFact<SpecKey>> {
    let fn_id: FnId = query.target.into();
    let target_fn = module.fn_by_id(fn_id);
    let n_params = target_fn.block(target_fn.entry).params.len();
    let mut full_key = query.captures.to_vec();
    full_key.extend_from_slice(query.args);
    let key = fixed_point_spec_key_for_arity(
        t,
        module,
        recursive_fns,
        slot_summaries,
        caller,
        fn_id,
        full_key,
        n_params,
        Some(callback_return_demand(query.demand)),
    );

    match activation_returns.result_slot0_for_key(t, &key) {
        ResultSlot0::Known(ret) => Some(crate::specs::CallbackReturnFact::Known {
            result: ret,
            read: key,
            complete: true,
        }),
        ResultSlot0::Pending => Some(crate::specs::CallbackReturnFact::Pending { read: key }),
    }
}

fn callback_return_demand(demand: crate::specs::CallbackReturnDemand) -> ReturnDemand {
    match demand {
        crate::specs::CallbackReturnDemand::Value => ReturnDemand::value(),
        crate::specs::CallbackReturnDemand::TupleFields(arity) => ReturnDemand::tuple_fields(arity),
    }
}
