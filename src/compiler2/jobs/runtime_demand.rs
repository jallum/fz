use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use super::super::body::{
    CallArg, CallInputMode, CallSiteId, ControlDestination, ControlEntryId, DeliveredValueSource, LoweredBody,
    LoweredEntry, LoweredStep, LoweredTail, ValueId, callsite_call_args, callsite_input_modes,
};
use super::super::callsite_dispatch::dispatch_stress;
use super::super::drive::{FactKey, JobEffects, settled_uses};
use super::super::executable_facts::{ExecutableFacts, LocalCallableProducer, RuntimeDemandFacts};
#[cfg(test)]
use super::super::executable_facts::{TransportOrigin, collect_callsite_return_origins, collect_value_origins};
use super::super::facts::FactUse;
use super::super::identity::{ExecutableKey, ExecutableNeed, FunctionId};
use super::super::incoming_inputs::{IncomingInputRole, IncomingInputSource, IncomingInputSources, InputSlot};
use super::super::scheduler::FatalError;
use super::super::semantic::{
    CallSiteSummary, CallableConstructionTargetKey, CallableDemand, CallableFlowEdge, CallableFlowFact,
    CallableSurface, CallableTarget, ExecutableRuntimeDemand, RuntimeDemand, SemanticOrd, ShapeDemand,
    TargetDemandContribution, ground_dispatch_surfaces,
};
use super::super::types::{Ty, Types};
use super::super::world::World;
use crate::telemetry::Telemetry;

#[cfg(test)]
thread_local! {
    static FORMULA_CAPTURE: std::cell::RefCell<Option<Vec<RuntimeDemandFormulaEvaluation>>> = const {
        std::cell::RefCell::new(None)
    };
}

#[cfg(test)]
pub(crate) struct RuntimeDemandFormulaCapture;

#[cfg(test)]
#[derive(Clone)]
pub(crate) struct RuntimeDemandFormulaEvaluation {
    pub(crate) member: ExecutableKey,
    pub(crate) demand: ExecutableRuntimeDemand,
    pub(crate) observed_return_contributions: Vec<(ExecutableKey, RuntimeDemand)>,
    pub(crate) contributions: HashMap<ExecutableKey, TargetDemandContribution>,
}

#[cfg(test)]
impl RuntimeDemandFormulaCapture {
    pub(crate) fn install() -> Self {
        FORMULA_CAPTURE.with(|capture| {
            assert!(
                capture.borrow().is_none(),
                "runtime-demand formula capture already installed"
            );
            *capture.borrow_mut() = Some(Vec::new());
        });
        Self
    }

    pub(crate) fn evaluations(&self) -> Vec<RuntimeDemandFormulaEvaluation> {
        FORMULA_CAPTURE.with(|capture| capture.borrow().as_ref().expect("formula capture installed").clone())
    }
}

#[cfg(test)]
impl Drop for RuntimeDemandFormulaCapture {
    fn drop(&mut self) {
        FORMULA_CAPTURE.with(|capture| *capture.borrow_mut() = None);
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct RuntimeDemandOwnInput {
    pub(crate) return_demand: RuntimeDemand,
    pub(crate) input_demands: Vec<RuntimeDemand>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct RuntimeDemandFormulaSnapshot {
    member: ExecutableKey,
    pub(crate) own: RuntimeDemandOwnInput,
    pub(crate) target_inputs: HashMap<ExecutableKey, Vec<RuntimeDemand>>,
    construction_targets: HashMap<(ValueId, CallableSurface), ExecutableKey>,
}

struct RuntimeDemandFormulaInput<'a> {
    member: &'a ExecutableKey,
    facts: RuntimeDemandFacts<'a>,
    current: RuntimeDemandFormulaSnapshot,
}

struct DerivedExecutableDemand {
    demand: ExecutableRuntimeDemand,
    call_return_demands: HashMap<CallSiteId, RuntimeDemand>,
    callable_flows: CallableFlowBuilder,
}

struct CallableFlowPlan {
    value: ValueId,
    producer: LocalCallableProducer,
    direct_surfaces: BTreeSet<CallableSurface>,
    direct_edges: Vec<CallableFlowEdge>,
    first_class_surfaces: BTreeSet<CallableSurface>,
    first_class_edges: Vec<CallableFlowEdge>,
    opaque: bool,
    escape: bool,
}

pub(super) fn derive_runtime_demand_fact<T: Telemetry>(
    world: &mut World,
    _tel: &T,
    executable: &ExecutableKey,
) -> Result<JobEffects, FatalError> {
    let executable_fact = FactKey::ExecutableFacts(executable.clone());
    if !world.fact_is_settled(&executable_fact) {
        return Ok(JobEffects {
            waits: settled_uses([executable_fact]),
            ..JobEffects::default()
        });
    }
    let facts = Rc::clone(
        world
            .executable_facts(executable)
            .expect("settled executable facts should have a value"),
    );
    let mut reads = vec![FactUse::current(executable_fact)];
    #[cfg(test)]
    let identity_inventory = world.types().identity_inventory();

    let input_fact = FactKey::RuntimeDemandInput(executable.clone());
    reads.push(FactUse::current(input_fact));
    let self_fact = FactKey::RuntimeDemand(executable.clone());
    let self_inputs_fact = FactKey::RuntimeDemandInputs(executable.clone());
    let contribution = world.runtime_demand_input(executable).cloned();
    let has_owner = contribution.is_some();
    let contribution = contribution.unwrap_or_default();
    let peer_keys = direct_local_targets(&facts);
    let mut ordered_peers = peer_keys.into_iter().collect::<Vec<_>>();
    ordered_peers.sort_by(|left, right| left.semantic_cmp(right, world.types()));
    let mut peers = HashMap::new();
    let mut peer_waits = Vec::new();
    for peer in ordered_peers.iter().cloned() {
        let fact = FactKey::RuntimeDemandInputs(peer.clone());
        reads.push(FactUse::current(fact.clone()));
        if let Some(demand) = world.runtime_demand_inputs(&peer) {
            peers.insert(peer, demand.to_vec());
        } else if peer != *executable {
            peer_waits.push(FactUse::current(fact));
        }
    }
    let own = RuntimeDemandOwnInput {
        return_demand: contribution.return_demand.unwrap_or_else(RuntimeDemand::ignore),
        input_demands: (0..executable.activation.input_len(world.types()))
            .map(|index| {
                contribution
                    .input_demands
                    .get(&index)
                    .cloned()
                    .unwrap_or_else(RuntimeDemand::ignore)
            })
            .collect(),
    };
    let mut input =
        RuntimeDemandFormulaInput::new(executable, &facts, world.runtime_demand_type_projections(), own, &peers);
    let mut loaded_target_demands = ordered_peers.into_iter().collect::<HashSet<_>>();
    let mut callable_target_reads = HashSet::new();
    let (mut derived, plans, unresolved_construction_targets, missing_target_demands) = loop {
        let derived = derive_executable_runtime_demand(world.types(), &input);
        let (plans, requested, unresolved) =
            plan_callable_flows(world, &input, &derived.callable_flows, &derived.demand);
        callable_target_reads.extend(requested);
        let mut input_grew = false;
        for plan in &plans {
            for edge in &plan.first_class_edges {
                let target = (plan.value, edge.surface.clone());
                match input
                    .current
                    .construction_targets
                    .insert(target, edge.resolution.clone())
                {
                    None => input_grew = true,
                    Some(previous) => assert_eq!(
                        previous, edge.resolution,
                        "one construction value and surface must resolve to one exact target"
                    ),
                }
            }
        }
        if input_grew {
            continue;
        }
        let mut missing_target_demands = HashSet::new();
        let mut exact_targets = plans
            .iter()
            .flat_map(|plan| plan.direct_edges.iter().chain(&plan.first_class_edges))
            .map(|edge| edge.resolution.clone())
            .collect::<Vec<_>>();
        exact_targets.sort_by(|left, right| left.semantic_cmp(right, world.types()));
        exact_targets.dedup();
        for target in exact_targets {
            if loaded_target_demands.insert(target.clone()) {
                let fact = FactKey::RuntimeDemandInputs(target.clone());
                reads.push(FactUse::current(fact));
                if let Some(demand) = world.runtime_demand_inputs(&target) {
                    input.current.target_inputs.insert(target, demand.to_vec());
                    input_grew = true;
                } else if target != *executable {
                    missing_target_demands.insert(target);
                }
            } else if !input.current.target_inputs.contains_key(&target) && target != *executable {
                missing_target_demands.insert(target);
            }
        }
        if input_grew {
            continue;
        }
        break (derived, plans, unresolved, missing_target_demands);
    };
    let return_contributions = call_return_demand_contributions(&input.facts, derived.call_return_demands);
    #[cfg(test)]
    let observed_return_contributions = return_contributions.clone();
    for key in &callable_target_reads {
        let fact = FactKey::CallableConstructionTarget(key.clone());
        reads.push(FactUse::current(fact.clone()));
        if unresolved_construction_targets.contains(key) {
            peer_waits.push(FactUse::current(fact));
        }
    }
    peer_waits.extend(
        missing_target_demands
            .into_iter()
            .map(|target| FactUse::current(FactKey::RuntimeDemandInputs(target))),
    );
    finish_callable_flows(plans, &mut derived.demand);
    let retained_returns = derived
        .demand
        .callable_flows
        .values()
        .flat_map(|flow| &flow.first_class_edges)
        .map(|edge| edge.resolution.clone())
        .collect::<Vec<_>>();
    let provisional_contributions =
        target_return_demand_contributions(return_contributions.clone(), retained_returns.iter().cloned());
    let mut contributions = target_return_demand_contributions(return_contributions, retained_returns);
    for (target, index, demand) in callable_boundary_input_demand_contributions_product(&derived.demand) {
        contributions
            .entry(target)
            .or_default()
            .input_demands
            .entry(index)
            .and_modify(|current| current.join_assign(&demand))
            .or_insert(demand);
    }
    derived.demand.ground_callable_surfaces(world.types());
    #[cfg(test)]
    assert_eq!(
        world.types().identity_inventory(),
        identity_inventory,
        "one RuntimeDemand formula evaluation must not mint types or structural addresses"
    );
    #[cfg(test)]
    FORMULA_CAPTURE.with(|capture| {
        let mut capture = capture.borrow_mut();
        let Some(evaluations) = capture.as_mut() else {
            return;
        };
        let evaluation = RuntimeDemandFormulaEvaluation {
            member: executable.clone(),
            demand: derived.demand.clone(),
            observed_return_contributions,
            contributions: contributions.clone(),
        };
        if let Some(previous) = evaluations
            .iter_mut()
            .find(|previous| previous.member == evaluation.member)
        {
            *previous = evaluation;
        } else {
            evaluations.push(evaluation);
        }
    });
    let demand = derived.demand;
    let runtime_demand_input_contributions = if !has_owner {
        Vec::new()
    } else if peer_waits.is_empty() && unresolved_construction_targets.is_empty() {
        contributions.into_iter().collect()
    } else {
        provisional_contributions.into_iter().collect()
    };
    let mut incoming = HashMap::new();
    if has_owner {
        collect_callsite_input_sources(world, executable, &facts, &mut incoming);
        collect_callable_capture_input_sources(executable, &demand, &mut incoming);
    }
    for semantic_index in 0..executable.activation.input_len(world.types()) {
        incoming
            .entry(InputSlot {
                executable: executable.clone(),
                semantic_index,
            })
            .or_default();
    }
    let incoming_input_contributions = incoming
        .into_iter()
        .map(|(slot, sources)| (slot, IncomingInputSources::new(sources, world.types())))
        .collect();
    let demand = Rc::new(demand);
    let (changed, inputs_changed) = world.define_runtime_demand(executable.clone(), demand);
    Ok(JobEffects {
        reads,
        outputs: vec![self_fact.clone(), self_inputs_fact.clone()],
        changed: changed
            .then_some(self_fact)
            .into_iter()
            .chain(inputs_changed.then_some(self_inputs_fact))
            .collect(),
        waits: peer_waits,
        runtime_demand_input_contributions,
        incoming_input_contributions,
        ..JobEffects::default()
    })
}

fn target_return_demand_contributions(
    observed: impl IntoIterator<Item = (ExecutableKey, RuntimeDemand)>,
    retained: impl IntoIterator<Item = ExecutableKey>,
) -> HashMap<ExecutableKey, TargetDemandContribution> {
    let mut contributions = HashMap::<ExecutableKey, TargetDemandContribution>::new();
    let mut join = |target: ExecutableKey, demand: RuntimeDemand| {
        let contribution = contributions.entry(target).or_default();
        match &mut contribution.return_demand {
            Some(current) => current.join_assign(&demand),
            None => contribution.return_demand = Some(demand),
        }
    };
    for (target, demand) in observed {
        join(target, demand);
    }
    for target in retained {
        let demand = RuntimeDemand::for_executable_need(target.need);
        join(target, demand);
    }
    contributions
}

fn trivial_value_clause_ids(body: &LoweredBody, reachable: &[u32]) -> Vec<u32> {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return Vec::new();
    };
    (0..clauses.len() as u32)
        .filter(|clause_id| !reachable.contains(clause_id))
        .filter(|clause_id| {
            let clause = &clauses[*clause_id as usize];
            let entry = &entries[clause.entry.as_u32() as usize];
            entry.steps.is_empty() && matches!(entry.tail, LoweredTail::Value { .. })
        })
        .collect()
}

#[derive(Debug, Clone, Default)]
struct CallableFlowBuilder {
    direct_surfaces: HashMap<ValueId, BTreeSet<CallableSurface>>,
    direct_targets: HashMap<ValueId, BTreeSet<CallableTarget>>,
    first_class_surfaces: HashMap<ValueId, BTreeSet<CallableSurface>>,
}

impl CallableFlowBuilder {
    fn new() -> Self {
        Self::default()
    }

    fn direct_surfaces(&self, value: ValueId) -> BTreeSet<CallableSurface> {
        self.direct_surfaces.get(&value).cloned().unwrap_or_default()
    }

    fn first_class_surfaces(&self, value: ValueId) -> BTreeSet<CallableSurface> {
        self.first_class_surfaces.get(&value).cloned().unwrap_or_default()
    }

    fn direct_targets(&self, value: ValueId) -> BTreeSet<CallableTarget> {
        self.direct_targets.get(&value).cloned().unwrap_or_default()
    }

    fn record_direct_demand(&mut self, facts: &RuntimeDemandFacts<'_>, value: ValueId, demand: &RuntimeDemand) {
        self.record_direct_surfaces(facts, value, &demand.callable.resolved);
        let targets = &demand.callable.targets;
        if !targets.is_empty() {
            let mut seen = HashSet::new();
            self.record_direct_targets_for_value(facts, value, targets, &mut seen);
        }
    }

    fn record_direct_surfaces(
        &mut self,
        facts: &RuntimeDemandFacts<'_>,
        value: ValueId,
        surfaces: &BTreeSet<CallableSurface>,
    ) {
        if surfaces.is_empty() {
            return;
        }
        let mut seen = HashSet::new();
        self.record_direct_surfaces_for_value(facts, value, surfaces, &mut seen);
    }

    fn record_first_class_demand(&mut self, facts: &RuntimeDemandFacts<'_>, value: ValueId, demand: &RuntimeDemand) {
        if demand.callable.is_first_class() {
            self.record_first_class_surfaces(facts, value, &demand.callable.resolved);
        }
    }

    fn record_first_class_surfaces(
        &mut self,
        facts: &RuntimeDemandFacts<'_>,
        value: ValueId,
        surfaces: &BTreeSet<CallableSurface>,
    ) {
        if surfaces.is_empty() {
            return;
        }
        let mut seen = HashSet::new();
        self.record_first_class_surfaces_for_value(facts, value, surfaces, &mut seen);
    }

    fn record_direct_surfaces_for_value(
        &mut self,
        facts: &RuntimeDemandFacts<'_>,
        value: ValueId,
        surfaces: &BTreeSet<CallableSurface>,
        seen: &mut HashSet<ValueId>,
    ) {
        if !seen.insert(value) {
            return;
        }
        if facts.callable_origin(value).is_some() {
            self.direct_surfaces
                .entry(value)
                .or_default()
                .extend(surfaces.iter().cloned());
        }
        for join in facts.delivered_value_joins.values().filter(|join| join.value == value) {
            for source in &join.sources {
                let DeliveredValueSource::LocalValue(source) = source else {
                    continue;
                };
                self.record_direct_surfaces_for_value(facts, *source, surfaces, seen);
            }
        }
    }

    fn record_first_class_surfaces_for_value(
        &mut self,
        facts: &RuntimeDemandFacts<'_>,
        value: ValueId,
        surfaces: &BTreeSet<CallableSurface>,
        seen: &mut HashSet<ValueId>,
    ) {
        if !seen.insert(value) {
            return;
        }
        if facts.callable_origin(value).is_some() {
            self.first_class_surfaces
                .entry(value)
                .or_default()
                .extend(surfaces.iter().cloned());
        }
        for join in facts.delivered_value_joins.values().filter(|join| join.value == value) {
            for source in &join.sources {
                let DeliveredValueSource::LocalValue(source) = source else {
                    continue;
                };
                self.record_first_class_surfaces_for_value(facts, *source, surfaces, seen);
            }
        }
    }

    fn record_direct_targets_for_value(
        &mut self,
        facts: &RuntimeDemandFacts<'_>,
        value: ValueId,
        targets: &BTreeSet<CallableTarget>,
        seen: &mut HashSet<ValueId>,
    ) {
        if !seen.insert(value) {
            return;
        }
        if facts.callable_origin(value).is_some() {
            self.direct_targets
                .entry(value)
                .or_default()
                .extend(targets.iter().cloned());
        }
        for join in facts.delivered_value_joins.values().filter(|join| join.value == value) {
            for source in &join.sources {
                let DeliveredValueSource::LocalValue(source) = source else {
                    continue;
                };
                self.record_direct_targets_for_value(facts, *source, targets, seen);
            }
        }
    }
}

impl<'a> RuntimeDemandFormulaInput<'a> {
    fn new(
        member: &'a ExecutableKey,
        facts: &'a ExecutableFacts,
        type_projections: &'a HashMap<Ty, Rc<super::super::semantic::RuntimeDemandTypeProjection>>,
        own: RuntimeDemandOwnInput,
        reads: &HashMap<ExecutableKey, Vec<RuntimeDemand>>,
    ) -> Self {
        Self {
            current: RuntimeDemandFormulaSnapshot::new(member.clone(), own, reads),
            member,
            facts: facts.runtime_demand_facts(type_projections),
        }
    }
}

impl RuntimeDemandFormulaSnapshot {
    fn new(
        member: ExecutableKey,
        own: RuntimeDemandOwnInput,
        reads: &HashMap<ExecutableKey, Vec<RuntimeDemand>>,
    ) -> Self {
        Self {
            member,
            own,
            target_inputs: reads.clone(),
            construction_targets: HashMap::new(),
        }
    }
}

fn construction_flow_edge(
    world: &World,
    input: &RuntimeDemandFormulaInput<'_>,
    key: &CallableConstructionTargetKey,
    producer: &LocalCallableProducer,
    surface: &CallableSurface,
) -> Option<CallableFlowEdge> {
    let facts = &input.facts;
    let Some(capture_tys) = producer
        .captures
        .iter()
        .map(|capture| facts.value_types.get(capture).copied())
        .collect::<Option<Vec<_>>>()
    else {
        panic!("settled callable producer has no capture types: {producer:?}");
    };
    let resolution = world.callable_construction_target(key)?.clone();
    let resolution = ExecutableKey {
        activation: resolution.activation,
        need: ExecutableNeed::Value,
    };
    let input_len = capture_tys.len() + surface.inputs.len();
    Some(CallableFlowEdge {
        surface: surface.clone(),
        resolution,
        capture_semantic_inputs: (0..capture_tys.len()).collect(),
        surface_semantic_inputs: (capture_tys.len()..input_len).collect(),
        boundary_input_demands: surface
            .inputs
            .iter()
            .map(|&ty| {
                if ty == facts.demand_types.any {
                    return None;
                }
                world
                    .runtime_demand_type_projection(ty)
                    .unwrap_or_else(|| panic!("callable surface omitted runtime-demand projection for {ty:?}"))
                    .informative_boundary_demand(world.types(), ty)
            })
            .collect(),
    })
}

fn collect_callsite_input_sources(
    world: &World,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    contribution: &mut HashMap<InputSlot, HashSet<IncomingInputSource>>,
) {
    let call_args = callsite_call_args(&facts.body);
    let call_modes = callsite_input_modes(&facts.body);
    for (callsite, summary) in &facts.callsites {
        let Some(args) = call_args.get(callsite) else {
            continue;
        };
        let Some(mode) = call_modes.get(callsite).copied() else {
            continue;
        };
        let need = facts
            .callsite_needs
            .get(callsite)
            .copied()
            .unwrap_or(ExecutableNeed::Value);
        for target in &summary.targets {
            let Some(callee) = target.runtime_executable(need) else {
                continue;
            };
            for (index, arg) in args.iter().enumerate() {
                let Some(semantic_index) =
                    mode.semantic_index(callee.activation.input_len(world.types()), args.len(), index)
                else {
                    continue;
                };
                contribution
                    .entry(InputSlot {
                        executable: callee.clone(),
                        semantic_index,
                    })
                    .or_default()
                    .insert(IncomingInputSource {
                        producer: executable.clone(),
                        value: arg.value,
                        role: IncomingInputRole::CallArgument,
                    });
            }
        }
    }
}

fn collect_callable_capture_input_sources(
    executable: &ExecutableKey,
    demand: &ExecutableRuntimeDemand,
    contribution: &mut HashMap<InputSlot, HashSet<IncomingInputSource>>,
) {
    for (&flow_value, flow) in &demand.callable_flows {
        for edge in flow.direct_edges.iter().chain(&flow.first_class_edges) {
            for (capture_index, (&semantic_index, value)) in edge
                .capture_semantic_inputs
                .iter()
                .zip(flow.captures.iter().copied())
                .enumerate()
            {
                contribution
                    .entry(InputSlot {
                        executable: edge.resolution.clone(),
                        semantic_index,
                    })
                    .or_default()
                    .insert(IncomingInputSource {
                        producer: executable.clone(),
                        value,
                        role: IncomingInputRole::CallableCapture {
                            construction: flow_value,
                            capture_index,
                        },
                    });
            }
        }
    }
}

fn direct_local_targets(facts: &ExecutableFacts) -> HashSet<ExecutableKey> {
    let mut targets = HashSet::new();
    for (callsite, summary) in &facts.callsites {
        let need = facts
            .callsite_needs
            .get(callsite)
            .copied()
            .unwrap_or(ExecutableNeed::Value);
        targets.extend(local_call_targets(summary, need));
    }
    targets
}

fn call_return_demand_contributions(
    facts: &RuntimeDemandFacts<'_>,
    observed_returns: HashMap<CallSiteId, RuntimeDemand>,
) -> Vec<(ExecutableKey, RuntimeDemand)> {
    // A caller's contribution names EVERY local callee it calls, including the
    // ones whose return it discards -- so the iteration is over the static call
    // graph (`facts.callsites`), not the lossy `observed_returns` (which omits a
    // callsite entirely once its demand collapses to `ignore`). A discarded
    // callee contributes the bottom `ignore` demand: a distinct cell from "no
    // caller has named this callee at all". Both absence and an explicit
    // discarded-callee contribution are bottom demand; publisher identity is
    // retained only where exact replacement and retraction need it.
    let mut out = Vec::new();
    for (callsite, summary) in facts.callsites {
        let need = facts
            .callsite_needs
            .get(callsite)
            .copied()
            .unwrap_or(ExecutableNeed::Value);
        let observed = observed_returns
            .get(callsite)
            .cloned()
            .unwrap_or_else(RuntimeDemand::ignore);
        let delivered = match need {
            // Destination-passing delivery writes fields into the caller frame,
            // so its slots are retained even when a field is ignored.
            ExecutableNeed::TupleFields(_) => tuple_return_demand_for_observed_need(need, observed),
            ExecutableNeed::Value => observed,
        };
        for target in local_call_targets(summary, need) {
            out.push((target, delivered.clone()));
        }
    }
    out
}

fn tuple_return_demand_for_observed_need(need: ExecutableNeed, observed: RuntimeDemand) -> RuntimeDemand {
    let mut delivered = RuntimeDemand::for_executable_need(need);
    if let (ShapeDemand::TupleFields(delivered_fields), ShapeDemand::TupleFields(observed_fields)) =
        (&mut delivered.shape, observed.shape)
    {
        for (delivered_field, observed_field) in delivered_fields.iter_mut().zip(observed_fields) {
            delivered_field.join_assign(&observed_field);
        }
    }
    delivered.callable.join_assign(&observed.callable);
    delivered
}

fn plan_callable_flows(
    world: &World,
    input: &RuntimeDemandFormulaInput,
    callable_flows: &CallableFlowBuilder,
    demand: &ExecutableRuntimeDemand,
) -> (
    Vec<CallableFlowPlan>,
    HashSet<CallableConstructionTargetKey>,
    HashSet<CallableConstructionTargetKey>,
) {
    let executable = input.member;
    let facts = &input.facts;
    let mut plans = Vec::new();
    let mut requested = HashSet::new();
    let mut unresolved = HashSet::new();
    for (&value, producer) in facts.callable_origins() {
        let Some(value_demand) = demand.value_demands.get(&value) else {
            continue;
        };
        if !value_demand.is_callable() {
            continue;
        }
        let (direct_surfaces, direct_edges, first_class_surfaces, ordered) = {
            let types = world.types();
            let direct_surfaces = callable_flows.direct_surfaces(value);
            let direct_targets = callable_flows.direct_targets(value);
            let producer_surfaces = callable_value_type_demand(facts, value)
                .map(|demand| demand.callable.resolved)
                .unwrap_or_default();
            let direct_edges = callable_flow_edges_for_targets(
                types,
                executable,
                facts,
                producer.function,
                &producer.captures,
                &direct_targets,
            );
            let mut ground_source = producer_surfaces;
            ground_source.extend(direct_surfaces.iter().cloned());
            let first_class_surfaces =
                ground_dispatch_surfaces(types, &callable_flows.first_class_surfaces(value), &ground_source);
            let mut ordered = first_class_surfaces.iter().cloned().collect::<Vec<_>>();
            ordered.sort_by(|a, b| types.cmp_activation_tys(&a.inputs, &b.inputs));
            (direct_surfaces, direct_edges, first_class_surfaces, ordered)
        };
        let first_class_edges = ordered
            .iter()
            .filter_map(|surface| {
                let key = CallableConstructionTargetKey {
                    owner: executable.clone(),
                    value,
                    surface: surface.clone(),
                };
                requested.insert(key.clone());
                let edge = construction_flow_edge(world, input, &key, producer, surface);
                if edge.is_none() {
                    unresolved.insert(key);
                }
                edge
            })
            .collect();
        plans.push(CallableFlowPlan {
            value,
            producer: producer.clone(),
            direct_surfaces,
            direct_edges,
            first_class_surfaces,
            first_class_edges,
            opaque: value_demand.callable.opaque,
            escape: value_demand.callable.escape,
        });
    }
    (plans, requested, unresolved)
}

fn callable_flow_edges_for_targets(
    types: &Types,
    executable: &ExecutableKey,
    facts: &RuntimeDemandFacts<'_>,
    function: FunctionId,
    captures: &[ValueId],
    targets: &BTreeSet<CallableTarget>,
) -> Vec<CallableFlowEdge> {
    if targets.is_empty() {
        return Vec::new();
    }
    let Some(capture_tys) = captures
        .iter()
        .map(|capture| facts.value_types.get(capture).copied())
        .collect::<Option<Vec<_>>>()
    else {
        return Vec::new();
    };
    let captures_len = capture_tys.len();
    let mut edges = targets
        .iter()
        .filter(|target| target.activation.root == executable.activation.root && target.activation.function == function)
        .filter(|target| {
            target.activation_inputs.len() == captures_len + target.surface.inputs.len()
                && target
                    .activation_inputs
                    .iter()
                    .zip(&capture_tys)
                    .all(|(target, capture)| types.is_equivalent(target, capture))
        })
        .map(|target| CallableFlowEdge {
            surface: target.surface.clone(),
            resolution: ExecutableKey {
                activation: target.activation.clone(),
                need: target.need,
            },
            capture_semantic_inputs: (0..captures_len).collect(),
            surface_semantic_inputs: (captures_len..captures_len + target.surface.inputs.len()).collect(),
            boundary_input_demands: Box::new([]),
        })
        .collect::<Vec<_>>();
    // `targets` is a `BTreeSet<CallableTarget>` ordered by interned-`Ty` id, so
    // walking it leaks the interner's mint order (the agenda's) into this
    // executable's stored `direct_edges` and every artifact rendered from them.
    // Order by what each surface says, the same typed activation key the first-class
    // edges use, so the direct half is canonical for the same reason and by the
    // same authority (fz-kdt.108).
    edges.sort_by(|a, b| types.cmp_activation_tys(&a.surface.inputs, &b.surface.inputs));
    edges
}

fn callable_boundary_input_demand_contributions_product(
    demand: &ExecutableRuntimeDemand,
) -> Vec<(ExecutableKey, usize, RuntimeDemand)> {
    let mut required = Vec::new();
    for flow in demand.callable_flows.values() {
        for edge in flow.direct_edges.iter().chain(&flow.first_class_edges) {
            for (&semantic_index, capture) in edge.capture_semantic_inputs.iter().zip(flow.captures.iter()) {
                let Some(capture_demand) = demand.value_demands.get(capture) else {
                    continue;
                };
                required.push((edge.resolution.clone(), semantic_index, capture_demand.clone()));
            }
        }
        if flow.first_class_surfaces.is_empty() {
            continue;
        }
        for edge in &flow.first_class_edges {
            for (offset, arg_demand) in edge.boundary_input_demands.iter().enumerate() {
                let Some(arg_demand) = arg_demand else {
                    continue;
                };
                required.push((
                    edge.resolution.clone(),
                    edge.capture_semantic_inputs.len() + offset,
                    arg_demand.clone(),
                ));
            }
        }
    }
    required
}

fn local_call_targets(summary: &CallSiteSummary, need: ExecutableNeed) -> Vec<ExecutableKey> {
    summary
        .targets
        .iter()
        .filter_map(|target| target.runtime_executable(need))
        .collect()
}

fn join_contributed_input_demands(input_demands: &mut [RuntimeDemand], contributed: &[RuntimeDemand]) {
    for (slot, contribution) in input_demands.iter_mut().zip(contributed) {
        slot.join_assign(contribution);
    }
}

fn derive_executable_runtime_demand(types: &Types, input: &RuntimeDemandFormulaInput) -> DerivedExecutableDemand {
    let executable = &input.member;
    let facts = &input.facts;
    let demands = &input.current;
    let mut callable_flows = CallableFlowBuilder::new();
    let contributed_input_demands = demands.own.input_demands.as_slice();
    let mut out = ExecutableRuntimeDemand {
        callable_activation_inputs: facts.callable_activation_inputs.to_vec(),
        return_demand: demands.own.return_demand.clone(),
        input_demands: vec![RuntimeDemand::ignore(); executable.activation.input_len(types)],
        ..ExecutableRuntimeDemand::default()
    };
    let mut call_return_demands = HashMap::new();

    let LoweredBody::Clauses { clauses, entries, .. } = &facts.body else {
        out.input_demands = match &facts.body {
            LoweredBody::Extern { signature } => executable
                .activation
                .inputs(types)
                .iter()
                .enumerate()
                .map(|(index, ty)| {
                    signature
                        .params
                        .get(index)
                        .map(|_| RuntimeDemand::whole())
                        .unwrap_or_else(|| facts.boundary_demand(*ty))
                })
                .collect(),
            LoweredBody::Clauses { .. } => unreachable!(),
        };
        join_contributed_input_demands(&mut out.input_demands, contributed_input_demands);
        return DerivedExecutableDemand {
            demand: out,
            call_return_demands,
            callable_flows: CallableFlowBuilder::new(),
        };
    };

    // Live-demand propagation is the authoritative "what must be
    // Codegen lowers every structural clause regardless of
    // the settled entry reachability, so a clause the type-level reachability
    // analysis under-approximates as dead (e.g. a recursive base case whose
    // list slot is over-narrowed) can still reach native lowering and crash
    // when its return value was never marked live. Widen the walked clause
    // set by the trivial delta `trivial_value_clause_ids` identifies.
    let mut walked_clauses = facts.reachable_clauses.to_vec();
    walked_clauses.extend(trivial_value_clause_ids(facts.body, facts.reachable_clauses));
    for clause_id in walked_clauses {
        let clause = &clauses[clause_id as usize];
        let mut live = collect_entry_live_demands(
            types,
            executable,
            entries.as_slice(),
            clause.entry,
            out.return_demand.clone(),
            facts,
            demands,
            &mut out,
            &mut call_return_demands,
            &mut callable_flows,
        );
        propagate_steps_reverse(
            types,
            clause.projections.as_slice(),
            &mut live,
            facts,
            demands,
            &mut out,
            &mut callable_flows,
        );
        note_clause_matcher_demands(facts, clause.projections.as_slice(), &mut live, &mut out);
        for (index, param) in clause.params.iter().enumerate() {
            if let Some(demand) = live.remove(param) {
                out.input_demands[index].join_assign(&demand);
            }
        }
    }

    let activation_inputs = executable.activation.inputs(types);
    for &semantic_index in facts.entry_dispatch_inputs {
        let Some(&ty) = activation_inputs.get(semantic_index) else {
            continue;
        };
        let demand = facts.dispatch_demand(ty);
        out.input_demands[semantic_index].join_assign(&demand);
    }

    join_contributed_input_demands(&mut out.input_demands, contributed_input_demands);
    widen_boxed_closure_call_results(facts, &mut out);

    DerivedExecutableDemand {
        demand: out,
        call_return_demands,
        callable_flows,
    }
}

/// The consumer half of the boxed apply seam's one return convention
/// (fz-kdt.155). Its producer half is the construction owner's exact
/// executable-need contribution to every first-class member; here every
/// callsite that reaches a wrapper is made to expect the lane the wrapper
/// hands back.
///
/// The question "does this call go through the seam?" is a property of the
/// CALLEE VALUE, not of the callsite: `materialize_closure_call_edge` lowers a
/// direct edge to a named target only while the callee travels in its exact
/// carrier, and that carrier is `ValueRef` the moment the value's own joined
/// demand is first-class -- which a use somewhere else in this body can decide
/// on its own. A callsite that names an exact target is still a boxed call if
/// the lambda it calls is also handed out of the function two lines later. So
/// this runs once the whole body is walked and asks the joined value demand,
/// the same authority transport asks.
///
/// A callsite past the seam names none of the members behind the wrapper -- a
/// mailbox callable names none at all -- so its `ignore` never reaches them and
/// the value arrives whatever the caller wanted. Publishing zero lanes for it
/// left the two halves of one calling convention on different lane counts: the
/// wrapper wrote the delivered value into the continuation's first slot, which
/// the continuation reads as its own closure pointer, and the run aborted in
/// `fz_closure_get_capture_atom`. Every RICHER demand already crosses the seam
/// as that one boxed lane, so only the zero widens.
///
/// A callee that stays in its exact carrier is untouched: its result aliases
/// the named target executable's own return fact
/// (`TransportRecipe::ClosureCallReturn`'s grounded arm), so caller and callee
/// read one shape whatever it settles to -- zero when no seam boxes the
/// callable (fz-f98.14.11), non-empty when a construction owner contributes
/// the member's return contract.
fn widen_boxed_closure_call_results(facts: &RuntimeDemandFacts<'_>, out: &mut ExecutableRuntimeDemand) {
    let LoweredBody::Clauses { entries, .. } = &facts.body else {
        return;
    };
    for entry in entries {
        let LoweredTail::ClosureCall { value, callee, .. } = &entry.tail else {
            continue;
        };
        if !out
            .value_demands
            .get(callee)
            .is_some_and(|demand| demand.callable.is_first_class())
        {
            continue;
        }
        // Only the ZERO delivered value widens. The callsite's observed target
        // demand stays exact; the construction owner contributes the member's
        // executable-need contract independently.
        if !out.value_demands.get(value).is_none_or(RuntimeDemand::is_ignore) {
            continue;
        }
        join_map_demand(&mut out.value_demands, *value, RuntimeDemand::whole());
    }
}

fn collect_entry_external_demands(
    types: &Types,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    entry_id: ControlEntryId,
    outgoing_demand: RuntimeDemand,
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    callable_flows: &mut CallableFlowBuilder,
) -> HashMap<ValueId, RuntimeDemand> {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut live = collect_entry_live_demands(
        types,
        executable,
        entries,
        entry_id,
        outgoing_demand,
        facts,
        demands,
        out,
        call_return_demands,
        callable_flows,
    );
    let mut external = HashMap::new();
    if let Some(value) = entry.origin.input_value()
        && let Some(demand) = live.remove(&value)
    {
        let demand = upgrade_joined_delivered_callable_value_demand(facts, callable_flows, entry_id, value, demand);
        record_delivered_call_return_demands(facts, call_return_demands, entry_id, value, &demand);
        join_map_demand(&mut out.value_demands, value, demand.clone());
        external.insert(value, demand);
    }
    let capture_demands = entry
        .captures
        .iter()
        .map(|capture| {
            let demand = live.remove(capture).unwrap_or(RuntimeDemand::ignore());
            continuation_capture_demand(facts, callable_flows, *capture, demand)
        })
        .collect::<Vec<_>>();
    record_entry_capture_demands(out, entry_id, &capture_demands);
    for (capture, demand) in entry.captures.iter().zip(capture_demands) {
        if !demand.is_ignore() {
            join_map_demand(&mut external, *capture, demand);
        }
    }
    for param in &entry.params {
        live.remove(param);
    }
    merge_live_demands(&mut external, live);
    external
}

fn collect_entry_live_demands(
    types: &Types,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    entry_id: ControlEntryId,
    outgoing_demand: RuntimeDemand,
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    callable_flows: &mut CallableFlowBuilder,
) -> HashMap<ValueId, RuntimeDemand> {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut live = HashMap::new();
    let mut tail_call_return = None;
    match &entry.tail {
        LoweredTail::Value { value, dest } => {
            let (boundary_demand, external_demands) = destination_demands(
                types,
                executable,
                entries,
                dest,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
                callable_flows,
            );
            let demand = boundary_value_flow_demand(facts, callable_flows, *value, boundary_demand);
            note_live_demand(out, &mut live, *value, demand);
            merge_live_demands(&mut live, external_demands);
        }
        LoweredTail::DirectCall {
            value,
            callsite,
            args,
            dest,
            ..
        } => {
            let (boundary_demand, external_demands) = destination_demands(
                types,
                executable,
                entries,
                dest,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
                callable_flows,
            );
            let demand = boundary_value_flow_demand(facts, callable_flows, *value, boundary_demand);
            note_live_demand(out, &mut live, *value, demand.clone());
            record_call_return_demand(call_return_demands, *callsite, demand);
            tail_call_return = Some((*callsite, *value));
            merge_live_demands(&mut live, external_demands);
            let arg_demands = direct_call_arg_demands(
                types,
                executable,
                *callsite,
                args.as_slice(),
                facts,
                demands,
                callable_flows,
            );
            record_call_arg_demands(out, *callsite, arg_demands.as_slice());
            for (arg, demand) in args.iter().zip(arg_demands) {
                note_live_demand(out, &mut live, arg.value, demand);
            }
        }
        LoweredTail::ClosureCall {
            value,
            callsite,
            callee,
            args,
            dest,
            ..
        } => {
            let (boundary_demand, external_demands) = destination_demands(
                types,
                executable,
                entries,
                dest,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
                callable_flows,
            );
            let demand = boundary_value_flow_demand(facts, callable_flows, *value, boundary_demand);
            note_live_demand(out, &mut live, *value, demand.clone());
            record_call_return_demand(call_return_demands, *callsite, demand);
            tail_call_return = Some((*callsite, *value));
            merge_live_demands(&mut live, external_demands);
            let callee_callable = closure_callee_demand(
                facts,
                args.as_slice(),
                facts.callsites.get(callsite),
                facts
                    .callsite_needs
                    .get(callsite)
                    .copied()
                    .unwrap_or(ExecutableNeed::Value),
            );
            let callee_demand = RuntimeDemand::callable(callee_callable);
            callable_flows.record_direct_demand(facts, *callee, &callee_demand);
            note_live_demand(out, &mut live, *callee, callee_demand);
            let arg_demands = closure_call_arg_demands(
                types,
                executable,
                *callsite,
                args.as_slice(),
                facts,
                demands,
                callable_flows,
            );
            record_call_arg_demands(out, *callsite, arg_demands.as_slice());
            for (arg, demand) in args.iter().zip(arg_demands) {
                note_live_demand(out, &mut live, arg.value, demand);
            }
        }
        LoweredTail::If {
            cond,
            then_entry,
            else_entry,
        } => {
            note_live_demand(out, &mut live, *cond, RuntimeDemand::whole());
            merge_live_demands(
                &mut live,
                collect_entry_external_demands(
                    types,
                    executable,
                    entries,
                    *then_entry,
                    outgoing_demand.clone(),
                    facts,
                    demands,
                    out,
                    call_return_demands,
                    callable_flows,
                ),
            );
            merge_live_demands(
                &mut live,
                collect_entry_external_demands(
                    types,
                    executable,
                    entries,
                    *else_entry,
                    outgoing_demand,
                    facts,
                    demands,
                    out,
                    call_return_demands,
                    callable_flows,
                ),
            );
        }
        LoweredTail::Dispatch {
            inputs,
            bindings,
            dispatch,
        } => {
            for input in inputs {
                note_live_demand(out, &mut live, *input, RuntimeDemand::whole());
            }
            for value in bindings.pinned.iter().chain(bindings.prepared.iter()) {
                note_live_demand(out, &mut live, *value, RuntimeDemand::whole());
            }
            for arm_entry in &dispatch.arm_entries {
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        types,
                        executable,
                        entries,
                        *arm_entry,
                        outgoing_demand.clone(),
                        facts,
                        demands,
                        out,
                        call_return_demands,
                        callable_flows,
                    ),
                );
            }
            merge_live_demands(
                &mut live,
                collect_entry_external_demands(
                    types,
                    executable,
                    entries,
                    dispatch.miss_entry,
                    outgoing_demand,
                    facts,
                    demands,
                    out,
                    call_return_demands,
                    callable_flows,
                ),
            );
        }
        LoweredTail::Receive(receive) => {
            for value in receive.bindings.pinned.iter().chain(receive.bindings.prepared.iter()) {
                note_live_demand(out, &mut live, *value, RuntimeDemand::whole());
            }
            for clause in &receive.clauses {
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        types,
                        executable,
                        entries,
                        clause.entry,
                        outgoing_demand.clone(),
                        facts,
                        demands,
                        out,
                        call_return_demands,
                        callable_flows,
                    ),
                );
            }
            if let Some(after) = &receive.after {
                note_live_demand(out, &mut live, after.timeout, RuntimeDemand::whole());
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        types,
                        executable,
                        entries,
                        after.entry,
                        outgoing_demand,
                        facts,
                        demands,
                        out,
                        call_return_demands,
                        callable_flows,
                    ),
                );
            }
        }
        LoweredTail::Halt { .. } => {}
    }

    propagate_steps_reverse(
        types,
        entry.steps.as_slice(),
        &mut live,
        facts,
        demands,
        out,
        callable_flows,
    );
    if let Some((callsite, value)) = tail_call_return
        && let Some(demand) = out.value_demands.get(&value).cloned()
    {
        record_call_return_demand(call_return_demands, callsite, demand);
    }
    live
}

fn destination_demands(
    types: &Types,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    dest: &ControlDestination,
    outgoing_demand: RuntimeDemand,
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    callable_flows: &mut CallableFlowBuilder,
) -> (RuntimeDemand, HashMap<ValueId, RuntimeDemand>) {
    match dest {
        ControlDestination::Return => (outgoing_demand, HashMap::new()),
        ControlDestination::Deliver(entry_id) => {
            let delivered = entries[entry_id.as_u32() as usize]
                .origin
                .input_value()
                .expect("delivered control edges should target a resume entry");
            let mut external_demands = collect_entry_external_demands(
                types,
                executable,
                entries,
                *entry_id,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
                callable_flows,
            );
            let delivered_demand = external_demands.remove(&delivered).unwrap_or(RuntimeDemand::ignore());
            (delivered_demand, external_demands)
        }
    }
}

fn upgrade_joined_delivered_callable_value_demand(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    entry: ControlEntryId,
    value: ValueId,
    mut demand: RuntimeDemand,
) -> RuntimeDemand {
    if demand.is_callable() && delivered_join_has_distinct_callable_producers(facts, entry, value) {
        callable_flows.record_direct_demand(facts, value, &demand);
        demand.callable.escape = true;
    }
    demand
}

fn continuation_capture_demand(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    capture: ValueId,
    mut demand: RuntimeDemand,
) -> RuntimeDemand {
    if demand.is_callable()
        && facts.callable_origin(capture).is_none()
        && value_is_callable(facts, capture)
        && value_depends_on_callsite_return(facts, capture)
        && value_is_closure_callee(facts.body, capture)
    {
        demand.callable.escape = true;
    }
    record_first_class_boundary_demand(facts, callable_flows, capture, demand, None)
}

fn value_is_closure_callee(body: &LoweredBody, value: ValueId) -> bool {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return false;
    };
    clauses
        .iter()
        .any(|clause| tail_closure_callee(&clause.entry, entries, value))
        || entries
            .iter()
            .any(|entry| matches!(&entry.tail, LoweredTail::ClosureCall { callee, .. } if *callee == value))
}

fn tail_closure_callee(entry_id: &ControlEntryId, entries: &[LoweredEntry], value: ValueId) -> bool {
    entries
        .get(entry_id.as_u32() as usize)
        .is_some_and(|entry| matches!(&entry.tail, LoweredTail::ClosureCall { callee, .. } if *callee == value))
}

fn value_depends_on_callsite_return(facts: &RuntimeDemandFacts<'_>, value: ValueId) -> bool {
    let mut seen = HashSet::new();
    value_depends_on_callsite_return_inner(facts, value, &mut seen)
}

fn value_depends_on_callsite_return_inner(
    facts: &RuntimeDemandFacts<'_>,
    value: ValueId,
    seen: &mut HashSet<ValueId>,
) -> bool {
    if !seen.insert(value) {
        return false;
    }
    for join in facts.delivered_value_joins.values().filter(|join| join.value == value) {
        for source in &join.sources {
            match source {
                DeliveredValueSource::CallsiteReturn(_) => return true,
                DeliveredValueSource::LocalValue(source) => {
                    if value_depends_on_callsite_return_inner(facts, *source, seen) {
                        return true;
                    }
                }
            }
        }
    }
    let LoweredBody::Clauses { entries, .. } = &facts.body else {
        return false;
    };
    entries
        .iter()
        .flat_map(|entry| entry.steps.iter())
        .any(|step| step_value_depends_on_callsite_return(facts, step, value, seen))
}

fn step_value_depends_on_callsite_return(
    facts: &RuntimeDemandFacts<'_>,
    step: &LoweredStep,
    value: ValueId,
    seen: &mut HashSet<ValueId>,
) -> bool {
    let mut depends = |source| value_depends_on_callsite_return_inner(facts, source, seen);
    match step {
        LoweredStep::Tuple { value: defined, items } if *defined == value => items.iter().copied().any(depends),
        LoweredStep::List {
            value: defined,
            items,
            tail,
        } if *defined == value => items.iter().copied().any(&mut depends) || tail.is_some_and(depends),
        LoweredStep::Map {
            value: defined,
            entries,
        } if *defined == value => entries.iter().any(|(key, field)| depends(key.value) || depends(*field)),
        LoweredStep::MapUpdate {
            value: defined,
            base,
            entries,
        } if *defined == value => {
            depends(*base) || entries.iter().any(|(key, field)| depends(key.value) || depends(*field))
        }
        LoweredStep::Struct {
            value: defined, fields, ..
        } if *defined == value => fields.iter().any(|(_, field)| depends(*field)),
        LoweredStep::Bitstring { value: defined, fields } if *defined == value => fields.iter().any(|field| {
            depends(field.value)
                || matches!(
                    field.spec.size,
                    Some(super::super::body::LoweredBitSize::Value(size)) if depends(size)
                )
        }),
        LoweredStep::BinaryOp {
            value: defined,
            left,
            right,
            ..
        } if *defined == value => depends(*left) || depends(*right),
        LoweredStep::UnaryOp {
            value: defined, input, ..
        } if *defined == value => depends(*input),
        LoweredStep::MapIndex {
            value: defined,
            base,
            key,
        } if *defined == value => depends(*base) || depends(key.value),
        LoweredStep::FieldAccess {
            value: defined, base, ..
        } if *defined == value => depends(*base),
        LoweredStep::RequireMapValue {
            value: defined, source, ..
        } if *defined == value => depends(*source),
        LoweredStep::TupleField {
            value: defined, source, ..
        } if *defined == value => depends(*source),
        LoweredStep::SplitList { source, head, tail } if *head == value || *tail == value => depends(*source),
        LoweredStep::BitstringInit { reader, source } if *reader == value => depends(*source),
        LoweredStep::BitstringRead {
            ok,
            value: read_value,
            next_reader,
            reader,
            spec,
            ..
        } if *ok == value || *read_value == value || *next_reader == value => {
            depends(*reader)
                || matches!(
                    spec.size,
                    Some(super::super::body::LoweredBitSize::Value(size)) if depends(size)
                )
        }
        LoweredStep::Const { .. }
        | LoweredStep::FunctionRef { .. }
        | LoweredStep::Lambda { .. }
        | LoweredStep::AssertLiteral { .. }
        | LoweredStep::AssertStruct { .. }
        | LoweredStep::AssertTuple { .. }
        | LoweredStep::AssertEmptyList { .. }
        | LoweredStep::AssertSame { .. }
        | LoweredStep::AssertBitstringDone { .. }
        | LoweredStep::Tuple { .. }
        | LoweredStep::List { .. }
        | LoweredStep::Map { .. }
        | LoweredStep::MapUpdate { .. }
        | LoweredStep::Struct { .. }
        | LoweredStep::Bitstring { .. }
        | LoweredStep::BinaryOp { .. }
        | LoweredStep::UnaryOp { .. }
        | LoweredStep::MapIndex { .. }
        | LoweredStep::FieldAccess { .. }
        | LoweredStep::RequireMapValue { .. }
        | LoweredStep::TupleField { .. }
        | LoweredStep::SplitList { .. }
        | LoweredStep::BitstringInit { .. }
        | LoweredStep::BitstringRead { .. } => false,
    }
}

fn record_delivered_call_return_demands(
    facts: &RuntimeDemandFacts<'_>,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    entry: ControlEntryId,
    value: ValueId,
    demand: &RuntimeDemand,
) {
    let Some(join) = facts.delivered_value_joins.get(&entry) else {
        return;
    };
    if join.value != value {
        return;
    }
    for source in &join.sources {
        let DeliveredValueSource::CallsiteReturn(callsite) = source else {
            continue;
        };
        record_call_return_demand(call_return_demands, *callsite, demand.clone());
    }
}

fn delivered_join_has_distinct_callable_producers(
    facts: &RuntimeDemandFacts<'_>,
    entry: ControlEntryId,
    delivered: ValueId,
) -> bool {
    let Some(join) = facts.delivered_value_joins.get(&entry) else {
        return false;
    };
    if join.value != delivered {
        return false;
    }
    let producers = join
        .sources
        .iter()
        .filter_map(|join_source| match join_source {
            DeliveredValueSource::LocalValue(value) => facts.callable_origin(*value),
            DeliveredValueSource::CallsiteReturn(_) => None,
        })
        .collect::<HashSet<_>>();
    producers.len() > 1
}

fn propagate_steps_reverse(
    types: &Types,
    steps: &[LoweredStep],
    live: &mut HashMap<ValueId, RuntimeDemand>,
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    out: &mut ExecutableRuntimeDemand,
    callable_flows: &mut CallableFlowBuilder,
) {
    let asserted_tuple_arities = step_asserted_tuple_arities(steps);
    for step in steps.iter().rev() {
        match step {
            LoweredStep::Const { .. } => {}
            LoweredStep::FunctionRef { value, .. } => {
                if let Some(demand) = live.get(value) {
                    callable_flows.record_direct_demand(facts, *value, demand);
                }
            }
            LoweredStep::Tuple { value, items } => {
                let demand = take_live_demand(live, *value);
                if !demand.is_callable() {
                    match demand.shape {
                        ShapeDemand::Ignore => {}
                        ShapeDemand::TupleFields(fields) if fields.len() <= items.len() => {
                            for (item, demand) in items.iter().zip(fields) {
                                let demand = boundary_value_flow_demand(facts, callable_flows, *item, demand);
                                note_live_demand(out, live, *item, demand);
                            }
                        }
                        _ => {
                            for item in items {
                                let demand =
                                    boundary_value_flow_demand(facts, callable_flows, *item, RuntimeDemand::whole());
                                note_live_demand(out, live, *item, demand);
                            }
                        }
                    }
                } else {
                    for item in items {
                        let demand = boundary_value_flow_demand(facts, callable_flows, *item, RuntimeDemand::whole());
                        note_live_demand(out, live, *item, demand);
                    }
                }
            }
            LoweredStep::List { value, items, tail } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for item in items {
                        let demand = boundary_value_flow_demand(facts, callable_flows, *item, RuntimeDemand::whole());
                        note_live_demand(out, live, *item, demand);
                    }
                    if let Some(tail) = tail {
                        let demand = boundary_value_flow_demand(facts, callable_flows, *tail, RuntimeDemand::whole());
                        note_live_demand(out, live, *tail, demand);
                    }
                }
            }
            LoweredStep::Map { value, entries } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for (key, field) in entries {
                        let key_demand =
                            boundary_value_flow_demand(facts, callable_flows, key.value, RuntimeDemand::whole());
                        let field_demand =
                            boundary_value_flow_demand(facts, callable_flows, *field, RuntimeDemand::whole());
                        note_live_demand(out, live, key.value, key_demand);
                        note_live_demand(out, live, *field, field_demand);
                    }
                }
            }
            LoweredStep::MapUpdate { value, base, entries } => {
                if !take_live_demand(live, *value).is_ignore() {
                    let base_demand = boundary_value_flow_demand(facts, callable_flows, *base, RuntimeDemand::whole());
                    note_live_demand(out, live, *base, base_demand);
                    for (key, field) in entries {
                        let key_demand =
                            boundary_value_flow_demand(facts, callable_flows, key.value, RuntimeDemand::whole());
                        let field_demand =
                            boundary_value_flow_demand(facts, callable_flows, *field, RuntimeDemand::whole());
                        note_live_demand(out, live, key.value, key_demand);
                        note_live_demand(out, live, *field, field_demand);
                    }
                }
            }
            LoweredStep::Struct { value, fields, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for (_, field) in fields {
                        let demand = boundary_value_flow_demand(facts, callable_flows, *field, RuntimeDemand::whole());
                        note_live_demand(out, live, *field, demand);
                    }
                }
            }
            LoweredStep::Bitstring { value, fields } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for field in fields {
                        note_live_demand(out, live, field.value, RuntimeDemand::whole());
                        if let Some(super::super::body::LoweredBitSize::Value(size)) = &field.spec.size {
                            note_live_demand(out, live, *size, RuntimeDemand::whole());
                        }
                    }
                }
            }
            LoweredStep::Lambda {
                value,
                function,
                captures,
            } => {
                let demand = take_live_demand(live, *value);
                callable_flows.record_direct_demand(facts, *value, &demand);
                if !demand.is_ignore() {
                    propagate_lambda_capture_demands(
                        types,
                        *value,
                        *function,
                        captures.as_slice(),
                        demand,
                        facts,
                        demands,
                        live,
                        out,
                        callable_flows,
                    );
                }
            }
            LoweredStep::BinaryOp { value, left, right, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(out, live, *left, RuntimeDemand::whole());
                    note_live_demand(out, live, *right, RuntimeDemand::whole());
                }
            }
            LoweredStep::UnaryOp { value, input, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(out, live, *input, RuntimeDemand::whole());
                }
            }
            LoweredStep::MapIndex { value, base, key } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(out, live, *base, RuntimeDemand::whole());
                    note_live_demand(out, live, key.value, RuntimeDemand::whole());
                }
            }
            LoweredStep::FieldAccess { value, base, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(out, live, *base, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertLiteral { source, .. } => {
                note_live_demand(out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::AssertStruct { source, .. } => {
                note_live_demand(out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::RequireMapValue { value, source, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertTuple { source, arity } => {
                if !live.contains_key(source) || asserted_tuple_arities.get(source).copied() != Some(*arity) {
                    note_live_demand(out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::TupleField { value, source, index } => {
                let demand = take_live_demand(live, *value);
                if !demand.is_ignore() {
                    let arity = asserted_tuple_arities.get(source).copied().unwrap_or(index + 1);
                    let mut fields = vec![RuntimeDemand::ignore(); arity];
                    fields[*index] = demand;
                    note_live_demand(out, live, *source, RuntimeDemand::tuple_fields(fields));
                }
            }
            LoweredStep::AssertEmptyList { source } => {
                note_live_demand(out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::AssertSame { source, value } => {
                note_live_demand(out, live, *source, RuntimeDemand::whole());
                note_live_demand(out, live, *value, RuntimeDemand::whole());
            }
            LoweredStep::SplitList { source, head, tail } => {
                let head_demand = take_live_demand(live, *head);
                let tail_demand = take_live_demand(live, *tail);
                if !head_demand.is_ignore() || !tail_demand.is_ignore() {
                    note_live_demand(out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::BitstringInit { reader, source } => {
                if !take_live_demand(live, *reader).is_ignore() {
                    note_live_demand(out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::BitstringRead {
                ok,
                value,
                next_reader,
                reader,
                spec,
                ..
            } => {
                let ok_demand = take_live_demand(live, *ok);
                let value_demand = take_live_demand(live, *value);
                let next_reader_demand = take_live_demand(live, *next_reader);
                if !ok_demand.is_ignore() || !value_demand.is_ignore() || !next_reader_demand.is_ignore() {
                    note_live_demand(out, live, *reader, RuntimeDemand::whole());
                    if let Some(super::super::body::LoweredBitSize::Value(size)) = &spec.size {
                        note_live_demand(out, live, *size, RuntimeDemand::whole());
                    }
                }
            }
            LoweredStep::AssertBitstringDone { reader } => {
                note_live_demand(out, live, *reader, RuntimeDemand::whole());
            }
        }
    }
    // `jobs/backend.rs::lower_step` packages a `TupleField` step into a real
    // `BackendStep::TupleField` unconditionally — unlike the fresh-construction
    // steps (`construction_step_or_omitted`), it
    // has no `Omitted` fallback for a provably-unread projection. Native
    // codegen therefore always reads `source` to extract the field, even
    // when every field ever projected from it goes unused downstream (e.g.
    // a guard-passed match arm that destructures `{:ok, s}` but returns a
    // literal without touching `s`). The per-step handling above already
    // keeps `source` live whenever ANY projected field carries real demand
    // (the ordinary, common case — no change needed there), but when EVERY
    // field projected from a given `source` is ignored, `source` never
    // enters `live` at all and its transport lane starves — the fz-xvq
    // "materialize absent value" crash. This closing sweep is the exact,
    // minimal net for only that starved case: for any `source` this steps
    // slice projects a `TupleField` from that isn't already live by any
    // other means, float it to a per-field `Whole` (`tuple_fields`, not a
    // bare `whole()`) so the transport layer keeps the same field-split
    // freedom an already-demanded source has — a bare `whole()` would
    // instead assert the *opaque box* is needed, forcing a single boxed
    // lane and coarsening an otherwise-splittable tuple (e.g. a `{:cont,
    // acc}` HOF continuation whose split raw lanes another clause of the
    // same shared body legitimately demands). Sources that already carry
    // demand from a live field are untouched, so this cannot regress the
    // split-lane shape of an already-working case.
    let mut floored = HashSet::new();
    for step in steps {
        if let LoweredStep::TupleField { source, .. } = step
            && !live.contains_key(source)
            && floored.insert(*source)
        {
            let arity = asserted_tuple_arities.get(source).copied().unwrap_or_else(|| {
                steps
                    .iter()
                    .filter_map(|step| match step {
                        LoweredStep::TupleField {
                            source: candidate,
                            index,
                            ..
                        } if candidate == source => Some(*index + 1),
                        _ => None,
                    })
                    .max()
                    .unwrap_or(1)
            });
            note_live_demand(
                out,
                live,
                *source,
                RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(); arity]),
            );
        }
    }
}

fn step_asserted_tuple_arities(steps: &[LoweredStep]) -> HashMap<ValueId, usize> {
    let mut arities = HashMap::new();
    for step in steps {
        if let LoweredStep::AssertTuple { source, arity } = step {
            arities.insert(*source, *arity);
        }
    }
    arities
}

fn note_clause_matcher_demands(
    facts: &RuntimeDemandFacts<'_>,
    steps: &[LoweredStep],
    live: &mut HashMap<ValueId, RuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
) {
    for step in steps {
        match step {
            LoweredStep::AssertLiteral { source, .. }
            | LoweredStep::AssertStruct { source, .. }
            | LoweredStep::AssertTuple { source, .. }
            | LoweredStep::AssertEmptyList { source }
            | LoweredStep::BitstringInit { source, .. } => {
                let demand = boundary_value_demand(facts, *source, RuntimeDemand::whole());
                note_live_demand(out, live, *source, demand);
            }
            LoweredStep::RequireMapValue { source, .. } => {
                let source_demand = boundary_value_demand(facts, *source, RuntimeDemand::whole());
                note_live_demand(out, live, *source, source_demand);
            }
            LoweredStep::AssertSame { source, value } => {
                let source_demand = boundary_value_demand(facts, *source, RuntimeDemand::whole());
                note_live_demand(out, live, *source, source_demand);
                let value_demand = boundary_value_demand(facts, *value, RuntimeDemand::whole());
                note_live_demand(out, live, *value, value_demand);
            }
            LoweredStep::SplitList { source, .. } => {
                let demand = boundary_value_demand(facts, *source, RuntimeDemand::whole());
                note_live_demand(out, live, *source, demand);
            }
            LoweredStep::BitstringRead { reader, spec, .. } => {
                let demand = boundary_value_demand(facts, *reader, RuntimeDemand::whole());
                note_live_demand(out, live, *reader, demand);
                if let Some(super::super::body::LoweredBitSize::Value(size)) = &spec.size {
                    note_live_demand(out, live, *size, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertBitstringDone { reader } => {
                let demand = boundary_value_demand(facts, *reader, RuntimeDemand::whole());
                note_live_demand(out, live, *reader, demand);
            }
            LoweredStep::Const { .. }
            | LoweredStep::Tuple { .. }
            | LoweredStep::List { .. }
            | LoweredStep::Map { .. }
            | LoweredStep::MapUpdate { .. }
            | LoweredStep::Struct { .. }
            | LoweredStep::Bitstring { .. }
            | LoweredStep::FunctionRef { .. }
            | LoweredStep::Lambda { .. }
            | LoweredStep::BinaryOp { .. }
            | LoweredStep::UnaryOp { .. }
            | LoweredStep::MapIndex { .. }
            | LoweredStep::FieldAccess { .. }
            | LoweredStep::TupleField { .. } => {}
        }
    }
}

fn propagate_lambda_capture_demands(
    types: &Types,
    value: ValueId,
    function: FunctionId,
    captures: &[ValueId],
    demand: RuntimeDemand,
    facts: &RuntimeDemandFacts<'_>,
    all_demands: &RuntimeDemandFormulaSnapshot,
    live: &mut HashMap<ValueId, RuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
    callable_flows: &mut CallableFlowBuilder,
) {
    if !demand.is_callable() {
        for capture in captures {
            note_live_demand(out, live, *capture, RuntimeDemand::whole());
        }
        return;
    }
    let callable = demand.callable;
    let mut exact_edges =
        callable_flow_edges_for_targets(types, &all_demands.member, facts, function, captures, &callable.targets);
    exact_edges.extend(
        all_demands
            .construction_targets
            .iter()
            .filter(|((owner_value, _), target)| *owner_value == value && target.activation.function == function)
            .map(|((_, surface), target)| CallableFlowEdge {
                surface: surface.clone(),
                resolution: target.clone(),
                capture_semantic_inputs: (0..captures.len()).collect(),
                surface_semantic_inputs: (captures.len()..captures.len() + surface.inputs.len()).collect(),
                boundary_input_demands: Box::new([]),
            }),
    );
    exact_edges.sort_by(|left, right| left.resolution.semantic_cmp(&right.resolution, types));
    exact_edges.dedup_by(|left, right| left.resolution == right.resolution && left.surface == right.surface);
    for edge in exact_edges {
        let Some(callee_inputs) = all_demands.target_inputs.get(&edge.resolution) else {
            continue;
        };
        for (capture, demand) in captures.iter().zip(callee_inputs) {
            callable_flows.record_direct_surfaces(facts, *capture, &demand.callable.resolved);
            let demand = closure_capture_boundary_demand(facts, callable_flows, *capture, demand.clone(), &callable);
            note_live_demand(out, live, *capture, demand);
        }
    }
}

fn closure_capture_boundary_demand(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    capture: ValueId,
    demand: RuntimeDemand,
    closure: &CallableDemand,
) -> RuntimeDemand {
    if demand.shape == ShapeDemand::Whole
        && !demand.is_callable()
        && value_is_callable(facts, capture)
        && let Some(direct) = direct_only_capture_callable_demand(facts, capture, closure)
    {
        callable_flows.record_direct_demand(facts, capture, &direct);
        return direct;
    }
    let mut upgraded = boundary_value_demand(facts, capture, demand);
    if upgraded.is_callable() {
        upgraded.callable.opaque |= closure.opaque;
        upgraded.callable.escape |= closure.escape;
        record_first_class_boundary_demand(facts, callable_flows, capture, upgraded.clone(), None);
    }
    upgraded
}

fn callable_value_type_demand(facts: &RuntimeDemandFacts<'_>, value: ValueId) -> Option<RuntimeDemand> {
    let ty = facts.value_types.get(&value).copied()?;
    facts.callable_value_demand(ty)
}

fn direct_only_capture_callable_demand(
    facts: &RuntimeDemandFacts<'_>,
    value: ValueId,
    closure: &CallableDemand,
) -> Option<RuntimeDemand> {
    let type_demand = callable_value_type_demand(facts, value)?;
    let arities = type_demand
        .callable
        .resolved
        .iter()
        .map(|surface| surface.inputs.len())
        .collect::<HashSet<_>>();
    let closure_surfaces = closure
        .resolved
        .iter()
        .filter(|surface| arities.contains(&surface.inputs.len()))
        .cloned()
        .collect::<BTreeSet<_>>();
    if closure_surfaces.is_empty() {
        return Some(type_demand);
    }
    Some(RuntimeDemand::callable(CallableDemand {
        resolved: closure_surfaces,
        targets: closure
            .targets
            .iter()
            .filter(|target| arities.contains(&target.surface.inputs.len()))
            .cloned()
            .collect(),
        opaque: false,
        escape: false,
    }))
}

fn direct_call_arg_demands(
    types: &Types,
    executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    callable_flows: &mut CallableFlowBuilder,
) -> Vec<RuntimeDemand> {
    arg_demands_for_summary(
        types,
        executable,
        callsite,
        args,
        CallInputMode::Direct,
        facts,
        demands,
        callable_flows,
    )
}

fn closure_call_arg_demands(
    types: &Types,
    executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    callable_flows: &mut CallableFlowBuilder,
) -> Vec<RuntimeDemand> {
    arg_demands_for_summary(
        types,
        executable,
        callsite,
        args,
        CallInputMode::Closure,
        facts,
        demands,
        callable_flows,
    )
}

fn arg_demands_for_summary(
    types: &Types,
    _executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    input_mode: CallInputMode,
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    callable_flows: &mut CallableFlowBuilder,
) -> Vec<RuntimeDemand> {
    let arity = args.len();
    let mut out = vec![RuntimeDemand::ignore(); arity];
    let Some(summary) = facts.callsites.get(&callsite) else {
        return args
            .iter()
            .map(|arg| boundary_value_flow_demand(facts, callable_flows, arg.value, RuntimeDemand::whole()))
            .collect();
    };
    let need = facts
        .callsite_needs
        .get(&callsite)
        .copied()
        .unwrap_or(ExecutableNeed::Value);
    if summary.targets.len() > 1
        && let Some(arg) = args.first()
    {
        for fallback_ty in multi_target_receiver_fallbacks(summary, facts.demand_types.any) {
            let receiver_demand =
                boundary_value_flow_demand_at(facts, callable_flows, arg.value, RuntimeDemand::whole(), fallback_ty);
            out[0].join_assign(&receiver_demand);
        }
    }
    for target in &summary.targets {
        let records_direct_arg_surfaces = matches!(target.callee, super::super::semantic::SelectedCallee::Function(_))
            && target.activation.is_some()
            && target.extern_params.is_none();
        let target_demands = local_target_input_demands(types, facts, target, need, demands);
        for (index, (arg, slot)) in args.iter().zip(out.iter_mut()).enumerate().take(arity) {
            let fallback_ty = target
                .surface_inputs
                .get(index)
                .copied()
                .unwrap_or(facts.demand_types.any);
            // A malformed callsite (more closure args than the callee has
            // inputs, or a direct arg past the callee's arity) falls back to
            // the raw `index` -- the same offset the checked computation
            // would have produced anyway for `Direct` (it returns `arg_index`
            // verbatim when in range), and the same offset the old unchecked
            // `Closure` arithmetic produced once its `saturating_sub`
            // underflow-clip landed on zero. `target_demands.get(offset)`
            // below treats an out-of-range offset as a miss regardless, so
            // this is not a behavior change.
            let offset = target
                .activation
                .as_ref()
                .and_then(|activation| input_mode.semantic_index(activation.input_len(types), args.len(), index))
                .unwrap_or(index);
            let observed = target_demands
                .get(offset)
                .cloned()
                .unwrap_or_else(|| facts.boundary_demand(fallback_ty));
            if records_direct_arg_surfaces {
                let direct_surfaces = facts
                    .callable_surfaces(fallback_ty)
                    .cloned()
                    .unwrap_or_else(|| observed.callable.resolved.clone());
                callable_flows.record_direct_surfaces(facts, arg.value, &direct_surfaces);
            }
            let mut observed = boundary_value_flow_demand_at(facts, callable_flows, arg.value, observed, fallback_ty);
            if !records_direct_arg_surfaces {
                ground_first_class_callable_surface(facts, &mut observed, fallback_ty);
            }
            slot.join_assign(&observed);
        }
    }
    // The boxed-apply ABI for a *closure* callsite (`CallEdge::Indirect` /
    // `generic_callable_shape`) transmits a real value in every argument
    // lane regardless of what any one resolved callee does with it, and
    // regardless of how many targets `summary.targets` resolved to. Whether
    // native codegen ends up on the direct-call fast path (which *can* skip
    // a truly-unused arg lane, because there the caller and the one callee
    // share a co-designed, per-instantiation ABI —
    // `direct_closure_capture_lanes`/`closure_fast_path_arg_is_structural`
    // in `native.rs`) or falls back to the generic indirect closure-call
    // path (which always lowers every positional arg via `env_runtime_vars`,
    // with no callee-demand check at all) is a native-codegen-time
    // structural decision this pass cannot predict — so it must assume the
    // worst case even for an unambiguous single-target callsite. Joining
    // demands *per target* (as the loop above does) lets an argument some
    // targets ignore -- e.g. a shared HOF body's `_acc` parameter that one
    // target discards, or a closure whose sole target never reads its own
    // parameter (an Enumerable slice continuation's unused `_map`) -- join
    // down to `Ignore`, starving that argument's materialization even
    // though the ABI still carries it once codegen picks the generic path.
    // Floor every argument to `Whole` for every closure callsite,
    // generalizing the index-0-only receiver floor above (which covers the
    // direct/receiver protocol-dispatch case) to every argument position.
    if matches!(input_mode, CallInputMode::Closure) {
        for slot in out.iter_mut() {
            slot.join_assign(&RuntimeDemand::whole());
        }
    }
    out
}

fn multi_target_receiver_fallbacks(summary: &CallSiteSummary, any: Ty) -> BTreeSet<Ty> {
    let mut fallbacks = summary
        .targets
        .iter()
        .filter_map(|target| target.surface_inputs.first().copied())
        .collect::<BTreeSet<_>>();
    if fallbacks.is_empty() {
        fallbacks.insert(any);
    }
    fallbacks
}

/// Seed an escaping callable argument's surface from the boundary it crosses.
///
/// `boundary_value_demand` raises first-class `escape` on the callable axis but
/// records no `resolved` surface — the axis is type-blind by construction. The
/// surface the callee actually invokes the argument at is the boundary's settled
/// parameter type (`boundary_ty`), which pins free callable type variables to
/// their grounded instantiation. Unioning that surface onto an escaping callable
/// keys the escaping body at the grounded lane instead of its own polymorphic
/// template.
///
/// This is a *type seed*, not a re-grounding: it only ever adds a surface
/// derived from the static boundary type, gated solely on the monotone `escape`
/// bit. It never inspects (and so never depends on) the evolving callable axis,
/// so the union is unconditional — a callable that is both directly called and
/// escapes keeps both its call surface and its escape surface, and the demand
/// can only ascend across content-changing reactive evaluations.
fn ground_first_class_callable_surface(facts: &RuntimeDemandFacts<'_>, demand: &mut RuntimeDemand, boundary_ty: Ty) {
    if !demand.callable.is_first_class() {
        return;
    }
    let Some(surfaces) = facts.callable_surfaces(boundary_ty) else {
        return;
    };
    demand.callable.resolved.extend(surfaces.iter().cloned());
}

fn local_target_input_demands(
    types: &Types,
    facts: &RuntimeDemandFacts<'_>,
    target: &super::super::semantic::CallTargetSummary,
    need: ExecutableNeed,
    demands: &RuntimeDemandFormulaSnapshot,
) -> Vec<RuntimeDemand> {
    match target.callee {
        super::super::semantic::SelectedCallee::ProviderBoundary(_function) => {
            // A provider boundary is interface-only by construction: it has no
            // defined function and no module body (`function_is_provider_boundary`),
            // so there is no lowered body to consult. Every argument crosses the
            // seam at its boundary demand; marshalling is the boundary fact's job.
            target
                .surface_inputs
                .iter()
                .copied()
                .map(|ty| facts.boundary_demand(ty))
                .collect()
        }
        super::super::semantic::SelectedCallee::Function(_) => {
            if let Some(extern_params) = target.extern_params {
                return target
                    .surface_inputs
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| {
                        if index < extern_params {
                            RuntimeDemand::whole()
                        } else {
                            facts.boundary_demand(*ty)
                        }
                    })
                    .collect();
            }
            let Some(activation) = target.activation.clone() else {
                return target
                    .surface_inputs
                    .iter()
                    .copied()
                    .map(|ty| facts.boundary_demand(ty))
                    .collect();
            };
            demands
                .target_inputs
                .get(&ExecutableKey { activation, need })
                .cloned()
                .unwrap_or_else(|| {
                    vec![RuntimeDemand::ignore(); target.activation.as_ref().map_or(0, |a| a.input_len(types))]
                })
        }
    }
}

fn value_is_callable(facts: &RuntimeDemandFacts<'_>, value: ValueId) -> bool {
    facts
        .value_types
        .get(&value)
        .copied()
        .is_some_and(|ty| facts.callable_surfaces(ty).is_some())
}

/// The runtime demand on `value` given the representation demand a consumer
/// places on it — the single chokepoint for first-class callable escape.
///
/// A callable consumed for its whole representation, with no resolved call
/// contract, escapes first-class. That is recorded by joining `escape` onto the
/// value's callable axis: a monotone raise that preserves the shape axis,
/// preserves any accumulated `resolved` surfaces, and never clears `opaque`.
/// Non-callable values, and callables that already carry a call contract, pass
/// through unchanged. There is no re-grounding from the value's type: the
/// callable axis is never erased by a shape join, so nothing needs recovering.
fn boundary_value_demand(facts: &RuntimeDemandFacts<'_>, value: ValueId, mut demand: RuntimeDemand) -> RuntimeDemand {
    if demand.shape == ShapeDemand::Whole && !demand.is_callable() && value_is_callable(facts, value) {
        demand.callable.join_assign(&CallableDemand::escaped());
    }
    demand
}

fn boundary_value_flow_demand(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    value: ValueId,
    demand: RuntimeDemand,
) -> RuntimeDemand {
    let demand = boundary_value_demand(facts, value, demand);
    record_first_class_boundary_demand(facts, callable_flows, value, demand, None)
}

fn boundary_value_flow_demand_at(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    value: ValueId,
    demand: RuntimeDemand,
    boundary_ty: Ty,
) -> RuntimeDemand {
    let demand = boundary_value_demand(facts, value, demand);
    record_first_class_boundary_demand(facts, callable_flows, value, demand, Some(boundary_ty))
}

fn record_first_class_boundary_demand(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    value: ValueId,
    demand: RuntimeDemand,
    boundary_ty: Option<Ty>,
) -> RuntimeDemand {
    if demand.callable.is_first_class() {
        let mut recorded = RuntimeDemand::callable(CallableDemand {
            resolved: BTreeSet::new(),
            targets: BTreeSet::new(),
            opaque: demand.callable.opaque,
            escape: demand.callable.escape,
        });
        let may_seed_from_value_type = demand.callable.resolved.is_empty() || facts.callable_origin(value).is_some();
        let type_seed = boundary_ty.or_else(|| {
            may_seed_from_value_type
                .then(|| facts.value_types.get(&value).copied())
                .flatten()
        });
        if let Some(ty) = type_seed {
            ground_first_class_callable_surface(facts, &mut recorded, ty);
        }
        if boundary_ty.is_none() {
            // No boundary type to ground against: seed the escaping surfaces from
            // the value's concrete call shapes. The publication surfaces are
            // grounded once, downstream, in `ground_dispatch_surfaces`.
            recorded.callable.resolved.extend(demand.callable.resolved.clone());
            recorded.callable.resolved.extend(callable_flows.direct_surfaces(value));
        }
        callable_flows.record_first_class_demand(facts, value, &recorded);
    }
    demand
}

fn closure_callee_demand(
    facts: &RuntimeDemandFacts<'_>,
    args: &[CallArg],
    summary: Option<&CallSiteSummary>,
    need: ExecutableNeed,
) -> CallableDemand {
    let actual_inputs: Vec<Ty> = args
        .iter()
        .map(|arg| {
            facts
                .value_types
                .get(&arg.value)
                .copied()
                .unwrap_or(facts.demand_types.any)
        })
        .collect();
    let Some(summary) = summary else {
        let mut demand = CallableDemand {
            resolved: Default::default(),
            targets: BTreeSet::new(),
            opaque: true,
            escape: false,
        };
        demand.resolved.insert(facts.demand_types.surface(&actual_inputs));
        return demand;
    };
    let mut demand = CallableDemand::default();
    demand.resolved.insert(facts.demand_types.surface(&actual_inputs));
    for target in &summary.targets {
        let surface = facts.demand_types.surface(&target.surface_inputs);
        demand.resolved.insert(surface.clone());
        if let (Some(activation), Some(activation_inputs)) = (&target.activation, &target.activation_inputs) {
            demand.targets.insert(CallableTarget {
                surface,
                activation: activation.clone(),
                activation_inputs: activation_inputs.clone(),
                need,
            });
        }
    }
    let exact_local_target = matches!(
        summary.targets.as_slice(),
        [target]
            if matches!(target.callee, super::super::semantic::SelectedCallee::Function(_))
                && target.activation.is_some()
                && target.activation_inputs.is_some()
    );
    if !exact_local_target {
        demand.opaque = true;
    }
    demand
}

fn finish_callable_flows(plans: Vec<CallableFlowPlan>, demand: &mut ExecutableRuntimeDemand) {
    demand.callable_flows.clear();
    for plan in plans {
        let first_class_edges = dispatch_stress::perturbed_construction_edges(plan.first_class_edges);
        let mut resolutions = Vec::new();
        extend_unique(
            &mut resolutions,
            plan.direct_edges
                .iter()
                .chain(&first_class_edges)
                .map(|edge| edge.resolution.clone())
                .collect(),
        );
        demand.callable_flows.insert(
            plan.value,
            CallableFlowFact {
                function: plan.producer.function,
                captures: plan.producer.captures,
                direct_surfaces: plan.direct_surfaces,
                first_class_surfaces: plan.first_class_surfaces,
                direct_edges: plan.direct_edges,
                first_class_edges,
                opaque: plan.opaque,
                escape: plan.escape,
                resolutions,
            },
        );
    }
}

fn extend_unique<T: PartialEq>(target: &mut Vec<T>, values: Vec<T>) {
    for value in values {
        if !target.contains(&value) {
            target.push(value);
        }
    }
}

fn note_live_demand(
    out: &mut ExecutableRuntimeDemand,
    live: &mut HashMap<ValueId, RuntimeDemand>,
    value: ValueId,
    demand: RuntimeDemand,
) {
    if demand.is_ignore() {
        return;
    }
    join_map_demand(live, value, demand.clone());
    join_map_demand(&mut out.value_demands, value, demand);
}

fn merge_live_demands(target: &mut HashMap<ValueId, RuntimeDemand>, observed: HashMap<ValueId, RuntimeDemand>) {
    for (value, demand) in observed {
        join_map_demand(target, value, demand);
    }
}

fn join_map_demand(target: &mut HashMap<ValueId, RuntimeDemand>, value: ValueId, demand: RuntimeDemand) {
    target
        .entry(value)
        .and_modify(|existing| existing.join_assign(&demand))
        .or_insert(demand);
}

fn record_call_arg_demands(out: &mut ExecutableRuntimeDemand, callsite: CallSiteId, observed: &[RuntimeDemand]) {
    let slot = out
        .call_arg_demands
        .entry(callsite)
        .or_insert_with(|| vec![RuntimeDemand::ignore(); observed.len()]);
    if slot.len() < observed.len() {
        slot.resize(observed.len(), RuntimeDemand::ignore());
    }
    for (existing, observed) in slot.iter_mut().zip(observed.iter()) {
        existing.join_assign(observed);
    }
}

fn record_entry_capture_demands(
    out: &mut ExecutableRuntimeDemand,
    entry_id: ControlEntryId,
    observed: &[RuntimeDemand],
) {
    let slot = out
        .entry_capture_demands
        .entry(entry_id)
        .or_insert_with(|| vec![RuntimeDemand::ignore(); observed.len()]);
    if slot.len() < observed.len() {
        slot.resize(observed.len(), RuntimeDemand::ignore());
    }
    for (existing, observed) in slot.iter_mut().zip(observed.iter()) {
        existing.join_assign(observed);
    }
}

fn record_call_return_demand(
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    callsite: CallSiteId,
    observed: RuntimeDemand,
) {
    if observed.is_ignore() {
        return;
    }
    call_return_demands
        .entry(callsite)
        .and_modify(|existing| existing.join_assign(&observed))
        .or_insert(observed);
}

fn take_live_demand(live: &mut HashMap<ValueId, RuntimeDemand>, value: ValueId) -> RuntimeDemand {
    live.remove(&value).unwrap_or(RuntimeDemand::ignore())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::body::ControlEntryOrigin;
    use crate::compiler2::semantic::{CallTargetSummary, SelectedCallee};
    use crate::compiler2::types::Types;
    use crate::source::Span;

    #[test]
    fn lowered_call_kind_is_preserved_in_transport_origins() {
        let direct_callsite = CallSiteId::from_u32(0);
        let closure_callsite = CallSiteId::from_u32(1);
        let direct_value = ValueId::from_u32(0);
        let closure_value = ValueId::from_u32(1);
        let entry = |tail| LoweredEntry {
            span: Span::DUMMY,
            origin: ControlEntryOrigin::Clause,
            params: Vec::new(),
            captures: Vec::new(),
            reusable_cons_captures: Vec::new(),
            steps: Vec::new(),
            tail,
        };
        let body = LoweredBody::Clauses {
            clauses: Vec::new(),
            entries: vec![
                entry(LoweredTail::DirectCall {
                    value: direct_value,
                    callsite: direct_callsite,
                    callee: FunctionId::for_test(0),
                    args: Vec::new(),
                    dest: ControlDestination::Return,
                }),
                entry(LoweredTail::ClosureCall {
                    value: closure_value,
                    callsite: closure_callsite,
                    callee: ValueId::from_u32(2),
                    args: Vec::new(),
                    dest: ControlDestination::Return,
                }),
            ],
            generated: Vec::new(),
        };

        let callsite_origins = collect_callsite_return_origins(&body);
        let value_origins = collect_value_origins(&body, &callsite_origins);

        assert_eq!(
            value_origins.get(&direct_value),
            Some(&TransportOrigin::CallsiteReturn(direct_callsite))
        );
        assert_eq!(
            value_origins.get(&closure_value),
            Some(&TransportOrigin::ClosureCallReturn {
                callsite: closure_callsite,
                callee: ValueId::from_u32(2),
            })
        );
    }

    #[test]
    fn multi_target_receiver_fallback_joins_exact_surfaces_independent_of_target_order() {
        let mut types = Types::new();
        let (any, int, atom) = (types.any(), types.int(), types.atom());
        let target = |ty: Option<Ty>| CallTargetSummary {
            callee: SelectedCallee::Function(FunctionId::for_test(0)),
            surface_inputs: ty.into_iter().collect(),
            activation: None,
            activation_inputs: None,
            extern_params: None,
            return_ty: None,
        };
        let summary = |targets| CallSiteSummary {
            targets,
            return_ty: None,
        };
        let expected = BTreeSet::from([int, atom]);

        assert_eq!(
            multi_target_receiver_fallbacks(&summary(vec![target(Some(int)), target(Some(atom))]), any),
            expected
        );
        assert_eq!(
            multi_target_receiver_fallbacks(&summary(vec![target(Some(atom)), target(Some(int))]), any),
            expected
        );
        assert_eq!(
            multi_target_receiver_fallbacks(&summary(vec![target(None), target(Some(atom))]), any),
            BTreeSet::from([atom]),
            "an absent surface must not widen a receiver when another target supplies its exact surface"
        );
        assert_eq!(
            multi_target_receiver_fallbacks(&summary(vec![target(None), target(None)]), any),
            BTreeSet::from([any]),
            "only an entirely unknown target set needs the any fallback"
        );
    }
}
