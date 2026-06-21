use std::collections::{BTreeSet, HashMap, HashSet};

use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryId, DeliveredValueJoin, DeliveredValueSource, LoweredBody,
    LoweredEntry, LoweredStep, LoweredTail, ValueId, delivered_value_joins,
};
use super::super::drive::{FactKey, Job, JobEffects, current_uses};
use super::super::identity::{ExecutableKey, ExecutableNeed, FunctionId};
use super::super::scheduler::FatalError;
use super::super::semantic::{
    ActivationAnalysis, CallSiteKey, CallSiteSummary, CallableDemand, CallableFlowEdge, CallableFlowFact,
    CallableSurface, ExecutableRuntimeDemand, RuntimeDemand, ShapeDemand, ground_dispatch_surfaces,
};
use super::super::types::{Ty, Types};
use super::super::world::World;
use super::semantic::executable_callsite_needs;

#[derive(Clone)]
struct ExecutableFacts {
    analysis: ActivationAnalysis,
    body: LoweredBody,
    entry_dispatch_inputs: HashSet<usize>,
    callsites: HashMap<CallSiteId, CallSiteSummary>,
    callsite_needs: HashMap<CallSiteId, ExecutableNeed>,
    delivered_value_joins: HashMap<ControlEntryId, DeliveredValueJoin>,
    local_callable_producers: HashMap<ValueId, LocalCallableProducer>,
}

struct DerivedExecutableDemand {
    demand: ExecutableRuntimeDemand,
    call_return_demands: HashMap<CallSiteId, RuntimeDemand>,
    callable_flows: CallableFlowBuilder,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LocalCallableProducer {
    function: FunctionId,
    captures: Box<[ValueId]>,
}

#[derive(Debug, Clone, Default)]
struct CallableFlowBuilder {
    direct_surfaces: HashMap<ValueId, BTreeSet<CallableSurface>>,
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

    fn has_direct_contract(&self, value: ValueId) -> bool {
        self.direct_surfaces
            .get(&value)
            .is_some_and(|surfaces| !surfaces.is_empty())
    }

    fn record_direct_demand(&mut self, facts: &ExecutableFacts, value: ValueId, demand: &RuntimeDemand) {
        self.record_direct_surfaces(facts, value, &demand.callable.resolved);
    }

    fn record_direct_surfaces(
        &mut self,
        facts: &ExecutableFacts,
        value: ValueId,
        surfaces: &BTreeSet<CallableSurface>,
    ) {
        if surfaces.is_empty() {
            return;
        }
        let mut seen = HashSet::new();
        self.record_direct_surfaces_for_value(facts, value, surfaces, &mut seen);
    }

    fn record_first_class_demand(&mut self, facts: &ExecutableFacts, value: ValueId, demand: &RuntimeDemand) {
        if demand.callable.is_first_class() {
            self.record_first_class_surfaces(facts, value, &demand.callable.resolved);
        }
    }

    fn record_first_class_surfaces(
        &mut self,
        facts: &ExecutableFacts,
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
        facts: &ExecutableFacts,
        value: ValueId,
        surfaces: &BTreeSet<CallableSurface>,
        seen: &mut HashSet<ValueId>,
    ) {
        if !seen.insert(value) {
            return;
        }
        if facts.local_callable_producers.contains_key(&value) {
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
        facts: &ExecutableFacts,
        value: ValueId,
        surfaces: &BTreeSet<CallableSurface>,
        seen: &mut HashSet<ValueId>,
    ) {
        if !seen.insert(value) {
            return;
        }
        if facts.local_callable_producers.contains_key(&value) {
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
}

pub(super) fn derive_runtime_demand(
    world: &mut World<'_>,
    executable: &ExecutableKey,
) -> Result<JobEffects, FatalError> {
    let mut reads = Vec::new();
    let mut waits = HashSet::new();
    let mut follow_up = HashSet::new();

    let executable_fact = FactKey::Executable(executable.clone());
    if world.has_fact(&executable_fact) {
        reads.push(executable_fact);
    } else {
        reads.push(executable_fact);
        return Ok(JobEffects {
            reads: current_uses(reads),
            ..JobEffects::default()
        });
    }

    let Some(facts) = collect_one_executable_facts(world, executable, &mut reads, &mut follow_up) else {
        return Ok(JobEffects {
            reads: current_uses(reads),
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    };

    let return_demand_fact = FactKey::ReturnDemand(executable.clone());
    reads.push(return_demand_fact);
    let mut demands = HashMap::new();
    let mut self_demand = world
        .runtime_demand(executable)
        .cloned()
        .unwrap_or_else(|| empty_runtime_demand(executable, world.types()));
    self_demand.return_demand = world.return_demand(executable);
    demands.insert(executable.clone(), self_demand);

    for target in direct_local_targets(&facts) {
        reads.push(FactKey::RuntimeDemand(target.clone()));
        demands.entry(target.clone()).or_insert_with(|| {
            world
                .runtime_demand(&target)
                .cloned()
                .unwrap_or_else(|| empty_runtime_demand(&target, world.types()))
        });
    }
    if let Some(current) = demands.get(executable).cloned() {
        for target in current
            .callable_flows
            .values()
            .flat_map(|flow| flow.resolutions.iter().cloned())
        {
            reads.push(FactKey::RuntimeDemand(target.clone()));
            follow_up.insert(Job::DeriveRuntimeDemand(target.clone()));
            demands.entry(target.clone()).or_insert_with(|| {
                world
                    .runtime_demand(&target)
                    .cloned()
                    .unwrap_or_else(|| empty_runtime_demand(&target, world.types()))
            });
        }
    }

    let mut derived = derive_executable_runtime_demand(world, executable, &facts, &demands);
    let mut return_demand_contributions = call_return_demand_contributions(&facts, derived.call_return_demands);
    derive_callable_flow_facts_for_executable(
        world,
        executable,
        &facts,
        &derived.callable_flows,
        &mut derived.demand,
        &mut reads,
        &mut waits,
        &mut follow_up,
    );
    return_demand_contributions.extend(callable_boundary_return_demand_contributions(
        world,
        &facts,
        &derived.demand,
        &mut reads,
        &mut follow_up,
    ));
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(waits),
            return_demand_contributions,
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    }
    // Seal the published demand to ground dispatch surfaces. Reverse propagation
    // and type-derived boundaries can leave a phantom polymorphic template beside
    // the concrete surface a real call instantiates; a consumer that published a
    // boundary per surface would put several boundaries on one boxed value.
    derived.demand.ground_callable_surfaces(world.types());
    Ok(JobEffects {
        reads: current_uses(reads),
        runtime_demands: vec![(executable.clone(), derived.demand)],
        return_demand_contributions,
        follow_up: follow_up.into_iter().collect(),
        ..JobEffects::default()
    })
}

fn collect_one_executable_facts(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    reads: &mut Vec<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Option<ExecutableFacts> {
    let activation = &executable.activation;
    let analyzed_fact = FactKey::ActivationAnalyzed(activation.clone());
    if !read_settled(world, analyzed_fact, reads) {
        follow_up.insert(Job::AnalyzeActivation(activation.clone()));
        return None;
    }
    let lowered_fact = FactKey::LoweredBody(activation.function);
    if !read_settled(world, lowered_fact, reads) {
        follow_up.insert(Job::LowerFunction(activation.function));
        return None;
    }
    let return_fact = FactKey::ReturnType(activation.clone());
    if !read_settled(world, return_fact, reads) {
        follow_up.insert(Job::AnalyzeActivation(activation.clone()));
        return None;
    }

    let analysis = world
        .activation_analysis(activation)
        .expect("settled activation analysis fact should have analysis")
        .clone();
    let body = world.lowered_body(activation.function);
    let mut callsites = HashMap::new();
    for callsite in &analysis.callsites {
        let key = CallSiteKey {
            activation: activation.clone(),
            callsite: *callsite,
        };
        let callsite_fact = FactKey::CallSiteSummary(key.clone());
        if !read_settled(world, callsite_fact, reads) {
            follow_up.insert(Job::AnalyzeActivation(activation.clone()));
            continue;
        }
        if let Some(summary) = world.callsite_summary(&key).cloned() {
            callsites.insert(*callsite, summary);
        }
    }
    if callsites.len() != analysis.callsites.len() {
        return None;
    }

    let delivered_value_joins = delivered_value_joins(&body);
    let local_callable_producers = local_callable_producers(&body);
    let entry_dispatch_inputs =
        executable_dispatch_input_ordinals(world, activation.function, analysis.reachable_clauses.clone());
    let callsite_needs = executable_callsite_needs(&body, &analysis.reachable_clauses, executable.need);
    Some(ExecutableFacts {
        analysis,
        body,
        entry_dispatch_inputs,
        callsites,
        callsite_needs,
        delivered_value_joins,
        local_callable_producers,
    })
}

fn read_settled(world: &World<'_>, fact: FactKey, reads: &mut Vec<FactKey>) -> bool {
    if world.fact_is_settled(&fact) {
        reads.push(fact);
        true
    } else {
        reads.push(fact);
        false
    }
}

fn empty_runtime_demand(executable: &ExecutableKey, types: &Types) -> ExecutableRuntimeDemand {
    ExecutableRuntimeDemand {
        input_demands: vec![RuntimeDemand::ignore(); executable.activation.input_len(types)],
        ..ExecutableRuntimeDemand::default()
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
    facts: &ExecutableFacts,
    observed_returns: HashMap<CallSiteId, RuntimeDemand>,
) -> Vec<(ExecutableKey, RuntimeDemand)> {
    let mut out = Vec::new();
    for (callsite, observed) in observed_returns {
        let need = facts
            .callsite_needs
            .get(&callsite)
            .copied()
            .unwrap_or(ExecutableNeed::Value);
        let delivered = match need {
            ExecutableNeed::TupleFields(_) => tuple_return_demand_for_observed_need(need, observed),
            ExecutableNeed::Value => {
                if observed.is_ignore() {
                    continue;
                }
                observed
            }
        };
        let Some(summary) = facts.callsites.get(&callsite) else {
            continue;
        };
        out.extend(
            local_call_targets(summary, need)
                .into_iter()
                .map(|target| (target, delivered.clone())),
        );
    }
    out
}

fn tuple_return_demand_for_observed_need(need: ExecutableNeed, observed: RuntimeDemand) -> RuntimeDemand {
    let mut delivered = runtime_demand_for_executable_need(need);
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

fn derive_callable_flow_facts_for_executable(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    callable_flows: &CallableFlowBuilder,
    demand: &mut ExecutableRuntimeDemand,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) {
    demand.callable_flows.clear();
    for (value, producer) in facts.local_callable_producers.clone() {
        let Some(value_demand) = demand.value_demands.get(&value) else {
            continue;
        };
        if !value_demand.is_callable() {
            continue;
        }
        // A `CallableFlowFact` is a runtime fact: every first-class surface it
        // carries names a published boundary contract, so the publication
        // surfaces are grounded to the concrete dispatch shapes the runtime
        // actually invokes (see `ground_dispatch_surfaces`).
        let direct_surfaces = callable_flows.direct_surfaces(value);
        let first_class_surfaces = ground_dispatch_surfaces(
            world.types(),
            &callable_flows.first_class_surfaces(value),
            &direct_surfaces,
        );
        let mut direct_edges = callable_flow_resolution_edges(
            world,
            executable,
            facts,
            &producer,
            &direct_surfaces,
            reads,
            waits,
            follow_up,
        );
        let mut first_class_edges = callable_flow_resolution_edges(
            world,
            executable,
            facts,
            &producer,
            &first_class_surfaces,
            reads,
            waits,
            follow_up,
        );
        // A resolution that is a value-template phantom — a bare-variable
        // activation that a ground sibling resolution already covers — is not a
        // real runtime target (fz-hwn.23), exactly as `ground_dispatch_surfaces`
        // drops a phantom surface beside its ground dispatch. A genuinely
        // polymorphic escape (no ground sibling) is kept: it is boxed, not
        // monomorphized. Drop the phantom so it is never demanded as a latent
        // executable and never reaches the backend.
        let phantoms = phantom_resolution_keys(world, direct_edges.iter().chain(first_class_edges.iter()));
        direct_edges.retain(|edge| !phantoms.contains(&edge.resolution));
        first_class_edges.retain(|edge| !phantoms.contains(&edge.resolution));
        let mut resolutions = Vec::new();
        extend_unique(
            &mut resolutions,
            direct_edges
                .iter()
                .chain(first_class_edges.iter())
                .map(|edge| edge.resolution.clone())
                .collect(),
        );
        demand.callable_flows.insert(
            value,
            CallableFlowFact {
                function: producer.function,
                captures: producer.captures,
                direct_surfaces,
                first_class_surfaces,
                direct_edges,
                first_class_edges,
                opaque: value_demand.callable.opaque,
                escape: value_demand.callable.escape,
                resolutions,
            },
        );
    }
}

fn callable_boundary_return_demand_contributions(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    demand: &ExecutableRuntimeDemand,
    reads: &mut Vec<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Vec<(ExecutableKey, RuntimeDemand)> {
    let mut required = Vec::new();
    for (value, flow) in &demand.callable_flows {
        if flow.first_class_surfaces.is_empty() {
            continue;
        }
        for surface in &flow.first_class_surfaces {
            for resolution in &flow.resolutions {
                let resolution_inputs = resolution.activation.inputs(world.types());
                if resolution.activation.function != flow.function || resolution_inputs.len() < surface.inputs.len() {
                    continue;
                }
                // Match `surface` as the own-surface suffix in the addressed
                // frame: project the suffix past the capture prefix and compare
                // to the canonical surface (fz-hwn.27.6, A; fz-hwn.27.8).
                let captures_len = resolution_inputs.len() - surface.inputs.len();
                let own_surface = world.types_mut().own_surface(&resolution_inputs, captures_len);
                if own_surface != surface.inputs {
                    continue;
                }
                let surface_return_ty = callable_surface_return_ty(world, facts, *value, surface);
                let return_fact = FactKey::ReturnType(resolution.activation.clone());
                reads.push(return_fact.clone());
                let return_fact_settled = world.fact_is_settled(&return_fact);
                let activation_return_ty = world.activation_return(&resolution.activation);
                let surface_demand =
                    surface_return_ty.and_then(|return_ty| informative_boundary_return_demand(world, return_ty));
                let activation_demand =
                    activation_return_ty.and_then(|return_ty| informative_boundary_return_demand(world, return_ty));
                if let Some(demand) = choose_boundary_return_demand(surface_demand, activation_demand) {
                    required.push((resolution.clone(), demand));
                    continue;
                }
                if return_fact_settled
                    && let Some(return_ty) = activation_return_ty.or(surface_return_ty)
                    && !world.types().is_empty(&return_ty)
                    && return_ty != world.types_mut().any()
                {
                    required.push((resolution.clone(), boundary_runtime_demand(world, return_ty)));
                    continue;
                }
                follow_up.insert(Job::AnalyzeActivation(resolution.activation.clone()));
            }
        }
    }
    required
}

fn informative_boundary_return_demand(world: &mut World<'_>, return_ty: Ty) -> Option<RuntimeDemand> {
    if world.types().is_empty(&return_ty) {
        return None;
    }
    let any = world.types_mut().any();
    if return_ty == any {
        return None;
    }
    let demand = boundary_runtime_demand(world, return_ty);
    if !matches!(demand.shape, ShapeDemand::Whole) || !demand.callable.is_empty() {
        return Some(demand);
    }
    (world.types().is_integer(&return_ty)
        || world.types().is_floating(&return_ty)
        || world.types().is_nil(&return_ty)
        || world.types().is_atom_type(&return_ty))
    .then_some(demand)
}

fn choose_boundary_return_demand(
    surface_demand: Option<RuntimeDemand>,
    activation_demand: Option<RuntimeDemand>,
) -> Option<RuntimeDemand> {
    surface_demand.into_iter().chain(activation_demand).next()
}

fn callable_surface_return_ty(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    value: ValueId,
    surface: &CallableSurface,
) -> Option<Ty> {
    let ty = facts.analysis.value_types.get(&value).copied()?;
    world
        .types_mut()
        .callable_value_clauses(&ty)?
        .into_iter()
        .find(|clause| clause.args == surface.inputs)
        .map(|clause| clause.ret)
}

fn local_call_targets(summary: &CallSiteSummary, need: ExecutableNeed) -> Vec<ExecutableKey> {
    summary
        .targets
        .iter()
        .filter_map(|target| {
            target
                .activation
                .clone()
                .map(|activation| ExecutableKey { activation, need })
        })
        .collect()
}

fn executable_dispatch_input_ordinals(
    world: &World<'_>,
    function: FunctionId,
    reachable_clauses: Vec<u32>,
) -> HashSet<usize> {
    match world.lowered_body(function) {
        LoweredBody::Extern { .. } => HashSet::new(),
        LoweredBody::Clauses { .. } => {
            let dispatch =
                crate::compiler2::artifact::ExecutableDispatch::new(world.entry_dispatch(function), reachable_clauses);
            dispatch.required_input_ordinals()
        }
    }
}

fn derive_executable_runtime_demand(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> DerivedExecutableDemand {
    let mut callable_flows = CallableFlowBuilder::new();
    let mut out = ExecutableRuntimeDemand {
        return_demand: demands
            .get(executable)
            .map(|demand| demand.return_demand.clone())
            .unwrap_or_default(),
        input_demands: vec![RuntimeDemand::ignore(); executable.activation.input_len(world.types())],
        ..ExecutableRuntimeDemand::default()
    };
    let mut call_return_demands = HashMap::new();

    let LoweredBody::Clauses { clauses, entries, .. } = &facts.body else {
        out.input_demands = match &facts.body {
            LoweredBody::Extern { signature } => executable
                .activation
                .inputs(world.types())
                .iter()
                .enumerate()
                .map(|(index, ty)| {
                    signature
                        .params
                        .get(index)
                        .map(|_| RuntimeDemand::whole())
                        .unwrap_or_else(|| boundary_runtime_demand(world, *ty))
                })
                .collect(),
            LoweredBody::Clauses { .. } => unreachable!(),
        };
        return DerivedExecutableDemand {
            demand: out,
            call_return_demands,
            callable_flows: CallableFlowBuilder::new(),
        };
    };

    for clause_id in &facts.analysis.reachable_clauses {
        let clause = &clauses[*clause_id as usize];
        let mut live = collect_entry_live_demands(
            world,
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
            world,
            executable,
            clause.projections.as_slice(),
            &mut live,
            facts,
            demands,
            &mut out,
            &mut callable_flows,
        );
        note_clause_matcher_demands(world, facts, clause.projections.as_slice(), &mut live, &mut out);
        for (index, param) in clause.params.iter().enumerate() {
            if let Some(demand) = live.remove(param) {
                out.input_demands[index].join_assign(&demand);
            }
        }
    }

    let activation_inputs = executable.activation.inputs(world.types());
    for &semantic_index in &facts.entry_dispatch_inputs {
        let Some(&ty) = activation_inputs.get(semantic_index) else {
            continue;
        };
        let demand = boundary_runtime_demand(world, ty);
        out.input_demands[semantic_index].join_assign(&demand);
    }

    DerivedExecutableDemand {
        demand: out,
        call_return_demands,
        callable_flows,
    }
}

fn collect_entry_external_demands(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    entry_id: ControlEntryId,
    outgoing_demand: RuntimeDemand,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    callable_flows: &mut CallableFlowBuilder,
) -> HashMap<ValueId, RuntimeDemand> {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut live = collect_entry_live_demands(
        world,
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
        .map(|capture| live.remove(capture).unwrap_or(RuntimeDemand::ignore()))
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
    world: &mut World<'_>,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    entry_id: ControlEntryId,
    outgoing_demand: RuntimeDemand,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
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
                world,
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
            let demand = boundary_value_flow_demand(world, facts, callable_flows, *value, boundary_demand);
            note_live_demand(world, out, &mut live, *value, demand);
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
                world,
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
            let demand = boundary_value_flow_demand(world, facts, callable_flows, *value, boundary_demand);
            note_live_demand(world, out, &mut live, *value, demand.clone());
            record_call_return_demand(call_return_demands, *callsite, demand);
            tail_call_return = Some((*callsite, *value));
            merge_live_demands(&mut live, external_demands);
            let arg_demands = direct_call_arg_demands(
                world,
                executable,
                *callsite,
                args.as_slice(),
                facts,
                demands,
                callable_flows,
            );
            record_call_arg_demands(out, *callsite, arg_demands.as_slice());
            for (arg, demand) in args.iter().zip(arg_demands) {
                note_live_demand(world, out, &mut live, arg.value, demand);
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
                world,
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
            let demand = boundary_value_flow_demand(world, facts, callable_flows, *value, boundary_demand);
            note_live_demand(world, out, &mut live, *value, demand.clone());
            record_call_return_demand(call_return_demands, *callsite, demand);
            tail_call_return = Some((*callsite, *value));
            merge_live_demands(&mut live, external_demands);
            let callee_callable = closure_callee_demand(world, facts, args.as_slice(), facts.callsites.get(callsite));
            callable_flows.record_direct_surfaces(facts, *callee, &callee_callable.resolved);
            let callee_demand = RuntimeDemand::callable(callee_callable);
            note_live_demand(world, out, &mut live, *callee, callee_demand);
            let arg_demands = closure_call_arg_demands(
                world,
                executable,
                *callsite,
                args.as_slice(),
                facts,
                demands,
                callable_flows,
            );
            record_call_arg_demands(out, *callsite, arg_demands.as_slice());
            for (arg, demand) in args.iter().zip(arg_demands) {
                note_live_demand(world, out, &mut live, arg.value, demand);
            }
        }
        LoweredTail::If {
            cond,
            then_entry,
            else_entry,
        } => {
            note_live_demand(world, out, &mut live, *cond, RuntimeDemand::whole());
            merge_live_demands(
                &mut live,
                collect_entry_external_demands(
                    world,
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
                    world,
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
                note_live_demand(world, out, &mut live, *input, RuntimeDemand::whole());
            }
            for value in bindings.pinned.iter().chain(bindings.prepared.iter()) {
                note_live_demand(world, out, &mut live, *value, RuntimeDemand::whole());
            }
            for arm_entry in &dispatch.arm_entries {
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        world,
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
                    world,
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
                note_live_demand(world, out, &mut live, *value, RuntimeDemand::whole());
            }
            for clause in &receive.clauses {
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        world,
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
                note_live_demand(world, out, &mut live, after.timeout, RuntimeDemand::whole());
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        world,
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
        world,
        executable,
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
    world: &mut World<'_>,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    dest: &ControlDestination,
    outgoing_demand: RuntimeDemand,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
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
                world,
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
    facts: &ExecutableFacts,
    callable_flows: &mut CallableFlowBuilder,
    entry: ControlEntryId,
    value: ValueId,
    mut demand: RuntimeDemand,
) -> RuntimeDemand {
    if demand.is_callable() && delivered_join_has_distinct_callable_producers(facts, entry, value) {
        callable_flows.record_direct_surfaces(facts, value, &demand.callable.resolved);
        demand.callable.escape = true;
    }
    demand
}

fn record_delivered_call_return_demands(
    facts: &ExecutableFacts,
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
    facts: &ExecutableFacts,
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
            DeliveredValueSource::LocalValue(value) => facts.local_callable_producers.get(value),
            DeliveredValueSource::CallsiteReturn(_) => None,
        })
        .collect::<HashSet<_>>();
    producers.len() > 1
}

fn propagate_steps_reverse(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    steps: &[LoweredStep],
    live: &mut HashMap<ValueId, RuntimeDemand>,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
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
                        ShapeDemand::TupleFields(fields) if fields.len() == items.len() => {
                            for (item, demand) in items.iter().zip(fields) {
                                let demand = boundary_value_flow_demand(world, facts, callable_flows, *item, demand);
                                note_live_demand(world, out, live, *item, demand);
                            }
                        }
                        _ => {
                            for item in items {
                                let demand = boundary_value_flow_demand(
                                    world,
                                    facts,
                                    callable_flows,
                                    *item,
                                    RuntimeDemand::whole(),
                                );
                                note_live_demand(world, out, live, *item, demand);
                            }
                        }
                    }
                } else {
                    for item in items {
                        let demand =
                            boundary_value_flow_demand(world, facts, callable_flows, *item, RuntimeDemand::whole());
                        note_live_demand(world, out, live, *item, demand);
                    }
                }
            }
            LoweredStep::List { value, items, tail } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for item in items {
                        let demand =
                            boundary_value_flow_demand(world, facts, callable_flows, *item, RuntimeDemand::whole());
                        note_live_demand(world, out, live, *item, demand);
                    }
                    if let Some(tail) = tail {
                        let demand =
                            boundary_value_flow_demand(world, facts, callable_flows, *tail, RuntimeDemand::whole());
                        note_live_demand(world, out, live, *tail, demand);
                    }
                }
            }
            LoweredStep::Map { value, entries } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for (key, field) in entries {
                        let key_demand =
                            boundary_value_flow_demand(world, facts, callable_flows, key.value, RuntimeDemand::whole());
                        let field_demand =
                            boundary_value_flow_demand(world, facts, callable_flows, *field, RuntimeDemand::whole());
                        note_live_demand(world, out, live, key.value, key_demand);
                        note_live_demand(world, out, live, *field, field_demand);
                    }
                }
            }
            LoweredStep::MapUpdate { value, base, entries } => {
                if !take_live_demand(live, *value).is_ignore() {
                    let base_demand =
                        boundary_value_flow_demand(world, facts, callable_flows, *base, RuntimeDemand::whole());
                    note_live_demand(world, out, live, *base, base_demand);
                    for (key, field) in entries {
                        let key_demand =
                            boundary_value_flow_demand(world, facts, callable_flows, key.value, RuntimeDemand::whole());
                        let field_demand =
                            boundary_value_flow_demand(world, facts, callable_flows, *field, RuntimeDemand::whole());
                        note_live_demand(world, out, live, key.value, key_demand);
                        note_live_demand(world, out, live, *field, field_demand);
                    }
                }
            }
            LoweredStep::Struct { value, fields, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for (_, field) in fields {
                        let demand =
                            boundary_value_flow_demand(world, facts, callable_flows, *field, RuntimeDemand::whole());
                        note_live_demand(world, out, live, *field, demand);
                    }
                }
            }
            LoweredStep::Bitstring { value, fields } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for field in fields {
                        note_live_demand(world, out, live, field.value, RuntimeDemand::whole());
                        if let Some(super::super::body::LoweredBitSize::Value(size)) = &field.spec.size {
                            note_live_demand(world, out, live, *size, RuntimeDemand::whole());
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
                        world,
                        executable,
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
                    note_live_demand(world, out, live, *left, RuntimeDemand::whole());
                    note_live_demand(world, out, live, *right, RuntimeDemand::whole());
                }
            }
            LoweredStep::UnaryOp { value, input, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *input, RuntimeDemand::whole());
                }
            }
            LoweredStep::MapIndex { value, base, key } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *base, RuntimeDemand::whole());
                    note_live_demand(world, out, live, key.value, RuntimeDemand::whole());
                }
            }
            LoweredStep::FieldAccess { value, base, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *base, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertLiteral { source, .. } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::AssertStruct { source, .. } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::RequireMapValue { value, source, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertTuple { source, arity } => {
                if !live.contains_key(source) || asserted_tuple_arities.get(source).copied() != Some(*arity) {
                    note_live_demand(world, out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::TupleField { value, source, index } => {
                let demand = take_live_demand(live, *value);
                if !demand.is_ignore() {
                    let arity = asserted_tuple_arities.get(source).copied().unwrap_or(index + 1);
                    let mut fields = vec![RuntimeDemand::ignore(); arity];
                    fields[*index] = demand;
                    note_live_demand(world, out, live, *source, RuntimeDemand::tuple_fields(fields));
                }
            }
            LoweredStep::AssertEmptyList { source } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::AssertSame { source, value } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::whole());
                note_live_demand(world, out, live, *value, RuntimeDemand::whole());
            }
            LoweredStep::SplitList { source, head, tail } => {
                let head_demand = take_live_demand(live, *head);
                let tail_demand = take_live_demand(live, *tail);
                if !head_demand.is_ignore() || !tail_demand.is_ignore() {
                    note_live_demand(world, out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::BitstringInit { reader, source } => {
                if !take_live_demand(live, *reader).is_ignore() {
                    note_live_demand(world, out, live, *source, RuntimeDemand::whole());
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
                    note_live_demand(world, out, live, *reader, RuntimeDemand::whole());
                    if let Some(super::super::body::LoweredBitSize::Value(size)) = &spec.size {
                        note_live_demand(world, out, live, *size, RuntimeDemand::whole());
                    }
                }
            }
            LoweredStep::AssertBitstringDone { reader } => {
                note_live_demand(world, out, live, *reader, RuntimeDemand::whole());
            }
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
    world: &mut World<'_>,
    facts: &ExecutableFacts,
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
                let demand = boundary_value_demand(world, facts, *source, RuntimeDemand::whole());
                note_live_demand(world, out, live, *source, demand);
            }
            LoweredStep::RequireMapValue { source, .. } => {
                let source_demand = boundary_value_demand(world, facts, *source, RuntimeDemand::whole());
                note_live_demand(world, out, live, *source, source_demand);
            }
            LoweredStep::AssertSame { source, value } => {
                let source_demand = boundary_value_demand(world, facts, *source, RuntimeDemand::whole());
                note_live_demand(world, out, live, *source, source_demand);
                let value_demand = boundary_value_demand(world, facts, *value, RuntimeDemand::whole());
                note_live_demand(world, out, live, *value, value_demand);
            }
            LoweredStep::SplitList { source, .. } => {
                let demand = boundary_value_demand(world, facts, *source, RuntimeDemand::whole());
                note_live_demand(world, out, live, *source, demand);
            }
            LoweredStep::BitstringRead { reader, spec, .. } => {
                let demand = boundary_value_demand(world, facts, *reader, RuntimeDemand::whole());
                note_live_demand(world, out, live, *reader, demand);
                if let Some(super::super::body::LoweredBitSize::Value(size)) = &spec.size {
                    note_live_demand(world, out, live, *size, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertBitstringDone { reader } => {
                let demand = boundary_value_demand(world, facts, *reader, RuntimeDemand::whole());
                note_live_demand(world, out, live, *reader, demand);
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
    world: &mut World<'_>,
    executable: &ExecutableKey,
    function: FunctionId,
    captures: &[ValueId],
    demand: RuntimeDemand,
    facts: &ExecutableFacts,
    all_demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    live: &mut HashMap<ValueId, RuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
    callable_flows: &mut CallableFlowBuilder,
) {
    if !demand.is_callable() {
        for capture in captures {
            note_live_demand(world, out, live, *capture, RuntimeDemand::whole());
        }
        return;
    }
    let callable = demand.callable;
    let capture_types = captures
        .iter()
        .map(|capture| facts.analysis.value_types.get(capture).copied())
        .collect::<Option<Vec<_>>>();
    let Some(capture_types) = capture_types else {
        for capture in captures {
            let demand = closure_capture_boundary_demand(
                world,
                facts,
                callable_flows,
                *capture,
                RuntimeDemand::whole(),
                &callable,
            );
            note_live_demand(world, out, live, *capture, demand);
        }
        return;
    };
    // The captured values' demands live in the producer's own executable, in the
    // input-demand prefix that precedes its parameters. The closure's call
    // surfaces only select *which* specialization to read: a directly-called
    // closure restricts to the invoked surfaces, but an escaped closure — one
    // returned or stored rather than called here — carries no direct surface
    // (`resolved` is empty) even though its body still proves how it invokes each
    // capture (e.g. a returned `fn () -> f.(1) end` calls `f` at `(int)`). Reading
    // the producer executable by capture-type prefix recovers that proven surface;
    // gating on a non-empty `resolved` would discard it and let `f` reach
    // transport as a surface-less first-class demand.
    // A callee activation key is the whole-scope addressed arrow of
    // `capture_tys ++ own_surface`. Match in that addressed frame (fz-hwn.27.6,
    // A): by the left-to-right property the addressed capture prefix is just the
    // captures addressed alone, and re-addressing the own-surface suffix
    // standalone yields the same canonical surface the resolved set carries.
    let addressed_captures = world.types_mut().address_inputs(&capture_types);
    let mut matched = false;
    for (callee, callee_demand) in all_demands {
        if callee.activation.root != executable.activation.root || callee.activation.function != function {
            continue;
        }
        let callee_inputs = callee.activation.inputs(world.types());
        let Some(own_params) = world
            .types_mut()
            .own_surface_past_captures(&callee_inputs, &addressed_captures)
        else {
            continue;
        };
        if !callable.resolved.is_empty() && !callable.resolved.iter().any(|surface| surface.inputs == own_params) {
            continue;
        }
        matched = true;
        for (capture, demand) in captures.iter().zip(callee_demand.input_demands.iter()) {
            callable_flows.record_direct_surfaces(facts, *capture, &demand.callable.resolved);
            let demand =
                closure_capture_boundary_demand(world, facts, callable_flows, *capture, demand.clone(), &callable);
            note_live_demand(world, out, live, *capture, demand);
        }
    }
    if !matched {
        for capture in captures {
            let demand = closure_capture_boundary_demand(
                world,
                facts,
                callable_flows,
                *capture,
                RuntimeDemand::whole(),
                &callable,
            );
            note_live_demand(world, out, live, *capture, demand);
        }
    }
}

fn closure_capture_boundary_demand(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    callable_flows: &mut CallableFlowBuilder,
    capture: ValueId,
    demand: RuntimeDemand,
    closure: &CallableDemand,
) -> RuntimeDemand {
    if demand.shape == ShapeDemand::Whole
        && !demand.is_callable()
        && value_is_callable(world, facts, capture)
        && let Some(direct) = direct_only_capture_callable_demand(world, facts, capture, closure)
    {
        callable_flows.record_direct_demand(facts, capture, &direct);
        return direct;
    }
    let mut upgraded = boundary_value_demand(world, facts, capture, demand);
    if upgraded.is_callable() {
        let has_direct_contract = !upgraded.callable.resolved.is_empty() || callable_flows.has_direct_contract(capture);
        if !has_direct_contract {
            upgraded.callable.opaque |= closure.opaque;
            upgraded.callable.escape |= closure.escape;
        }
        record_first_class_boundary_demand(world, facts, callable_flows, capture, upgraded.clone(), None);
    }
    upgraded
}

fn callable_value_type_demand(world: &mut World<'_>, facts: &ExecutableFacts, value: ValueId) -> Option<RuntimeDemand> {
    let ty = facts.analysis.value_types.get(&value).copied()?;
    let mut callable = CallableDemand::default();
    for clause in world.types_mut().callable_value_clauses(&ty)? {
        callable.join_assign(&CallableDemand::resolved(clause.args, world.types_mut()));
    }
    (!callable.resolved.is_empty()).then(|| RuntimeDemand::callable(callable))
}

fn direct_only_capture_callable_demand(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    value: ValueId,
    closure: &CallableDemand,
) -> Option<RuntimeDemand> {
    let type_demand = callable_value_type_demand(world, facts, value)?;
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
        opaque: false,
        escape: false,
    }))
}

fn direct_call_arg_demands(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    callable_flows: &mut CallableFlowBuilder,
) -> Vec<RuntimeDemand> {
    arg_demands_for_summary(world, executable, callsite, args, 0, facts, demands, callable_flows)
}

fn closure_call_arg_demands(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    callable_flows: &mut CallableFlowBuilder,
) -> Vec<RuntimeDemand> {
    arg_demands_for_summary(world, executable, callsite, args, 0, facts, demands, callable_flows)
}

fn arg_demands_for_summary(
    world: &mut World<'_>,
    _executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    default_offset: usize,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    callable_flows: &mut CallableFlowBuilder,
) -> Vec<RuntimeDemand> {
    let arity = args.len();
    let mut out = vec![RuntimeDemand::ignore(); arity];
    let Some(summary) = facts.callsites.get(&callsite) else {
        return args
            .iter()
            .map(|arg| boundary_value_flow_demand(world, facts, callable_flows, arg.value, RuntimeDemand::whole()))
            .collect();
    };
    let need = facts
        .callsite_needs
        .get(&callsite)
        .copied()
        .unwrap_or(ExecutableNeed::Value);
    for target in &summary.targets {
        let records_direct_arg_surfaces = match target.callee {
            super::super::semantic::SelectedCallee::Function(function) => {
                target.activation.is_some() && !matches!(world.lowered_body(function), LoweredBody::Extern { .. })
            }
            super::super::semantic::SelectedCallee::ProviderBoundary(_) => false,
        };
        let target_demands = local_target_input_demands(world, target, need, demands);
        let offset = target
            .activation
            .as_ref()
            .map(|activation| {
                activation
                    .input_len(world.types())
                    .saturating_sub(target.surface_inputs.len())
            })
            .unwrap_or(default_offset);
        for (index, (arg, slot)) in args.iter().zip(out.iter_mut()).enumerate().take(arity) {
            let fallback_ty = target
                .surface_inputs
                .get(index)
                .copied()
                .unwrap_or_else(|| world.types_mut().any());
            let observed = target_demands
                .get(offset + index)
                .cloned()
                .unwrap_or_else(|| boundary_runtime_demand(world, fallback_ty));
            if records_direct_arg_surfaces {
                let direct_surfaces =
                    callable_surfaces_for_ty(world, fallback_ty).unwrap_or_else(|| observed.callable.resolved.clone());
                callable_flows.record_direct_surfaces(facts, arg.value, &direct_surfaces);
            }
            let mut observed =
                boundary_value_flow_demand_at(world, facts, callable_flows, arg.value, observed, fallback_ty);
            if !records_direct_arg_surfaces {
                ground_first_class_callable_surface(world, &mut observed, fallback_ty);
            }
            slot.join_assign(&observed);
        }
    }
    out
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
/// can only ascend across fixpoint rounds.
fn ground_first_class_callable_surface(world: &mut World<'_>, demand: &mut RuntimeDemand, boundary_ty: Ty) {
    if !demand.callable.is_first_class() {
        return;
    }
    let Some(clauses) = world.types_mut().callable_clauses(&boundary_ty) else {
        return;
    };
    demand.callable.resolved.extend(
        clauses
            .into_iter()
            .map(|clause| CallableSurface::new(clause.args, world.types_mut())),
    );
}

fn callable_surfaces_for_ty(world: &mut World<'_>, ty: Ty) -> Option<BTreeSet<CallableSurface>> {
    let clauses = world.types_mut().callable_clauses(&ty)?;
    let surfaces = clauses
        .into_iter()
        .map(|clause| CallableSurface::new(clause.args, world.types_mut()))
        .collect::<BTreeSet<_>>();
    (!surfaces.is_empty()).then_some(surfaces)
}

fn local_target_input_demands(
    world: &mut World<'_>,
    target: &super::super::semantic::CallTargetSummary,
    need: ExecutableNeed,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
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
                .map(|ty| boundary_runtime_demand(world, ty))
                .collect()
        }
        super::super::semantic::SelectedCallee::Function(function) => {
            if let LoweredBody::Extern { signature } = world.lowered_body(function) {
                return target
                    .surface_inputs
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| {
                        signature
                            .params
                            .get(index)
                            .map(|_| RuntimeDemand::whole())
                            .unwrap_or_else(|| boundary_runtime_demand(world, *ty))
                    })
                    .collect();
            }
            let Some(activation) = target.activation.clone() else {
                return target
                    .surface_inputs
                    .iter()
                    .copied()
                    .map(|ty| boundary_runtime_demand(world, ty))
                    .collect();
            };
            demands
                .get(&ExecutableKey { activation, need })
                .map(|demand| demand.input_demands.clone())
                .unwrap_or_else(|| {
                    vec![RuntimeDemand::ignore(); target.activation.as_ref().map_or(0, |a| a.input_len(world.types()))]
                })
        }
    }
}

fn boundary_runtime_demand(world: &mut World<'_>, ty: Ty) -> RuntimeDemand {
    let Some(clauses) = world.types_mut().callable_clauses(&ty) else {
        if let Some(fields) = exact_tuple_field_tys(world, ty) {
            return RuntimeDemand::tuple_fields(
                fields
                    .into_iter()
                    .map(|field_ty| boundary_runtime_demand(world, field_ty))
                    .collect(),
            );
        }
        return RuntimeDemand::whole();
    };
    // A callable crossing a boundary escapes as a first-class value. Carry the
    // boundary's settled surface so callable-flow derivation keys the escaping
    // body at those exact argument lanes.
    let resolved = clauses
        .into_iter()
        .map(|clause| CallableSurface::new(clause.args, world.types_mut()))
        .collect::<BTreeSet<_>>();
    RuntimeDemand::callable(CallableDemand {
        resolved,
        opaque: false,
        escape: true,
    })
}

fn exact_tuple_field_tys(world: &mut World<'_>, ty: Ty) -> Option<Vec<Ty>> {
    let predicate = world.types().runtime_type_predicate(&ty);
    if predicate.tuple_arities.cofinite || predicate.tuple_arities.values.len() != 1 {
        return None;
    }
    let arity = *predicate.tuple_arities.values.iter().next()?;
    Some(tuple_field_tys(world, ty, arity))
}

fn tuple_field_tys(world: &mut World<'_>, ty: Ty, arity: usize) -> Vec<Ty> {
    let any = world.types_mut().any();
    let mut fields = world.types_mut().tuple_projections(&ty, arity);
    if fields.len() < arity {
        fields.resize(arity, any);
    } else if fields.len() > arity {
        fields.truncate(arity);
    }
    fields
}

fn value_is_callable(world: &mut World<'_>, facts: &ExecutableFacts, value: ValueId) -> bool {
    facts
        .analysis
        .value_types
        .get(&value)
        .copied()
        .is_some_and(|ty| world.types_mut().callable_clauses(&ty).is_some())
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
fn boundary_value_demand(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    value: ValueId,
    mut demand: RuntimeDemand,
) -> RuntimeDemand {
    if demand.shape == ShapeDemand::Whole && !demand.is_callable() && value_is_callable(world, facts, value) {
        demand.callable.join_assign(&CallableDemand::escaped());
    }
    demand
}

fn boundary_value_flow_demand(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    callable_flows: &mut CallableFlowBuilder,
    value: ValueId,
    demand: RuntimeDemand,
) -> RuntimeDemand {
    let demand = boundary_value_demand(world, facts, value, demand);
    record_first_class_boundary_demand(world, facts, callable_flows, value, demand, None)
}

fn boundary_value_flow_demand_at(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    callable_flows: &mut CallableFlowBuilder,
    value: ValueId,
    demand: RuntimeDemand,
    boundary_ty: Ty,
) -> RuntimeDemand {
    let demand = boundary_value_demand(world, facts, value, demand);
    record_first_class_boundary_demand(world, facts, callable_flows, value, demand, Some(boundary_ty))
}

fn record_first_class_boundary_demand(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    callable_flows: &mut CallableFlowBuilder,
    value: ValueId,
    demand: RuntimeDemand,
    boundary_ty: Option<Ty>,
) -> RuntimeDemand {
    if demand.callable.is_first_class() {
        let mut recorded = RuntimeDemand::callable(CallableDemand {
            resolved: BTreeSet::new(),
            opaque: demand.callable.opaque,
            escape: demand.callable.escape,
        });
        if let Some(ty) = boundary_ty.or_else(|| facts.analysis.value_types.get(&value).copied()) {
            ground_first_class_callable_surface(world, &mut recorded, ty);
        }
        if boundary_ty.is_none() {
            // No boundary type to ground against: seed the escaping surfaces from
            // the value's concrete call shapes. The publication surfaces are
            // grounded once, downstream, in `ground_dispatch_surfaces`.
            recorded.callable.resolved.extend(callable_flows.direct_surfaces(value));
        }
        callable_flows.record_first_class_demand(facts, value, &recorded);
    }
    demand
}

fn closure_callee_demand(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    args: &[CallArg],
    summary: Option<&CallSiteSummary>,
) -> CallableDemand {
    let Some(summary) = summary else {
        let mut demand = CallableDemand {
            resolved: Default::default(),
            opaque: true,
            escape: false,
        };
        let inputs: Vec<Ty> = args
            .iter()
            .map(|arg| {
                facts
                    .analysis
                    .value_types
                    .get(&arg.value)
                    .copied()
                    .unwrap_or_else(|| world.types_mut().any())
            })
            .collect();
        demand.resolved.insert(CallableSurface::new(inputs, world.types_mut()));
        return demand;
    };
    let mut demand = CallableDemand::default();
    for target in &summary.targets {
        demand.join_assign(&CallableDemand::resolved(
            target.surface_inputs.clone(),
            world.types_mut(),
        ));
    }
    let exact_local_target = matches!(
        summary.targets.as_slice(),
        [target]
            if matches!(target.callee, super::super::semantic::SelectedCallee::Function(_))
                && target.activation.is_some()
    );
    if !exact_local_target {
        demand.opaque = true;
    }
    demand
}

fn runtime_demand_for_executable_need(need: ExecutableNeed) -> RuntimeDemand {
    match need {
        ExecutableNeed::Value => RuntimeDemand::whole(),
        ExecutableNeed::TupleFields(arity) => RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(); arity]),
    }
}

pub(super) fn demanded_callable_executables(
    executables: &HashSet<ExecutableKey>,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> HashSet<ExecutableKey> {
    let mut latent = HashSet::new();
    for executable in executables {
        let demand = demands
            .get(executable)
            .expect("runtime demand closure should produce a plan for every executable");
        for flow in demand.callable_flows.values() {
            if flow.direct_surfaces.is_empty() && flow.first_class_surfaces.is_empty() && !flow.escape && !flow.opaque {
                continue;
            }
            latent.extend(flow.resolutions.iter().cloned());
        }
    }
    latent
}

fn callable_flow_resolutions(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    producer: &LocalCallableProducer,
    surfaces: &BTreeSet<CallableSurface>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Vec<ExecutableKey> {
    if surfaces.is_empty() {
        return Vec::new();
    }
    if !world.require_activation_key_facts(producer.function, reads, waits, follow_up) {
        return Vec::new();
    }
    let Some(capture_tys) = producer
        .captures
        .iter()
        .copied()
        .map(|capture| facts.analysis.value_types.get(&capture).copied())
        .collect::<Option<Vec<_>>>()
    else {
        return Vec::new();
    };
    let root = executable.activation.root;
    let captures_len = capture_tys.len();
    surfaces
        .iter()
        .map(|surface| {
            // A boxed callable resolves at runtime to its GROUND instances, never
            // to the dead generic activation whose body cannot materialize an
            // unrepresentable parameter (fz-hwn.23). When this call surface grounds
            // to a representable sibling elsewhere in the root, point the resolution
            // at that real instance; the local flow has no ground evidence (the
            // generic activation never sees a concrete element), so the sibling
            // search is whole-root. Captures are threaded through unchanged — they
            // carry the callable's identity. A genuine escape with no ground
            // sibling keeps its template and is lowered boxed.
            let surface_inputs = world
                .ground_surface_for_template(root, producer.function, captures_len, &surface.inputs)
                .unwrap_or_else(|| surface.inputs.clone());
            let mut inputs = capture_tys.clone();
            inputs.extend(surface_inputs);
            ExecutableKey {
                activation: world.activation_key(root, producer.function, &inputs),
                need: ExecutableNeed::Value,
            }
        })
        .collect()
}

fn callable_flow_resolution_edges(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    producer: &LocalCallableProducer,
    surfaces: &BTreeSet<CallableSurface>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Vec<CallableFlowEdge> {
    let resolutions = callable_flow_resolutions(world, executable, facts, producer, surfaces, reads, waits, follow_up);
    surfaces
        .iter()
        .cloned()
        .zip(resolutions)
        .map(|(surface, resolution)| CallableFlowEdge { surface, resolution })
        .collect()
}

/// Value-template resolutions that a ground sibling already covers — phantoms in
/// the sense of [`ground_dispatch_surfaces`], lifted to the executable level. A
/// resolution whose activation carries a bare-variable argument is a runtime
/// non-fact when another resolution of the same function and need has concrete
/// inputs that instantiate it; the boxed call resolves to the ground sibling, so
/// the template must not be demanded as a latent executable (fz-hwn.23). With no
/// ground sibling the template is a genuinely polymorphic escape and stays.
fn phantom_resolution_keys<'a>(
    world: &World<'_>,
    edges: impl Iterator<Item = &'a CallableFlowEdge>,
) -> HashSet<ExecutableKey> {
    let types = world.types();
    let resolutions: Vec<(ExecutableKey, Vec<Ty>)> = edges
        .map(|edge| {
            let inputs = edge.resolution.activation.inputs(types);
            (edge.resolution.clone(), inputs)
        })
        .collect();
    let ground: Vec<&(ExecutableKey, Vec<Ty>)> = resolutions
        .iter()
        .filter(|(_, inputs)| !types.key_has_vars(inputs))
        .collect();
    resolutions
        .iter()
        .filter(|(key, inputs)| {
            types.key_is_value_template(inputs)
                && ground.iter().any(|(candidate, candidate_inputs)| {
                    candidate.need == key.need
                        && candidate.activation.function == key.activation.function
                        && types.key_list_subsumes(candidate_inputs, inputs)
                })
        })
        .map(|(key, _)| key.clone())
        .collect()
}

fn extend_unique<T: PartialEq>(target: &mut Vec<T>, values: Vec<T>) {
    for value in values {
        if !target.contains(&value) {
            target.push(value);
        }
    }
}

fn local_callable_producers(body: &LoweredBody) -> HashMap<ValueId, LocalCallableProducer> {
    let mut producers = HashMap::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return producers;
    };
    for clause in clauses {
        for step in &clause.projections {
            if let Some((value, producer)) = step_local_callable_producer(step) {
                producers.insert(value, producer);
            }
        }
    }
    for entry in entries {
        for step in &entry.steps {
            if let Some((value, producer)) = step_local_callable_producer(step) {
                producers.insert(value, producer);
            }
        }
    }
    producers
}

fn step_local_callable_producer(step: &LoweredStep) -> Option<(ValueId, LocalCallableProducer)> {
    match step {
        LoweredStep::FunctionRef { value, function } => Some((
            *value,
            LocalCallableProducer {
                function: *function,
                captures: Box::default(),
            },
        )),
        LoweredStep::Lambda {
            value,
            function,
            captures,
        } => Some((
            *value,
            LocalCallableProducer {
                function: *function,
                captures: captures.clone().into_boxed_slice(),
            },
        )),
        _ => None,
    }
}

fn note_live_demand(
    _world: &mut World<'_>,
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
