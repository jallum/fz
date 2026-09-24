use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use super::super::artifact::{AbiValueRepr, ClosureCallEdge};
use super::super::body::{
    CallSiteId, ControlDestination, ControlEntryId, LoweredBody, LoweredTail, ValueId, callsite_call_args,
    callsite_input_modes,
};
use super::super::drive::FactKey;
use super::super::executable_facts::{ExecutableFacts, LocalCallableProducer, TransportOrigin as TransportSource};
use super::super::facts::FactUse;
use super::super::identity::{
    ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, RootId, function_id_of_closure_target,
};
use super::super::incoming_inputs::InputSlot;
use super::super::pull::{
    ProductKey, ProductReadContext, ProductValue, PullOutcome, PullWait, TransportCarrier, TransportLayout,
    TransportShapeFact,
};
use super::super::semantic::{
    CallSiteSummary, CallTargetSummary, CallableDemand, CallableFlowFact, CallableSurface, CallableTarget,
    ExecutableRuntimeDemand, RuntimeDemand, SelectedCallee, SemanticOrd, ShapeDemand,
};
use super::super::transport::{
    BoundaryDescr, BoundaryFacts, BoundaryId, CallableAlternative, CallableConstructionCapture,
    CallableConstructionFact, CallableConstructionMember, CallableConstructionOwner, CallableDescr, CallableDirectEdge,
    CallableFacts, CallableId, ExecutableSymbol, LaneId, ShapeDescr, ShapeId, TransportClass, TransportPosition,
};
use super::super::types::{Ty, Types};
use super::super::world::World;

#[derive(Debug, Clone, PartialEq, Eq)]
struct CallableFactsDraft {
    resolutions: Vec<ExecutableSymbol>,
    direct_surfaces: Vec<Box<[ShapeId]>>,
    direct_edges: Vec<CallableDirectEdge>,
    boundary_ids: Vec<BoundaryId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BoundaryFactsDraft {
    publications: Vec<TransportPosition>,
    resolutions: Vec<ExecutableSymbol>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct TransportFactsBuilder {
    callables: HashMap<CallableId, CallableFactsDraft>,
    boundaries: HashMap<BoundaryId, BoundaryFactsDraft>,
}

impl TransportFactsBuilder {
    fn merge_owner(&mut self, owner: &CallableConstructionOwner) {
        for (callable, facts) in &owner.callable_facts {
            self.record_callable(
                *callable,
                facts.resolutions.to_vec(),
                facts.direct_surfaces.to_vec(),
                facts.direct_edges.to_vec(),
                facts.boundary_ids.to_vec(),
            );
        }
        for (boundary, facts) in &owner.boundary_facts {
            for publication in facts.publications.iter().cloned() {
                self.record_boundary(*boundary, publication);
            }
            self.record_boundary_resolutions(*boundary, facts.resolutions.to_vec());
        }
    }

    fn record_callable(
        &mut self,
        callable: CallableId,
        resolutions: Vec<ExecutableSymbol>,
        direct_surfaces: Vec<Box<[ShapeId]>>,
        direct_edges: Vec<CallableDirectEdge>,
        boundary_ids: Vec<BoundaryId>,
    ) {
        let entry = self.callables.entry(callable).or_insert_with(|| CallableFactsDraft {
            resolutions: Vec::new(),
            direct_surfaces: Vec::new(),
            direct_edges: Vec::new(),
            boundary_ids: Vec::new(),
        });
        extend_unique(&mut entry.resolutions, resolutions);
        extend_unique(&mut entry.direct_surfaces, direct_surfaces);
        extend_unique(&mut entry.direct_edges, direct_edges);
        extend_unique(&mut entry.boundary_ids, boundary_ids);
    }

    fn record_boundary(&mut self, boundary: BoundaryId, publication: TransportPosition) {
        let entry = self.boundaries.entry(boundary).or_insert_with(|| BoundaryFactsDraft {
            publications: Vec::new(),
            resolutions: Vec::new(),
        });
        if !entry.publications.contains(&publication) {
            entry.publications.push(publication);
        }
    }

    fn record_boundary_resolutions(&mut self, boundary: BoundaryId, resolutions: Vec<ExecutableSymbol>) {
        let entry = self.boundaries.entry(boundary).or_insert_with(|| BoundaryFactsDraft {
            publications: Vec::new(),
            resolutions: Vec::new(),
        });
        extend_unique(&mut entry.resolutions, resolutions);
    }

    /// Fold another fact set into this one. The fact builder is an additive,
    /// idempotent monoid -- every `record_*` only ever unions entries in -- so
    /// committing a speculatively-explored subtree is `self ∪ delta`, never a
    /// structural overwrite. This is what replaces the old "snapshot the whole
    /// builder, then `*facts = staged` or drop it" rollback: a dead branch is
    /// discarded by simply not merging its delta. Taken by reference so a cached
    /// delta can be re-merged on every memo hit without being consumed.
    fn merge(&mut self, other: &TransportFactsBuilder) {
        for (callable, draft) in &other.callables {
            self.record_callable(
                *callable,
                draft.resolutions.clone(),
                draft.direct_surfaces.clone(),
                draft.direct_edges.clone(),
                draft.boundary_ids.clone(),
            );
        }
        for (boundary, draft) in &other.boundaries {
            for publication in &draft.publications {
                self.record_boundary(*boundary, publication.clone());
            }
            self.record_boundary_resolutions(*boundary, draft.resolutions.clone());
        }
    }

    fn finish(self, types: &Types) -> (HashMap<CallableId, CallableFacts>, HashMap<BoundaryId, BoundaryFacts>) {
        let callables = self
            .callables
            .into_iter()
            .map(|(id, mut draft)| {
                draft.resolutions.sort_by(|left, right| left.semantic_cmp(right, types));
                draft
                    .direct_surfaces
                    .sort_by_cached_key(|surface| surface.iter().map(|shape| shape.as_u32()).collect::<Vec<_>>());
                draft
                    .direct_edges
                    .sort_by(|left, right| compare_callable_direct_edges(left, right, types));
                draft.boundary_ids.sort_by_key(|boundary| boundary.as_u32());
                (
                    id,
                    CallableFacts {
                        resolutions: draft.resolutions.into_boxed_slice(),
                        direct_surfaces: draft.direct_surfaces.into_boxed_slice(),
                        direct_edges: draft.direct_edges.into_boxed_slice(),
                        boundary_ids: draft.boundary_ids.into_boxed_slice(),
                    },
                )
            })
            .collect();
        let boundaries = self
            .boundaries
            .into_iter()
            .map(|(id, mut draft)| {
                draft
                    .publications
                    .sort_by(|left, right| left.semantic_cmp(right, types));
                draft.resolutions.sort_by(|left, right| left.semantic_cmp(right, types));
                (
                    id,
                    BoundaryFacts {
                        publications: draft.publications.into_boxed_slice(),
                        resolutions: draft.resolutions.into_boxed_slice(),
                    },
                )
            })
            .collect();
        (callables, boundaries)
    }
}

pub(crate) fn produce_transport_shape_product(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    position: &TransportPosition,
) -> PullOutcome {
    let executable = executable_key_for_transport_position(context.session().root(), position);
    if let Some(outcome) = produce_named_transport_position(world, tel, context, &executable, position) {
        return outcome;
    }
    let layout = TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing));
    PullOutcome::Produced(ProductValue::TransportShape(TransportShapeFact::Layout(layout)))
}

pub(crate) fn produce_callable_construction_product(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    position: &TransportPosition,
) -> PullOutcome {
    let executable = executable_key_for_transport_position(context.session().root(), position);
    let facts = context.read_executable_facts(world, &executable);
    let runtime = context.read_runtime_demand_fact(world, &executable);
    let mut waits = Vec::new();
    if facts.is_none() {
        waits.push(PullWait::Fact(FactUse::settled(FactKey::ExecutableFacts(
            executable.clone(),
        ))));
    }
    if runtime.is_none() {
        waits.push(PullWait::Fact(FactUse::settled(FactKey::RuntimeDemand(
            executable.clone(),
        ))));
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let facts = facts.expect("executable-facts wait should have been satisfied");
    let runtime = runtime.expect("runtime-demand wait should have been satisfied");
    let Some((value, producer, flow)) = local_callable_construction(&facts, &runtime, position) else {
        return produce_generic_callable_owner(world, tel, context, &executable, facts.as_ref(), &runtime, position);
    };
    let demand = runtime.value_demands.get(&value).cloned().unwrap_or_default();
    match produce_local_callable_construction(
        world,
        tel,
        context,
        &executable,
        facts.as_ref(),
        value,
        producer,
        flow,
        demand,
    ) {
        Ok(answer) => PullOutcome::Produced(ProductValue::CallableConstruction(Rc::new(answer))),
        Err(waits) => PullOutcome::Waiting(waits),
    }
}

pub(crate) fn local_callable_construction<'a>(
    facts: &'a ExecutableFacts,
    runtime: &'a ExecutableRuntimeDemand,
    position: &TransportPosition,
) -> Option<(ValueId, &'a LocalCallableProducer, &'a CallableFlowFact)> {
    let TransportPosition::Value { value, .. } = position else {
        return None;
    };
    let TransportSource::CallableValue(producer) = facts.value_origin(*value)? else {
        return None;
    };
    Some((*value, producer, runtime.callable_flows.get(value)?))
}

fn produce_generic_callable_owner(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    runtime: &ExecutableRuntimeDemand,
    position: &TransportPosition,
) -> PullOutcome {
    let shape_key = ProductKey::TransportShape(position.clone());
    let mut waits = Vec::new();
    if let TransportPosition::ExecutableInput { semantic_index, .. } = position
        && runtime
            .input_demands
            .get(*semantic_index)
            .is_some_and(demand_contains_callable)
    {
        let fact = FactUse::settled(FactKey::IncomingInputSlot(InputSlot {
            executable: executable.clone(),
            semantic_index: *semantic_index,
        }));
        if !context.read_fact(world, fact.clone()) {
            waits.push(PullWait::Fact(fact));
        }
    }
    let layout = match context.read_product(tel, shape_key.clone(), world.types()) {
        Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => Some(*layout),
        Some(value) => panic!("transport shape produced unexpected value {value:?}"),
        None => {
            waits.push(PullWait::Product(shape_key));
            None
        }
    };
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let layout = layout.expect("shape wait must be satisfied");
    if matches!(world.shape(layout.structural), ShapeDescr::Nothing) {
        return PullOutcome::Produced(ProductValue::CallableConstruction(Rc::new(CallableConstructionOwner {
            layout,
            construction: None,
            callable_facts: HashMap::new(),
            boundary_facts: HashMap::new(),
        })));
    }
    if let Some(fact) = generic_owner_ty_fact(executable, position) {
        let fact = FactUse::settled(fact);
        if !context.read_fact(world, fact.clone()) {
            return PullOutcome::wait_on_fact(fact);
        }
    }
    let (ty, demand) = generic_owner_ty_and_demand(world, executable, facts, runtime, position);
    let mut source_positions = Vec::new();
    if demand_contains_callable(&demand) {
        match position {
            TransportPosition::ExecutableInput { semantic_index, .. } => {
                let slot = InputSlot {
                    executable: executable.clone(),
                    semantic_index: *semantic_index,
                };
                let sources = world
                    .incoming_input_sources(&slot)
                    .expect("settled input slot has an authoritative answer");
                source_positions.extend(sources.iter().map(|source| TransportPosition::Value {
                    executable: ExecutableSymbol::from_key(&source.producer),
                    value: source.value,
                }));
            }
            TransportPosition::Value { value, .. } => {
                if let Some(origin) = facts.value_origin(*value)
                    && !append_origin_children(position.executable(), facts, origin, &mut source_positions)
                {
                    source_positions.clear();
                }
            }
            TransportPosition::ExecutableReturn { .. } => {
                for origin in facts.return_origins() {
                    if !append_origin_children(position.executable(), facts, origin, &mut source_positions) {
                        source_positions.clear();
                        break;
                    }
                }
            }
            TransportPosition::CallArg {
                callsite,
                semantic_index,
                ..
            } => {
                if let Some(arg) = callsite_call_args(facts.body())
                    .get(callsite)
                    .and_then(|args| args.get(*semantic_index))
                {
                    source_positions.push(TransportPosition::Value {
                        executable: position.executable().clone(),
                        value: arg.value,
                    });
                }
            }
            TransportPosition::ReturnPayload { callsite, .. } => {
                if facts.callsite_return_origin(*callsite).is_none_or(|origin| {
                    !append_origin_children(position.executable(), facts, origin, &mut source_positions)
                }) {
                    source_positions.clear();
                }
            }
            TransportPosition::EntryCapture {
                entry, capture_index, ..
            } => {
                if let LoweredBody::Clauses { entries, .. } = facts.body()
                    && let Some(capture) = entries
                        .get(entry.as_u32() as usize)
                        .and_then(|entry| entry.captures.get(*capture_index))
                {
                    source_positions.push(TransportPosition::Value {
                        executable: position.executable().clone(),
                        value: *capture,
                    });
                }
            }
            TransportPosition::ResumePayload { callsite, entry, .. } => {
                if let Some(callsite) = callsite {
                    if facts.callsite_return_origin(*callsite).is_none_or(|origin| {
                        !append_origin_children(position.executable(), facts, origin, &mut source_positions)
                    }) {
                        source_positions.clear();
                    }
                } else if let LoweredBody::Clauses { entries, .. } = facts.body()
                    && let Some(value) = entries
                        .get(entry.as_u32() as usize)
                        .and_then(|entry| match entry.origin {
                            super::super::body::ControlEntryOrigin::DeliveredResume { value } => Some(value),
                            _ => None,
                        })
                {
                    source_positions.push(TransportPosition::Value {
                        executable: position.executable().clone(),
                        value,
                    });
                }
            }
        }
    }
    let mut builder = TransportFactsBuilder::default();
    record_generic_owner_facts(world, &mut builder, layout.structural, ty, &demand, position);
    for source in &source_positions {
        let key = ProductKey::CallableConstruction(source.clone());
        let current = ProductKey::CallableConstruction(position.clone());
        let members = match context.read_recursive_product(tel, key.clone(), &current, world.types()) {
            super::super::pull::RecursiveProductRead::Ready(ProductValue::CallableConstruction(owner)) => {
                builder.merge_owner(owner);
                continue;
            }
            super::super::pull::RecursiveProductRead::Ready(value) => {
                panic!("callable construction produced unexpected value {value:?}")
            }
            super::super::pull::RecursiveProductRead::Waiting => return PullOutcome::wait_on_product(key),
            super::super::pull::RecursiveProductRead::Group(members) => members,
        };
        let mut evidence = TransportFactsBuilder::default();
        evidence.merge(&builder);
        for owner in context.recursive_group_callable_owners(&current, &members, world.types()) {
            evidence.merge_owner(&owner);
        }
        let values = members
            .iter()
            .map(|member| project_group_member_owner(world, context, &evidence, member))
            .collect();
        let value = context.stage_recursive_group(&current, &members, values);
        return PullOutcome::Produced(value);
    }
    PullOutcome::Produced(ProductValue::CallableConstruction(Rc::new(project_owner_answer(
        world, &builder, layout, ty, &demand, position,
    ))))
}

/// One recursive-group member's own answer: the evidence the cycle forces the
/// members to share, projected through THIS member's layout, analyzed type and
/// demand. Sharing the evidence is what the knot is for; sharing the projection
/// is not -- each member publishes only the facts its own position can carry,
/// so which member's job resolves the group cannot change what any of them say.
fn project_group_member_owner(
    world: &mut World,
    context: &ProductReadContext<'_>,
    evidence: &TransportFactsBuilder,
    member: &ProductKey,
) -> ProductValue {
    let ProductKey::CallableConstruction(position) = member else {
        unreachable!("a callable-construction group holds only callable-construction members")
    };
    let layout = context
        .callable_group_layout(member)
        .expect("callable owner group member must have a settled transport shape");
    let executable = executable_key_for_transport_position(context.session().root(), position);
    let facts = world
        .executable_facts(&executable)
        .cloned()
        .expect("callable owner group member must have settled executable facts");
    let runtime = world
        .runtime_demand(&executable)
        .cloned()
        .expect("callable owner group member must have a settled runtime demand");
    let (ty, demand) = generic_owner_ty_and_demand(world, &executable, &facts, &runtime, position);
    ProductValue::CallableConstruction(Rc::new(project_owner_answer(
        world, evidence, layout, ty, &demand, position,
    )))
}

/// The answer one position publishes: its evidence projected through the
/// position's OWN layout, analyzed type and demand. Cycle or no cycle, the same
/// derivation -- an owner says only what its own position can carry.
/// Source and destination descriptors may differ: exact target evidence follows
/// typed activation demand, not equality of their physical callable layouts.
fn project_owner_answer(
    world: &mut World,
    evidence: &TransportFactsBuilder,
    layout: TransportLayout,
    ty: Ty,
    demand: &RuntimeDemand,
    position: &TransportPosition,
) -> CallableConstructionOwner {
    let projected = project_generic_owner_facts(world, evidence, layout.structural, ty, demand, position);
    let (callable_facts, boundary_facts) = projected.finish(world.types());
    CallableConstructionOwner {
        layout,
        construction: None,
        callable_facts,
        boundary_facts,
    }
}

/// The settled fact a generic callable-owner position reads its analyzed type
/// out of, if any. The owner's own job settles it here; a group member's job
/// already settled its own, so the group resolution reads members' types
/// without re-subscribing.
fn generic_owner_ty_fact(executable: &ExecutableKey, position: &TransportPosition) -> Option<FactKey> {
    match position {
        TransportPosition::ExecutableInput { .. } => Some(FactKey::ActivationInputs(executable.activation.clone())),
        TransportPosition::ExecutableReturn { .. } | TransportPosition::ReturnPayload { .. } => {
            Some(FactKey::ReturnType(executable.activation.clone()))
        }
        TransportPosition::Value { .. }
        | TransportPosition::CallArg { .. }
        | TransportPosition::EntryCapture { .. }
        | TransportPosition::ResumePayload { .. } => None,
    }
}

/// The analyzed type and runtime demand a generic callable-owner position
/// carries. This pair is the filter every facts projection runs through, so it
/// is derived per position -- never inherited from a group-mate.
fn generic_owner_ty_and_demand(
    world: &mut World,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    runtime: &ExecutableRuntimeDemand,
    position: &TransportPosition,
) -> (Ty, RuntimeDemand) {
    match position {
        TransportPosition::ExecutableInput { semantic_index, .. } => (
            world
                .activation_inputs_joined(&executable.activation)
                .unwrap_or_else(|| executable.activation.inputs().to_vec())
                .get(*semantic_index)
                .copied()
                .unwrap_or_else(|| world.types_mut().any()),
            runtime.input_demands.get(*semantic_index).cloned().unwrap_or_default(),
        ),
        TransportPosition::ExecutableReturn { .. } | TransportPosition::ReturnPayload { .. } => {
            let Some(ty) = world.activation_return(&executable.activation) else {
                unreachable!("bottom transport layouts return before callable-owner derivation")
            };
            (ty, runtime.return_demand.clone())
        }
        TransportPosition::Value { value, .. } => (
            facts
                .analysis()
                .value_types
                .get(value)
                .copied()
                .unwrap_or_else(|| world.types_mut().any()),
            runtime.value_demands.get(value).cloned().unwrap_or_default(),
        ),
        TransportPosition::CallArg {
            callsite,
            semantic_index,
            ..
        } => {
            let arg_value = callsite_call_args(facts.body())
                .get(callsite)
                .and_then(|args| args.get(*semantic_index))
                .map(|arg| arg.value);
            (
                arg_value
                    .and_then(|value| facts.analysis().value_types.get(&value).copied())
                    .unwrap_or_else(|| world.types_mut().any()),
                runtime
                    .call_arg_demands
                    .get(callsite)
                    .and_then(|demands| demands.get(*semantic_index))
                    .cloned()
                    .unwrap_or_default(),
            )
        }
        TransportPosition::EntryCapture {
            entry, capture_index, ..
        } => {
            let capture = entry_capture_value(facts, *entry, *capture_index)
                .expect("an entry-capture position must name a capture value");
            (
                entry_capture_ty(executable, facts, capture),
                runtime
                    .entry_capture_demands
                    .get(entry)
                    .and_then(|demands| demands.get(*capture_index))
                    .cloned()
                    .unwrap_or_default(),
            )
        }
        TransportPosition::ResumePayload { entry, .. } => {
            let value = match facts.body() {
                LoweredBody::Clauses { entries, .. } => {
                    entries
                        .get(entry.as_u32() as usize)
                        .and_then(|entry| match entry.origin {
                            super::super::body::ControlEntryOrigin::DeliveredResume { value } => Some(value),
                            _ => None,
                        })
                }
                LoweredBody::Extern { .. } => None,
            };
            (
                value
                    .and_then(|value| facts.analysis().value_types.get(&value).copied())
                    .unwrap_or_else(|| world.types_mut().any()),
                value
                    .and_then(|value| runtime.value_demands.get(&value).cloned())
                    .unwrap_or_else(RuntimeDemand::whole),
            )
        }
    }
}

fn demand_contains_callable(demand: &RuntimeDemand) -> bool {
    demand.is_callable()
        || match &demand.shape {
            ShapeDemand::TupleFields(fields) => fields.iter().any(demand_contains_callable),
            ShapeDemand::Ignore | ShapeDemand::Whole => false,
        }
}

fn project_generic_owner_facts(
    world: &mut World,
    source: &TransportFactsBuilder,
    shape: ShapeId,
    ty: Ty,
    demand: &RuntimeDemand,
    publication: &TransportPosition,
) -> TransportFactsBuilder {
    let mut projected = TransportFactsBuilder::default();
    project_generic_owner_node(world, source, &mut projected, shape, ty, demand, publication);
    projected
}

fn project_generic_owner_node(
    world: &mut World,
    source: &TransportFactsBuilder,
    projected: &mut TransportFactsBuilder,
    shape: ShapeId,
    ty: Ty,
    demand: &RuntimeDemand,
    publication: &TransportPosition,
) {
    match world.shape(shape).clone() {
        ShapeDescr::Callable(callable) => {
            record_generic_owner_facts(world, projected, shape, ty, demand, publication);
            let resolutions = exact_demand_resolution_symbols(source, demand, None);
            if let Some(draft) = projected.callables.get_mut(&callable) {
                extend_unique(&mut draft.resolutions, resolutions);
            }
            if world.callable(callable).direct().is_some()
                && demand.callable.is_first_class()
                && let Some(owner) = source.callables.get(&callable)
            {
                let draft = projected
                    .callables
                    .get_mut(&callable)
                    .expect("the position published its callable");
                extend_unique(&mut draft.boundary_ids, owner.boundary_ids.clone());
                for boundary in &owner.boundary_ids {
                    if let Some(facts) = source.boundaries.get(boundary) {
                        projected.record_boundary_resolutions(*boundary, facts.resolutions.clone());
                    }
                    projected.record_boundary(*boundary, publication.clone());
                }
            }
            let boundary_ids = projected
                .callables
                .get(&callable)
                .map(|draft| draft.boundary_ids.clone())
                .unwrap_or_default();
            for (surface, boundary) in demand.callable.resolved.iter().zip(boundary_ids) {
                projected.record_boundary_resolutions(
                    boundary,
                    exact_demand_resolution_symbols(source, demand, Some(surface)),
                );
            }
        }
        ShapeDescr::Tuple(fields) => {
            let ShapeDemand::TupleFields(field_demands) = &demand.shape else {
                return;
            };
            let field_tys =
                exact_tuple_field_tys(world, ty).unwrap_or_else(|| vec![world.types_mut().any(); fields.len()]);
            for ((field, field_ty), field_demand) in fields.iter().copied().zip(field_tys).zip(field_demands) {
                project_generic_owner_node(
                    world,
                    source,
                    projected,
                    field.structural,
                    field_ty,
                    field_demand,
                    publication,
                );
            }
        }
        ShapeDescr::Nothing | ShapeDescr::Lane(_) => {}
    }
}

fn exact_demand_resolution_symbols(
    source: &TransportFactsBuilder,
    demand: &RuntimeDemand,
    surface: Option<&CallableSurface>,
) -> Vec<ExecutableSymbol> {
    let mut resolutions = Vec::new();
    for target in demand
        .callable
        .targets
        .iter()
        .filter(|target| surface.is_none_or(|surface| target.surface == *surface))
    {
        for resolution in source
            .callables
            .values()
            .flat_map(|draft| draft.resolutions.iter())
            .filter(|resolution| {
                resolution.activation.function == target.activation.function
                    && resolution.activation.signature == target.activation.signature
            })
        {
            if !resolutions.contains(resolution) {
                resolutions.push(resolution.clone());
            }
        }
    }
    resolutions
}

fn record_generic_owner_facts(
    world: &mut World,
    facts: &mut TransportFactsBuilder,
    shape: ShapeId,
    ty: Ty,
    demand: &RuntimeDemand,
    publication: &TransportPosition,
) {
    match world.shape(shape).clone() {
        ShapeDescr::Callable(callable) => {
            let surfaces = &demand.callable.resolved;
            let surface_layouts = surface_layouts(world, surfaces);
            let surface_shapes = surface_shapes_from_layouts(&surface_layouts);
            let boundary_ids = if demand.callable.is_first_class() && !surfaces.is_empty() {
                publish_boundaries_for_callable(
                    world,
                    facts,
                    callable,
                    surfaces,
                    &surface_layouts,
                    ty,
                    &vec![Vec::new(); surfaces.len()],
                    Some(publication.clone()),
                )
                .into_values()
                .collect()
            } else {
                Vec::new()
            };
            facts.record_callable(callable, Vec::new(), surface_shapes, Vec::new(), boundary_ids);
        }
        ShapeDescr::Tuple(fields) => {
            let ShapeDemand::TupleFields(field_demands) = &demand.shape else {
                return;
            };
            let field_tys =
                exact_tuple_field_tys(world, ty).unwrap_or_else(|| vec![world.types_mut().any(); fields.len()]);
            for ((field, field_ty), field_demand) in fields.iter().copied().zip(field_tys).zip(field_demands) {
                record_generic_owner_facts(world, facts, field.structural, field_ty, field_demand, publication);
            }
        }
        ShapeDescr::Nothing | ShapeDescr::Lane(_) => {}
    }
}

/// Whether this layout carries its value as ONE public word: a pointer, and
/// nothing structural beside it.
///
/// An explicit `ValueRef` carrier is that word by definition. So is a bare
/// structural lane holding a callable, because a callable has no raw form --
/// its single lane IS the closure pointer. Either way the caller holds a
/// pointer it cannot take apart, so a callable arriving this way is called
/// through the apply seam.
///
/// A callable that travels DECOMPOSED is not a public word however wide it is:
/// a direct callable whose one capture happens to be boxed still hands the
/// caller that capture, not a closure pointer. So the question is asked of the
/// carrier and of a bare lane, and the lane's form comes from the ABI's own
/// rule.
///
/// The `&mut` is that rule's: `AbiValueRepr::for_ty` interns the atom type to
/// ask whether a lane is one. Interning it once at world construction would
/// let both take `&World`, but it would also move every type minted after it,
/// which is a large change of ids for a smaller change of signature.
fn layout_is_one_public_word(world: &mut World, layout: TransportLayout) -> bool {
    if layout.carrier.is_value_ref() {
        return true;
    }
    let ShapeDescr::Lane(lane) = world.shape(layout.structural) else {
        return false;
    };
    let ty = world.lane(*lane).ty;
    AbiValueRepr::for_ty(world, ty) == AbiValueRepr::ValueRef
}

/// Match the carried construction alternatives to the callsite's owned rows.
/// Both return grounding and emitted call forms use this decision. A selector
/// names a construction; argument dispatch may still choose several executable
/// specializations within that construction.
fn closed_call_arms(
    world: &mut World,
    callee: TransportLayout,
    targets: &[CallTargetSummary],
) -> Option<Vec<(usize, CallTargetSummary)>> {
    if layout_is_one_public_word(world, callee) || targets.is_empty() {
        return None;
    }
    let alternatives = match world.shape(callee.structural) {
        ShapeDescr::Callable(callable) => world.callable(*callable).alternatives().to_vec(),
        _ => Vec::new(),
    };
    // An erased, capture-free singleton still has one statically known target.
    if alternatives.is_empty() {
        return (targets.len() == 1
            && matches!(targets[0].callee, SelectedCallee::Function(_))
            && targets[0]
                .activation
                .as_ref()
                .is_some_and(|target| world.activation_capture_count(target) == 0))
        .then(|| vec![(0, targets[0].clone())]);
    }
    let mut arms = Vec::new();
    for (index, alternative) in alternatives.iter().enumerate() {
        let before = arms.len();
        for target in targets {
            let Some(activation) = &target.activation else { continue };
            if target.callee != SelectedCallee::Function(alternative.function)
                || activation.function != alternative.function
                || usize::from(alternative.arity) != target.surface_inputs.len()
                || alternative.capture_layouts.len() != alternative.capture_tys.len()
                || alternative.capture_layouts.len() != world.activation_capture_count(activation)
            {
                continue;
            }
            {
                let inputs = target.activation_inputs.as_ref()?;
                let count = inputs.len().checked_sub(target.surface_inputs.len())?;
                // Captures identify a construction specialization. Subtyping
                // would also route a precise environment into a different
                // alternative's broader capture row.
                if count != alternative.capture_tys.len() || alternative.capture_tys.as_ref() != &inputs[..count] {
                    continue;
                }
            }
            arms.push((index, target.clone()));
        }
        if arms.len() == before {
            return None;
        }
    }
    // No row may silently disappear: a missing capture view contradicts a
    // summary which promises that row is reachable.
    if targets.iter().any(|target| !arms.iter().any(|(_, arm)| arm == target)) {
        return None;
    }
    Some(arms)
}

pub(super) fn closure_call_form(
    world: &mut World,
    callee_layout: TransportLayout,
    summary: Option<&CallSiteSummary>,
    need: ExecutableNeed,
) -> ClosureCallForm {
    if let Some(arms) = summary.and_then(|summary| closed_call_arms(world, callee_layout, &summary.targets)) {
        let has_selector = matches!(world.shape(callee_layout.structural), ShapeDescr::Callable(id)
            if world.callable(*id).selector().is_some());
        if arms.len() == 1 && !has_selector {
            let (_, target) = arms.into_iter().next().unwrap();
            let activation = target.activation.clone().expect("owned target");
            return ClosureCallForm::Direct {
                edge: ClosureCallEdge::Direct {
                    capture_count: world.activation_capture_count(&activation),
                    target: ExecutableKey { activation, need },
                },
                target,
            };
        }
        return ClosureCallForm::Closed { arms };
    }
    if layout_is_one_public_word(world, callee_layout) {
        return ClosureCallForm::Seam;
    }
    match summary {
        Some(summary) => panic!(
            "closure callee layout {callee_layout:?} carries neither the captures of the {} target(s) its callsite names nor one public word",
            summary.targets.len()
        ),
        None => ClosureCallForm::Dead,
    }
}

/// What `closure_call_form` decided, with what lowering needs to act on it.
///
/// Only the `ClosureCallEdge` travels on to the emitted tail. A direct call is
/// also lowered against the callsite summary row it was decided from, so the
/// answer carries that row rather than leaving the caller to look it up again.
pub(super) enum ClosureCallForm {
    Direct {
        edge: ClosureCallEdge,
        target: CallTargetSummary,
    },
    Closed {
        arms: Vec<(usize, CallTargetSummary)>,
    },
    Seam,
    Dead,
}

#[derive(Clone)]
enum TransportRecipe {
    Terminal,
    PublicCallableReturn,
    /// A closure-call result grounds in each owned arm's return fact when
    /// the carrier supplies those arms' captures; a public call stays boxed.
    ClosureCallReturn {
        callee: TransportPosition,
        grounded: Vec<DirectClosureTarget>,
    },
    Alias(TransportPosition),
    /// A recursion edge cut at construction: a child whose transport layout can
    /// never be read here, because reading it would close a cycle in the
    /// position graph. It is the one recipe node with no product behind it.
    CutEdge,
    Alternatives(Vec<Self>),
    Tuple(Vec<Self>),
    Projection {
        source: Box<Self>,
        kind: crate::dispatch_matrix::ProjectionKind,
    },
}

/// One owned callback arm and the executable return it contributes.
#[derive(Clone)]
struct DirectClosureTarget {
    target: CallTargetSummary,
    return_recipe: TransportRecipe,
}

enum RecipeLayout {
    Exact(TransportLayout),
    /// A subtree holding a cut edge has no form of its own: nothing here
    /// observed the cut child, so nothing here may claim its shape. What it
    /// carries instead is the evidence gathered beside the cut -- the layouts
    /// of the alternatives that WERE readable -- for the owning position to
    /// settle on in `cut_transport_layout`.
    Cut(Vec<TransportLayout>),
    Waiting(ProductKey),
}

fn evaluate_transport_recipe(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    recipe: &TransportRecipe,
    ty: Ty,
    demand: &RuntimeDemand,
    position: &TransportPosition,
) -> RecipeLayout {
    match recipe {
        TransportRecipe::Terminal => {
            joined_transport_layout(world, Some(CallableReads { tel, context, position }), ty, demand, &[])
        }
        TransportRecipe::PublicCallableReturn => {
            let layout = derived_transport_layout(world, ty, demand, &[]);
            RecipeLayout::Exact(with_value_ref_carrier(world, ty, layout))
        }
        TransportRecipe::ClosureCallReturn { callee, grounded } => {
            let callee_key = ProductKey::TransportShape(callee.clone());
            let callee_layout = match context.read_product(tel, callee_key.clone(), world.types()) {
                Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => *layout,
                Some(value) => panic!("closure callee shape produced unexpected value {value:?}"),
                None => return RecipeLayout::Waiting(callee_key),
            };
            let targets = grounded.iter().map(|ground| ground.target.clone()).collect::<Vec<_>>();
            let recipe = if closed_call_arms(world, callee_layout, &targets).is_some() {
                TransportRecipe::Alternatives(grounded.iter().map(|ground| ground.return_recipe.clone()).collect())
            } else {
                TransportRecipe::PublicCallableReturn
            };
            evaluate_transport_recipe(world, tel, context, &recipe, ty, demand, position)
        }
        TransportRecipe::CutEdge => RecipeLayout::Cut(Vec::new()),
        TransportRecipe::Alias(child) => {
            let key = ProductKey::TransportShape(child.clone());
            match context.read_product(tel, key.clone(), world.types()) {
                Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => RecipeLayout::Exact(*layout),
                Some(value) => panic!("transport shape produced unexpected value {value:?}"),
                None => RecipeLayout::Waiting(key),
            }
        }
        TransportRecipe::Alternatives(recipes) => {
            let mut layouts = Vec::new();
            let mut cut = false;
            for recipe in recipes {
                match evaluate_transport_recipe(world, tel, context, recipe, ty, demand, position) {
                    RecipeLayout::Exact(layout) => layouts.push(layout),
                    RecipeLayout::Cut(evidence) => {
                        cut = true;
                        layouts.extend(evidence);
                    }
                    waiting @ RecipeLayout::Waiting(_) => return waiting,
                }
            }
            if cut {
                RecipeLayout::Cut(layouts)
            } else {
                joined_transport_layout(
                    world,
                    Some(CallableReads { tel, context, position }),
                    ty,
                    demand,
                    &layouts,
                )
            }
        }
        TransportRecipe::Tuple(fields) => {
            let mut layouts = Vec::with_capacity(fields.len());
            for field in fields {
                match evaluate_transport_recipe(world, tel, context, field, ty, demand, position) {
                    RecipeLayout::Exact(layout) => layouts.push(layout),
                    cut @ RecipeLayout::Cut(_) => return cut,
                    waiting @ RecipeLayout::Waiting(_) => return waiting,
                }
            }
            RecipeLayout::Exact(tuple_layout(world, &layouts))
        }
        TransportRecipe::Projection { source, kind } => {
            let crate::dispatch_matrix::ProjectionKind::TupleField(index) = kind else {
                return RecipeLayout::Exact(derived_transport_layout(world, ty, demand, &[]));
            };
            match evaluate_transport_recipe(world, tel, context, source, ty, demand, position) {
                RecipeLayout::Exact(layout) => match world.shape(layout.structural) {
                    ShapeDescr::Tuple(fields) => {
                        if let Some(field) = fields.get(*index as usize).copied() {
                            RecipeLayout::Exact(TransportLayout {
                                structural: field.structural,
                                carrier: if layout.carrier.is_value_ref() {
                                    TransportCarrier::ValueRef(value_lane(world, ty))
                                } else {
                                    field.carrier
                                },
                            })
                        } else {
                            RecipeLayout::Exact(derived_transport_layout(world, ty, demand, &[]))
                        }
                    }
                    ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => {
                        RecipeLayout::Exact(derived_transport_layout(world, ty, demand, &[]))
                    }
                },
                other => other,
            }
        }
    }
}

fn tuple_layout(world: &mut World, fields: &[TransportLayout]) -> TransportLayout {
    TransportLayout {
        structural: world.intern_shape(ShapeDescr::Tuple(fields.to_vec().into_boxed_slice())),
        carrier: TransportCarrier::Absent,
    }
}

/// Closed construction alternatives, with each capture carrying the combined
/// requirements of the executable interfaces that can consume it. Selection
/// identifies the lexical function and capture schema, never an executable.
/// Target layouts are products: an unread capture waits, and a capture cycle
/// retains the existing public cut instead of inventing a finite environment.
fn exact_direct_callable_layout(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    ty: Ty,
    demand: &RuntimeDemand,
    position: &TransportPosition,
) -> Option<RecipeLayout> {
    if demand.callable.is_first_class() {
        return None;
    }
    let targets = targets_the_slot_type_admits(world, ty, &demand.callable.targets);
    if targets.is_empty() {
        return None;
    }
    let clauses = world.types().closed_callable_clauses(&ty)?;
    let mut settled: Option<CallableDescr> = None;
    for clause in clauses {
        let closure = clause.closure.expect("closed clause has a literal");
        let function = function_id_of_closure_target(closure.target);
        let mut covered = false;
        for target in &targets {
            let count = target
                .activation_inputs
                .len()
                .checked_sub(target.surface.inputs.len())?;
            // Invocation keying preserves captures verbatim; only argument
            // interfaces may differ within this construction's requirements.
            if target.activation.function != function
                || count != closure.captures.len()
                || clause.args.len() != target.surface.inputs.len()
                || closure.captures.as_slice() != &target.activation_inputs[..count]
            {
                continue;
            }
            covered = true;
            match direct_callable_descr(world, tel, context, ty, demand, position, target) {
                DirectCallableDescr::Descr(mut alternative) => {
                    alternative.capture_tys = closure.captures.clone().into_boxed_slice();
                    let descr = CallableDescr::Direct { alternative };
                    settled = Some(match &settled {
                        Some(first) => combine_callable_requirements(world, first, &descr)?,
                        None => descr,
                    });
                }
                DirectCallableDescr::Position(layout) => return Some(layout),
                DirectCallableDescr::Unavailable => return None,
            }
        }
        if !covered {
            return None;
        }
    }
    let callable = world.intern_callable(settled?);
    Some(RecipeLayout::Exact(TransportLayout {
        structural: world.intern_shape(ShapeDescr::Callable(callable)),
        carrier: TransportCarrier::Absent,
    }))
}

/// The targets whose function this slot's type admits.
///
/// A callable type brands each of its closure clauses with the lambda the
/// value was minted from, and that type is a coordinate of the key addressing
/// this position: it is the position's own statement of which functions can
/// arrive. The demand's target set answers a different question — where each
/// reachable target lives, so its captures can be read — and it accumulates
/// across every callsite the value is joined through, so it can name a lambda
/// this slot's type excludes. Where the two differ the type decides, because
/// the key was minted from it.
///
/// A type that brands nothing says nothing about which functions arrive and
/// admits every target it was given.
pub(super) fn targets_the_slot_type_admits(
    world: &mut World,
    ty: Ty,
    targets: &BTreeSet<CallableTarget>,
) -> BTreeSet<CallableTarget> {
    let brands = world
        .types_mut()
        .callable_clauses(&ty)
        .map(|clauses| {
            clauses
                .iter()
                .filter_map(|clause| clause.closure.as_ref())
                .map(|closure| function_id_of_closure_target(closure.target))
                .collect::<BTreeSet<_>>()
        })
        .unwrap_or_default();
    if brands.is_empty() {
        return targets.clone();
    }
    targets
        .iter()
        .filter(|target| brands.contains(&target.activation.function))
        .cloned()
        .collect()
}

/// What one target contributes to [`exact_direct_callable_layout`].
enum DirectCallableDescr {
    /// The callable layout this target names.
    Descr(CallableAlternative),
    /// An answer for the whole position, reached before any layout could be
    /// named: a capture cycle's cut, or a capture layout not yet readable.
    Position(RecipeLayout),
    /// This target names no exact layout at all.
    Unavailable,
}

fn combine_callable_requirements(
    world: &mut World,
    left: &CallableDescr,
    right: &CallableDescr,
) -> Option<CallableDescr> {
    if matches!(left, CallableDescr::Opaque) || matches!(right, CallableDescr::Opaque) {
        return None;
    }
    let mut alternatives = left.alternatives().to_vec();
    for alternative in right.alternatives() {
        if let Some(existing) = alternatives.iter_mut().find(|item| item.same_identity(alternative)) {
            if existing.arity != alternative.arity
                || existing.capture_layouts.len() != alternative.capture_layouts.len()
            {
                return None;
            }
            existing.capture_layouts = existing
                .capture_layouts
                .iter()
                .copied()
                .zip(alternative.capture_layouts.iter().copied())
                .map(|(left, right)| combine_capture_requirements(world, left, right))
                .collect::<Option<Box<_>>>()?;
        } else {
            alternatives.push(alternative.clone());
        }
    }
    alternatives.sort_by(|left, right| {
        world
            .function_ref(left.function)
            .denotation
            .semantic_cmp(&world.function_ref(right.function).denotation)
            .then_with(|| world.types().cmp_activation_tys(&left.capture_tys, &right.capture_tys))
    });
    if alternatives.len() == 1 {
        Some(CallableDescr::Direct {
            alternative: alternatives.remove(0),
        })
    } else {
        let int = world.types_mut().int();
        Some(CallableDescr::Closed {
            selector: value_lane(world, int),
            alternatives: alternatives.into_boxed_slice(),
        })
    }
}

fn combine_capture_requirements(
    world: &mut World,
    left: TransportLayout,
    right: TransportLayout,
) -> Option<TransportLayout> {
    if left == right {
        return Some(left);
    }
    let absent = |layout: TransportLayout| {
        world.shape(layout.structural).is_semantically_absent() && layout.carrier == TransportCarrier::Absent
    };
    if absent(left) {
        return Some(right);
    }
    if absent(right) {
        return Some(left);
    }
    let carrier = match (left.carrier, right.carrier) {
        (TransportCarrier::Absent, carrier) | (carrier, TransportCarrier::Absent) => carrier,
        (left, right) if left == right => left,
        _ => return None,
    };
    let structural = if left.structural == right.structural {
        left.structural
    } else {
        match (
            world.shape(left.structural).clone(),
            world.shape(right.structural).clone(),
        ) {
            (ShapeDescr::Tuple(left), ShapeDescr::Tuple(right)) if left.len() == right.len() => {
                let fields = left
                    .iter()
                    .copied()
                    .zip(right.iter().copied())
                    .map(|(left, right)| combine_capture_requirements(world, left, right))
                    .collect::<Option<Box<_>>>()?;
                world.intern_shape(ShapeDescr::Tuple(fields))
            }
            (ShapeDescr::Callable(left), ShapeDescr::Callable(right)) => {
                let left = world.callable(left).clone();
                let right = world.callable(right).clone();
                let combined = combine_callable_requirements(world, &left, &right)?;
                let callable = world.intern_callable(combined);
                world.intern_shape(ShapeDescr::Callable(callable))
            }
            _ => return None,
        }
    };
    Some(TransportLayout { structural, carrier })
}

fn direct_callable_descr(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    ty: Ty,
    demand: &RuntimeDemand,
    position: &TransportPosition,
    target: &CallableTarget,
) -> DirectCallableDescr {
    let Some(capture_count) = target.activation_inputs.len().checked_sub(target.surface.inputs.len()) else {
        return DirectCallableDescr::Unavailable;
    };
    let executable = ExecutableKey {
        activation: target.activation.clone(),
        need: target.need,
    };
    let executable = ExecutableSymbol::from_key(&executable);
    let mut capture_layouts = Vec::with_capacity(capture_count);
    for semantic_index in 0..capture_count {
        let capture = TransportPosition::ExecutableInput {
            executable: executable.clone(),
            semantic_index,
        };
        if &capture == position {
            // This position IS one of the captures it would have to read: a
            // closure standing among its own capture surface. Nothing can be
            // known about the surface from inside it, so the value travels as
            // a generic boxed callable, the one shape both ends can name
            // without it. A longer capture chain cannot close a cycle -- a
            // closure's captures exist before the closure does, so none of
            // them can reach back to it.
            let mut layout = derived_transport_layout(world, ty, demand, &[]);
            layout.carrier = TransportCarrier::ValueRef(value_lane(world, ty));
            return DirectCallableDescr::Position(RecipeLayout::Cut(vec![layout]));
        }
        let key = ProductKey::TransportShape(capture);
        match context.read_product(tel, key.clone(), world.types()) {
            Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => capture_layouts.push(*layout),
            Some(value) => panic!("transport shape produced unexpected value {value:?}"),
            None => return DirectCallableDescr::Position(RecipeLayout::Waiting(key)),
        }
    }
    DirectCallableDescr::Descr(CallableAlternative {
        function: target.activation.function,
        capture_tys: target.activation_inputs[..capture_count].to_vec().into_boxed_slice(),
        arity: world
            .function_ref(target.activation.function)
            .arity
            .try_into()
            .expect("source arity fits its descriptor"),
        capture_layouts: capture_layouts.into_boxed_slice(),
    })
}

fn origin_transport_recipe(
    symbol: &ExecutableSymbol,
    facts: &ExecutableFacts,
    origin: &TransportSource,
) -> TransportRecipe {
    match origin {
        TransportSource::ExecutableInput(semantic_index) => {
            TransportRecipe::Alias(TransportPosition::ExecutableInput {
                executable: symbol.clone(),
                semantic_index: *semantic_index,
            })
        }
        TransportSource::LocalValue(value) => TransportRecipe::Alias(TransportPosition::Value {
            executable: symbol.clone(),
            value: *value,
        }),
        TransportSource::CallsiteReturn(callsite) => {
            let Some(summary) = facts.callsites().get(callsite) else {
                return TransportRecipe::Terminal;
            };
            let need = facts
                .callsite_needs()
                .get(callsite)
                .copied()
                .unwrap_or(ExecutableNeed::Value);
            TransportRecipe::Alternatives(
                summary
                    .targets
                    .iter()
                    .map(|target| match (&target.callee, &target.activation) {
                        (SelectedCallee::Function(_), Some(activation)) => {
                            TransportRecipe::Alias(TransportPosition::ExecutableReturn {
                                executable: ExecutableSymbol::from_key(&ExecutableKey {
                                    activation: activation.clone(),
                                    need,
                                }),
                            })
                        }
                        (SelectedCallee::ProviderBoundary(_), _) | (_, None) => TransportRecipe::Terminal,
                    })
                    .collect(),
            )
        }
        TransportSource::ClosureCallReturn { callsite, callee } => {
            let need = facts
                .callsite_needs()
                .get(callsite)
                .copied()
                .unwrap_or(ExecutableNeed::Value);
            let grounded = facts
                .callsites()
                .get(callsite)
                .map(|summary| {
                    summary
                        .targets
                        .iter()
                        .map(|target| {
                            let activation = match (&target.callee, &target.activation) {
                                (SelectedCallee::Function(_), Some(activation)) => activation,
                                _ => return None,
                            };
                            Some(DirectClosureTarget {
                                target: target.clone(),
                                return_recipe: TransportRecipe::Alias(TransportPosition::ExecutableReturn {
                                    executable: ExecutableSymbol::from_key(&ExecutableKey {
                                        activation: activation.clone(),
                                        need,
                                    }),
                                }),
                            })
                        })
                        .collect::<Option<Vec<_>>>()
                        .unwrap_or_default()
                })
                .unwrap_or_default();
            TransportRecipe::ClosureCallReturn {
                callee: TransportPosition::Value {
                    executable: symbol.clone(),
                    value: *callee,
                },
                grounded,
            }
        }
        TransportSource::Join(origins) => TransportRecipe::Alternatives(
            origins
                .iter()
                .map(|origin| origin_transport_recipe(symbol, facts, origin))
                .collect(),
        ),
        TransportSource::TupleValue(values) => TransportRecipe::Tuple(
            values
                .iter()
                .map(|value| {
                    TransportRecipe::Alias(TransportPosition::Value {
                        executable: symbol.clone(),
                        value: *value,
                    })
                })
                .collect(),
        ),
        TransportSource::Projection { source, kind } => TransportRecipe::Projection {
            source: Box::new(TransportRecipe::Alias(TransportPosition::Value {
                executable: symbol.clone(),
                value: *source,
            })),
            kind: kind.clone(),
        },
        TransportSource::OutcomeSubject { owner, subject } => {
            let (source, path) = facts.body().dispatch_subject_origin(*owner, *subject);
            let super::super::body::SubjectOriginRoot::Value(source) = source else {
                return TransportRecipe::Terminal;
            };
            path.into_iter().fold(
                TransportRecipe::Alias(TransportPosition::Value {
                    executable: symbol.clone(),
                    value: source,
                }),
                |source, kind| TransportRecipe::Projection {
                    source: Box::new(source),
                    kind: kind.clone(),
                },
            )
        }
        TransportSource::CallableValue(_) => TransportRecipe::Terminal,
    }
}

/// A callable value's arity, read off its own type. Every clause of one
/// callable value takes the same argument count, so the first clause answers
/// for all of them; a type too broad to carry clauses (`any`) reports 0.
fn callable_ty_arity(world: &mut World, ty: Ty) -> u16 {
    world
        .types_mut()
        .callable_clauses(&ty)
        .and_then(|clauses| clauses.first().map(|clause| clause.args.len() as u16))
        .unwrap_or(0)
}

fn produce_local_callable_construction(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    value: ValueId,
    producer: &LocalCallableProducer,
    flow: &CallableFlowFact,
    demand: RuntimeDemand,
) -> Result<CallableConstructionOwner, Vec<PullWait>> {
    assert_eq!(flow.function, producer.function);
    assert_eq!(flow.captures, producer.captures);
    let callable_ty = facts
        .analysis()
        .value_types
        .get(&value)
        .copied()
        .unwrap_or_else(|| world.types_mut().any());
    let capture_tys = producer
        .captures
        .iter()
        .map(|capture| {
            facts
                .analysis()
                .value_types
                .get(capture)
                .copied()
                .unwrap_or_else(|| world.types_mut().any())
        })
        .collect::<Vec<_>>();
    let mut capture_demands = vec![RuntimeDemand::ignore(); capture_tys.len()];
    let mut waits = Vec::new();
    for resolution in &flow.resolutions {
        let Some(resolution_demand) = context.read_runtime_demand_fact(world, resolution) else {
            waits.push(PullWait::Fact(FactUse::settled(FactKey::RuntimeDemand(
                resolution.clone(),
            ))));
            continue;
        };
        assert!(resolution_demand.input_demands.len() >= capture_tys.len());
        for (capture, input) in capture_demands
            .iter_mut()
            .zip(resolution_demand.input_demands.iter().take(capture_tys.len()))
        {
            capture.join_assign(input);
        }
    }
    let symbol = ExecutableSymbol::from_key(executable);
    let mut capture_layouts = Vec::with_capacity(producer.captures.len());
    for (index, capture) in producer.captures.iter().copied().enumerate() {
        let key = ProductKey::TransportShape(TransportPosition::Value {
            executable: symbol.clone(),
            value: capture,
        });
        match context.read_product(tel, key.clone(), world.types()) {
            Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => {
                let mut layout = *layout;
                if capture_demands[index].callable.is_first_class() && !layout.carrier.is_value_ref() {
                    layout.carrier = TransportCarrier::ValueRef(value_lane(world, capture_tys[index]));
                }
                capture_layouts.push(layout);
            }
            Some(value) => panic!("transport shape produced unexpected value {value:?}"),
            None => waits.push(PullWait::Product(key)),
        }
    }
    if !waits.is_empty() {
        return Err(waits);
    }

    let mut builder = TransportFactsBuilder::default();
    let direct_surfaces = surface_shapes(world, &flow.direct_surfaces);
    let direct_edges = callable_direct_edges(world, &flow.direct_edges);
    let arity = callable_ty_arity(world, callable_ty);
    let mut descr = CallableDescr::Direct {
        alternative: CallableAlternative {
            function: producer.function,
            arity,
            capture_tys: capture_tys.clone().into_boxed_slice(),
            capture_layouts: capture_layouts.clone().into_boxed_slice(),
        },
    };
    if flow.first_class_edges.is_empty()
        && !flow.opaque
        && !flow.escape
        && let Some(clauses) = world.types().closed_callable_clauses(&callable_ty)
    {
        // A source lambda can be reached under several correlated capture
        // rows. Preserve those rows; the aggregate capture ValueIds alone
        // would lose the construction selection before its first call.
        let mut closed = None;
        for clause in clauses {
            let closure = clause.closure.expect("closed callable literal");
            assert_eq!(function_id_of_closure_target(closure.target), producer.function);
            assert_eq!(closure.captures.len(), capture_layouts.len());
            let row = CallableDescr::Direct {
                alternative: CallableAlternative {
                    function: producer.function,
                    arity,
                    capture_tys: closure.captures.into_boxed_slice(),
                    capture_layouts: capture_layouts.clone().into_boxed_slice(),
                },
            };
            closed = Some(match closed {
                None => row,
                Some(previous) => combine_callable_requirements(world, &previous, &row)
                    .expect("one source producer supplies the same physical capture layouts"),
            });
        }
        if let Some(closed) = closed {
            descr = closed;
        }
    }
    let callable = world.intern_callable(descr);
    let boundary_surfaces = flow.first_class_surfaces.clone();
    let boundary_layouts = surface_layouts(world, &boundary_surfaces);
    let boundary_resolutions = boundary_resolution_symbols_for_flow_surfaces(flow, &boundary_surfaces);
    let producer_position = TransportPosition::Value {
        executable: symbol,
        value,
    };
    let boundaries_by_surface = publish_boundaries_for_callable(
        world,
        &mut builder,
        callable,
        &boundary_surfaces,
        &boundary_layouts,
        callable_ty,
        &boundary_resolutions,
        Some(producer_position.clone()),
    );
    builder.record_callable(
        callable,
        flow.resolutions.iter().map(ExecutableSymbol::from_key).collect(),
        direct_surfaces,
        direct_edges,
        boundaries_by_surface.values().copied().collect(),
    );
    let construction = if flow.first_class_edges.is_empty() {
        None
    } else {
        let construction_edges = callable_direct_edges(world, &flow.first_class_edges);
        // ONE ROUTING RULE, MEMBER SELECTION INCLUDED (fz-kdt.179). The
        // selection names which edges are destinations at all and the order
        // the wrapper tests them in; the member list below is built by walking
        // exactly that, which is how the fz-kdt.108 weld -- selection row `i`
        // is member `i` -- is re-derived from the seated order instead of
        // inherited from the edge list's typed activation content order.
        let selection =
            super::super::callsite_dispatch::construction_member_selection(world.types_mut(), &flow.first_class_edges)
                .expect("settled callable flow edges should produce a dispatch plan");
        Some(CallableConstructionFact {
            callable,
            producer: producer_position,
            captures: producer
                .captures
                .iter()
                .copied()
                .zip(capture_layouts)
                .zip(capture_tys)
                .map(|((value, layout), ty)| CallableConstructionCapture {
                    source: TransportPosition::Value {
                        executable: ExecutableSymbol::from_key(executable),
                        value,
                    },
                    layout,
                    ty,
                })
                .collect(),
            members: selection
                .members
                .iter()
                .map(|member| {
                    let source = &flow.first_class_edges[*member];
                    let edge = &construction_edges[*member];
                    CallableConstructionMember {
                        boundary: *boundaries_by_surface
                            .get(&source.surface)
                            .expect("every construction edge surface should have a published boundary"),
                        surface_inputs: edge.surface_inputs.clone(),
                        surface_arg_shapes: edge.surface_arg_shapes.clone(),
                        resolution: edge.resolution.clone(),
                        capture_semantic_inputs: edge.capture_semantic_inputs.clone(),
                        surface_semantic_inputs: edge.surface_semantic_inputs.clone(),
                    }
                })
                .collect(),
            selection: selection.plan,
        })
    };
    let (callable_facts, boundary_facts) = builder.finish(world.types());
    Ok(CallableConstructionOwner {
        layout: TransportLayout {
            structural: world.intern_shape(ShapeDescr::Callable(callable)),
            carrier: if demand.callable.is_first_class() {
                TransportCarrier::ValueRef(value_lane(world, callable_ty))
            } else {
                TransportCarrier::Absent
            },
        },
        construction,
        callable_facts,
        boundary_facts,
    })
}

/// The callsite's result value and whether the call sits in tail position
/// (`ControlDestination::Return`), where the result aliases the caller's
/// return. `None` when the callsite id names no call tail in this body.
fn callsite_result(facts: &ExecutableFacts, callsite: CallSiteId) -> Option<(ValueId, bool)> {
    let LoweredBody::Clauses { entries, .. } = facts.body() else {
        return None;
    };
    entries.iter().find_map(|entry| match &entry.tail {
        LoweredTail::DirectCall {
            value,
            callsite: tail_callsite,
            dest,
            ..
        }
        | LoweredTail::ClosureCall {
            value,
            callsite: tail_callsite,
            dest,
            ..
        } if *tail_callsite == callsite => Some((*value, matches!(dest, ControlDestination::Return))),
        _ => None,
    })
}

fn resume_payload_value(facts: &ExecutableFacts, entry: ControlEntryId) -> ValueId {
    match facts.body() {
        LoweredBody::Clauses { entries, .. } => entries
            .get(entry.as_u32() as usize)
            .and_then(|entry| match entry.origin {
                super::super::body::ControlEntryOrigin::DeliveredResume { value } => Some(value),
                _ => None,
            })
            .expect("a resume payload position must name a delivered-resume entry"),
        LoweredBody::Extern { .. } => panic!("an extern executable cannot own a resume payload"),
    }
}

/// The value an entry-capture position names, if the entry has that capture.
fn entry_capture_value(facts: &ExecutableFacts, entry: ControlEntryId, capture_index: usize) -> Option<ValueId> {
    match facts.body() {
        LoweredBody::Clauses { entries, .. } => entries
            .get(entry.as_u32() as usize)
            .and_then(|entry| entry.captures.get(capture_index))
            .copied(),
        LoweredBody::Extern { .. } => None,
    }
}

/// The analyzed type of an entry capture — an invariant, not a lookup with a
/// fallback.
///
/// This used to default a missing type to `any`, the same silent lie
/// fz-f98.17 removed from the semantic layer: a capture whose type the analysis
/// never produced is a hole, and `any` turns it into a wrong answer that the
/// cumulative join can never retract. The default is provably dead — the whole
/// lib suite and the fixture matrix run without reaching it — so it says so out
/// loud instead (fz-f98.18). Its sibling `resume_payload_ty` below is the same
/// shape for the same reason.
fn entry_capture_ty(executable: &ExecutableKey, facts: &ExecutableFacts, capture: ValueId) -> Ty {
    facts.analysis().value_types.get(&capture).copied().unwrap_or_else(|| {
        panic!("an entry capture must have an analyzed type: {capture:?} in executable {executable:?}")
    })
}

fn resume_payload_ty(types: &Types, executable: &ExecutableKey, facts: &ExecutableFacts, entry: ControlEntryId) -> Ty {
    let value = resume_payload_value(facts, entry);
    facts.analysis().value_types.get(&value).copied().unwrap_or_else(|| {
        // fz-hwn.27.5 — name the predicate at the failure site, as native
        // lowering does. An executable whose activation inputs are a value
        // template is not a runtime specialization: no call can supply a bare
        // variable, so a call THROUGH such a slot is dead and its delivered
        // value never exists.
        //
        // The cure is not pruning the activation — that was tried at three
        // boundaries and falsified; value-template activations are legitimate
        // semantic facts and some of them do materialize. The cure is upstream
        // in the semantics: `callee_has_no_inhabitants` makes the call dead and
        // gives it the empty type, so the value has a type and this arm never
        // fires (fz-f98.18). Defaulting to `any` here is the defect fz-f98.17
        // removed.
        if types.key_is_value_template(executable.activation.inputs()) {
            panic!(
                "transport invariant failed: resume payload value {:?} in executable {:?} has no \
                 analyzed type because the activation is a value template — a value-template \
                 activation reached transport and cannot be materialized (fz-hwn.23; predicate \
                 key_is_value_template)",
                value, executable,
            )
        }
        panic!("a resume payload value must have an analyzed type: {value:?} in executable {executable:?}")
    })
}

fn produce_named_transport_position(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
    position: &TransportPosition,
) -> Option<PullOutcome> {
    let facts = context.read_executable_facts(world, executable);
    let runtime = context.read_runtime_demand_fact(world, executable);
    let position_fact = match position {
        TransportPosition::ExecutableInput { .. } => Some(FactKey::ActivationInputs(executable.activation.clone())),
        TransportPosition::ExecutableReturn { .. } | TransportPosition::ReturnPayload { .. } => {
            Some(FactKey::ReturnType(executable.activation.clone()))
        }
        _ => None,
    };
    let position_fact_ready = position_fact
        .as_ref()
        .is_none_or(|fact| context.read_fact(world, FactUse::settled(fact.clone())));
    let mut waits = Vec::new();
    if facts.is_none() {
        waits.push(PullWait::Fact(FactUse::settled(FactKey::ExecutableFacts(
            executable.clone(),
        ))));
    }
    if runtime.is_none() {
        waits.push(PullWait::Fact(FactUse::settled(FactKey::RuntimeDemand(
            executable.clone(),
        ))));
    }
    if !position_fact_ready {
        waits.push(PullWait::Fact(FactUse::settled(
            position_fact.expect("an unready position fact must exist"),
        )));
    }
    if !waits.is_empty() {
        return Some(PullOutcome::Waiting(waits));
    }
    let facts = facts.expect("executable-facts wait should have been satisfied");
    let runtime = runtime.expect("runtime-demand wait should have been satisfied");
    let symbol = position.executable().clone();
    let mut recipe = TransportRecipe::Terminal;
    let (ty, demand) = match position {
        TransportPosition::ExecutableInput { semantic_index, .. } => {
            let ty = world
                .activation_inputs_joined(&executable.activation)
                .unwrap_or_else(|| executable.activation.inputs().to_vec())
                .get(*semantic_index)
                .copied()
                .unwrap_or_else(|| world.types_mut().any());
            let demand = runtime.input_demands.get(*semantic_index).cloned().unwrap_or_default();
            (ty, demand)
        }
        TransportPosition::ExecutableReturn { .. } => {
            let Some(ty) = world.activation_return(&executable.activation) else {
                return Some(bottom_transport_shape(world));
            };
            recipe = TransportRecipe::Alternatives(
                facts
                    .return_origins()
                    .iter()
                    .map(|origin| origin_transport_recipe(&symbol, &facts, origin))
                    .collect(),
            );
            (ty, runtime.return_demand.clone())
        }
        TransportPosition::Value { value, .. } => {
            let ty = facts
                .analysis()
                .value_types
                .get(value)
                .copied()
                .unwrap_or_else(|| world.types_mut().any());
            let demand = runtime.value_demands.get(value).cloned().unwrap_or_default();
            match facts.value_origin(*value) {
                Some(TransportSource::CallableValue(_)) if runtime.callable_flows.contains_key(value) => {
                    let key = ProductKey::CallableConstruction(position.clone());
                    return Some(match context.read_product(tel, key.clone(), world.types()) {
                        Some(ProductValue::CallableConstruction(construction)) => PullOutcome::Produced(
                            ProductValue::TransportShape(TransportShapeFact::Layout(construction.layout)),
                        ),
                        Some(value) => panic!("callable construction produced unexpected value {value:?}"),
                        None => PullOutcome::wait_on_product(key),
                    });
                }
                Some(origin) => recipe = origin_transport_recipe(&symbol, &facts, origin),
                None => {}
            }
            (ty, demand)
        }
        TransportPosition::CallArg {
            callsite,
            semantic_index,
            ..
        } => {
            let arg = callsite_call_args(facts.body())
                .get(callsite)
                .and_then(|args| args.get(*semantic_index))
                .cloned();
            let Some(arg) = arg else {
                let ty = world.types_mut().any();
                let demand = runtime
                    .call_arg_demands
                    .get(callsite)
                    .and_then(|demands| demands.get(*semantic_index))
                    .cloned()
                    .unwrap_or_default();
                let layout = derived_transport_layout(world, ty, &demand, &[]);
                return Some(PullOutcome::Produced(ProductValue::TransportShape(
                    TransportShapeFact::Layout(layout),
                )));
            };
            let args_len = callsite_call_args(facts.body()).get(callsite).map_or(0, Vec::len);
            let mode = callsite_input_modes(facts.body()).get(callsite).copied();
            let need = facts
                .callsite_needs()
                .get(callsite)
                .copied()
                .unwrap_or(ExecutableNeed::Value);
            if let (Some(mode), Some(summary)) = (mode, facts.callsites().get(callsite)) {
                for target in &summary.targets {
                    let Some(activation) = &target.activation else {
                        continue;
                    };
                    let Some(target_index) = mode.semantic_index(activation.input_len(), args_len, *semantic_index)
                    else {
                        continue;
                    };
                    let target = TransportRecipe::Alias(TransportPosition::ExecutableInput {
                        executable: ExecutableSymbol::from_key(&ExecutableKey {
                            activation: activation.clone(),
                            need,
                        }),
                        semantic_index: target_index,
                    });
                    match &mut recipe {
                        TransportRecipe::Alternatives(targets) => targets.push(target),
                        TransportRecipe::Terminal => recipe = TransportRecipe::Alternatives(vec![target]),
                        _ => unreachable!(),
                    }
                }
            }
            let ty = facts
                .analysis()
                .value_types
                .get(&arg.value)
                .copied()
                .unwrap_or_else(|| world.types_mut().any());
            let demand = runtime
                .call_arg_demands
                .get(callsite)
                .and_then(|demands| demands.get(*semantic_index))
                .cloned()
                .or_else(|| runtime.value_demands.get(&arg.value).cloned())
                .unwrap_or_default();
            (ty, demand)
        }
        TransportPosition::ReturnPayload { callsite, .. } => {
            let Some(caller_return_ty) = world.activation_return(&executable.activation) else {
                return Some(bottom_transport_shape(world));
            };
            recipe = origin_transport_recipe(
                &symbol,
                &facts,
                facts
                    .callsite_return_origin(*callsite)
                    .expect("every return payload must have a normalized callsite origin"),
            );
            // The payload is the CALLSITE RESULT's contract. A tail-positioned
            // call's result IS the caller's return, so those alias; a
            // delivered result has its own value, whose type and demand are
            // the contract -- a discarded result carries no demand and must
            // publish no lanes, the same zero its callee-side boundary
            // derives. Deriving the delivered case from the caller's OWN
            // return instead compiled the two halves of one calling
            // convention against different lane counts (fz-f98.14.11).
            match callsite_result(&facts, *callsite) {
                Some((value, false)) => (
                    facts
                        .analysis()
                        .value_types
                        .get(&value)
                        .copied()
                        .unwrap_or_else(|| world.types_mut().any()),
                    runtime.value_demands.get(&value).cloned().unwrap_or_default(),
                ),
                _ => (caller_return_ty, runtime.return_demand.clone()),
            }
        }
        TransportPosition::EntryCapture {
            entry, capture_index, ..
        } => {
            let capture = entry_capture_value(&facts, *entry, *capture_index)?;
            recipe = TransportRecipe::Alias(TransportPosition::Value {
                executable: symbol,
                value: capture,
            });
            (
                entry_capture_ty(executable, &facts, capture),
                runtime
                    .entry_capture_demands
                    .get(entry)
                    .and_then(|demands| demands.get(*capture_index))
                    .cloned()
                    .unwrap_or_default(),
            )
        }
        TransportPosition::ResumePayload { callsite, entry, .. } => {
            let value = resume_payload_value(&facts, *entry);
            if let Some(callsite) = callsite {
                recipe = origin_transport_recipe(
                    &symbol,
                    &facts,
                    facts
                        .callsite_return_origin(*callsite)
                        .expect("every resume payload must have a normalized callsite origin"),
                );
            } else {
                recipe = TransportRecipe::Alias(TransportPosition::Value {
                    executable: symbol,
                    value,
                });
            }
            (
                resume_payload_ty(world.types(), executable, &facts, *entry),
                runtime.value_demands.get(&value).cloned().unwrap_or_default(),
            )
        }
    };

    if demand.is_ignore() {
        return Some(bottom_transport_shape(world));
    }
    let names_in_component_direct_return = match cut_recursive_edges(world, context, executable, &mut recipe) {
        Ok(names_direct) => names_direct,
        Err(fact) => return Some(PullOutcome::wait_on_fact(fact)),
    };
    // A CALLABLE return is exempt: a callable's form is not a lane contract but
    // the row its own demand names, which `exact_direct_callable_layout`
    // derives from facts alone and every view of the convention reaches the
    // same way (fz-9i4.4.5). `tuple_refined_demand` stands aside for the same
    // reason -- there is no type contract to state for a clause set.
    let cycle_return = names_in_component_direct_return
        && matches!(position, TransportPosition::ExecutableReturn { .. })
        && !demand.is_callable();

    let mut layout = match evaluate_transport_recipe(world, tel, context, &recipe, ty, &demand, position) {
        RecipeLayout::Waiting(key) => return Some(PullOutcome::wait_on_product(key)),
        // A return whose recipe names an in-component DIRECT return publishes
        // the CONTRACT, however much
        // its own arms saw. The cut falls on one side of the cycle only, so the
        // members do not all read each other: a form drawn from what one member
        // happened to see cannot bind the rest, and the caller that returns
        // this value derives its payload from the contract too. Deriving the
        // same way is what leaves one recursive chain on one form -- and a call
        // whose three ends name one form is a TAIL call (fz-kdt.97).
        //
        // The arms are still read: they are this position's dependencies
        // whether or not they decide it.
        _ if cycle_return => contract_transport_layout(world, ty, &demand),
        RecipeLayout::Exact(layout) => layout,
        RecipeLayout::Cut(evidence) => cut_transport_layout(world, ty, &demand, &evidence),
    };
    if extern_position_requires_value_ref(world, facts.body(), position, layout) {
        layout = with_value_ref_carrier(world, ty, layout);
    }
    Some(PullOutcome::Produced(ProductValue::TransportShape(
        TransportShapeFact::Layout(layout),
    )))
}

fn extern_position_requires_value_ref(
    world: &World,
    body: &LoweredBody,
    position: &TransportPosition,
    layout: TransportLayout,
) -> bool {
    let LoweredBody::Extern { signature } = body else {
        return false;
    };
    let composite = matches!(
        world.shape(layout.structural),
        ShapeDescr::Tuple(_) | ShapeDescr::Callable(_)
    );
    match position {
        TransportPosition::ExecutableInput { semantic_index, .. } => signature
            .params
            .get(*semantic_index)
            .is_some_and(|param| *param == crate::fz_ir::ExternTy::Any && composite),
        TransportPosition::ExecutableReturn { .. } => signature.ret == crate::fz_ir::ExternTy::Any && composite,
        _ => false,
    }
}

fn with_value_ref_carrier(world: &mut World, ty: Ty, mut layout: TransportLayout) -> TransportLayout {
    if matches!(world.shape(layout.structural), ShapeDescr::Nothing) {
        return layout;
    }
    if !layout_carries(world, layout, ty) {
        let complete = tuple_refined_demand(world, ty, &RuntimeDemand::whole());
        layout = derived_transport_layout(world, ty, &complete, &[]);
    }
    layout.carrier = TransportCarrier::ValueRef(value_lane(world, ty));
    layout
}

/// The form a position settles on when a cut left its evidence incomplete.
///
/// The arms that WERE readable still decide, exactly as they do without a cut
/// -- but only while their agreed form still carries the whole value. The
/// unread arm delivers values of the position's own type too, and a form that
/// only fits the arms it saw can be narrower than that type, leaving those
/// values no room to travel. The type-and-demand form is the fallback: the one
/// contract both ends of the cut derive from facts alone.
fn cut_transport_layout(
    world: &mut World,
    ty: Ty,
    demand: &RuntimeDemand,
    evidence: &[TransportLayout],
) -> TransportLayout {
    if !evidence.is_empty() {
        let layout = derived_transport_layout(world, ty, demand, evidence);
        if layout_carries(world, layout, ty) {
            return layout;
        }
    }
    contract_transport_layout(world, ty, demand)
}

/// The form a position's own type and demand describe -- the ONE contract
/// derived from facts alone, with nothing read.
///
/// It is what both ends of an unreadable edge can name without reading each
/// other, so it is what a cut settles on, and it is what every return on a
/// recursion cycle publishes. Two positions that share a type and a demand
/// reach the same form here by construction, which is the whole point: a
/// calling convention has more than one view of it, and they must agree.
fn contract_transport_layout(world: &mut World, ty: Ty, demand: &RuntimeDemand) -> TransportLayout {
    let contract = tuple_refined_demand(world, ty, demand);
    derived_transport_layout(world, ty, &contract, &[])
}

/// A whole-value demand on an exact tuple type, read as the per-field demand it
/// stands for -- the same reading `boundary_runtime_demand` gives a boundary's
/// contract, for the same reason.
///
/// Only the contract asks. Elsewhere a position's form comes from sources it
/// actually read, or from a demand a consumer actually stated; where the
/// contract is reached the form must be INVENTED, and every end has to invent
/// the same one from the same fact. A value of an exact tuple type is built
/// decomposed, so the form its type describes is the form it already travels
/// in.
fn tuple_refined_demand(world: &mut World, ty: Ty, demand: &RuntimeDemand) -> RuntimeDemand {
    let ShapeDemand::Whole = demand.shape else {
        return demand.clone();
    };
    if demand.is_callable() {
        return demand.clone();
    }
    let Some(fields) = exact_tuple_field_tys(world, ty) else {
        return demand.clone();
    };
    let mut refined = demand.clone();
    refined.shape = ShapeDemand::TupleFields(
        fields
            .into_iter()
            .map(|field_ty| tuple_refined_demand(world, field_ty, &RuntimeDemand::whole()))
            .collect(),
    );
    refined
}

/// Whether every value of `ty` has somewhere to travel in `shape`. A callable
/// shape answers for its whole type by construction -- its identity is the
/// clause set, not a lane -- so it always carries.
fn shape_carries(world: &mut World, shape: ShapeId, ty: Ty) -> bool {
    match world.shape(shape).clone() {
        ShapeDescr::Nothing => world.types().is_empty(&ty),
        ShapeDescr::Lane(lane) => {
            let lane_ty = world.lane(lane).ty;
            world.types().is_subtype(&ty, &lane_ty)
        }
        ShapeDescr::Tuple(fields) => {
            world.types().exclusive_tuple_root_arity(&ty) == Some(fields.len())
                && tuple_field_tys(world, ty, fields.len())
                    .into_iter()
                    .zip(fields.iter().copied())
                    .all(|(field_ty, field)| layout_carries(world, field, field_ty))
        }
        ShapeDescr::Callable(_) => true,
    }
}

fn layout_carries(world: &mut World, layout: TransportLayout, ty: Ty) -> bool {
    match layout.carrier {
        TransportCarrier::Absent => shape_carries(world, layout.structural, ty),
        TransportCarrier::ValueRef(lane) => {
            let lane_ty = world.lane(lane).ty;
            world.types().is_subtype(&ty, &lane_ty)
        }
    }
}

/// Cuts the recursion out of a recipe before it is evaluated, so evaluation is
/// a function of settled facts and of products that can settle without it.
///
/// Every cycle in the position graph runs through some executable return: a
/// body's own positions follow its acyclic def-use, so leaving a body means
/// naming a callee's return. There are two kinds of such edge and each is cut
/// on its own terms.
///
/// A DIRECT call's edge is an edge of the static call graph. Both its ends lie
/// on the cycle, so they are mutually reachable and share a component -- and
/// the edges of one cycle cannot all climb, so at least one names a callee
/// whose function id does not rise. Cutting exactly those leaves the surviving
/// same-component edges strictly climbing, and cross-component ones can close
/// nothing because the condensation is a DAG.
///
/// A GROUNDED CLOSURE call's edge is not in that graph at all: it reaches its
/// callee through a value. A closure built outside a recursion and threaded
/// back through it leaves caller and lambda in different components, so the
/// argument above has nothing to stand on and would leave the cycle whole.
/// `cut_in_component_returns` asks the one-way question instead, which keeps
/// the condensation a DAG and the whole argument true.
///
/// Both choices read call-graph facts alone, so the same edges are cut in
/// every run. What keeps one recursive chain on one form is not the surviving
/// edges -- they run one way round the cycle only -- but the contract every
/// return on the cycle publishes: the answer this returns says which returns
/// those are.
fn cut_recursive_edges(
    world: &World,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
    recipe: &mut TransportRecipe,
) -> Result<bool, FactUse<FactKey>> {
    let owner = executable.activation.function;
    let component = settled_component(world, context, owner)?;
    cut_in_component_returns(world, context, component, owner, recipe)
}

/// Cuts the in-component return edges that do not rise, and answers whether the
/// recipe named an in-component return AT ALL -- cut or kept. Both ends of such
/// an edge lie on one recursion cycle, and the position that owns this recipe
/// is one of them.
fn cut_in_component_returns(
    world: &World,
    context: &mut ProductReadContext<'_>,
    component: FunctionId,
    owner: FunctionId,
    recipe: &mut TransportRecipe,
) -> Result<bool, FactUse<FactKey>> {
    let mut on_cycle = false;
    match recipe {
        TransportRecipe::Alias(child @ TransportPosition::ExecutableReturn { .. }) => {
            let callee = child.executable().activation.function;
            on_cycle = settled_component(world, context, callee)? == component;
            if on_cycle && callee.as_u32() <= owner.as_u32() {
                *recipe = TransportRecipe::CutEdge;
            }
        }
        TransportRecipe::Alternatives(children) | TransportRecipe::Tuple(children) => {
            for child in children {
                on_cycle |= cut_in_component_returns(world, context, component, owner, child)?;
            }
        }
        TransportRecipe::Projection { source: tuple, .. } => {
            on_cycle = cut_in_component_returns(world, context, component, owner, tuple)?;
        }
        TransportRecipe::ClosureCallReturn { grounded, .. } => {
            // A closure call reaches its callee through a VALUE, so the static
            // graph carries no edge for it: a closure built outside a
            // recursion and threaded back through it leaves caller and lambda
            // in DIFFERENT components, and the licence above -- keep a
            // cross-component edge, because no static path returns -- is void.
            // Ask the returning question directly instead. If the target
            // cannot reach this function statically then adding this edge
            // leaves the condensation a DAG and the grounding is safe to keep,
            // which is what preserves one authority for an exact-carrier
            // closure call (fz-9i4.4.5).
            // This arm deliberately does NOT set `on_cycle`: a data-returning
            // cycle carried only by closure edges keeps its evidence form
            // instead of the contract. This existing cut rule applies to each
            // closed target as well as public calls; it is not a proof that
            // arbitrary callable return cycles have a finite private layout
            // (fz-kdt.100 records that residual).
            for grounded in grounded {
                if let TransportRecipe::Alias(child) = &grounded.return_recipe
                    && statically_reaches(world, context, child.executable().activation.function, owner)?
                {
                    grounded.return_recipe = TransportRecipe::CutEdge;
                }
            }
        }
        TransportRecipe::Terminal
        | TransportRecipe::PublicCallableReturn
        | TransportRecipe::CutEdge
        | TransportRecipe::Alias(_) => {}
    }
    Ok(on_cycle)
}

/// Whether `from` reaches `owner` through the static call graph, walking the
/// `StaticCallees` edge facts the same way `derive_call_graph_component` does.
///
/// `CallGraphComponent` answers MUTUAL reachability, which is an equality; a
/// closure call needs the one-way question, and only for the rare grounded
/// edge, so it is asked here rather than turned into a fact of its own. The
/// walk looks for `owner` itself and never consults a component: reaching any
/// member of `owner`'s component means reaching `owner`, because the members
/// of a component all reach each other, so the transitive walk finds `owner`
/// too.
fn statically_reaches(
    world: &World,
    context: &mut ProductReadContext<'_>,
    from: FunctionId,
    owner: FunctionId,
) -> Result<bool, FactUse<FactKey>> {
    let mut seen = BTreeSet::new();
    let mut frontier = vec![from];
    while let Some(function) = frontier.pop() {
        if function == owner {
            return Ok(true);
        }
        if !seen.insert(function) {
            continue;
        }
        let fact = FactUse::settled(FactKey::StaticCallees(function));
        if !context.read_fact(world, fact.clone()) {
            return Err(fact);
        }
        frontier.extend(world.static_callees(function).iter().copied());
    }
    Ok(false)
}

fn settled_component(
    world: &World,
    context: &mut ProductReadContext<'_>,
    function: FunctionId,
) -> Result<FunctionId, FactUse<FactKey>> {
    let fact = FactUse::settled(FactKey::CallGraphComponent(function));
    if !context.read_fact(world, fact.clone()) {
        return Err(fact);
    }
    Ok(world
        .call_graph_component(function)
        .unwrap_or_else(|| panic!("settled CallGraphComponent({function:?}) must name a component")))
}

fn bottom_transport_shape(world: &mut World) -> PullOutcome {
    let layout = TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing));
    PullOutcome::Produced(ProductValue::TransportShape(TransportShapeFact::Layout(layout)))
}

fn append_origin_children(
    symbol: &ExecutableSymbol,
    facts: &ExecutableFacts,
    origin: &TransportSource,
    children: &mut Vec<TransportPosition>,
) -> bool {
    match origin {
        TransportSource::ExecutableInput(semantic_index) => children.push(TransportPosition::ExecutableInput {
            executable: symbol.clone(),
            semantic_index: *semantic_index,
        }),
        TransportSource::LocalValue(value) => children.push(TransportPosition::Value {
            executable: symbol.clone(),
            value: *value,
        }),
        TransportSource::CallsiteReturn(callsite) => {
            let Some(summary) = facts.callsites().get(callsite) else {
                return false;
            };
            let need = facts
                .callsite_needs()
                .get(callsite)
                .copied()
                .unwrap_or(ExecutableNeed::Value);
            for target in &summary.targets {
                match (&target.callee, &target.activation) {
                    (SelectedCallee::ProviderBoundary(_), _) | (_, None) => return false,
                    (SelectedCallee::Function(_), Some(activation)) => {
                        children.push(TransportPosition::ExecutableReturn {
                            executable: ExecutableSymbol::from_key(&ExecutableKey {
                                activation: activation.clone(),
                                need,
                            }),
                        });
                    }
                }
            }
        }
        TransportSource::ClosureCallReturn { callsite, callee } => {
            // The carrier decides whether each owned target's exact return
            // can ground the result. Keep every dependency for invalidation.
            children.push(TransportPosition::Value {
                executable: symbol.clone(),
                value: *callee,
            });
            if let Some(summary) = facts.callsites().get(callsite) {
                let need = facts
                    .callsite_needs()
                    .get(callsite)
                    .copied()
                    .unwrap_or(ExecutableNeed::Value);
                for target in &summary.targets {
                    if let (SelectedCallee::Function(_), Some(activation)) = (&target.callee, &target.activation) {
                        children.push(TransportPosition::ExecutableReturn {
                            executable: ExecutableSymbol::from_key(&ExecutableKey {
                                activation: activation.clone(),
                                need,
                            }),
                        });
                    }
                }
            }
        }
        TransportSource::Join(origins) => {
            for origin in origins {
                if !append_origin_children(symbol, facts, origin, children) {
                    return false;
                }
            }
        }
        TransportSource::TupleValue(values) => children.extend(values.iter().map(|value| TransportPosition::Value {
            executable: symbol.clone(),
            value: *value,
        })),
        TransportSource::Projection { source, .. } => children.push(TransportPosition::Value {
            executable: symbol.clone(),
            value: *source,
        }),
        TransportSource::OutcomeSubject { owner, subject } => {
            let (source, _) = facts.body().dispatch_subject_origin(*owner, *subject);
            let super::super::body::SubjectOriginRoot::Value(source) = source else {
                return false;
            };
            children.push(TransportPosition::Value {
                executable: symbol.clone(),
                value: source,
            });
        }
        TransportSource::CallableValue(_) => return false,
    }
    true
}

/// What a position needs to name a callable demand's EXACT direct layout: the
/// position itself -- a closure standing among its own captures cannot read
/// them -- and a way to read the target's capture positions.
///
/// A derivation with nothing to read still answers; it answers with the generic
/// boxed callable, the one shape both ends of an unread edge can name.
struct CallableReads<'a, 'ctx, T: crate::telemetry::Telemetry> {
    tel: &'a T,
    context: &'a mut ProductReadContext<'ctx>,
    position: &'a TransportPosition,
}

impl<'ctx, T: crate::telemetry::Telemetry> CallableReads<'_, 'ctx, T> {
    fn reborrow(&mut self) -> CallableReads<'_, 'ctx, T> {
        CallableReads {
            tel: self.tel,
            context: self.context,
            position: self.position,
        }
    }
}

fn reborrow_reads<'r, 'ctx, T: crate::telemetry::Telemetry>(
    reads: &'r mut Option<CallableReads<'_, 'ctx, T>>,
) -> Option<CallableReads<'r, 'ctx, T>> {
    reads.as_mut().map(CallableReads::reborrow)
}

/// The layout a type and demand describe with nothing read.
///
/// Naming a callable's exact direct layout means reading its target's capture
/// positions, so a derivation with no reads settles every callable on the
/// generic boxed shape -- and, having nothing to wait on and no capture cycle
/// to cut, it always answers exactly.
///
/// Only the reads make an interrupted answer possible, so a return type that
/// could not express one would have to be chosen by the presence of the reads:
/// that means a second return type threaded through the whole recursion, for
/// one call site. The claim is cheaper stated here than paid for there.
fn derived_transport_layout(
    world: &mut World,
    ty: Ty,
    demand: &RuntimeDemand,
    layouts: &[TransportLayout],
) -> TransportLayout {
    let no_reads: Option<CallableReads<'_, '_, crate::telemetry::sink::NullTelemetry>> = None;
    match joined_transport_layout(world, no_reads, ty, demand, layouts) {
        RecipeLayout::Exact(layout) => layout,
        RecipeLayout::Cut(_) | RecipeLayout::Waiting(_) => {
            unreachable!("a derivation that reads nothing has nothing to wait on and no capture cycle to cut")
        }
    }
}

fn joined_transport_layout<T: crate::telemetry::Telemetry>(
    world: &mut World,
    mut reads: Option<CallableReads<'_, '_, T>>,
    ty: Ty,
    demand: &RuntimeDemand,
    layouts: &[TransportLayout],
) -> RecipeLayout {
    if let [first, rest @ ..] = layouts
        && rest.iter().all(|layout| layout == first)
    {
        return RecipeLayout::Exact(*first);
    }
    let generic = match layout_from_demand(world, reborrow_reads(&mut reads), ty, demand) {
        RecipeLayout::Exact(layout) => layout,
        interrupted => return interrupted,
    };
    if layouts.is_empty() {
        return RecipeLayout::Exact(generic);
    }
    let structural = match joined_tuple_structural(world, reborrow_reads(&mut reads), ty, demand, layouts) {
        Ok(Some(structural)) => structural,
        Ok(None) => generic.structural,
        Err(interrupted) => return interrupted,
    };
    // A called-only receiver can extract a published source's construction
    // and captures into its exact carrier. One escaping alternative does not
    // impose a public wrapper on its otherwise closed siblings.
    let exact_callable = demand.is_callable()
        && !demand.callable.is_first_class()
        && !generic.carrier.is_value_ref()
        && matches!(world.shape(generic.structural), ShapeDescr::Callable(callable)
            if !world.callable(*callable).alternatives().is_empty());
    let carrier = generic.carrier.is_value_ref()
        || (!exact_callable && layouts.iter().any(|layout| layout.carrier.is_value_ref()));
    RecipeLayout::Exact(TransportLayout {
        structural,
        carrier: if carrier {
            TransportCarrier::ValueRef(value_lane(world, ty))
        } else {
            TransportCarrier::Absent
        },
    })
}

/// `Ok(None)` means these alternatives are not a tuple join at all -- the
/// position falls back to the layout its own demand describes.
fn joined_tuple_structural<T: crate::telemetry::Telemetry>(
    world: &mut World,
    mut reads: Option<CallableReads<'_, '_, T>>,
    ty: Ty,
    demand: &RuntimeDemand,
    layouts: &[TransportLayout],
) -> Result<Option<ShapeId>, RecipeLayout> {
    let Some(field_tys) = exact_tuple_field_tys(world, ty) else {
        return Ok(None);
    };
    let arity = field_tys.len();
    let alternatives = layouts
        .iter()
        .map(|layout| match world.shape(layout.structural) {
            ShapeDescr::Tuple(fields) if fields.len() == arity => Some(fields.to_vec()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>();
    let (Some(alternatives), Some(field_demands)) = (alternatives, demand.shape.field_prefix(arity)) else {
        return Ok(None);
    };
    let mut fields = Vec::with_capacity(arity);
    for (index, (field_ty, field_demand)) in field_tys.into_iter().zip(field_demands).enumerate() {
        let layouts = alternatives.iter().map(|fields| fields[index]).collect::<Vec<_>>();
        match joined_transport_layout(world, reborrow_reads(&mut reads), field_ty, &field_demand, &layouts) {
            RecipeLayout::Exact(layout) => fields.push(layout),
            interrupted => return Err(interrupted),
        }
    }
    Ok(Some(world.intern_shape(ShapeDescr::Tuple(fields.into_boxed_slice()))))
}

fn executable_key_for_transport_position(root: RootId, position: &TransportPosition) -> ExecutableKey {
    let symbol = position.executable();
    ExecutableKey {
        activation: ActivationKey {
            root,
            function: symbol.activation.function,
            signature: symbol.activation.signature.clone(),
            callable_surfaces: symbol.activation.callable_surfaces.clone(),
        },
        need: symbol.need,
    }
}

/// A direct edge orders by the SURFACE it is reached through, then by the
/// resolution it names — both canonically (fz-kdt.101), so the edge list a
/// construction wrapper publishes is a function of what the edges say.
fn compare_callable_direct_edges(left: &CallableDirectEdge, right: &CallableDirectEdge, types: &Types) -> Ordering {
    types
        .cmp_activation_tys(&left.surface_inputs, &right.surface_inputs)
        .then_with(|| left.resolution.semantic_cmp(&right.resolution, types))
}

fn extend_unique<T: PartialEq>(target: &mut Vec<T>, values: Vec<T>) {
    for value in values {
        if !target.contains(&value) {
            target.push(value);
        }
    }
}

fn surface_shapes(world: &mut World, surfaces: &BTreeSet<CallableSurface>) -> Vec<Box<[ShapeId]>> {
    surface_shapes_from_layouts(&surface_layouts(world, surfaces))
}

fn surface_shapes_from_layouts(layouts: &[Box<[TransportLayout]>]) -> Vec<Box<[ShapeId]>> {
    layouts
        .iter()
        .map(|layouts| layouts.iter().map(|layout| layout.structural).collect())
        .collect()
}

fn surface_layouts(world: &mut World, surfaces: &BTreeSet<CallableSurface>) -> Vec<Box<[TransportLayout]>> {
    // One shape row per surface, in the SAME order the surfaces are walked:
    // `publish_boundaries_for_callable` zips this result positionally with the
    // same `surfaces` set, so a boundary's `surface_arg_layouts` must be the
    // layouts of the surface it is published for. Sorting the rows here by
    // `ShapeId` (a mint-order index, the agenda's) broke that correspondence,
    // handing a surface the shapes of whichever surface happened to intern a
    // lower shape id -- a schedule-dependent boundary content, visible as the
    // members/boundary desync fz-kdt.108 closes.
    surfaces
        .iter()
        .map(|surface| {
            surface
                .inputs
                .iter()
                .copied()
                .map(|ty| {
                    let demand = boundary_runtime_demand(world, ty);
                    derived_transport_layout(world, ty, &demand, &[])
                })
                .collect::<Vec<_>>()
                .into_boxed_slice()
        })
        .collect()
}

fn callable_direct_edges(
    world: &mut World,
    edges: &[super::super::semantic::CallableFlowEdge],
) -> Vec<CallableDirectEdge> {
    edges
        .iter()
        .map(|edge| CallableDirectEdge {
            surface_inputs: edge.surface.inputs.clone().into_boxed_slice(),
            surface_arg_shapes: surface_shape(world, &edge.surface),
            resolution: ExecutableSymbol::from_key(&edge.resolution),
            capture_semantic_inputs: edge.capture_semantic_inputs.clone(),
            surface_semantic_inputs: edge.surface_semantic_inputs.clone(),
        })
        .collect()
}

fn surface_shape(world: &mut World, surface: &CallableSurface) -> Box<[ShapeId]> {
    surface
        .inputs
        .iter()
        .copied()
        .map(|ty| {
            let demand = boundary_runtime_demand(world, ty);
            derived_transport_layout(world, ty, &demand, &[]).structural
        })
        .collect::<Vec<_>>()
        .into_boxed_slice()
}

/// The layout one type and demand describe, walked recursively. A tuple field
/// is derived exactly as the whole value would be, from the field's own type
/// and its own demand.
fn layout_from_demand<T: crate::telemetry::Telemetry>(
    world: &mut World,
    mut reads: Option<CallableReads<'_, '_, T>>,
    ty: Ty,
    demand: &RuntimeDemand,
) -> RecipeLayout {
    if demand.is_ignore() || world.types().is_empty(&ty) {
        return RecipeLayout::Exact(TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing)));
    }
    if demand.is_callable() {
        return callable_layout_from_demand(world, reads, ty, demand);
    }
    let field_demands = match &demand.shape {
        ShapeDemand::Ignore => {
            return RecipeLayout::Exact(TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing)));
        }
        ShapeDemand::Whole | ShapeDemand::TupleFields(_) => {
            let Some(field_tys) = exact_tuple_field_tys(world, ty) else {
                return RecipeLayout::Exact(TransportLayout::structural(value_lane_shape(world, ty)));
            };
            let Some(field_demands) = demand.shape.field_prefix(field_tys.len()) else {
                return RecipeLayout::Exact(TransportLayout::structural(value_lane_shape(world, ty)));
            };
            field_tys.into_iter().zip(field_demands).collect::<Vec<_>>()
        }
    };
    let mut items = Vec::with_capacity(field_demands.len());
    for (field_ty, field_demand) in field_demands {
        match layout_from_demand(world, reborrow_reads(&mut reads), field_ty, &field_demand) {
            RecipeLayout::Exact(layout) => items.push(layout),
            interrupted => return interrupted,
        }
    }
    RecipeLayout::Exact(TransportLayout::structural(
        world.intern_shape(ShapeDescr::Tuple(items.into_boxed_slice())),
    ))
}

/// The layout a CALLABLE demand produces, at every depth.
///
/// A demand that names its targets, and can read their capture positions, gets
/// the exact direct layout: the target's own identity beside the capture lanes
/// the caller will have to supply. Everything else gets the generic callable,
/// which names no function and carries no captures; a first-class demand puts
/// that one in the `ValueRef` carrier and calls it through the apply seam.
fn callable_layout_from_demand<T: crate::telemetry::Telemetry>(
    world: &mut World,
    reads: Option<CallableReads<'_, '_, T>>,
    ty: Ty,
    demand: &RuntimeDemand,
) -> RecipeLayout {
    if let Some(reads) = reads
        && let Some(exact) = exact_direct_callable_layout(world, reads.tel, reads.context, ty, demand, reads.position)
    {
        return exact;
    }
    let callable = world.intern_callable(CallableDescr::Opaque);
    RecipeLayout::Exact(TransportLayout {
        structural: world.intern_shape(ShapeDescr::Callable(callable)),
        carrier: if demand.callable.is_first_class() {
            TransportCarrier::ValueRef(value_lane(world, ty))
        } else {
            TransportCarrier::Absent
        },
    })
}

fn publish_boundaries_for_callable(
    world: &mut World,
    facts: &mut TransportFactsBuilder,
    callable: CallableId,
    surfaces: &BTreeSet<CallableSurface>,
    surface_layouts: &[Box<[TransportLayout]>],
    published_value_ty: Ty,
    resolution_symbols: &[Vec<ExecutableSymbol>],
    publication: Option<TransportPosition>,
) -> BTreeMap<CallableSurface, BoundaryId> {
    assert_eq!(
        surfaces.len(),
        surface_layouts.len(),
        "boundary surface layouts must align with published surfaces"
    );
    assert_eq!(
        surfaces.len(),
        resolution_symbols.len(),
        "boundary resolution symbols must align with published surfaces"
    );
    let mut boundaries_by_surface = BTreeMap::new();
    for ((surface, arg_layouts), resolutions) in surfaces
        .iter()
        .zip(surface_layouts.iter())
        .zip(resolution_symbols.iter())
    {
        let published_value_lane = value_lane(world, published_value_ty);
        let boundary = world.intern_boundary(BoundaryDescr {
            callable,
            surface_arg_layouts: arg_layouts.clone(),
            published_value_lane,
        });
        if let Some(position) = publication.clone() {
            facts.record_boundary(boundary, position);
        }
        facts.record_boundary_resolutions(boundary, resolutions.clone());
        boundaries_by_surface.insert(surface.clone(), boundary);
    }
    boundaries_by_surface
}

fn boundary_resolution_symbols_for_flow_surfaces(
    flow: &CallableFlowFact,
    surfaces: &BTreeSet<CallableSurface>,
) -> Vec<Vec<ExecutableSymbol>> {
    surfaces
        .iter()
        .map(|surface| {
            flow.first_class_edges
                .iter()
                .filter(|edge| &edge.surface == surface)
                .map(|edge| ExecutableSymbol::from_key(&edge.resolution))
                .collect::<Vec<_>>()
        })
        .collect()
}

fn exact_tuple_field_tys(world: &mut World, ty: Ty) -> Option<Vec<Ty>> {
    let arity = world.types().exclusive_tuple_root_arity(&ty)?;
    Some(tuple_field_tys(world, ty, arity))
}

fn value_lane_shape(world: &mut World, ty: Ty) -> ShapeId {
    let lane = value_lane(world, ty);
    world.intern_shape(ShapeDescr::Lane(lane))
}

fn value_lane(world: &mut World, ty: Ty) -> LaneId {
    let ty = world.types_mut().value_lane_repr(ty);
    world.intern_lane(super::super::transport::LaneDescr {
        ty,
        class: TransportClass::Value,
    })
}

fn tuple_field_tys(world: &mut World, ty: Ty, arity: usize) -> Vec<Ty> {
    let any = world.types_mut().any();
    let mut fields = world.types_mut().tuple_projections(&ty, arity);
    if fields.len() < arity {
        fields.resize(arity, any);
    } else if fields.len() > arity {
        fields.truncate(arity);
    }
    fields
}

fn boundary_runtime_demand(world: &mut World, ty: Ty) -> RuntimeDemand {
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
    RuntimeDemand::callable(CallableDemand {
        resolved: clauses
            .into_iter()
            .map(|clause| CallableSurface::new(clause.args, world.types_mut()))
            .collect::<BTreeSet<_>>(),
        targets: BTreeSet::new(),
        opaque: false,
        escape: true,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn overlapping_capture_types_do_not_mix_construction_rows() {
        let mut world = World::new();
        let function = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "capture", 1);
        let int = world.types_mut().int();
        let any = world.types_mut().any();
        assert!(world.types().is_subtype(&int, &any));
        let mut alternatives = Vec::new();
        let mut targets = Vec::new();
        for ty in [int, any] {
            alternatives.push(CallableAlternative {
                function,
                arity: 1,
                capture_tys: Box::new([ty]),
                capture_layouts: Box::new([TransportLayout::structural(value_lane_shape(&mut world, ty))]),
            });
            let inputs = vec![ty, int];
            targets.push(CallTargetSummary {
                callee: SelectedCallee::Function(function),
                surface_inputs: vec![int],
                activation: Some(ActivationKey::from_inputs(
                    RootId::for_test(0),
                    function,
                    &inputs,
                    world.types_mut(),
                )),
                activation_inputs: Some(inputs),
                extern_params: None,
                return_ty: Some(int),
            });
        }
        let selector = value_lane(&mut world, int);
        let callable = world.intern_callable(CallableDescr::Closed {
            selector,
            alternatives: alternatives.into_boxed_slice(),
        });
        let layout = TransportLayout::structural(world.intern_shape(ShapeDescr::Callable(callable)));
        let arms = closed_call_arms(&mut world, layout, &targets).unwrap();
        assert_eq!(
            arms,
            vec![(0, targets[0].clone()), (1, targets[1].clone())],
            "subtype containment proves admission, not construction identity"
        );
    }

    #[test]
    fn closed_selector_order_uses_source_denotations_not_interning_order() {
        let mut world = World::new();
        let module = super::super::super::identity::ModuleId::GLOBAL;
        let z = world.reference_function(module, "z", 0);
        let a = world.reference_function(module, "a", 0);
        let descriptor = |function| CallableDescr::Direct {
            alternative: CallableAlternative {
                function,
                arity: 0,
                capture_tys: Box::default(),
                capture_layouts: Box::default(),
            },
        };
        let az = combine_callable_requirements(&mut world, &descriptor(a), &descriptor(z)).unwrap();
        let za = combine_callable_requirements(&mut world, &descriptor(z), &descriptor(a)).unwrap();
        assert_eq!(az, za);
        assert_eq!(
            az.alternatives().iter().map(|a| a.function).collect::<Vec<_>>(),
            vec![a, z]
        );
        let callable = world.intern_callable(az);
        let shape = world.intern_shape(ShapeDescr::Callable(callable));
        assert_eq!(
            world.shape_width(shape),
            1,
            "capture-free joins carry only the selector"
        );
    }

    #[test]
    fn selector_distinguishes_capture_schemas_and_combines_invocation_requirements() {
        let mut world = World::new();
        let function = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "factory", 0);
        let int = world.types_mut().int();
        let float = world.types_mut().float();
        let nothing = TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing));
        let int_layout = TransportLayout::structural(value_lane_shape(&mut world, int));
        let alternative = |ty, layout| CallableDescr::Direct {
            alternative: CallableAlternative {
                function,
                arity: 0,
                capture_tys: Box::new([ty]),
                capture_layouts: Box::new([layout]),
            },
        };
        let used = alternative(int, int_layout);
        let unused = alternative(int, nothing);
        let combined = combine_callable_requirements(&mut world, &used, &unused).unwrap();
        assert_eq!(
            combined, used,
            "an invocation does not create a construction alternative"
        );
        let other_schema = alternative(float, nothing);
        let combined = combine_callable_requirements(&mut world, &combined, &other_schema).unwrap();
        assert_eq!(
            combined.alternatives().len(),
            2,
            "even an elided capture retains its construction schema"
        );
        let callable = world.intern_callable(combined);
        let shape = world.intern_shape(ShapeDescr::Callable(callable));
        assert_eq!(world.shape_width(shape), 2, "selector plus the only live capture");
    }

    #[test]
    fn same_source_capture_requirements_retain_concrete_zero_lane_children() {
        let mut world = World::new();
        let module = super::super::super::identity::ModuleId::GLOBAL;
        let function = world.reference_function(module, "holder", 0);
        let captured = world.reference_function(module, "captured", 0);
        let nothing = TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing));
        let captured = world.intern_callable(CallableDescr::Direct {
            alternative: CallableAlternative {
                function: captured,
                arity: 0,
                capture_tys: Box::default(),
                capture_layouts: Box::default(),
            },
        });
        let captured = TransportLayout::structural(world.intern_shape(ShapeDescr::Callable(captured)));
        let left = CallableAlternative {
            function,
            arity: 0,
            capture_tys: Box::new([world.types_mut().any()]),
            capture_layouts: Box::new([tuple_layout(&mut world, &[nothing, captured])]),
        };
        let right = CallableAlternative {
            capture_layouts: Box::new([tuple_layout(&mut world, &[captured, nothing])]),
            ..left.clone()
        };
        let expected = CallableAlternative {
            capture_layouts: Box::new([tuple_layout(&mut world, &[captured, captured])]),
            ..left.clone()
        };
        for (left, right) in [(&left, &right), (&right, &left)] {
            let combined = combine_callable_requirements(
                &mut world,
                &CallableDescr::Direct {
                    alternative: left.clone(),
                },
                &CallableDescr::Direct {
                    alternative: right.clone(),
                },
            )
            .expect("one activation's unused slot does not erase another activation's concrete child");
            assert_eq!(combined.direct().unwrap(), &expected);
            assert!(
                world
                    .layout_physical_lanes(combined.direct().unwrap().capture_layouts[0])
                    .is_empty()
            );
        }
    }

    #[test]
    fn incompatible_capture_requirements_do_not_invent_a_source_payload() {
        let mut world = World::new();
        let function = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "capturing", 0);
        let int = world.types_mut().int();
        let float = world.types_mut().float();
        let left = CallableAlternative {
            function,
            arity: 0,
            capture_tys: Box::new([world.types_mut().any()]),
            capture_layouts: Box::new([TransportLayout::structural(value_lane_shape(&mut world, int))]),
        };
        let right = CallableAlternative {
            capture_layouts: Box::new([TransportLayout::structural(value_lane_shape(&mut world, float))]),
            ..left.clone()
        };
        assert!(
            combine_callable_requirements(
                &mut world,
                &CallableDescr::Direct { alternative: left },
                &CallableDescr::Direct { alternative: right }
            )
            .is_none(),
            "target requirements alone do not prove that the source retained a whole boxed payload"
        );
    }

    #[test]
    fn exact_callable_owner_keeps_typed_target_evidence_from_a_generic_source() {
        let mut world = World::new();
        let function = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "target", 0);
        let ty = world
            .types_mut()
            .fn_ref_lit(crate::types::ClosureTarget(function.as_u32()), 0);
        let activation = super::super::super::ActivationKey::from_inputs(
            super::super::super::RootId::for_test(0),
            function,
            &[],
            world.types_mut(),
        );
        let executable = ExecutableKey {
            activation: activation.clone(),
            need: ExecutableNeed::Value,
        };
        let resolution = ExecutableSymbol::from_key(&executable);
        let surface = CallableSurface::new(Vec::new(), world.types_mut());
        let demand = RuntimeDemand::callable(CallableDemand {
            resolved: BTreeSet::from([surface.clone()]),
            targets: BTreeSet::from([CallableTarget {
                surface,
                activation,
                activation_inputs: Vec::new(),
                need: ExecutableNeed::Value,
            }]),
            opaque: false,
            escape: false,
        });
        let generic = world.intern_callable(CallableDescr::Opaque);
        let exact = world.intern_callable(CallableDescr::Direct {
            alternative: CallableAlternative {
                function,
                arity: 0,
                capture_tys: Box::default(),
                capture_layouts: Box::default(),
            },
        });
        let layout = TransportLayout::structural(world.intern_shape(ShapeDescr::Callable(exact)));
        let position = TransportPosition::Value {
            executable: resolution.clone(),
            value: ValueId::from_u32(0),
        };
        let mut source = TransportFactsBuilder::default();
        source.record_callable(generic, vec![resolution.clone()], Vec::new(), Vec::new(), Vec::new());

        let owner = project_owner_answer(&mut world, &source, layout, ty, &demand, &position);

        assert_eq!(
            owner.layout, layout,
            "projection preserves the consumer's exact zero-lane layout"
        );
        assert_eq!(
            owner.callable_facts.len(),
            1,
            "the owner publishes only its own callable descriptor"
        );
        assert_eq!(
            owner.callable_facts[&exact].resolutions.as_ref(),
            &[resolution],
            "typed target evidence survives a generic-to-exact representation change"
        );
        assert!(owner.construction.is_none());
        assert!(
            owner.boundary_facts.is_empty(),
            "a direct-only consumer creates no runtime boundary"
        );
    }

    #[test]
    fn tuple_carrier_comes_from_the_composite_demand_not_its_child_lanes() {
        let mut world = World::new();
        let atom = world.types_mut().atom();
        let any = world.types_mut().any();
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let atom_lane = value_lane_shape(&mut world, atom);
        let any_lane_id = value_lane(&mut world, any);
        let any_lane = world.intern_shape(ShapeDescr::Lane(any_lane_id));
        let child = TransportLayout {
            structural: any_lane,
            carrier: TransportCarrier::ValueRef(any_lane_id),
        };
        let partial_layout = tuple_layout(&mut world, &[TransportLayout::structural(nothing), child]);
        assert_eq!(partial_layout.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(partial_layout.structural) else {
            panic!("the partial composite should retain its tuple field positions")
        };
        assert_eq!(fields.as_ref(), &[TransportLayout::structural(nothing), child]);

        let complete_fields = [TransportLayout::structural(atom_lane), child];
        let whole = tuple_layout(&mut world, &complete_fields);
        assert_eq!(whole.carrier, TransportCarrier::Absent);
        assert_eq!(
            world.shape(whole.structural),
            &ShapeDescr::Tuple(Box::new([TransportLayout::structural(atom_lane), child,]))
        );

        assert!(
            !tuple_layout(&mut world, &complete_fields).carrier.is_value_ref(),
            "tuple composition never manufactures the composite carrier",
        );
    }

    #[test]
    fn tuple_child_carrier_lane_must_cover_its_field_type() {
        let mut world = World::new();
        let atom = world.types_mut().atom();
        let int = world.types_mut().int();
        let any = world.types_mut().any();
        let tuple_ty = world.types_mut().tuple(&[atom]);
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let int_lane = value_lane(&mut world, int);
        let any_lane = value_lane(&mut world, any);
        let mismatched = world.intern_shape(ShapeDescr::Tuple(Box::new([TransportLayout {
            structural: nothing,
            carrier: TransportCarrier::ValueRef(int_lane),
        }])));
        let covering = world.intern_shape(ShapeDescr::Tuple(Box::new([TransportLayout {
            structural: nothing,
            carrier: TransportCarrier::ValueRef(any_lane),
        }])));

        assert!(!shape_carries(&mut world, mismatched, tuple_ty));
        assert!(shape_carries(&mut world, covering, tuple_ty));
    }

    #[test]
    fn same_arity_tuple_join_keeps_a_child_carrier_local() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let tuple_ty = world.types_mut().tuple(&[int]);
        let lane = value_lane(&mut world, int);
        let scalar = world.intern_shape(ShapeDescr::Lane(lane));
        let structural_child = TransportLayout::structural(scalar);
        let carried_child = TransportLayout {
            structural: scalar,
            carrier: TransportCarrier::ValueRef(lane),
        };
        let structural_tuple = tuple_layout(&mut world, &[structural_child]);
        let carried_tuple = tuple_layout(&mut world, &[carried_child]);
        let joined = derived_transport_layout(
            &mut world,
            tuple_ty,
            &RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole()]),
            &[structural_tuple, carried_tuple],
        );

        assert_eq!(joined.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(joined.structural) else {
            panic!("same-arity tuple alternatives should join field by field")
        };
        assert_eq!(fields.as_ref(), &[carried_child]);
    }

    #[test]
    fn generic_tuple_layout_retains_a_nested_first_class_carrier() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let callable_ty = world.types_mut().fn_ref_lit(crate::types::ClosureTarget(7), 1);
        let tuple_ty = world.types_mut().tuple(&[int, callable_ty]);
        let demand = RuntimeDemand::tuple_fields(vec![
            RuntimeDemand::whole(),
            RuntimeDemand::callable(CallableDemand::escaped()),
        ]);
        let layout = derived_transport_layout(&mut world, tuple_ty, &demand, &[]);

        assert_eq!(layout.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(layout.structural) else {
            panic!("the exact tuple demand should produce a recursive tuple layout")
        };
        assert!(fields[1].carrier.is_value_ref());
        assert!(matches!(world.shape(fields[1].structural), ShapeDescr::Callable(_)));
    }

    #[test]
    fn generic_whole_exact_tuple_stays_complete_and_decomposed() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let tuple_ty = world.types_mut().tuple(&[int, int]);
        let layout = derived_transport_layout(&mut world, tuple_ty, &RuntimeDemand::whole(), &[]);

        assert_eq!(layout.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(layout.structural) else {
            panic!("Whole over an exact tuple must retain complete field layouts")
        };
        assert_eq!(fields.len(), 2);
        assert!(fields.iter().all(|field| field.carrier == TransportCarrier::Absent));
        assert!(
            fields
                .iter()
                .all(|field| matches!(world.shape(field.structural), ShapeDescr::Lane(_)))
        );
    }

    #[test]
    fn generic_partial_exact_tuple_fills_omitted_trailing_fields_with_nothing() {
        let mut world = World::new();
        let atom = world.types_mut().atom();
        let int = world.types_mut().int();
        let tuple_ty = world.types_mut().tuple(&[atom, atom, int, atom]);
        let demand = RuntimeDemand::tuple_fields(vec![
            RuntimeDemand::ignore(),
            RuntimeDemand::ignore(),
            RuntimeDemand::whole(),
        ]);
        let layout = derived_transport_layout(&mut world, tuple_ty, &demand, &[]);

        assert_eq!(layout.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(layout.structural) else {
            panic!("a tuple demand prefix must retain the exact tuple's positions")
        };
        assert_eq!(fields.len(), 4);
        assert!(matches!(world.shape(fields[0].structural), ShapeDescr::Nothing));
        assert!(matches!(world.shape(fields[1].structural), ShapeDescr::Nothing));
        assert!(matches!(world.shape(fields[2].structural), ShapeDescr::Lane(_)));
        assert!(matches!(world.shape(fields[3].structural), ShapeDescr::Nothing));

        // A demand vector longer than the tuple it is read against describes a
        // DIFFERENT tuple -- one clause of a value spanning arities read
        // further than this one has fields. The surplus names no field here and
        // is dropped; the fields that do exist keep their own lanes rather than
        // boxing the whole value over a position it never had.
        let overlong = RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(); 5]);
        let layout = derived_transport_layout(&mut world, tuple_ty, &overlong, &[]);

        assert_eq!(layout.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(layout.structural) else {
            panic!("a surplus field demand must not box the positions the tuple does have")
        };
        assert_eq!(fields.len(), 4);
        assert!(
            fields
                .iter()
                .all(|field| matches!(world.shape(field.structural), ShapeDescr::Lane(_)))
        );
    }

    #[test]
    fn equal_layout_join_returns_without_minting_a_generic_alternative() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let exact = TransportLayout::structural(nothing);
        let before = (world.shape_count(), world.lane_count());

        let joined = derived_transport_layout(&mut world, int, &RuntimeDemand::whole(), &[exact, exact]);

        assert_eq!(joined, exact);
        assert_eq!(
            (world.shape_count(), world.lane_count()),
            before,
            "an exact concordant join must not construct an unused generic layout",
        );
    }
}
