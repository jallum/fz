use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use super::super::body::{
    CallSiteId, ControlDestination, ControlEntryId, LoweredBody, LoweredTail, ValueId, callsite_call_args,
    callsite_input_modes,
};
use super::super::drive::FactKey;
use super::super::executable_facts::{ExecutableFacts, LocalCallableProducer, TransportOrigin as TransportSource};
use super::super::facts::FactUse;
use super::super::identity::{ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, RootId};
use super::super::pull::{
    InputSlot, ProductKey, ProductReadContext, ProductValue, PullOutcome, PullWait, TransportCarrier, TransportLayout,
    TransportShapeFact,
};
use super::super::semantic::{
    CallableDemand, CallableFlowFact, CallableSurface, CallableTarget, ExecutableRuntimeDemand, RuntimeDemand,
    SelectedCallee, SemanticOrd, ShapeDemand,
};
use super::super::transport::{
    ActivationSymbol, BoundaryDescr, BoundaryFacts, BoundaryId, CallableConstructionCapture, CallableConstructionFact,
    CallableConstructionMember, CallableConstructionOwner, CallableDescr, CallableDirectEdge, CallableFacts,
    CallableId, ExecutableSymbol, LaneId, ShapeDescr, ShapeId, TransportClass, TransportPosition,
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
    let facts = match context.read_executable_facts(world, &executable) {
        Some(facts) => facts,
        None => return PullOutcome::wait_on_fact(FactUse::settled(FactKey::ExecutableFacts(executable))),
    };
    let runtime = match context.read_runtime_demand(tel, &executable, world.types()) {
        Some(runtime) => runtime,
        None => return PullOutcome::wait_on_product(ProductKey::RuntimeDemand(executable)),
    };
    let TransportPosition::Value { value, .. } = position else {
        return produce_generic_callable_owner(world, tel, context, &executable, facts.as_ref(), &runtime, position);
    };
    let Some(TransportSource::CallableValue(producer)) = facts.value_origin(*value) else {
        return produce_generic_callable_owner(world, tel, context, &executable, facts.as_ref(), &runtime, position);
    };
    let Some(flow) = runtime.callable_flows.get(value) else {
        return produce_generic_callable_owner(world, tel, context, &executable, facts.as_ref(), &runtime, position);
    };
    let demand = runtime.value_demands.get(value).cloned().unwrap_or_default();
    match produce_local_callable_construction(
        world,
        tel,
        context,
        &executable,
        facts.as_ref(),
        *value,
        producer,
        flow,
        demand,
    ) {
        Ok(answer) => PullOutcome::Produced(ProductValue::CallableConstruction(Rc::new(answer))),
        Err(waits) => PullOutcome::Waiting(waits),
    }
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
    let layout = match context.read_product(tel, shape_key.clone(), world.types()) {
        Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => *layout,
        Some(value) => panic!("transport shape produced unexpected value {value:?}"),
        None => return PullOutcome::wait_on_product(shape_key),
    };
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
                let key = ProductKey::IncomingInputSlot(InputSlot {
                    executable: executable.clone(),
                    semantic_index: *semantic_index,
                });
                match context.read_product(tel, key.clone(), world.types()) {
                    Some(ProductValue::IncomingInputSlot(sources)) => {
                        source_positions.extend(sources.iter().map(|source| TransportPosition::Value {
                            executable: executable_symbol(&source.producer, world.types()),
                            value: source.value,
                        }));
                    }
                    Some(value) => panic!("incoming input slot produced unexpected value {value:?}"),
                    None => return PullOutcome::wait_on_product(key),
                }
            }
            TransportPosition::Value { value, .. } => {
                if let Some(origin) = facts.value_origin(*value)
                    && !append_origin_children(
                        world,
                        executable,
                        position.executable(),
                        facts,
                        origin,
                        &mut source_positions,
                    )
                {
                    source_positions.clear();
                }
            }
            TransportPosition::ExecutableReturn { .. } => {
                for origin in facts.return_origins() {
                    if !append_origin_children(
                        world,
                        executable,
                        position.executable(),
                        facts,
                        origin,
                        &mut source_positions,
                    ) {
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
                    !append_origin_children(
                        world,
                        executable,
                        position.executable(),
                        facts,
                        origin,
                        &mut source_positions,
                    )
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
                        !append_origin_children(
                            world,
                            executable,
                            position.executable(),
                            facts,
                            origin,
                            &mut source_positions,
                        )
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
    let runtime = context
        .settled_runtime_demand(&executable)
        .expect("callable owner group member must have a settled runtime demand");
    let (ty, demand) = generic_owner_ty_and_demand(world, &executable, &facts, runtime, position);
    ProductValue::CallableConstruction(Rc::new(project_owner_answer(
        world, evidence, layout, ty, &demand, position,
    )))
}

/// The answer one position publishes: its evidence projected through the
/// position's OWN layout, analyzed type and demand. Cycle or no cycle, the same
/// derivation -- an owner says only what its own position can carry.
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
                .unwrap_or_else(|| executable.activation.inputs(world.types()))
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
        ShapeDescr::Callable(callable) if world.callable(callable).function.is_none() => {
            record_generic_owner_facts(world, projected, shape, ty, demand, publication);
            let resolutions = exact_demand_resolution_symbols(source, demand, None);
            if let Some(draft) = projected.callables.get_mut(&callable) {
                extend_unique(&mut draft.resolutions, resolutions);
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
        ShapeDescr::Callable(callable) => {
            let Some(draft) = source.callables.get(&callable) else {
                return;
            };
            let boundary_ids = if demand.callable.is_first_class() {
                draft.boundary_ids.clone()
            } else {
                Vec::new()
            };
            projected.record_callable(
                callable,
                exact_demand_resolution_symbols(source, demand, None),
                draft.direct_surfaces.clone(),
                draft.direct_edges.clone(),
                boundary_ids.clone(),
            );
            for boundary in boundary_ids {
                if let Some(facts) = source.boundaries.get(&boundary) {
                    projected.record_boundary_resolutions(boundary, facts.resolutions.clone());
                }
                projected.record_boundary(boundary, publication.clone());
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
                    && resolution.activation.arrow == target.activation.arrow
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
            if world.callable(callable).function.is_some() {
                return;
            }
            let surfaces = &demand.callable.resolved;
            let surface_layouts = surface_layouts(world, surfaces, facts);
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

#[derive(Clone)]
enum TransportRecipe {
    Terminal,
    PublicCallableReturn,
    /// A closure-call result: grounded to the singleton target's return fact
    /// when the callee value's carrier is exact, public boxed when the callee
    /// is a `ValueRef` (the construction-wrapper convention).
    ClosureCallReturn {
        callee: TransportPosition,
        grounded: Option<Box<TransportRecipe>>,
    },
    Alias(TransportPosition),
    /// A recursion edge cut at construction: a child whose transport layout can
    /// never be read here, because reading it would close a cycle in the
    /// position graph. It is the one recipe node with no product behind it.
    CutEdge,
    Alternatives(Vec<Self>),
    Tuple(Vec<Self>),
    TupleField {
        tuple: Box<Self>,
        index: usize,
    },
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
        TransportRecipe::Terminal => exact_direct_callable_layout(world, tel, context, ty, demand, position)
            .unwrap_or_else(|| RecipeLayout::Exact(joined_transport_layout(world, ty, demand, position, &[]))),
        TransportRecipe::PublicCallableReturn => {
            let layout = joined_transport_layout(world, ty, demand, position, &[]);
            RecipeLayout::Exact(with_value_ref_carrier(world, ty, position, layout))
        }
        TransportRecipe::ClosureCallReturn { callee, grounded } => {
            // One authority: `materialize_closure_call_edge` goes direct only
            // when the callee value's carrier is exact; the claim grounds on
            // exactly that condition.
            let callee_key = ProductKey::TransportShape(callee.clone());
            let callee_layout = match context.read_product(tel, callee_key.clone(), world.types()) {
                Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => *layout,
                Some(value) => panic!("closure callee shape produced unexpected value {value:?}"),
                None => return RecipeLayout::Waiting(callee_key),
            };
            match grounded {
                Some(grounded) if !matches!(callee_layout.carrier, TransportCarrier::ValueRef(_)) => {
                    evaluate_transport_recipe(world, tel, context, grounded, ty, demand, position)
                }
                _ => evaluate_transport_recipe(
                    world,
                    tel,
                    context,
                    &TransportRecipe::PublicCallableReturn,
                    ty,
                    demand,
                    position,
                ),
            }
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
                RecipeLayout::Exact(joined_transport_layout(world, ty, demand, position, &layouts))
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
        TransportRecipe::TupleField { tuple, index } => {
            match evaluate_transport_recipe(world, tel, context, tuple, ty, demand, position) {
                RecipeLayout::Exact(layout) => match world.shape(layout.structural) {
                    ShapeDescr::Tuple(fields) => {
                        if let Some(field) = fields.get(*index).copied() {
                            RecipeLayout::Exact(TransportLayout {
                                structural: field.structural,
                                carrier: if layout.carrier.is_value_ref() {
                                    TransportCarrier::ValueRef(value_lane(world, ty))
                                } else {
                                    field.carrier
                                },
                            })
                        } else {
                            RecipeLayout::Exact(joined_transport_layout(world, ty, demand, position, &[]))
                        }
                    }
                    ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => {
                        RecipeLayout::Exact(joined_transport_layout(world, ty, demand, position, &[]))
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

/// The one physical callable layout this position's settled target set names,
/// if the set names exactly one. A transport layout is pure physics, so the
/// question is never "how many targets" but "how many LAYOUTS": several
/// activations of one function — specializations reached at different argument
/// types — describe the same captures, and a value that must reach any of them
/// travels as those captures. Which activation a callsite reaches is decided
/// there, from the argument types it holds (fz-kdt.132), so that choice never
/// has to travel with the value.
///
/// `None` means no single layout covers the set — the position falls back to
/// the generic joined layout, which boxes whenever anything needs the identity.
fn exact_direct_callable_layout(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    ty: Ty,
    demand: &RuntimeDemand,
    position: &TransportPosition,
) -> Option<RecipeLayout> {
    let targets = demand.callable.targets.clone();
    if demand.callable.is_first_class() || targets.is_empty() {
        return None;
    }
    let mut settled: Option<CallableDescr> = None;
    for target in &targets {
        match direct_callable_descr(world, tel, context, ty, demand, position, target) {
            DirectCallableDescr::Descr(descr) => match &settled {
                Some(first) if *first != descr => return None,
                Some(_) => {}
                None => settled = Some(descr),
            },
            // A cut or a not-yet-readable capture answers for the whole
            // position: the Cut LAYOUT is target-independent (built from
            // position/ty/demand alone); a Waiting KEY is that target's own
            // capture position, but waiting on any unread key converges, so
            // which target raised it is behaviorally moot. Where a position
            // could hold BOTH a cycle and a disagreement, BTreeSet order
            // deterministically reaches one first; Cut(ValueRef) is the
            // safer of the two answers.
            DirectCallableDescr::Position(layout) => return Some(layout),
            DirectCallableDescr::Unavailable => return None,
        }
    }
    let callable = world.intern_callable(settled?);
    Some(RecipeLayout::Exact(TransportLayout {
        structural: world.intern_shape(ShapeDescr::Callable(callable)),
        carrier: TransportCarrier::Absent,
    }))
}

/// What one target contributes to [`exact_direct_callable_layout`].
enum DirectCallableDescr {
    /// The callable layout this target names.
    Descr(CallableDescr),
    /// An answer for the whole position, reached before any layout could be
    /// named: a capture cycle's cut, or a capture layout not yet readable.
    Position(RecipeLayout),
    /// This target names no exact layout at all.
    Unavailable,
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
    let executable = executable_symbol(&executable, world.types());
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
            let mut layout = joined_transport_layout(world, ty, demand, position, &[]);
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
    let capture_tys = &target.activation_inputs[..capture_count];
    DirectCallableDescr::Descr(CallableDescr {
        function: Some(target.activation.function),
        // The activation's inputs are the environment followed by the call
        // arguments, so what the environment does not supply is the arity.
        arity: (target.activation_inputs.len() - capture_count) as u16,
        capture_tys: capture_tys.to_vec().into_boxed_slice(),
        capture_layouts: capture_layouts.into_boxed_slice(),
    })
}

/// The one callable row a closure callsite could ground its return against:
/// a settled summary naming exactly one compiler-owned target. Whether the
/// grounding APPLIES is decided at recipe evaluation from the callee value's
/// own transport carrier — the same fact `materialize_closure_call_edge` uses
/// to choose a direct edge — so claim and call share one authority.
fn singleton_closure_call_target(
    facts: &ExecutableFacts,
    callsite: &CallSiteId,
) -> Option<(ActivationKey, ExecutableNeed)> {
    let summary = facts.callsites().get(callsite)?;
    let [target] = summary.targets.as_slice() else {
        return None;
    };
    let (SelectedCallee::Function(_), Some(activation)) = (&target.callee, &target.activation) else {
        return None;
    };
    let need = facts
        .callsite_needs()
        .get(callsite)
        .copied()
        .unwrap_or(ExecutableNeed::Value);
    Some((activation.clone(), need))
}

fn origin_transport_recipe(
    world: &World,
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
                                executable: executable_symbol(
                                    &ExecutableKey {
                                        activation: activation.clone(),
                                        need,
                                    },
                                    world.types(),
                                ),
                            })
                        }
                        (SelectedCallee::ProviderBoundary(_), _) | (_, None) => TransportRecipe::Terminal,
                    })
                    .collect(),
            )
        }
        TransportSource::ClosureCallReturn { callsite, callee } => {
            // A closure-call result refines the authoritative callable row
            // forward (fz-9i4.4.5): when the callee VALUE travels in its exact
            // (non-ValueRef) carrier, `materialize_closure_call_edge` lowers
            // the call as a direct edge to the settled singleton target, so
            // the result aliases that executable's own return fact — caller
            // and callee read one shape and agree by construction. A boxed
            // callee dispatches through the construction wrapper, whose
            // return is the public boxed contract; the claim stays public
            // with it. The gate is deferred to recipe evaluation because the
            // callee's carrier is itself a transport product.
            TransportRecipe::ClosureCallReturn {
                callee: TransportPosition::Value {
                    executable: symbol.clone(),
                    value: *callee,
                },
                grounded: singleton_closure_call_target(facts, callsite).map(|(activation, need)| {
                    Box::new(TransportRecipe::Alias(TransportPosition::ExecutableReturn {
                        executable: executable_symbol(&ExecutableKey { activation, need }, world.types()),
                    }))
                }),
            }
        }
        TransportSource::Join(origins) => TransportRecipe::Alternatives(
            origins
                .iter()
                .map(|origin| origin_transport_recipe(world, symbol, facts, origin))
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
        TransportSource::TupleField { source, index } => TransportRecipe::TupleField {
            tuple: Box::new(TransportRecipe::Alias(TransportPosition::Value {
                executable: symbol.clone(),
                value: *source,
            })),
            index: *index,
        },
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
        let key = ProductKey::RuntimeDemand(resolution.clone());
        let Some(value) = context.read_product(tel, key.clone(), world.types()) else {
            waits.push(PullWait::Product(key));
            continue;
        };
        let ProductValue::RuntimeDemand(resolution_demand) = value else {
            panic!("runtime demand produced unexpected value {value:?}");
        };
        assert!(resolution_demand.input_demands.len() >= capture_tys.len());
        for (capture, input) in capture_demands
            .iter_mut()
            .zip(resolution_demand.input_demands.iter().take(capture_tys.len()))
        {
            capture.join_assign(input);
        }
    }
    let symbol = executable_symbol(executable, world.types());
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
    let direct_surfaces = surface_shapes(world, &flow.direct_surfaces, &mut builder);
    let direct_edges = callable_direct_edges(world, &flow.direct_edges, &mut builder);
    let arity = callable_ty_arity(world, callable_ty);
    let callable = world.intern_callable(CallableDescr {
        function: Some(producer.function),
        arity,
        capture_tys: capture_tys.into_boxed_slice(),
        capture_layouts: capture_layouts.clone().into_boxed_slice(),
    });
    let boundary_surfaces = flow.first_class_surfaces.clone();
    let boundary_layouts = surface_layouts(world, &boundary_surfaces, &mut builder);
    let boundary_resolutions = boundary_resolution_symbols_for_flow_surfaces(flow, &boundary_surfaces, world.types());
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
        flow.resolutions
            .iter()
            .map(|resolution| executable_symbol(resolution, world.types()))
            .collect(),
        direct_surfaces,
        direct_edges,
        boundaries_by_surface.values().copied().collect(),
    );
    let construction = if flow.first_class_edges.is_empty() {
        None
    } else {
        let construction_edges = callable_direct_edges(world, &flow.first_class_edges, &mut builder);
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
                .map(|(value, layout)| CallableConstructionCapture {
                    source: TransportPosition::Value {
                        executable: executable_symbol(executable, world.types()),
                        value,
                    },
                    layout,
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
        if types.key_is_value_template(&executable.activation.inputs(types)) {
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
    let facts = match context.read_executable_facts(world, executable) {
        Some(facts) => facts,
        None => {
            return Some(PullOutcome::wait_on_fact(FactUse::settled(FactKey::ExecutableFacts(
                executable.clone(),
            ))));
        }
    };
    let runtime = match context.read_runtime_demand(tel, executable, world.types()) {
        Some(runtime) => runtime,
        None => {
            return Some(PullOutcome::wait_on_product(ProductKey::RuntimeDemand(
                executable.clone(),
            )));
        }
    };
    let symbol = position.executable().clone();
    let mut recipe = TransportRecipe::Terminal;
    let (ty, demand) = match position {
        TransportPosition::ExecutableInput { semantic_index, .. } => {
            let fact = FactUse::settled(FactKey::ActivationInputs(executable.activation.clone()));
            if !context.read_fact(world, fact.clone()) {
                return Some(PullOutcome::wait_on_fact(fact));
            }
            let ty = world
                .activation_inputs_joined(&executable.activation)
                .unwrap_or_else(|| executable.activation.inputs(world.types()))
                .get(*semantic_index)
                .copied()
                .unwrap_or_else(|| world.types_mut().any());
            let demand = runtime.input_demands.get(*semantic_index).cloned().unwrap_or_default();
            (ty, demand)
        }
        TransportPosition::ExecutableReturn { .. } => {
            let fact = FactUse::settled(FactKey::ReturnType(executable.activation.clone()));
            if !context.read_fact(world, fact.clone()) {
                return Some(PullOutcome::wait_on_fact(fact));
            }
            let Some(ty) = world.activation_return(&executable.activation) else {
                return Some(bottom_transport_shape(world));
            };
            recipe = TransportRecipe::Alternatives(
                facts
                    .return_origins()
                    .iter()
                    .map(|origin| origin_transport_recipe(world, &symbol, &facts, origin))
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
                Some(origin) => recipe = origin_transport_recipe(world, &symbol, &facts, origin),
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
                return Some(produce_generic_transport_layout(
                    world,
                    facts.as_ref(),
                    ty,
                    demand,
                    position,
                ));
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
                    let Some(target_index) =
                        mode.semantic_index(activation.input_len(world.types()), args_len, *semantic_index)
                    else {
                        continue;
                    };
                    let target = TransportRecipe::Alias(TransportPosition::ExecutableInput {
                        executable: executable_symbol(
                            &ExecutableKey {
                                activation: activation.clone(),
                                need,
                            },
                            world.types(),
                        ),
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
            let fact = FactUse::settled(FactKey::ReturnType(executable.activation.clone()));
            if !context.read_fact(world, fact.clone()) {
                return Some(PullOutcome::wait_on_fact(fact));
            }
            let Some(caller_return_ty) = world.activation_return(&executable.activation) else {
                return Some(bottom_transport_shape(world));
            };
            recipe = origin_transport_recipe(
                world,
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
                    world,
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
        _ if cycle_return => contract_transport_layout(world, ty, &demand, position),
        RecipeLayout::Exact(layout) => layout,
        RecipeLayout::Cut(evidence) => cut_transport_layout(world, ty, &demand, position, &evidence),
    };
    if extern_position_requires_value_ref(world, facts.body(), position, layout) {
        layout = with_value_ref_carrier(world, ty, position, layout);
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

fn with_value_ref_carrier(
    world: &mut World,
    ty: Ty,
    position: &TransportPosition,
    mut layout: TransportLayout,
) -> TransportLayout {
    if matches!(world.shape(layout.structural), ShapeDescr::Nothing) {
        return layout;
    }
    if !layout_carries(world, layout, ty) {
        let complete = tuple_refined_demand(world, ty, &RuntimeDemand::whole());
        layout = joined_transport_layout(world, ty, &complete, position, &[]);
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
    position: &TransportPosition,
    evidence: &[TransportLayout],
) -> TransportLayout {
    if !evidence.is_empty() {
        let layout = joined_transport_layout(world, ty, demand, position, evidence);
        if layout_carries(world, layout, ty) {
            return layout;
        }
    }
    contract_transport_layout(world, ty, demand, position)
}

/// The form a position's own type and demand describe -- the ONE contract
/// derived from facts alone, with nothing read.
///
/// It is what both ends of an unreadable edge can name without reading each
/// other, so it is what a cut settles on, and it is what every return on a
/// recursion cycle publishes. Two positions that share a type and a demand
/// reach the same form here by construction, which is the whole point: a
/// calling convention has more than one view of it, and they must agree.
fn contract_transport_layout(
    world: &mut World,
    ty: Ty,
    demand: &RuntimeDemand,
    position: &TransportPosition,
) -> TransportLayout {
    let contract = tuple_refined_demand(world, ty, demand);
    joined_transport_layout(world, ty, &contract, position, &[])
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
            has_exact_tuple_arity(world, ty, fields.len())
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
        TransportRecipe::TupleField { tuple, .. } => {
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
            // instead of the contract. The edge is indirect through the boxed
            // apply seam, so no direct-call tail is at stake (fz-kdt.100
            // records the residual).
            if let Some(target) = grounded.as_deref_mut()
                && let TransportRecipe::Alias(child) = target
                && statically_reaches(world, context, child.executable().activation.function, owner)?
            {
                *target = TransportRecipe::CutEdge;
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
    world: &World,
    executable: &ExecutableKey,
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
                            executable: executable_symbol(
                                &ExecutableKey {
                                    activation: activation.clone(),
                                    need,
                                },
                                world.types(),
                            ),
                        });
                    }
                }
            }
        }
        TransportSource::ClosureCallReturn { callsite, callee } => {
            // The claim depends on the callee value's carrier and, when a
            // singleton target exists, on that target's return fact — so
            // replacement or withdrawal of either product re-settles this
            // position.
            children.push(TransportPosition::Value {
                executable: symbol.clone(),
                value: *callee,
            });
            if let Some((activation, need)) = singleton_closure_call_target(facts, callsite) {
                children.push(TransportPosition::ExecutableReturn {
                    executable: executable_symbol(&ExecutableKey { activation, need }, world.types()),
                });
            }
        }
        TransportSource::Join(origins) => {
            for origin in origins {
                if !append_origin_children(world, executable, symbol, facts, origin, children) {
                    return false;
                }
            }
        }
        TransportSource::TupleValue(values) => children.extend(values.iter().map(|value| TransportPosition::Value {
            executable: symbol.clone(),
            value: *value,
        })),
        TransportSource::TupleField { source, .. } => children.push(TransportPosition::Value {
            executable: symbol.clone(),
            value: *source,
        }),
        TransportSource::CallableValue(_) => return false,
    }
    let _ = executable;
    true
}

fn produce_joined_transport_layout(
    world: &mut World,
    _facts: &ExecutableFacts,
    ty: Ty,
    demand: RuntimeDemand,
    position: &TransportPosition,
    layouts: &[TransportLayout],
) -> PullOutcome {
    PullOutcome::Produced(ProductValue::TransportShape(TransportShapeFact::Layout(
        joined_transport_layout(world, ty, &demand, position, layouts),
    )))
}

fn joined_transport_layout(
    world: &mut World,
    ty: Ty,
    demand: &RuntimeDemand,
    position: &TransportPosition,
    layouts: &[TransportLayout],
) -> TransportLayout {
    if let [first, rest @ ..] = layouts
        && rest.iter().all(|layout| layout == first)
    {
        return *first;
    }
    let mut facts = TransportFactsBuilder::default();
    let generic = generic_layout_from_demand(world, ty, demand, &mut facts, Some(position.clone()));
    if layouts.is_empty() {
        return generic;
    }
    let structural = joined_tuple_structural(world, ty, demand, position, layouts).unwrap_or(generic.structural);
    let carrier = layouts.iter().any(|layout| layout.carrier.is_value_ref()) || generic.carrier.is_value_ref();
    TransportLayout {
        structural,
        carrier: if carrier {
            TransportCarrier::ValueRef(value_lane(world, ty))
        } else {
            TransportCarrier::Absent
        },
    }
}

fn joined_tuple_structural(
    world: &mut World,
    ty: Ty,
    demand: &RuntimeDemand,
    position: &TransportPosition,
    layouts: &[TransportLayout],
) -> Option<ShapeId> {
    let field_tys = exact_tuple_field_tys(world, ty)?;
    let arity = field_tys.len();
    let alternatives = layouts
        .iter()
        .map(|layout| match world.shape(layout.structural) {
            ShapeDescr::Tuple(fields) if fields.len() == arity => Some(fields.to_vec()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let field_demands = match &demand.shape {
        ShapeDemand::TupleFields(fields) if fields.len() == arity => fields.clone(),
        ShapeDemand::Whole => vec![RuntimeDemand::whole(); arity],
        ShapeDemand::Ignore | ShapeDemand::TupleFields(_) => return None,
    };
    let fields = field_tys
        .into_iter()
        .zip(field_demands)
        .enumerate()
        .map(|(index, (field_ty, field_demand))| {
            let layouts = alternatives.iter().map(|fields| fields[index]).collect::<Vec<_>>();
            joined_transport_layout(world, field_ty, &field_demand, position, &layouts)
        })
        .collect::<Vec<_>>();
    Some(world.intern_shape(ShapeDescr::Tuple(fields.into_boxed_slice())))
}

fn produce_generic_transport_layout(
    world: &mut World,
    facts: &ExecutableFacts,
    ty: Ty,
    demand: RuntimeDemand,
    position: &TransportPosition,
) -> PullOutcome {
    produce_joined_transport_layout(world, facts, ty, demand, position, &[])
}

fn executable_key_for_transport_position(root: RootId, position: &TransportPosition) -> ExecutableKey {
    let symbol = position.executable();
    ExecutableKey {
        activation: ActivationKey {
            root,
            function: symbol.activation.function,
            arrow: symbol.activation.arrow,
        },
        need: symbol.need,
    }
}

fn executable_symbol(executable: &ExecutableKey, types: &Types) -> ExecutableSymbol {
    ExecutableSymbol {
        activation: ActivationSymbol {
            function: executable.activation.function,
            arrow: executable.activation.arrow,
            input: executable.activation.inputs(types).into_boxed_slice(),
        },
        need: executable.need,
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

fn surface_shapes(
    world: &mut World,
    surfaces: &BTreeSet<CallableSurface>,
    facts: &mut TransportFactsBuilder,
) -> Vec<Box<[ShapeId]>> {
    surface_shapes_from_layouts(&surface_layouts(world, surfaces, facts))
}

fn surface_shapes_from_layouts(layouts: &[Box<[TransportLayout]>]) -> Vec<Box<[ShapeId]>> {
    layouts
        .iter()
        .map(|layouts| layouts.iter().map(|layout| layout.structural).collect())
        .collect()
}

fn surface_layouts(
    world: &mut World,
    surfaces: &BTreeSet<CallableSurface>,
    facts: &mut TransportFactsBuilder,
) -> Vec<Box<[TransportLayout]>> {
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
                    generic_layout_from_demand(world, ty, &demand, facts, None)
                })
                .collect::<Vec<_>>()
                .into_boxed_slice()
        })
        .collect()
}

fn callable_direct_edges(
    world: &mut World,
    edges: &[super::super::semantic::CallableFlowEdge],
    facts: &mut TransportFactsBuilder,
) -> Vec<CallableDirectEdge> {
    edges
        .iter()
        .map(|edge| CallableDirectEdge {
            surface_inputs: edge.surface.inputs.clone().into_boxed_slice(),
            surface_arg_shapes: surface_shape(world, &edge.surface, facts),
            resolution: executable_symbol(&edge.resolution, world.types()),
            capture_semantic_inputs: edge.capture_semantic_inputs.clone(),
            surface_semantic_inputs: edge.surface_semantic_inputs.clone(),
        })
        .collect()
}

fn surface_shape(world: &mut World, surface: &CallableSurface, facts: &mut TransportFactsBuilder) -> Box<[ShapeId]> {
    surface
        .inputs
        .iter()
        .copied()
        .map(|ty| {
            let demand = boundary_runtime_demand(world, ty);
            generic_shape_from_demand(world, ty, &demand, facts, None)
        })
        .collect::<Vec<_>>()
        .into_boxed_slice()
}

fn generic_shape_from_demand(
    world: &mut World,
    ty: Ty,
    demand: &RuntimeDemand,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
    generic_layout_from_demand(world, ty, demand, facts, publication).structural
}

fn generic_layout_from_demand(
    world: &mut World,
    ty: Ty,
    demand: &RuntimeDemand,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> TransportLayout {
    if demand.is_ignore() || world.types().is_empty(&ty) {
        return TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing));
    }
    if demand.is_callable() {
        let structural = generic_callable_shape(world, ty, &demand.callable, facts, publication);
        return TransportLayout {
            structural,
            carrier: if demand.callable.is_first_class() {
                TransportCarrier::ValueRef(value_lane(world, ty))
            } else {
                TransportCarrier::Absent
            },
        };
    }
    match &demand.shape {
        ShapeDemand::Ignore => TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing)),
        ShapeDemand::Whole => {
            let Some(fields) = exact_tuple_field_tys(world, ty) else {
                return TransportLayout::structural(value_lane_shape(world, ty));
            };
            let items = fields
                .into_iter()
                .map(|field_ty| generic_layout_from_demand(world, field_ty, &RuntimeDemand::whole(), facts, None))
                .collect::<Vec<_>>();
            TransportLayout::structural(world.intern_shape(ShapeDescr::Tuple(items.into_boxed_slice())))
        }
        ShapeDemand::TupleFields(fields) => {
            if !has_exact_tuple_arity(world, ty, fields.len()) {
                return TransportLayout::structural(value_lane_shape(world, ty));
            }
            let items = tuple_field_tys(world, ty, fields.len())
                .into_iter()
                .zip(fields.iter())
                .map(|(field_ty, field_demand)| generic_layout_from_demand(world, field_ty, field_demand, facts, None))
                .collect::<Vec<_>>();
            TransportLayout::structural(world.intern_shape(ShapeDescr::Tuple(items.into_boxed_slice())))
        }
    }
}

fn has_exact_tuple_arity(world: &World, ty: Ty, arity: usize) -> bool {
    let predicate = world.types().runtime_type_predicate(&ty);
    predicate.tuples.arities().finite_elems().is_some_and(|mut arities| {
        arities.next() == Some(arity)
            && arities.next().is_none()
            && predicate.ints.is_none()
            && predicate.floats.is_none()
            && predicate.atoms.is_none()
            && predicate.lists.shapes().is_none()
            && predicate.named_structs.is_none()
            && !predicate.allow_other_structs
            && !predicate.maps
            && !predicate.binaries
            && predicate.callables.is_none()
            && !predicate.resources
    })
}

fn generic_callable_shape(
    world: &mut World,
    ty: Ty,
    demand: &CallableDemand,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
    generic_callable_shape_with_resolutions(world, ty, demand, facts, publication)
}

fn generic_callable_shape_with_resolutions(
    world: &mut World,
    _ty: Ty,
    _demand: &CallableDemand,
    _facts: &mut TransportFactsBuilder,
    _publication: Option<TransportPosition>,
) -> ShapeId {
    let callable = world.intern_callable(CallableDescr {
        function: None,
        // A generic callable names no function, so it has no arity of its own;
        // it is never minted into a closure value.
        arity: 0,
        capture_tys: Box::default(),
        capture_layouts: Box::default(),
    });
    world.intern_shape(ShapeDescr::Callable(callable))
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
    types: &Types,
) -> Vec<Vec<ExecutableSymbol>> {
    surfaces
        .iter()
        .map(|surface| {
            flow.first_class_edges
                .iter()
                .filter(|edge| &edge.surface == surface)
                .map(|edge| executable_symbol(&edge.resolution, types))
                .collect::<Vec<_>>()
        })
        .collect()
}

fn exact_tuple_field_tys(world: &mut World, ty: Ty) -> Option<Vec<Ty>> {
    let predicate = world.types().runtime_type_predicate(&ty);
    if predicate.tuples.arities().cofinite || predicate.tuples.arities().values.len() != 1 {
        return None;
    }
    let arity = *predicate.tuples.arities().values.iter().next()?;
    has_exact_tuple_arity(world, ty, arity).then(|| tuple_field_tys(world, ty, arity))
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
        let function = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "join", 0);
        let arrow = world
            .types_mut()
            .fn_ref_lit(crate::types::ClosureTarget(function.as_u32()), 0);
        let position = TransportPosition::Value {
            executable: ExecutableSymbol {
                activation: ActivationSymbol {
                    function,
                    arrow,
                    input: Box::default(),
                },
                need: ExecutableNeed::Value,
            },
            value: ValueId::from_u32(0),
        };
        let joined = joined_transport_layout(
            &mut world,
            tuple_ty,
            &RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole()]),
            &position,
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
        let mut facts = TransportFactsBuilder::default();
        let layout = generic_layout_from_demand(&mut world, tuple_ty, &demand, &mut facts, None);

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
        let mut facts = TransportFactsBuilder::default();

        let layout = generic_layout_from_demand(&mut world, tuple_ty, &RuntimeDemand::whole(), &mut facts, None);

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
    fn equal_layout_join_returns_without_minting_a_generic_alternative() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let exact = TransportLayout::structural(nothing);
        let function = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "join", 0);
        let arrow = world
            .types_mut()
            .fn_ref_lit(crate::types::ClosureTarget(function.as_u32()), 0);
        let position = TransportPosition::Value {
            executable: ExecutableSymbol {
                activation: ActivationSymbol {
                    function,
                    arrow,
                    input: Box::default(),
                },
                need: ExecutableNeed::Value,
            },
            value: ValueId::from_u32(0),
        };
        let before = (world.shape_count(), world.lane_count());

        let joined = joined_transport_layout(&mut world, int, &RuntimeDemand::whole(), &position, &[exact, exact]);

        assert_eq!(joined, exact);
        assert_eq!(
            (world.shape_count(), world.lane_count()),
            before,
            "an exact concordant join must not construct an unused generic layout",
        );
    }
}
