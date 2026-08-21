use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::super::body::{CallSiteId, ControlEntryId, LoweredBody, ValueId, callsite_call_args, callsite_input_modes};
use super::super::drive::FactKey;
use super::super::facts::FactUse;
use super::super::identity::{ActivationKey, ExecutableKey, ExecutableNeed, RootId};
use super::super::pull::{
    InputSlot, ProductKey, ProductReadContext, ProductValue, PullOutcome, PullWait, TransportCarrier, TransportLayout,
    TransportShapeFact,
};
use super::super::semantic::{
    CallableDemand, CallableFlowFact, CallableSurface, ExecutableRuntimeDemand, RuntimeDemand, SelectedCallee,
    ShapeDemand,
};
use super::super::transport::{
    ActivationSymbol, BoundaryDescr, BoundaryFacts, BoundaryId, CallableConstructionCapture, CallableConstructionFact,
    CallableConstructionMember, CallableConstructionOwner, CallableDescr, CallableDirectEdge, CallableFacts,
    CallableId, ExecutableSymbol, LaneId, ShapeDescr, ShapeId, TransportClass, TransportPosition,
};
use super::super::types::{Ty, Types};
use super::super::world::World;
use super::runtime_demand::{ExecutableFacts, LocalCallableProducer, TransportOrigin as TransportSource};

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

    fn record_layout_publication(&mut self, world: &World, shape: ShapeId, publication: &TransportPosition) {
        match world.shape(shape) {
            ShapeDescr::Callable(callable) => {
                let boundaries = self
                    .callables
                    .get(callable)
                    .map(|facts| facts.boundary_ids.clone())
                    .unwrap_or_default();
                for boundary in boundaries {
                    self.record_boundary(boundary, publication.clone());
                }
            }
            ShapeDescr::Tuple(fields) => {
                for field in fields.clone() {
                    self.record_layout_publication(world, field, publication);
                }
            }
            ShapeDescr::Nothing | ShapeDescr::Lane(_) => {}
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

    fn finish(self) -> (HashMap<CallableId, CallableFacts>, HashMap<BoundaryId, BoundaryFacts>) {
        let callables = self
            .callables
            .into_iter()
            .map(|(id, mut draft)| {
                draft.resolutions.sort_by_cached_key(executable_symbol_sort_key);
                draft
                    .direct_surfaces
                    .sort_by_cached_key(|surface| surface.iter().map(|shape| shape.as_u32()).collect::<Vec<_>>());
                draft.direct_edges.sort_by_cached_key(callable_direct_edge_sort_key);
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
                    .sort_by_cached_key(super::artifact::transport_position_global_sort_key);
                draft.resolutions.sort_by_cached_key(executable_symbol_sort_key);
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
    context: &mut ProductReadContext<'_>,
    position: &TransportPosition,
) -> PullOutcome {
    let executable = executable_key_for_transport_position(context.session().root(), position);
    if let Some(outcome) = produce_named_transport_position(world, context, &executable, position) {
        return outcome;
    }
    let layout = TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing));
    PullOutcome::Produced(ProductValue::TransportShape(TransportShapeFact::Layout(layout)))
}

pub(crate) fn produce_callable_construction_product(
    world: &mut World,
    context: &mut ProductReadContext<'_>,
    position: &TransportPosition,
) -> PullOutcome {
    let executable = executable_key_for_transport_position(context.session().root(), position);
    let facts = match context.read_executable_facts(&executable) {
        Some(facts) => facts,
        None => return PullOutcome::wait_on_product(ProductKey::ExecutableFacts(executable)),
    };
    let runtime = match context.read_runtime_demand(&executable) {
        Some(runtime) => runtime,
        None => return PullOutcome::wait_on_product(ProductKey::RuntimeDemand(executable)),
    };
    let TransportPosition::Value { value, .. } = position else {
        return produce_generic_callable_owner(world, context, &executable, facts.as_ref(), &runtime, position);
    };
    let Some(TransportSource::CallableValue(producer)) = facts.value_origin(*value) else {
        return produce_generic_callable_owner(world, context, &executable, facts.as_ref(), &runtime, position);
    };
    let Some(flow) = runtime.callable_flows.get(value) else {
        return produce_generic_callable_owner(world, context, &executable, facts.as_ref(), &runtime, position);
    };
    let demand = runtime.value_demands.get(value).cloned().unwrap_or_default();
    match produce_local_callable_construction(world, context, &executable, facts.as_ref(), producer, flow, demand) {
        Ok(answer) => PullOutcome::Produced(ProductValue::CallableConstruction(Box::new(answer))),
        Err(waits) => PullOutcome::Waiting(waits),
    }
}

fn produce_generic_callable_owner(
    world: &mut World,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
    facts: &super::runtime_demand::ExecutableFacts,
    runtime: &ExecutableRuntimeDemand,
    position: &TransportPosition,
) -> PullOutcome {
    let shape_key = ProductKey::TransportShape(position.clone());
    let layout = match context.read_product(shape_key.clone()) {
        Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => *layout,
        Some(value) => panic!("transport shape produced unexpected value {value:?}"),
        None => return PullOutcome::wait_on_product(shape_key),
    };
    if matches!(world.shape(layout.structural), ShapeDescr::Nothing) {
        return PullOutcome::Produced(ProductValue::CallableConstruction(Box::new(
            CallableConstructionOwner {
                layout,
                construction: None,
                callable_facts: HashMap::new(),
                boundary_facts: HashMap::new(),
            },
        )));
    }
    let (ty, demand) = match position {
        TransportPosition::ExecutableInput { semantic_index, .. } => {
            let fact = FactUse::settled(FactKey::ActivationInputs(executable.activation.clone()));
            if !context.read_fact(world, fact.clone()) {
                return PullOutcome::wait_on_fact(fact);
            }
            (
                world
                    .activation_inputs_joined(&executable.activation)
                    .unwrap_or_else(|| executable.activation.inputs(world.types()))
                    .get(*semantic_index)
                    .copied()
                    .unwrap_or_else(|| world.types_mut().any()),
                runtime.input_demands.get(*semantic_index).cloned().unwrap_or_default(),
            )
        }
        TransportPosition::ExecutableReturn { .. } | TransportPosition::ReturnPayload { .. } => {
            let fact = FactUse::settled(FactKey::ReturnType(executable.activation.clone()));
            if !context.read_fact(world, fact.clone()) {
                return PullOutcome::wait_on_fact(fact);
            }
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
            let capture = match facts.body() {
                LoweredBody::Clauses { entries, .. } => entries
                    .get(entry.as_u32() as usize)
                    .and_then(|entry| entry.captures.get(*capture_index)),
                LoweredBody::Extern { .. } => None,
            };
            (
                capture
                    .and_then(|capture| facts.analysis().value_types.get(capture).copied())
                    .unwrap_or_else(|| world.types_mut().any()),
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
    };
    let mut source_positions = Vec::new();
    if demand_contains_callable(&demand) {
        match position {
            TransportPosition::ExecutableInput { semantic_index, .. } => {
                let key = ProductKey::IncomingInputSlot(InputSlot {
                    executable: executable.clone(),
                    semantic_index: *semantic_index,
                });
                match context.read_product(key.clone()) {
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
        if context.pending_dependency_reaches(&key, &current) {
            let _ = context.read_product(key);
            let members = context.pending_callable_construction_group(&current);
            let mut settled = TransportFactsBuilder::default();
            settled.merge(&builder);
            for owner in context.recursive_group_callable_owners(&members) {
                settled.merge_owner(&owner);
            }
            let mut settled = project_generic_owner_facts(world, &settled, layout.structural, ty, &demand, position);
            for member in &members {
                let ProductKey::CallableConstruction(member) = member else {
                    unreachable!()
                };
                let member_layout = context
                    .callable_group_layout(&ProductKey::CallableConstruction(member.clone()))
                    .expect("callable owner group member must have a settled transport shape");
                settled.record_layout_publication(world, member_layout.structural, member);
            }
            let (callable_facts, boundary_facts) = settled.finish();
            let values = members
                .iter()
                .map(|member| {
                    let layout = context
                        .callable_group_layout(member)
                        .expect("callable owner group member must have a settled transport shape");
                    ProductValue::CallableConstruction(Box::new(CallableConstructionOwner {
                        layout,
                        construction: None,
                        callable_facts: callable_facts.clone(),
                        boundary_facts: boundary_facts.clone(),
                    }))
                })
                .collect();
            if !context.finish_callable_construction_group(&current, &members, values) {
                return PullOutcome::wait_on_product(current);
            }
            return context
                .session()
                .memo()
                .get(&current)
                .cloned()
                .map(PullOutcome::Produced)
                .expect("settled callable owner group must contain the requested member");
        }
        match context.read_product(key.clone()) {
            Some(ProductValue::CallableConstruction(owner)) => builder.merge_owner(owner),
            Some(value) => panic!("callable construction produced unexpected value {value:?}"),
            None => return PullOutcome::wait_on_product(key),
        }
    }
    let builder = project_generic_owner_facts(world, &builder, layout.structural, ty, &demand, position);
    let (callable_facts, boundary_facts) = builder.finish();
    PullOutcome::Produced(ProductValue::CallableConstruction(Box::new(
        CallableConstructionOwner {
            layout,
            construction: None,
            callable_facts,
            boundary_facts,
        },
    )))
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
                project_generic_owner_node(world, source, projected, field, field_ty, field_demand, publication);
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
            let surface_shapes = surface_shapes(world, surfaces, facts);
            let boundary_ids = if demand.callable.is_first_class() && !surfaces.is_empty() {
                publish_boundaries_for_callable(
                    world,
                    facts,
                    callable,
                    surfaces,
                    &surface_shapes,
                    &[],
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
                record_generic_owner_facts(world, facts, field, field_ty, field_demand, publication);
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
    Alternatives(Vec<Self>),
    Tuple(Vec<Self>),
    TupleField {
        tuple: Box<Self>,
        index: usize,
    },
}

enum RecipeLayout {
    Exact(TransportLayout),
    Recursive(Vec<TransportLayout>),
    Waiting(ProductKey),
}

fn evaluate_transport_recipe(
    world: &mut World,
    context: &mut ProductReadContext<'_>,
    current: &ProductKey,
    recipe: &TransportRecipe,
    ty: Ty,
    demand: &RuntimeDemand,
    position: &TransportPosition,
) -> RecipeLayout {
    match recipe {
        TransportRecipe::Terminal => exact_direct_callable_layout(world, context, current, ty, demand, position)
            .unwrap_or_else(|| RecipeLayout::Exact(joined_transport_layout(world, ty, demand, position, &[]))),
        TransportRecipe::PublicCallableReturn => {
            let mut layout = joined_transport_layout(world, ty, demand, position, &[]);
            if !matches!(world.shape(layout.structural), ShapeDescr::Nothing) {
                layout.carrier = TransportCarrier::ValueRef;
            }
            RecipeLayout::Exact(layout)
        }
        TransportRecipe::ClosureCallReturn { callee, grounded } => {
            // One authority: `materialize_closure_call_edge` goes direct only
            // when the callee value's carrier is exact; the claim grounds on
            // exactly that condition.
            let callee_key = ProductKey::TransportShape(callee.clone());
            let callee_layout = match context.read_product(callee_key.clone()) {
                Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => *layout,
                Some(value) => panic!("closure callee shape produced unexpected value {value:?}"),
                None => return RecipeLayout::Waiting(callee_key),
            };
            match grounded {
                Some(grounded) if !matches!(callee_layout.carrier, TransportCarrier::ValueRef) => {
                    evaluate_transport_recipe(world, context, current, grounded, ty, demand, position)
                }
                _ => evaluate_transport_recipe(
                    world,
                    context,
                    current,
                    &TransportRecipe::PublicCallableReturn,
                    ty,
                    demand,
                    position,
                ),
            }
        }
        TransportRecipe::Alias(child) => {
            let key = ProductKey::TransportShape(child.clone());
            if key == *current || context.pending_dependency_reaches(&key, current) {
                let _ = context.read_product(key);
                return RecipeLayout::Recursive(Vec::new());
            }
            match context.read_product(key.clone()) {
                Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => RecipeLayout::Exact(*layout),
                Some(value) => panic!("transport shape produced unexpected value {value:?}"),
                None => RecipeLayout::Waiting(key),
            }
        }
        TransportRecipe::Alternatives(recipes) => {
            let mut layouts = Vec::new();
            let mut recursive = false;
            for recipe in recipes {
                match evaluate_transport_recipe(world, context, current, recipe, ty, demand, position) {
                    RecipeLayout::Exact(layout) => layouts.push(layout),
                    RecipeLayout::Recursive(anchors) => {
                        recursive = true;
                        layouts.extend(anchors);
                    }
                    waiting @ RecipeLayout::Waiting(_) => return waiting,
                }
            }
            if recursive {
                RecipeLayout::Recursive(layouts)
            } else {
                RecipeLayout::Exact(joined_transport_layout(world, ty, demand, position, &layouts))
            }
        }
        TransportRecipe::Tuple(fields) => {
            let mut layouts = Vec::with_capacity(fields.len());
            for field in fields {
                match evaluate_transport_recipe(world, context, current, field, ty, demand, position) {
                    RecipeLayout::Exact(layout) => layouts.push(layout),
                    RecipeLayout::Recursive(anchors) => return RecipeLayout::Recursive(anchors),
                    waiting @ RecipeLayout::Waiting(_) => return waiting,
                }
            }
            let carrier = layouts
                .iter()
                .any(|layout| layout.carrier == TransportCarrier::ValueRef)
                || demand.callable.is_first_class();
            RecipeLayout::Exact(TransportLayout {
                structural: world.intern_shape(ShapeDescr::Tuple(
                    layouts
                        .iter()
                        .map(|layout| layout.structural)
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                )),
                carrier: if carrier {
                    TransportCarrier::ValueRef
                } else {
                    TransportCarrier::Absent
                },
            })
        }
        TransportRecipe::TupleField { tuple, index } => {
            match evaluate_transport_recipe(world, context, current, tuple, ty, demand, position) {
                RecipeLayout::Exact(layout) => match world.shape(layout.structural) {
                    ShapeDescr::Tuple(fields) => fields.get(*index).copied().map_or_else(
                        || RecipeLayout::Exact(joined_transport_layout(world, ty, demand, position, &[])),
                        |structural| {
                            RecipeLayout::Exact(TransportLayout {
                                structural,
                                carrier: layout.carrier,
                            })
                        },
                    ),
                    ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => {
                        RecipeLayout::Exact(joined_transport_layout(world, ty, demand, position, &[]))
                    }
                },
                other => other,
            }
        }
    }
}

fn exact_direct_callable_layout(
    world: &mut World,
    context: &mut ProductReadContext<'_>,
    current: &ProductKey,
    ty: Ty,
    demand: &RuntimeDemand,
    position: &TransportPosition,
) -> Option<RecipeLayout> {
    let targets = demand.callable.targets.clone();
    if demand.callable.is_first_class() || targets.len() != 1 {
        return None;
    }
    let target = targets.iter().next().expect("singleton callable target");
    let capture_count = target
        .activation_inputs
        .len()
        .checked_sub(target.surface.inputs.len())?;
    let executable = ExecutableKey {
        activation: target.activation.clone(),
        need: target.need,
    };
    let executable = executable_symbol(&executable, world.types());
    let mut capture_layouts = Vec::with_capacity(capture_count);
    let mut recursive = false;
    for semantic_index in 0..capture_count {
        let key = ProductKey::TransportShape(TransportPosition::ExecutableInput {
            executable: executable.clone(),
            semantic_index,
        });
        if key == *current || context.pending_dependency_reaches(&key, current) {
            let _ = context.read_product(key);
            recursive = true;
            continue;
        }
        match context.read_product(key.clone()) {
            Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => capture_layouts.push(*layout),
            Some(value) => panic!("transport shape produced unexpected value {value:?}"),
            None => return Some(RecipeLayout::Waiting(key)),
        }
    }
    if recursive {
        let mut layout = joined_transport_layout(world, ty, demand, position, &[]);
        layout.carrier = TransportCarrier::ValueRef;
        return Some(RecipeLayout::Recursive(vec![layout]));
    }
    let capture_tys = &target.activation_inputs[..capture_count];
    let capture_shapes = capture_layouts
        .iter()
        .map(|layout| layout.structural)
        .collect::<Vec<_>>();
    let capture_lanes = capture_layouts
        .iter()
        .zip(capture_tys.iter().copied())
        .flat_map(|(layout, ty)| capture_lanes_for_layout(world, *layout, ty))
        .collect::<Vec<_>>();
    let callable = world.intern_callable(CallableDescr {
        function: Some(target.activation.function),
        capture_tys: capture_tys.to_vec().into_boxed_slice(),
        capture_shapes: capture_shapes.into_boxed_slice(),
        capture_lanes: capture_lanes.into_boxed_slice(),
    });
    Some(RecipeLayout::Exact(TransportLayout {
        structural: world.intern_shape(ShapeDescr::Callable(callable)),
        carrier: TransportCarrier::Absent,
    }))
}

/// The one callable row a closure callsite could ground its return against:
/// a settled summary naming exactly one compiler-owned target. Whether the
/// grounding APPLIES is decided at recipe evaluation from the callee value's
/// own transport carrier — the same fact `materialize_closure_call_edge` uses
/// to choose a direct edge — so claim and call share one authority.
fn singleton_closure_call_target(
    facts: &super::runtime_demand::ExecutableFacts,
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
    facts: &super::runtime_demand::ExecutableFacts,
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

fn produce_local_callable_construction(
    world: &mut World,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
    facts: &super::runtime_demand::ExecutableFacts,
    producer: &LocalCallableProducer,
    flow: &CallableFlowFact,
    demand: RuntimeDemand,
) -> Result<CallableConstructionOwner, Vec<PullWait>> {
    assert_eq!(flow.function, producer.function);
    assert_eq!(flow.captures, producer.captures);
    let callable_ty = facts
        .analysis()
        .value_types
        .get(&producer.value)
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
        let Some(value) = context.read_product(key.clone()) else {
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
    for capture in producer.captures.iter().copied() {
        let key = ProductKey::TransportShape(TransportPosition::Value {
            executable: symbol.clone(),
            value: capture,
        });
        match context.read_product(key.clone()) {
            Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => capture_layouts.push(*layout),
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
    let capture_shapes = capture_layouts
        .iter()
        .map(|layout| layout.structural)
        .collect::<Vec<_>>();
    let capture_lanes = capture_layouts
        .iter()
        .zip(capture_tys.iter().copied())
        .zip(capture_demands.iter())
        .flat_map(|((layout, ty), demand)| capture_lanes_for_callable_descriptor(world, *layout, ty, demand))
        .collect::<Vec<_>>();
    let callable = world.intern_callable(CallableDescr {
        function: Some(producer.function),
        capture_tys: capture_tys.into_boxed_slice(),
        capture_shapes: capture_shapes.into_boxed_slice(),
        capture_lanes: capture_lanes.clone().into_boxed_slice(),
    });
    let boundary_surfaces = flow.first_class_surfaces.clone();
    let boundary_shapes = surface_shapes(world, &boundary_surfaces, &mut builder);
    let boundary_resolutions = boundary_resolution_symbols_for_flow_surfaces(flow, &boundary_surfaces, world.types());
    let producer_position = TransportPosition::Value {
        executable: symbol,
        value: producer.value,
    };
    let boundaries_by_surface = publish_boundaries_for_callable(
        world,
        &mut builder,
        callable,
        &boundary_surfaces,
        &boundary_shapes,
        &capture_lanes,
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
            members: flow
                .first_class_edges
                .iter()
                .zip(construction_edges.iter())
                .map(|(source, edge)| CallableConstructionMember {
                    boundary: *boundaries_by_surface
                        .get(&source.surface)
                        .expect("every construction edge surface should have a published boundary"),
                    surface_inputs: edge.surface_inputs.clone(),
                    surface_arg_shapes: edge.surface_arg_shapes.clone(),
                    resolution: edge.resolution.clone(),
                    capture_semantic_inputs: edge.capture_semantic_inputs.clone(),
                    surface_semantic_inputs: edge.surface_semantic_inputs.clone(),
                })
                .collect(),
            selection: super::super::callsite_dispatch::dispatch_from_callable_flow_edges(
                world.types_mut(),
                &flow.first_class_edges,
            )
            .expect("settled callable flow edges should produce a dispatch plan"),
        })
    };
    let (callable_facts, boundary_facts) = builder.finish();
    Ok(CallableConstructionOwner {
        layout: TransportLayout {
            structural: world.intern_shape(ShapeDescr::Callable(callable)),
            carrier: if demand.callable.is_first_class() {
                TransportCarrier::ValueRef
            } else {
                TransportCarrier::Absent
            },
        },
        construction,
        callable_facts,
        boundary_facts,
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

fn resume_payload_ty(facts: &ExecutableFacts, entry: ControlEntryId) -> Ty {
    let value = resume_payload_value(facts, entry);
    facts
        .analysis()
        .value_types
        .get(&value)
        .copied()
        .expect("a resume payload value must have an analyzed type")
}

fn produce_named_transport_position(
    world: &mut World,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
    position: &TransportPosition,
) -> Option<PullOutcome> {
    let facts = match context.read_executable_facts(executable) {
        Some(facts) => facts,
        None => {
            return Some(PullOutcome::wait_on_product(ProductKey::ExecutableFacts(
                executable.clone(),
            )));
        }
    };
    let runtime = match context.read_runtime_demand(executable) {
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
            (ty, runtime.return_demand)
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
                    let construction = context.read_product(key.clone()).cloned();
                    return Some(match construction {
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
            let Some(ty) = world.activation_return(&executable.activation) else {
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
            (ty, runtime.return_demand)
        }
        TransportPosition::EntryCapture {
            entry, capture_index, ..
        } => {
            let capture = match facts.body() {
                LoweredBody::Clauses { entries, .. } => entries
                    .get(entry.as_u32() as usize)
                    .and_then(|entry| entry.captures.get(*capture_index))
                    .copied(),
                LoweredBody::Extern { .. } => None,
            }?;
            recipe = TransportRecipe::Alias(TransportPosition::Value {
                executable: symbol,
                value: capture,
            });
            (
                facts
                    .analysis()
                    .value_types
                    .get(&capture)
                    .copied()
                    .unwrap_or_else(|| world.types_mut().any()),
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
                resume_payload_ty(&facts, *entry),
                runtime.value_demands.get(&value).cloned().unwrap_or_default(),
            )
        }
    };

    let current = ProductKey::TransportShape(position.clone());
    match evaluate_transport_recipe(world, context, &current, &recipe, ty, &demand, position) {
        RecipeLayout::Exact(layout) => Some(PullOutcome::Produced(ProductValue::TransportShape(
            TransportShapeFact::Layout(layout),
        ))),
        RecipeLayout::Waiting(key) => Some(PullOutcome::wait_on_product(key)),
        RecipeLayout::Recursive(mut anchors) => {
            let members = context.pending_transport_shape_group(&current);
            anchors.extend(context.recursive_group_transport_layouts(&members));
            let layout = joined_transport_layout(world, ty, &demand, position, &anchors);
            let value = ProductValue::TransportShape(TransportShapeFact::Layout(layout));
            if !context.finish_transport_shape_group(&current, &members, value.clone()) {
                return Some(PullOutcome::wait_on_product(current));
            }
            Some(PullOutcome::Produced(value))
        }
    }
}

fn bottom_transport_shape(world: &mut World) -> PullOutcome {
    let layout = TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing));
    PullOutcome::Produced(ProductValue::TransportShape(TransportShapeFact::Layout(layout)))
}

fn append_origin_children(
    world: &World,
    executable: &ExecutableKey,
    symbol: &ExecutableSymbol,
    facts: &super::runtime_demand::ExecutableFacts,
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
    _facts: &super::runtime_demand::ExecutableFacts,
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
    let carrier = layouts
        .iter()
        .any(|layout| layout.carrier == TransportCarrier::ValueRef)
        || demand.callable.is_first_class();
    let structural = match layouts {
        [first, rest @ ..] if rest.iter().all(|layout| layout.structural == first.structural) => first.structural,
        _ => {
            let mut facts = TransportFactsBuilder::default();
            generic_shape_from_demand(world, ty, demand, &mut facts, Some(position.clone()))
        }
    };
    TransportLayout {
        structural,
        carrier: if carrier {
            TransportCarrier::ValueRef
        } else {
            TransportCarrier::Absent
        },
    }
}

fn produce_generic_transport_layout(
    world: &mut World,
    facts: &super::runtime_demand::ExecutableFacts,
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

fn lanes_for_codegen_seam_shape(world: &World, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
    match world.shape(shape) {
        ShapeDescr::Nothing => Vec::new(),
        ShapeDescr::Lane(lane) => vec![(shape, *lane)],
        ShapeDescr::Callable(callable) => world
            .callable(*callable)
            .capture_lanes
            .iter()
            .copied()
            .map(|lane| (shape, lane))
            .collect(),
        ShapeDescr::Tuple(items) => items
            .iter()
            .copied()
            .flat_map(|item| lanes_for_codegen_seam_shape(world, item))
            .collect(),
    }
}

type ExecutableSymbolSortKey = (u32, Ty, Vec<Ty>, u8, usize);
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

fn executable_symbol_sort_key(symbol: &ExecutableSymbol) -> ExecutableSymbolSortKey {
    let need = match symbol.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        symbol.activation.function.as_u32(),
        symbol.activation.arrow,
        symbol.activation.input.to_vec(),
        need.0,
        need.1,
    )
}

fn callable_direct_edge_sort_key(edge: &CallableDirectEdge) -> (Vec<Ty>, ExecutableSymbolSortKey) {
    (
        edge.surface_inputs.to_vec(),
        executable_symbol_sort_key(&edge.resolution),
    )
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
    let mut rendered = surfaces
        .iter()
        .map(|surface| {
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
        })
        .collect::<Vec<_>>();
    rendered.sort_by_cached_key(|surface| surface.iter().map(|shape| shape.as_u32()).collect::<Vec<_>>());
    rendered
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
    if demand.is_ignore() || world.types().is_empty(&ty) {
        return world.intern_shape(ShapeDescr::Nothing);
    }
    if demand.is_callable() {
        return generic_callable_shape(world, ty, &demand.callable, facts, publication);
    }
    match &demand.shape {
        ShapeDemand::Ignore => world.intern_shape(ShapeDescr::Nothing),
        ShapeDemand::Whole => value_lane_shape(world, ty),
        ShapeDemand::TupleFields(fields) => {
            if !has_exact_tuple_arity(world, ty, fields.len()) {
                return value_lane_shape(world, ty);
            }
            let items = tuple_field_tys(world, ty, fields.len())
                .into_iter()
                .zip(fields.iter())
                .map(|(field_ty, field_demand)| generic_shape_from_demand(world, field_ty, field_demand, facts, None))
                .collect::<Vec<_>>();
            world.intern_shape(ShapeDescr::Tuple(items.into_boxed_slice()))
        }
    }
}

fn has_exact_tuple_arity(world: &World, ty: Ty, arity: usize) -> bool {
    let predicate = world.types().runtime_type_predicate(&ty);
    predicate.tuple_arities.finite_elems().is_some_and(|mut arities| {
        arities.next() == Some(arity)
            && arities.next().is_none()
            && predicate.ints.is_none()
            && predicate.floats.is_none()
            && predicate.atoms.is_none()
            && predicate.lists.is_none()
            && predicate.named_structs.is_none()
            && !predicate.allow_other_structs
            && !predicate.maps
            && !predicate.binaries
            && !predicate.closures
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
        capture_tys: Box::default(),
        capture_shapes: Box::default(),
        capture_lanes: Box::default(),
    });
    world.intern_shape(ShapeDescr::Callable(callable))
}

fn publish_boundaries_for_callable(
    world: &mut World,
    facts: &mut TransportFactsBuilder,
    callable: CallableId,
    surfaces: &BTreeSet<CallableSurface>,
    surface_shapes: &[Box<[ShapeId]>],
    capture_lanes: &[LaneId],
    published_value_ty: Ty,
    resolution_symbols: &[Vec<ExecutableSymbol>],
    publication: Option<TransportPosition>,
) -> BTreeMap<CallableSurface, BoundaryId> {
    assert_eq!(
        surfaces.len(),
        surface_shapes.len(),
        "boundary surface shapes must align with published surfaces"
    );
    assert_eq!(
        surfaces.len(),
        resolution_symbols.len(),
        "boundary resolution symbols must align with published surfaces"
    );
    let mut boundaries_by_surface = BTreeMap::new();
    for ((surface, arg_shapes), resolutions) in surfaces
        .iter()
        .zip(surface_shapes.iter())
        .zip(resolution_symbols.iter())
    {
        let published_value_lane = value_lane(world, published_value_ty);
        let arg_lanes = arg_shapes
            .iter()
            .copied()
            .zip(surface.inputs.iter().copied())
            .flat_map(|(shape, ty)| boundary_lanes_for_shape(world, shape, ty))
            .collect::<Vec<_>>();
        let boundary = world.intern_boundary(BoundaryDescr {
            callable,
            surface_arg_shapes: arg_shapes.clone(),
            published_value_lane,
            published_capture_lanes: capture_lanes.to_vec().into_boxed_slice(),
            published_arg_lanes: arg_lanes.into_boxed_slice(),
        });
        if let Some(position) = publication.clone() {
            facts.record_boundary(boundary, position);
        }
        facts.record_boundary_resolutions(boundary, resolutions.clone());
        boundaries_by_surface.insert(surface.clone(), boundary);
    }
    boundaries_by_surface
}

fn capture_lanes_for_callable_descriptor(
    world: &mut World,
    layout: TransportLayout,
    ty: Ty,
    demand: &RuntimeDemand,
) -> Vec<LaneId> {
    if layout.carrier == TransportCarrier::ValueRef || demand.callable.is_first_class() {
        return vec![value_lane(world, ty)];
    }
    capture_lanes_for_layout(world, layout, ty)
}

fn capture_lanes_for_layout(world: &mut World, layout: TransportLayout, ty: Ty) -> Vec<LaneId> {
    if layout.carrier == TransportCarrier::ValueRef {
        return vec![value_lane(world, ty)];
    }
    lanes_for_codegen_seam_shape(world, layout.structural)
        .into_iter()
        .map(|(_, lane)| lane)
        .collect()
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

fn boundary_lanes_for_shape(world: &mut World, shape: ShapeId, ty: Ty) -> Vec<LaneId> {
    match world.shape(shape).clone() {
        ShapeDescr::Nothing => Vec::new(),
        ShapeDescr::Lane(lane) => vec![lane],
        ShapeDescr::Tuple(items) => {
            let field_tys = tuple_field_tys(world, ty, items.len());
            items
                .iter()
                .copied()
                .zip(field_tys)
                .flat_map(|(item, field_ty)| boundary_lanes_for_shape(world, item, field_ty))
                .collect()
        }
        ShapeDescr::Callable(_) => {
            vec![value_lane(world, ty)]
        }
    }
}

fn exact_tuple_field_tys(world: &mut World, ty: Ty) -> Option<Vec<Ty>> {
    let predicate = world.types().runtime_type_predicate(&ty);
    if predicate.tuple_arities.cofinite || predicate.tuple_arities.values.len() != 1 {
        return None;
    }
    let arity = *predicate.tuple_arities.values.iter().next()?;
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
