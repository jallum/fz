use std::collections::{BTreeSet, HashMap, HashSet};

use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryId, LoweredBody, LoweredStep, LoweredTail, ValueId,
};
use super::super::drive::{FactKey, Job, JobEffects, settled_uses};
use super::super::identity::{ExecutableKey, ExecutableNeed, FunctionId, RootId};
use super::super::scheduler::FatalError;
use super::super::semantic::{
    ActivationAnalysis, CallSiteKey, CallableDemand, CallableMaterialization, CallableSurface, ExecutableRuntimeDemand,
    RuntimeDemand, SelectedCallee,
};
use super::super::transport::{
    ActivationSymbol, CallableDescr, ExecutableSymbol, ShapeDescr, ShapeId, TransportClass, TransportPlan,
    TransportPosition,
};
use super::super::types::Ty;
use super::super::world::World;
use super::semantic::executable_callsite_needs;

#[derive(Debug, Clone)]
struct ExecutableContext {
    analysis: ActivationAnalysis,
    return_ty: Ty,
    body: LoweredBody,
    runtime_demand: ExecutableRuntimeDemand,
    callsite_needs: HashMap<CallSiteId, ExecutableNeed>,
    callsite_args: HashMap<CallSiteId, Vec<CallArg>>,
    local_origins: HashMap<ValueId, ValueOrigin>,
    return_sources: Vec<ProducedSource>,
    resume_entries: Vec<ResumeEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ValueOrigin {
    Tuple(Box<[ValueId]>),
    Callable(LocalCallableProducer),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LocalCallableProducer {
    function: FunctionId,
    captures: Box<[ValueId]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProducedSource {
    LocalValue(ValueId),
    Callsite(CallSiteId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ResumeEntry {
    entry: ControlEntryId,
    value: ValueId,
    callsite: CallSiteId,
}

pub(super) fn derive_transport_plan(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let closed_fact = FactKey::SemanticClosed(root_id);
    if !world.fact_is_settled(&closed_fact) {
        return Ok(JobEffects::wait_on_settled(
            closed_fact,
            [Job::SealSemanticClosure(root_id)],
        ));
    }

    let closure = world.semantic_closure(root_id);
    let mut reads = vec![closed_fact];
    let mut wait_facts = HashSet::new();
    let mut contexts = HashMap::new();

    for executable in &closure.executables {
        let activation_fact = FactKey::ActivationAnalyzed(executable.activation.clone());
        if !world.fact_is_settled(&activation_fact) {
            wait_facts.insert(activation_fact);
            continue;
        }
        reads.push(activation_fact);

        let return_fact = FactKey::ReturnType(executable.activation.clone());
        if !world.fact_is_settled(&return_fact) {
            wait_facts.insert(return_fact);
            continue;
        }
        reads.push(return_fact);

        let analysis = world
            .activation_analysis(&executable.activation)
            .cloned()
            .expect("settled activation analyses should be readable");
        let return_ty = world
            .activation_return(&executable.activation)
            .unwrap_or_else(|| world.types_mut().none());
        let body = world.lowered_body(executable.activation.function);
        let runtime_demand = closure.runtime_demands.get(executable).cloned().unwrap_or_default();
        let callsite_needs = executable_callsite_needs(&body, &analysis.reachable_clauses, executable.need);
        for callsite in &analysis.callsites {
            let fact = FactKey::CallSiteSummary(CallSiteKey {
                activation: executable.activation.clone(),
                callsite: *callsite,
            });
            if !world.fact_is_settled(&fact) {
                wait_facts.insert(fact);
                continue;
            }
            reads.push(fact);
        }
        contexts.insert(
            executable.clone(),
            ExecutableContext {
                callsite_args: collect_callsite_args(&body),
                local_origins: collect_value_origins(&body),
                return_sources: collect_return_sources(&body, &analysis),
                resume_entries: collect_resume_entries(&body, &analysis),
                analysis,
                return_ty,
                body,
                runtime_demand,
                callsite_needs,
            },
        );
    }

    if !wait_facts.is_empty() {
        return Ok(JobEffects {
            reads: settled_uses(reads),
            waits: settled_uses(wait_facts),
            follow_up: vec![Job::DeriveTransportPlan(root_id)],
            ..JobEffects::default()
        });
    }

    let mut executables = closure.executables.into_iter().collect::<Vec<_>>();
    executables.sort_by_key(executable_sort_key);

    let entry = executable_symbol(&closure.entry);
    let executable_membership = executables
        .iter()
        .map(executable_symbol)
        .collect::<Vec<_>>()
        .into_boxed_slice();

    let mut return_shapes = HashMap::<ExecutableKey, ShapeId>::new();
    for executable in &executables {
        let context = contexts
            .get(executable)
            .expect("transport derivation requires one context per settled executable");
        let shape = shape_for_sources(
            world,
            &contexts,
            &return_shapes,
            executable,
            context,
            context.return_ty,
            &context.runtime_demand.return_demand,
            &context.return_sources,
        );
        return_shapes.insert(executable.clone(), shape);
    }

    let mut positions = HashMap::new();
    for executable in &executables {
        let symbol = executable_symbol(executable);
        let context = contexts
            .get(executable)
            .expect("transport derivation requires one context per settled executable");

        for (semantic_index, ty) in executable.activation.input.iter().copied().enumerate() {
            let demand = context
                .runtime_demand
                .input_demands
                .get(semantic_index)
                .cloned()
                .unwrap_or_default();
            let shape = generic_shape_from_demand(world, ty, &demand);
            positions.insert(
                TransportPosition::ExecutableInput {
                    executable: symbol.clone(),
                    semantic_index,
                },
                shape,
            );
        }

        positions.insert(
            TransportPosition::ExecutableReturn {
                executable: symbol.clone(),
            },
            *return_shapes
                .get(executable)
                .expect("return shapes should be precomputed for every executable"),
        );

        let mut values = context.analysis.value_types.iter().collect::<Vec<_>>();
        values.sort_by_key(|(value, _)| value.as_u32());
        for (&value, &ty) in values {
            let demand = context
                .runtime_demand
                .value_demands
                .get(&value)
                .cloned()
                .unwrap_or_default();
            let shape = shape_for_local_value(
                world,
                &contexts,
                &return_shapes,
                executable,
                context,
                value,
                ty,
                &demand,
            );
            positions.insert(
                TransportPosition::Value {
                    executable: symbol.clone(),
                    value,
                },
                shape,
            );
        }

        let mut call_args = context.runtime_demand.call_arg_demands.iter().collect::<Vec<_>>();
        call_args.sort_by_key(|(callsite, _)| callsite.as_u32());
        for (&callsite, demands) in call_args {
            let args = context.callsite_args.get(&callsite).cloned().unwrap_or_default();
            for (semantic_index, demand) in demands.iter().cloned().enumerate() {
                let ty = args
                    .get(semantic_index)
                    .and_then(|arg| context.analysis.value_types.get(&arg.value))
                    .copied()
                    .unwrap_or_else(|| world.types_mut().any());
                let shape = args
                    .get(semantic_index)
                    .map(|arg| {
                        shape_for_local_value(
                            world,
                            &contexts,
                            &return_shapes,
                            executable,
                            context,
                            arg.value,
                            ty,
                            &demand,
                        )
                    })
                    .unwrap_or_else(|| generic_shape_from_demand(world, ty, &demand));
                positions.insert(
                    TransportPosition::CallArg {
                        executable: symbol.clone(),
                        callsite,
                        semantic_index,
                    },
                    shape,
                );
            }
        }

        let mut entry_captures = context.runtime_demand.entry_capture_demands.iter().collect::<Vec<_>>();
        entry_captures.sort_by_key(|(entry, _)| entry.as_u32());
        for (&entry, demands) in entry_captures {
            let LoweredBody::Clauses { entries, .. } = &context.body else {
                continue;
            };
            let captures = entries
                .get(entry.as_u32() as usize)
                .map(|lowered| lowered.captures.clone())
                .unwrap_or_default();
            for (capture_index, demand) in demands.iter().cloned().enumerate() {
                let Some(&capture) = captures.get(capture_index) else {
                    continue;
                };
                let ty = context
                    .analysis
                    .value_types
                    .get(&capture)
                    .copied()
                    .unwrap_or_else(|| world.types_mut().any());
                let shape = shape_for_local_value(
                    world,
                    &contexts,
                    &return_shapes,
                    executable,
                    context,
                    capture,
                    ty,
                    &demand,
                );
                positions.insert(
                    TransportPosition::EntryCapture {
                        executable: symbol.clone(),
                        entry,
                        capture_index,
                    },
                    shape,
                );
            }
        }

        for resume in &context.resume_entries {
            let demand = resume_demand(world, &contexts, executable, context, *resume);
            let shape = resume_shape(world, &contexts, &return_shapes, executable, context, *resume, &demand);
            positions.insert(
                TransportPosition::ResumePayload {
                    executable: symbol.clone(),
                    callsite: resume.callsite,
                    entry: resume.entry,
                },
                shape,
            );
        }
    }

    let changed = world.define_transport_plan(
        root_id,
        TransportPlan {
            entry,
            executable_membership,
            positions,
        },
    );

    Ok(JobEffects {
        reads: settled_uses(reads),
        outputs: vec![FactKey::TransportPlan(root_id)],
        changed: changed.then_some(FactKey::TransportPlan(root_id)).into_iter().collect(),
        ..JobEffects::default()
    })
}

fn executable_sort_key(executable: &ExecutableKey) -> (u32, Vec<Ty>, u8, usize) {
    let need = match executable.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        executable.activation.function.as_u32(),
        executable.activation.input.clone(),
        need.0,
        need.1,
    )
}

fn executable_symbol(executable: &ExecutableKey) -> ExecutableSymbol {
    ExecutableSymbol {
        activation: ActivationSymbol {
            function: executable.activation.function,
            input: executable.activation.input.clone().into_boxed_slice(),
        },
        need: executable.need,
    }
}

fn collect_callsite_args(body: &LoweredBody) -> HashMap<CallSiteId, Vec<CallArg>> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return out;
    };
    for clause in clauses {
        collect_tail_call_args(&clause.entry, entries, &mut out);
    }
    out
}

fn collect_tail_call_args(
    entry_id: &ControlEntryId,
    entries: &[super::super::body::LoweredEntry],
    out: &mut HashMap<CallSiteId, Vec<CallArg>>,
) {
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        LoweredTail::DirectCall { callsite, args, .. } | LoweredTail::ClosureCall { callsite, args, .. } => {
            out.insert(*callsite, args.clone());
        }
        LoweredTail::If {
            then_entry, else_entry, ..
        } => {
            collect_tail_call_args(then_entry, entries, out);
            collect_tail_call_args(else_entry, entries, out);
        }
        LoweredTail::Dispatch { dispatch, .. } => {
            for arm_entry in &dispatch.arm_entries {
                collect_tail_call_args(arm_entry, entries, out);
            }
            collect_tail_call_args(&dispatch.miss_entry, entries, out);
        }
        LoweredTail::Receive(receive) => {
            for clause in &receive.clauses {
                collect_tail_call_args(&clause.entry, entries, out);
            }
            if let Some(after) = &receive.after {
                collect_tail_call_args(&after.entry, entries, out);
            }
            if let ControlDestination::Deliver(target) = receive.dest {
                collect_tail_call_args(&target, entries, out);
            }
        }
        LoweredTail::Value { dest, .. } => {
            if let ControlDestination::Deliver(target) = dest {
                collect_tail_call_args(target, entries, out);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
}

fn collect_value_origins(body: &LoweredBody) -> HashMap<ValueId, ValueOrigin> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return out;
    };
    for clause in clauses {
        for step in &clause.projections {
            collect_step_origin(step, &mut out);
        }
    }
    for entry in entries {
        for step in &entry.steps {
            collect_step_origin(step, &mut out);
        }
    }
    out
}

fn collect_step_origin(step: &LoweredStep, out: &mut HashMap<ValueId, ValueOrigin>) {
    match step {
        LoweredStep::Tuple { value, items } => {
            out.insert(*value, ValueOrigin::Tuple(items.clone().into_boxed_slice()));
        }
        LoweredStep::FunctionRef { value, function } => {
            out.insert(
                *value,
                ValueOrigin::Callable(LocalCallableProducer {
                    function: *function,
                    captures: Box::default(),
                }),
            );
        }
        LoweredStep::Lambda {
            value,
            function,
            captures,
        } => {
            out.insert(
                *value,
                ValueOrigin::Callable(LocalCallableProducer {
                    function: *function,
                    captures: captures.clone().into_boxed_slice(),
                }),
            );
        }
        _ => {}
    }
}

fn collect_return_sources(body: &LoweredBody, analysis: &ActivationAnalysis) -> Vec<ProducedSource> {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return Vec::new();
    };
    let reachable_clauses = analysis.reachable_clauses.iter().copied().collect::<HashSet<_>>();
    let reachable_entries = analysis.reachable_entries.iter().copied().collect::<HashSet<_>>();
    let mut out = Vec::new();
    for clause_id in reachable_clauses {
        collect_return_sources_from_entry(clauses[clause_id as usize].entry, entries, &reachable_entries, &mut out);
    }
    out
}

fn collect_return_sources_from_entry(
    entry_id: ControlEntryId,
    entries: &[super::super::body::LoweredEntry],
    reachable_entries: &HashSet<ControlEntryId>,
    out: &mut Vec<ProducedSource>,
) {
    if !reachable_entries.contains(&entry_id) {
        return;
    }
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        LoweredTail::Value {
            value,
            dest: ControlDestination::Return,
        } => out.push(ProducedSource::LocalValue(*value)),
        LoweredTail::DirectCall {
            callsite,
            dest: ControlDestination::Return,
            ..
        }
        | LoweredTail::ClosureCall {
            callsite,
            dest: ControlDestination::Return,
            ..
        } => out.push(ProducedSource::Callsite(*callsite)),
        LoweredTail::Value {
            dest: ControlDestination::Deliver(target),
            ..
        }
        | LoweredTail::DirectCall {
            dest: ControlDestination::Deliver(target),
            ..
        }
        | LoweredTail::ClosureCall {
            dest: ControlDestination::Deliver(target),
            ..
        } => collect_return_sources_from_entry(*target, entries, reachable_entries, out),
        LoweredTail::If {
            then_entry, else_entry, ..
        } => {
            collect_return_sources_from_entry(*then_entry, entries, reachable_entries, out);
            collect_return_sources_from_entry(*else_entry, entries, reachable_entries, out);
        }
        LoweredTail::Dispatch { dispatch, .. } => {
            for arm_entry in &dispatch.arm_entries {
                collect_return_sources_from_entry(*arm_entry, entries, reachable_entries, out);
            }
            collect_return_sources_from_entry(dispatch.miss_entry, entries, reachable_entries, out);
        }
        LoweredTail::Receive(receive) => {
            for clause in &receive.clauses {
                collect_return_sources_from_entry(clause.entry, entries, reachable_entries, out);
            }
            if let Some(after) = &receive.after {
                collect_return_sources_from_entry(after.entry, entries, reachable_entries, out);
            }
            if let ControlDestination::Deliver(target) = receive.dest {
                collect_return_sources_from_entry(target, entries, reachable_entries, out);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
}

fn collect_resume_entries(body: &LoweredBody, analysis: &ActivationAnalysis) -> Vec<ResumeEntry> {
    let LoweredBody::Clauses { entries, .. } = body else {
        return Vec::new();
    };
    let reachable_entries = analysis.reachable_entries.iter().copied().collect::<HashSet<_>>();
    let mut deliver_callsites = HashMap::new();
    for entry in entries {
        let callsite = match entry.tail {
            LoweredTail::DirectCall { callsite, .. } | LoweredTail::ClosureCall { callsite, .. } => Some(callsite),
            _ => None,
        };
        let dest = match &entry.tail {
            LoweredTail::DirectCall { dest, .. } | LoweredTail::ClosureCall { dest, .. } => Some(dest),
            _ => None,
        };
        if let (Some(callsite), Some(ControlDestination::Deliver(target))) = (callsite, dest) {
            deliver_callsites.insert(*target, callsite);
        }
    }
    entries
        .iter()
        .enumerate()
        .filter_map(|(index, entry)| {
            let entry_id = ControlEntryId::from_u32(index as u32);
            if !reachable_entries.contains(&entry_id) {
                return None;
            }
            let super::super::body::ControlEntryOrigin::DeliveredResume { value } = entry.origin else {
                return None;
            };
            Some(ResumeEntry {
                entry: entry_id,
                value,
                callsite: *deliver_callsites.get(&entry_id)?,
            })
        })
        .collect()
}

fn shape_for_local_value(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    return_shapes: &HashMap<ExecutableKey, ShapeId>,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    value: ValueId,
    ty: Ty,
    demand: &RuntimeDemand,
) -> ShapeId {
    shape_for_sources(
        world,
        contexts,
        return_shapes,
        executable,
        context,
        ty,
        demand,
        &[ProducedSource::LocalValue(value)],
    )
}

fn shape_for_sources(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    return_shapes: &HashMap<ExecutableKey, ShapeId>,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    ty: Ty,
    demand: &RuntimeDemand,
    sources: &[ProducedSource],
) -> ShapeId {
    if demand.is_ignore() || world.types().is_empty(&ty) {
        return world.transport_mut().interners_mut().intern_shape(ShapeDescr::Nothing);
    }
    let mut exact = Vec::new();
    for source in sources {
        let Some(shape) =
            exact_shape_for_source(world, contexts, return_shapes, executable, context, ty, demand, *source)
        else {
            return generic_shape_from_demand(world, ty, demand);
        };
        exact.push(shape);
    }
    if exact.is_empty() {
        return generic_shape_from_demand(world, ty, demand);
    }
    if exact.windows(2).all(|pair| pair[0] == pair[1]) {
        exact[0]
    } else {
        generic_shape_from_demand(world, ty, demand)
    }
}

fn exact_shape_for_source(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    return_shapes: &HashMap<ExecutableKey, ShapeId>,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    ty: Ty,
    demand: &RuntimeDemand,
    source: ProducedSource,
) -> Option<ShapeId> {
    match source {
        ProducedSource::LocalValue(value) => {
            exact_shape_for_local_value(world, contexts, return_shapes, executable, context, value, ty, demand)
        }
        ProducedSource::Callsite(callsite) => {
            exact_shape_for_callsite(world, return_shapes, executable, context, callsite)
        }
    }
}

fn exact_shape_for_local_value(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    return_shapes: &HashMap<ExecutableKey, ShapeId>,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    value: ValueId,
    ty: Ty,
    demand: &RuntimeDemand,
) -> Option<ShapeId> {
    match demand {
        RuntimeDemand::Ignore => Some(world.transport_mut().interners_mut().intern_shape(ShapeDescr::Nothing)),
        RuntimeDemand::Value => None,
        RuntimeDemand::TupleFields(fields) => {
            let ValueOrigin::Tuple(items) = context.local_origins.get(&value)? else {
                return None;
            };
            if items.len() != fields.len() {
                return None;
            }
            let field_tys = tuple_field_tys(world, ty, fields.len());
            let item_shapes = items
                .iter()
                .copied()
                .zip(field_tys.into_iter().zip(fields.iter()))
                .map(|(item, (item_ty, field_demand))| {
                    exact_shape_for_local_value(
                        world,
                        contexts,
                        return_shapes,
                        executable,
                        context,
                        item,
                        item_ty,
                        field_demand,
                    )
                    .or_else(|| {
                        Some(shape_for_local_value(
                            world,
                            contexts,
                            return_shapes,
                            executable,
                            context,
                            item,
                            item_ty,
                            field_demand,
                        ))
                    })
                })
                .collect::<Option<Vec<_>>>()?;
            Some(
                world
                    .transport_mut()
                    .interners_mut()
                    .intern_shape(ShapeDescr::Tuple(item_shapes.into_boxed_slice())),
            )
        }
        RuntimeDemand::Callable(_) => {
            let ValueOrigin::Callable(producer) = context.local_origins.get(&value)? else {
                return None;
            };
            let materialization = context.runtime_demand.callable_materializations.get(&value)?;
            let callable = callable_descr_for_producer(
                world,
                contexts,
                return_shapes,
                executable,
                context,
                producer,
                materialization,
            )?;
            Some(
                world
                    .transport_mut()
                    .interners_mut()
                    .intern_shape(ShapeDescr::Callable(callable)),
            )
        }
    }
}

fn exact_shape_for_callsite(
    world: &mut World<'_>,
    return_shapes: &HashMap<ExecutableKey, ShapeId>,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    callsite: CallSiteId,
) -> Option<ShapeId> {
    let key = CallSiteKey {
        activation: executable.activation.clone(),
        callsite,
    };
    let summary = world.callsite_summary(&key)?;
    let need = context
        .callsite_needs
        .get(&callsite)
        .copied()
        .unwrap_or(ExecutableNeed::Value);
    let mut shapes = Vec::new();
    for target in &summary.targets {
        match target.callee {
            SelectedCallee::ProviderBoundary(_) => return None,
            SelectedCallee::Function(_) => {
                let activation = target.activation.clone()?;
                shapes.push(*return_shapes.get(&ExecutableKey { activation, need })?);
            }
        }
    }
    if shapes.is_empty() || !shapes.windows(2).all(|pair| pair[0] == pair[1]) {
        return None;
    }
    Some(shapes[0])
}

fn callable_descr_for_producer(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    return_shapes: &HashMap<ExecutableKey, ShapeId>,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    producer: &LocalCallableProducer,
    materialization: &CallableMaterialization,
) -> Option<super::super::transport::CallableId> {
    let capture_shapes = producer
        .captures
        .iter()
        .copied()
        .map(|capture| {
            let capture_ty = context.analysis.value_types.get(&capture).copied()?;
            let capture_demand = boundary_runtime_demand(world, capture_ty);
            Some(shape_for_local_value(
                world,
                contexts,
                return_shapes,
                executable,
                context,
                capture,
                capture_ty,
                &capture_demand,
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    let surfaces = match materialization {
        CallableMaterialization::DirectOnly { surfaces } => direct_surface_shapes(world, surfaces),
        CallableMaterialization::FirstClass { .. } => Vec::new(),
    };
    let target_input = callable_target_input(world, producer, materialization, &capture_shapes, context);
    Some(world.transport_mut().interners_mut().intern_callable(CallableDescr {
        target: ExecutableSymbol {
            activation: ActivationSymbol {
                function: producer.function,
                input: target_input.into_boxed_slice(),
            },
            need: ExecutableNeed::Value,
        },
        capture_shapes: capture_shapes.into_boxed_slice(),
        direct_surfaces: surfaces.into_boxed_slice(),
    }))
}

fn callable_target_input(
    world: &mut World<'_>,
    producer: &LocalCallableProducer,
    materialization: &CallableMaterialization,
    _capture_shapes: &[ShapeId],
    context: &ExecutableContext,
) -> Vec<Ty> {
    let mut out = producer
        .captures
        .iter()
        .copied()
        .map(|capture| {
            context
                .analysis
                .value_types
                .get(&capture)
                .copied()
                .unwrap_or_else(|| world.types_mut().any())
        })
        .collect::<Vec<_>>();
    let surfaces = match materialization {
        CallableMaterialization::DirectOnly { surfaces } | CallableMaterialization::FirstClass { surfaces } => surfaces,
    };
    if let Some(surface) = surfaces.iter().next() {
        out.extend(surface.inputs.iter().copied());
    }
    out
}

fn direct_surface_shapes(world: &mut World<'_>, surfaces: &BTreeSet<CallableSurface>) -> Vec<Box<[ShapeId]>> {
    let mut rendered = surfaces
        .iter()
        .map(|surface| {
            surface
                .inputs
                .iter()
                .copied()
                .map(|ty| {
                    let demand = boundary_runtime_demand(world, ty);
                    generic_shape_from_demand(world, ty, &demand)
                })
                .collect::<Vec<_>>()
                .into_boxed_slice()
        })
        .collect::<Vec<_>>();
    rendered.sort_by_key(|surface| surface.iter().map(|shape| shape.as_u32()).collect::<Vec<_>>());
    rendered
}

fn generic_shape_from_demand(world: &mut World<'_>, ty: Ty, demand: &RuntimeDemand) -> ShapeId {
    if demand.is_ignore() || world.types().is_empty(&ty) {
        return world.transport_mut().interners_mut().intern_shape(ShapeDescr::Nothing);
    }
    match demand {
        RuntimeDemand::Ignore => world.transport_mut().interners_mut().intern_shape(ShapeDescr::Nothing),
        RuntimeDemand::Value => value_lane_shape(world, ty),
        RuntimeDemand::TupleFields(fields) => {
            let items = tuple_field_tys(world, ty, fields.len())
                .into_iter()
                .zip(fields.iter())
                .map(|(field_ty, field_demand)| generic_shape_from_demand(world, field_ty, field_demand))
                .collect::<Vec<_>>();
            world
                .transport_mut()
                .interners_mut()
                .intern_shape(ShapeDescr::Tuple(items.into_boxed_slice()))
        }
        RuntimeDemand::Callable(_) => value_lane_shape(world, ty),
    }
}

fn value_lane_shape(world: &mut World<'_>, ty: Ty) -> ShapeId {
    let lane = world
        .transport_mut()
        .interners_mut()
        .intern_lane(super::super::transport::LaneDescr {
            ty,
            class: TransportClass::Value,
        });
    world
        .transport_mut()
        .interners_mut()
        .intern_shape(ShapeDescr::Lane(lane))
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

fn boundary_runtime_demand(world: &mut World<'_>, ty: Ty) -> RuntimeDemand {
    let Some(clauses) = world.types_mut().callable_clauses(&ty) else {
        return RuntimeDemand::Value;
    };
    RuntimeDemand::callable(CallableDemand {
        resolved: clauses
            .into_iter()
            .map(|clause| CallableSurface::new(clause.args))
            .collect::<BTreeSet<_>>(),
        opaque: false,
        escape: true,
    })
}

fn runtime_demand_for_executable_need(need: ExecutableNeed) -> RuntimeDemand {
    match need {
        ExecutableNeed::Value => RuntimeDemand::Value,
        ExecutableNeed::TupleFields(arity) => RuntimeDemand::tuple_fields(vec![RuntimeDemand::Value; arity]),
    }
}

fn resume_demand(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    resume: ResumeEntry,
) -> RuntimeDemand {
    let key = CallSiteKey {
        activation: executable.activation.clone(),
        callsite: resume.callsite,
    };
    let Some(summary) = world.callsite_summary(&key) else {
        return context
            .runtime_demand
            .value_demands
            .get(&resume.value)
            .cloned()
            .unwrap_or_default();
    };
    if summary
        .targets
        .iter()
        .any(|target| matches!(target.callee, SelectedCallee::ProviderBoundary(_)))
    {
        return RuntimeDemand::Value;
    }
    let need = context
        .callsite_needs
        .get(&resume.callsite)
        .copied()
        .unwrap_or(ExecutableNeed::Value);
    if summary.targets.len() == 1
        && let Some(target) = summary.targets.first()
        && let Some(activation) = target.activation.clone()
        && let Some(callee) = contexts.get(&ExecutableKey { activation, need })
    {
        return callee.runtime_demand.return_demand.clone();
    }
    runtime_demand_for_executable_need(need)
}

fn resume_shape(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    return_shapes: &HashMap<ExecutableKey, ShapeId>,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    resume: ResumeEntry,
    demand: &RuntimeDemand,
) -> ShapeId {
    let value_ty = context
        .analysis
        .value_types
        .get(&resume.value)
        .copied()
        .unwrap_or_else(|| world.types_mut().any());
    exact_shape_for_callsite(world, return_shapes, executable, context, resume.callsite).unwrap_or_else(|| {
        shape_for_sources(
            world,
            contexts,
            return_shapes,
            executable,
            context,
            value_ty,
            demand,
            &[ProducedSource::Callsite(resume.callsite)],
        )
    })
}
