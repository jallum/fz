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
    ActivationSymbol, BoundaryDescr, BoundaryFacts, BoundaryId, BoundaryReturnDescr, CallableDescr, CallableFacts,
    CallableId, CallableMaterializationKind, ExecutableSymbol, LaneId, ShapeDescr, ShapeId, TransportClass,
    TransportPlan, TransportPosition,
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
    input_values: Vec<Box<[ValueId]>>,
    local_origins: HashMap<ValueId, ValueOrigin>,
    callable_uses: HashMap<ValueId, Vec<CallSiteId>>,
    return_sources: Vec<ProducedSource>,
    resume_entries: Vec<ResumeEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ValueOrigin {
    Tuple(Box<[ValueId]>),
    Callable(LocalCallableProducer),
    Callsite(CallSiteId),
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct CallableFactsDraft {
    resolutions: Vec<ExecutableSymbol>,
    direct_surfaces: Vec<Box<[ShapeId]>>,
    capture_lanes: Vec<LaneId>,
    materialization: CallableMaterializationKind,
    boundary_ids: Vec<BoundaryId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BoundaryFactsDraft {
    publications: Vec<TransportPosition>,
}

#[derive(Debug, Default)]
struct TransportFactsBuilder {
    callables: HashMap<CallableId, CallableFactsDraft>,
    boundaries: HashMap<BoundaryId, BoundaryFactsDraft>,
}

impl TransportFactsBuilder {
    fn record_callable(
        &mut self,
        callable: CallableId,
        resolutions: Vec<ExecutableSymbol>,
        direct_surfaces: Vec<Box<[ShapeId]>>,
        capture_lanes: Vec<LaneId>,
        materialization: CallableMaterializationKind,
        boundary_ids: Vec<BoundaryId>,
    ) {
        let entry = self.callables.entry(callable).or_insert_with(|| CallableFactsDraft {
            resolutions: Vec::new(),
            direct_surfaces: Vec::new(),
            capture_lanes: Vec::new(),
            materialization,
            boundary_ids: Vec::new(),
        });
        entry.materialization = match (entry.materialization, materialization) {
            (CallableMaterializationKind::FirstClass, _) | (_, CallableMaterializationKind::FirstClass) => {
                CallableMaterializationKind::FirstClass
            }
            _ => CallableMaterializationKind::DirectOnly,
        };
        extend_unique(&mut entry.resolutions, resolutions);
        extend_unique(&mut entry.direct_surfaces, direct_surfaces);
        extend_unique(&mut entry.capture_lanes, capture_lanes);
        extend_unique(&mut entry.boundary_ids, boundary_ids);
    }

    fn record_boundary(&mut self, boundary: BoundaryId, publication: TransportPosition) {
        let entry = self.boundaries.entry(boundary).or_insert_with(|| BoundaryFactsDraft {
            publications: Vec::new(),
        });
        if !entry.publications.contains(&publication) {
            entry.publications.push(publication);
        }
    }

    fn finish(self) -> (HashMap<CallableId, CallableFacts>, HashMap<BoundaryId, BoundaryFacts>) {
        let callables = self
            .callables
            .into_iter()
            .map(|(id, mut draft)| {
                draft.resolutions.sort_by_key(executable_symbol_sort_key);
                draft
                    .direct_surfaces
                    .sort_by_key(|surface| surface.iter().map(|shape| shape.as_u32()).collect::<Vec<_>>());
                draft.capture_lanes.sort_by_key(|lane| lane.as_u32());
                draft.boundary_ids.sort_by_key(|boundary| boundary.as_u32());
                (
                    id,
                    CallableFacts {
                        resolutions: draft.resolutions.into_boxed_slice(),
                        direct_surfaces: draft.direct_surfaces.into_boxed_slice(),
                        capture_lanes: draft.capture_lanes.into_boxed_slice(),
                        materialization: draft.materialization,
                        boundary_ids: draft.boundary_ids.into_boxed_slice(),
                    },
                )
            })
            .collect();
        let boundaries = self
            .boundaries
            .into_iter()
            .map(|(id, draft)| {
                (
                    id,
                    BoundaryFacts {
                        publications: draft.publications.into_boxed_slice(),
                    },
                )
            })
            .collect();
        (callables, boundaries)
    }
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
        let resume_entries = collect_resume_entries(&body, &analysis);
        let mut local_origins = collect_value_origins(&body);
        for (value, callsite) in collect_callsite_result_origins(&body) {
            local_origins.insert(value, ValueOrigin::Callsite(callsite));
        }
        for resume in &resume_entries {
            local_origins.insert(resume.value, ValueOrigin::Callsite(resume.callsite));
        }
        contexts.insert(
            executable.clone(),
            ExecutableContext {
                callsite_args: collect_callsite_args(&body),
                input_values: collect_input_values(&body),
                local_origins,
                callable_uses: collect_callable_uses(&body),
                return_sources: collect_return_sources(&body, &analysis),
                resume_entries,
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
    let executables = order_executables_by_call_dependencies(world, executables, &contexts);

    let entry = executable_symbol(&closure.entry);
    let executable_membership = executables
        .iter()
        .map(executable_symbol)
        .collect::<Vec<_>>()
        .into_boxed_slice();

    let mut facts = TransportFactsBuilder::default();
    let mut return_shapes = HashMap::<ExecutableKey, ShapeId>::new();
    for executable in &executables {
        let context = contexts
            .get(executable)
            .expect("transport derivation requires one context per settled executable");
        let symbol = executable_symbol(executable);
        let shape = shape_for_sources(
            world,
            &contexts,
            &return_shapes,
            &mut facts,
            executable,
            context,
            context.return_ty,
            &context.runtime_demand.return_demand,
            &context.return_sources,
            Some(TransportPosition::ExecutableReturn { executable: symbol }),
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
            let position = TransportPosition::ExecutableInput {
                executable: symbol.clone(),
                semantic_index,
            };
            let input_values = context
                .input_values
                .get(semantic_index)
                .map(|values| values.as_ref())
                .unwrap_or(&[]);
            let shape = shape_for_executable_input(
                world,
                context,
                ty,
                &demand,
                input_values,
                &mut facts,
                Some(position.clone()),
            );
            positions.insert(position, shape);
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
                &mut facts,
                executable,
                context,
                value,
                ty,
                &demand,
                Some(TransportPosition::Value {
                    executable: symbol.clone(),
                    value,
                }),
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
                            &mut facts,
                            executable,
                            context,
                            arg.value,
                            ty,
                            &demand,
                            Some(TransportPosition::CallArg {
                                executable: symbol.clone(),
                                callsite,
                                semantic_index,
                            }),
                        )
                    })
                    .unwrap_or_else(|| {
                        generic_shape_from_demand(
                            world,
                            ty,
                            &demand,
                            &mut facts,
                            Some(TransportPosition::CallArg {
                                executable: symbol.clone(),
                                callsite,
                                semantic_index,
                            }),
                        )
                    });
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
                    &mut facts,
                    executable,
                    context,
                    capture,
                    ty,
                    &demand,
                    Some(TransportPosition::EntryCapture {
                        executable: symbol.clone(),
                        entry,
                        capture_index,
                    }),
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
            let position = TransportPosition::ResumePayload {
                executable: symbol.clone(),
                callsite: resume.callsite,
                entry: resume.entry,
            };
            let shape = resume_shape(
                world,
                &contexts,
                &return_shapes,
                &mut facts,
                executable,
                context,
                *resume,
                &demand,
                Some(position.clone()),
            );
            positions.insert(position, shape);
        }
    }
    let (callables, boundaries) = facts.finish();

    let changed = world.define_transport_plan(
        root_id,
        TransportPlan {
            entry,
            executable_membership,
            positions,
            callables,
            boundaries,
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

fn order_executables_by_call_dependencies(
    world: &World<'_>,
    executables: Vec<ExecutableKey>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
) -> Vec<ExecutableKey> {
    let membership = executables.iter().cloned().collect::<HashSet<_>>();
    let mut visiting = HashSet::new();
    let mut visited = HashSet::new();
    let mut out = Vec::new();
    for executable in &executables {
        visit_executable_dependencies(
            world,
            contexts,
            &membership,
            executable,
            &mut visiting,
            &mut visited,
            &mut out,
        );
    }
    out
}

fn visit_executable_dependencies(
    world: &World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    membership: &HashSet<ExecutableKey>,
    executable: &ExecutableKey,
    visiting: &mut HashSet<ExecutableKey>,
    visited: &mut HashSet<ExecutableKey>,
    out: &mut Vec<ExecutableKey>,
) {
    if visited.contains(executable) || !visiting.insert(executable.clone()) {
        return;
    }
    if let Some(context) = contexts.get(executable) {
        let mut callsites = context.analysis.callsites.clone();
        callsites.sort_by_key(|callsite| callsite.as_u32());
        for callsite in callsites {
            let key = CallSiteKey {
                activation: executable.activation.clone(),
                callsite,
            };
            let Some(summary) = world.callsite_summary(&key) else {
                continue;
            };
            let need = context
                .callsite_needs
                .get(&callsite)
                .copied()
                .unwrap_or(ExecutableNeed::Value);
            for target in &summary.targets {
                let Some(activation) = target.activation.clone() else {
                    continue;
                };
                let dependency = ExecutableKey { activation, need };
                if membership.contains(&dependency) {
                    visit_executable_dependencies(world, contexts, membership, &dependency, visiting, visited, out);
                }
            }
        }
    }
    visiting.remove(executable);
    visited.insert(executable.clone());
    out.push(executable.clone());
}

fn executable_symbol_sort_key(symbol: &ExecutableSymbol) -> (u32, Vec<Ty>, u8, usize) {
    let need = match symbol.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        symbol.activation.function.as_u32(),
        symbol.activation.input.to_vec(),
        need.0,
        need.1,
    )
}

fn extend_unique<T: PartialEq>(target: &mut Vec<T>, values: Vec<T>) {
    for value in values {
        if !target.contains(&value) {
            target.push(value);
        }
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

fn collect_callsite_result_origins(body: &LoweredBody) -> HashMap<ValueId, CallSiteId> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { entries, .. } = body else {
        return out;
    };
    for entry in entries {
        match &entry.tail {
            LoweredTail::DirectCall { value, callsite, .. } | LoweredTail::ClosureCall { value, callsite, .. } => {
                out.insert(*value, *callsite);
            }
            _ => {}
        }
    }
    out
}

fn collect_input_values(body: &LoweredBody) -> Vec<Box<[ValueId]>> {
    let LoweredBody::Clauses { clauses, .. } = body else {
        return Vec::new();
    };
    let arity = clauses.iter().map(|clause| clause.params.len()).max().unwrap_or(0);
    let mut out = vec![Vec::new(); arity];
    for clause in clauses {
        for (index, value) in clause.params.iter().copied().enumerate() {
            if !out[index].contains(&value) {
                out[index].push(value);
            }
        }
    }
    out.into_iter().map(Vec::into_boxed_slice).collect()
}

fn collect_callable_uses(body: &LoweredBody) -> HashMap<ValueId, Vec<CallSiteId>> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { entries, .. } = body else {
        return out;
    };
    for entry in entries {
        let LoweredTail::ClosureCall { callee, callsite, .. } = &entry.tail else {
            continue;
        };
        out.entry(*callee).or_insert_with(Vec::new).push(*callsite);
    }
    out
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
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    value: ValueId,
    ty: Ty,
    demand: &RuntimeDemand,
    publication: Option<TransportPosition>,
) -> ShapeId {
    shape_for_sources(
        world,
        contexts,
        return_shapes,
        facts,
        executable,
        context,
        ty,
        demand,
        &[ProducedSource::LocalValue(value)],
        publication,
    )
}

fn shape_for_executable_input(
    world: &mut World<'_>,
    context: &ExecutableContext,
    ty: Ty,
    demand: &RuntimeDemand,
    input_values: &[ValueId],
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
    let RuntimeDemand::Callable(callable) = demand else {
        return generic_shape_from_demand(world, ty, demand, facts, publication);
    };
    let surfaces = callable_surface_evidence(world, context, ty, callable, input_values);
    generic_callable_shape(world, ty, callable, &surfaces, facts, publication)
}

fn shape_for_sources(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    return_shapes: &HashMap<ExecutableKey, ShapeId>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    ty: Ty,
    demand: &RuntimeDemand,
    sources: &[ProducedSource],
    publication: Option<TransportPosition>,
) -> ShapeId {
    if demand.is_ignore() || world.types().is_empty(&ty) {
        return world.transport_mut().interners_mut().intern_shape(ShapeDescr::Nothing);
    }
    let mut exact = Vec::new();
    for source in sources {
        let Some(shape) = exact_shape_for_source(
            world,
            contexts,
            return_shapes,
            facts,
            executable,
            context,
            ty,
            demand,
            *source,
            publication.clone(),
        ) else {
            return generic_shape_from_demand(world, ty, demand, facts, publication);
        };
        exact.push(shape);
    }
    if exact.is_empty() {
        return generic_shape_from_demand(world, ty, demand, facts, publication);
    }
    if exact.windows(2).all(|pair| pair[0] == pair[1]) {
        exact[0]
    } else {
        generic_shape_from_demand(world, ty, demand, facts, publication)
    }
}

fn exact_shape_for_source(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    return_shapes: &HashMap<ExecutableKey, ShapeId>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    ty: Ty,
    demand: &RuntimeDemand,
    source: ProducedSource,
    publication: Option<TransportPosition>,
) -> Option<ShapeId> {
    match source {
        ProducedSource::LocalValue(value) => exact_shape_for_local_value(
            world,
            contexts,
            return_shapes,
            facts,
            executable,
            context,
            value,
            ty,
            demand,
            publication,
        ),
        ProducedSource::Callsite(callsite) => {
            exact_shape_for_callsite(world, return_shapes, executable, context, callsite)
        }
    }
}

fn exact_shape_for_local_value(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    return_shapes: &HashMap<ExecutableKey, ShapeId>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    value: ValueId,
    ty: Ty,
    demand: &RuntimeDemand,
    publication: Option<TransportPosition>,
) -> Option<ShapeId> {
    match demand {
        RuntimeDemand::Ignore => Some(world.transport_mut().interners_mut().intern_shape(ShapeDescr::Nothing)),
        RuntimeDemand::Value => match context.local_origins.get(&value) {
            Some(ValueOrigin::Callsite(callsite)) => {
                exact_shape_for_callsite(world, return_shapes, executable, context, *callsite)
            }
            _ => None,
        },
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
                        facts,
                        executable,
                        context,
                        item,
                        item_ty,
                        field_demand,
                        None,
                    )
                    .or_else(|| {
                        Some(shape_for_local_value(
                            world,
                            contexts,
                            return_shapes,
                            facts,
                            executable,
                            context,
                            item,
                            item_ty,
                            field_demand,
                            None,
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
            let callable = match context.local_origins.get(&value)? {
                ValueOrigin::Callable(producer) => {
                    let materialization = context.runtime_demand.callable_materializations.get(&value)?;
                    let callable_demand =
                        context
                            .runtime_demand
                            .value_demands
                            .get(&value)
                            .and_then(|demand| match demand {
                                RuntimeDemand::Callable(callable) => Some(callable),
                                _ => None,
                            });
                    callable_for_producer(
                        world,
                        contexts,
                        return_shapes,
                        facts,
                        executable,
                        context,
                        producer,
                        materialization,
                        ty,
                        callable_demand,
                        publication,
                    )?
                }
                ValueOrigin::Callsite(callsite) => {
                    return exact_shape_for_callsite(world, return_shapes, executable, context, *callsite);
                }
                ValueOrigin::Tuple(_) => return None,
            };
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

fn callable_for_producer(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    return_shapes: &HashMap<ExecutableKey, ShapeId>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    producer: &LocalCallableProducer,
    materialization: &CallableMaterialization,
    callable_ty: Ty,
    callable_demand: Option<&CallableDemand>,
    publication: Option<TransportPosition>,
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
                facts,
                executable,
                context,
                capture,
                capture_ty,
                &capture_demand,
                None,
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    let capture_lanes = capture_shapes
        .iter()
        .copied()
        .flat_map(|shape| shape_lanes(world, shape))
        .collect::<Vec<_>>();
    let materialization_surfaces = match materialization {
        CallableMaterialization::DirectOnly { surfaces } | CallableMaterialization::FirstClass { surfaces } => surfaces,
    };
    let surface_demands = callable_demand
        .map(|demand| callable_surface_evidence(world, context, callable_ty, demand, &[]))
        .filter(|surfaces| !surfaces.is_empty())
        .unwrap_or_else(|| {
            if materialization_surfaces.is_empty() {
                callable_type_surfaces(world, callable_ty)
            } else {
                materialization_surfaces.clone()
            }
        });
    let surface_shapes = surface_shapes(world, &surface_demands, facts);
    let direct_surfaces = match materialization {
        CallableMaterialization::DirectOnly { .. } => surface_shapes.clone(),
        CallableMaterialization::FirstClass { .. } => Vec::new(),
    };
    let materialization_kind = match materialization {
        CallableMaterialization::DirectOnly { .. } => CallableMaterializationKind::DirectOnly,
        CallableMaterialization::FirstClass { .. } => CallableMaterializationKind::FirstClass,
    };
    let callable = world.transport_mut().interners_mut().intern_callable(CallableDescr {
        function: Some(producer.function),
        capture_shapes: capture_shapes.into_boxed_slice(),
    });
    let resolutions = callable_resolutions(world, context, producer, &surface_demands);
    let boundary_ids = match materialization {
        CallableMaterialization::DirectOnly { .. } => Vec::new(),
        CallableMaterialization::FirstClass { .. } => publish_boundaries_for_callable(
            world,
            facts,
            callable,
            &surface_demands,
            &surface_shapes,
            &capture_lanes,
            callable_ty,
            publication,
        ),
    };
    facts.record_callable(
        callable,
        resolutions,
        direct_surfaces,
        capture_lanes,
        materialization_kind,
        boundary_ids,
    );
    Some(callable)
}

fn surface_shapes(
    world: &mut World<'_>,
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
    rendered.sort_by_key(|surface| surface.iter().map(|shape| shape.as_u32()).collect::<Vec<_>>());
    rendered
}

fn callable_surface_evidence(
    world: &mut World<'_>,
    context: &ExecutableContext,
    callable_ty: Ty,
    demand: &CallableDemand,
    values: &[ValueId],
) -> BTreeSet<CallableSurface> {
    let mut surfaces = demand.resolved.clone();
    for value in values {
        let Some(callsites) = context.callable_uses.get(value) else {
            continue;
        };
        for callsite in callsites {
            let Some(args) = context.callsite_args.get(callsite) else {
                continue;
            };
            surfaces.insert(CallableSurface::new(
                args.iter()
                    .map(|arg| {
                        context
                            .analysis
                            .value_types
                            .get(&arg.value)
                            .copied()
                            .unwrap_or_else(|| world.types_mut().any())
                    })
                    .collect(),
            ));
        }
    }
    if surfaces.is_empty() {
        surfaces = callable_type_surfaces(world, callable_ty);
    }
    surfaces
}

fn callable_type_surfaces(world: &mut World<'_>, callable_ty: Ty) -> BTreeSet<CallableSurface> {
    world
        .types_mut()
        .callable_clauses(&callable_ty)
        .unwrap_or_default()
        .into_iter()
        .map(|clause| CallableSurface::new(clause.args))
        .collect()
}

fn callable_resolutions(
    world: &mut World<'_>,
    context: &ExecutableContext,
    producer: &LocalCallableProducer,
    surfaces: &BTreeSet<CallableSurface>,
) -> Vec<ExecutableSymbol> {
    let capture_tys = producer
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
    surfaces
        .iter()
        .map(|surface| {
            let mut input = capture_tys.clone();
            input.extend(surface.inputs.iter().copied());
            ExecutableSymbol {
                activation: ActivationSymbol {
                    function: producer.function,
                    input: input.into_boxed_slice(),
                },
                need: ExecutableNeed::Value,
            }
        })
        .collect()
}

fn generic_shape_from_demand(
    world: &mut World<'_>,
    ty: Ty,
    demand: &RuntimeDemand,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
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
                .map(|(field_ty, field_demand)| generic_shape_from_demand(world, field_ty, field_demand, facts, None))
                .collect::<Vec<_>>();
            world
                .transport_mut()
                .interners_mut()
                .intern_shape(ShapeDescr::Tuple(items.into_boxed_slice()))
        }
        RuntimeDemand::Callable(callable) => {
            let surfaces = if callable.resolved.is_empty() {
                callable_type_surfaces(world, ty)
            } else {
                callable.resolved.clone()
            };
            generic_callable_shape(world, ty, callable, &surfaces, facts, publication)
        }
    }
}

fn generic_callable_shape(
    world: &mut World<'_>,
    ty: Ty,
    demand: &CallableDemand,
    surfaces: &BTreeSet<CallableSurface>,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
    let callable = world.transport_mut().interners_mut().intern_callable(CallableDescr {
        function: None,
        capture_shapes: Box::default(),
    });
    let surface_shapes = surface_shapes(world, surfaces, facts);
    let materialization = if demand.opaque || demand.escape {
        CallableMaterializationKind::FirstClass
    } else {
        CallableMaterializationKind::DirectOnly
    };
    let direct_surfaces = if matches!(materialization, CallableMaterializationKind::DirectOnly) {
        surface_shapes.clone()
    } else {
        Vec::new()
    };
    let boundary_ids = if matches!(materialization, CallableMaterializationKind::FirstClass) {
        publish_boundaries_for_callable(world, facts, callable, surfaces, &surface_shapes, &[], ty, publication)
    } else {
        Vec::new()
    };
    facts.record_callable(
        callable,
        Vec::new(),
        direct_surfaces,
        Vec::new(),
        materialization,
        boundary_ids,
    );
    world
        .transport_mut()
        .interners_mut()
        .intern_shape(ShapeDescr::Callable(callable))
}

fn publish_boundaries_for_callable(
    world: &mut World<'_>,
    facts: &mut TransportFactsBuilder,
    callable: CallableId,
    surfaces: &BTreeSet<CallableSurface>,
    surface_shapes: &[Box<[ShapeId]>],
    capture_lanes: &[LaneId],
    callable_ty: Ty,
    publication: Option<TransportPosition>,
) -> Vec<BoundaryId> {
    let ret = boundary_return_for_callable(world, callable_ty);
    let mut boundary_ids = Vec::new();
    for (surface, arg_shapes) in surfaces.iter().zip(surface_shapes.iter()) {
        let arg_lanes = arg_shapes
            .iter()
            .copied()
            .flat_map(|shape| shape_lanes(world, shape))
            .collect::<Vec<_>>();
        let boundary = world.transport_mut().interners_mut().intern_boundary(BoundaryDescr {
            callable,
            surface_arg_shapes: arg_shapes.clone(),
            published_capture_lanes: capture_lanes.to_vec().into_boxed_slice(),
            published_arg_lanes: arg_lanes.into_boxed_slice(),
            published_return: ret.clone(),
        });
        if let Some(position) = publication.clone() {
            facts.record_boundary(boundary, position);
        } else {
            facts.record_boundary(boundary, TransportPosition::Boundary { boundary });
        }
        boundary_ids.push(boundary);
        let _ = surface;
    }
    boundary_ids
}

fn boundary_return_for_callable(world: &mut World<'_>, callable_ty: Ty) -> BoundaryReturnDescr {
    let ret_ty = world.types_mut().arrow_join_return(&callable_ty);
    if world.types().is_empty(&ret_ty) {
        BoundaryReturnDescr::Nothing
    } else {
        let lane = value_lane(world, ret_ty);
        BoundaryReturnDescr::Value(lane)
    }
}

fn shape_lanes(world: &World<'_>, shape: ShapeId) -> Vec<LaneId> {
    match world.transport().interners().shape(shape) {
        ShapeDescr::Nothing => Vec::new(),
        ShapeDescr::Lane(lane) => vec![*lane],
        ShapeDescr::Tuple(items) => items
            .iter()
            .copied()
            .flat_map(|item| shape_lanes(world, item))
            .collect(),
        ShapeDescr::Callable(_) => Vec::new(),
    }
}

fn value_lane_shape(world: &mut World<'_>, ty: Ty) -> ShapeId {
    let lane = value_lane(world, ty);
    world
        .transport_mut()
        .interners_mut()
        .intern_shape(ShapeDescr::Lane(lane))
}

fn value_lane(world: &mut World<'_>, ty: Ty) -> LaneId {
    world
        .transport_mut()
        .interners_mut()
        .intern_lane(super::super::transport::LaneDescr {
            ty,
            class: TransportClass::Value,
        })
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
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    resume: ResumeEntry,
    demand: &RuntimeDemand,
    publication: Option<TransportPosition>,
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
            facts,
            executable,
            context,
            value_ty,
            demand,
            &[ProducedSource::Callsite(resume.callsite)],
            publication,
        )
    })
}
