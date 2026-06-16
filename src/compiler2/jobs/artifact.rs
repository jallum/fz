//! Compiler2 artifact projection jobs.
//!
//! This module turns a closed semantic root into backend-owned artifact
//! projections. Each rung is derived from the one below it and never reopens
//! semantic discovery.

use std::collections::{HashMap, HashSet};

use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{PatternDispatchOutcome, PatternDispatchPlan, PatternSubjectRef};
use crate::dispatch_matrix::{
    DispatchCompileOptions, DispatchMatrixBuilder, EdgeEvidence, EqualTypeRegionPolicy, Order, OutcomeMultiplicity,
    RegionQuestion, compile_dispatch_matrix_with_type_order,
};
use crate::ir_lower::extern_ty_from_name;
use crate::parser::lexer::Tok;

use super::super::artifact::{
    AbiReadyCallEdge, AbiReadyExecutable, AbiReadyProgram, AbiValueRepr, CallTarget, CallableEntry, EffectSummary,
    EmissionReadyCallEdge, EmissionReadyCallableEntry, EmissionReadyExecutable, EmissionReadyProgram,
    ExecutableDispatch, MaterializedCallEdge, MaterializedExecutable, MaterializedExecutableTransport,
    MaterializedProgram, MaterializedTransportPlan,
};
use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, ControlEntryOrigin, DispatchBindings,
    Literal, LoweredBody, LoweredEntry, LoweredStep, LoweredTail, ValueId,
};
use super::super::drive::{FactKey, Job, JobEffects, settled_uses};
use super::super::identity::{ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, RootId};
use super::super::scheduler::FatalError;
use super::super::semantic::{ActivationAnalysis, CallSiteKey, CallTargetSummary, SelectedCallee};
use super::super::transport::{
    ActivationSymbol, CodegenLaneRepr, CodegenSeam, ExecutableSymbol, LaneId, ShapeDescr, ShapeId, TransportPlan,
    TransportPosition,
};
use super::super::types::Ty;
use super::super::world::World;
use super::semantic::executable_callsite_needs;

const UNREACHABLE_CONTROL_ATOM: &str = "compiler2_unreachable_control";
const PROTOCOL_DISPATCH_UNPLANNED_ATOM: &str = "protocol_dispatch_unplanned";

/// Materializes one closed root into a backend-owned program snapshot.
///
/// The job reads the current `SemanticClosed(root)` payload, clones only the
/// reachable lowered bodies, prunes unreachable clauses, rewrites semantically
/// cold local-control entries into explicit halt stubs, freezes each live
/// callsite to its selected callee executable, and settles executable effects
/// over the closed call graph. Missing semantic constituents are fatal:
/// materialization never reopens discovery.
pub(super) fn materialize_root(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let closed_fact = FactKey::SemanticClosed(root_id);
    if !world.fact_is_settled(&closed_fact) {
        return Ok(JobEffects::wait_on_settled(
            closed_fact,
            [super::super::Job::SealSemanticClosure(root_id)],
        ));
    }
    let transport_fact = FactKey::TransportPlan(root_id);
    if !world.fact_is_settled(&transport_fact) {
        return Ok(JobEffects::wait_on_settled(
            transport_fact,
            [super::super::Job::DeriveTransportPlan(root_id)],
        ));
    }

    let closed_revision = world
        .fact_revision(&closed_fact)
        .expect("settled semantic closure should have a revision");
    let transport_revision = world
        .fact_revision(&transport_fact)
        .expect("settled transport plan should have a revision");
    let transport_plan = world
        .transport()
        .plans()
        .get(root_id)
        .cloned()
        .expect("settled transport plan should be readable");
    let closure = world.semantic_closure(root_id);
    let reads = settled_uses([closed_fact, transport_fact]);
    let mut executables = HashMap::new();

    for executable in &closure.executables {
        let analysis = world
            .activation_analysis(&executable.activation)
            .cloned()
            .expect("settled semantic closure should have activation analysis for every executable");
        // The Kleene reading at the settled boundary: return evidence still
        // absent at the fixpoint means no value ever flows — the function
        // provably never returns, and its return type is the empty type.
        let return_ty = world
            .activation_return(&executable.activation)
            .unwrap_or_else(|| world.types_mut().none());
        let pruned = prune_lowered_body(
            world.lowered_body(executable.activation.function),
            &analysis.reachable_clauses,
            &analysis.reachable_entries,
        );
        let mut body = pruned.body;
        let synthetic_targets = rewrite_protocol_dispatch_calls(world, root_id, executable, &analysis, &mut body)?;
        let callsite_args = collect_callsite_args(&body);
        let Some(call_edges) = materialize_call_edges(
            world,
            root_id,
            executable,
            &analysis,
            &body,
            &callsite_args,
            &synthetic_targets,
        )?
        else {
            return Err(incomplete_semantic_plan(
                world,
                root_id,
                format!("executable {:?} has incomplete call edges", executable),
            ));
        };
        let effects = local_effects(&body, &call_edges);
        executables.insert(
            executable.clone(),
            MaterializedExecutable {
                entry_dispatch: materialize_entry_dispatch(world, executable, &analysis),
                return_ty,
                runtime_demand: closure
                    .runtime_demands
                    .get(executable)
                    .cloned()
                    .expect("settled semantic closure should have runtime demand for every executable"),
                transport: materialized_executable_transport(&transport_plan, executable),
                original_entry_ids: pruned.original_entry_ids,
                value_types: analysis.value_types,
                effects,
                body,
                call_edges,
            },
        );
    }

    settle_effects(world, root_id, &mut executables)?;

    let program = MaterializedProgram {
        semantic_revision: closed_revision,
        transport_revision,
        entry: closure.entry,
        transport: materialized_transport_plan(&transport_plan),
        executables,
    };
    let materialized_fact = FactKey::MaterializedProgram(root_id);
    let changed = world.define_materialized_program(root_id, program);
    Ok(JobEffects {
        reads,
        outputs: vec![materialized_fact.clone()],
        changed: changed.then_some(materialized_fact).into_iter().collect(),
        follow_up: changed.then_some(Job::DeriveAbiReady(root_id)).into_iter().collect(),
        ..JobEffects::default()
    })
}

/// Derives one ABI-ready program from one materialized closed artifact.
///
/// This job consumes only `MaterializedProgram(root)` plus the world-owned type
/// store. It makes ABI lanes and return delivery explicit without asking any
/// semantic question or discovering new executable work.
pub(super) fn derive_abi_ready(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let materialized_fact = FactKey::MaterializedProgram(root_id);
    let Some(materialized_revision) = world.fact_revision(&materialized_fact) else {
        return Ok(JobEffects::wait_on_settled(
            materialized_fact,
            [Job::MaterializeRoot(root_id)],
        ));
    };

    let reads = settled_uses([materialized_fact]);
    let materialized = world.materialized_program(root_id);
    let transport_plan = world
        .transport()
        .plans()
        .get(root_id)
        .cloned()
        .expect("materialized program should name a readable transport plan");
    let plans = materialized
        .executables
        .iter()
        .map(|(key, executable)| {
            (
                key.clone(),
                build_executable_abi_plan(world, key, executable, &transport_plan),
            )
        })
        .collect::<HashMap<_, _>>();
    let executables = materialized
        .executables
        .iter()
        .map(|(key, executable)| {
            Ok((
                key.clone(),
                derive_abi_ready_executable(
                    executable,
                    plans
                        .get(key)
                        .expect("ABI-ready executable plan should exist for every materialized executable"),
                )?,
            ))
        })
        .collect::<Result<HashMap<_, _>, FatalError>>()?;
    let callable_entries = derive_callable_entries(world, root_id, &materialized, &executables)?;
    let program = AbiReadyProgram {
        materialized_revision,
        transport_revision: materialized.transport_revision,
        entry: materialized.entry,
        transport: materialized.transport.clone(),
        executables,
        callable_entries,
    };
    let abi_ready_fact = FactKey::AbiReadyProgram(root_id);
    let changed = world.define_abi_ready_program(root_id, program);
    Ok(JobEffects {
        reads,
        outputs: vec![abi_ready_fact.clone()],
        changed: changed.then_some(abi_ready_fact).into_iter().collect(),
        follow_up: changed
            .then_some(Job::DeriveEmissionReady(root_id))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

#[derive(Debug, Clone)]
struct ExecutableAbiPlan {
    param_reprs: Vec<AbiValueRepr>,
    value_reprs: HashMap<ValueId, AbiValueRepr>,
}

struct PrunedLoweredBody {
    body: LoweredBody,
    original_entry_ids: Vec<ControlEntryId>,
}

fn materialized_transport_plan(plan: &TransportPlan) -> MaterializedTransportPlan {
    let mut position_shapes = plan
        .positions
        .iter()
        .map(|(position, shape)| (position.clone(), *shape))
        .collect::<Vec<_>>();
    position_shapes.sort_by_key(|left| transport_position_sort_key(&left.0));
    let mut callable_ids = plan.callables.keys().copied().collect::<Vec<_>>();
    callable_ids.sort_by_key(|callable| callable.as_u32());
    let mut boundary_ids = plan.boundaries.keys().copied().collect::<Vec<_>>();
    boundary_ids.sort_by_key(|boundary| boundary.as_u32());
    MaterializedTransportPlan {
        entry: plan.entry.clone(),
        executable_membership: plan.executable_membership.clone(),
        position_shapes,
        callable_ids,
        boundary_ids,
        codegen_seam_facts: plan.codegen_seam_facts.clone(),
    }
}

fn materialized_executable_transport(
    plan: &TransportPlan,
    executable: &ExecutableKey,
) -> MaterializedExecutableTransport {
    let symbol = transport_executable_symbol(executable);
    let mut input_positions = Vec::new();
    let mut return_position = None;
    let mut resume_positions = Vec::new();
    let mut entry_capture_positions = Vec::new();
    let mut call_arg_positions = Vec::new();
    let mut value_positions = Vec::new();
    for position in plan.positions.keys() {
        if transport_position_executable(position) != &symbol {
            continue;
        }
        match position {
            TransportPosition::ExecutableInput { .. } => input_positions.push(position.clone()),
            TransportPosition::ExecutableReturn { .. } => return_position = Some(position.clone()),
            TransportPosition::ResumePayload { .. } => resume_positions.push(position.clone()),
            TransportPosition::EntryCapture { .. } => entry_capture_positions.push(position.clone()),
            TransportPosition::CallArg { .. } => call_arg_positions.push(position.clone()),
            TransportPosition::Value { .. } => value_positions.push(position.clone()),
        }
    }
    sort_transport_positions(&mut input_positions);
    sort_transport_positions(&mut resume_positions);
    sort_transport_positions(&mut entry_capture_positions);
    sort_transport_positions(&mut call_arg_positions);
    sort_transport_positions(&mut value_positions);
    MaterializedExecutableTransport {
        executable: symbol,
        input_positions,
        return_position: return_position.unwrap_or_else(|| {
            panic!("transport plan should publish one return position for materialized executable {executable:?}")
        }),
        resume_positions,
        entry_capture_positions,
        call_arg_positions,
        value_positions,
    }
}

fn transport_executable_symbol(executable: &ExecutableKey) -> ExecutableSymbol {
    ExecutableSymbol {
        activation: ActivationSymbol {
            function: executable.activation.function,
            input: executable.activation.input.clone().into_boxed_slice(),
        },
        need: executable.need,
    }
}

fn transport_position_executable(position: &TransportPosition) -> &ExecutableSymbol {
    match position {
        TransportPosition::ExecutableInput { executable, .. }
        | TransportPosition::ExecutableReturn { executable }
        | TransportPosition::ResumePayload { executable, .. }
        | TransportPosition::CallArg { executable, .. }
        | TransportPosition::EntryCapture { executable, .. }
        | TransportPosition::Value { executable, .. } => executable,
    }
}

fn sort_transport_positions(positions: &mut [TransportPosition]) {
    positions.sort_by_key(transport_position_sort_key);
}

fn transport_position_sort_key(position: &TransportPosition) -> (u8, u32, u32, u32, usize) {
    match position {
        TransportPosition::ExecutableInput {
            executable,
            semantic_index,
        } => (0, executable.activation.function.as_u32(), 0, 0, *semantic_index),
        TransportPosition::ExecutableReturn { executable } => (1, executable.activation.function.as_u32(), 0, 0, 0),
        TransportPosition::ResumePayload {
            executable,
            callsite,
            entry,
        } => (
            2,
            executable.activation.function.as_u32(),
            callsite.map(|callsite| callsite.as_u32()).unwrap_or(u32::MAX),
            entry.as_u32(),
            0,
        ),
        TransportPosition::EntryCapture {
            executable,
            entry,
            capture_index,
        } => (
            3,
            executable.activation.function.as_u32(),
            0,
            entry.as_u32(),
            *capture_index,
        ),
        TransportPosition::CallArg {
            executable,
            callsite,
            semantic_index,
        } => (
            4,
            executable.activation.function.as_u32(),
            callsite.as_u32(),
            0,
            *semantic_index,
        ),
        TransportPosition::Value { executable, value } => {
            (5, executable.activation.function.as_u32(), value.as_u32(), 0, 0)
        }
    }
}

/// Derives one emission-ready inventory from one ABI-ready closed artifact.
///
/// This job consumes only `AbiReadyProgram(root)`. It assigns stable
/// emission-local executable indices, rewrites executable cross-references to
/// those indices, and preserves Compiler2 keys only as descriptive inventory
/// payload.
pub(super) fn derive_emission_ready(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let abi_ready_fact = FactKey::AbiReadyProgram(root_id);
    let Some(abi_ready_revision) = world.fact_revision(&abi_ready_fact) else {
        return Ok(JobEffects::wait_on_settled(
            abi_ready_fact,
            [Job::DeriveAbiReady(root_id)],
        ));
    };

    let reads = settled_uses([abi_ready_fact]);
    let abi_ready = world.abi_ready_program(root_id);

    let mut executable_keys = abi_ready.executables.keys().cloned().collect::<Vec<_>>();
    executable_keys.sort_by(compare_executable_keys);

    let executable_index = executable_keys
        .iter()
        .enumerate()
        .map(|(index, key)| (key.clone(), index))
        .collect::<HashMap<_, _>>();

    let executables = executable_keys
        .into_iter()
        .map(|key| derive_emission_ready_executable(world, root_id, &abi_ready, &executable_index, key))
        .collect::<Result<Vec<_>, _>>()?;

    let mut callable_entries = abi_ready
        .callable_entries
        .iter()
        .map(|entry| {
            Ok(EmissionReadyCallableEntry {
                boundary: entry.boundary,
                target: executable_index.get(&entry.target).copied().ok_or_else(|| {
                    incomplete_semantic_plan(
                        world,
                        root_id,
                        format!(
                            "callable entry target {:?} is missing from the ABI-ready executable inventory",
                            entry.target
                        ),
                    )
                })?,
                capture_count: entry.capture_count,
                capture_reprs: entry.capture_reprs.clone(),
                arg_reprs: entry.arg_reprs.clone(),
                return_ty: entry.return_ty,
                return_shape: entry.return_shape,
                return_lanes: entry.return_lanes.clone(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    callable_entries.sort_by(compare_emission_callable_entries);

    let entry = executable_index.get(&abi_ready.entry).copied().ok_or_else(|| {
        incomplete_semantic_plan(
            world,
            root_id,
            format!(
                "root entry {:?} is missing from the ABI-ready executable inventory",
                abi_ready.entry
            ),
        )
    })?;

    let program = EmissionReadyProgram {
        abi_ready_revision,
        transport_revision: abi_ready.transport_revision,
        entry,
        transport: abi_ready.transport,
        executables,
        callable_entries,
    };
    let emission_ready_fact = FactKey::EmissionReadyProgram(root_id);
    let changed = world.define_emission_ready_program(root_id, program);
    Ok(JobEffects {
        reads,
        outputs: vec![emission_ready_fact.clone()],
        changed: changed.then_some(emission_ready_fact).into_iter().collect(),
        follow_up: changed
            .then_some(Job::LowerBackendProgram(root_id))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

#[derive(Debug, Clone)]
struct SyntheticCallTarget {
    function: FunctionId,
    surface_inputs: Vec<Ty>,
    activation: ActivationKey,
    return_ty: Ty,
}

fn rewrite_protocol_dispatch_calls(
    world: &mut World<'_>,
    root_id: RootId,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    body: &mut LoweredBody,
) -> Result<HashMap<CallSiteId, SyntheticCallTarget>, FatalError> {
    let LoweredBody::Clauses { entries, .. } = body else {
        return Ok(HashMap::new());
    };

    let mut synthetic = HashMap::new();
    let mut next_entry_id = entries.len() as u32;
    let mut next_callsite_id = next_callsite_id(entries);
    let mut entry_index = 0;
    while entry_index < entries.len() {
        let entry = entries[entry_index].clone();
        let LoweredTail::DirectCall {
            value,
            callsite,
            args,
            dest,
            ..
        } = entry.tail
        else {
            entry_index += 1;
            continue;
        };
        let key = CallSiteKey {
            activation: executable.activation.clone(),
            callsite,
        };
        let Some(summary) = world.callsite_summary(&key).cloned() else {
            entry_index += 1;
            continue;
        };
        if summary.targets.len() <= 1 {
            entry_index += 1;
            continue;
        }

        let receiver_ty = args
            .first()
            .and_then(|arg| analysis.value_types.get(&arg.value).copied())
            .unwrap_or_else(|| world.types_mut().any());
        let mut targets = summary.targets.clone();
        targets.sort_by_key(|target| match target.callee {
            SelectedCallee::Function(function) => (
                function.as_u32(),
                target
                    .activation
                    .as_ref()
                    .map(|activation| activation.input.len())
                    .unwrap_or(0),
            ),
            SelectedCallee::ProviderBoundary(function) => (function.as_u32(), 0),
        });
        let plan = protocol_dispatch_plan(world, root_id, receiver_ty, &targets, entry.span)?;

        let mut arm_entries = Vec::with_capacity(targets.len());
        for target in &targets {
            let SelectedCallee::Function(function) = target.callee else {
                return Err(incomplete_semantic_plan(
                    world,
                    root_id,
                    "multi-target direct-call dispatch cannot target a provider boundary",
                ));
            };
            let arm_entry = ControlEntryId::from_u32(next_entry_id);
            next_entry_id += 1;
            let synthetic_callsite = CallSiteId::from_u32(next_callsite_id);
            next_callsite_id += 1;
            synthetic.insert(
                synthetic_callsite,
                SyntheticCallTarget {
                    function,
                    surface_inputs: target.surface_inputs.clone(),
                    activation: target.activation.clone().ok_or_else(|| {
                        incomplete_semantic_plan(
                            world,
                            root_id,
                            format!(
                                "dispatch target {} is missing its settled activation",
                                function.as_u32()
                            ),
                        )
                    })?,
                    return_ty: target.settled_return(world.types_mut()),
                },
            );
            arm_entries.push(arm_entry);
            entries.push(LoweredEntry {
                span: entry.span,
                origin: ControlEntryOrigin::Branch,
                params: Vec::new(),
                captures: protocol_dispatch_entry_captures(entries, &args, &dest),
                reusable_cons_captures: Vec::new(),
                steps: Vec::new(),
                tail: LoweredTail::DirectCall {
                    value,
                    callsite: synthetic_callsite,
                    callee: function,
                    args: args.clone(),
                    dest: dest.clone(),
                },
            });
        }

        let miss_entry = ControlEntryId::from_u32(next_entry_id);
        next_entry_id += 1;
        entries.push(LoweredEntry {
            span: entry.span,
            origin: ControlEntryOrigin::Branch,
            params: Vec::new(),
            captures: Vec::new(),
            reusable_cons_captures: Vec::new(),
            steps: Vec::new(),
            tail: LoweredTail::Halt {
                atom: PROTOCOL_DISPATCH_UNPLANNED_ATOM.to_string(),
            },
        });

        let receiver_value = args.first().map(|arg| arg.value).ok_or_else(|| {
            incomplete_semantic_plan(
                world,
                root_id,
                format!(
                    "protocol dispatch callsite {} is missing its receiver",
                    callsite.as_u32()
                ),
            )
        })?;
        entries[entry_index].tail = LoweredTail::Dispatch {
            inputs: vec![receiver_value],
            bindings: DispatchBindings {
                pinned: Vec::new(),
                prepared: Vec::new(),
            },
            dispatch: Box::new(ControlDispatch {
                plan,
                arm_entries,
                miss_entry,
            }),
        };
        entry_index += 1;
    }

    Ok(synthetic)
}

fn materialize_call_edges(
    world: &mut World<'_>,
    root_id: RootId,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    body: &LoweredBody,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
    synthetic_targets: &HashMap<CallSiteId, SyntheticCallTarget>,
) -> Result<Option<HashMap<CallSiteId, MaterializedCallEdge>>, FatalError> {
    let mut call_edges = HashMap::new();
    let callsite_needs = callsite_needs_for_body(body, executable.need);
    let LoweredBody::Clauses { entries, .. } = body else {
        return Ok(Some(call_edges));
    };
    for entry in entries {
        match &entry.tail {
            LoweredTail::DirectCall { callsite, .. } => {
                let Some(edge) = materialize_direct_call_edge(
                    world,
                    root_id,
                    executable,
                    analysis,
                    callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                    *callsite,
                    callsite_args,
                    synthetic_targets,
                )?
                else {
                    return Ok(None);
                };
                call_edges.insert(*callsite, edge);
            }
            LoweredTail::ClosureCall { callsite, .. } => {
                if let Some(edge) = materialize_closure_call_edge(
                    world,
                    root_id,
                    executable,
                    analysis,
                    callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                    *callsite,
                    callsite_args,
                )? {
                    call_edges.insert(*callsite, edge);
                }
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Halt { .. } => {}
        }
    }
    Ok(Some(call_edges))
}

fn materialize_direct_call_edge(
    world: &mut World<'_>,
    root_id: RootId,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    need: ExecutableNeed,
    callsite: CallSiteId,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
    synthetic_targets: &HashMap<CallSiteId, SyntheticCallTarget>,
) -> Result<Option<MaterializedCallEdge>, FatalError> {
    let target = if let Some(target) = synthetic_targets.get(&callsite) {
        call_target_summary(
            SelectedCallee::Function(target.function),
            target.surface_inputs.clone(),
            Some(target.activation.clone()),
            target.return_ty,
        )
    } else {
        let key = CallSiteKey {
            activation: executable.activation.clone(),
            callsite,
        };
        if !world.has_fact(&FactKey::CallSiteSummary(key.clone())) {
            return Ok(None);
        }
        let Some(summary) = world.callsite_summary(&key).cloned() else {
            return Ok(None);
        };
        let Some(target) = summary.single_target().cloned() else {
            return Err(incomplete_semantic_plan(
                world,
                root_id,
                format!(
                    "materialization reached unresolved multi-target direct callsite {} without a dispatch rewrite",
                    callsite.as_u32()
                ),
            ));
        };
        target
    };
    lower_materialized_call_target(world, root_id, analysis, need, callsite, callsite_args, target).map(Some)
}

fn materialize_closure_call_edge(
    world: &mut World<'_>,
    root_id: RootId,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    need: ExecutableNeed,
    callsite: CallSiteId,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<MaterializedCallEdge>, FatalError> {
    let key = CallSiteKey {
        activation: executable.activation.clone(),
        callsite,
    };
    let Some(summary) = world.callsite_summary(&key).cloned() else {
        return Ok(None);
    };
    let Some(target) = summary.single_target().cloned() else {
        return Ok(None);
    };
    lower_materialized_call_target(world, root_id, analysis, need, callsite, callsite_args, target).map(Some)
}

fn lower_materialized_call_target(
    world: &mut World<'_>,
    root_id: RootId,
    analysis: &ActivationAnalysis,
    need: ExecutableNeed,
    callsite: CallSiteId,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
    target: CallTargetSummary,
) -> Result<MaterializedCallEdge, FatalError> {
    let (callee, extern_marshals) = match target.callee {
        SelectedCallee::Function(function) => {
            let activation = target.activation.clone().ok_or_else(|| {
                incomplete_semantic_plan(
                    world,
                    root_id,
                    format!(
                        "function target {} at callsite {} is missing its settled activation",
                        function.as_u32(),
                        callsite.as_u32()
                    ),
                )
            })?;
            let callee = ExecutableKey { activation, need };
            let extern_marshals = if let LoweredBody::Extern { signature } = world.lowered_body(function) {
                let Some(args) = callsite_args.get(&callsite) else {
                    return Err(incomplete_semantic_plan(
                        world,
                        root_id,
                        format!(
                            "missing lowered call arguments for extern callsite {}",
                            callsite.as_u32()
                        ),
                    ));
                };
                Some(resolve_extern_marshals(
                    world,
                    root_id,
                    args,
                    &analysis.value_types,
                    &signature.params,
                    signature.variadic,
                )?)
            } else {
                None
            };
            (CallTarget::Local(callee), extern_marshals)
        }
        SelectedCallee::ProviderBoundary(function) => (CallTarget::ProviderBoundary(function), None),
    };
    Ok(MaterializedCallEdge {
        callee,
        return_ty: target.settled_return(world.types_mut()),
        extern_marshals,
    })
}

fn callsite_needs_for_body(body: &LoweredBody, need: ExecutableNeed) -> HashMap<CallSiteId, ExecutableNeed> {
    match body {
        LoweredBody::Extern { .. } => HashMap::new(),
        LoweredBody::Clauses { clauses, .. } => {
            let clause_ids = (0..clauses.len() as u32).collect::<Vec<_>>();
            executable_callsite_needs(body, &clause_ids, need)
        }
    }
}

fn next_callsite_id(entries: &[LoweredEntry]) -> u32 {
    entries
        .iter()
        .filter_map(|entry| match entry.tail {
            LoweredTail::DirectCall { callsite, .. } | LoweredTail::ClosureCall { callsite, .. } => {
                Some(callsite.as_u32())
            }
            _ => None,
        })
        .max()
        .map_or(0, |next| next + 1)
}

fn protocol_dispatch_entry_captures(
    entries: &[LoweredEntry],
    args: &[CallArg],
    dest: &ControlDestination,
) -> Vec<ValueId> {
    let mut seen = HashSet::new();
    let mut captures = Vec::new();
    for arg in args {
        if seen.insert(arg.value) {
            captures.push(arg.value);
        }
    }
    if let ControlDestination::Deliver(target) = dest {
        for capture in &entries[target.as_u32() as usize].captures {
            if seen.insert(*capture) {
                captures.push(*capture);
            }
        }
    }
    captures
}

fn protocol_dispatch_plan(
    world: &mut World<'_>,
    root_id: RootId,
    receiver_ty: Ty,
    targets: &[CallTargetSummary],
    span: Span,
) -> Result<PatternDispatchPlan<Ty>, FatalError> {
    let mut builder = DispatchMatrixBuilder::typed(Order::Specificity);
    let receiver = builder.add_input_subject();
    let mut outcomes = Vec::with_capacity(targets.len());
    let mut covered = world.types_mut().none();
    for (index, target) in targets.iter().enumerate() {
        let target_ty = target
            .surface_inputs
            .first()
            .copied()
            .unwrap_or_else(|| world.types_mut().any());
        covered = if world.types().is_empty(&covered) {
            target_ty
        } else {
            world.types_mut().union(covered, target_ty)
        };
        let outcome = builder.add_outcome(OutcomeMultiplicity::Unique);
        builder
            .add_arm_questions(
                vec![RegionQuestion::type_region(receiver, target_ty)],
                EdgeEvidence::empty(),
                outcome,
            )
            .map_err(|error| {
                incomplete_semantic_plan(
                    world,
                    root_id,
                    format!("protocol dispatch matrix build failed: {error:?}"),
                )
            })?;
        outcomes.push(PatternDispatchOutcome {
            outcome,
            body_id: index as u32,
            bindings: Vec::new(),
            span,
        });
    }
    let fallback =
        (!world.types().is_subtype(&receiver_ty, &covered)).then_some(builder.add_outcome(OutcomeMultiplicity::Unique));
    let matrix = builder.build().map_err(|error| {
        incomplete_semantic_plan(
            world,
            root_id,
            format!("protocol dispatch matrix build failed: {error:?}"),
        )
    })?;
    let options = fallback
        .map(DispatchCompileOptions::open)
        .unwrap_or_else(DispatchCompileOptions::closed);
    let graph = compile_dispatch_matrix_with_type_order(
        world.types_mut(),
        &matrix,
        options,
        EqualTypeRegionPolicy::DuplicateCoverage,
    )
    .map_err(|error| {
        incomplete_semantic_plan(
            world,
            root_id,
            format!("protocol dispatch graph compile failed: {error:?}"),
        )
    })?;
    let mut subjects = vec![None; matrix.subjects.len()];
    subjects[receiver.0 as usize] = Some(PatternSubjectRef::Input(0));
    Ok(PatternDispatchPlan {
        matrix,
        graph: graph.graph,
        input_count: 1,
        subjects,
        outcomes,
        guards: Vec::new(),
        pinned: Vec::new(),
        prepared_keys: Vec::new(),
        bitstring_direct_bindings: HashMap::new(),
    })
}

fn call_target_summary(
    callee: SelectedCallee,
    surface_inputs: Vec<Ty>,
    activation: Option<ActivationKey>,
    return_ty: Ty,
) -> CallTargetSummary {
    CallTargetSummary {
        callee,
        surface_inputs,
        activation,
        return_ty: Some(return_ty),
    }
}

fn materialize_entry_dispatch(
    world: &World<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
) -> Option<ExecutableDispatch> {
    match world.lowered_body(executable.activation.function) {
        LoweredBody::Extern { .. } => None,
        LoweredBody::Clauses { .. } => Some(ExecutableDispatch::new(
            world.entry_dispatch(executable.activation.function),
            analysis.reachable_clauses.clone(),
        )),
    }
}

fn prune_lowered_body(
    body: LoweredBody,
    reachable_clauses: &[u32],
    reachable_entries: &[ControlEntryId],
) -> PrunedLoweredBody {
    match body {
        LoweredBody::Extern { .. } => PrunedLoweredBody {
            body,
            original_entry_ids: Vec::new(),
        },
        LoweredBody::Clauses {
            clauses,
            entries,
            generated,
        } => {
            let reachable_entries = reachable_entries.iter().copied().collect::<HashSet<_>>();
            let mut clauses = reachable_clauses
                .iter()
                .map(|clause_id| clauses[*clause_id as usize].clone())
                .collect::<Vec<_>>();
            let mut needed = HashMap::new();
            let mut kept_ids = Vec::new();
            for clause in &clauses {
                collect_reachable_entries(&entries, clause.entry, &reachable_entries, &mut kept_ids, &mut needed);
            }
            let mut kept = kept_ids
                .iter()
                .map(|entry_id| {
                    specialize_entry(
                        entries[entry_id.as_u32() as usize].clone(),
                        reachable_entries.contains(entry_id),
                    )
                })
                .collect::<Vec<_>>();
            reindex_entries(&mut clauses, &mut kept, &needed);
            PrunedLoweredBody {
                body: LoweredBody::Clauses {
                    clauses,
                    entries: kept,
                    generated,
                },
                original_entry_ids: kept_ids,
            }
        }
    }
}

fn collect_reachable_entries(
    entries: &[LoweredEntry],
    entry_id: super::super::body::ControlEntryId,
    reachable_entries: &HashSet<super::super::body::ControlEntryId>,
    order: &mut Vec<super::super::body::ControlEntryId>,
    out: &mut HashMap<super::super::body::ControlEntryId, super::super::body::ControlEntryId>,
) {
    if out.contains_key(&entry_id) {
        return;
    }
    let next_id = super::super::body::ControlEntryId::from_u32(order.len() as u32);
    order.push(entry_id);
    out.insert(entry_id, next_id);
    if !reachable_entries.contains(&entry_id) {
        return;
    }
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        LoweredTail::Value { dest, .. }
        | LoweredTail::DirectCall { dest, .. }
        | LoweredTail::ClosureCall { dest, .. } => {
            if let super::super::body::ControlDestination::Deliver(target) = dest {
                collect_reachable_entries(entries, *target, reachable_entries, order, out);
            }
        }
        LoweredTail::If {
            then_entry, else_entry, ..
        } => {
            collect_reachable_entries(entries, *then_entry, reachable_entries, order, out);
            collect_reachable_entries(entries, *else_entry, reachable_entries, order, out);
        }
        LoweredTail::Dispatch { dispatch, .. } => {
            for arm_entry in &dispatch.arm_entries {
                collect_reachable_entries(entries, *arm_entry, reachable_entries, order, out);
            }
            collect_reachable_entries(entries, dispatch.miss_entry, reachable_entries, order, out);
        }
        LoweredTail::Receive(receive) => {
            if let super::super::body::ControlDestination::Deliver(target) = &receive.dest {
                collect_reachable_entries(entries, *target, reachable_entries, order, out);
            }
            for clause in &receive.clauses {
                collect_reachable_entries(entries, clause.entry, reachable_entries, order, out);
            }
            if let Some(after) = &receive.after {
                collect_reachable_entries(entries, after.entry, reachable_entries, order, out);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
}

fn specialize_entry(mut entry: LoweredEntry, is_reachable: bool) -> LoweredEntry {
    if is_reachable {
        return entry;
    }
    entry.steps.clear();
    entry.tail = LoweredTail::Halt {
        atom: UNREACHABLE_CONTROL_ATOM.to_string(),
    };
    entry
}

fn reindex_entries(
    clauses: &mut [super::super::body::LoweredClause],
    entries: &mut [LoweredEntry],
    ids: &HashMap<super::super::body::ControlEntryId, super::super::body::ControlEntryId>,
) {
    for clause in clauses {
        clause.entry = ids[&clause.entry];
    }
    for entry in entries {
        match &mut entry.tail {
            LoweredTail::Value { dest, .. }
            | LoweredTail::DirectCall { dest, .. }
            | LoweredTail::ClosureCall { dest, .. } => {
                if let super::super::body::ControlDestination::Deliver(target) = dest {
                    *target = ids[target];
                }
            }
            LoweredTail::If {
                then_entry, else_entry, ..
            } => {
                *then_entry = ids[then_entry];
                *else_entry = ids[else_entry];
            }
            LoweredTail::Dispatch { dispatch, .. } => {
                for arm_entry in &mut dispatch.arm_entries {
                    *arm_entry = ids[arm_entry];
                }
                dispatch.miss_entry = ids[&dispatch.miss_entry];
            }
            LoweredTail::Receive(receive) => {
                if let super::super::body::ControlDestination::Deliver(target) = &mut receive.dest {
                    *target = ids[target];
                }
                for clause in &mut receive.clauses {
                    clause.entry = ids[&clause.entry];
                }
                if let Some(after) = &mut receive.after {
                    after.entry = ids[&after.entry];
                }
            }
            LoweredTail::Halt { .. } => {}
        }
    }
}

fn collect_callsite_args(body: &LoweredBody) -> HashMap<CallSiteId, Vec<CallArg>> {
    let mut out = HashMap::new();
    match body {
        LoweredBody::Extern { .. } => {}
        LoweredBody::Clauses { clauses, entries, .. } => {
            for clause in clauses {
                collect_step_call_args(&clause.projections, &mut out);
            }
            for entry in entries {
                collect_step_call_args(&entry.steps, &mut out);
                collect_tail_call_args(&entry.tail, &mut out);
            }
        }
    }
    out
}

fn collect_step_call_args(_steps: &[LoweredStep], _out: &mut HashMap<CallSiteId, Vec<CallArg>>) {}

fn collect_tail_call_args(tail: &LoweredTail, out: &mut HashMap<CallSiteId, Vec<CallArg>>) {
    match tail {
        LoweredTail::DirectCall { callsite, args, .. } | LoweredTail::ClosureCall { callsite, args, .. } => {
            out.insert(*callsite, args.clone());
        }
        LoweredTail::Value { .. }
        | LoweredTail::If { .. }
        | LoweredTail::Dispatch { .. }
        | LoweredTail::Receive(_)
        | LoweredTail::Halt { .. } => {}
    }
}

fn resolve_extern_marshals(
    world: &mut World<'_>,
    root_id: RootId,
    args: &[CallArg],
    value_types: &HashMap<super::super::body::ValueId, Ty>,
    fixed_params: &[crate::fz_ir::ExternTy],
    variadic: bool,
) -> Result<Vec<crate::fz_ir::ExternTy>, FatalError> {
    let fixed = fixed_params.len();
    let actual = args.len();
    if (!variadic && actual != fixed) || (variadic && actual < fixed) {
        return Err(incomplete_semantic_plan(
            world,
            root_id,
            format!("extern call expected {} argument(s) but saw {}", fixed, actual),
        ));
    }

    let mut marshals = Vec::with_capacity(actual);
    for (index, arg) in args.iter().enumerate() {
        if index < fixed {
            let expected = fixed_params[index];
            if let Some(ascription) = &arg.ascription {
                let ascribed = parse_extern_ascription(world, root_id, ascription)?;
                if ascribed != expected {
                    return Err(incomplete_semantic_plan(
                        world,
                        root_id,
                        format!(
                            "extern fixed arg {} ascribed as {:?}, declared as {:?}",
                            index + 1,
                            ascribed,
                            expected
                        ),
                    ));
                }
            }
            marshals.push(expected);
            continue;
        }

        if let Some(ascription) = &arg.ascription {
            marshals.push(parse_extern_ascription(world, root_id, ascription)?);
            continue;
        }

        let Some(arg_ty) = value_types.get(&arg.value).copied() else {
            return Err(incomplete_semantic_plan(
                world,
                root_id,
                format!("missing settled type for extern argument value {}", arg.value.as_u32()),
            ));
        };
        marshals.push(resolve_auto_variadic_marshal(world, root_id, arg_ty)?);
    }

    Ok(marshals)
}

fn parse_extern_ascription(
    world: &World<'_>,
    root_id: RootId,
    body: &crate::ast::TypeExprBody,
) -> Result<crate::fz_ir::ExternTy, FatalError> {
    let Some(tok) = body.0.first().map(|token| &token.tok) else {
        return Err(incomplete_semantic_plan(
            world,
            root_id,
            "empty extern call-arg ascription",
        ));
    };
    let name = match tok {
        Tok::Ident(name) | Tok::Upper(name) => name.as_str(),
        Tok::Nil => "nil",
        _ => {
            return Err(incomplete_semantic_plan(
                world,
                root_id,
                format!("unsupported extern call-arg ascription token {:?}", tok),
            ));
        }
    };
    extern_ty_from_name(name)
        .ok_or_else(|| incomplete_semantic_plan(world, root_id, format!("unknown extern call-arg ascription `{name}`")))
}

fn resolve_auto_variadic_marshal(
    world: &mut World<'_>,
    root_id: RootId,
    arg_ty: Ty,
) -> Result<crate::fz_ir::ExternTy, FatalError> {
    if world.types().is_integer(&arg_ty) {
        return Ok(crate::fz_ir::ExternTy::I64);
    }
    if world.types().is_floating(&arg_ty) {
        return Ok(crate::fz_ir::ExternTy::F64);
    }
    let str_ty = world.types_mut().str_t();
    if world.types().is_subtype(&arg_ty, &str_ty) {
        return Err(incomplete_semantic_plan(
            world,
            root_id,
            "binary values need an explicit extern variadic marshal ascription",
        ));
    }
    Err(incomplete_semantic_plan(
        world,
        root_id,
        "no default extern variadic marshal class for this argument",
    ))
}

fn local_effects(body: &LoweredBody, call_edges: &HashMap<CallSiteId, MaterializedCallEdge>) -> EffectSummary {
    match body {
        LoweredBody::Extern { signature } => EffectSummary {
            reads_allocation_stats: signature.symbol == "fz_process_heap_alloc_stats",
            scheduler_visible: matches!(signature.symbol.as_str(), "fz_send" | "fz_spawn" | "fz_spawn_opt"),
            observable: true,
            halts: signature.ret == crate::fz_ir::ExternTy::Never,
            ..EffectSummary::default()
        },
        LoweredBody::Clauses { clauses, entries, .. } => {
            let mut effects = EffectSummary::default();
            for clause in clauses {
                effects.union_with(step_effects(&clause.projections, call_edges));
            }
            for entry in entries {
                effects.union_with(step_effects(&entry.steps, call_edges));
                effects.union_with(tail_effects(&entry.tail, call_edges));
            }
            effects
        }
    }
}

fn step_effects(steps: &[LoweredStep], _call_edges: &HashMap<CallSiteId, MaterializedCallEdge>) -> EffectSummary {
    let mut effects = EffectSummary::default();
    for step in steps {
        match step {
            LoweredStep::Tuple { .. }
            | LoweredStep::List { .. }
            | LoweredStep::Map { .. }
            | LoweredStep::MapUpdate { .. }
            | LoweredStep::Struct { .. }
            | LoweredStep::Bitstring { .. }
            | LoweredStep::Lambda { .. } => {
                effects.allocates = true;
            }
            _ => {}
        }
    }
    effects
}

fn tail_effects(tail: &LoweredTail, call_edges: &HashMap<CallSiteId, MaterializedCallEdge>) -> EffectSummary {
    let mut effects = EffectSummary::default();
    match tail {
        LoweredTail::ClosureCall { callsite, .. } if !call_edges.contains_key(callsite) => {
            effects.calls_opaque = true;
        }
        LoweredTail::DirectCall { callsite, .. } => {
            if matches!(
                call_edges.get(callsite).map(|edge| &edge.callee),
                Some(CallTarget::ProviderBoundary(_))
            ) {
                effects.calls_opaque = true;
            }
        }
        LoweredTail::Value { .. }
        | LoweredTail::If { .. }
        | LoweredTail::Dispatch { .. }
        | LoweredTail::Receive(_)
        | LoweredTail::Halt { .. } => {}
        LoweredTail::ClosureCall { .. } => {}
    }
    effects
}

fn settle_effects(
    world: &World<'_>,
    root_id: RootId,
    executables: &mut HashMap<ExecutableKey, MaterializedExecutable>,
) -> Result<(), FatalError> {
    loop {
        let snapshot = executables
            .iter()
            .map(|(key, executable)| (key.clone(), executable.effects))
            .collect::<HashMap<_, _>>();
        let mut changed = false;
        for (caller_key, executable) in executables.iter_mut() {
            let mut settled = local_effects(&executable.body, &executable.call_edges);
            for edge in executable.call_edges.values() {
                let Some(callee) = edge.callee.local() else {
                    continue;
                };
                let Some(callee_effects) = snapshot.get(callee).copied() else {
                    return Err(incomplete_semantic_plan(
                        world,
                        root_id,
                        format!(
                            "materialized call edge {:?} -> {:?} points outside the closed executable frontier",
                            caller_key, edge.callee
                        ),
                    ));
                };
                settled.union_with(callee_effects);
            }
            if executable.effects != settled {
                executable.effects = settled;
                changed = true;
            }
        }
        if !changed {
            return Ok(());
        }
    }
}

fn build_executable_abi_plan(
    world: &mut World<'_>,
    _key: &ExecutableKey,
    executable: &MaterializedExecutable,
    transport_plan: &TransportPlan,
) -> ExecutableAbiPlan {
    let param_reprs = executable
        .transport
        .input_positions
        .iter()
        .flat_map(|position| {
            let TransportPosition::ExecutableInput {
                executable: symbol,
                semantic_index,
            } = position
            else {
                return Vec::new();
            };
            let shape = *transport_plan
                .positions
                .get(position)
                .unwrap_or_else(|| panic!("transport plan should publish materialized input position {position:?}"));
            shape_leaf_lanes_for_artifact(world, shape)
                .into_iter()
                .map(|(leaf_shape, lane)| {
                    seam_repr_for_lane(
                        &transport_plan.codegen_seam_facts,
                        |seam| {
                            matches!(
                                seam,
                                CodegenSeam::FunctionEntry {
                                    executable,
                                    semantic_index: index
                                } if executable == symbol && index == semantic_index
                            )
                        },
                        Some(leaf_shape),
                        lane,
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut value_reprs = HashMap::new();
    if let LoweredBody::Clauses { clauses, entries, .. } = &executable.body {
        for clause in clauses {
            for (index, value) in clause.params.iter().copied().enumerate() {
                let Some(position) = executable.transport.input_positions.iter().find(|position| {
                    matches!(
                        position,
                        TransportPosition::ExecutableInput {
                            semantic_index,
                            ..
                        } if *semantic_index == index
                    )
                }) else {
                    continue;
                };
                let shape = *transport_plan.positions.get(position).unwrap_or_else(|| {
                    panic!("transport plan should publish materialized input position {position:?}")
                });
                let leaf_lanes = shape_leaf_lanes_for_artifact(world, shape);
                if let [(leaf_shape, lane)] = leaf_lanes.as_slice() {
                    let TransportPosition::ExecutableInput {
                        executable: symbol,
                        semantic_index,
                    } = position
                    else {
                        continue;
                    };
                    let repr = seam_repr_for_lane(
                        &transport_plan.codegen_seam_facts,
                        |seam| {
                            matches!(
                                seam,
                                CodegenSeam::FunctionEntry {
                                    executable,
                                    semantic_index: index
                                } if executable == symbol && index == semantic_index
                            )
                        },
                        Some(*leaf_shape),
                        *lane,
                    );
                    value_reprs.insert(value, repr);
                }
            }
        }
        for clause in clauses {
            record_step_reprs(world, executable, &clause.projections, &mut value_reprs);
        }
        for entry in entries {
            record_step_reprs(world, executable, &entry.steps, &mut value_reprs);
        }
    }

    ExecutableAbiPlan {
        param_reprs,
        value_reprs,
    }
}

fn derive_abi_ready_executable(
    executable: &MaterializedExecutable,
    plan: &ExecutableAbiPlan,
) -> Result<AbiReadyExecutable, FatalError> {
    let call_edges = executable
        .call_edges
        .iter()
        .map(|(callsite, edge)| {
            (
                *callsite,
                AbiReadyCallEdge {
                    callee: edge.callee.clone(),
                    return_ty: edge.return_ty,
                    extern_marshals: edge.extern_marshals.clone(),
                },
            )
        })
        .collect::<HashMap<_, _>>();
    Ok(AbiReadyExecutable {
        entry_dispatch: executable.entry_dispatch.clone(),
        return_ty: executable.return_ty,
        param_reprs: plan.param_reprs.clone(),
        runtime_demand: executable.runtime_demand.clone(),
        transport: executable.transport.clone(),
        original_entry_ids: executable.original_entry_ids.clone(),
        value_types: executable.value_types.clone(),
        value_reprs: plan.value_reprs.clone(),
        effects: executable.effects,
        body: executable.body.clone(),
        call_edges,
    })
}

fn shape_leaf_lanes_for_artifact(world: &World<'_>, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
    match world.transport().interners().shape(shape) {
        ShapeDescr::Nothing => Vec::new(),
        ShapeDescr::Lane(lane) => vec![(shape, *lane)],
        ShapeDescr::Tuple(items) => items
            .iter()
            .copied()
            .flat_map(|item| shape_leaf_lanes_for_artifact(world, item))
            .collect(),
        ShapeDescr::Callable(callable) => world
            .transport()
            .interners()
            .callable(*callable)
            .capture_lanes
            .iter()
            .copied()
            .map(|lane| (shape, lane))
            .collect(),
    }
}

fn seam_repr_for_lane(
    facts: &[super::super::transport::CodegenSeamFact],
    seam_matches: impl Fn(&CodegenSeam) -> bool,
    shape: Option<ShapeId>,
    lane: LaneId,
) -> AbiValueRepr {
    let fact = facts
        .iter()
        .find(|fact| seam_matches(&fact.seam) && fact.shape == shape && fact.lane == lane)
        .unwrap_or_else(|| panic!("transport plan should publish a codegen seam fact for {shape:?} {lane:?}"));
    abi_repr_from_codegen(fact.repr)
}

fn abi_repr_from_codegen(repr: CodegenLaneRepr) -> AbiValueRepr {
    match repr {
        CodegenLaneRepr::ValueRef => AbiValueRepr::ValueRef,
        CodegenLaneRepr::RawInt => AbiValueRepr::RawInt,
        CodegenLaneRepr::RawF64 => AbiValueRepr::RawF64,
        CodegenLaneRepr::RawAtom => AbiValueRepr::RawAtom,
    }
}

fn record_step_reprs(
    world: &mut World<'_>,
    executable: &MaterializedExecutable,
    steps: &[LoweredStep],
    value_reprs: &mut HashMap<ValueId, AbiValueRepr>,
) {
    for step in steps {
        match step {
            LoweredStep::Const { value, literal } => {
                value_reprs.insert(*value, literal_repr(literal));
            }
            LoweredStep::Tuple { value, .. }
            | LoweredStep::List { value, .. }
            | LoweredStep::Map { value, .. }
            | LoweredStep::MapUpdate { value, .. }
            | LoweredStep::Struct { value, .. }
            | LoweredStep::Bitstring { value, .. }
            | LoweredStep::FunctionRef { value, .. }
            | LoweredStep::Lambda { value, .. }
            | LoweredStep::MapIndex { value, .. }
            | LoweredStep::FieldAccess { value, .. }
            | LoweredStep::RequireMapValue { value, .. }
            | LoweredStep::TupleField { value, .. }
            | LoweredStep::BitstringInit { reader: value, .. } => {
                value_reprs.insert(*value, AbiValueRepr::ValueRef);
            }
            LoweredStep::BinaryOp { value, .. } | LoweredStep::UnaryOp { value, .. } => {
                let ty = executable
                    .value_types
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| world.types_mut().any());
                value_reprs.insert(*value, abi_value_repr(world, ty));
            }
            LoweredStep::SplitList { head, tail, .. } => {
                value_reprs.insert(*head, AbiValueRepr::ValueRef);
                value_reprs.insert(*tail, AbiValueRepr::ValueRef);
            }
            LoweredStep::BitstringRead {
                ok, value, next_reader, ..
            } => {
                value_reprs.insert(*ok, AbiValueRepr::ValueRef);
                value_reprs.insert(*value, AbiValueRepr::ValueRef);
                value_reprs.insert(*next_reader, AbiValueRepr::ValueRef);
            }
            LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertStruct { .. }
            | LoweredStep::AssertTuple { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::AssertSame { .. }
            | LoweredStep::AssertBitstringDone { .. } => {}
        }
    }
}

fn literal_repr(literal: &Literal) -> AbiValueRepr {
    match literal {
        Literal::Int(_) => AbiValueRepr::RawInt,
        Literal::Float(_) => AbiValueRepr::RawF64,
        Literal::Atom(_) | Literal::Bool(_) | Literal::Nil => AbiValueRepr::RawAtom,
        Literal::Binary(_) => AbiValueRepr::ValueRef,
    }
}

fn derive_emission_ready_executable(
    world: &World<'_>,
    root_id: RootId,
    abi_ready: &AbiReadyProgram,
    executable_index: &HashMap<ExecutableKey, usize>,
    key: ExecutableKey,
) -> Result<EmissionReadyExecutable, FatalError> {
    let executable = abi_ready
        .executables
        .get(&key)
        .expect("sorted executable keys should resolve in the ABI-ready program");
    let mut call_edges = executable
        .call_edges
        .iter()
        .map(|(callsite, edge)| {
            Ok(EmissionReadyCallEdge {
                callsite: *callsite,
                callee: match &edge.callee {
                    CallTarget::Local(callee) => {
                        CallTarget::Local(executable_index.get(callee).copied().ok_or_else(|| {
                            incomplete_semantic_plan(
                                world,
                                root_id,
                                format!(
                                    "ABI-ready call edge {:?} -> {:?} points outside the executable inventory",
                                    key, callee
                                ),
                            )
                        })?)
                    }
                    CallTarget::ProviderBoundary(function) => CallTarget::ProviderBoundary(*function),
                },
                extern_marshals: edge.extern_marshals.clone(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    call_edges.sort_by_key(|edge| edge.callsite.as_u32());
    Ok(EmissionReadyExecutable {
        key,
        entry_dispatch: executable.entry_dispatch.clone(),
        return_ty: executable.return_ty,
        param_reprs: executable.param_reprs.clone(),
        runtime_demand: executable.runtime_demand.clone(),
        transport: executable.transport.clone(),
        original_entry_ids: executable.original_entry_ids.clone(),
        value_types: executable.value_types.clone(),
        value_reprs: executable.value_reprs.clone(),
        effects: executable.effects,
        body: executable.body.clone(),
        call_edges,
    })
}

fn derive_callable_entries(
    world: &mut World<'_>,
    root_id: RootId,
    materialized: &MaterializedProgram,
    executables: &HashMap<ExecutableKey, AbiReadyExecutable>,
) -> Result<Vec<CallableEntry>, FatalError> {
    let mut entries = Vec::new();
    let transport_plan = world
        .transport()
        .plans()
        .get(root_id)
        .expect("ABI-ready callable inventory should read the settled transport plan");
    for boundary in &materialized.transport.boundary_ids {
        let boundary_descr = world.transport().interners().boundary(*boundary);
        let callable_descr = world.transport().interners().callable(boundary_descr.callable);
        let callable_facts = transport_plan
            .callables
            .get(&boundary_descr.callable)
            .unwrap_or_else(|| {
                panic!(
                    "transport plan should publish callable facts for {:?}",
                    boundary_descr.callable
                )
            });
        let capture_count = callable_descr.capture_shapes.len();
        let capture_reprs = boundary_lanes_reprs_from_transport(
            &materialized.transport.codegen_seam_facts,
            *boundary,
            boundary_descr.published_capture_lanes.as_ref(),
        );
        let arg_reprs = boundary_lanes_reprs_from_transport(
            &materialized.transport.codegen_seam_facts,
            *boundary,
            boundary_descr.published_arg_lanes.as_ref(),
        );
        for target_symbol in callable_facts.resolutions.iter() {
            let target = executable_key_for_symbol(materialized, target_symbol).ok_or_else(|| {
                incomplete_semantic_plan(
                    world,
                    root_id,
                    format!("transport callable boundary target is missing from artifact inventory: {target_symbol:?}"),
                )
            })?;
            let target_executable = executables.get(&target).ok_or_else(|| {
                incomplete_semantic_plan(
                    world,
                    root_id,
                    format!("transport callable boundary target is missing from ABI-ready inventory: {target:?}"),
                )
            })?;
            entries.push(CallableEntry {
                boundary: *boundary,
                target,
                capture_count,
                capture_reprs: capture_reprs.clone(),
                arg_reprs: arg_reprs.clone(),
                return_ty: target_executable.return_ty,
                return_shape: boundary_descr.published_return_shape,
                return_lanes: boundary_descr.published_return_lanes.to_vec(),
            });
        }
    }
    entries.sort_by(compare_callable_entries);
    entries.dedup();
    Ok(entries)
}

fn executable_key_for_symbol(materialized: &MaterializedProgram, symbol: &ExecutableSymbol) -> Option<ExecutableKey> {
    materialized
        .executables
        .keys()
        .find(|key| {
            key.need == symbol.need
                && key.activation.function == symbol.activation.function
                && key.activation.input.as_slice() == symbol.activation.input.as_ref()
        })
        .cloned()
}

fn boundary_lanes_reprs_from_transport(
    facts: &[super::super::transport::CodegenSeamFact],
    boundary: super::super::transport::BoundaryId,
    lanes: &[LaneId],
) -> Vec<AbiValueRepr> {
    lanes
        .iter()
        .copied()
        .map(|lane| {
            seam_repr_for_lane(
                facts,
                |seam| matches!(seam, CodegenSeam::CallableBoundary { boundary: candidate } if *candidate == boundary),
                None,
                lane,
            )
        })
        .collect()
}

fn compare_callable_entries(left: &CallableEntry, right: &CallableEntry) -> std::cmp::Ordering {
    left.boundary
        .as_u32()
        .cmp(&right.boundary.as_u32())
        .then_with(|| {
            left.target
                .activation
                .function
                .as_u32()
                .cmp(&right.target.activation.function.as_u32())
        })
        .then_with(|| left.capture_count.cmp(&right.capture_count))
        .then_with(|| left.target.activation.input.cmp(&right.target.activation.input))
        .then_with(|| left.capture_reprs.cmp(&right.capture_reprs))
        .then_with(|| left.arg_reprs.cmp(&right.arg_reprs))
        .then_with(|| left.return_ty.cmp(&right.return_ty))
        .then_with(|| left.return_shape.cmp(&right.return_shape))
        .then_with(|| left.return_lanes.cmp(&right.return_lanes))
}

fn compare_executable_keys(left: &ExecutableKey, right: &ExecutableKey) -> std::cmp::Ordering {
    left.activation
        .root
        .as_u32()
        .cmp(&right.activation.root.as_u32())
        .then_with(|| {
            left.activation
                .function
                .as_u32()
                .cmp(&right.activation.function.as_u32())
        })
        .then_with(|| left.activation.input.cmp(&right.activation.input))
        .then_with(|| compare_executable_needs(left.need, right.need))
}

fn compare_executable_needs(left: ExecutableNeed, right: ExecutableNeed) -> std::cmp::Ordering {
    match (left, right) {
        (ExecutableNeed::Value, ExecutableNeed::Value) => std::cmp::Ordering::Equal,
        (ExecutableNeed::Value, ExecutableNeed::TupleFields(_)) => std::cmp::Ordering::Less,
        (ExecutableNeed::TupleFields(_), ExecutableNeed::Value) => std::cmp::Ordering::Greater,
        (ExecutableNeed::TupleFields(left), ExecutableNeed::TupleFields(right)) => left.cmp(&right),
    }
}

fn compare_emission_callable_entries(
    left: &EmissionReadyCallableEntry,
    right: &EmissionReadyCallableEntry,
) -> std::cmp::Ordering {
    left.target
        .cmp(&right.target)
        .then_with(|| left.boundary.as_u32().cmp(&right.boundary.as_u32()))
        .then_with(|| left.capture_count.cmp(&right.capture_count))
}

fn abi_value_repr(world: &mut World<'_>, ty: Ty) -> AbiValueRepr {
    if world.types().is_floating(&ty) {
        return AbiValueRepr::RawF64;
    }
    if world.types().is_integer(&ty) {
        return AbiValueRepr::RawInt;
    }
    let atom = world.types_mut().atom();
    if world.types().is_subtype(&ty, &atom) {
        AbiValueRepr::RawAtom
    } else {
        AbiValueRepr::ValueRef
    }
}

fn incomplete_semantic_plan(world: &World<'_>, root_id: RootId, message: impl Into<String>) -> FatalError {
    let message = message.into();
    let diagnostic = Diagnostic::error(
        codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN,
        format!("compiler2 materialization for root {}: {}", root_id.as_u32(), message),
        Span::DUMMY,
    );
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    FatalError
}
