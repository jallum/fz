//! Compiler2 artifact projection jobs.
//!
//! This module turns a closed semantic root into backend-owned artifact
//! projections. Each rung is derived from the one below it and never reopens
//! semantic discovery.

use std::collections::{HashMap, HashSet};

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::extern_contract::extern_ty_from_name;
use crate::parser::lexer::Tok;
use crate::source::Span;

use super::super::artifact::{
    AbiReadyCallEdge, AbiReadyExecutable, AbiReadyProgram, AbiValueRepr, CallEdge, CallReturnFlow, CallTarget,
    CallableEntry, DirectCallEdge, DispatchCallArm, DispatchCallEdge, DispatchCallMiss, EffectSummary,
    EmissionReadyCallEdge, EmissionReadyCallableEntry, EmissionReadyExecutable, EmissionReadyProgram,
    ExecutableDispatch, MaterializedCallEdge, MaterializedExecutable, MaterializedExecutableTransport,
    MaterializedProgram, MaterializedTransportPlan,
};
use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryId, Literal, LoweredBody, LoweredEntry, LoweredStep,
    LoweredTail, ValueId,
};
use super::super::drive::{FactKey, Job, JobEffects, settled_uses};
use super::super::identity::{ExecutableKey, ExecutableNeed, RootId};
use super::super::scheduler::FatalError;
use super::super::semantic::{ActivationAnalysis, CallSiteKey, CallTargetSummary, SelectedCallee};
use super::super::transport::{
    ActivationSymbol, CodegenLaneRepr, CodegenSeam, ExecutableSymbol, LaneId, ShapeDescr, ShapeId, TransportPlan,
    TransportPosition,
};
use super::super::types::{Ty, Types};
use super::super::world::World;
use super::semantic::executable_callsite_needs;

const UNREACHABLE_CONTROL_ATOM: &str = "compiler2_unreachable_control";

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
        .transport_plan(root_id)
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
        let body = pruned.body;
        let callsite_args = collect_callsite_args(&body);
        let Some(call_edges) = materialize_call_edges(
            world,
            root_id,
            &transport_plan,
            executable,
            &analysis,
            &body,
            &callsite_args,
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
                transport: materialized_executable_transport(&transport_plan, executable, world.types()),
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
        .transport_plan(root_id)
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
    let mut publication_boundaries = plan
        .boundaries
        .iter()
        .flat_map(|(boundary, facts)| facts.publications.iter().cloned().map(|position| (position, *boundary)))
        .collect::<Vec<_>>();
    publication_boundaries.sort_by(|left, right| {
        transport_position_sort_key(&left.0)
            .cmp(&transport_position_sort_key(&right.0))
            .then_with(|| left.1.as_u32().cmp(&right.1.as_u32()))
    });
    MaterializedTransportPlan {
        entry: plan.entry.clone(),
        executable_membership: plan.executable_membership.clone(),
        position_shapes,
        callable_ids,
        boundary_ids,
        publication_boundaries,
        codegen_seam_facts: plan.codegen_seam_facts.clone(),
    }
}

fn materialized_executable_transport(
    plan: &TransportPlan,
    executable: &ExecutableKey,
    types: &Types,
) -> MaterializedExecutableTransport {
    let symbol = transport_executable_symbol(executable, types);
    let mut input_positions = Vec::new();
    let mut return_position = None;
    let mut resume_positions = Vec::new();
    let mut return_payload_positions = Vec::new();
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
            TransportPosition::ReturnPayload { .. } => return_payload_positions.push(position.clone()),
            TransportPosition::EntryCapture { .. } => entry_capture_positions.push(position.clone()),
            TransportPosition::CallArg { .. } => call_arg_positions.push(position.clone()),
            TransportPosition::Value { .. } => value_positions.push(position.clone()),
        }
    }
    sort_transport_positions(&mut input_positions);
    sort_transport_positions(&mut resume_positions);
    sort_transport_positions(&mut return_payload_positions);
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
        return_payload_positions,
        entry_capture_positions,
        call_arg_positions,
        value_positions,
    }
}

fn transport_executable_symbol(executable: &ExecutableKey, types: &Types) -> ExecutableSymbol {
    ExecutableSymbol {
        activation: ActivationSymbol {
            function: executable.activation.function,
            input: executable.activation.inputs(types).into_boxed_slice(),
        },
        need: executable.need,
    }
}

fn transport_position_executable(position: &TransportPosition) -> &ExecutableSymbol {
    match position {
        TransportPosition::ExecutableInput { executable, .. }
        | TransportPosition::ExecutableReturn { executable }
        | TransportPosition::ResumePayload { executable, .. }
        | TransportPosition::ReturnPayload { executable, .. }
        | TransportPosition::CallArg { executable, .. }
        | TransportPosition::EntryCapture { executable, .. }
        | TransportPosition::Value { executable, .. } => executable,
    }
}

fn sort_transport_positions(positions: &mut [TransportPosition]) {
    positions.sort_by_key(transport_position_sort_key);
}

type TransportExecutableSortKey = (u32, Vec<Ty>, u8, usize);
type TransportPositionSortKey = (u8, TransportExecutableSortKey, u32, u32, usize);

fn transport_position_sort_key(position: &TransportPosition) -> TransportPositionSortKey {
    match position {
        TransportPosition::ExecutableInput {
            executable,
            semantic_index,
        } => (0, transport_executable_sort_key(executable), 0, 0, *semantic_index),
        TransportPosition::ExecutableReturn { executable } => (1, transport_executable_sort_key(executable), 0, 0, 0),
        TransportPosition::ResumePayload {
            executable,
            callsite,
            entry,
        } => (
            2,
            transport_executable_sort_key(executable),
            callsite.map(|callsite| callsite.as_u32()).unwrap_or(u32::MAX),
            entry.as_u32(),
            0,
        ),
        TransportPosition::ReturnPayload { executable, callsite } => {
            (3, transport_executable_sort_key(executable), callsite.as_u32(), 0, 0)
        }
        TransportPosition::EntryCapture {
            executable,
            entry,
            capture_index,
        } => (
            4,
            transport_executable_sort_key(executable),
            0,
            entry.as_u32(),
            *capture_index,
        ),
        TransportPosition::CallArg {
            executable,
            callsite,
            semantic_index,
        } => (
            5,
            transport_executable_sort_key(executable),
            callsite.as_u32(),
            0,
            *semantic_index,
        ),
        TransportPosition::Value { executable, value } => {
            (6, transport_executable_sort_key(executable), value.as_u32(), 0, 0)
        }
    }
}

fn transport_executable_sort_key(executable: &ExecutableSymbol) -> TransportExecutableSortKey {
    let need = match executable.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        executable.activation.function.as_u32(),
        executable.activation.input.to_vec(),
        need.0,
        need.1,
    )
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
    executable_keys.sort_by(|left, right| compare_executable_keys(left, right, world.types()));

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

fn materialize_call_edges(
    world: &mut World<'_>,
    root_id: RootId,
    transport_plan: &TransportPlan,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    body: &LoweredBody,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<HashMap<CallSiteId, MaterializedCallEdge>>, FatalError> {
    let mut call_edges = HashMap::new();
    let callsite_needs = callsite_needs_for_body(body, executable.need);
    let LoweredBody::Clauses { entries, .. } = body else {
        return Ok(Some(call_edges));
    };
    for entry in entries {
        match &entry.tail {
            LoweredTail::DirectCall { callsite, dest, .. } => {
                let Some(edge) = materialize_direct_call_edge(
                    world,
                    root_id,
                    transport_plan,
                    executable,
                    analysis,
                    callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                    *callsite,
                    dest,
                    callsite_args,
                )?
                else {
                    return Ok(None);
                };
                call_edges.insert(*callsite, edge);
            }
            LoweredTail::ClosureCall { callsite, dest, .. } => {
                if let Some(edge) = materialize_closure_call_edge(
                    world,
                    root_id,
                    transport_plan,
                    executable,
                    analysis,
                    callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                    *callsite,
                    dest,
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
    transport_plan: &TransportPlan,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    need: ExecutableNeed,
    callsite: CallSiteId,
    dest: &ControlDestination,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<MaterializedCallEdge>, FatalError> {
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
    if let Some(target) = summary.single_target().cloned() {
        let (direct, return_ty) = lower_materialized_call_target(
            world,
            root_id,
            transport_plan,
            executable,
            analysis,
            need,
            callsite,
            dest,
            callsite_args,
            target,
        )?;
        return Ok(Some(MaterializedCallEdge {
            target: CallEdge::Direct(direct),
            return_ty,
        }));
    }
    let Some(dispatch) =
        super::super::callsite_dispatch::dispatch_from_callsite_summary(&summary).map_err(|error| {
            incomplete_semantic_plan(
                world,
                root_id,
                format!(
                    "materialization could not build dispatch for multi-target direct callsite {}: {error:?}",
                    callsite.as_u32()
                ),
            )
        })?
    else {
        return Ok(None);
    };
    let mut arms = Vec::new();
    let mut return_ty = None;
    for (body_id, target) in dispatch.targets.into_iter().enumerate() {
        let (direct, arm_return_ty) = lower_materialized_call_target(
            world,
            root_id,
            transport_plan,
            executable,
            analysis,
            need,
            callsite,
            dest,
            callsite_args,
            target,
        )?;
        match return_ty {
            Some(existing) if existing != arm_return_ty => {
                return Err(incomplete_semantic_plan(
                    world,
                    root_id,
                    format!(
                        "multi-target direct callsite {} has inconsistent arm return types {:?} and {:?}",
                        callsite.as_u32(),
                        existing,
                        arm_return_ty
                    ),
                ));
            }
            Some(_) => {}
            None => return_ty = Some(arm_return_ty),
        }
        arms.push(DispatchCallArm {
            body_id: body_id as u32,
            callee: direct.callee,
            return_flow: direct.return_flow,
            extern_marshals: direct.extern_marshals,
        });
    }
    let return_ty = return_ty.ok_or_else(|| {
        incomplete_semantic_plan(
            world,
            root_id,
            format!(
                "multi-target direct callsite {} has no dispatch arms",
                callsite.as_u32()
            ),
        )
    })?;
    Ok(Some(MaterializedCallEdge {
        target: CallEdge::Dispatch(DispatchCallEdge {
            plan: dispatch.plan,
            arms,
            miss: DispatchCallMiss::Unreachable,
        }),
        return_ty,
    }))
}

fn materialize_closure_call_edge(
    world: &mut World<'_>,
    root_id: RootId,
    transport_plan: &TransportPlan,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    need: ExecutableNeed,
    callsite: CallSiteId,
    dest: &ControlDestination,
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
    let (direct, return_ty) = lower_materialized_call_target(
        world,
        root_id,
        transport_plan,
        executable,
        analysis,
        need,
        callsite,
        dest,
        callsite_args,
        target,
    )?;
    Ok(Some(MaterializedCallEdge {
        target: CallEdge::Direct(direct),
        return_ty,
    }))
}

fn lower_materialized_call_target(
    world: &mut World<'_>,
    root_id: RootId,
    transport_plan: &TransportPlan,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    need: ExecutableNeed,
    callsite: CallSiteId,
    dest: &ControlDestination,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
    target: CallTargetSummary,
) -> Result<(DirectCallEdge<ExecutableKey>, Ty), FatalError> {
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
    let return_flow = call_return_flow(world, root_id, transport_plan, executable, &callee, callsite, dest)?;
    Ok((
        DirectCallEdge {
            callee,
            return_flow,
            extern_marshals,
        },
        target.settled_return(world.types_mut()),
    ))
}

fn call_return_flow(
    world: &World<'_>,
    root_id: RootId,
    transport_plan: &TransportPlan,
    executable: &ExecutableKey,
    callee: &CallTarget<ExecutableKey>,
    callsite: CallSiteId,
    dest: &ControlDestination,
) -> Result<CallReturnFlow, FatalError> {
    let caller_symbol = transport_executable_symbol(executable, world.types());
    match dest {
        ControlDestination::Deliver(entry) => {
            let payload = TransportPosition::ResumePayload {
                executable: caller_symbol,
                callsite: Some(callsite),
                entry: *entry,
            };
            Ok(CallReturnFlow::Deliver { payload, entry: *entry })
        }
        ControlDestination::Return => {
            let caller_return = TransportPosition::ExecutableReturn {
                executable: caller_symbol.clone(),
            };
            let payload = TransportPosition::ReturnPayload {
                executable: caller_symbol,
                callsite,
            };
            let caller_shape = require_transport_position(world, root_id, transport_plan, &caller_return)?;
            let payload_shape = require_transport_position(world, root_id, transport_plan, &payload)?;
            if let CallTarget::Local(callee) = callee {
                let callee_return = TransportPosition::ExecutableReturn {
                    executable: transport_executable_symbol(callee, world.types()),
                };
                let callee_shape = require_transport_position(world, root_id, transport_plan, &callee_return)?;
                if matches!(world.shape(callee_shape), ShapeDescr::Nothing)
                    || (caller_shape == callee_shape && payload_shape == callee_shape)
                {
                    return Ok(CallReturnFlow::Tail {
                        callee_return,
                        caller_return,
                    });
                }
            }
            Ok(CallReturnFlow::Continue { payload, caller_return })
        }
    }
}

fn require_transport_position(
    world: &World<'_>,
    root_id: RootId,
    transport_plan: &TransportPlan,
    position: &TransportPosition,
) -> Result<ShapeId, FatalError> {
    transport_plan.positions.get(position).copied().ok_or_else(|| {
        incomplete_semantic_plan(
            world,
            root_id,
            format!("transport plan is missing required call return-flow position {position:?}"),
        )
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
            if call_edges.get(callsite).is_some_and(call_edge_calls_provider_boundary) {
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

fn call_edge_calls_provider_boundary(edge: &MaterializedCallEdge) -> bool {
    match &edge.target {
        CallEdge::Direct(direct) => matches!(direct.callee, CallTarget::ProviderBoundary(_)),
        CallEdge::Dispatch(dispatch) => dispatch
            .arms
            .iter()
            .any(|arm| matches!(arm.callee, CallTarget::ProviderBoundary(_))),
    }
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
                for callee in local_call_edge_callees(edge) {
                    let Some(callee_effects) = snapshot.get(callee).copied() else {
                        return Err(incomplete_semantic_plan(
                            world,
                            root_id,
                            format!(
                                "materialized call edge {:?} -> {:?} points outside the closed executable frontier",
                                caller_key, callee
                            ),
                        ));
                    };
                    settled.union_with(callee_effects);
                }
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

fn local_call_edge_callees(edge: &MaterializedCallEdge) -> Vec<&ExecutableKey> {
    match &edge.target {
        CallEdge::Direct(direct) => direct.callee.local().into_iter().collect(),
        CallEdge::Dispatch(dispatch) => dispatch.arms.iter().filter_map(|arm| arm.callee.local()).collect(),
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
            let publication_reprs =
                function_entry_publication_reprs(&transport_plan.codegen_seam_facts, symbol, *semantic_index);
            if !publication_reprs.is_empty() {
                return publication_reprs;
            }
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
                    let publication_reprs =
                        function_entry_publication_reprs(&transport_plan.codegen_seam_facts, symbol, *semantic_index);
                    let repr = if let [repr] = publication_reprs.as_slice() {
                        *repr
                    } else {
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
                            Some(*leaf_shape),
                            *lane,
                        )
                    };
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
                    target: edge.target.clone(),
                    return_ty: edge.return_ty,
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

fn function_entry_publication_reprs(
    facts: &[super::super::transport::CodegenSeamFact],
    executable: &ExecutableSymbol,
    semantic_index: usize,
) -> Vec<AbiValueRepr> {
    facts
        .iter()
        .filter(|fact| {
            fact.shape.is_none()
                && matches!(
                    &fact.seam,
                    CodegenSeam::FunctionEntry {
                        executable: candidate,
                        semantic_index: candidate_index,
                    } if candidate == executable && *candidate_index == semantic_index
                )
        })
        .map(|fact| abi_repr_from_codegen(fact.repr))
        .collect()
}

fn shape_leaf_lanes_for_artifact(world: &World<'_>, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
    match world.shape(shape) {
        ShapeDescr::Nothing => Vec::new(),
        ShapeDescr::Lane(lane) => vec![(shape, *lane)],
        ShapeDescr::Tuple(items) => items
            .iter()
            .copied()
            .flat_map(|item| shape_leaf_lanes_for_artifact(world, item))
            .collect(),
        ShapeDescr::Callable(callable) => world
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
                target: lower_emission_call_edge_target(world, root_id, executable_index, &key, &edge.target)?,
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

fn lower_emission_call_edge_target(
    world: &World<'_>,
    root_id: RootId,
    executable_index: &HashMap<ExecutableKey, usize>,
    caller: &ExecutableKey,
    target: &CallEdge<ExecutableKey>,
) -> Result<CallEdge<usize>, FatalError> {
    Ok(match target {
        CallEdge::Direct(direct) => CallEdge::Direct(DirectCallEdge {
            callee: lower_emission_call_target(world, root_id, executable_index, caller, &direct.callee)?,
            return_flow: direct.return_flow.clone(),
            extern_marshals: direct.extern_marshals.clone(),
        }),
        CallEdge::Dispatch(dispatch) => CallEdge::Dispatch(DispatchCallEdge {
            plan: dispatch.plan.clone(),
            arms: dispatch
                .arms
                .iter()
                .map(|arm| {
                    Ok(DispatchCallArm {
                        body_id: arm.body_id,
                        callee: lower_emission_call_target(world, root_id, executable_index, caller, &arm.callee)?,
                        return_flow: arm.return_flow.clone(),
                        extern_marshals: arm.extern_marshals.clone(),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?,
            miss: dispatch.miss,
        }),
    })
}

fn lower_emission_call_target(
    world: &World<'_>,
    root_id: RootId,
    executable_index: &HashMap<ExecutableKey, usize>,
    caller: &ExecutableKey,
    target: &CallTarget<ExecutableKey>,
) -> Result<CallTarget<usize>, FatalError> {
    Ok(match target {
        CallTarget::Local(callee) => CallTarget::Local(executable_index.get(callee).copied().ok_or_else(|| {
            incomplete_semantic_plan(
                world,
                root_id,
                format!(
                    "ABI-ready call edge {:?} -> {:?} points outside the executable inventory",
                    caller, callee
                ),
            )
        })?),
        CallTarget::ProviderBoundary(function) => CallTarget::ProviderBoundary(*function),
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
        .transport_plan(root_id)
        .expect("ABI-ready callable inventory should read the settled transport plan");
    for boundary in &materialized.transport.boundary_ids {
        let boundary_descr = world.boundary(*boundary);
        let callable_descr = world.callable(boundary_descr.callable);
        let boundary_facts = transport_plan
            .boundaries
            .get(boundary)
            .unwrap_or_else(|| panic!("transport plan should publish boundary facts for {boundary:?}"));
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
        for target_symbol in boundary_facts.resolutions.iter() {
            let target = executable_key_for_symbol(materialized, target_symbol, world.types()).ok_or_else(|| {
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
    entries.sort_by(|left, right| compare_callable_entries(left, right, world.types()));
    entries.dedup();
    Ok(entries)
}

fn executable_key_for_symbol(
    materialized: &MaterializedProgram,
    symbol: &ExecutableSymbol,
    types: &Types,
) -> Option<ExecutableKey> {
    materialized
        .executables
        .keys()
        .find(|key| {
            key.need == symbol.need
                && key.activation.function == symbol.activation.function
                && key.activation.inputs(types).as_slice() == symbol.activation.input.as_ref()
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

fn compare_callable_entries(left: &CallableEntry, right: &CallableEntry, types: &Types) -> std::cmp::Ordering {
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
        .then_with(|| {
            left.target
                .activation
                .inputs(types)
                .cmp(&right.target.activation.inputs(types))
        })
        .then_with(|| left.capture_reprs.cmp(&right.capture_reprs))
        .then_with(|| left.arg_reprs.cmp(&right.arg_reprs))
        .then_with(|| left.return_ty.cmp(&right.return_ty))
        .then_with(|| left.return_shape.cmp(&right.return_shape))
        .then_with(|| left.return_lanes.cmp(&right.return_lanes))
}

fn compare_executable_keys(left: &ExecutableKey, right: &ExecutableKey, types: &Types) -> std::cmp::Ordering {
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
        .then_with(|| left.activation.inputs(types).cmp(&right.activation.inputs(types)))
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
    emit_through(world.tel(), std::slice::from_ref(&diagnostic));
    FatalError
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::telemetry::ConfiguredTelemetry;

    #[test]
    fn transport_position_sort_key_distinguishes_executable_symbol_identity() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        world.submit_code(None, "fn main(x), do: x".to_string());
        let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
        let function = world.root_entry(root).function;
        let int = world.types_mut().int();
        let any = world.types_mut().any();

        let value_symbol = ExecutableSymbol {
            activation: ActivationSymbol {
                function,
                input: vec![int].into_boxed_slice(),
            },
            need: ExecutableNeed::Value,
        };
        let tuple_symbol = ExecutableSymbol {
            activation: ActivationSymbol {
                function,
                input: vec![any].into_boxed_slice(),
            },
            need: ExecutableNeed::TupleFields(1),
        };

        let value_position = TransportPosition::ExecutableReturn {
            executable: value_symbol,
        };
        let tuple_position = TransportPosition::ExecutableReturn {
            executable: tuple_symbol,
        };

        assert_ne!(
            transport_position_sort_key(&value_position),
            transport_position_sort_key(&tuple_position),
            "artifact handoff ordering must be stable for multiple activations/needs of the same function"
        );
    }
}
