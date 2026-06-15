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
    ExecutableDispatch, MaterializedCallEdge, MaterializedExecutable, MaterializedProgram, TrashReturnAbi,
    TrashRuntimeInputLayout, TrashRuntimeLane, TrashRuntimeParamLayout, TrashRuntimeValueLayout,
};
use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, ControlEntryOrigin, DispatchBindings,
    Literal, LoweredBody, LoweredEntry, LoweredStep, LoweredTail, ValueId,
};
use super::super::drive::{FactKey, Job, JobEffects, settled_uses};
use super::super::identity::{
    ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, RootId, function_id_of_closure_target,
};
use super::super::scheduler::FatalError;
use super::super::semantic::{
    ActivationAnalysis, CallSiteKey, CallTargetSummary, CallableMaterialization, SelectedCallee,
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

    let closed_revision = world
        .fact_revision(&closed_fact)
        .expect("settled semantic closure should have a revision");
    let closure = world.semantic_closure(root_id);
    let reads = settled_uses([closed_fact]);
    let mut executables = HashMap::new();
    let mut original_entry_ids = HashMap::new();

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
        original_entry_ids.insert(executable.clone(), pruned.original_entry_ids);
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
                runtime_params: TrashRuntimeParamLayout::from_inputs(Vec::new()),
                return_layout: TrashRuntimeValueLayout::Omitted,
                resume_layouts: Vec::new(),
                entry_capture_layouts: Vec::new(),
                value_types: analysis.value_types,
                effects,
                body,
                call_edges,
            },
        );
    }

    let runtime_transports = derive_runtime_transports(world, &executables, &original_entry_ids);
    for (key, transport) in runtime_transports {
        let executable = executables
            .get_mut(&key)
            .expect("runtime transports should resolve for every materialized executable");
        executable.runtime_params = transport.runtime_params;
        executable.return_layout = transport.return_layout;
        executable.resume_layouts = transport.resume_layouts;
        executable.entry_capture_layouts = transport.entry_capture_layouts;
    }

    settle_effects(world, root_id, &mut executables)?;

    let program = MaterializedProgram {
        semantic_revision: closed_revision,
        entry: closure.entry,
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
    let plans = materialized
        .executables
        .iter()
        .map(|(key, executable)| (key.clone(), build_executable_abi_plan(world, key, executable)))
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
    let callable_entries = derive_callable_entries(world, root_id, &executables)?;
    let program = AbiReadyProgram {
        materialized_revision,
        entry: materialized.entry,
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

struct ExecutableRuntimeTransport {
    runtime_params: TrashRuntimeParamLayout,
    return_layout: TrashRuntimeValueLayout,
    resume_layouts: Vec<Option<TrashRuntimeValueLayout>>,
    entry_capture_layouts: Vec<Vec<TrashRuntimeValueLayout>>,
}

struct PrunedLoweredBody {
    body: LoweredBody,
    original_entry_ids: Vec<ControlEntryId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DeliverySource {
    Value(ValueId),
    DirectCall(CallSiteId),
    ClosureCall(CallSiteId),
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
                return_abi: entry.return_abi.clone(),
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
        entry,
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

fn collect_closure_callees(body: &LoweredBody) -> HashMap<CallSiteId, ValueId> {
    let mut out = HashMap::new();
    match body {
        LoweredBody::Extern { .. } => {}
        LoweredBody::Clauses { clauses, entries, .. } => {
            for clause in clauses {
                collect_step_closure_callees(&clause.projections, &mut out);
            }
            for entry in entries {
                collect_step_closure_callees(&entry.steps, &mut out);
                collect_tail_closure_callees(&entry.tail, &mut out);
            }
        }
    }
    out
}

fn collect_step_call_args(_steps: &[LoweredStep], _out: &mut HashMap<CallSiteId, Vec<CallArg>>) {}

fn collect_step_closure_callees(_steps: &[LoweredStep], _out: &mut HashMap<CallSiteId, ValueId>) {}

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

fn collect_tail_closure_callees(tail: &LoweredTail, out: &mut HashMap<CallSiteId, ValueId>) {
    if let LoweredTail::ClosureCall { callsite, callee, .. } = tail {
        out.insert(*callsite, *callee);
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct LocalCallableProducer {
    function: FunctionId,
    captures: Vec<ValueId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct LocalCallableId(usize);

#[derive(Debug, Clone, PartialEq, Eq)]
struct LocalCallableRecord {
    exec: usize,
    function: FunctionId,
    captures: Vec<ValueId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CallableWitnessState {
    Unknown,
    Exact(LocalCallableId),
    NonDirect,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExecutableCallableWitnesses {
    inputs: Vec<CallableWitnessState>,
    result: CallableWitnessState,
}

#[derive(Debug, Clone)]
enum WitnessMemo<T> {
    Unvisited,
    Pending,
    Ready(T),
}

struct ExecutableCallableFacts {
    callsite_args: HashMap<CallSiteId, Vec<CallArg>>,
    closure_callees: HashMap<CallSiteId, ValueId>,
    local_values: HashMap<ValueId, LocalCallableProducer>,
    params: HashMap<ValueId, usize>,
    resume_entries: HashMap<ValueId, ControlEntryId>,
    deliveries: HashMap<ControlEntryId, Vec<DeliverySource>>,
}

#[derive(Debug, Clone)]
struct IncomingLocalCall {
    caller: usize,
    args: Vec<CallArg>,
    closure_callee: Option<ValueId>,
}

struct CallableWitnessPlan<'a> {
    exec_ids: HashMap<&'a ExecutableKey, usize>,
    keys: Vec<&'a ExecutableKey>,
    executables: Vec<&'a MaterializedExecutable>,
    facts: Vec<&'a ExecutableCallableFacts>,
    local_callables: Vec<LocalCallableRecord>,
    incoming_local_calls: Vec<Vec<IncomingLocalCall>>,
    input_slots: Vec<usize>,
    value_slots: Vec<usize>,
    entry_slots: Vec<usize>,
    value_facts: Vec<Vec<ValueWitnessFact>>,
}

struct CallableWitnessResolver<'a> {
    plan: &'a CallableWitnessPlan<'a>,
    states: &'a [ExecutableCallableWitnesses],
    input_memo: Vec<Vec<WitnessMemo<CallableWitnessState>>>,
    result_memo: Vec<WitnessMemo<CallableWitnessState>>,
    value_memo: Vec<Vec<WitnessMemo<CallableWitnessState>>>,
    resume_memo: Vec<Vec<WitnessMemo<CallableWitnessState>>>,
    entry_return_memo: Vec<Vec<WitnessMemo<CallableWitnessState>>>,
    local_layout_memo: Vec<WitnessMemo<TrashRuntimeValueLayout>>,
}

#[derive(Debug, Clone, Default)]
struct ValueWitnessFact {
    producer: Option<LocalCallableId>,
    param: Option<usize>,
    resume_entry: Option<ControlEntryId>,
    ty: Option<Ty>,
    demand: super::super::semantic::RuntimeDemand,
}

struct SettledCallableWitnesses {
    states: Vec<ExecutableCallableWitnesses>,
}

/// Maps each resume entry (by `ControlEntryId::as_u32()` index) to the callsite
/// of the call that delivers to it. A `DeliveredResume` entry is always the
/// continuation of exactly one call tail whose `dest` is `Deliver(entry)`.
fn deliver_callsites(body: &LoweredBody) -> HashMap<usize, CallSiteId> {
    let mut map = HashMap::new();
    let LoweredBody::Clauses { entries, .. } = body else {
        return map;
    };
    for entry in entries {
        let (callsite, dest) = match &entry.tail {
            LoweredTail::DirectCall { callsite, dest, .. } | LoweredTail::ClosureCall { callsite, dest, .. } => {
                (*callsite, dest)
            }
            _ => continue,
        };
        if let ControlDestination::Deliver(target) = dest {
            map.insert(target.as_u32() as usize, callsite);
        }
    }
    map
}

/// The runtime demand a resume continuation will physically RECEIVE: exactly
/// what the producing callee emits. The callee delivers per its own settled
/// `return_demand` (a boundary callee delivers a `Value`); the resume value's
/// own demand only governs which delivered lanes are subsequently ignored, and
/// that stays a separate fact consumed at the native seam. Deriving the resume
/// layout from the callee's delivery -- not from the local use demand -- keeps
/// the continuation's reception and the callee's emission a single transport
/// fact, so they cannot diverge (e.g. an ignored `:ok` return still arrives as
/// a `Value` lane the continuation receives-then-drops, instead of vanishing to
/// `Omitted` and shifting the continuation's `self` pointer into a stale slot).
fn resume_delivery_demand(
    executable: &MaterializedExecutable,
    executables: &HashMap<ExecutableKey, MaterializedExecutable>,
    deliver_callsites: &HashMap<usize, CallSiteId>,
    entry_index: usize,
) -> Option<super::super::semantic::RuntimeDemand> {
    let callsite = deliver_callsites.get(&entry_index)?;
    let edge = executable.call_edges.get(callsite)?;
    match &edge.callee {
        CallTarget::Local(callee_key) => Some(executables.get(callee_key)?.runtime_demand.return_demand.clone()),
        CallTarget::ProviderBoundary(_) => Some(super::super::semantic::RuntimeDemand::Value),
    }
}

fn derive_runtime_transports(
    world: &mut World<'_>,
    executables: &HashMap<ExecutableKey, MaterializedExecutable>,
    original_entry_ids: &HashMap<ExecutableKey, Vec<ControlEntryId>>,
) -> HashMap<ExecutableKey, ExecutableRuntimeTransport> {
    let facts = executable_callable_facts(executables);
    let witness_plan = CallableWitnessPlan::new(executables, &facts);
    let SettledCallableWitnesses { states: witness_states } = settle_callable_witnesses(executables, &facts);
    let mut resolver = CallableWitnessResolver::new(&witness_plan, &witness_states);
    executables
        .iter()
        .map(|(key, executable)| {
            let exec = resolver
                .plan
                .exec_ids
                .get(key)
                .copied()
                .expect("runtime transport derivation requires a witness resolver id for every executable");
            let inputs = key
                .activation
                .input
                .iter()
                .copied()
                .enumerate()
                .map(|(semantic_index, ty)| {
                    let demand = executable
                        .runtime_demand
                        .input_demands
                        .get(semantic_index)
                        .cloned()
                        .unwrap_or_default();
                    trash_runtime_input_layout_from_demand(
                        world,
                        &mut resolver,
                        exec,
                        semantic_index,
                        ty,
                        &demand,
                        witness_states.get(exec).and_then(|states| states.inputs.get(semantic_index)),
                    )
                })
                .collect::<Vec<_>>();
            let return_layout = resolver.trash_runtime_value_layout_from_demand(
                world,
                exec,
                executable.return_ty,
                &executable.runtime_demand.return_demand,
                witness_states.get(exec).map(|states| &states.result),
            );
            let resume_layouts = match &executable.body {
                LoweredBody::Clauses { entries, .. } => {
                    let deliver_callsites = deliver_callsites(&executable.body);
                    entries
                        .iter()
                        .enumerate()
                        .map(|(entry_index, entry)| {
                            let value = entry.origin.input_value()?;
                            let ty = executable
                                .value_types
                                .get(&value)
                                .copied()
                                .unwrap_or_else(|| world.types_mut().any());
                            // Transport follows the producing callee's settled return
                            // delivery; the resume value's own use demand only governs
                            // lane-ignoring at the native seam, never the layout itself.
                            let demand =
                                resume_delivery_demand(executable, executables, &deliver_callsites, entry_index)
                                    .unwrap_or_else(|| {
                                        executable
                                            .runtime_demand
                                            .value_demands
                                            .get(&value)
                                            .cloned()
                                            .unwrap_or_default()
                                    });
                            let witness = resolver.value_witness(exec, value);
                            Some(resolver.trash_runtime_value_layout_from_demand(world, exec, ty, &demand, Some(&witness)))
                        })
                        .collect()
                }
                LoweredBody::Extern { .. } => Vec::new(),
            };
            let entry_capture_layouts = match &executable.body {
                LoweredBody::Clauses { entries, .. } => entries
                    .iter()
                    .enumerate()
                    .map(|(entry_index, entry)| {
                        let entry_id = *original_entry_ids
                            .get(key)
                            .and_then(|ids| ids.get(entry_index))
                            .unwrap_or_else(|| {
                                panic!(
                                    "runtime transport derivation requires an original lowered entry id for {:?} entry {}",
                                    key, entry_index
                                )
                            });
                        let capture_demands = executable
                            .runtime_demand
                            .entry_capture_demands
                            .get(&entry_id)
                            .cloned()
                            .unwrap_or_else(|| vec![super::super::semantic::RuntimeDemand::Ignore; entry.captures.len()]);
                        entry.captures
                            .iter()
                            .copied()
                            .zip(capture_demands)
                            .map(|(capture, demand)| {
                                let ty = executable
                                    .value_types
                                    .get(&capture)
                                    .copied()
                                    .unwrap_or_else(|| world.types_mut().any());
                                let witness = resolver.value_witness(exec, capture);
                                resolver.trash_runtime_value_layout_from_demand(world, exec, ty, &demand, Some(&witness))
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect(),
                LoweredBody::Extern { .. } => Vec::new(),
            };
            (
                key.clone(),
                ExecutableRuntimeTransport {
                    runtime_params: TrashRuntimeParamLayout::from_inputs(inputs),
                    return_layout,
                    resume_layouts,
                    entry_capture_layouts,
                },
            )
        })
        .collect()
}

fn trash_runtime_input_layout_from_demand(
    world: &mut World<'_>,
    resolver: &mut CallableWitnessResolver<'_>,
    exec: usize,
    semantic_index: usize,
    ty: Ty,
    demand: &super::super::semantic::RuntimeDemand,
    witness: Option<&CallableWitnessState>,
) -> TrashRuntimeInputLayout {
    TrashRuntimeInputLayout {
        semantic_index,
        layout: resolver.trash_runtime_value_layout_from_demand(world, exec, ty, demand, witness),
    }
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

fn executable_callable_facts(
    executables: &HashMap<ExecutableKey, MaterializedExecutable>,
) -> HashMap<ExecutableKey, ExecutableCallableFacts> {
    executables
        .iter()
        .map(|(key, executable)| {
            let mut local_values = HashMap::new();
            let mut params = HashMap::new();
            if let LoweredBody::Clauses { clauses, entries, .. } = &executable.body {
                for clause in clauses {
                    for (semantic_index, value) in clause.params.iter().copied().enumerate() {
                        params.insert(value, semantic_index);
                    }
                    collect_local_callable_values(&clause.projections, &mut local_values);
                }
                for entry in entries {
                    collect_local_callable_values(&entry.steps, &mut local_values);
                }
            }
            let resume_entries = resume_values(&executable.body)
                .into_iter()
                .map(|(entry, value)| (value, entry))
                .collect::<HashMap<_, _>>();
            (
                key.clone(),
                ExecutableCallableFacts {
                    callsite_args: collect_callsite_args(&executable.body),
                    closure_callees: collect_closure_callees(&executable.body),
                    local_values,
                    params,
                    resume_entries,
                    deliveries: deliveries(&executable.body),
                },
            )
        })
        .collect()
}

fn collect_local_callable_values(steps: &[LoweredStep], out: &mut HashMap<ValueId, LocalCallableProducer>) {
    for step in steps {
        let witness = match step {
            LoweredStep::FunctionRef { value, function } => Some((
                *value,
                LocalCallableProducer {
                    function: *function,
                    captures: Vec::new(),
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
                    captures: captures.clone(),
                },
            )),
            _ => None,
        };
        if let Some((value, witness)) = witness {
            out.insert(value, witness);
        }
    }
}

fn settle_callable_witnesses(
    executables: &HashMap<ExecutableKey, MaterializedExecutable>,
    facts: &HashMap<ExecutableKey, ExecutableCallableFacts>,
) -> SettledCallableWitnesses {
    let plan = CallableWitnessPlan::new(executables, facts);
    let mut states = plan
        .keys
        .iter()
        .map(|key| ExecutableCallableWitnesses {
            inputs: vec![CallableWitnessState::Unknown; key.activation.input.len()],
            result: CallableWitnessState::Unknown,
        })
        .collect::<Vec<_>>();

    loop {
        let mut resolver = CallableWitnessResolver::new(&plan, &states);
        let next = resolver.solve();
        if next == states {
            return SettledCallableWitnesses { states: next };
        }
        states = next;
    }
}

impl<'a> CallableWitnessPlan<'a> {
    fn new(
        executables: &'a HashMap<ExecutableKey, MaterializedExecutable>,
        facts: &'a HashMap<ExecutableKey, ExecutableCallableFacts>,
    ) -> Self {
        let keys = executables.keys().collect::<Vec<_>>();
        let exec_ids = keys
            .iter()
            .enumerate()
            .map(|(id, key)| (*key, id))
            .collect::<HashMap<_, _>>();
        let executables_by_id = keys
            .iter()
            .map(|key| {
                executables
                    .get(*key)
                    .expect("witness resolver keys must point at reachable executables")
            })
            .collect::<Vec<_>>();
        let facts_by_id = keys
            .iter()
            .map(|key| {
                facts
                    .get(*key)
                    .expect("witness resolver requires callable facts for every executable")
            })
            .collect::<Vec<_>>();
        let mut local_callables = Vec::new();
        let mut local_ids_by_exec = vec![HashMap::new(); keys.len()];
        for (exec, fact) in facts_by_id.iter().enumerate() {
            let mut local_values = fact.local_values.iter().collect::<Vec<_>>();
            local_values.sort_by_key(|(value, _)| value.as_u32());
            for (value, producer) in local_values {
                let id = LocalCallableId(local_callables.len());
                local_callables.push(LocalCallableRecord {
                    exec,
                    function: producer.function,
                    captures: producer.captures.clone(),
                });
                local_ids_by_exec[exec].insert(*value, id);
            }
        }
        let mut incoming_local_calls = vec![Vec::new(); keys.len()];
        for (caller_id, _key) in keys.iter().enumerate() {
            let caller = executables_by_id[caller_id];
            let caller_facts = facts_by_id[caller_id];
            for (callsite, edge) in &caller.call_edges {
                let CallTarget::Local(target) = &edge.callee else {
                    continue;
                };
                let Some(target_id) = exec_ids.get(target).copied() else {
                    continue;
                };
                let Some(args) = caller_facts.callsite_args.get(callsite) else {
                    continue;
                };
                incoming_local_calls[target_id].push(IncomingLocalCall {
                    caller: caller_id,
                    args: args.clone(),
                    closure_callee: caller_facts.closure_callees.get(callsite).copied(),
                });
            }
        }
        let input_slots = executables_by_id
            .iter()
            .map(|executable| executable.runtime_demand.input_demands.len())
            .collect::<Vec<_>>();
        let value_slots = executables_by_id
            .iter()
            .zip(facts_by_id.iter())
            .map(|(executable, fact)| witness_value_slots(executable, fact))
            .collect::<Vec<_>>();
        let entry_slots = executables_by_id
            .iter()
            .map(|executable| witness_entry_slots(executable))
            .collect::<Vec<_>>();
        let value_facts = executables_by_id
            .iter()
            .zip(facts_by_id.iter())
            .zip(value_slots.iter().copied())
            .enumerate()
            .map(|(exec, ((executable, fact), slots))| {
                let mut values = vec![ValueWitnessFact::default(); slots];
                for (value, producer) in &local_ids_by_exec[exec] {
                    values[value.as_u32() as usize].producer = Some(*producer);
                }
                for (value, semantic_index) in &fact.params {
                    values[value.as_u32() as usize].param = Some(*semantic_index);
                }
                for (value, entry_id) in &fact.resume_entries {
                    values[value.as_u32() as usize].resume_entry = Some(*entry_id);
                }
                for (value, ty) in &executable.value_types {
                    values[value.as_u32() as usize].ty = Some(*ty);
                }
                for (value, demand) in &executable.runtime_demand.value_demands {
                    values[value.as_u32() as usize].demand = demand.clone();
                }
                values
            })
            .collect::<Vec<_>>();

        Self {
            exec_ids,
            keys,
            executables: executables_by_id,
            facts: facts_by_id,
            local_callables,
            incoming_local_calls,
            input_slots,
            value_slots,
            entry_slots,
            value_facts,
        }
    }
}

impl<'a> CallableWitnessResolver<'a> {
    fn new(plan: &'a CallableWitnessPlan<'a>, states: &'a [ExecutableCallableWitnesses]) -> Self {
        let input_memo = plan
            .input_slots
            .iter()
            .copied()
            .map(|len| vec![WitnessMemo::Unvisited; len])
            .collect::<Vec<_>>();
        let result_memo = vec![WitnessMemo::Unvisited; plan.keys.len()];
        let value_memo = plan
            .value_slots
            .iter()
            .copied()
            .map(|len| vec![WitnessMemo::Unvisited; len])
            .collect::<Vec<_>>();
        let resume_memo = plan
            .entry_slots
            .iter()
            .copied()
            .map(|len| vec![WitnessMemo::Unvisited; len])
            .collect::<Vec<_>>();
        let entry_return_memo = plan
            .entry_slots
            .iter()
            .copied()
            .map(|len| vec![WitnessMemo::Unvisited; len])
            .collect::<Vec<_>>();
        let local_layout_memo = vec![WitnessMemo::Unvisited; plan.local_callables.len()];
        Self {
            plan,
            states,
            input_memo,
            result_memo,
            value_memo,
            resume_memo,
            entry_return_memo,
            local_layout_memo,
        }
    }

    fn solve(&mut self) -> Vec<ExecutableCallableWitnesses> {
        let mut out = Vec::with_capacity(self.plan.keys.len());
        for exec in 0..self.plan.keys.len() {
            out.push(ExecutableCallableWitnesses {
                inputs: self.input_witnesses(exec),
                result: self.result_witness(exec),
            });
        }
        out
    }

    fn value_witness(&mut self, exec: usize, value: ValueId) -> CallableWitnessState {
        let slot = value.as_u32() as usize;
        let Some(memo) = self.value_memo.get(exec).and_then(|memo| memo.get(slot)) else {
            return CallableWitnessState::NonDirect;
        };
        match memo {
            WitnessMemo::Pending => return CallableWitnessState::Unknown,
            WitnessMemo::Ready(state) => return *state,
            WitnessMemo::Unvisited => {}
        }
        self.value_memo[exec][slot] = WitnessMemo::Pending;
        let resolved = self.compute_value_witness(exec, value);
        self.value_memo[exec][slot] = WitnessMemo::Ready(resolved);
        resolved
    }

    fn result_witness(&mut self, exec: usize) -> CallableWitnessState {
        match &self.result_memo[exec] {
            WitnessMemo::Pending => return CallableWitnessState::Unknown,
            WitnessMemo::Ready(state) => return *state,
            WitnessMemo::Unvisited => {}
        }
        self.result_memo[exec] = WitnessMemo::Pending;
        let resolved = self.compute_result_witness(exec);
        self.result_memo[exec] = WitnessMemo::Ready(resolved);
        resolved
    }

    fn entry_return_witness(&mut self, exec: usize, entry_id: ControlEntryId) -> CallableWitnessState {
        let slot = entry_id.as_u32() as usize;
        let Some(memo) = self.entry_return_memo.get(exec).and_then(|memo| memo.get(slot)) else {
            return CallableWitnessState::NonDirect;
        };
        match memo {
            WitnessMemo::Pending => return CallableWitnessState::Unknown,
            WitnessMemo::Ready(state) => return *state,
            WitnessMemo::Unvisited => {}
        }
        self.entry_return_memo[exec][slot] = WitnessMemo::Pending;
        let resolved = self.compute_entry_return_witness(exec, entry_id);
        self.entry_return_memo[exec][slot] = WitnessMemo::Ready(resolved);
        resolved
    }

    fn resume_witness(&mut self, exec: usize, entry_id: ControlEntryId) -> CallableWitnessState {
        let slot = entry_id.as_u32() as usize;
        let Some(memo) = self.resume_memo.get(exec).and_then(|memo| memo.get(slot)) else {
            return CallableWitnessState::NonDirect;
        };
        match memo {
            WitnessMemo::Pending => return CallableWitnessState::Unknown,
            WitnessMemo::Ready(state) => return *state,
            WitnessMemo::Unvisited => {}
        }
        self.resume_memo[exec][slot] = WitnessMemo::Pending;
        let resolved = self.compute_resume_witness(exec, entry_id);
        self.resume_memo[exec][slot] = WitnessMemo::Ready(resolved);
        resolved
    }

    fn input_witnesses(&mut self, exec: usize) -> Vec<CallableWitnessState> {
        let len = self.plan.executables[exec].runtime_demand.input_demands.len();
        let mut out = Vec::with_capacity(len);
        for semantic_index in 0..len {
            out.push(self.input_witness(exec, semantic_index));
        }
        out
    }

    fn input_witness(&mut self, exec: usize, semantic_index: usize) -> CallableWitnessState {
        match &self.input_memo[exec][semantic_index] {
            WitnessMemo::Pending => return CallableWitnessState::Unknown,
            WitnessMemo::Ready(state) => return *state,
            WitnessMemo::Unvisited => {}
        }
        self.input_memo[exec][semantic_index] = WitnessMemo::Pending;
        let resolved = self.compute_input_witness(exec, semantic_index);
        self.input_memo[exec][semantic_index] = WitnessMemo::Ready(resolved);
        resolved
    }

    fn compute_input_witness(&mut self, exec: usize, semantic_index: usize) -> CallableWitnessState {
        let executable = self.plan.executables[exec];
        let Some(demand) = executable.runtime_demand.input_demands.get(semantic_index) else {
            return CallableWitnessState::NonDirect;
        };
        let super::super::semantic::RuntimeDemand::Callable(callable) = demand else {
            return CallableWitnessState::NonDirect;
        };
        if callable.opaque || callable.escape || callable.resolved.is_empty() {
            return CallableWitnessState::NonDirect;
        }
        let mut joined = CallableWitnessState::Unknown;
        for incoming_index in 0..self.plan.incoming_local_calls[exec].len() {
            enum IncomingWitnessSource {
                Arg(ValueId),
                Capture { callee: ValueId, capture_index: usize },
            }

            let Some((caller, source)) = ({
                let incoming = &self.plan.incoming_local_calls[exec][incoming_index];
                let capture_prefix = self.plan.keys[exec]
                    .activation
                    .input
                    .len()
                    .saturating_sub(incoming.args.len());
                if semantic_index < capture_prefix {
                    incoming.closure_callee.map(|callee| {
                        (
                            incoming.caller,
                            IncomingWitnessSource::Capture {
                                callee,
                                capture_index: semantic_index,
                            },
                        )
                    })
                } else {
                    let arg_index = semantic_index - capture_prefix;
                    incoming
                        .args
                        .get(arg_index)
                        .map(|arg| (incoming.caller, IncomingWitnessSource::Arg(arg.value)))
                }
            }) else {
                continue;
            };
            let observed = match source {
                IncomingWitnessSource::Arg(value) => self.value_witness(caller, value),
                IncomingWitnessSource::Capture { callee, capture_index } => match self.value_witness(caller, callee) {
                    CallableWitnessState::Exact(local_id) => self
                        .plan
                        .local_callables
                        .get(local_id.0)
                        .and_then(|callable| {
                            callable
                                .captures
                                .get(capture_index)
                                .copied()
                                .map(|capture| (callable.exec, capture))
                        })
                        .map(|(producer_exec, capture)| self.value_witness(producer_exec, capture))
                        .unwrap_or(CallableWitnessState::NonDirect),
                    other => other,
                },
            };
            joined = join_callable_witness(joined, observed);
        }
        joined
    }

    fn compute_result_witness(&mut self, exec: usize) -> CallableWitnessState {
        let executable = self.plan.executables[exec];
        let super::super::semantic::RuntimeDemand::Callable(callable) = &executable.runtime_demand.return_demand else {
            return CallableWitnessState::NonDirect;
        };
        if callable.opaque || callable.escape || callable.resolved.is_empty() {
            return CallableWitnessState::NonDirect;
        }
        let LoweredBody::Clauses { clauses, .. } = &executable.body else {
            return CallableWitnessState::NonDirect;
        };
        let mut joined = CallableWitnessState::Unknown;
        for clause in clauses {
            let observed = self.entry_return_witness(exec, clause.entry);
            joined = join_callable_witness(joined, observed);
        }
        joined
    }

    fn compute_entry_return_witness(&mut self, exec: usize, entry_id: ControlEntryId) -> CallableWitnessState {
        let executable = self.plan.executables[exec];
        let LoweredBody::Clauses { entries, .. } = &executable.body else {
            return CallableWitnessState::NonDirect;
        };
        let Some(entry) = entries.get(entry_id.as_u32() as usize) else {
            return CallableWitnessState::NonDirect;
        };
        match &entry.tail {
            LoweredTail::Value { value, dest } => match dest {
                ControlDestination::Return => self.value_witness(exec, *value),
                ControlDestination::Deliver(target) => self.entry_return_witness(exec, *target),
            },
            LoweredTail::DirectCall { callsite, dest, .. } | LoweredTail::ClosureCall { callsite, dest, .. } => {
                match dest {
                    ControlDestination::Return => self.callsite_return_witness(exec, *callsite),
                    ControlDestination::Deliver(target) => self.entry_return_witness(exec, *target),
                }
            }
            LoweredTail::If {
                then_entry, else_entry, ..
            } => join_callable_witness(
                self.entry_return_witness(exec, *then_entry),
                self.entry_return_witness(exec, *else_entry),
            ),
            LoweredTail::Dispatch { dispatch, .. } => {
                let mut joined = self.entry_return_witness(exec, dispatch.miss_entry);
                for arm_entry in &dispatch.arm_entries {
                    joined = join_callable_witness(joined, self.entry_return_witness(exec, *arm_entry));
                }
                joined
            }
            LoweredTail::Receive(receive) => {
                let mut joined = CallableWitnessState::Unknown;
                for clause in &receive.clauses {
                    joined = join_callable_witness(joined, self.entry_return_witness(exec, clause.entry));
                }
                if let Some(after) = &receive.after {
                    joined = join_callable_witness(joined, self.entry_return_witness(exec, after.entry));
                }
                joined
            }
            LoweredTail::Halt { .. } => CallableWitnessState::NonDirect,
        }
    }

    fn compute_value_witness(&mut self, exec: usize, value: ValueId) -> CallableWitnessState {
        let slot = value.as_u32() as usize;
        let Some(fact) = self.plan.value_facts[exec].get(slot) else {
            return CallableWitnessState::NonDirect;
        };
        if let Some(producer) = fact.producer {
            return CallableWitnessState::Exact(producer);
        }
        if let Some(semantic_index) = fact.param {
            return self.states[exec]
                .inputs
                .get(semantic_index)
                .cloned()
                .unwrap_or(CallableWitnessState::Unknown);
        }
        if let Some(entry_id) = fact.resume_entry {
            return self.resume_witness(exec, entry_id);
        }
        CallableWitnessState::NonDirect
    }

    fn compute_resume_witness(&mut self, exec: usize, entry_id: ControlEntryId) -> CallableWitnessState {
        let fact = self.plan.facts[exec];
        let mut joined = CallableWitnessState::Unknown;
        for delivery in fact.deliveries.get(&entry_id).into_iter().flatten() {
            let observed = match delivery {
                DeliverySource::Value(value) => self.value_witness(exec, *value),
                DeliverySource::DirectCall(callsite) | DeliverySource::ClosureCall(callsite) => {
                    self.callsite_return_witness(exec, *callsite)
                }
            };
            joined = join_callable_witness(joined, observed);
        }
        joined
    }

    fn callsite_return_witness(&self, exec: usize, callsite: CallSiteId) -> CallableWitnessState {
        let executable = self.plan.executables[exec];
        let Some(edge) = executable.call_edges.get(&callsite) else {
            return CallableWitnessState::NonDirect;
        };
        match &edge.callee {
            CallTarget::Local(callee) => self
                .plan
                .exec_ids
                .get(callee)
                .map(|callee| self.states[*callee].result)
                .unwrap_or(CallableWitnessState::Unknown),
            CallTarget::ProviderBoundary(_) => CallableWitnessState::NonDirect,
        }
    }

    fn trash_runtime_value_layout_from_demand(
        &mut self,
        world: &mut World<'_>,
        _exec: usize,
        ty: Ty,
        demand: &super::super::semantic::RuntimeDemand,
        witness: Option<&CallableWitnessState>,
    ) -> TrashRuntimeValueLayout {
        if world.types().is_empty(&ty) {
            return TrashRuntimeValueLayout::Omitted;
        }
        match demand {
            super::super::semantic::RuntimeDemand::Ignore => TrashRuntimeValueLayout::Omitted,
            super::super::semantic::RuntimeDemand::Value => TrashRuntimeValueLayout::Value {
                ty,
                repr: abi_value_repr(world, ty),
            },
            super::super::semantic::RuntimeDemand::TupleFields(fields) => TrashRuntimeValueLayout::TupleFields {
                fields: tuple_field_tys(world, ty, fields.len())
                    .into_iter()
                    .zip(fields.iter())
                    .map(|(field_ty, field_demand)| {
                        self.trash_runtime_value_layout_from_demand(world, _exec, field_ty, field_demand, None)
                    })
                    .collect(),
            },
            super::super::semantic::RuntimeDemand::Callable(callable) => {
                if callable.opaque || callable.escape || callable.resolved.is_empty() {
                    return TrashRuntimeValueLayout::Value {
                        ty,
                        repr: AbiValueRepr::ValueRef,
                    };
                }
                match witness {
                    Some(CallableWitnessState::Exact(local_id)) => self.trash_local_callable_layout(world, *local_id),
                    _ => TrashRuntimeValueLayout::Value {
                        ty,
                        repr: AbiValueRepr::ValueRef,
                    },
                }
            }
        }
    }

    /// Serves the settled transport layout for a direct-only callable value:
    /// one-level target identity plus the FLAT capture lanes it occupies. Each
    /// capture's own structure is flattened to leaf lanes here and never stored
    /// nested — the carrier only moves lanes; the callee body interprets them
    /// via its own settled capture layout. A direct-only capture chain is a DAG
    /// (a lambda's captures are bound before the lambda), so re-entry is
    /// impossible; we treat it as an invariant violation rather than silently
    /// collapsing to a ValueRef as the old recursive model did.
    fn trash_local_callable_layout(
        &mut self,
        world: &mut World<'_>,
        local_id: LocalCallableId,
    ) -> TrashRuntimeValueLayout {
        match self.local_layout_memo.get(local_id.0) {
            Some(WitnessMemo::Ready(layout)) => return layout.clone(),
            Some(WitnessMemo::Pending) => {
                panic!("direct-only callable capture chain must be acyclic; local callable {local_id:?} re-entered");
            }
            Some(WitnessMemo::Unvisited) => {}
            None => panic!("local callable layout requested for unknown local callable {local_id:?}"),
        }
        self.local_layout_memo[local_id.0] = WitnessMemo::Pending;
        let callable = &self.plan.local_callables[local_id.0];
        let function = callable.function;
        let exec = callable.exec;
        let captures = callable.captures.clone();
        let mut capture_lanes = Vec::new();
        for capture in captures {
            let fact = self.plan.value_facts[exec]
                .get(capture.as_u32() as usize)
                .cloned()
                .unwrap_or_default();
            let capture_ty = fact.ty.unwrap_or_else(|| world.types_mut().any());
            let capture_witness = self.value_witness(exec, capture);
            let layout = self.trash_runtime_value_layout_from_demand(
                world,
                exec,
                capture_ty,
                &fact.demand,
                Some(&capture_witness),
            );
            for (ty, repr) in layout.lane_tys().into_iter().zip(layout.abi_reprs()) {
                capture_lanes.push(TrashRuntimeLane { ty, repr });
            }
        }
        let layout = TrashRuntimeValueLayout::DirectCallable {
            function,
            capture_lanes,
        };
        self.local_layout_memo[local_id.0] = WitnessMemo::Ready(layout.clone());
        layout
    }
}

fn witness_entry_slots(executable: &MaterializedExecutable) -> usize {
    match &executable.body {
        LoweredBody::Clauses { entries, .. } => entries.len(),
        LoweredBody::Extern { .. } => 0,
    }
}

fn witness_value_slots(executable: &MaterializedExecutable, fact: &ExecutableCallableFacts) -> usize {
    let value_max = executable
        .value_types
        .keys()
        .chain(executable.runtime_demand.value_demands.keys())
        .chain(fact.local_values.keys())
        .chain(fact.params.keys())
        .chain(fact.resume_entries.keys())
        .map(|value| value.as_u32() as usize)
        .max()
        .unwrap_or(0);
    value_max + 1
}

fn join_callable_witness(left: CallableWitnessState, right: CallableWitnessState) -> CallableWitnessState {
    match (left, right) {
        (CallableWitnessState::NonDirect, _) | (_, CallableWitnessState::NonDirect) => CallableWitnessState::NonDirect,
        (CallableWitnessState::Unknown, other) | (other, CallableWitnessState::Unknown) => other,
        (CallableWitnessState::Exact(left), CallableWitnessState::Exact(right)) => {
            if left == right {
                CallableWitnessState::Exact(left)
            } else {
                CallableWitnessState::NonDirect
            }
        }
    }
}

fn build_executable_abi_plan(
    world: &mut World<'_>,
    _key: &ExecutableKey,
    executable: &MaterializedExecutable,
) -> ExecutableAbiPlan {
    let runtime_params = executable.runtime_params.clone();
    let param_reprs = runtime_params.abi_reprs();
    let mut value_reprs = HashMap::new();
    if let LoweredBody::Clauses { clauses, entries, .. } = &executable.body {
        for clause in clauses {
            for (index, value) in clause.params.iter().copied().enumerate() {
                let Some(layout) = runtime_params.semantic_input(index) else {
                    continue;
                };
                if let TrashRuntimeValueLayout::Value { repr, .. } = layout.value_layout() {
                    value_reprs.insert(value, *repr);
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
        runtime_params: executable.runtime_params.clone(),
        return_layout: executable.return_layout.clone(),
        // The settled recursive resume transport from MaterializeRoot is the
        // authority. We no longer recover it from the narrow return ABI.
        resume_layouts: executable.resume_layouts.clone(),
        entry_capture_layouts: executable.entry_capture_layouts.clone(),
        value_types: executable.value_types.clone(),
        value_reprs: plan.value_reprs.clone(),
        effects: executable.effects,
        body: executable.body.clone(),
        call_edges,
    })
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

fn resume_values(body: &LoweredBody) -> HashMap<ControlEntryId, ValueId> {
    let mut values = HashMap::new();
    if let LoweredBody::Clauses { entries, .. } = body {
        for (index, entry) in entries.iter().enumerate() {
            if let super::super::body::ControlEntryOrigin::DeliveredResume { value } = entry.origin {
                values.insert(ControlEntryId::from_u32(index as u32), value);
            }
        }
    }
    values
}

fn deliveries(body: &LoweredBody) -> HashMap<ControlEntryId, Vec<DeliverySource>> {
    let mut deliveries = HashMap::new();
    if let LoweredBody::Clauses { entries, .. } = body {
        for entry in entries {
            record_delivery(&entry.tail, &mut deliveries);
        }
    }
    deliveries
}

fn record_delivery(tail: &LoweredTail, deliveries: &mut HashMap<ControlEntryId, Vec<DeliverySource>>) {
    match tail {
        LoweredTail::Value {
            value,
            dest: ControlDestination::Deliver(entry_id),
        } => deliveries
            .entry(*entry_id)
            .or_default()
            .push(DeliverySource::Value(*value)),
        LoweredTail::DirectCall {
            callsite,
            dest: ControlDestination::Deliver(entry_id),
            ..
        } => deliveries
            .entry(*entry_id)
            .or_default()
            .push(DeliverySource::DirectCall(*callsite)),
        LoweredTail::ClosureCall {
            callsite,
            dest: ControlDestination::Deliver(entry_id),
            ..
        } => deliveries
            .entry(*entry_id)
            .or_default()
            .push(DeliverySource::ClosureCall(*callsite)),
        LoweredTail::Value { .. } | LoweredTail::DirectCall { .. } | LoweredTail::ClosureCall { .. } => {}
        LoweredTail::If { .. } | LoweredTail::Dispatch { .. } | LoweredTail::Receive(_) | LoweredTail::Halt { .. } => {}
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
        runtime_params: executable.runtime_params.clone(),
        return_layout: executable.return_layout.clone(),
        resume_layouts: executable.resume_layouts.clone(),
        entry_capture_layouts: executable.entry_capture_layouts.clone(),
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
    executables: &HashMap<ExecutableKey, AbiReadyExecutable>,
) -> Result<Vec<CallableEntry>, FatalError> {
    let mut entries = Vec::new();
    for executable in executables.values() {
        let producer_values = local_callable_producer_values(&executable.body);
        for (value, materialization) in &executable.runtime_demand.callable_materializations {
            if !matches!(materialization, CallableMaterialization::FirstClass { .. }) {
                continue;
            }
            if !producer_values.contains(value) {
                continue;
            }
            let ty = executable.value_types.get(value).copied().ok_or_else(|| {
                incomplete_semantic_plan(
                    world,
                    root_id,
                    format!(
                        "ABI-ready executable is missing the settled type for runtime callable value {}",
                        value.as_u32()
                    ),
                )
            })?;
            match resolve_callable_entries_for_type(world, root_id, executables, ty)? {
                CallableResolution::Resolved(resolved) => entries.extend(resolved),
                CallableResolution::NotCallable => {
                    return Err(incomplete_semantic_plan(
                        world,
                        root_id,
                        format!("runtime callable value {} is not callable", value.as_u32()),
                    ));
                }
                CallableResolution::Opaque => {
                    return Err(incomplete_semantic_plan(
                        world,
                        root_id,
                        format!(
                            "first-class callable materialization for value {} lost closure identity",
                            value.as_u32()
                        ),
                    ));
                }
            }
        }
    }
    entries.sort_by(compare_callable_entries);
    entries.dedup_by(|left, right| left.target == right.target && left.capture_count == right.capture_count);
    Ok(entries)
}

fn local_callable_producer_values(body: &LoweredBody) -> HashSet<ValueId> {
    let mut values = HashSet::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return values;
    };
    for clause in clauses {
        for step in &clause.projections {
            if let Some(value) = step_local_callable_value(step) {
                values.insert(value);
            }
        }
    }
    for entry in entries {
        for step in &entry.steps {
            if let Some(value) = step_local_callable_value(step) {
                values.insert(value);
            }
        }
    }
    values
}

fn step_local_callable_value(step: &LoweredStep) -> Option<ValueId> {
    match step {
        LoweredStep::FunctionRef { value, .. } | LoweredStep::Lambda { value, .. } => Some(*value),
        _ => None,
    }
}

/// Projects a true callable boundary's return ABI from the target's settled
/// return transport. This is the only place TrashReturnAbi is produced: a boundary
/// is a publication contract for a first-class callable, so a structural return
/// (tuple fields, direct callable) boxes to one ValueRef at the boundary, and a
/// diverging target (empty return type) never returns.
fn trash_boundary_return_abi(
    world: &mut World<'_>,
    return_ty: Ty,
    return_layout: &TrashRuntimeValueLayout,
) -> TrashReturnAbi {
    if world.types().is_empty(&return_ty) {
        return TrashReturnAbi::Never;
    }
    match return_layout {
        TrashRuntimeValueLayout::Value { repr, .. } => TrashReturnAbi::Value(*repr),
        TrashRuntimeValueLayout::Omitted
        | TrashRuntimeValueLayout::TupleFields { .. }
        | TrashRuntimeValueLayout::DirectCallable { .. } => TrashReturnAbi::Value(AbiValueRepr::ValueRef),
    }
}

fn resolve_callable_entries_for_type(
    world: &mut World<'_>,
    root_id: RootId,
    executables: &HashMap<ExecutableKey, AbiReadyExecutable>,
    ty: Ty,
) -> Result<CallableResolution, FatalError> {
    let Some(clauses) = world.types_mut().callable_value_clauses(&ty) else {
        return Ok(CallableResolution::NotCallable);
    };
    if clauses.is_empty() {
        return Ok(CallableResolution::NotCallable);
    }

    let mut entries = Vec::with_capacity(clauses.len());
    for clause in clauses {
        let Some(closure) = clause.closure else {
            return Ok(CallableResolution::Opaque);
        };
        let function = function_id_of_closure_target(closure.target);
        let capture_count = closure.captures.len();
        let fixed_arity = clause.args.len();
        let variadic = world.function_variadic(function);
        let mut matched = false;
        for (target, target_executable) in executables {
            if target.activation.function != function || target.need != ExecutableNeed::Value {
                continue;
            }
            if !callable_entry_arity_matches(target, capture_count, fixed_arity, variadic) {
                continue;
            }
            if !capture_prefix_matches(world, &target.activation.input, &closure.captures) {
                continue;
            }
            matched = true;
            let capture_reprs = closure
                .captures
                .iter()
                .copied()
                .map(|capture_ty| abi_value_repr(world, capture_ty))
                .collect::<Vec<_>>();
            let arg_reprs = target.activation.input[capture_count..]
                .iter()
                .copied()
                .map(|arg_ty| abi_value_repr(world, arg_ty))
                .collect::<Vec<_>>();
            entries.push(CallableEntry {
                target: target.clone(),
                capture_count,
                capture_reprs,
                arg_reprs,
                return_ty: target_executable.return_ty,
                return_abi: trash_boundary_return_abi(
                    world,
                    target_executable.return_ty,
                    &target_executable.return_layout,
                ),
            });
        }
        if !matched {
            let function_ref = world.function_ref(function);
            return Err(incomplete_semantic_plan(
                world,
                root_id,
                format!(
                    "callable entry target `{}/{}` with {} capture(s) is missing from the closed executable frontier",
                    function_ref.name, function_ref.arity, capture_count,
                ),
            ));
        }
    }
    Ok(CallableResolution::Resolved(entries))
}

fn compare_callable_entries(left: &CallableEntry, right: &CallableEntry) -> std::cmp::Ordering {
    left.target
        .activation
        .function
        .as_u32()
        .cmp(&right.target.activation.function.as_u32())
        .then_with(|| left.capture_count.cmp(&right.capture_count))
        .then_with(|| left.target.activation.input.cmp(&right.target.activation.input))
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
        .then_with(|| left.capture_count.cmp(&right.capture_count))
}

fn capture_prefix_matches(world: &mut World<'_>, input: &[Ty], captures: &[Ty]) -> bool {
    if input.len() < captures.len() {
        return false;
    }
    input
        .iter()
        .copied()
        .zip(captures.iter().copied())
        .all(|(target, capture)| {
            let overlap = world.types_mut().intersect(target, capture);
            !world.types().is_empty(&overlap)
        })
}

fn callable_entry_arity_matches(
    target: &ExecutableKey,
    capture_count: usize,
    fixed_arity: usize,
    variadic: bool,
) -> bool {
    let actual_arity = target.activation.input.len().saturating_sub(capture_count);
    if variadic {
        actual_arity >= fixed_arity
    } else {
        actual_arity == fixed_arity
    }
}

enum CallableResolution {
    NotCallable,
    Opaque,
    Resolved(Vec<CallableEntry>),
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
