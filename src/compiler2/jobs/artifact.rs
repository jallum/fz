//! Compiler2 artifact projection jobs.
//!
//! This module turns a closed semantic root into backend-owned artifact
//! projections. Each rung is derived from the one below it and never reopens
//! semantic discovery.

use std::collections::HashMap;

use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::ir_lower::extern_ty_from_name;
use crate::parser::lexer::Tok;

use super::super::artifact::{
    AbiReadyCallEdge, AbiReadyExecutable, AbiReadyProgram, AbiValueRepr, CallableEntry, EffectSummary,
    EmissionReadyCallEdge, EmissionReadyCallableEntry, EmissionReadyExecutable, EmissionReadyProgram,
    MaterializedCallEdge, MaterializedExecutable, MaterializedProgram, ReturnAbi,
};
use super::super::body::{CallArg, CallSiteId, LoweredBlock, LoweredBody, LoweredStep, ValueId};
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::facts::FactValue;
use super::super::identity::{ExecutableKey, ExecutableNeed, FunctionId, RootId};
use super::super::scheduler::FatalError;
use super::super::semantic::{ActivationAnalysis, CallSiteKey, SelectedCallee};
use super::super::types::Ty;
use super::super::world::World;

/// Materializes one closed root into a backend-owned program snapshot.
///
/// The job reads the current `SemanticClosed(root)` payload, clones only the
/// reachable lowered bodies, prunes unreachable clauses, freezes each live
/// callsite to its selected callee executable, and settles executable effects
/// over the closed call graph. Missing semantic constituents are fatal:
/// materialization never reopens discovery.
pub(super) fn materialize_root(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let closed_fact = FactKey::SemanticClosed(root_id);
    let Some(closed_revision) = world.fact_revision(closed_fact.clone()) else {
        return Ok(JobEffects::wait_on(
            closed_fact,
            [super::super::Job::SealSemanticClosure(root_id)],
        ));
    };

    let closure = world.semantic_closure(root_id);
    if !semantic_closure_is_current(world, root_id) {
        return Ok(wait_for_fresh_closure(root_id));
    }
    let reads = vec![closed_fact];
    let mut executables = HashMap::new();

    for executable in &closure.executables {
        if world.fact_revision(FactKey::Executable(executable.clone())).is_none()
            || world
                .fact_revision(FactKey::ActivationAnalyzed(executable.activation.clone()))
                .is_none()
            || world
                .fact_revision(FactKey::ReturnType(executable.activation.clone()))
                .is_none()
            || world
                .fact_revision(FactKey::LoweredBody(executable.activation.function))
                .is_none()
        {
            return Ok(wait_for_fresh_closure(root_id));
        }

        let Some(analysis) = world.activation_analysis(&executable.activation).cloned() else {
            return Ok(wait_for_fresh_closure(root_id));
        };
        let Some(return_ty) = world.activation_return(&executable.activation) else {
            return Ok(wait_for_fresh_closure(root_id));
        };
        let body = prune_lowered_body(
            world.lowered_body(executable.activation.function),
            &analysis.reachable_clauses,
        );
        let callsite_args = collect_callsite_args(&body);
        let Some(call_edges) = materialize_call_edges(world, root_id, executable, &analysis, &callsite_args)? else {
            return Ok(wait_for_fresh_closure(root_id));
        };
        let effects = local_effects(&body, &call_edges);
        executables.insert(
            executable.clone(),
            MaterializedExecutable {
                return_ty,
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
        entry: closure.entry,
        executables,
    };
    let revision = world.define_materialized_program(root_id, program);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::MaterializedProgram(root_id), FactValue::presence(revision))],
        follow_up: vec![Job::DeriveAbiReady(root_id)],
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
    let Some(materialized_revision) = world.fact_revision(materialized_fact.clone()) else {
        return Ok(JobEffects::wait_on(materialized_fact, [Job::MaterializeRoot(root_id)]));
    };

    let reads = vec![materialized_fact];
    let materialized = world.materialized_program(root_id);
    let executables = materialized
        .executables
        .iter()
        .map(|(key, executable)| (key.clone(), derive_abi_ready_executable(world, key, executable)))
        .collect::<HashMap<_, _>>();
    let callable_entries = derive_callable_entries(world, root_id, &executables)?;
    let program = AbiReadyProgram {
        materialized_revision,
        entry: materialized.entry,
        executables,
        callable_entries,
    };
    let revision = world.define_abi_ready_program(root_id, program);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::AbiReadyProgram(root_id), FactValue::presence(revision))],
        follow_up: vec![Job::DeriveEmissionReady(root_id)],
        ..JobEffects::default()
    })
}

/// Derives one emission-ready inventory from one ABI-ready closed artifact.
///
/// This job consumes only `AbiReadyProgram(root)`. It assigns stable
/// emission-local executable indices, rewrites executable cross-references to
/// those indices, and preserves Compiler2 keys only as descriptive inventory
/// payload.
pub(super) fn derive_emission_ready(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let abi_ready_fact = FactKey::AbiReadyProgram(root_id);
    let Some(abi_ready_revision) = world.fact_revision(abi_ready_fact.clone()) else {
        return Ok(JobEffects::wait_on(abi_ready_fact, [Job::DeriveAbiReady(root_id)]));
    };

    let reads = vec![abi_ready_fact];
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
    let revision = world.define_emission_ready_program(root_id, program);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::EmissionReadyProgram(root_id), FactValue::presence(revision))],
        ..JobEffects::default()
    })
}

fn materialize_call_edges(
    world: &mut World<'_>,
    root_id: RootId,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<HashMap<CallSiteId, MaterializedCallEdge>>, FatalError> {
    let mut call_edges = HashMap::new();
    for callsite in &analysis.callsites {
        let key = CallSiteKey {
            activation: executable.activation.clone(),
            callsite: *callsite,
        };
        if world.fact_revision(FactKey::CallSiteSummary(key.clone())).is_none() {
            return Ok(None);
        }
        let Some(summary) = world.callsite_summary(&key).cloned() else {
            return Ok(None);
        };
        let SelectedCallee::Function(function) = summary.callee else {
            return Err(incomplete_semantic_plan(
                world,
                root_id,
                "materialization cannot lower unresolved named call targets",
            ));
        };
        let callee = ExecutableKey {
            activation: world.activation_key(root_id, function, &summary.input_types),
            need: summary.need,
        };
        let extern_marshals = if let LoweredBody::Extern { signature } = world.lowered_body(function) {
            let Some(args) = callsite_args.get(callsite) else {
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
        call_edges.insert(
            *callsite,
            MaterializedCallEdge {
                callee,
                return_ty: summary.return_ty,
                extern_marshals,
            },
        );
    }
    Ok(Some(call_edges))
}

fn prune_lowered_body(body: LoweredBody, reachable_clauses: &[u32]) -> LoweredBody {
    match body {
        LoweredBody::Extern { .. } => body,
        LoweredBody::Clauses { clauses, generated } => LoweredBody::Clauses {
            clauses: reachable_clauses
                .iter()
                .map(|clause_id| clauses[*clause_id as usize].clone())
                .collect(),
            generated,
        },
    }
}

fn collect_callsite_args(body: &LoweredBody) -> HashMap<CallSiteId, Vec<CallArg>> {
    let mut out = HashMap::new();
    match body {
        LoweredBody::Extern { .. } => {}
        LoweredBody::Clauses { clauses, .. } => {
            for clause in clauses {
                collect_step_call_args(&clause.projections, &mut out);
                collect_block_call_args(&clause.body, &mut out);
            }
        }
    }
    out
}

fn collect_block_call_args(block: &LoweredBlock, out: &mut HashMap<CallSiteId, Vec<CallArg>>) {
    collect_step_call_args(&block.steps, out);
}

fn collect_step_call_args(steps: &[LoweredStep], out: &mut HashMap<CallSiteId, Vec<CallArg>>) {
    for step in steps {
        match step {
            LoweredStep::DirectCall { callsite, args, .. } | LoweredStep::ClosureCall { callsite, args, .. } => {
                out.insert(*callsite, args.clone());
            }
            LoweredStep::If {
                then_block, else_block, ..
            } => {
                collect_block_call_args(then_block, out);
                collect_block_call_args(else_block, out);
            }
            _ => {}
        }
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
        LoweredBody::Clauses { clauses, .. } => {
            let mut effects = EffectSummary::default();
            for clause in clauses {
                effects.union_with(step_effects(&clause.projections, call_edges));
                effects.union_with(block_effects(&clause.body, call_edges));
            }
            effects
        }
    }
}

fn block_effects(block: &LoweredBlock, call_edges: &HashMap<CallSiteId, MaterializedCallEdge>) -> EffectSummary {
    step_effects(&block.steps, call_edges)
}

fn step_effects(steps: &[LoweredStep], call_edges: &HashMap<CallSiteId, MaterializedCallEdge>) -> EffectSummary {
    let mut effects = EffectSummary::default();
    for step in steps {
        match step {
            LoweredStep::Tuple { .. } | LoweredStep::List { .. } | LoweredStep::Lambda { .. } => {
                effects.allocates = true;
            }
            LoweredStep::ClosureCall { callsite, .. } if !call_edges.contains_key(callsite) => {
                effects.calls_opaque = true;
            }
            LoweredStep::If {
                then_block, else_block, ..
            } => {
                effects.union_with(block_effects(then_block, call_edges));
                effects.union_with(block_effects(else_block, call_edges));
            }
            _ => {}
        }
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
                let Some(callee_effects) = snapshot.get(&edge.callee).copied() else {
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

fn derive_abi_ready_executable(
    world: &mut World<'_>,
    key: &ExecutableKey,
    executable: &MaterializedExecutable,
) -> AbiReadyExecutable {
    let param_reprs = key
        .activation
        .input
        .iter()
        .copied()
        .map(|ty| abi_value_repr(world, ty))
        .collect();
    let value_reprs = executable
        .value_types
        .iter()
        .map(|(value, ty)| (*value, abi_value_repr(world, *ty)))
        .collect();
    let call_edges = executable
        .call_edges
        .iter()
        .map(|(callsite, edge)| {
            (
                *callsite,
                AbiReadyCallEdge {
                    callee: edge.callee.clone(),
                    return_ty: edge.return_ty,
                    return_abi: return_abi(world, edge.return_ty, edge.callee.need),
                    extern_marshals: edge.extern_marshals.clone(),
                },
            )
        })
        .collect();
    AbiReadyExecutable {
        return_ty: executable.return_ty,
        return_abi: return_abi(world, executable.return_ty, key.need),
        param_reprs,
        value_types: executable.value_types.clone(),
        value_reprs,
        effects: executable.effects,
        body: executable.body.clone(),
        call_edges,
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
                callee: executable_index.get(&edge.callee).copied().ok_or_else(|| {
                    incomplete_semantic_plan(
                        world,
                        root_id,
                        format!(
                            "ABI-ready call edge {:?} -> {:?} points outside the executable inventory",
                            key, edge.callee
                        ),
                    )
                })?,
                extern_marshals: edge.extern_marshals.clone(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    call_edges.sort_by_key(|edge| edge.callsite.as_u32());
    Ok(EmissionReadyExecutable {
        key,
        return_ty: executable.return_ty,
        return_abi: executable.return_abi.clone(),
        param_reprs: executable.param_reprs.clone(),
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
        let named_refs = named_function_refs(&executable.body);
        callable_entries_in_body(world, root_id, executables, executable, &named_refs, &mut entries)?;
    }
    entries.sort_by(compare_callable_entries);
    entries.dedup_by(|left, right| left.target == right.target && left.capture_count == right.capture_count);
    Ok(entries)
}

fn named_function_refs(body: &LoweredBody) -> HashMap<ValueId, (String, usize)> {
    let mut named = HashMap::new();
    match body {
        LoweredBody::Extern { .. } => {}
        LoweredBody::Clauses { clauses, .. } => {
            for clause in clauses {
                collect_named_function_refs(&clause.projections, &mut named);
                collect_named_function_refs(&clause.body.steps, &mut named);
            }
        }
    }
    named
}

fn collect_named_function_refs(steps: &[LoweredStep], named: &mut HashMap<ValueId, (String, usize)>) {
    for step in steps {
        match step {
            LoweredStep::NamedFunctionRef { value, name, arity } => {
                named.insert(*value, (name.clone(), *arity));
            }
            LoweredStep::If {
                then_block, else_block, ..
            } => {
                collect_named_function_refs(&then_block.steps, named);
                collect_named_function_refs(&else_block.steps, named);
            }
            LoweredStep::Const { .. }
            | LoweredStep::Tuple { .. }
            | LoweredStep::List { .. }
            | LoweredStep::FunctionRef { .. }
            | LoweredStep::DirectCall { .. }
            | LoweredStep::ClosureCall { .. }
            | LoweredStep::Lambda { .. }
            | LoweredStep::BinaryOp { .. }
            | LoweredStep::UnaryOp { .. }
            | LoweredStep::MapIndex { .. }
            | LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertTuple { .. }
            | LoweredStep::TupleField { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::AssertSame { .. }
            | LoweredStep::SplitList { .. } => {}
        }
    }
}

fn callable_entries_in_body(
    world: &mut World<'_>,
    root_id: RootId,
    executables: &HashMap<ExecutableKey, AbiReadyExecutable>,
    executable: &AbiReadyExecutable,
    named_refs: &HashMap<ValueId, (String, usize)>,
    out: &mut Vec<CallableEntry>,
) -> Result<(), FatalError> {
    match &executable.body {
        LoweredBody::Extern { .. } => Ok(()),
        LoweredBody::Clauses { clauses, .. } => {
            for clause in clauses {
                callable_entries_in_steps(
                    world,
                    root_id,
                    executables,
                    executable,
                    named_refs,
                    &clause.projections,
                    out,
                )?;
                callable_entries_in_steps(
                    world,
                    root_id,
                    executables,
                    executable,
                    named_refs,
                    &clause.body.steps,
                    out,
                )?;
            }
            Ok(())
        }
    }
}

fn callable_entries_in_steps(
    world: &mut World<'_>,
    root_id: RootId,
    executables: &HashMap<ExecutableKey, AbiReadyExecutable>,
    executable: &AbiReadyExecutable,
    named_refs: &HashMap<ValueId, (String, usize)>,
    steps: &[LoweredStep],
    out: &mut Vec<CallableEntry>,
) -> Result<(), FatalError> {
    for step in steps {
        match step {
            LoweredStep::DirectCall { callsite, args, .. } => {
                record_callable_boundary_args(
                    world,
                    root_id,
                    executables,
                    executable,
                    named_refs,
                    *callsite,
                    None,
                    args,
                    out,
                )?;
            }
            LoweredStep::ClosureCall {
                callsite, callee, args, ..
            } => {
                record_callable_boundary_args(
                    world,
                    root_id,
                    executables,
                    executable,
                    named_refs,
                    *callsite,
                    Some(*callee),
                    args,
                    out,
                )?;
            }
            LoweredStep::If {
                then_block, else_block, ..
            } => {
                callable_entries_in_steps(
                    world,
                    root_id,
                    executables,
                    executable,
                    named_refs,
                    &then_block.steps,
                    out,
                )?;
                callable_entries_in_steps(
                    world,
                    root_id,
                    executables,
                    executable,
                    named_refs,
                    &else_block.steps,
                    out,
                )?;
            }
            LoweredStep::Const { .. }
            | LoweredStep::Tuple { .. }
            | LoweredStep::List { .. }
            | LoweredStep::FunctionRef { .. }
            | LoweredStep::NamedFunctionRef { .. }
            | LoweredStep::Lambda { .. }
            | LoweredStep::BinaryOp { .. }
            | LoweredStep::UnaryOp { .. }
            | LoweredStep::MapIndex { .. }
            | LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertTuple { .. }
            | LoweredStep::TupleField { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::AssertSame { .. }
            | LoweredStep::SplitList { .. } => {}
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn record_callable_boundary_args(
    world: &mut World<'_>,
    root_id: RootId,
    executables: &HashMap<ExecutableKey, AbiReadyExecutable>,
    executable: &AbiReadyExecutable,
    named_refs: &HashMap<ValueId, (String, usize)>,
    callsite: CallSiteId,
    closure_callee: Option<ValueId>,
    args: &[CallArg],
    out: &mut Vec<CallableEntry>,
) -> Result<(), FatalError> {
    for (arg_index, arg) in args.iter().enumerate() {
        if let Some((name, arity)) = named_refs.get(&arg.value) {
            return Err(incomplete_semantic_plan(
                world,
                root_id,
                format!(
                    "callable boundary at callsite {} carries unresolved named function ref `&{}/{}`",
                    callsite.as_u32(),
                    name,
                    arity
                ),
            ));
        }

        let arg_ty = executable
            .value_types
            .get(&arg.value)
            .copied()
            .expect("ABI-ready executables should carry settled types for every call argument value");
        match resolve_callable_entries_for_type(world, root_id, executables, arg_ty)? {
            CallableResolution::NotCallable => {
                if boundary_expects_callable(world, executable, callsite, closure_callee, arg_index) {
                    return Err(incomplete_semantic_plan(
                        world,
                        root_id,
                        format!(
                            "callable boundary at callsite {} expects a resolved callable entry for arg {}",
                            callsite.as_u32(),
                            arg_index
                        ),
                    ));
                }
            }
            CallableResolution::Opaque => {
                return Err(incomplete_semantic_plan(
                    world,
                    root_id,
                    format!(
                        "callable boundary at callsite {} carries an opaque callable arg {}",
                        callsite.as_u32(),
                        arg_index
                    ),
                ));
            }
            CallableResolution::Resolved(entries) => out.extend(entries),
        }
    }
    Ok(())
}

fn boundary_expects_callable(
    world: &mut World<'_>,
    executable: &AbiReadyExecutable,
    callsite: CallSiteId,
    closure_callee: Option<ValueId>,
    arg_index: usize,
) -> bool {
    let Some(edge) = executable.call_edges.get(&callsite) else {
        return false;
    };
    let offset = closure_callee
        .and_then(|callee| executable.value_types.get(&callee))
        .and_then(|callee_ty| world.types().closure_lit_parts(callee_ty))
        .map_or(0, |parts| parts.captures.len());
    let Some(expected_ty) = edge.callee.activation.input.get(offset + arg_index) else {
        return false;
    };
    world.types_mut().callable_clauses(expected_ty).is_some()
}

fn resolve_callable_entries_for_type(
    world: &mut World<'_>,
    root_id: RootId,
    executables: &HashMap<ExecutableKey, AbiReadyExecutable>,
    ty: Ty,
) -> Result<CallableResolution, FatalError> {
    let Some(clauses) = world.types_mut().callable_clauses(&ty) else {
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
        let function = FunctionId::from_u32(closure.target.0);
        let capture_count = closure.captures.len();
        let fixed_arity = clause.args.len();
        let variadic = world.function_variadic(function);
        let mut matched = false;
        for (target, target_executable) in executables.iter().filter(|(key, _)| {
            key.activation.function == function
                && key.need == ExecutableNeed::Value
                && has_capture_prefix(&key.activation.input, &closure.captures)
                && callable_entry_arity_matches(key, capture_count, fixed_arity, variadic)
        }) {
            matched = true;
            entries.push(CallableEntry {
                target: target.clone(),
                capture_count,
                param_reprs: target_executable.param_reprs.clone(),
                return_ty: target_executable.return_ty,
                return_abi: target_executable.return_abi.clone(),
            });
        }
        if !matched {
            return Err(incomplete_semantic_plan(
                world,
                root_id,
                format!(
                    "callable entry target {} with {} capture(s) and arity {} is missing from the closed executable frontier",
                    function.as_u32(),
                    capture_count,
                    fixed_arity
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

fn has_capture_prefix(input: &[Ty], captures: &[Ty]) -> bool {
    input.starts_with(captures)
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

fn return_abi(world: &mut World<'_>, return_ty: Ty, need: ExecutableNeed) -> ReturnAbi {
    match need {
        ExecutableNeed::Value => ReturnAbi::Value(abi_value_repr(world, return_ty)),
        ExecutableNeed::TupleFields(arity) => ReturnAbi::TupleFields(
            world
                .types_mut()
                .tuple_projections(&return_ty, arity)
                .into_iter()
                .map(|field| abi_value_repr(world, field))
                .collect(),
        ),
    }
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

fn semantic_closure_is_current(world: &World<'_>, root_id: RootId) -> bool {
    world
        .semantic_closure_dependencies(root_id)
        .iter()
        .all(|(fact, revision)| world.fact_revision(fact.clone()) == Some(*revision))
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

fn wait_for_fresh_closure(root_id: RootId) -> JobEffects {
    JobEffects::wait_on(
        FactKey::SemanticClosed(root_id),
        [super::super::Job::SealSemanticClosure(root_id)],
    )
}
