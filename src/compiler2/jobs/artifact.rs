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
    AbiReadyCallEdge, AbiReadyExecutable, AbiReadyProgram, AbiValueRepr, EffectSummary, MaterializedCallEdge,
    MaterializedExecutable, MaterializedProgram, ReturnAbi,
};
use super::super::body::{CallArg, CallSiteId, LoweredBlock, LoweredBody, LoweredStep};
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::facts::FactValue;
use super::super::identity::{ExecutableKey, ExecutableNeed, RootId};
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
    let program = AbiReadyProgram {
        materialized_revision,
        entry: materialized.entry,
        executables,
    };
    let revision = world.define_abi_ready_program(root_id, program);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::AbiReadyProgram(root_id), FactValue::presence(revision))],
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
