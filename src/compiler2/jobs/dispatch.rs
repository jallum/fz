//! Compiler2 guard and entry-dispatch jobs.
//!
//! This module owns the shared-dispatch layer for Compiler2. It reifies named
//! dispatch-pure helpers into `PatternGuardDispatch`, plans ordered function
//! entry dispatch from clause heads, and keeps both facts keyed by
//! `FunctionId`.

use std::collections::{HashMap, HashSet};

use super::super::drive::{FactKey, Job, JobEffects};
use super::super::facts::FactValue;
use super::super::identity::{FunctionDef, FunctionId};
use super::super::namespace::{Namespace, NamespaceSymbol};
use super::super::scheduler::FatalError;
use super::super::types::Ty;
use super::super::world::World;
use crate::ast::{Expr, FnDef, Pattern, Spanned};
use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{
    PatternBodyId, PatternDispatchError, PatternGuardDispatch, PatternGuardExpr, PatternRow, PatternSubjectRef,
    SourcePatternError, SourcePatternRows, guard_dispatch_from_fn_def,
    pattern_dispatch_from_source_with_guard_resolver,
};

#[derive(Debug, Clone)]
pub(super) struct GuardCall {
    name: String,
    arity: usize,
    span: Span,
}

/// Reifies one dispatch-pure helper into the shared guard-dispatch artifact.
///
/// The job stays at the function-definition layer. It waits on missing helper
/// definitions, rejects impure helper bodies or cycles with diagnostics, and
/// publishes one `GuardDispatch(function)` fact when the helper is reifiable.
pub(super) fn reify_guard_dispatch(world: &mut World<'_>, function: FunctionId) -> Result<JobEffects, FatalError> {
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };

    let def = world.function_definition(function);
    if def.legacy_ast.is_macro {
        return Err(emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!(
                    "compiler2 cannot reify macro `{}` as a dispatch-pure helper",
                    function_label(&def.legacy_ast)
                ),
                def.legacy_ast.span,
            ),
        ));
    }

    let mut reads = Vec::new();
    let mut waits = HashSet::new();
    let mut follow_up = HashSet::new();
    let mut seen = HashSet::new();
    let mut stack = Vec::new();
    collect_requirements(
        world,
        function,
        &mut reads,
        &mut waits,
        &mut follow_up,
        &mut seen,
        &mut stack,
    )?;
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads,
            waits: waits.into_iter().collect(),
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    let mut cache = HashMap::new();
    let mut build_stack = Vec::new();
    let dispatch = build_guard_dispatch(world, function, &mut cache, &mut build_stack)
        .map_err(|err| emit_guard_dispatch_error(world, function, def.legacy_ast.span, err))?;
    let revision = world.define_guard_dispatch(function, dispatch);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::GuardDispatch(function), FactValue::presence(revision))],
        ..JobEffects::default()
    })
}

/// Plans ordered function entry selection from clause heads and guards.
///
/// The job consumes the function definition plus any helper guard-dispatch
/// facts its clause guards call. When every dependency is ready, it publishes
/// one `EntryDispatch(function)` fact carrying the shared pattern-dispatch
/// artifact that later semantic jobs will consume.
pub(super) fn plan_entry_dispatch(world: &mut World<'_>, function: FunctionId) -> Result<JobEffects, FatalError> {
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };

    let def = world.function_definition(function);
    if def.legacy_ast.is_macro {
        return Err(emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!(
                    "compiler2 cannot plan macro `{}` as runtime entry dispatch",
                    function_label(&def.legacy_ast)
                ),
                def.legacy_ast.span,
            ),
        ));
    }

    let mut reads = vec![FactKey::FunctionDefined(function)];
    let module = def.owner_module;
    if !module.is_global() {
        let module_fact = FactKey::ModuleDefined(module);
        if world.fact_revision(module_fact.clone()).is_some() {
            reads.push(module_fact);
        } else {
            return Ok(JobEffects::wait_on(module_fact, [Job::DefineModule(module)]));
        }
    }
    let mut waits = HashSet::new();
    let mut follow_up = HashSet::new();
    for referenced in world.function_type_refs(function).iter().cloned() {
        let fact = FactKey::TypeDefined(referenced.clone());
        if world.fact_revision(fact.clone()).is_some() {
            reads.push(fact);
        } else {
            waits.insert(fact);
            follow_up.insert(Job::DeriveTypeDef(referenced));
        }
    }
    for call in collect_guard_calls_in_guards(&def.legacy_ast)
        .map_err(|span| emit_entry_guard_error(world, function, span, "are not dispatch-pure"))?
    {
        let callee = resolve_guard_callee(world, def.namespace, &call)?;
        let fact = FactKey::GuardDispatch(callee);
        if world.fact_revision(fact.clone()).is_some() {
            reads.push(fact);
        } else {
            waits.insert(fact);
            follow_up.insert(Job::ReifyGuardDispatch(callee));
        }
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads,
            waits: waits.into_iter().collect(),
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    let source_patterns = entry_source_patterns(world, function, &def)?;
    let mut resolver = |name: &str, arity: usize, args: Vec<PatternGuardExpr<Ty>>| {
        let callee = resolve_guard_callee_checked(world, def.namespace, name, arity);
        Ok(Some(PatternGuardExpr::Dispatch {
            inputs: args,
            dispatch: Box::new(world.guard_dispatch(callee)),
        }))
    };
    let plan = pattern_dispatch_from_source_with_guard_resolver(source_patterns, &mut resolver)
        .map_err(|error| emit_entry_dispatch_error(world, function, def.legacy_ast.span, error))?;
    let revision = world.define_entry_dispatch(function, plan);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::EntryDispatch(function), FactValue::presence(revision))],
        ..JobEffects::default()
    })
}

fn collect_requirements(
    world: &mut World<'_>,
    function: FunctionId,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
    seen: &mut HashSet<FunctionId>,
    stack: &mut Vec<FunctionId>,
) -> Result<(), FatalError> {
    if let Some(cycle_start) = stack.iter().position(|id| *id == function) {
        return Err(emit_cycle(world, function, &stack[cycle_start..]));
    }
    if !seen.insert(function) {
        return Ok(());
    }
    let Some(_) = world.function_defined_revision(function) else {
        waits.insert(FactKey::FunctionDefined(function));
        follow_up.extend(world.ensure_function_surface(function));
        return Ok(());
    };
    reads.push(FactKey::FunctionDefined(function));
    let def = world.function_definition(function);
    stack.push(function);
    for call in collect_guard_calls_in_fn(&def.legacy_ast)
        .map_err(|span| emit_guard_dispatch_error(world, function, span, SourcePatternError::UnsupportedGuardExpr))?
    {
        let callee = resolve_guard_callee(world, def.namespace, &call)?;
        collect_requirements(world, callee, reads, waits, follow_up, seen, stack)?;
    }
    stack.pop();
    Ok(())
}

fn build_guard_dispatch(
    world: &mut World<'_>,
    function: FunctionId,
    cache: &mut HashMap<FunctionId, PatternGuardDispatch<Ty>>,
    stack: &mut Vec<FunctionId>,
) -> Result<PatternGuardDispatch<Ty>, SourcePatternError> {
    if let Some(dispatch) = cache.get(&function) {
        return Ok(dispatch.clone());
    }
    if stack.contains(&function) {
        let def = world.function_definition(function);
        return Err(SourcePatternError::GuardCallCycle(
            def.legacy_ast.name.clone(),
            def.legacy_ast.arity(),
        ));
    }

    let def = world.function_definition(function);
    stack.push(function);
    let mut resolver = |name: &str, arity: usize, args: Vec<PatternGuardExpr<Ty>>| {
        let callee = resolve_guard_callee_checked(world, def.namespace, name, arity);
        let dispatch = build_guard_dispatch(world, callee, cache, stack)?;
        Ok(Some(PatternGuardExpr::Dispatch {
            inputs: args,
            dispatch: Box::new(dispatch),
        }))
    };
    let dispatch = guard_dispatch_from_fn_def(&def.legacy_ast, &mut resolver)?;
    stack.pop();
    cache.insert(function, dispatch.clone());
    Ok(dispatch)
}

fn entry_source_patterns(
    world: &mut World<'_>,
    _function: FunctionId,
    def: &FunctionDef,
) -> Result<SourcePatternRows<Ty>, FatalError> {
    let capture_patterns = def
        .capture_params
        .iter()
        .map(|name| Spanned::new(Pattern::Var(name.clone()), def.legacy_ast.span))
        .collect::<Vec<_>>();
    let input_count = capture_patterns.len() + def.legacy_ast.arity();
    if def.legacy_ast.extern_abi.is_some() {
        return Ok(SourcePatternRows {
            input_count,
            rows: vec![PatternRow {
                patterns: (0..input_count)
                    .map(|_| Spanned::new(Pattern::Wildcard, def.legacy_ast.span))
                    .collect(),
                preconditions: Vec::new(),
                guard: None,
                body_id: 0,
            }],
        });
    }

    let mut rows = Vec::with_capacity(def.legacy_ast.clauses.len());
    for (body_id, clause) in def.legacy_ast.clauses.iter().enumerate() {
        let mut preconditions = Vec::new();
        for (index, tokens) in clause.param_annotations.iter().enumerate() {
            let Some(tokens) = tokens else {
                continue;
            };
            let ty = world.resolve_type_expr_body(def.namespace, tokens).map_err(|error| {
                emit_job_diagnostic(
                    world,
                    Diagnostic::error(
                        codes::RESOLVE_TYPE_ALIAS,
                        format!(
                            "compiler2 could not resolve parameter annotation {} for `{}`: {}",
                            index + 1,
                            function_label(&def.legacy_ast),
                            error.msg
                        ),
                        error.span,
                    ),
                )
            })?;
            preconditions.push((PatternSubjectRef::Input((capture_patterns.len() + index) as u32), ty));
        }
        let mut patterns = capture_patterns.clone();
        patterns.extend(clause.params.clone());
        rows.push(PatternRow {
            patterns,
            preconditions,
            guard: clause.guard.clone(),
            body_id: body_id as PatternBodyId,
        });
    }

    Ok(SourcePatternRows { input_count, rows })
}

fn collect_guard_calls_in_guards(def: &FnDef) -> Result<Vec<GuardCall>, Span> {
    let mut calls = Vec::new();
    for clause in &def.clauses {
        if let Some(guard) = &clause.guard {
            collect_guard_calls_in_expr(guard, &mut calls)?;
        }
    }
    Ok(calls)
}

fn collect_guard_calls_in_fn(def: &FnDef) -> Result<Vec<GuardCall>, Span> {
    let mut calls = Vec::new();
    for clause in &def.clauses {
        if let Some(guard) = &clause.guard {
            collect_guard_calls_in_expr(guard, &mut calls)?;
        }
        collect_guard_calls_in_expr(&clause.body, &mut calls)?;
    }
    Ok(calls)
}

pub(super) fn collect_guard_calls_in_expr(expr: &Spanned<Expr>, out: &mut Vec<GuardCall>) -> Result<(), Span> {
    match &expr.node {
        Expr::Int(_) | Expr::Float(_) | Expr::Binary(_) | Expr::Atom(_) | Expr::Bool(_) | Expr::Nil | Expr::Var(_) => {
            Ok(())
        }
        Expr::Ascribe(inner, _) => collect_guard_calls_in_expr(inner, out),
        Expr::UnOp(_, inner) => collect_guard_calls_in_expr(inner, out),
        Expr::BinOp(_, left, right) => {
            collect_guard_calls_in_expr(left, out)?;
            collect_guard_calls_in_expr(right, out)
        }
        Expr::Call(target, args) => {
            let callee = match &target.node {
                Expr::Var(name) => Some((name.clone(), args.len())),
                Expr::FnRef { name, arity } if *arity == args.len() => Some((name.clone(), *arity)),
                _ => None,
            };
            let Some((name, arity)) = callee else {
                return Err(expr.span);
            };
            for arg in args {
                collect_guard_calls_in_expr(arg, out)?;
            }
            out.push(GuardCall {
                name,
                arity,
                span: expr.span,
            });
            Ok(())
        }
        Expr::FnRef { .. }
        | Expr::Capture(_)
        | Expr::CaptureArg(_)
        | Expr::List(_, _)
        | Expr::Tuple(_)
        | Expr::Bitstring(_)
        | Expr::Map(_)
        | Expr::MapUpdate(_, _)
        | Expr::Struct { .. }
        | Expr::Index(_, _)
        | Expr::ClosureCall(_, _)
        | Expr::If(_, _, _)
        | Expr::Case(_, _)
        | Expr::Cond(_)
        | Expr::With(_, _, _)
        | Expr::Receive { .. }
        | Expr::Match(_, _)
        | Expr::Block(_)
        | Expr::Lambda(_)
        | Expr::Quote(_)
        | Expr::Unquote(_) => Err(expr.span),
    }
}

pub(super) fn resolve_guard_callee(
    world: &mut World<'_>,
    namespace: Namespace,
    call: &GuardCall,
) -> Result<FunctionId, FatalError> {
    match world.lookup_callable_namespace(namespace, &call.name, call.arity) {
        Some(NamespaceSymbol::Function(function)) => Ok(function),
        Some(NamespaceSymbol::Macro(_)) => Err(emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!(
                    "compiler2 guard calls must be expanded before dispatch planning: `{}/{}`",
                    call.name, call.arity
                ),
                call.span,
            ),
        )),
        Some(NamespaceSymbol::Module(_)) | Some(NamespaceSymbol::Type(_)) | None => Err(emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNBOUND,
                format!(
                    "compiler2 guard call `{}/{}` is unresolved in this namespace",
                    call.name, call.arity
                ),
                call.span,
            ),
        )),
    }
}

pub(super) fn resolve_guard_callee_checked(
    world: &mut World<'_>,
    namespace: Namespace,
    name: &str,
    arity: usize,
) -> FunctionId {
    match world.lookup_callable_namespace(namespace, name, arity) {
        Some(NamespaceSymbol::Function(function)) => function,
        Some(NamespaceSymbol::Macro(_)) => {
            panic!("guard analysis should reject macro calls before building dispatch artifacts")
        }
        Some(NamespaceSymbol::Module(_)) | Some(NamespaceSymbol::Type(_)) | None => {
            panic!("guard analysis should reject unresolved helper calls before building dispatch artifacts")
        }
    }
}

fn emit_cycle(world: &World<'_>, function: FunctionId, cycle: &[FunctionId]) -> FatalError {
    let mut path = cycle
        .iter()
        .map(|function| function_label(&world.function_definition(*function).legacy_ast))
        .collect::<Vec<_>>();
    path.push(function_label(&world.function_definition(function).legacy_ast));
    emit_job_diagnostic(
        world,
        Diagnostic::error(
            codes::LOWER_UNSUPPORTED,
            format!("compiler2 guard helper cycle detected: {}", path.join(" -> ")),
            world.function_definition(function).legacy_ast.span,
        ),
    )
}

fn emit_guard_dispatch_error(
    world: &World<'_>,
    function: FunctionId,
    span: Span,
    error: SourcePatternError,
) -> FatalError {
    let label = function_label(&world.function_definition(function).legacy_ast);
    match error {
        SourcePatternError::UnsupportedGuardExpr => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 helper `{label}` is not dispatch-pure and cannot be reified into guard dispatch"),
                span,
            ),
        ),
        SourcePatternError::UnknownPinned(name) | SourcePatternError::UnknownGuardVar(name) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNBOUND,
                format!("compiler2 helper `{label}` references unknown guard name `{name}`"),
                span,
            ),
        ),
        SourcePatternError::GuardCallCycle(name, arity) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 guard helper cycle detected through `{name}/{arity}`"),
                span,
            ),
        ),
        SourcePatternError::DispatchMatrix(message) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 helper `{label}` could not be reified: {message}"),
                span,
            ),
        ),
        SourcePatternError::UnknownSubject(_)
        | SourcePatternError::RowPatternArity { .. }
        | SourcePatternError::NonMonotonicBodyId { .. } => {
            panic!("compiler2 built an invalid guard dispatch row set: {error:?}")
        }
        SourcePatternError::UnsupportedMapKey => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 helper `{label}` uses an unsupported map key in a guard pattern"),
                span,
            ),
        ),
    }
}

fn emit_entry_guard_error(world: &World<'_>, function: FunctionId, span: Span, reason: &str) -> FatalError {
    emit_job_diagnostic(
        world,
        Diagnostic::error(
            codes::LOWER_UNSUPPORTED,
            format!(
                "compiler2 entry guards for `{}` {reason} and cannot be planned",
                function_label(&world.function_definition(function).legacy_ast)
            ),
            span,
        ),
    )
}

fn emit_entry_dispatch_error(
    world: &World<'_>,
    function: FunctionId,
    span: Span,
    error: PatternDispatchError,
) -> FatalError {
    let label = function_label(&world.function_definition(function).legacy_ast);
    match error {
        PatternDispatchError::SourcePattern(SourcePatternError::UnsupportedGuardExpr) => {
            emit_entry_guard_error(world, function, span, "are not dispatch-pure")
        }
        PatternDispatchError::SourcePattern(SourcePatternError::UnknownPinned(name))
        | PatternDispatchError::SourcePattern(SourcePatternError::UnknownGuardVar(name)) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNBOUND,
                format!("compiler2 entry guard for `{label}` references unknown guard name `{name}`"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(SourcePatternError::UnsupportedMapKey) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 entry dispatch for `{label}` uses an unsupported map key"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(
            SourcePatternError::UnknownSubject(_)
            | SourcePatternError::RowPatternArity { .. }
            | SourcePatternError::NonMonotonicBodyId { .. }
            | SourcePatternError::GuardCallCycle(_, _)
            | SourcePatternError::DispatchMatrix(_),
        ) => panic!("compiler2 built an invalid entry-dispatch row set: {error:?}"),
        PatternDispatchError::MatrixBuild(error) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 could not build entry dispatch for `{label}`: {error:?}"),
                span,
            ),
        ),
        PatternDispatchError::Compile(error) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 could not compile entry dispatch for `{label}`: {error:?}"),
                span,
            ),
        ),
    }
}

fn function_label(def: &FnDef) -> String {
    format!("{}/{}", def.name, def.arity())
}

fn emit_job_diagnostic(world: &World<'_>, diagnostic: Diagnostic) -> FatalError {
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    FatalError
}
