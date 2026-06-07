//! Compiler2 guard-dispatch jobs.
//!
//! This module reifies one named helper function at a time into the shared
//! `dispatch_matrix::pattern::PatternGuardDispatch` shape. The job reads the
//! frozen function definitions it transitively depends on, rejects unsupported
//! helper bodies with diagnostics, and publishes one reusable fact keyed by
//! `FunctionId`.

use std::collections::{HashMap, HashSet};

use crate::ast::{Expr, FnDef, Spanned};
use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{
    PatternGuardDispatch, PatternGuardExpr, SourcePatternError, guard_dispatch_from_fn_def,
};

use super::super::drive::{FactKey, JobEffects};
use super::super::identity::FunctionId;
use super::super::namespace::{Namespace, NamespaceSymbol};
use super::super::scheduler::FatalError;
use super::super::world::World;

#[derive(Debug, Clone)]
struct GuardCall {
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
    let function_fact = FactKey::FunctionDefined(function);
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(JobEffects::wait_on(function_fact, []));
    };

    let def = world.function_definition(function);
    if def.ast.is_macro {
        return Err(emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!(
                    "compiler2 cannot reify macro `{}` as a dispatch-pure helper",
                    function_label(&def.ast)
                ),
                def.ast.span,
            ),
        ));
    }

    let mut reads = Vec::new();
    let mut waits = HashSet::new();
    let mut seen = HashSet::new();
    let mut stack = Vec::new();
    collect_requirements(world, function, &mut reads, &mut waits, &mut seen, &mut stack)?;
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads,
            waits: waits.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    let mut cache = HashMap::new();
    let mut build_stack = Vec::new();
    let dispatch = build_guard_dispatch(world, function, &mut cache, &mut build_stack)
        .map_err(|err| emit_guard_dispatch_error(world, function, def.ast.span, err))?;
    let revision = world.define_guard_dispatch(function, dispatch);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::GuardDispatch(function), revision)],
        ..JobEffects::default()
    })
}

fn collect_requirements(
    world: &World<'_>,
    function: FunctionId,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
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
        return Ok(());
    };
    reads.push(FactKey::FunctionDefined(function));
    let def = world.function_definition(function);
    stack.push(function);
    for call in collect_guard_calls_in_fn(&def.ast)
        .map_err(|span| emit_guard_dispatch_error(world, function, span, SourcePatternError::UnsupportedGuardExpr))?
    {
        let callee = resolve_guard_callee(world, def.namespace, &call)?;
        collect_requirements(world, callee, reads, waits, seen, stack)?;
    }
    stack.pop();
    Ok(())
}

fn build_guard_dispatch(
    world: &World<'_>,
    function: FunctionId,
    cache: &mut HashMap<FunctionId, PatternGuardDispatch>,
    stack: &mut Vec<FunctionId>,
) -> Result<PatternGuardDispatch, SourcePatternError> {
    if let Some(dispatch) = cache.get(&function) {
        return Ok(dispatch.clone());
    }
    if stack.contains(&function) {
        let def = world.function_definition(function);
        return Err(SourcePatternError::GuardCallCycle(
            def.ast.name.clone(),
            def.ast.arity(),
        ));
    }

    let def = world.function_definition(function);
    stack.push(function);
    let mut resolver = |name: &str, arity: usize, args: Vec<PatternGuardExpr>| {
        let callee = resolve_guard_callee_checked(world, def.namespace, name, arity);
        let dispatch = build_guard_dispatch(world, callee, cache, stack)?;
        Ok(Some(PatternGuardExpr::Dispatch {
            inputs: args,
            dispatch: Box::new(dispatch),
        }))
    };
    let dispatch = guard_dispatch_from_fn_def(&def.ast, &mut resolver)?;
    stack.pop();
    cache.insert(function, dispatch.clone());
    Ok(dispatch)
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

fn collect_guard_calls_in_expr(expr: &Spanned<Expr>, out: &mut Vec<GuardCall>) -> Result<(), Span> {
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

fn resolve_guard_callee(world: &World<'_>, namespace: Namespace, call: &GuardCall) -> Result<FunctionId, FatalError> {
    match world.lookup_callable_namespace(namespace, &call.name, call.arity) {
        Some(NamespaceSymbol::Function(function)) => Ok(function),
        Some(NamespaceSymbol::Macro(_)) => Err(emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!(
                    "compiler2 guard helper calls must be expanded before reification: `{}/{}`",
                    call.name, call.arity
                ),
                call.span,
            ),
        )),
        Some(NamespaceSymbol::Module(_)) | None => Err(emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNBOUND,
                format!(
                    "compiler2 guard helper call `{}/{}` is unresolved in this namespace",
                    call.name, call.arity
                ),
                call.span,
            ),
        )),
    }
}

fn resolve_guard_callee_checked(world: &World<'_>, namespace: Namespace, name: &str, arity: usize) -> FunctionId {
    match world.lookup_callable_namespace(namespace, name, arity) {
        Some(NamespaceSymbol::Function(function)) => function,
        Some(NamespaceSymbol::Macro(_)) => {
            panic!("guard analysis should reject macro calls before building guard dispatch")
        }
        Some(NamespaceSymbol::Module(_)) | None => {
            panic!("guard analysis should reject unresolved helper calls before building guard dispatch")
        }
    }
}

fn emit_cycle(world: &World<'_>, function: FunctionId, cycle: &[FunctionId]) -> FatalError {
    let mut path = cycle
        .iter()
        .map(|function| function_label(&world.function_definition(*function).ast))
        .collect::<Vec<_>>();
    path.push(function_label(&world.function_definition(function).ast));
    emit_job_diagnostic(
        world,
        Diagnostic::error(
            codes::LOWER_UNSUPPORTED,
            format!("compiler2 guard helper cycle detected: {}", path.join(" -> ")),
            world.function_definition(function).ast.span,
        ),
    )
}

fn emit_guard_dispatch_error(
    world: &World<'_>,
    function: FunctionId,
    span: Span,
    error: SourcePatternError,
) -> FatalError {
    let label = function_label(&world.function_definition(function).ast);
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

fn function_label(def: &FnDef) -> String {
    format!("{}/{}", def.name, def.arity())
}

fn emit_job_diagnostic(world: &World<'_>, diagnostic: Diagnostic) -> FatalError {
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    FatalError
}
