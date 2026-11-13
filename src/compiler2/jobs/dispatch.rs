//! Compiler2 guard and entry-dispatch jobs.
//!
//! This module owns the shared-dispatch layer for Compiler2. It reifies named
//! dispatch-pure helpers into `PatternGuardDispatch`, plans ordered function
//! entry dispatch from clause heads, and keeps both facts keyed by
//! `FunctionId`.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;

use super::super::drive::{FactKey, JobEffects, current_uses};
use super::super::identity::{FunctionId, FunctionSource};
use super::super::namespace::{Namespace, NamespaceSymbol};
use super::super::scheduler::FatalError;
use super::super::types::Ty;
use super::super::world::World;
use crate::ast::{CallableName, Callee, Expr, Pattern, Spanned, UnOp, Var, VarContext};
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{
    GuardCallee, GuardExtern, LastResort, PatternDispatchError, PatternPinnedInput, PatternRow, SourcePatternError,
    SourcePatternRows, guard_dispatch_from_rows, pattern_dispatch_from_source_with_resolver,
};
use crate::function_surface::FunctionSurface;
use crate::source::Span;

#[derive(Debug, Clone)]
pub(super) struct GuardCall {
    callee: Callee,
    arity: usize,
    span: Span,
}

/// Reifies one dispatch-pure helper into the shared guard-dispatch artifact.
///
/// The job stays at the function-definition layer. It waits on missing helper
/// definitions, rejects impure helper bodies or cycles with diagnostics, and
/// publishes one `GuardDispatch(function)` fact when the helper is reifiable.
pub(super) fn reify_guard_dispatch(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
) -> Result<JobEffects, FatalError> {
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };

    let surface = world.function_surface(function);
    if surface.is_macro {
        return Err(emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!(
                    "compiler2 cannot reify macro `{}` as a dispatch-pure helper",
                    function_label(surface)
                ),
                surface.span,
            ),
        ));
    }
    let fn_span = surface.span;

    let mut reads = Vec::new();
    let mut waits = HashSet::new();
    let mut seen = HashSet::new();
    let mut stack = Vec::new();
    collect_requirements(world, tel, function, &mut reads, &mut waits, &mut seen, &mut stack)?;
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    }

    let mut cache = HashMap::new();
    let mut build_stack = Vec::new();
    let callee = build_guard_dispatch(world, function, &mut cache, &mut build_stack)
        .map_err(|err| emit_guard_dispatch_error(tel, world, function, fn_span, err))?;
    let changed = super::super::drive::ExecutionContext::new(world, tel).define_guard_dispatch(function, callee);
    Ok(JobEffects {
        reads: current_uses(reads),
        outputs: vec![FactKey::GuardDispatch(function)],
        changed: changed
            .then_some(FactKey::GuardDispatch(function))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

/// Plans ordered function entry selection from clause heads and guards.
///
/// The job asks for exactly what it reads: `FunctionDefined(function)`, the
/// `TypeDefined` and `StructDefined` facts its clause heads name, and the
/// `GuardDispatch` of each helper its guards call. It does not wait on
/// `ModuleDefined(owner_module)`, whose value it never consumes. When every
/// dependency is ready the job publishes one `EntryDispatch(function)` fact
/// carrying the shared pattern-dispatch artifact that later semantic jobs
/// consume.
pub(super) fn plan_entry_dispatch(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
) -> Result<JobEffects, FatalError> {
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };

    let (source, surface) = world.function_definition(function);
    let (source, surface) = (source.clone(), surface.clone());
    let mut reads = vec![FactKey::FunctionDefined(function)];
    let mut waits = HashSet::new();
    collect_annotation_requirements(world, function, &mut reads, &mut waits);
    for clause in &surface.clauses {
        for pattern in &clause.params {
            super::body::collect_local_pattern_requirements(
                world,
                tel,
                source.namespace,
                source.owner_module,
                source.owner,
                pattern,
                &mut reads,
                &mut waits,
            )?;
        }
    }
    for call in collect_guard_calls_in_guards(&surface)
        .map_err(|span| emit_entry_guard_error(tel, world, function, span, "are not dispatch-pure"))?
    {
        let callee = resolve_guard_callee(world, tel, source.namespace, &call)?;
        let fact = FactKey::GuardDispatch(callee);
        if world.has_fact(&fact) {
            reads.push(fact);
        } else {
            waits.insert(fact);
        }
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    }

    let source_patterns = entry_source_patterns(world, tel, function, &source, &surface)?
        .raising(LastResort::function_clause(&world.function_ref(function).elixir_name()));
    let namespace = source.namespace;
    let fn_span = surface.span;
    let redundancy_check = (source_patterns.rows.len() > 1).then(|| source_patterns.clone());
    let mut resolver = super::super::dispatch::SourcePatternResolver {
        world,
        namespace,
        owner: source.owner_module,
        guard: |world: &mut World, callee: &Callee, arity: usize| {
            let callee = resolve_guard_callee_checked(world, namespace, callee, arity);
            Ok(Some(world.guard_callee(callee)))
        },
    };
    let plan = match pattern_dispatch_from_source_with_resolver(source_patterns, &mut resolver) {
        Ok(plan) => plan,
        Err(error) => return Err(emit_entry_dispatch_error(tel, world, function, fn_span, error)),
    };
    if let Some(source_patterns) = redundancy_check {
        let redundant_rows = crate::dispatch_matrix::pattern::source::find_redundant_rows_with_resolver(
            &source_patterns,
            &plan,
            &mut resolver,
        );
        for redundant in redundant_rows {
            let always_matches_span = surface.clauses[redundant.always_matches as usize].span;
            let always_matches_line = world.source_map().borrow().locate(always_matches_span).line;
            let diagnostic = super::super::source_diagnostics::redundant_clause_diagnostic(
                surface.clauses[redundant.body_id as usize].span,
                always_matches_line,
            );
            super::super::drive::ExecutionContext::new(world, tel).emit_warning_once(diagnostic);
        }
    }
    let changed = super::super::drive::ExecutionContext::new(world, tel).define_entry_dispatch(function, Rc::new(plan));
    Ok(JobEffects {
        reads: current_uses(reads),
        outputs: vec![FactKey::EntryDispatch(function)],
        changed: changed
            .then_some(FactKey::EntryDispatch(function))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

/// The facts a function's parameter annotations are resolved against: the type
/// aliases they name and the structs behind any `%Mod{}` they spell. An entry
/// and a reified helper resolve annotations the same way, so both wait here.
fn collect_annotation_requirements(
    world: &World,
    function: FunctionId,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) {
    let type_facts = world
        .function_type_refs(function)
        .iter()
        .cloned()
        .map(FactKey::TypeDefined);
    let struct_facts = world
        .function_type_struct_refs(function)
        .iter()
        .copied()
        .map(FactKey::StructDefined);
    for fact in type_facts.chain(struct_facts) {
        if world.has_fact(&fact) {
            reads.push(fact);
        } else {
            waits.insert(fact);
        }
    }
}

fn collect_requirements(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    seen: &mut HashSet<FunctionId>,
    stack: &mut Vec<FunctionId>,
) -> Result<(), FatalError> {
    if let Some(cycle_start) = stack.iter().position(|id| *id == function) {
        return Err(emit_cycle(tel, world, function, &stack[cycle_start..]));
    }
    if !seen.insert(function) {
        return Ok(());
    }
    let Some(_) = world.function_defined_revision(function) else {
        waits.insert(FactKey::FunctionDefined(function));
        return Ok(());
    };
    reads.push(FactKey::FunctionDefined(function));
    let (source, surface) = world.function_definition(function);
    // An extern has no clauses to reify: a guard calls it as it is, and what
    // it needs to know is the wire its contract settles.
    if surface.extern_abi.is_some() {
        let contract = FactKey::FunctionContract(function);
        if world.has_fact(&contract) {
            reads.push(contract);
        } else {
            waits.insert(contract);
        }
        return Ok(());
    }
    let namespace = source.namespace;
    let owner_module = source.owner_module;
    let owner = source.owner;
    let surface = surface.clone();
    collect_annotation_requirements(world, function, reads, waits);
    stack.push(function);
    for clause in &surface.clauses {
        for pattern in &clause.params {
            super::body::collect_local_pattern_requirements(
                world,
                tel,
                namespace,
                owner_module,
                owner,
                pattern,
                reads,
                waits,
            )?;
        }
    }
    for call in collect_guard_calls_in_fn(&surface).map_err(|span| {
        emit_guard_dispatch_error(tel, world, function, span, SourcePatternError::UnsupportedGuardExpr)
    })? {
        let callee = resolve_guard_callee(world, tel, namespace, &call)?;
        collect_requirements(world, tel, callee, reads, waits, seen, stack)?;
    }
    stack.pop();
    Ok(())
}

fn build_guard_dispatch(
    world: &mut World,
    function: FunctionId,
    cache: &mut HashMap<FunctionId, GuardCallee<Ty>>,
    stack: &mut Vec<FunctionId>,
) -> Result<GuardCallee<Ty>, SourcePatternError> {
    if let Some(callee) = cache.get(&function) {
        return Ok(callee.clone());
    }
    if stack.contains(&function) {
        let surface = world.function_surface(function);
        return Err(SourcePatternError::GuardCallCycle(
            surface.name.clone(),
            surface.arity(),
        ));
    }

    let (source, surface) = world.function_definition(function);
    if surface.extern_abi.is_some() {
        let wire = world
            .extern_wire(function)
            .expect("an extern's wire is settled before its guard callee is built");
        let callee = GuardCallee::Extern(Arc::new(GuardExtern::new(
            wire.abi,
            &wire.symbol,
            &wire.params,
            wire.ret,
            wire.variadic,
        )?));
        cache.insert(function, callee.clone());
        return Ok(callee);
    }
    let namespace = source.namespace;
    let owner = source.owner_module;
    let surface = surface.clone();
    stack.push(function);
    let mut resolver = super::super::dispatch::SourcePatternResolver {
        world,
        namespace,
        owner,
        guard: |world: &mut World, callee: &Callee, arity: usize| {
            let callee = resolve_guard_callee_checked(world, namespace, callee, arity);
            Ok(Some(build_guard_dispatch(world, callee, cache, stack)?))
        },
    };
    let rows = super::super::dispatch::surface_pattern_rows(resolver.world, namespace, &surface, &[])?;
    let callee = GuardCallee::Helper(Arc::new(guard_dispatch_from_rows(&surface, rows, &mut resolver)?));
    stack.pop();
    cache.insert(function, callee.clone());
    Ok(callee)
}

fn entry_source_patterns(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
    source: &FunctionSource,
    surface: &FunctionSurface,
) -> Result<SourcePatternRows<Ty>, FatalError> {
    let capture_patterns = source
        .capture_params
        .iter()
        .map(|name| Spanned::new(Pattern::Var(name.clone()), surface.span))
        .collect::<Vec<_>>();
    let macro_caller_patterns = surface
        .is_macro
        .then(|| Spanned::new(Pattern::Wildcard, surface.span))
        .into_iter()
        .collect::<Vec<_>>();
    let macro_offset = macro_caller_patterns.len();
    let input_count = macro_offset + capture_patterns.len() + surface.arity();
    // A function entry has no enclosing scope of its own. What a lambda closed
    // over arrives as its leading inputs, and that capture prefix is the whole
    // of the snapshot its patterns may pin against.
    let captures = source
        .capture_params
        .iter()
        .enumerate()
        .map(|(index, name)| (name.clone(), (macro_offset + index) as u32))
        .collect::<Vec<_>>();
    if surface.extern_abi.is_some() {
        return Ok(SourcePatternRows::entry(
            input_count,
            vec![PatternRow {
                patterns: (0..input_count)
                    .map(|_| Spanned::new(Pattern::Wildcard, surface.span))
                    .collect(),
                preconditions: Vec::new(),
                guard: None,
                body_id: 0,
            }],
            captures,
        ));
    }

    let leading = [macro_caller_patterns, capture_patterns].concat();
    let rows = super::super::dispatch::surface_pattern_rows(world, source.namespace, surface, &leading)
        .map_err(|error| emit_guard_dispatch_error(tel, world, function, surface.span, error))?;

    Ok(SourcePatternRows::entry(input_count, rows, captures))
}

fn collect_guard_calls_in_guards(def: &FunctionSurface) -> Result<Vec<GuardCall>, Span> {
    let mut calls = Vec::new();
    for clause in &def.clauses {
        if let Some(guard) = &clause.guard {
            collect_guard_calls_in_expr(guard, &mut calls)?;
        }
    }
    Ok(calls)
}

fn collect_guard_calls_in_fn(def: &FunctionSurface) -> Result<Vec<GuardCall>, Span> {
    let mut calls = Vec::new();
    for clause in &def.clauses {
        if let Some(guard) = &clause.guard {
            collect_guard_calls_in_expr(guard, &mut calls)?;
        }
        collect_guard_calls_in_expr(&clause.body, &mut calls)?;
    }
    Ok(calls)
}

/// A zero-argument call a receive guard makes, hoisted out of the guard so the
/// receiver evaluates it before it parks. `name` is what the guard reads in
/// the call's place.
pub(super) struct HoistedGuardCall {
    pub(super) name: Var,
    pub(super) call: Spanned<Expr>,
}

/// Replaces each zero-argument call in `guard` with a fresh variable and
/// records the call in `hoisted`.
///
/// A receive matcher can run on the process that sends the message, so
/// whatever a guard reads from process state would name the sender. A call
/// with no arguments has no inputs but process state, so the receiver
/// evaluates it once, and the guard sees the result as a pinned value like any
/// other variable the guard reads from outside the pattern.
pub(super) fn hoist_zero_argument_guard_calls(
    guard: &Spanned<Expr>,
    hoisted: &mut Vec<HoistedGuardCall>,
) -> Spanned<Expr> {
    let node = match &guard.node {
        Expr::Call(_, args) if args.is_empty() => {
            let name = Var {
                name: "__fz_guard_call".to_string(),
                context: VarContext::Generated(hoisted.len() as u32),
            };
            hoisted.push(HoistedGuardCall {
                name: name.clone(),
                call: guard.clone(),
            });
            Expr::Var(name)
        }
        Expr::Call(target, args) => Expr::Call(
            target.clone(),
            args.iter()
                .map(|arg| hoist_zero_argument_guard_calls(arg, hoisted))
                .collect(),
        ),
        Expr::Ascribe(inner, ty) => {
            Expr::Ascribe(Box::new(hoist_zero_argument_guard_calls(inner, hoisted)), ty.clone())
        }
        Expr::UnOp(op, inner) => Expr::UnOp(*op, Box::new(hoist_zero_argument_guard_calls(inner, hoisted))),
        Expr::BinOp(op, lhs, rhs) => Expr::BinOp(
            *op,
            Box::new(hoist_zero_argument_guard_calls(lhs, hoisted)),
            Box::new(hoist_zero_argument_guard_calls(rhs, hoisted)),
        ),
        other => other.clone(),
    };
    Spanned::new(node, guard.span)
}

/// Whether dispatch can evaluate `expr` as a guard.
pub(in crate::compiler2) fn is_guard_expr(expr: &Spanned<Expr>) -> bool {
    collect_guard_calls_in_expr(expr, &mut Vec::new()).is_ok()
}

pub(super) fn collect_guard_calls_in_expr(expr: &Spanned<Expr>, out: &mut Vec<GuardCall>) -> Result<(), Span> {
    match &expr.node {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Alias(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Var(_) => Ok(()),
        Expr::Ascribe(inner, _) => collect_guard_calls_in_expr(inner, out),
        Expr::UnOp(op, inner) => {
            collect_guard_calls_in_expr(inner, out)?;
            if matches!(op, UnOp::Neg) {
                out.push(GuardCall {
                    callee: Callee::Name(CallableName::negation()),
                    arity: 1,
                    span: expr.span,
                });
            }
            Ok(())
        }
        Expr::BinOp(op, left, right) => {
            collect_guard_calls_in_expr(left, out)?;
            collect_guard_calls_in_expr(right, out)?;
            if let Some(name) = op.arithmetic_function() {
                out.push(GuardCall {
                    callee: Callee::Name(CallableName::source(name)),
                    arity: 2,
                    span: expr.span,
                });
            }
            Ok(())
        }
        Expr::Call(target, args) => {
            let Some(callee) = Callee::for_call(&target.node, args.len()) else {
                return Err(expr.span);
            };
            for arg in args {
                collect_guard_calls_in_expr(arg, out)?;
            }
            out.push(GuardCall {
                callee,
                arity: args.len(),
                span: expr.span,
            });
            Ok(())
        }
        Expr::FnRef { .. }
        | Expr::Module(_)
        | Expr::BoundFunction(_)
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
        | Expr::Try { .. }
        | Expr::Match(_, _)
        | Expr::Block(_)
        | Expr::Lambda { .. }
        | Expr::Quote(_, _)
        | Expr::Unquote(_) => Err(expr.span),
    }
}

/// How a guard's callee reads in a diagnostic: a source name as written, a
/// retained callable as the function it names.
fn guard_callee_label(world: &World, callee: &Callee, arity: usize) -> String {
    match callee {
        Callee::Name(name) => format!("{name}/{arity}"),
        Callee::Bound(function) => world
            .try_function_ref(*function)
            .map_or_else(|| format!("<unknown callable>/{arity}"), |reference| reference.label()),
    }
}

pub(super) fn resolve_guard_callee(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    namespace: Namespace,
    call: &GuardCall,
) -> Result<FunctionId, FatalError> {
    let label = guard_callee_label(world, &call.callee, call.arity);
    match world.lookup_callee(namespace, &call.callee, call.arity) {
        Some(NamespaceSymbol::Function(function)) | Some(NamespaceSymbol::Callable(function)) => Ok(function),
        Some(NamespaceSymbol::Macro(_)) => Err(emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 guard calls must be expanded before dispatch planning: `{label}`"),
                call.span,
            ),
        )),
        Some(NamespaceSymbol::Module(_)) | Some(NamespaceSymbol::Type(_)) | Some(NamespaceSymbol::Splice(_)) | None => {
            Err(emit_job_diagnostic(
                tel,
                Diagnostic::error(
                    codes::LOWER_UNBOUND,
                    format!("compiler2 guard call `{label}` is unresolved in this namespace"),
                    call.span,
                ),
            ))
        }
    }
}

pub(super) fn resolve_guard_callee_checked(
    world: &mut World,
    namespace: Namespace,
    callee: &Callee,
    arity: usize,
) -> FunctionId {
    match world.lookup_callee(namespace, callee, arity) {
        Some(NamespaceSymbol::Function(function)) | Some(NamespaceSymbol::Callable(function)) => function,
        Some(NamespaceSymbol::Macro(_)) => {
            panic!("guard analysis should reject macro calls before building dispatch artifacts")
        }
        Some(NamespaceSymbol::Module(_)) | Some(NamespaceSymbol::Type(_)) | Some(NamespaceSymbol::Splice(_)) | None => {
            panic!("guard analysis should reject unresolved helper calls before building dispatch artifacts")
        }
    }
}

fn emit_cycle(
    tel: &impl crate::telemetry::Telemetry,
    world: &World,
    function: FunctionId,
    cycle: &[FunctionId],
) -> FatalError {
    let mut path = cycle
        .iter()
        .map(|function| function_label(world.function_surface(*function)))
        .collect::<Vec<_>>();
    path.push(function_label(world.function_surface(function)));
    emit_job_diagnostic(
        tel,
        Diagnostic::error(
            codes::LOWER_UNSUPPORTED,
            format!("compiler2 guard helper cycle detected: {}", path.join(" -> ")),
            world.function_surface(function).span,
        ),
    )
}

fn emit_guard_dispatch_error(
    tel: &impl crate::telemetry::Telemetry,
    world: &World,
    function: FunctionId,
    span: Span,
    error: SourcePatternError,
) -> FatalError {
    let label = function_label(world.function_surface(function));
    match error {
        SourcePatternError::UnsupportedGuardExpr => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 helper `{label}` is not dispatch-pure and cannot be reified into guard dispatch"),
                span,
            ),
        ),
        SourcePatternError::UndefinedPins(pinned) => emit_undefined_pins(tel, &pinned),
        SourcePatternError::UnknownPinned(name) | SourcePatternError::UnknownGuardVar(name) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNBOUND,
                format!("compiler2 helper `{label}` references unknown guard name `{name}`"),
                span,
            ),
        ),
        SourcePatternError::GuardCallCycle(name, arity) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 guard helper cycle detected through `{name}/{arity}`"),
                span,
            ),
        ),
        SourcePatternError::DispatchMatrix(message) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 helper `{label}` could not be reified: {message}"),
                span,
            ),
        ),
        SourcePatternError::ParamAnnotation { index, message, span } => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::RESOLVE_TYPE_ALIAS,
                format!(
                    "compiler2 could not resolve parameter annotation {} for `{label}`: {message}",
                    index + 1
                ),
                span,
            ),
        ),
        SourcePatternError::GuardExternClass { symbol, why } => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 guards cannot call extern `{symbol}`: {why}"),
                span,
            ),
        ),
        SourcePatternError::UnknownSubject(_)
        | SourcePatternError::UnresolvedStruct(_)
        | SourcePatternError::RowPatternArity { .. }
        | SourcePatternError::NonMonotonicBodyId { .. } => {
            panic!("compiler2 built an invalid guard dispatch row set: {error:?}")
        }
        SourcePatternError::UnsupportedMapKey => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 helper `{label}` uses an unsupported map key in a guard pattern"),
                span,
            ),
        ),
    }
}

fn emit_entry_guard_error(
    tel: &impl crate::telemetry::Telemetry,
    world: &World,
    function: FunctionId,
    span: Span,
    reason: &str,
) -> FatalError {
    emit_job_diagnostic(
        tel,
        Diagnostic::error(
            codes::LOWER_UNSUPPORTED,
            format!(
                "compiler2 entry guards for `{}` {reason} and cannot be planned",
                function_label(world.function_surface(function))
            ),
            span,
        ),
    )
}

fn emit_entry_dispatch_error(
    tel: &impl crate::telemetry::Telemetry,
    world: &World,
    function: FunctionId,
    span: Span,
    error: PatternDispatchError,
) -> FatalError {
    let label = function_label(world.function_surface(function));
    match error {
        PatternDispatchError::SourcePattern(SourcePatternError::UnsupportedGuardExpr) => {
            emit_entry_guard_error(tel, world, function, span, "are not dispatch-pure")
        }
        PatternDispatchError::SourcePattern(SourcePatternError::UndefinedPins(pinned)) => {
            emit_undefined_pins(tel, &pinned)
        }
        PatternDispatchError::SourcePattern(SourcePatternError::UnknownPinned(name))
        | PatternDispatchError::SourcePattern(SourcePatternError::UnknownGuardVar(name)) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNBOUND,
                format!("compiler2 entry guard for `{label}` references unknown guard name `{name}`"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(SourcePatternError::UnsupportedMapKey) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 entry dispatch for `{label}` uses an unsupported map key"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(
            SourcePatternError::UnknownSubject(_)
            | SourcePatternError::UnresolvedStruct(_)
            | SourcePatternError::RowPatternArity { .. }
            | SourcePatternError::NonMonotonicBodyId { .. }
            | SourcePatternError::GuardCallCycle(_, _)
            | SourcePatternError::GuardExternClass { .. }
            | SourcePatternError::ParamAnnotation { .. }
            | SourcePatternError::DispatchMatrix(_),
        ) => panic!("compiler2 built an invalid entry-dispatch row set: {error:?}"),
        PatternDispatchError::MatrixBuild(error) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 could not build entry dispatch for `{label}`: {error:?}"),
                span,
            ),
        ),
        PatternDispatchError::Compile(error) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 could not compile entry dispatch for `{label}`: {error:?}"),
                span,
            ),
        ),
    }
}

/// Every name the patterns reached for that was never bound, each reported at
/// the place that reached for it.
fn emit_undefined_pins(tel: &impl crate::telemetry::Telemetry, pinned: &[PatternPinnedInput]) -> FatalError {
    let mut error = FatalError;
    for pin in pinned {
        error = emit_job_diagnostic(
            tel,
            Diagnostic::error(codes::LOWER_UNBOUND, pin.undefined_message(), pin.span),
        );
    }
    error
}

fn function_label(def: &FunctionSurface) -> String {
    format!("{}/{}", def.name, def.arity())
}

fn emit_job_diagnostic(tel: &impl crate::telemetry::Telemetry, diagnostic: Diagnostic) -> FatalError {
    emit_through(tel, std::slice::from_ref(&diagnostic));
    FatalError
}
