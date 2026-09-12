//! Compiler2 body-lowering jobs and helpers.
//!
//! This module lowers one defined function at a time into Compiler2's
//! structured body form. It owns the local lowering algorithm, lambda capture
//! discovery, and generated-function definition path.

use std::collections::{HashMap, HashSet};

use crate::ast::{
    AfterClause, BitField, BitSize, CallableName, Expr, FnClause, LambdaClause, MatchClause, Pattern, Spanned,
    WithBinding,
};
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{
    PatternBodyId, PatternDispatchError, PatternRow, SourcePatternError, SourcePatternRows,
    pattern_dispatch_from_source, pattern_dispatch_from_source_with_resolver,
};
use crate::extern_contract::{
    explicit_extern_wire_hint, extern_symbol_from_name, native_semantic_contract, runtime_symbol_abi, ty_to_extern_ty,
};
use crate::function_surface::FunctionSurface;
use crate::fz_ir::ExternAbi;
use crate::ground_value::GroundValue;
use crate::modules::identity::{ModuleDenotation, ModuleName};
use crate::source::Span;

use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, ControlEntryOrigin, DispatchBindings,
    LoweredBitField, LoweredBitFieldSpec, LoweredBitSize, LoweredBody, LoweredClause, LoweredEntry, LoweredExtern,
    LoweredMapKey, LoweredStep, LoweredTail, ReceiveAfter, SubjectOriginRoot, ValueId,
};
use super::super::code::SourceOwner;
use super::super::drive::{FactKey, JobEffects, current_uses};
use super::super::identity::{FunctionId, FunctionSource, ModuleId};
use super::super::module_interface::{InterfaceCallableKind, InterfaceRequester};
use super::super::namespace::{Namespace, NamespaceSymbol};
use super::super::scheduler::FatalError;
use super::super::world::World;
use super::dispatch::{collect_guard_calls_in_expr, resolve_guard_callee, resolve_guard_callee_checked};

type Output = FactKey;
type Changed = FactKey;

#[derive(Debug, Clone)]
struct ExprClause {
    span: Span,
    params: Vec<ValueId>,
    projections: Vec<ExprStep>,
    body: ExprBlock,
}

#[derive(Debug, Clone)]
struct ExprBlock {
    span: Span,
    steps: Vec<ExprStep>,
    result: ValueId,
}

#[derive(Debug, Clone)]
struct ExprDispatch {
    plan: crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>,
    arm_blocks: Vec<ExprOutcome>,
    miss_block: ExprBlock,
}

#[derive(Debug, Clone)]
struct ExprOutcome {
    outcome: crate::dispatch_matrix::OutcomeId,
    arguments: Box<[super::super::body::OutcomeArgument]>,
    block: ExprBlock,
}

#[derive(Debug, Clone)]
struct ExprReceiveAfter {
    span: Span,
    timeout: ValueId,
    body: ExprBlock,
}

#[derive(Debug, Clone)]
struct ExprReceive {
    value: ValueId,
    bindings: DispatchBindings,
    dispatch: crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>,
    outcomes: Vec<ExprOutcome>,
    after: Option<ExprReceiveAfter>,
    captures: Vec<ValueId>,
}

#[derive(Debug, Clone)]
enum ExprStep {
    Const {
        value: ValueId,
        literal: GroundValue,
    },
    Tuple {
        value: ValueId,
        items: Vec<ValueId>,
    },
    List {
        value: ValueId,
        items: Vec<ValueId>,
        tail: Option<ValueId>,
    },
    Map {
        value: ValueId,
        entries: Vec<(LoweredMapKey, ValueId)>,
        quoted_span: Option<Span>,
    },
    MapUpdate {
        value: ValueId,
        base: ValueId,
        entries: Vec<(LoweredMapKey, ValueId)>,
    },
    Struct {
        value: ValueId,
        module: super::super::identity::ModuleId,
        fields: Vec<(String, ValueId)>,
    },
    Bitstring {
        value: ValueId,
        fields: Vec<LoweredBitField>,
    },
    FunctionRef {
        value: ValueId,
        function: FunctionId,
    },
    DirectCall {
        value: ValueId,
        callsite: CallSiteId,
        callee: FunctionId,
        args: Vec<CallArg>,
    },
    ClosureCall {
        value: ValueId,
        callsite: CallSiteId,
        callee: ValueId,
        args: Vec<CallArg>,
    },
    Lambda {
        value: ValueId,
        function: FunctionId,
        captures: Vec<ValueId>,
    },
    BinaryOp {
        value: ValueId,
        op: crate::ast::BinOp,
        left: ValueId,
        right: ValueId,
    },
    UnaryOp {
        value: ValueId,
        op: crate::ast::UnOp,
        input: ValueId,
    },
    MapIndex {
        value: ValueId,
        base: ValueId,
        key: LoweredMapKey,
    },
    FieldAccess {
        value: ValueId,
        base: ValueId,
        field: String,
    },
    If {
        value: ValueId,
        cond: ValueId,
        then_block: ExprBlock,
        else_block: ExprBlock,
    },
    Dispatch {
        value: ValueId,
        inputs: Vec<ValueId>,
        bindings: DispatchBindings,
        dispatch: Box<ExprDispatch>,
    },
    Receive(Box<ExprReceive>),
    Halt {
        atom: String,
    },
    AssertLiteral {
        source: ValueId,
        literal: GroundValue,
    },
    AssertStruct {
        source: ValueId,
        module: super::super::identity::ModuleId,
    },
    RequireMapValue {
        value: ValueId,
        source: ValueId,
        key: GroundValue,
    },
    AssertTuple {
        source: ValueId,
        arity: usize,
    },
    TupleField {
        value: ValueId,
        source: ValueId,
        index: usize,
    },
    AssertEmptyList {
        source: ValueId,
    },
    AssertSame {
        source: ValueId,
        value: ValueId,
    },
    SplitList {
        source: ValueId,
        head: ValueId,
        tail: ValueId,
    },
    BitstringInit {
        reader: ValueId,
        source: ValueId,
    },
    BitstringRead {
        ok: ValueId,
        value: ValueId,
        next_reader: ValueId,
        reader: ValueId,
        spec: LoweredBitFieldSpec,
        is_last: bool,
    },
    AssertBitstringDone {
        reader: ValueId,
    },
}

/// Lowers one demanded function into Compiler2's structured body form.
///
/// This job reads the frozen function definition and emits one reusable body
/// fact keyed by `FunctionId`. It lowers only that function, plus any lambda
/// definitions it syntactically owns, and leaves unrelated bodies cold.
pub(super) fn lower_function(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
) -> Result<JobEffects, FatalError> {
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };
    let (source, surface) = world.function_definition(function);

    let mut reads = vec![FactKey::FunctionDefined(function)];
    let mut waits = HashSet::new();
    if surface.declaration.is_some() {
        for referenced in world.function_type_refs(function).iter().cloned() {
            let fact = FactKey::TypeDefined(referenced);
            if world.has_fact(&fact) {
                reads.push(fact);
            } else {
                waits.insert(fact);
            }
        }
        // Same wait, `StructDefined` side: an extern contract that names
        // `%Mod{...}` resolves through the shared `TypeExpr::StructRecord` arm
        // (`resolve_extern_signature` -> `resolve_spec_decl`), which needs
        // `Mod`'s settled schema. Resolving before the defstruct lands would
        // validate and type the tagged record against an incomplete field set.
        // This waits on the extern spec's struct refs, mirroring the
        // `TypeDefined` loop above; it is spec-type resolution, distinct from
        // the struct-literal/pattern lowering wait recorded below.
        for module in world.function_type_struct_refs(function).iter().copied() {
            let fact = FactKey::StructDefined(module);
            if world.has_fact(&fact) {
                reads.push(fact);
            } else {
                waits.insert(fact);
            }
        }
    }
    for clause in &surface.clauses {
        for param in &clause.params {
            collect_local_pattern_requirements(
                world,
                tel,
                source.namespace,
                source.owner_module,
                source.owner,
                param,
                &mut reads,
                &mut waits,
            )?;
        }
        if let Some(guard) = &clause.guard {
            collect_local_dispatch_requirements(
                world,
                tel,
                source.namespace,
                source.owner_module,
                source.owner,
                guard,
                &mut reads,
                &mut waits,
            )?;
        }
        collect_local_dispatch_requirements(
            world,
            tel,
            source.namespace,
            source.owner_module,
            source.owner,
            &clause.body,
            &mut reads,
            &mut waits,
        )?;
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    }

    let mut lowerer = Lowerer::new(world, tel, function, source, surface);
    let (body, mut outputs, mut changed) = lowerer.lower()?;
    let body_changed =
        super::super::drive::ExecutionContext::new(lowerer.world, tel).define_lowered_body(function, body);
    outputs.push(FactKey::LoweredBody(function));
    if body_changed {
        changed.push(FactKey::LoweredBody(function));
    }
    Ok(JobEffects {
        reads: current_uses(reads),
        outputs,
        changed,
        ..JobEffects::default()
    })
}

fn extern_wire_ty(
    types: &mut super::super::types::Types,
    body: &crate::ast::TypeExprBody,
    semantic_ty: &super::super::types::Ty,
    constraints: &HashMap<super::super::types::TypeVarId, super::super::types::Ty>,
) -> crate::fz_ir::ExternTy {
    if let Some(hint) = explicit_extern_wire_hint(body) {
        return hint;
    }
    let upper_bound = if constraints.is_empty() {
        *semantic_ty
    } else {
        types.instantiate(semantic_ty, constraints)
    };
    ty_to_extern_ty(types, &upper_bound)
}

fn collect_local_dispatch_requirements(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    namespace: Namespace,
    owner_module: ModuleId,
    owner: SourceOwner,
    expr: &Spanned<Expr>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<(), FatalError> {
    match &expr.node {
        Expr::Case(subject, clauses) => {
            if let Some(subject) = subject {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, subject, reads, waits)?;
            }
            for clause in clauses {
                collect_local_pattern_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &clause.pattern,
                    reads,
                    waits,
                )?;
                if let Some(guard) = &clause.guard {
                    collect_local_guard_requirements(world, tel, namespace, guard, reads, waits)?;
                }
                collect_local_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &clause.body,
                    reads,
                    waits,
                )?;
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for binding in bindings {
                match binding {
                    WithBinding::Match(pattern, expr) => {
                        collect_local_pattern_requirements(
                            world,
                            tel,
                            namespace,
                            owner_module,
                            owner,
                            pattern,
                            reads,
                            waits,
                        )?;
                        collect_local_dispatch_requirements(
                            world,
                            tel,
                            namespace,
                            owner_module,
                            owner,
                            expr,
                            reads,
                            waits,
                        )?;
                    }
                    WithBinding::Bare(expr) => {
                        collect_local_dispatch_requirements(
                            world,
                            tel,
                            namespace,
                            owner_module,
                            owner,
                            expr,
                            reads,
                            waits,
                        )?;
                    }
                }
            }
            collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, body, reads, waits)?;
            for clause in else_clauses {
                collect_local_pattern_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &clause.pattern,
                    reads,
                    waits,
                )?;
                if let Some(guard) = &clause.guard {
                    collect_local_guard_requirements(world, tel, namespace, guard, reads, waits)?;
                }
                collect_local_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &clause.body,
                    reads,
                    waits,
                )?;
            }
        }
        Expr::If(cond, then_expr, else_expr) => {
            collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, cond, reads, waits)?;
            collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, then_expr, reads, waits)?;
            if let Some(else_expr) = else_expr {
                collect_local_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    else_expr,
                    reads,
                    waits,
                )?;
            }
        }
        Expr::Cond(arms) => {
            for (cond, body) in arms {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, cond, reads, waits)?;
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, body, reads, waits)?;
            }
        }
        Expr::Receive { clauses, after } => {
            for clause in clauses {
                collect_local_pattern_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &clause.pattern,
                    reads,
                    waits,
                )?;
                if let Some(guard) = &clause.guard {
                    collect_local_guard_requirements(world, tel, namespace, guard, reads, waits)?;
                }
                collect_local_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &clause.body,
                    reads,
                    waits,
                )?;
            }
            if let Some(after) = after {
                collect_local_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &after.timeout,
                    reads,
                    waits,
                )?;
                collect_local_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &after.body,
                    reads,
                    waits,
                )?;
            }
        }
        Expr::Match(pattern, rhs) => {
            collect_local_pattern_requirements(world, tel, namespace, owner_module, owner, pattern, reads, waits)?;
            collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, rhs, reads, waits)?;
        }
        Expr::Ascribe(rhs, _) | Expr::UnOp(_, rhs) | Expr::Capture(rhs) | Expr::Unquote(rhs) => {
            collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, rhs, reads, waits)?;
        }
        Expr::Quote(rhs) => {
            collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, rhs, reads, waits)?;
        }
        Expr::BinOp(_, left, right) | Expr::Index(left, right) => {
            collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, left, reads, waits)?;
            collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, right, reads, waits)?;
        }
        Expr::Call(target, args) | Expr::ClosureCall(target, args) => {
            collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, target, reads, waits)?;
            for arg in args {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, arg, reads, waits)?;
            }
        }
        Expr::List(items, tail) => {
            for item in items {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, item, reads, waits)?;
            }
            if let Some(tail) = tail {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, tail, reads, waits)?;
            }
        }
        Expr::Tuple(items) => {
            for item in items {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, item, reads, waits)?;
            }
        }
        Expr::Bitstring(fields) => {
            for field in fields {
                collect_local_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &field.value,
                    reads,
                    waits,
                )?;
            }
        }
        Expr::Map(entries) | Expr::MapUpdate(_, entries) => {
            if let Expr::MapUpdate(base, _) = &expr.node {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, base, reads, waits)?;
            }
            for (key, value) in entries {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, key, reads, waits)?;
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, value, reads, waits)?;
            }
        }
        Expr::Struct { module, fields } => {
            record_struct_reference(
                world,
                tel,
                namespace,
                owner_module,
                owner,
                module,
                fields.iter().map(|(name, _)| name.as_str()),
                expr.span,
                reads,
                waits,
            )?;
            for (_, value) in fields {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, value, reads, waits)?;
            }
        }
        Expr::Block(exprs) => {
            for expr in exprs {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, expr, reads, waits)?;
            }
        }
        Expr::Lambda { .. } => {}
        Expr::CaptureArg(_)
        | Expr::Module(_)
        | Expr::FnRef { .. }
        | Expr::Var(_)
        | Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil => {}
    }
    Ok(())
}

/// Walks one pattern for the same reason `collect_local_dispatch_requirements`
/// walks expressions: a `%Mod{field: pattern, ...}` struct pattern needs
/// `Mod`'s schema before executable pattern dispatch or body binding can use its
/// fields. Entry, guard-helper, and body jobs share these field obligations and
/// the `StructDefined` wait, mirroring the `Expr::Struct` arm above.
/// Patterns never carry dispatch calls of their own
/// (guards are the only dispatch-call surface, and guards are walked
/// separately), so this only needs to recurse far enough to find nested
/// struct patterns.
pub(super) fn collect_local_pattern_requirements(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    namespace: Namespace,
    owner_module: ModuleId,
    owner: SourceOwner,
    pattern: &Spanned<Pattern>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<(), FatalError> {
    match &pattern.node {
        Pattern::Struct { module, fields } => {
            record_struct_reference(
                world,
                tel,
                namespace,
                owner_module,
                owner,
                module,
                fields.iter().map(|(name, _)| name.as_str()),
                pattern.span,
                reads,
                waits,
            )?;
            for (_, field_pattern) in fields {
                collect_local_pattern_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    field_pattern,
                    reads,
                    waits,
                )?;
            }
        }
        Pattern::Tuple(items) => {
            for item in items {
                collect_local_pattern_requirements(world, tel, namespace, owner_module, owner, item, reads, waits)?;
            }
        }
        Pattern::List(items, tail) => {
            for item in items {
                collect_local_pattern_requirements(world, tel, namespace, owner_module, owner, item, reads, waits)?;
            }
            if let Some(tail) = tail {
                collect_local_pattern_requirements(world, tel, namespace, owner_module, owner, tail, reads, waits)?;
            }
        }
        Pattern::Map(entries) => {
            for (_, value) in entries {
                collect_local_pattern_requirements(world, tel, namespace, owner_module, owner, value, reads, waits)?;
            }
        }
        Pattern::As(_, inner) => {
            collect_local_pattern_requirements(world, tel, namespace, owner_module, owner, inner, reads, waits)?;
        }
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_local_pattern_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &field.value,
                    reads,
                    waits,
                )?;
            }
        }
        Pattern::Wildcard
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil
        | Pattern::Pinned(_) => {}
    }
    Ok(())
}

/// Records one `%Mod{...}` reference from a struct literal or struct pattern
/// in a function body: the module-obligation and field-obligation halves
/// mirror `source_publish.rs`'s `collect_struct_obligations` (same
/// expectation store, so a non-struct module or bad field is diagnosed at
/// the requester regardless of whether the reference came from a type
/// position or a body position), and the `StructDefined` wait half mirrors
/// every other consumer in this file (`lower_function`'s extern-contract loop,
/// `plan_entry_dispatch`, `derive_function_contract`) — `Mod`'s field *order*
/// is unknown until `StructDefined(Mod)` publishes, so the caller must wait
/// rather than guess an order from the literal/pattern's own field list.
///
/// Module resolution mirrors `Lowerer::resolve_struct_module` exactly (same
/// `resolve_module_target` call against the same `owner_module`/`namespace`),
/// so the module identity this pre-pass records obligations/waits against is
/// always the module the later `Lowerer` pass will actually consume. If
/// resolution itself fails, this records nothing and defers to
/// `resolve_struct_module`'s own `LOWER_UNBOUND` diagnostic once lowering
/// runs — an unresolvable module name is an unrelated, pre-existing failure
/// mode, not a struct-schema question.
#[allow(clippy::too_many_arguments)]
fn record_struct_reference<'a>(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    namespace: Namespace,
    owner_module: ModuleId,
    owner: SourceOwner,
    module: &crate::ast::ModuleTarget,
    fields: impl Iterator<Item = &'a str>,
    span: Span,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<(), FatalError> {
    let Some(module_id) = world.resolve_module_target(owner_module, namespace, module) else {
        return Ok(());
    };
    let requester = InterfaceRequester {
        owner,
        module: owner_module,
        span,
    };
    world.note_struct_reference_expectation(module_id, requester.clone());
    for field in fields {
        super::super::drive::ExecutionContext::new(world, tel).note_struct_field_expectation(
            module_id,
            field.to_string(),
            requester.clone(),
        )?;
    }
    let fact = FactKey::StructDefined(module_id);
    if world.has_fact(&fact) {
        reads.push(fact);
    } else {
        waits.insert(fact);
    }
    Ok(())
}

fn collect_unquote_dispatch_requirements(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    namespace: Namespace,
    owner_module: ModuleId,
    owner: SourceOwner,
    expr: &Spanned<Expr>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<(), FatalError> {
    match &expr.node {
        Expr::Unquote(inner) => {
            collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, inner, reads, waits)
        }
        Expr::Ascribe(inner, _) | Expr::Quote(inner) => {
            collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, inner, reads, waits)
        }
        Expr::Case(subject, clauses) => {
            if let Some(subject) = subject {
                collect_unquote_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    subject,
                    reads,
                    waits,
                )?;
            }
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_unquote_dispatch_requirements(
                        world,
                        tel,
                        namespace,
                        owner_module,
                        owner,
                        guard,
                        reads,
                        waits,
                    )?;
                }
                collect_unquote_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &clause.body,
                    reads,
                    waits,
                )?;
            }
            Ok(())
        }
        Expr::With(bindings, body, else_clauses) => {
            for binding in bindings {
                match binding {
                    WithBinding::Match(_, expr) | WithBinding::Bare(expr) => {
                        collect_unquote_dispatch_requirements(
                            world,
                            tel,
                            namespace,
                            owner_module,
                            owner,
                            expr,
                            reads,
                            waits,
                        )?;
                    }
                }
            }
            collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, body, reads, waits)?;
            for clause in else_clauses {
                if let Some(guard) = &clause.guard {
                    collect_unquote_dispatch_requirements(
                        world,
                        tel,
                        namespace,
                        owner_module,
                        owner,
                        guard,
                        reads,
                        waits,
                    )?;
                }
                collect_unquote_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &clause.body,
                    reads,
                    waits,
                )?;
            }
            Ok(())
        }
        Expr::If(cond, then_expr, else_expr) => {
            collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, cond, reads, waits)?;
            collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, then_expr, reads, waits)?;
            if let Some(else_expr) = else_expr {
                collect_unquote_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    else_expr,
                    reads,
                    waits,
                )?;
            }
            Ok(())
        }
        Expr::Cond(arms) => {
            for (cond, body) in arms {
                collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, cond, reads, waits)?;
                collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, body, reads, waits)?;
            }
            Ok(())
        }
        Expr::Receive { clauses, after } => {
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_unquote_dispatch_requirements(
                        world,
                        tel,
                        namespace,
                        owner_module,
                        owner,
                        guard,
                        reads,
                        waits,
                    )?;
                }
                collect_unquote_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &clause.body,
                    reads,
                    waits,
                )?;
            }
            if let Some(after) = after {
                collect_unquote_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &after.timeout,
                    reads,
                    waits,
                )?;
                collect_unquote_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &after.body,
                    reads,
                    waits,
                )?;
            }
            Ok(())
        }
        Expr::Match(_, rhs) | Expr::UnOp(_, rhs) | Expr::Capture(rhs) => {
            collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, rhs, reads, waits)
        }
        Expr::BinOp(_, left, right) | Expr::Index(left, right) => {
            collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, left, reads, waits)?;
            collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, right, reads, waits)
        }
        Expr::Call(target, args) | Expr::ClosureCall(target, args) => {
            collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, target, reads, waits)?;
            for arg in args {
                collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, arg, reads, waits)?;
            }
            Ok(())
        }
        Expr::List(items, tail) => {
            for item in items {
                collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, item, reads, waits)?;
            }
            if let Some(tail) = tail {
                collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, tail, reads, waits)?;
            }
            Ok(())
        }
        Expr::Tuple(items) => {
            for item in items {
                collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, item, reads, waits)?;
            }
            Ok(())
        }
        Expr::Bitstring(fields) => {
            for field in fields {
                collect_unquote_dispatch_requirements(
                    world,
                    tel,
                    namespace,
                    owner_module,
                    owner,
                    &field.value,
                    reads,
                    waits,
                )?;
            }
            Ok(())
        }
        Expr::Map(entries) | Expr::MapUpdate(_, entries) => {
            if let Expr::MapUpdate(base, _) = &expr.node {
                collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, base, reads, waits)?;
            }
            for (key, value) in entries {
                collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, key, reads, waits)?;
                collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, value, reads, waits)?;
            }
            Ok(())
        }
        Expr::Struct { fields, .. } => {
            for (_, value) in fields {
                collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, value, reads, waits)?;
            }
            Ok(())
        }
        Expr::Block(exprs) => {
            for expr in exprs {
                collect_unquote_dispatch_requirements(world, tel, namespace, owner_module, owner, expr, reads, waits)?;
            }
            Ok(())
        }
        Expr::Lambda { .. }
        | Expr::Module(_)
        | Expr::CaptureArg(_)
        | Expr::FnRef { .. }
        | Expr::Var(_)
        | Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil => Ok(()),
    }
}

fn collect_local_guard_requirements(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    namespace: Namespace,
    guard: &Spanned<Expr>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<(), FatalError> {
    let mut calls = Vec::new();
    collect_guard_calls_in_expr(guard, &mut calls).map_err(|span| {
        emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                "compiler2 case/with guards must be dispatch-pure".to_string(),
                span,
            ),
        )
    })?;
    for call in calls {
        let callee = resolve_guard_callee(world, tel, namespace, &call)?;
        let fact = FactKey::GuardDispatch(callee);
        if world.fact_revision(&fact).is_some() {
            reads.push(fact);
        } else {
            waits.insert(fact);
        }
    }
    Ok(())
}

struct Lowerer<'w, 'tel, T: crate::telemetry::Telemetry> {
    world: &'w mut World,
    telemetry: &'tel T,
    owner: FunctionId,
    namespace: Namespace,
    source: FunctionSource,
    surface: FunctionSurface,
    next_value: u32,
    next_callsite: u32,
    generated: Vec<Output>,
    generated_changed: Vec<Changed>,
    generated_ids: Vec<FunctionId>,
}

struct QuoteLowerer<'a, 'w, 'tel, 'env, 'steps, T: crate::telemetry::Telemetry> {
    lowerer: &'a mut Lowerer<'w, 'tel, T>,
    env: &'env mut HashMap<String, ValueId>,
    steps: &'steps mut Vec<ExprStep>,
}

impl<'a, 'w, 'tel, 'env, 'steps, T: crate::telemetry::Telemetry> QuoteLowerer<'a, 'w, 'tel, 'env, 'steps, T> {
    fn new(
        lowerer: &'a mut Lowerer<'w, 'tel, T>,
        env: &'env mut HashMap<String, ValueId>,
        steps: &'steps mut Vec<ExprStep>,
    ) -> Self {
        Self { lowerer, env, steps }
    }

    fn lower(&mut self, expr: &Spanned<Expr>) -> Result<ValueId, FatalError> {
        match &expr.node {
            Expr::Unquote(inner) => self.lowerer.lower_expr(inner, self.env, self.steps),
            Expr::Ascribe(inner, _) => self.lower(inner),
            Expr::Int(value) => Ok(self.lowerer.push_const(self.steps, GroundValue::Int(*value))),
            Expr::Float(value) => Ok(self.lowerer.push_const(self.steps, GroundValue::from_f64(*value))),
            Expr::Binary(value) => Ok(self.lowerer.push_const(self.steps, GroundValue::Binary(value.clone()))),
            Expr::Atom(value) => Ok(self.lowerer.push_const(self.steps, GroundValue::Atom(value.clone()))),
            Expr::Bool(value) => Ok(self.lowerer.push_const(self.steps, GroundValue::Bool(*value))),
            Expr::Nil => Ok(self.lowerer.push_const(self.steps, GroundValue::Nil)),
            Expr::Var(name) => self.lower_variable(name, expr.span),
            Expr::Module(module) => Ok(self.lower_module(module, expr.span)),
            Expr::List(items, None) => {
                let values = items
                    .iter()
                    .map(|item| self.lower(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.push_list(values, None))
            }
            Expr::List(_, Some(_)) => Err(emit_job_diagnostic(
                self.lowerer.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "compiler2 quote does not lower improper source lists yet".to_string(),
                    expr.span,
                ),
            )),
            Expr::Tuple(items) => {
                let values = items
                    .iter()
                    .map(|item| self.lower(item))
                    .collect::<Result<Vec<_>, _>>()?;
                self.lower_atom_node("{}", values, expr.span)
            }
            Expr::Map(entries) => {
                let values = entries
                    .iter()
                    .map(|(key, value)| {
                        let key = self.lower(key)?;
                        let value = self.lower(value)?;
                        Ok(self.push_tuple(vec![key, value]))
                    })
                    .collect::<Result<Vec<_>, FatalError>>()?;
                self.lower_atom_node("%{}", values, expr.span)
            }
            Expr::Call(callee, args) => {
                let values = args.iter().map(|arg| self.lower(arg)).collect::<Result<Vec<_>, _>>()?;
                if let Expr::Var(name) = &callee.node {
                    let name = self.quoted_callable_name(name, values.len());
                    self.lower_atom_node(&name, values, expr.span)
                } else {
                    let head = self.lower(callee)?;
                    let tail = self.push_list(values, None);
                    Ok(self.push_ast_node(head, tail, expr.span))
                }
            }
            Expr::BinOp(op, left, right) => {
                let left = self.lower(left)?;
                let right = self.lower(right)?;
                self.lower_atom_node(quoted_binop_atom(*op), vec![left, right], expr.span)
            }
            Expr::UnOp(op, input) => {
                let input = self.lower(input)?;
                self.lower_atom_node(quoted_unop_atom(*op), vec![input], expr.span)
            }
            Expr::Match(pattern, rhs) => {
                let Pattern::Var(name) = &pattern.node else {
                    return Err(emit_job_diagnostic(
                        self.lowerer.telemetry,
                        Diagnostic::error(
                            codes::LOWER_UNSUPPORTED,
                            "compiler2 quote only supports variable match patterns today".to_string(),
                            pattern.span,
                        ),
                    ));
                };
                let lhs = self.lower_variable(name, pattern.span)?;
                let rhs = self.lower(rhs)?;
                self.lower_atom_node("=", vec![lhs, rhs], expr.span)
            }
            Expr::Block(exprs) => {
                let values = exprs
                    .iter()
                    .map(|expr| self.lower(expr))
                    .collect::<Result<Vec<_>, _>>()?;
                self.lower_atom_node("__block__", values, expr.span)
            }
            Expr::If(cond, then_expr, else_expr) => {
                let cond = self.lower(cond)?;
                let then_value = self.lower(then_expr)?;
                let mut keywords = vec![self.push_keyword("do", then_value)];
                if let Some(else_expr) = else_expr {
                    let else_value = self.lower(else_expr)?;
                    keywords.push(self.push_keyword("else", else_value));
                }
                let keyword_list = self.push_list(keywords, None);
                self.lower_atom_node("if", vec![cond, keyword_list], expr.span)
            }
            Expr::Index(base, key) => self.lower_index(base, key, expr.span),
            Expr::Quote(_)
            | Expr::FnRef { .. }
            | Expr::Capture(_)
            | Expr::CaptureArg(_)
            | Expr::Bitstring(_)
            | Expr::MapUpdate(_, _)
            | Expr::Struct { .. }
            | Expr::ClosureCall(_, _)
            | Expr::Case(_, _)
            | Expr::Cond(_)
            | Expr::With(_, _, _)
            | Expr::Receive { .. }
            | Expr::Lambda { .. } => Err(emit_job_diagnostic(
                self.lowerer.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("compiler2 quote does not lower `{}` yet", expr_name(&expr.node)),
                    expr.span,
                ),
            )),
        }
    }

    fn quoted_callable_name(&mut self, name: &str, arity: usize) -> String {
        if name.contains('.') {
            return name.to_string();
        }
        let Some(symbol) = self
            .lowerer
            .world
            .lookup_callable_namespace(self.lowerer.namespace, name, arity)
        else {
            return name.to_string();
        };
        let function = match symbol {
            NamespaceSymbol::Function(function)
            | NamespaceSymbol::Macro(function)
            | NamespaceSymbol::Callable(function) => function,
            NamespaceSymbol::Module(_) | NamespaceSymbol::Type(_) | NamespaceSymbol::Splice(_) => {
                return name.to_string();
            }
        };
        let module = self.lowerer.world.function_module(function);
        if module.is_global() {
            return name.to_string();
        }
        let Some(module_name) = self.lowerer.world.module_name(module) else {
            return name.to_string();
        };
        format!("{module_name}.{name}")
    }

    fn lower_variable(&mut self, name: &str, span: Span) -> Result<ValueId, FatalError> {
        if quoted_alias_segments(name).is_some() {
            return self.lower_alias(name, span);
        }
        let head = self.lowerer.push_const(self.steps, GroundValue::Atom(name.to_string()));
        let tail = self.lowerer.push_const(self.steps, GroundValue::Nil);
        Ok(self.push_ast_node(head, tail, span))
    }

    fn lower_alias(&mut self, name: &str, span: Span) -> Result<ValueId, FatalError> {
        let segments = quoted_alias_segments(name).expect("checked quoted alias name");
        let head = self
            .lowerer
            .push_const(self.steps, GroundValue::Atom("__aliases__".to_string()));
        let mut items = Vec::with_capacity(segments.len());
        for segment in segments {
            items.push(
                self.lowerer
                    .push_const(self.steps, GroundValue::Atom(segment.to_string())),
            );
        }
        let tail = self.push_list(items, None);
        Ok(self.push_ast_node(head, tail, span))
    }

    fn lower_module(&mut self, module: &ModuleDenotation, span: Span) -> ValueId {
        let head = self
            .lowerer
            .push_const(self.steps, GroundValue::Atom("__aliases__".into()));
        let tail = self.module_path(module.display_segments());
        let (tag, paths) = module.quoted_parts();
        let tag = self.lowerer.push_const(self.steps, GroundValue::Atom(tag.into()));
        let mut fields = vec![tag];
        for path in paths {
            fields.push(self.module_path(path.segments().iter()));
        }
        let identity = self.push_tuple(fields);
        let key = self.lowerer.push_const(
            self.steps,
            GroundValue::Atom(super::super::source::META_MODULE_KEY.into()),
        );
        let key = LoweredMapKey {
            value: key,
            literal: Some(GroundValue::Atom(super::super::source::META_MODULE_KEY.into())),
        };
        let meta = self.push_meta(span, vec![(key, identity)]);
        self.push_tuple(vec![head, meta, tail])
    }

    fn module_path<'s>(&mut self, segments: impl Iterator<Item = &'s String>) -> ValueId {
        let items = segments
            .map(|segment| self.lowerer.push_const(self.steps, GroundValue::Atom(segment.clone())))
            .collect();
        self.push_list(items, None)
    }

    fn lower_index(&mut self, base: &Spanned<Expr>, key: &Spanned<Expr>, span: Span) -> Result<ValueId, FatalError> {
        let Expr::Atom(field) = &key.node else {
            return Err(emit_job_diagnostic(
                self.lowerer.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "compiler2 quote only lowers atom field access today".to_string(),
                    span,
                ),
            ));
        };
        let base = self.lower(base)?;
        let field = self.lowerer.push_const(self.steps, GroundValue::Atom(field.clone()));
        let head = self.lowerer.push_const(self.steps, GroundValue::Atom(".".to_string()));
        let meta = self.push_meta(span, Vec::new());
        let tail = self.push_list(vec![base, field], None);
        Ok(self.push_tuple(vec![head, meta, tail]))
    }

    fn lower_atom_node(&mut self, name: &str, args: Vec<ValueId>, span: Span) -> Result<ValueId, FatalError> {
        let head = self.lowerer.push_const(self.steps, GroundValue::Atom(name.to_string()));
        let tail = self.push_list(args, None);
        Ok(self.push_ast_node(head, tail, span))
    }

    fn push_ast_node(&mut self, head: ValueId, tail: ValueId, span: Span) -> ValueId {
        let meta = self.push_meta(span, Vec::new());
        self.push_tuple(vec![head, meta, tail])
    }

    fn push_meta(&mut self, span: Span, entries: Vec<(LoweredMapKey, ValueId)>) -> ValueId {
        let value = self.lowerer.fresh_value();
        self.steps.push(ExprStep::Map {
            value,
            entries,
            quoted_span: (!span.is_dummy()).then_some(span),
        });
        value
    }

    fn push_keyword(&mut self, key: &str, value: ValueId) -> ValueId {
        let key = self.lowerer.push_const(self.steps, GroundValue::Atom(key.to_string()));
        self.push_tuple(vec![key, value])
    }

    fn push_tuple(&mut self, items: Vec<ValueId>) -> ValueId {
        let value = self.lowerer.fresh_value();
        self.steps.push(ExprStep::Tuple { value, items });
        value
    }

    fn push_list(&mut self, items: Vec<ValueId>, tail: Option<ValueId>) -> ValueId {
        let value = self.lowerer.fresh_value();
        self.steps.push(ExprStep::List { value, items, tail });
        value
    }
}

impl<'w, 'tel, T: crate::telemetry::Telemetry> Lowerer<'w, 'tel, T> {
    fn new(
        world: &'w mut World,
        telemetry: &'tel T,
        owner: FunctionId,
        source: FunctionSource,
        surface: FunctionSurface,
    ) -> Self {
        let namespace = source.namespace;
        Self {
            world,
            telemetry,
            owner,
            namespace,
            source,
            surface,
            next_value: 0,
            next_callsite: 0,
            generated: Vec::new(),
            generated_changed: Vec::new(),
            generated_ids: Vec::new(),
        }
    }

    fn lower(&mut self) -> Result<(LoweredBody, Vec<Output>, Vec<Changed>), FatalError> {
        if let Some(crate::function_surface::NativeDeclaration::Intrinsic(name)) = &self.surface.declaration {
            if !self.declared_by_runtime_library() {
                return Err(
                    self.extern_abi_error("intrinsic declarations are reserved to the runtime library".to_string())
                );
            }
            if self.surface.variadic {
                return Err(self.extern_abi_error("intrinsic declarations cannot be variadic".to_string()));
            }
            let identity = fz_runtime::intrinsic::Intrinsic::resolve(name)
                .ok_or_else(|| self.extern_abi_error(format!("unknown intrinsic `{name}`")))?;
            let contract = self.resolve_native_contract()?;
            let signature = super::super::body::LoweredIntrinsic::validate(self.world.types_mut(), identity, contract)
                .map_err(|error| self.extern_abi_error(format!("intrinsic `{identity:?}`: {error}")))?;
            return Ok((LoweredBody::Intrinsic { signature }, Vec::new(), Vec::new()));
        }
        if self.surface.declaration.is_some() {
            let signature = self.resolve_extern_signature()?;
            return Ok((LoweredBody::Extern { signature }, Vec::new(), Vec::new()));
        }

        let mut clause_defs = Vec::new();
        for clause in self.surface.clauses.clone() {
            clause_defs.push(self.lower_clause(&clause)?);
        }
        let body = self.plan_clauses(clause_defs);

        Ok((
            body,
            std::mem::take(&mut self.generated),
            std::mem::take(&mut self.generated_changed),
        ))
    }

    /// The declared calling convention, or a diagnostic.
    ///
    /// Four ways to get it wrong, and every one of them is refused HERE rather
    /// than in a door's lowering, because a diagnostic raised in the shared
    /// front end is the only kind every door raises identically. Each of these
    /// was, at some point, a per-door check that protected fewer doors than it
    /// appeared to.
    ///
    /// 1. An unrecognised name must not fall back to C: the conventions
    ///    disagree about the implicit process argument and about what a
    ///    `binary` parameter is, so a wrong guess is a crash inside the callee.
    ///
    /// 2. `"fz"` is reserved to the runtime library. It passes fz's own
    ///    `*mut Process` and fz's internal value representation, which nothing
    ///    outside the runtime can accept; worse, the symbols it can name are
    ///    the ones both doors also claim by name in their lowerings, and those
    ///    two claim sets are not equal, so a foreign declaration of one is a
    ///    question the doors would answer differently.
    ///
    /// 3. There is no variadic `"fz"`: a variadic call goes through a
    ///    fixed-arity C dispatcher with nowhere to put the process.
    ///
    /// 4. A declaration may not contradict what the runtime actually provides.
    ///    `fz_dbg_value` is `fn(*mut Process, u64)` however it is declared, so
    ///    an `extern "C"` one reached it as `fn(u64)` -- nil under `interp`,
    ///    and for the same shape on `fz_process_heap_alloc_stats`, a segfault
    ///    under `run` and `build`.
    fn resolve_extern_abi(&self) -> Result<ExternAbi, FatalError> {
        let Some(crate::function_surface::NativeDeclaration::Extern(declared)) = &self.surface.declaration else {
            return Err(self.extern_abi_error("generic extern lowering requires an extern declaration".to_string()));
        };
        let Some(abi) = ExternAbi::parse(declared) else {
            return Err(self.extern_abi_error(format!(
                "unknown extern ABI `{}` on `{}`; expected one of {}",
                declared,
                self.surface.name,
                ExternAbi::ALL
                    .iter()
                    .map(|known| format!("`{known}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )));
        };
        if abi.takes_process() && !self.declared_by_runtime_library() {
            return Err(self.extern_abi_error(format!(
                "`{}` declares the `fz` ABI, which is reserved for fz's own runtime library; \
                 it passes the running process and fz's internal value representation, \
                 so declare a foreign symbol `extern \"C\"` instead",
                self.surface.name
            )));
        }
        if abi.takes_process() && self.surface.variadic {
            return Err(self.extern_abi_error(format!(
                "`{}` is variadic and declares the `fz` ABI; every variadic call goes through a \
                 fixed-arity C dispatcher, which has nowhere to put the implicit process argument",
                self.surface.name
            )));
        }
        let symbol = extern_symbol_from_name(&self.surface.name);
        if let Some(provided) = runtime_symbol_abi(symbol)
            && provided != abi
        {
            return Err(self.extern_abi_error(format!(
                "`{}` names `{}`, which the fz runtime provides with the `{}` ABI, \
                 but declares `extern \"{}\"`; the two disagree about the implicit process \
                 argument and about how a binary is passed, so the call would reach the \
                 symbol with arguments it never accepts",
                self.surface.name, symbol, provided, abi
            )));
        }
        Ok(abi)
    }

    fn declared_by_runtime_library(&self) -> bool {
        self.world.is_bootstrap(self.source.owner)
    }

    fn extern_abi_error(&self, message: String) -> FatalError {
        emit_job_diagnostic(
            self.telemetry,
            Diagnostic::error(codes::LOWER_UNSUPPORTED, message, self.surface.name_span),
        )
    }

    fn resolve_extern_signature(&mut self) -> Result<LoweredExtern, FatalError> {
        // Checked first: it is the cheapest question, and a wrong answer makes
        // every later one moot.
        let abi = self.resolve_extern_abi()?;
        let semantic_contract = self.resolve_native_contract()?;
        let params = self
            .surface
            .native_param_tokens
            .iter()
            .zip(semantic_contract.params.iter())
            .map(|(body, ty)| extern_wire_ty(self.world.types_mut(), body, ty, &semantic_contract.constraints))
            .collect();
        let ret = extern_wire_ty(
            self.world.types_mut(),
            &self.surface.native_ret_tokens,
            &semantic_contract.result,
            &semantic_contract.constraints,
        );
        Ok(LoweredExtern {
            abi,
            symbol: extern_symbol_from_name(&self.surface.name).to_string(),
            params,
            variadic: self.surface.variadic,
            ret,
            return_ty: semantic_contract.result,
            semantic_contract,
        })
    }

    fn resolve_native_contract(
        &mut self,
    ) -> Result<crate::type_expr::ResolvedSpecDecl<super::super::types::Ty>, FatalError> {
        let contract = native_semantic_contract(&self.surface).ok_or_else(|| {
            emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("`{}` is not a native declaration", self.surface.name),
                    self.surface.name_span,
                ),
            )
        })?;
        self.world
            .resolve_spec_decl(self.namespace, &contract)
            .map_err(|error| {
                emit_job_diagnostic(
                    self.telemetry,
                    Diagnostic::error(
                        codes::RESOLVE_TYPE_ALIAS,
                        format!(
                            "compiler2 could not resolve native contract for `{}`: {}",
                            self.surface.name, error.msg
                        ),
                        error.span,
                    ),
                )
            })
    }

    fn lower_clause(&mut self, clause: &FnClause) -> Result<ExprClause, FatalError> {
        let mut env = HashMap::new();
        let mut projections = Vec::new();
        let mut params = Vec::new();
        if self.surface.is_macro {
            let value = self.fresh_value();
            params.push(value);
            env.insert("__CALLER__".to_string(), value);
        }
        for capture in self.source.capture_params.clone() {
            let value = self.fresh_value();
            params.push(value);
            env.insert(capture, value);
        }
        for param in &clause.params {
            let value = self.fresh_value();
            params.push(value);
            self.bind_pattern(&param.node, param.span, value, &mut env, &mut projections)?;
        }

        let body = self.lower_expr_as_block(&clause.body, env)?;

        Ok(ExprClause {
            span: clause.span,
            params,
            projections,
            body,
        })
    }

    fn lower_expr_as_block(
        &mut self,
        expr: &Spanned<Expr>,
        mut env: HashMap<String, ValueId>,
    ) -> Result<ExprBlock, FatalError> {
        let mut steps = Vec::new();
        let result = self.lower_expr(expr, &mut env, &mut steps)?;
        Ok(ExprBlock {
            span: expr.span,
            steps,
            result,
        })
    }

    fn lower_expr(
        &mut self,
        expr: &Spanned<Expr>,
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        match &expr.node {
            Expr::Int(value) => Ok(self.push_const(steps, GroundValue::Int(*value))),
            Expr::Float(value) => Ok(self.push_const(steps, GroundValue::from_f64(*value))),
            Expr::Binary(value) => Ok(self.push_const(steps, GroundValue::Binary(value.clone()))),
            Expr::Atom(value) => Ok(self.push_const(steps, GroundValue::Atom(value.clone()))),
            Expr::Bool(value) => Ok(self.push_const(steps, GroundValue::Bool(*value))),
            Expr::Nil => Ok(self.push_const(steps, GroundValue::Nil)),
            Expr::Module(module) => Ok(QuoteLowerer::new(self, env, steps).lower_module(module, expr.span)),
            Expr::Var(name) => {
                if let Some(value) = env.get(name) {
                    return Ok(*value);
                }
                match self.world.lookup_namespace(self.namespace, name) {
                    Some(NamespaceSymbol::Function(function)) => {
                        let value = self.fresh_value();
                        steps.push(ExprStep::FunctionRef { value, function });
                        Ok(value)
                    }
                    Some(NamespaceSymbol::Callable(function)) => {
                        let module = self.world.function_module(function);
                        if let Some(interface) = self.world.module_interface_if_present(module)
                            && let Some(callable) = interface
                                .callables()
                                .iter()
                                .find(|callable| callable.function == function)
                        {
                            return match callable.kind {
                                InterfaceCallableKind::PublicFunction => {
                                    let value = self.fresh_value();
                                    steps.push(ExprStep::FunctionRef { value, function });
                                    Ok(value)
                                }
                                InterfaceCallableKind::Macro => Err(emit_job_diagnostic(
                                    self.telemetry,
                                    Diagnostic::error(
                                        codes::LOWER_UNSUPPORTED,
                                        format!("macro `{name}` cannot be used as a runtime value"),
                                        expr.span,
                                    ),
                                )),
                                InterfaceCallableKind::Callable => unreachable!(
                                    "settled module interfaces should not publish unresolved callable kinds"
                                ),
                            };
                        }
                        Err(emit_job_diagnostic(
                            self.telemetry,
                            Diagnostic::error(
                                codes::LOWER_UNSUPPORTED,
                                format!(
                                    "compiler2 lowering needs the callable kind for `{name}` before it can use it as a runtime value"
                                ),
                                expr.span,
                            ),
                        ))
                    }
                    Some(NamespaceSymbol::Macro(_)) => Err(emit_job_diagnostic(
                        self.telemetry,
                        Diagnostic::error(
                            codes::LOWER_UNSUPPORTED,
                            format!("macro `{name}` cannot be used as a runtime value"),
                            expr.span,
                        ),
                    )),
                    Some(NamespaceSymbol::Module(_))
                    | Some(NamespaceSymbol::Type(_))
                    | Some(NamespaceSymbol::Splice(_))
                    | None => Err(emit_job_diagnostic(
                        self.telemetry,
                        Diagnostic::error(
                            codes::LOWER_UNBOUND,
                            format!("compiler2 lowering found unresolved value `{name}`"),
                            expr.span,
                        ),
                    )),
                }
            }
            Expr::FnRef { name, arity } => {
                let value = self.fresh_value();
                let function = self.resolve_callable_name(name, *arity, expr.span, "captured runtime function")?;
                steps.push(ExprStep::FunctionRef { value, function });
                Ok(value)
            }
            Expr::List(items, tail) => {
                let mut lowered = Vec::with_capacity(items.len());
                for item in items {
                    lowered.push(self.lower_expr(item, env, steps)?);
                }
                let tail = tail
                    .as_ref()
                    .map(|tail| self.lower_expr(tail, env, steps))
                    .transpose()?;
                let value = self.fresh_value();
                steps.push(ExprStep::List {
                    value,
                    items: lowered,
                    tail,
                });
                Ok(value)
            }
            Expr::Tuple(items) => {
                let mut lowered = Vec::with_capacity(items.len());
                for item in items {
                    lowered.push(self.lower_expr(item, env, steps)?);
                }
                let value = self.fresh_value();
                steps.push(ExprStep::Tuple { value, items: lowered });
                Ok(value)
            }
            Expr::Map(entries) => {
                let mut lowered = Vec::with_capacity(entries.len());
                for (key, value) in entries {
                    let lowered_key = LoweredMapKey {
                        value: self.lower_expr(key, env, steps)?,
                        literal: expr_literal(&key.node),
                    };
                    lowered.push((lowered_key, self.lower_expr(value, env, steps)?));
                }
                let value = self.fresh_value();
                steps.push(ExprStep::Map {
                    value,
                    entries: lowered,
                    quoted_span: None,
                });
                Ok(value)
            }
            Expr::MapUpdate(base, entries) => {
                let base = self.lower_expr(base, env, steps)?;
                let mut lowered = Vec::with_capacity(entries.len());
                for (key, value) in entries {
                    let lowered_key = LoweredMapKey {
                        value: self.lower_expr(key, env, steps)?,
                        literal: expr_literal(&key.node),
                    };
                    lowered.push((lowered_key, self.lower_expr(value, env, steps)?));
                }
                let value = self.fresh_value();
                steps.push(ExprStep::MapUpdate {
                    value,
                    base,
                    entries: lowered,
                });
                Ok(value)
            }
            Expr::Struct { module, fields } => self.lower_struct_expr(expr.span, module, fields, env, steps),
            Expr::Bitstring(fields) => self.lower_bitstring_expr(fields, env, steps),
            Expr::Index(base, key) => {
                let base = self.lower_expr(base, env, steps)?;
                let value = self.fresh_value();
                if let Expr::Atom(field) = &key.node {
                    steps.push(ExprStep::FieldAccess {
                        value,
                        base,
                        field: field.clone(),
                    });
                } else {
                    let lowered_key = LoweredMapKey {
                        value: self.lower_expr(key, env, steps)?,
                        literal: expr_literal(&key.node),
                    };
                    steps.push(ExprStep::MapIndex {
                        value,
                        base,
                        key: lowered_key,
                    });
                }
                Ok(value)
            }
            Expr::Call(target, args) => {
                let lowered_args = self.lower_call_args(args, env, steps)?;
                let callsite = self.fresh_callsite(expr.span);
                if let Some(name) = direct_call_name(target, env) {
                    let value = self.fresh_value();
                    steps.push(ExprStep::DirectCall {
                        value,
                        callsite,
                        callee: self.resolve_callable_name(&name, args.len(), target.span, "direct runtime callee")?,
                        args: lowered_args,
                    });
                    return Ok(value);
                }
                let callee = self.lower_expr(target, env, steps)?;
                let value = self.fresh_value();
                steps.push(ExprStep::ClosureCall {
                    value,
                    callsite,
                    callee,
                    args: lowered_args,
                });
                Ok(value)
            }
            Expr::ClosureCall(target, args) => {
                let callee = self.lower_expr(target, env, steps)?;
                let lowered_args = self.lower_call_args(args, env, steps)?;
                let value = self.fresh_value();
                steps.push(ExprStep::ClosureCall {
                    value,
                    callsite: self.fresh_callsite(expr.span),
                    callee,
                    args: lowered_args,
                });
                Ok(value)
            }
            Expr::BinOp(op, left, right) => {
                let left = self.lower_expr(left, env, steps)?;
                let right = self.lower_expr(right, env, steps)?;
                if let Some(name) = direct_operator_name(*op) {
                    let value = self.fresh_value();
                    steps.push(ExprStep::DirectCall {
                        value,
                        callsite: self.fresh_callsite(expr.span),
                        callee: self.resolve_direct_callee(name, 2, expr.span)?,
                        args: vec![
                            CallArg {
                                value: left,
                                ascription: None,
                                ownership: crate::fz_ir::OwnershipMode::Share,
                            },
                            CallArg {
                                value: right,
                                ascription: None,
                                ownership: crate::fz_ir::OwnershipMode::Share,
                            },
                        ],
                    });
                    Ok(value)
                } else {
                    let value = self.fresh_value();
                    steps.push(ExprStep::BinaryOp {
                        value,
                        op: *op,
                        left,
                        right,
                    });
                    Ok(value)
                }
            }
            Expr::UnOp(op, input) => {
                let input = self.lower_expr(input, env, steps)?;
                let value = self.fresh_value();
                steps.push(ExprStep::UnaryOp { value, op: *op, input });
                Ok(value)
            }
            Expr::Ascribe(inner, _) => self.lower_expr(inner, env, steps),
            Expr::Match(pattern, rhs) => {
                let value = self.lower_expr(rhs, env, steps)?;
                self.apply_pattern(&pattern.node, pattern.span, value, env, steps)?;
                Ok(value)
            }
            Expr::Block(exprs) => {
                if exprs.is_empty() {
                    return Ok(self.push_const(steps, GroundValue::Nil));
                }
                let mut last = None;
                for expr in exprs {
                    last = Some(self.lower_expr(expr, env, steps)?);
                }
                Ok(last.expect("non-empty block should yield a result"))
            }
            Expr::If(cond, then_expr, else_expr) => {
                let cond = self.lower_expr(cond, env, steps)?;
                let then_block = self.lower_expr_as_block(then_expr, env.clone())?;
                let else_block = if let Some(else_expr) = else_expr {
                    self.lower_expr_as_block(else_expr, env.clone())?
                } else {
                    let nil_span = expr.span;
                    let result = self.fresh_value();
                    ExprBlock {
                        span: nil_span,
                        steps: vec![ExprStep::Const {
                            value: result,
                            literal: GroundValue::Nil,
                        }],
                        result,
                    }
                };
                let value = self.fresh_value();
                steps.push(ExprStep::If {
                    value,
                    cond,
                    then_block,
                    else_block,
                });
                Ok(value)
            }
            Expr::Case(Some(subject), clauses) => self.lower_case(expr.span, subject, clauses, env, steps),
            Expr::Case(None, _) => Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "source-only headless `case` reached body lowering without a pipe subject".to_string(),
                    expr.span,
                ),
            )),
            Expr::Cond(arms) => self.lower_cond(expr.span, arms, env, steps),
            Expr::With(bindings, body, else_clauses) => {
                self.lower_with(expr.span, bindings, body, else_clauses, env, steps)
            }
            Expr::Receive { clauses, after } => self.lower_receive(expr.span, clauses, after.as_deref(), env, steps),
            Expr::Lambda { occurrence, clauses } => self.lower_lambda(*occurrence, expr.span, clauses, env, steps),
            Expr::Quote(inner) => QuoteLowerer::new(self, env, steps).lower(inner),
            Expr::Unquote(_) => Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "compiler2 lowering found `unquote` outside `quote`".to_string(),
                    expr.span,
                ),
            )),
            Expr::Capture(_) | Expr::CaptureArg(_) => Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("compiler2 does not lower `{}` yet", expr_name(&expr.node)),
                    expr.span,
                ),
            )),
        }
    }

    fn resolve_direct_callee(&mut self, name: &str, arity: usize, span: Span) -> Result<FunctionId, FatalError> {
        let function = self.resolve_runtime_function(name, arity, span, "direct runtime callee")?;
        Ok(function)
    }

    fn resolve_callable_name(
        &mut self,
        name: &CallableName,
        arity: usize,
        span: Span,
        context: &str,
    ) -> Result<FunctionId, FatalError> {
        match &name.module {
            Some(module) => {
                let module = self.world.reference_module_denotation(module.clone());
                self.resolve_module_callee(module, &name.name, arity, span)
            }
            None => self.resolve_runtime_function(&name.name, arity, span, context),
        }
    }

    fn resolve_module_callee(
        &mut self,
        module: ModuleId,
        name: &str,
        arity: usize,
        span: Span,
    ) -> Result<FunctionId, FatalError> {
        let minimum = self.world.min_module_variadic_arity(module, name);
        if minimum.is_some_and(|minimum| arity < minimum) {
            let label = format!(
                "{}.{}",
                self.world.module_denotation(module).expect("qualified callee module"),
                name
            );
            self.check_variadic_arity(&label, arity, span, minimum)?;
        }
        if let Some(function) = self
            .world
            .module_interface_if_present(module)
            .and_then(|interface| interface.public_function_with_name_arity(name, arity))
        {
            return Ok(function);
        }
        Ok(self.world.reference_module_interface_callable(
            module,
            name.to_string(),
            arity,
            InterfaceCallableKind::PublicFunction,
            Some(self.interface_requester(span)),
        ))
    }

    fn resolve_runtime_function(
        &mut self,
        name: &str,
        arity: usize,
        span: Span,
        context: &str,
    ) -> Result<FunctionId, FatalError> {
        if let Some((module_path, local_name)) = name.rsplit_once('.') {
            let Ok(module_path) = ModuleName::parse_dotted(module_path) else {
                return Err(self.unbound_runtime_function(name, arity, span, context));
            };
            let Some(module) = self.world.lookup_module_path(self.namespace, &module_path) else {
                return Err(self.unbound_runtime_function(name, arity, span, context));
            };
            return self.resolve_module_callee(module, local_name, arity, span);
        }

        match self.world.lookup_callable_namespace(self.namespace, name, arity) {
            Some(NamespaceSymbol::Function(function)) | Some(NamespaceSymbol::Callable(function)) => Ok(function),
            Some(NamespaceSymbol::Macro(_)) => Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("macro call `{name}/{arity}` reached body lowering without source expansion"),
                    span,
                ),
            )),
            Some(NamespaceSymbol::Module(_))
            | Some(NamespaceSymbol::Type(_))
            | Some(NamespaceSymbol::Splice(_))
            | None => {
                self.reject_too_few_variadic_args(name, arity, span)?;
                Err(self.unbound_runtime_function(name, arity, span, context))
            }
        }
    }

    fn reject_too_few_variadic_args(&mut self, name: &str, arity: usize, span: Span) -> Result<(), FatalError> {
        let minimum = self.world.min_variadic_arity(self.namespace, name);
        self.check_variadic_arity(name, arity, span, minimum)
    }

    fn check_variadic_arity(
        &self,
        name: &str,
        arity: usize,
        span: Span,
        minimum: Option<usize>,
    ) -> Result<(), FatalError> {
        if let Some(fixed_arity) = minimum
            && arity < fixed_arity
        {
            return Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!(
                        "variadic fn `{}` expects at least {} arg(s), but this call provides {}",
                        name, fixed_arity, arity
                    ),
                    span,
                ),
            ));
        }
        Ok(())
    }

    fn interface_requester(&self, span: Span) -> InterfaceRequester {
        InterfaceRequester {
            owner: self.source.owner,
            module: self.source.owner_module,
            span,
        }
    }

    fn unbound_runtime_function(&mut self, name: &str, arity: usize, span: Span, context: &str) -> FatalError {
        emit_job_diagnostic(
            self.telemetry,
            Diagnostic::error(
                codes::LOWER_UNBOUND,
                format!("compiler2 lowering found unresolved {context} `{name}/{arity}`"),
                span,
            ),
        )
    }

    fn lower_call_args(
        &mut self,
        args: &[Spanned<Expr>],
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<Vec<CallArg>, FatalError> {
        let mut lowered = Vec::with_capacity(args.len());
        for arg in args {
            let (expr, ascription) = match &arg.node {
                Expr::Ascribe(inner, ty) => (inner.as_ref(), Some(ty.clone())),
                _ => (arg, None),
            };
            lowered.push(CallArg {
                value: self.lower_expr(expr, env, steps)?,
                ascription,
                ownership: crate::fz_ir::OwnershipMode::Share,
            });
        }
        Ok(lowered)
    }

    fn lower_struct_expr(
        &mut self,
        span: Span,
        module: &crate::ast::ModuleTarget,
        fields: &[(String, Spanned<Expr>)],
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let module_id = self.resolve_struct_module(module, span)?;
        // `collect_local_dispatch_requirements`'s `Expr::Struct` arm already
        // recorded this literal's field obligations and waited on
        // `StructDefined(module_id)` before `lower_function` built this
        // `Lowerer`, so the ordered schema is present by construction; an
        // unknown field is diagnosed durably by
        // `World::validate_struct_field_expectations` at settle time (the
        // same obligation store `note_struct_field_expectation` recorded
        // into), not by a local synchronous check here. The literal's own
        // field order is only a fallback for the unreachable case where the
        // schema is somehow still absent, mirroring `resolve.rs`'s
        // `TypeExpr::StructRecord` arm.
        let order = self
            .world
            .struct_def_fields(module_id)
            .map(|fields| fields.to_vec())
            .unwrap_or_else(|| fields.iter().map(|(name, _)| name.clone()).collect());
        let mut by_name = fields
            .iter()
            .map(|(name, expr)| (name.as_str(), expr))
            .collect::<HashMap<_, _>>();
        let mut lowered = Vec::with_capacity(order.len());
        for field in order {
            let value = if let Some(expr) = by_name.remove(field.as_str()) {
                self.lower_expr(expr, env, steps)?
            } else {
                self.push_const(steps, GroundValue::Nil)
            };
            lowered.push((field, value));
        }
        let value = self.fresh_value();
        steps.push(ExprStep::Struct {
            value,
            module: module_id,
            fields: lowered,
        });
        Ok(value)
    }

    fn lower_bitstring_expr(
        &mut self,
        fields: &[BitField<Spanned<Expr>>],
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let mut lowered = Vec::with_capacity(fields.len());
        for field in fields {
            lowered.push(LoweredBitField {
                value: self.lower_expr(&field.value, env, steps)?,
                spec: self.lower_bitfield_spec(
                    &field.spec.size,
                    field.spec.ty,
                    field.spec.endian,
                    field.spec.signed,
                    field.spec.unit,
                    field.value.span,
                    env,
                )?,
            });
        }
        let value = self.fresh_value();
        steps.push(ExprStep::Bitstring { value, fields: lowered });
        Ok(value)
    }

    fn lower_bitfield_spec(
        &mut self,
        size: &Option<BitSize>,
        ty: crate::ast::BitType,
        endian: crate::ast::Endian,
        signed: bool,
        unit: Option<u32>,
        span: Span,
        env: &HashMap<String, ValueId>,
    ) -> Result<LoweredBitFieldSpec, FatalError> {
        Ok(LoweredBitFieldSpec {
            ty,
            size: self.lower_bit_size(size, span, env)?,
            endian,
            signed,
            unit,
        })
    }

    fn lower_bit_size(
        &mut self,
        size: &Option<BitSize>,
        span: Span,
        env: &HashMap<String, ValueId>,
    ) -> Result<Option<LoweredBitSize>, FatalError> {
        Ok(match size {
            None => None,
            Some(BitSize::Literal(value)) => Some(LoweredBitSize::Literal(*value)),
            Some(BitSize::Var(name)) => Some(LoweredBitSize::Value(*env.get(name).ok_or_else(|| {
                emit_job_diagnostic(
                    self.telemetry,
                    Diagnostic::error(
                        codes::LOWER_UNBOUND,
                        format!("compiler2 lowering found unbound bit size name `{name}`"),
                        span,
                    ),
                )
            })?)),
        })
    }

    fn resolve_struct_module(
        &mut self,
        module: &crate::ast::ModuleTarget,
        span: Span,
    ) -> Result<super::super::identity::ModuleId, FatalError> {
        self.world
            .resolve_module_target(self.source.owner_module, self.namespace, module)
            .ok_or_else(|| {
                emit_job_diagnostic(
                    self.telemetry,
                    Diagnostic::error(
                        codes::LOWER_UNBOUND,
                        format!("compiler2 could not resolve struct module `{module}`"),
                        span,
                    ),
                )
            })
    }

    fn lower_case(
        &mut self,
        span: Span,
        subject: &Spanned<Expr>,
        clauses: &[MatchClause],
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let subject_value = self.lower_expr(subject, env, steps)?;
        let plan = self.compile_match_dispatch("case", span, match_rows(clauses))?;
        let bindings = self.lower_dispatch_bindings(&plan, &[subject_value], env, steps, span)?;
        let arm_blocks = clauses
            .iter()
            .enumerate()
            .map(|(index, clause)| self.lower_match_clause_block(&plan.outcomes[index], clause, env.clone()))
            .collect::<Result<Vec<_>, _>>()?;
        let value = self.fresh_value();
        steps.push(ExprStep::Dispatch {
            value,
            inputs: vec![subject_value],
            bindings,
            dispatch: Box::new(ExprDispatch {
                plan,
                arm_blocks,
                miss_block: self.halt_block(span, "case_clause"),
            }),
        });
        Ok(value)
    }

    fn lower_cond(
        &mut self,
        span: Span,
        arms: &[(Spanned<Expr>, Spanned<Expr>)],
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let block = self.lower_cond_block(span, arms, env.clone())?;
        steps.extend(block.steps);
        Ok(block.result)
    }

    fn lower_with(
        &mut self,
        span: Span,
        bindings: &[WithBinding],
        body: &Spanned<Expr>,
        else_clauses: &[MatchClause],
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let block = self.lower_with_block(span, bindings, body, else_clauses, env.clone())?;
        steps.extend(block.steps);
        Ok(block.result)
    }

    fn lower_cond_block(
        &mut self,
        span: Span,
        arms: &[(Spanned<Expr>, Spanned<Expr>)],
        mut env: HashMap<String, ValueId>,
    ) -> Result<ExprBlock, FatalError> {
        let Some((cond, body)) = arms.first() else {
            return Ok(self.halt_block(span, "cond_clause"));
        };

        let mut steps = Vec::new();
        let cond_value = self.lower_expr(cond, &mut env, &mut steps)?;
        let arm_block = self.lower_expr_as_block(body, env.clone())?;
        let miss_block = if arms.len() == 1 {
            self.halt_block(span, "cond_clause")
        } else {
            self.lower_cond_block(span, &arms[1..], env)?
        };
        let value = self.fresh_value();
        steps.push(ExprStep::Dispatch {
            value,
            inputs: vec![cond_value],
            bindings: DispatchBindings {
                pinned: Vec::new(),
                prepared: Vec::new(),
            },
            dispatch: Box::new(ExprDispatch {
                plan: self.compile_bool_true_dispatch(span)?,
                arm_blocks: vec![ExprOutcome {
                    outcome: crate::dispatch_matrix::OutcomeId(0),
                    arguments: Box::default(),
                    block: arm_block,
                }],
                miss_block,
            }),
        });
        Ok(ExprBlock {
            span,
            steps,
            result: value,
        })
    }

    fn lower_with_block(
        &mut self,
        span: Span,
        bindings: &[WithBinding],
        body: &Spanned<Expr>,
        else_clauses: &[MatchClause],
        mut env: HashMap<String, ValueId>,
    ) -> Result<ExprBlock, FatalError> {
        let Some((binding, rest)) = bindings.split_first() else {
            return self.lower_expr_as_block(body, env);
        };
        match binding {
            WithBinding::Bare(expr) => {
                let mut steps = Vec::new();
                let _ = self.lower_expr(expr, &mut env, &mut steps)?;
                let rest_block = self.lower_with_block(span, rest, body, else_clauses, env)?;
                steps.extend(rest_block.steps);
                Ok(ExprBlock {
                    span,
                    steps,
                    result: rest_block.result,
                })
            }
            WithBinding::Match(pattern, expr) => {
                let mut steps = Vec::new();
                let matched = self.lower_expr(expr, &mut env, &mut steps)?;
                let plan = self.compile_single_pattern_dispatch("with", pattern, span)?;
                let mut success_env = env.clone();
                let arguments = self.bind_outcome_arguments(&plan.outcomes[0], &mut success_env);
                let success_block = self.lower_with_block(span, rest, body, else_clauses, success_env)?;
                let miss_block = self.lower_with_fail_block(span, matched, else_clauses, env.clone())?;
                let bindings = self.lower_dispatch_bindings(&plan, &[matched], &env, &mut steps, pattern.span)?;
                let value = self.fresh_value();
                steps.push(ExprStep::Dispatch {
                    value,
                    inputs: vec![matched],
                    bindings,
                    dispatch: Box::new(ExprDispatch {
                        plan,
                        arm_blocks: vec![ExprOutcome {
                            outcome: crate::dispatch_matrix::OutcomeId(0),
                            arguments,
                            block: success_block,
                        }],
                        miss_block,
                    }),
                });
                Ok(ExprBlock {
                    span,
                    steps,
                    result: value,
                })
            }
        }
    }

    fn lower_with_fail_block(
        &mut self,
        span: Span,
        failed: ValueId,
        else_clauses: &[MatchClause],
        env: HashMap<String, ValueId>,
    ) -> Result<ExprBlock, FatalError> {
        if else_clauses.is_empty() {
            return Ok(ExprBlock {
                span,
                steps: Vec::new(),
                result: failed,
            });
        }
        let plan = self.compile_match_dispatch("with else", span, match_rows(else_clauses))?;
        let mut steps = Vec::new();
        let bindings = self.lower_dispatch_bindings(&plan, &[failed], &env, &mut steps, span)?;
        let arm_blocks = else_clauses
            .iter()
            .enumerate()
            .map(|(index, clause)| self.lower_match_clause_block(&plan.outcomes[index], clause, env.clone()))
            .collect::<Result<Vec<_>, _>>()?;
        let value = self.fresh_value();
        Ok(ExprBlock {
            span,
            steps: {
                steps.push(ExprStep::Dispatch {
                    value,
                    inputs: vec![failed],
                    bindings,
                    dispatch: Box::new(ExprDispatch {
                        plan,
                        arm_blocks,
                        miss_block: self.halt_block(span, "with_clause"),
                    }),
                });
                steps
            },
            result: value,
        })
    }

    fn lower_receive(
        &mut self,
        span: Span,
        clauses: &[MatchClause],
        after: Option<&AfterClause>,
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        if clauses.is_empty() && after.is_none() {
            return Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "compiler2 does not lower `receive` with no clauses and no `after`".to_string(),
                    span,
                ),
            ));
        }

        let timeout = after
            .map(|after| self.lower_expr(&after.timeout, env, steps))
            .transpose()?;
        let plan = self.compile_match_dispatch("receive", span, match_rows(clauses))?;
        let bindings = self.lower_dispatch_bindings(&plan, &[], env, steps, span)?;
        let captures = self.receive_capture_values(clauses, after, env);
        let outcomes = plan
            .outcomes
            .iter()
            .map(|outcome| self.lower_match_clause_block(outcome, &clauses[outcome.body_id as usize], env.clone()))
            .collect::<Result<Vec<_>, _>>()?;
        let after = after
            .map(|after| self.lower_receive_after(after, timeout.expect("receive after should have a timeout"), env))
            .transpose()?;
        let value = self.fresh_value();
        steps.push(ExprStep::Receive(Box::new(ExprReceive {
            value,
            bindings,
            dispatch: plan,
            outcomes,
            after,
            captures,
        })));
        Ok(value)
    }

    fn lower_match_clause_block(
        &mut self,
        outcome: &crate::dispatch_matrix::pattern::PatternDispatchOutcome,
        clause: &MatchClause,
        mut env: HashMap<String, ValueId>,
    ) -> Result<ExprOutcome, FatalError> {
        let arguments = self.bind_outcome_arguments(outcome, &mut env);
        let block = self.lower_expr_as_block(&clause.body, env)?;
        Ok(ExprOutcome {
            outcome: outcome.outcome,
            arguments,
            block,
        })
    }

    fn bind_outcome_arguments(
        &mut self,
        outcome: &crate::dispatch_matrix::pattern::PatternDispatchOutcome,
        env: &mut HashMap<String, ValueId>,
    ) -> Box<[super::super::body::OutcomeArgument]> {
        outcome
            .bindings
            .iter()
            .map(|binding| {
                let parameter = self.fresh_value();
                env.insert(binding.name.clone(), parameter);
                super::super::body::OutcomeArgument {
                    subject: binding.source,
                    parameter,
                    role: super::super::body::ValueRole::Semantic,
                }
            })
            .collect()
    }

    fn compile_match_dispatch(
        &mut self,
        label: &str,
        span: Span,
        rows: Vec<PatternRow<super::super::types::Ty>>,
    ) -> Result<crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>, FatalError> {
        let source = SourcePatternRows { input_count: 1, rows };
        let namespace = self.namespace;
        let mut resolver = super::super::dispatch::SourcePatternResolver {
            world: self.world,
            namespace,
            owner: self.source.owner_module,
            guard: |world: &mut World, name: &CallableName, arity: usize| {
                let callee = resolve_guard_callee_checked(world, namespace, name, arity);
                Ok(Some(world.guard_dispatch(callee)))
            },
        };
        pattern_dispatch_from_source_with_resolver(source, &mut resolver)
            .map_err(|error| emit_local_dispatch_error(self.telemetry, label, span, error))
    }

    fn compile_single_pattern_dispatch(
        &mut self,
        label: &str,
        pattern: &Spanned<Pattern>,
        span: Span,
    ) -> Result<crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>, FatalError> {
        self.compile_match_dispatch(
            label,
            span,
            vec![PatternRow {
                patterns: vec![pattern.clone()],
                preconditions: Vec::new(),
                guard: None,
                body_id: 0,
            }],
        )
    }

    fn compile_bool_true_dispatch(
        &mut self,
        span: Span,
    ) -> Result<crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>, FatalError> {
        pattern_dispatch_from_source(SourcePatternRows {
            input_count: 1,
            rows: vec![PatternRow {
                patterns: vec![Spanned::new(Pattern::Bool(true), span)],
                preconditions: Vec::new(),
                guard: None,
                body_id: 0,
            }],
        })
        .map_err(|error| emit_local_dispatch_error(self.telemetry, "cond", span, error))
    }

    fn lower_dispatch_bindings(
        &mut self,
        plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>,
        inputs: &[ValueId],
        env: &HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
        span: Span,
    ) -> Result<DispatchBindings, FatalError> {
        let pinned = plan
            .pinned
            .iter()
            .map(|pinned| {
                if let Some(input) = pinned.input {
                    return inputs.get(input as usize).copied().ok_or_else(|| {
                        emit_job_diagnostic(
                            self.telemetry,
                            Diagnostic::error(
                                codes::LOWER_UNSUPPORTED,
                                format!("compiler2 local dispatch input {} is out of bounds", input),
                                span,
                            ),
                        )
                    });
                }
                env.get(&pinned.name).copied().ok_or_else(|| {
                    emit_job_diagnostic(
                        self.telemetry,
                        Diagnostic::error(
                            codes::LOWER_UNBOUND,
                            format!("compiler2 local dispatch pinned name `{}` is unresolved", pinned.name),
                            pinned.span,
                        ),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let prepared = plan
            .prepared_keys
            .iter()
            .map(|key| self.materialize_dispatch_const(key, steps))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(DispatchBindings { pinned, prepared })
    }

    fn materialize_dispatch_const(
        &mut self,
        key: &crate::dispatch_matrix::GroundValue,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        use crate::ground_value::DispatchShape;
        let value = self.fresh_value();
        match key
            .as_dispatch_shape()
            .expect("materialize_dispatch_const only ever sees a dispatch-matrix const")
        {
            DispatchShape::Int(n) => steps.push(ExprStep::Const {
                value,
                literal: GroundValue::Int(n),
            }),
            DispatchShape::Float(bits) => steps.push(ExprStep::Const {
                value,
                literal: GroundValue::Float(bits),
            }),
            DispatchShape::Utf8Binary(bytes) => steps.push(ExprStep::Const {
                value,
                literal: GroundValue::Binary(bytes.to_vec()),
            }),
            DispatchShape::Atom(name) => steps.push(ExprStep::Const {
                value,
                literal: GroundValue::Atom(name.to_string()),
            }),
            DispatchShape::Bool(flag) => steps.push(ExprStep::Const {
                value,
                literal: GroundValue::Bool(flag),
            }),
            DispatchShape::Nil => steps.push(ExprStep::Const {
                value,
                literal: GroundValue::Nil,
            }),
        }
        Ok(value)
    }

    fn receive_capture_values(
        &mut self,
        clauses: &[MatchClause],
        after: Option<&AfterClause>,
        env: &HashMap<String, ValueId>,
    ) -> Vec<ValueId> {
        let mut free = HashSet::new();
        let mut bound = HashSet::new();
        collect_match_clause_free_names(clauses, &mut bound, &mut free);
        if let Some(after) = after {
            collect_expr_free_names(&after.timeout.node, &mut HashSet::new(), &mut free);
            collect_expr_free_names(&after.body.node, &mut HashSet::new(), &mut free);
        }
        let mut captures = free
            .into_iter()
            .filter_map(|name| env.get(&name).copied())
            .collect::<Vec<_>>();
        captures.sort_by_key(|value| value.as_u32());
        captures.dedup();
        captures
    }

    fn lower_receive_after(
        &mut self,
        after: &AfterClause,
        timeout: ValueId,
        env: &HashMap<String, ValueId>,
    ) -> Result<ExprReceiveAfter, FatalError> {
        Ok(ExprReceiveAfter {
            span: after.span,
            timeout,
            body: self.lower_expr_as_block(&after.body, env.clone())?,
        })
    }

    fn halt_block(&mut self, span: Span, atom: &str) -> ExprBlock {
        let value = self.fresh_value();
        ExprBlock {
            span,
            steps: vec![
                ExprStep::Const {
                    value,
                    literal: GroundValue::Nil,
                },
                ExprStep::Halt { atom: atom.to_string() },
            ],
            result: value,
        }
    }

    fn lower_lambda(
        &mut self,
        occurrence: crate::ast::LambdaOccurrence,
        span: Span,
        clauses: &[LambdaClause],
        env: &HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let value = self.fresh_value();
        let surface = FunctionSurface {
            name: "#lambda".to_string(),
            name_span: span,
            clauses: clauses
                .iter()
                .map(|clause| FnClause {
                    params: clause.params.clone(),
                    param_annotations: vec![None; clause.params.len()],
                    guard: clause.guard.clone(),
                    body: clause.body.clone(),
                    span: clause.span,
                })
                .collect(),
            is_macro: false,
            declaration: None,
            native_param_tokens: Vec::new(),
            native_ret_tokens: crate::ast::TypeExprBody(Vec::new()),
            native_constraints: Vec::new(),
            variadic: false,
            attrs: Vec::new(),
            span,
        };
        let mut capture_params = lambda_free_names(clauses)
            .into_iter()
            .filter(|name| env.contains_key(name))
            .collect::<Vec<_>>();
        capture_params.sort();
        let captures = capture_params
            .iter()
            .map(|name| *env.get(name).expect("captured names should resolve in the local env"))
            .collect::<Vec<_>>();

        let (function, changed) = super::super::drive::ExecutionContext::new(self.world, self.telemetry)
            .define_generated_function(self.owner, occurrence, self.namespace, capture_params, surface);
        self.generated.push(FactKey::FunctionDefined(function));
        if changed {
            self.generated_changed.push(FactKey::FunctionDefined(function));
        }
        self.generated_ids.push(function);

        let captures = captures.into_iter().collect::<Vec<_>>();
        steps.push(ExprStep::Lambda {
            value,
            function,
            captures,
        });
        Ok(value)
    }

    fn plan_clauses(&mut self, clauses: Vec<ExprClause>) -> LoweredBody {
        let mut lowered = Vec::with_capacity(clauses.len());
        let mut entries = Vec::new();
        let mut clause_bounds = HashMap::new();
        for clause in clauses {
            let projection_steps = clause.projections.iter().map(lower_projection_step).collect::<Vec<_>>();
            let entry = self.plan_block(
                clause.body,
                ControlEntryOrigin::Clause,
                ControlDestination::Return,
                Vec::new(),
                Vec::new(),
                &mut entries,
            );
            let mut bound = clause.params.iter().copied().collect::<HashSet<_>>();
            bound.extend(values_defined_by_steps(&projection_steps));
            clause_bounds.insert(entry, bound);
            lowered.push(LoweredClause {
                span: clause.span,
                params: clause.params,
                projections: projection_steps,
                entry,
            });
        }
        let mut body = LoweredBody::Clauses {
            clauses: lowered,
            entries,
            generated: self.generated_ids.clone(),
        };
        self.construct_entry_captures(&mut body, &clause_bounds);
        body
    }

    fn construct_entry_captures(
        &mut self,
        body: &mut LoweredBody,
        clause_bounds: &HashMap<ControlEntryId, HashSet<ValueId>>,
    ) {
        use super::super::executable_facts::{TransportOrigin, collect_callsite_return_origins, collect_value_origins};
        use crate::fz_ir::{ListRetention, ListRewritePermission};
        let origins = collect_value_origins(body, &collect_callsite_return_origins(body));
        let LoweredBody::Clauses { entries, .. } = body else {
            unreachable!()
        };
        let constructions = entries
            .iter()
            .enumerate()
            .flat_map(|(entry, block)| {
                block.steps.iter().enumerate().filter_map(move |(step, instruction)| {
                    let LoweredStep::List {
                        items, tail: Some(_), ..
                    } = instruction
                    else {
                        return None;
                    };
                    (items.len() == 1).then_some((entry, step, items[0]))
                })
            })
            .collect::<Vec<_>>();
        let sources = constructions
            .iter()
            .filter_map(|&(entry, step, head)| {
                let origin = list_source_origin(body, &origins, head)?;
                Some((entry, step, head, origin))
            })
            .collect::<Vec<_>>();
        for (entry, step, head, origin) in &sources {
            let source = match origin {
                TransportOrigin::LocalValue(source) => *source,
                TransportOrigin::OutcomeSubject { owner, subject } => {
                    let LoweredBody::Clauses { entries, .. } = body else {
                        unreachable!()
                    };
                    let (target, existing) = {
                        let edge = entries[owner.as_u32() as usize]
                            .tail
                            .outcome_edges()
                            .iter()
                            .find(|edge| edge.arguments.iter().any(|argument| argument.parameter == *head))
                            .expect("head has a winning edge");
                        (
                            edge.target,
                            edge.arguments
                                .iter()
                                .find(|argument| argument.subject == *subject)
                                .map(|argument| argument.parameter),
                        )
                    };
                    if let Some(existing) = existing {
                        existing
                    } else {
                        let parameter = self.fresh_value();
                        entries[target.as_u32() as usize].params.push(parameter);
                        entries[target.as_u32() as usize].physical_params.push(parameter);
                        let edge = entries[owner.as_u32() as usize]
                            .tail
                            .outcome_edges_mut()
                            .iter_mut()
                            .find(|edge| edge.target == target)
                            .expect("physical subject has its target");
                        let mut arguments = std::mem::take(&mut edge.arguments).into_vec();
                        arguments.push(super::super::body::OutcomeArgument {
                            subject: *subject,
                            parameter,
                            role: super::super::body::ValueRole::Physical,
                        });
                        edge.arguments = arguments.into_boxed_slice();
                        parameter
                    }
                }
                _ => unreachable!("a list source is a local value or a plan-owned subject"),
            };
            let LoweredBody::Clauses { entries, .. } = body else {
                unreachable!()
            };
            let LoweredStep::List { retention, .. } = &mut entries[*entry].steps[*step] else {
                unreachable!()
            };
            *retention = Some(ListRetention {
                source,
                permission: ListRewritePermission::RetainOnly,
            });
        }
        let LoweredBody::Clauses { entries, .. } = body else {
            unreachable!()
        };
        let semantic = compute_entry_captures(entries, clause_bounds, false);
        let mut physical = compute_entry_captures(entries, clause_bounds, true);
        for entry in entries.iter() {
            let LoweredTail::Receive(receive) = &entry.tail else {
                continue;
            };
            let targets = receive
                .outcomes
                .iter()
                .map(|edge| edge.target)
                .chain(receive.after.iter().map(|after| after.entry))
                .collect::<Vec<_>>();
            let mut shared = targets
                .iter()
                .flat_map(|target| physical[target.as_u32() as usize].iter().copied())
                .collect::<Vec<_>>();
            shared.sort_unstable_by_key(|value| value.as_u32());
            shared.dedup();
            for target in targets {
                physical[target.as_u32() as usize] = shared.clone();
            }
        }
        for ((entry, captures), retained) in entries.iter_mut().zip(semantic).zip(physical) {
            entry.physical_captures = retained.into_iter().filter(|value| !captures.contains(value)).collect();
            entry.captures = captures;
        }
        let origins = collect_value_origins(body, &collect_callsite_return_origins(body));
        construct_call_ownership(body, &origins);
        construct_tuple_ownership(body, &origins);
        for (entry, step, _, _) in sources {
            let permission = if list_can_rewrite(body, &origins, entry, step) {
                ListRewritePermission::Rewrite
            } else {
                ListRewritePermission::RetainOnly
            };
            let LoweredBody::Clauses { entries, .. } = body else {
                unreachable!()
            };
            let LoweredStep::List {
                retention: Some(retention),
                ..
            } = &mut entries[entry].steps[step]
            else {
                unreachable!()
            };
            retention.permission = permission;
        }
    }

    fn plan_block(
        &mut self,
        block: ExprBlock,
        origin: ControlEntryOrigin,
        dest: ControlDestination,
        params: Vec<ValueId>,
        captures: Vec<ValueId>,
        entries: &mut Vec<LoweredEntry>,
    ) -> ControlEntryId {
        let (steps, tail) = self.plan_steps(&block, dest, entries);
        let entry_id = ControlEntryId::from_u32(entries.len() as u32);
        entries.push(LoweredEntry {
            span: block.span,
            origin,
            params,
            captures,
            physical_captures: Vec::new(),
            physical_params: Vec::new(),
            steps,
            tail,
        });
        entry_id
    }

    fn plan_steps(
        &mut self,
        block: &ExprBlock,
        dest: ControlDestination,
        entries: &mut Vec<LoweredEntry>,
    ) -> (Vec<LoweredStep>, LoweredTail) {
        let mut lowered = Vec::new();
        for (index, step) in block.steps.iter().enumerate() {
            match step {
                ExprStep::DirectCall {
                    value,
                    callsite,
                    callee,
                    args,
                } => {
                    let tail_dest = if index + 1 == block.steps.len() && *value == block.result {
                        dest
                    } else {
                        let resume = self.plan_block(
                            ExprBlock {
                                span: block.span,
                                steps: block.steps[index + 1..].to_vec(),
                                result: block.result,
                            },
                            ControlEntryOrigin::DeliveredResume { value: *value },
                            dest,
                            Vec::new(),
                            Vec::new(),
                            entries,
                        );
                        ControlDestination::Deliver(resume)
                    };
                    return (
                        lowered,
                        LoweredTail::DirectCall {
                            value: *value,
                            callsite: *callsite,
                            callee: *callee,
                            args: args.clone(),
                            dest: tail_dest,
                        },
                    );
                }
                ExprStep::ClosureCall {
                    value,
                    callsite,
                    callee,
                    args,
                } => {
                    let tail_dest = if index + 1 == block.steps.len() && *value == block.result {
                        dest
                    } else {
                        let resume = self.plan_block(
                            ExprBlock {
                                span: block.span,
                                steps: block.steps[index + 1..].to_vec(),
                                result: block.result,
                            },
                            ControlEntryOrigin::DeliveredResume { value: *value },
                            dest,
                            Vec::new(),
                            Vec::new(),
                            entries,
                        );
                        ControlDestination::Deliver(resume)
                    };
                    return (
                        lowered,
                        LoweredTail::ClosureCall {
                            value: *value,
                            callsite: *callsite,
                            callee: *callee,
                            args: args.clone(),
                            dest: tail_dest,
                        },
                    );
                }
                ExprStep::If {
                    value,
                    cond,
                    then_block,
                    else_block,
                } => {
                    let branch_dest = if index + 1 == block.steps.len() && *value == block.result {
                        dest
                    } else {
                        let resume = self.plan_block(
                            ExprBlock {
                                span: block.span,
                                steps: block.steps[index + 1..].to_vec(),
                                result: block.result,
                            },
                            ControlEntryOrigin::DeliveredResume { value: *value },
                            dest,
                            Vec::new(),
                            Vec::new(),
                            entries,
                        );
                        ControlDestination::Deliver(resume)
                    };
                    let then_entry = self.plan_block(
                        then_block.clone(),
                        ControlEntryOrigin::Branch,
                        branch_dest.clone(),
                        Vec::new(),
                        Vec::new(),
                        entries,
                    );
                    let else_entry = self.plan_block(
                        else_block.clone(),
                        ControlEntryOrigin::Branch,
                        branch_dest,
                        Vec::new(),
                        Vec::new(),
                        entries,
                    );
                    return (
                        lowered,
                        LoweredTail::If {
                            cond: *cond,
                            then_entry,
                            else_entry,
                        },
                    );
                }
                ExprStep::Dispatch {
                    value,
                    inputs,
                    bindings,
                    dispatch,
                } => {
                    let branch_dest = if index + 1 == block.steps.len() && *value == block.result {
                        dest
                    } else {
                        let resume = self.plan_block(
                            ExprBlock {
                                span: block.span,
                                steps: block.steps[index + 1..].to_vec(),
                                result: block.result,
                            },
                            ControlEntryOrigin::DeliveredResume { value: *value },
                            dest,
                            Vec::new(),
                            Vec::new(),
                            entries,
                        );
                        ControlDestination::Deliver(resume)
                    };
                    let outcomes = dispatch
                        .arm_blocks
                        .iter()
                        .cloned()
                        .map(|arm| {
                            let params = arm.arguments.iter().map(|argument| argument.parameter).collect();
                            let target = self.plan_block(
                                arm.block,
                                ControlEntryOrigin::Branch,
                                branch_dest.clone(),
                                params,
                                Vec::new(),
                                entries,
                            );
                            super::super::body::OutcomeEdge {
                                outcome: arm.outcome,
                                target,
                                arguments: arm.arguments,
                            }
                        })
                        .collect::<Vec<_>>();
                    let miss_entry = self.plan_block(
                        dispatch.miss_block.clone(),
                        ControlEntryOrigin::Branch,
                        branch_dest,
                        Vec::new(),
                        Vec::new(),
                        entries,
                    );
                    return (
                        lowered,
                        LoweredTail::Dispatch {
                            inputs: inputs.clone(),
                            bindings: bindings.clone(),
                            dispatch: Box::new(ControlDispatch {
                                plan: dispatch.plan.clone(),
                                outcomes,
                                miss_entry,
                            }),
                        },
                    );
                }
                ExprStep::Receive(receive) => {
                    let value = receive.value;
                    let bindings = &receive.bindings;
                    let dispatch = &receive.dispatch;
                    let outcomes = &receive.outcomes;
                    let after = &receive.after;
                    let captures = &receive.captures;
                    let branch_dest = if index + 1 == block.steps.len() && value == block.result {
                        dest
                    } else {
                        let resume = self.plan_block(
                            ExprBlock {
                                span: block.span,
                                steps: block.steps[index + 1..].to_vec(),
                                result: block.result,
                            },
                            ControlEntryOrigin::DeliveredResume { value },
                            dest,
                            Vec::new(),
                            Vec::new(),
                            entries,
                        );
                        ControlDestination::Deliver(resume)
                    };
                    let receive_dest = branch_dest.clone();
                    let outcomes = outcomes
                        .iter()
                        .map(|outcome| {
                            let target = self.plan_block(
                                outcome.block.clone(),
                                ControlEntryOrigin::ReceiveOutcome,
                                branch_dest.clone(),
                                outcome.arguments.iter().map(|argument| argument.parameter).collect(),
                                captures.clone(),
                                entries,
                            );
                            super::super::body::OutcomeEdge {
                                outcome: outcome.outcome,
                                arguments: outcome.arguments.clone(),
                                target,
                            }
                        })
                        .collect::<Vec<_>>();
                    let after = after.as_ref().map(|after| {
                        let entry = self.plan_block(
                            after.body.clone(),
                            ControlEntryOrigin::ReceiveOutcome,
                            branch_dest,
                            Vec::new(),
                            captures.clone(),
                            entries,
                        );
                        ReceiveAfter {
                            span: after.span,
                            timeout: after.timeout,
                            entry,
                        }
                    });
                    return (
                        lowered,
                        LoweredTail::Receive(Box::new(super::super::body::LoweredReceive {
                            bindings: bindings.clone(),
                            dispatch: dispatch.clone(),
                            outcomes,
                            after,
                            dest: receive_dest,
                        })),
                    );
                }
                ExprStep::Halt { atom } => {
                    return (lowered, LoweredTail::Halt { atom: atom.clone() });
                }
                _ => lowered.push(lower_projection_step(step)),
            }
        }
        (
            lowered,
            LoweredTail::Value {
                value: block.result,
                dest,
            },
        )
    }

    fn apply_pattern(
        &mut self,
        pattern: &Pattern,
        span: Span,
        source: ValueId,
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<(), FatalError> {
        match pattern {
            Pattern::Wildcard => Ok(()),
            Pattern::Var(name) => {
                env.insert(name.clone(), source);
                Ok(())
            }
            Pattern::Int(value) => {
                steps.push(ExprStep::AssertLiteral {
                    source,
                    literal: GroundValue::Int(*value),
                });
                Ok(())
            }
            Pattern::Float(value) => {
                steps.push(ExprStep::AssertLiteral {
                    source,
                    literal: GroundValue::from_f64(*value),
                });
                Ok(())
            }
            Pattern::Binary(value) => {
                steps.push(ExprStep::AssertLiteral {
                    source,
                    literal: GroundValue::Binary(value.clone()),
                });
                Ok(())
            }
            Pattern::Atom(value) => {
                steps.push(ExprStep::AssertLiteral {
                    source,
                    literal: GroundValue::Atom(value.clone()),
                });
                Ok(())
            }
            Pattern::Bool(value) => {
                steps.push(ExprStep::AssertLiteral {
                    source,
                    literal: GroundValue::Bool(*value),
                });
                Ok(())
            }
            Pattern::Nil => {
                steps.push(ExprStep::AssertLiteral {
                    source,
                    literal: GroundValue::Nil,
                });
                Ok(())
            }
            Pattern::Tuple(items) => {
                steps.push(ExprStep::AssertTuple {
                    source,
                    arity: items.len(),
                });
                for (index, item) in items.iter().enumerate() {
                    let value = self.fresh_value();
                    steps.push(ExprStep::TupleField { value, source, index });
                    self.apply_pattern(&item.node, item.span, value, env, steps)?;
                }
                Ok(())
            }
            Pattern::List(items, tail) => {
                if items.is_empty() && tail.is_none() {
                    steps.push(ExprStep::AssertEmptyList { source });
                    return Ok(());
                }
                let mut current = source;
                for item in items {
                    let head = self.fresh_value();
                    let tail_value = self.fresh_value();
                    steps.push(ExprStep::SplitList {
                        source: current,
                        head,
                        tail: tail_value,
                    });
                    self.apply_pattern(&item.node, item.span, head, env, steps)?;
                    current = tail_value;
                }
                if let Some(tail) = tail {
                    self.apply_pattern(&tail.node, tail.span, current, env, steps)?;
                } else {
                    steps.push(ExprStep::AssertEmptyList { source: current });
                }
                Ok(())
            }
            Pattern::As(name, inner) => {
                env.insert(name.clone(), source);
                self.apply_pattern(&inner.node, inner.span, source, env, steps)
            }
            Pattern::Pinned(name) => {
                let Some(pinned) = env.get(name).copied() else {
                    return Err(emit_job_diagnostic(
                        self.telemetry,
                        Diagnostic::error(
                            codes::LOWER_UNBOUND,
                            format!("compiler2 lowering found unbound pinned name `{name}`"),
                            span,
                        ),
                    ));
                };
                steps.push(ExprStep::AssertSame { source, value: pinned });
                Ok(())
            }
            Pattern::Map(entries) => self.lower_map_pattern(entries, span, source, env, steps, true),
            Pattern::Struct { module, fields } => {
                self.lower_struct_pattern(module, fields, span, source, env, steps, true)
            }
            Pattern::Bitstring(fields) => self.lower_bitstring_pattern(fields, span, source, env, steps, true),
        }
    }

    fn bind_pattern(
        &mut self,
        pattern: &Pattern,
        span: Span,
        source: ValueId,
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<(), FatalError> {
        match pattern {
            Pattern::Wildcard
            | Pattern::Int(_)
            | Pattern::Float(_)
            | Pattern::Binary(_)
            | Pattern::Atom(_)
            | Pattern::Bool(_)
            | Pattern::Nil
            | Pattern::Pinned(_) => Ok(()),
            Pattern::Var(name) => {
                env.insert(name.clone(), source);
                Ok(())
            }
            Pattern::Tuple(items) => {
                for (index, item) in items.iter().enumerate() {
                    let value = self.fresh_value();
                    steps.push(ExprStep::TupleField { value, source, index });
                    self.bind_pattern(&item.node, item.span, value, env, steps)?;
                }
                Ok(())
            }
            Pattern::List(items, tail) => {
                let mut current = source;
                for item in items {
                    let head = self.fresh_value();
                    let tail_value = self.fresh_value();
                    steps.push(ExprStep::SplitList {
                        source: current,
                        head,
                        tail: tail_value,
                    });
                    self.bind_pattern(&item.node, item.span, head, env, steps)?;
                    current = tail_value;
                }
                if let Some(tail) = tail {
                    self.bind_pattern(&tail.node, tail.span, current, env, steps)?;
                }
                Ok(())
            }
            Pattern::As(name, inner) => {
                env.insert(name.clone(), source);
                self.bind_pattern(&inner.node, inner.span, source, env, steps)
            }
            Pattern::Map(entries) => self.lower_map_pattern(entries, span, source, env, steps, false),
            Pattern::Struct { module, fields } => {
                self.lower_struct_pattern(module, fields, span, source, env, steps, false)
            }
            Pattern::Bitstring(fields) => self.lower_bitstring_pattern(fields, span, source, env, steps, false),
        }
    }

    fn lower_map_pattern(
        &mut self,
        entries: &[(Spanned<Pattern>, Spanned<Pattern>)],
        span: Span,
        source: ValueId,
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
        with_asserts: bool,
    ) -> Result<(), FatalError> {
        for (key_pattern, value_pattern) in entries {
            let Some(key) = literal_from_pattern(&key_pattern.node) else {
                return Err(emit_job_diagnostic(
                    self.telemetry,
                    Diagnostic::error(
                        codes::LOWER_UNSUPPORTED,
                        format!(
                            "compiler2 map patterns require literal keys, found `{}`",
                            pattern_name(&key_pattern.node)
                        ),
                        key_pattern.span,
                    ),
                ));
            };
            let value = self.fresh_value();
            steps.push(ExprStep::RequireMapValue { value, source, key });
            if with_asserts {
                self.apply_pattern(&value_pattern.node, value_pattern.span, value, env, steps)?;
            } else {
                self.bind_pattern(&value_pattern.node, value_pattern.span, value, env, steps)?;
            }
        }
        let _ = span;
        Ok(())
    }

    fn lower_struct_pattern(
        &mut self,
        module: &crate::ast::ModuleTarget,
        fields: &[(String, Spanned<Pattern>)],
        span: Span,
        source: ValueId,
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
        with_asserts: bool,
    ) -> Result<(), FatalError> {
        let module_id = self.resolve_struct_module(module, span)?;
        // Same invariant as `lower_struct_expr`: `collect_local_pattern_requirements`'s
        // `Pattern::Struct` arm already recorded this pattern's field
        // obligations and waited on `StructDefined(module_id)` before this
        // `Lowerer` was built, so the ordered schema is present by
        // construction, and an unknown field is diagnosed durably through
        // that obligation store rather than a local check here.
        let order = self
            .world
            .struct_def_fields(module_id)
            .map(|fields| fields.to_vec())
            .unwrap_or_else(|| fields.iter().map(|(name, _)| name.clone()).collect());
        let mut by_name = fields
            .iter()
            .map(|(name, pattern)| (name.as_str(), pattern))
            .collect::<HashMap<_, _>>();
        steps.push(ExprStep::AssertStruct {
            source,
            module: module_id,
        });
        for field in &order {
            let Some(pattern) = by_name.remove(field.as_str()) else {
                continue;
            };
            let value = self.fresh_value();
            steps.push(ExprStep::FieldAccess {
                value,
                base: source,
                field: field.clone(),
            });
            if with_asserts {
                self.apply_pattern(&pattern.node, pattern.span, value, env, steps)?;
            } else {
                self.bind_pattern(&pattern.node, pattern.span, value, env, steps)?;
            }
        }
        Ok(())
    }

    fn lower_bitstring_pattern(
        &mut self,
        fields: &[BitField<Spanned<Pattern>>],
        span: Span,
        source: ValueId,
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
        with_asserts: bool,
    ) -> Result<(), FatalError> {
        let mut reader = self.fresh_value();
        steps.push(ExprStep::BitstringInit { reader, source });
        for (index, field) in fields.iter().enumerate() {
            let ok = self.fresh_value();
            let value = self.fresh_value();
            let next_reader = self.fresh_value();
            steps.push(ExprStep::BitstringRead {
                ok,
                value,
                next_reader,
                reader,
                spec: self.lower_bitfield_spec(
                    &field.spec.size,
                    field.spec.ty,
                    field.spec.endian,
                    field.spec.signed,
                    field.spec.unit,
                    field.value.span,
                    env,
                )?,
                is_last: index + 1 == fields.len(),
            });
            steps.push(ExprStep::AssertLiteral {
                source: ok,
                literal: GroundValue::Bool(true),
            });
            if with_asserts {
                self.apply_pattern(&field.value.node, field.value.span, value, env, steps)?;
            } else {
                self.bind_pattern(&field.value.node, field.value.span, value, env, steps)?;
            }
            reader = next_reader;
        }
        steps.push(ExprStep::AssertBitstringDone { reader });
        let _ = span;
        Ok(())
    }

    fn push_const(&mut self, steps: &mut Vec<ExprStep>, literal: GroundValue) -> ValueId {
        let value = self.fresh_value();
        steps.push(ExprStep::Const { value, literal });
        value
    }

    fn fresh_value(&mut self) -> ValueId {
        let value = ValueId::from_u32(self.next_value);
        self.next_value += 1;
        value
    }

    fn fresh_callsite(&mut self, span: Span) -> CallSiteId {
        let value = CallSiteId::new(self.next_callsite, span);
        self.next_callsite += 1;
        value
    }
}

fn lower_projection_step(step: &ExprStep) -> LoweredStep {
    match step {
        ExprStep::Const { value, literal } => LoweredStep::Const {
            value: *value,
            literal: literal.clone(),
        },
        ExprStep::Tuple { value, items } => LoweredStep::Tuple {
            value: *value,
            items: items.iter().copied().map(crate::fz_ir::OwnershipUse::share).collect(),
        },
        ExprStep::List { value, items, tail } => LoweredStep::List {
            value: *value,
            items: items.clone(),
            tail: *tail,
            retention: None,
        },
        ExprStep::Map {
            value,
            entries,
            quoted_span,
        } => LoweredStep::Map {
            value: *value,
            entries: entries.clone(),
            quoted_span: *quoted_span,
        },
        ExprStep::MapUpdate { value, base, entries } => LoweredStep::MapUpdate {
            value: *value,
            base: *base,
            entries: entries.clone(),
        },
        ExprStep::Struct { value, module, fields } => LoweredStep::Struct {
            value: *value,
            module: *module,
            fields: fields.clone(),
        },
        ExprStep::Bitstring { value, fields } => LoweredStep::Bitstring {
            value: *value,
            fields: fields.clone(),
        },
        ExprStep::FunctionRef { value, function } => LoweredStep::FunctionRef {
            value: *value,
            function: *function,
        },
        ExprStep::Lambda {
            value,
            function,
            captures,
        } => LoweredStep::Lambda {
            value: *value,
            function: *function,
            captures: captures.clone(),
        },
        ExprStep::BinaryOp { value, op, left, right } => LoweredStep::BinaryOp {
            value: *value,
            op: *op,
            left: *left,
            right: *right,
        },
        ExprStep::UnaryOp { value, op, input } => LoweredStep::UnaryOp {
            value: *value,
            op: *op,
            input: *input,
        },
        ExprStep::MapIndex { value, base, key } => LoweredStep::MapIndex {
            value: *value,
            base: *base,
            key: key.clone(),
        },
        ExprStep::FieldAccess { value, base, field } => LoweredStep::FieldAccess {
            value: *value,
            base: *base,
            field: field.clone(),
        },
        ExprStep::AssertLiteral { source, literal } => LoweredStep::AssertLiteral {
            source: *source,
            literal: literal.clone(),
        },
        ExprStep::AssertStruct { source, module } => LoweredStep::AssertStruct {
            source: *source,
            module: *module,
        },
        ExprStep::RequireMapValue { value, source, key } => LoweredStep::RequireMapValue {
            value: *value,
            source: *source,
            key: key.clone(),
        },
        ExprStep::AssertTuple { source, arity } => LoweredStep::AssertTuple {
            source: *source,
            arity: *arity,
        },
        ExprStep::TupleField { value, source, index } => LoweredStep::TupleField {
            value: *value,
            source: *source,
            index: *index,
        },
        ExprStep::AssertEmptyList { source } => LoweredStep::AssertEmptyList { source: *source },
        ExprStep::AssertSame { source, value } => LoweredStep::AssertSame {
            source: *source,
            value: *value,
        },
        ExprStep::SplitList { source, head, tail } => LoweredStep::SplitList {
            source: *source,
            head: *head,
            tail: *tail,
        },
        ExprStep::BitstringInit { reader, source } => LoweredStep::BitstringInit {
            reader: *reader,
            source: *source,
        },
        ExprStep::BitstringRead {
            ok,
            value,
            next_reader,
            reader,
            spec,
            is_last,
        } => LoweredStep::BitstringRead {
            ok: *ok,
            value: *value,
            next_reader: *next_reader,
            reader: *reader,
            spec: spec.clone(),
            is_last: *is_last,
        },
        ExprStep::AssertBitstringDone { reader } => LoweredStep::AssertBitstringDone { reader: *reader },
        ExprStep::DirectCall { .. }
        | ExprStep::ClosureCall { .. }
        | ExprStep::If { .. }
        | ExprStep::Dispatch { .. }
        | ExprStep::Receive(_)
        | ExprStep::Halt { .. } => {
            panic!("control steps should be lowered into tails before projection conversion")
        }
    }
}

fn values_defined_by_steps(steps: &[LoweredStep]) -> HashSet<ValueId> {
    steps.iter().flat_map(step_defined_values).collect()
}

fn step_defined_values(step: &LoweredStep) -> impl Iterator<Item = ValueId> {
    let values = match step {
        LoweredStep::Const { value, .. }
        | LoweredStep::Tuple { value, .. }
        | LoweredStep::List { value, .. }
        | LoweredStep::Map { value, .. }
        | LoweredStep::MapUpdate { value, .. }
        | LoweredStep::Struct { value, .. }
        | LoweredStep::Bitstring { value, .. }
        | LoweredStep::FunctionRef { value, .. }
        | LoweredStep::Lambda { value, .. }
        | LoweredStep::BinaryOp { value, .. }
        | LoweredStep::UnaryOp { value, .. }
        | LoweredStep::MapIndex { value, .. }
        | LoweredStep::FieldAccess { value, .. }
        | LoweredStep::RequireMapValue { value, .. }
        | LoweredStep::TupleField { value, .. }
        | LoweredStep::BitstringInit { reader: value, .. } => [Some(*value), None, None],
        LoweredStep::SplitList { head, tail, .. } => [Some(*head), Some(*tail), None],
        LoweredStep::BitstringRead {
            ok, value, next_reader, ..
        } => [Some(*ok), Some(*value), Some(*next_reader)],
        LoweredStep::AssertLiteral { .. }
        | LoweredStep::AssertStruct { .. }
        | LoweredStep::AssertTuple { .. }
        | LoweredStep::AssertEmptyList { .. }
        | LoweredStep::AssertSame { .. }
        | LoweredStep::AssertBitstringDone { .. } => [None; 3],
    };
    values.into_iter().flatten()
}

fn value_definition(body: &LoweredBody, value: ValueId) -> Option<&LoweredStep> {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return None;
    };
    clauses
        .iter()
        .flat_map(|clause| &clause.projections)
        .chain(entries.iter().flat_map(|entry| &entry.steps))
        .find(|step| step_defined_values(step).any(|defined| defined == value))
}

fn compute_entry_captures(
    entries: &[LoweredEntry],
    clause_bounds: &HashMap<ControlEntryId, HashSet<ValueId>>,
    physical: bool,
) -> Vec<Vec<ValueId>> {
    let mut memo = HashMap::new();
    for entry_id in 0..entries.len() {
        let entry_id = ControlEntryId::from_u32(entry_id as u32);
        let _ = entry_captures(entries, clause_bounds, entry_id, physical, &mut memo);
    }
    (0..entries.len())
        .map(|index| memo.remove(&ControlEntryId::from_u32(index as u32)).unwrap_or_default())
        .collect()
}

fn list_source_origin(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    head: ValueId,
) -> Option<super::super::executable_facts::TransportOrigin> {
    use super::super::executable_facts::TransportOrigin;
    use crate::dispatch_matrix::{ProjectionKind, SubjectSource};
    match origins.get(&head)? {
        TransportOrigin::Projection {
            source,
            kind: ProjectionKind::ListHead,
        } => Some(TransportOrigin::LocalValue(*source)),
        TransportOrigin::OutcomeSubject { owner, subject } => {
            let LoweredBody::Clauses { entries, .. } = body else {
                return None;
            };
            let SubjectSource::Projection(projection) =
                entries[owner.as_u32() as usize].tail.dispatch_plan().subject(*subject)
            else {
                return None;
            };
            matches!(projection.kind, ProjectionKind::ListHead).then_some(TransportOrigin::OutcomeSubject {
                owner: *owner,
                subject: projection.source,
            })
        }
        _ => None,
    }
}

type SourcePath = (SubjectOriginRoot, Vec<crate::dispatch_matrix::ProjectionKind>);

fn origin_source_path(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    origin: &super::super::executable_facts::TransportOrigin,
) -> Option<SourcePath> {
    use super::super::executable_facts::TransportOrigin;
    let (value, suffix) = match origin {
        TransportOrigin::LocalValue(value) => (*value, Vec::new()),
        TransportOrigin::Projection { source, kind } => (*source, vec![kind.clone()]),
        TransportOrigin::OutcomeSubject { owner, subject } => {
            let (source, path) = body.dispatch_subject_origin(*owner, *subject);
            let path = path.into_iter().cloned().collect();
            match source {
                SubjectOriginRoot::Value(value) => (value, path),
                SubjectOriginRoot::MailboxMessage(_) => return Some((source, path)),
            }
        }
        TransportOrigin::Join(alternatives) => {
            let mut paths = alternatives
                .iter()
                .map(|origin| origin_source_path(body, origins, origin));
            let first = paths.next()??;
            return paths.all(|path| path.as_ref() == Some(&first)).then_some(first);
        }
        _ => return None,
    };
    let (mut root, mut path) = match origins.get(&value) {
        Some(
            TransportOrigin::ExecutableInput(_)
            | TransportOrigin::CallsiteReturn(_)
            | TransportOrigin::ClosureCallReturn { .. }
            | TransportOrigin::TupleValue(_)
            | TransportOrigin::CallableValue(_),
        )
        | None => (SubjectOriginRoot::Value(value), Vec::new()),
        Some(origin) => origin_source_path(body, origins, origin)?,
    };
    path.extend(suffix);
    while let SubjectOriginRoot::Value(value) = root
        && let Some((item, consumed)) = construction_projection(body, origins, value, &path)
    {
        let (next_root, mut prefix) = origin_source_path(body, origins, &TransportOrigin::LocalValue(item))?;
        prefix.extend(path.into_iter().skip(consumed));
        root = next_root;
        path = prefix;
    }
    Some((root, path))
}

fn construction_projection(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    root: ValueId,
    path: &[crate::dispatch_matrix::ProjectionKind],
) -> Option<(ValueId, usize)> {
    use crate::dispatch_matrix::ProjectionKind;
    if let Some(ProjectionKind::TupleField(index)) = path.first()
        && let Some(super::super::executable_facts::TransportOrigin::TupleValue(items)) = origins.get(&root)
    {
        return items.get(*index as usize).map(|item| (*item, 1));
    }
    let LoweredStep::List { items, tail, .. } = value_definition(body, root)? else {
        return None;
    };
    let tails = path
        .iter()
        .take_while(|kind| matches!(kind, ProjectionKind::ListTail))
        .count();
    if tails >= items.len() && !items.is_empty() {
        return tail.map(|tail| (tail, items.len()));
    }
    if matches!(path.get(tails), Some(ProjectionKind::ListHead)) {
        return items.get(tails).map(|item| (*item, tails + 1));
    }
    None
}

fn list_can_rewrite(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    entry: usize,
    step: usize,
) -> bool {
    use super::super::executable_facts::TransportOrigin;
    let LoweredBody::Clauses { entries, .. } = body else {
        return false;
    };
    let LoweredStep::List {
        value,
        items,
        tail,
        retention: Some(retention),
    } = &entries[entry].steps[step]
    else {
        return false;
    };
    let Some(source) = origin_source_path(body, origins, &TransportOrigin::LocalValue(retention.source)) else {
        return false;
    };
    !items
        .iter()
        .chain(tail)
        .any(|operand| value_may_retain_source(body, origins, *operand, &source, Some(*value), &mut HashSet::new()))
        && !source_used_after(body, origins, entry, step, &source)
}

fn source_used_after(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    entry: usize,
    step: usize,
    source: &SourcePath,
) -> bool {
    let LoweredBody::Clauses { entries, .. } = body else {
        return true;
    };
    let exempt = match entries[entry].steps.get(step) {
        Some(LoweredStep::List { value, .. } | LoweredStep::Tuple { value, .. }) => Some(*value),
        _ => None,
    };
    any_later_ownership_use(body, entry, step, |value, role| match role {
        super::super::body::ValueRole::Semantic => {
            value_may_retain_source(body, origins, value, source, exempt, &mut HashSet::new())
        }
        super::super::body::ValueRole::Physical => origin_source_path(
            body,
            origins,
            &super::super::executable_facts::TransportOrigin::LocalValue(value),
        )
        .as_ref()
        .is_none_or(|identity| identity == source),
    })
}

fn any_later_ownership_use(
    body: &LoweredBody,
    entry: usize,
    step: usize,
    mut competes: impl FnMut(ValueId, super::super::body::ValueRole) -> bool,
) -> bool {
    use super::super::body::ValueRole;
    let LoweredBody::Clauses { entries, .. } = body else {
        return true;
    };
    let mut pending = vec![(entry, step + 1)];
    let mut visited = HashSet::new();
    while let Some((block_id, start)) = pending.pop() {
        if !visited.insert(block_id) {
            continue;
        }
        let block = &entries[block_id];
        let mut used = HashSet::new();
        collect_used_values(&block.steps[start..], &mut used);
        for instruction in block.steps.iter().skip(start) {
            if let LoweredStep::List {
                retention: Some(retention),
                ..
            } = instruction
                && competes(retention.source, ValueRole::Physical)
            {
                return true;
            }
        }
        collect_tail_used_values(&block.tail, &mut used);
        if used.into_iter().any(|value| competes(value, ValueRole::Semantic)) {
            return true;
        }
        pending.extend(
            child_entries(block.tail.clone())
                .into_iter()
                .map(|child| (child.as_u32() as usize, 0)),
        );
    }
    false
}

fn value_is_new_owner_projection(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    value: ValueId,
    owner: ValueId,
) -> bool {
    value == owner
        || origins
            .get(&value)
            .is_some_and(|origin| origin_is_new_owner_projection(body, origins, origin, owner))
}

fn origin_is_new_owner_projection(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    origin: &super::super::executable_facts::TransportOrigin,
    owner: ValueId,
) -> bool {
    use super::super::executable_facts::TransportOrigin;
    match origin {
        TransportOrigin::LocalValue(value) | TransportOrigin::Projection { source: value, .. } => {
            value_is_new_owner_projection(body, origins, *value, owner)
        }
        TransportOrigin::OutcomeSubject {
            owner: dispatch,
            subject,
        } => match body.dispatch_subject_origin(*dispatch, *subject).0 {
            SubjectOriginRoot::Value(value) => value_is_new_owner_projection(body, origins, value, owner),
            SubjectOriginRoot::MailboxMessage(_) => false,
        },
        TransportOrigin::Join(alternatives) => {
            !alternatives.is_empty()
                && alternatives
                    .iter()
                    .all(|origin| origin_is_new_owner_projection(body, origins, origin, owner))
        }
        _ => false,
    }
}

fn value_may_retain_source(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    value: ValueId,
    source: &SourcePath,
    exempt: Option<ValueId>,
    visiting: &mut HashSet<ValueId>,
) -> bool {
    use super::super::executable_facts::TransportOrigin;
    if exempt.is_some_and(|owner| value_is_new_owner_projection(body, origins, value, owner)) {
        return false;
    }
    if SubjectOriginRoot::Value(value) == source.0 || !visiting.insert(value) {
        return true;
    }
    if let Some((root, path)) = origin_source_path(body, origins, &TransportOrigin::LocalValue(value))
        && root == source.0
    {
        visiting.remove(&value);
        return source.1.starts_with(&path);
    }
    let retained = if let Some(origin) = origins.get(&value) {
        origin_may_retain_source(body, origins, origin, source, exempt, visiting)
    } else {
        match value_definition(body, value) {
            Some(
                LoweredStep::Const { .. }
                | LoweredStep::FunctionRef { .. }
                | LoweredStep::UnaryOp { .. }
                | LoweredStep::Bitstring { .. },
            ) => false,
            Some(LoweredStep::BinaryOp { op, .. }) if !matches!(op, crate::ast::BinOp::And | crate::ast::BinOp::Or) => {
                false
            }
            Some(step) => {
                let mut operands = HashSet::new();
                collect_used_values(std::slice::from_ref(step), &mut operands);
                if let LoweredStep::List {
                    retention: Some(retention),
                    ..
                } = step
                {
                    let identity = origin_source_path(body, origins, &TransportOrigin::LocalValue(retention.source));
                    if identity.as_ref().is_none_or(|identity| identity == source) {
                        visiting.remove(&value);
                        return true;
                    }
                }
                operands
                    .into_iter()
                    .any(|value| value_may_retain_source(body, origins, value, source, exempt, visiting))
            }
            None => true,
        }
    };
    visiting.remove(&value);
    retained
}

fn origin_may_retain_source(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    origin: &super::super::executable_facts::TransportOrigin,
    source: &SourcePath,
    exempt: Option<ValueId>,
    visiting: &mut HashSet<ValueId>,
) -> bool {
    use super::super::executable_facts::TransportOrigin;
    if let Some((root, path)) = origin_source_path(body, origins, origin) {
        if Some(root) == exempt.map(SubjectOriginRoot::Value) {
            return false;
        }
        if root == source.0 {
            return source.1.starts_with(&path);
        }
    }
    match origin {
        TransportOrigin::LocalValue(value) | TransportOrigin::Projection { source: value, .. } => {
            value_may_retain_source(body, origins, *value, source, exempt, visiting)
        }
        TransportOrigin::OutcomeSubject { owner, subject } => {
            let (value, _) = body.dispatch_subject_origin(*owner, *subject);
            match value {
                SubjectOriginRoot::Value(value) => {
                    value_may_retain_source(body, origins, value, source, exempt, visiting)
                }
                SubjectOriginRoot::MailboxMessage(_) => false,
            }
        }
        TransportOrigin::Join(alternatives) => alternatives
            .iter()
            .any(|origin| origin_may_retain_source(body, origins, origin, source, exempt, visiting)),
        TransportOrigin::TupleValue(items) => items
            .iter()
            .any(|value| value_may_retain_source(body, origins, *value, source, exempt, visiting)),
        TransportOrigin::CallableValue(producer) => producer
            .captures
            .iter()
            .any(|value| value_may_retain_source(body, origins, *value, source, exempt, visiting)),
        // Every producing call edge guards overlap with caller-retained values
        // before these independent roots enter a body. Unknown ingress without
        // a producing origin remains conservative in value_may_retain_source.
        TransportOrigin::ExecutableInput(_)
        | TransportOrigin::CallsiteReturn(_)
        | TransportOrigin::ClosureCallReturn { .. } => false,
    }
}

fn values_overlap(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    left: ValueId,
    right: ValueId,
) -> bool {
    values_overlap_inner(body, origins, left, right, None, &mut HashSet::new())
}

fn values_overlap_inner(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    left: ValueId,
    right: ValueId,
    exempt: Option<ValueId>,
    visited: &mut HashSet<(ValueId, ValueId)>,
) -> bool {
    use super::super::executable_facts::TransportOrigin;
    if !visited.insert((left, right)) {
        return false;
    }
    if exempt.is_some_and(|owner| {
        value_is_new_owner_projection(body, origins, left, owner)
            || value_is_new_owner_projection(body, origins, right, owner)
    }) {
        return false;
    }
    let Some(left_path) = origin_source_path(body, origins, &TransportOrigin::LocalValue(left)) else {
        return true;
    };
    let Some(right_path) = origin_source_path(body, origins, &TransportOrigin::LocalValue(right)) else {
        return true;
    };
    value_may_retain_source(body, origins, left, &right_path, exempt, &mut HashSet::new())
        || value_may_retain_source(body, origins, right, &left_path, exempt, &mut HashSet::new())
        || construction_children(body, origins, left)
            .into_iter()
            .any(|child| values_overlap_inner(body, origins, child, right, exempt, visited))
        || construction_children(body, origins, right)
            .into_iter()
            .any(|child| values_overlap_inner(body, origins, left, child, exempt, visited))
}

fn construction_children(
    body: &LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    value: ValueId,
) -> Vec<ValueId> {
    use super::super::executable_facts::TransportOrigin;
    use crate::dispatch_matrix::ProjectionKind;
    let Some((value, path)) = origin_source_path(body, origins, &TransportOrigin::LocalValue(value)) else {
        return Vec::new();
    };
    let SubjectOriginRoot::Value(value) = value else {
        return Vec::new();
    };
    if path.is_empty() {
        match origins.get(&value) {
            Some(TransportOrigin::TupleValue(items)) => return items.to_vec(),
            Some(TransportOrigin::CallableValue(producer)) => return producer.captures.to_vec(),
            _ => {}
        }
    }
    match value_definition(body, value) {
        Some(LoweredStep::List { items, tail, .. })
            if path.iter().all(|kind| matches!(kind, ProjectionKind::ListTail)) =>
        {
            items.iter().skip(path.len()).chain(tail).copied().collect()
        }
        Some(LoweredStep::Struct { fields, .. }) if path.is_empty() => fields.iter().map(|(_, value)| *value).collect(),
        Some(LoweredStep::Map { entries, .. }) if path.is_empty() => {
            entries.iter().flat_map(|(key, value)| [key.value, *value]).collect()
        }
        Some(LoweredStep::MapUpdate { base, entries, .. }) if path.is_empty() => std::iter::once(*base)
            .chain(entries.iter().flat_map(|(key, value)| [key.value, *value]))
            .collect(),
        _ => Vec::new(),
    }
}

fn construct_call_ownership(
    body: &mut LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
) {
    use super::super::executable_facts::TransportOrigin;
    use crate::fz_ir::OwnershipMode;
    let LoweredBody::Clauses { entries, .. } = body else {
        return;
    };
    let calls = entries
        .iter()
        .enumerate()
        .filter_map(|(index, entry)| {
            let (args, dest) = match &entry.tail {
                LoweredTail::DirectCall { args, dest, .. } | LoweredTail::ClosureCall { args, dest, .. } => {
                    (args, dest)
                }
                _ => return None,
            };
            Some((
                index,
                args.iter().map(|arg| arg.value).collect::<Vec<_>>(),
                dest.clone(),
            ))
        })
        .collect::<Vec<_>>();
    for (index, args, dest) in calls {
        let modes =
            args.iter()
                .enumerate()
                .map(|(arg_index, arg)| {
                    let peers_overlap = args.iter().enumerate().any(|(peer_index, peer)| {
                        arg_index != peer_index && values_overlap(body, origins, *arg, *peer)
                    });
                    let retained_overlap = if let ControlDestination::Deliver(target) = dest {
                        let LoweredBody::Clauses { entries, .. } = &*body else {
                            unreachable!()
                        };
                        let target = &entries[target.as_u32() as usize];
                        target
                            .captures
                            .iter()
                            .any(|capture| values_overlap(body, origins, *arg, *capture))
                            || target.physical_captures.iter().any(|capture| {
                                let Some(source) =
                                    origin_source_path(body, origins, &TransportOrigin::LocalValue(*capture))
                                else {
                                    return true;
                                };
                                value_may_retain_source(body, origins, *arg, &source, None, &mut HashSet::new())
                            })
                    } else {
                        false
                    };
                    if peers_overlap || retained_overlap {
                        OwnershipMode::Share
                    } else {
                        OwnershipMode::Transfer
                    }
                })
                .collect::<Vec<_>>();
        let LoweredBody::Clauses { entries, .. } = body else {
            unreachable!()
        };
        let args = match &mut entries[index].tail {
            LoweredTail::DirectCall { args, .. } | LoweredTail::ClosureCall { args, .. } => args,
            _ => unreachable!(),
        };
        for (arg, mode) in args.iter_mut().zip(modes) {
            arg.ownership = mode;
        }
    }
}

fn construct_tuple_ownership(
    body: &mut LoweredBody,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
) {
    use super::super::body::ValueRole;
    use super::super::executable_facts::TransportOrigin;
    use crate::fz_ir::OwnershipMode;
    let LoweredBody::Clauses { entries, .. } = body else {
        return;
    };
    let tuples = entries
        .iter()
        .enumerate()
        .flat_map(|(entry, block)| {
            block
                .steps
                .iter()
                .enumerate()
                .filter_map(move |(step, instruction)| match instruction {
                    LoweredStep::Tuple { value, items } => Some((
                        entry,
                        step,
                        *value,
                        items.iter().map(|item| item.value).collect::<Vec<_>>(),
                    )),
                    _ => None,
                })
        })
        .collect::<Vec<_>>();
    for (entry, step, result, items) in tuples {
        let modes = items
            .iter()
            .enumerate()
            .map(|(index, item)| {
                let peers_overlap = items
                    .iter()
                    .enumerate()
                    .any(|(peer_index, peer)| index != peer_index && values_overlap(body, origins, *item, *peer));
                let old_owner = any_later_ownership_use(body, entry, step, |value, role| match role {
                    ValueRole::Semantic => {
                        values_overlap_inner(body, origins, value, *item, Some(result), &mut HashSet::new())
                    }
                    ValueRole::Physical => origin_source_path(body, origins, &TransportOrigin::LocalValue(value))
                        .is_none_or(|source| {
                            value_may_retain_source(body, origins, *item, &source, Some(result), &mut HashSet::new())
                        }),
                });
                if peers_overlap || old_owner {
                    OwnershipMode::Share
                } else {
                    OwnershipMode::Transfer
                }
            })
            .collect::<Vec<_>>();
        let LoweredBody::Clauses { entries, .. } = body else {
            unreachable!()
        };
        let LoweredStep::Tuple { items, .. } = &mut entries[entry].steps[step] else {
            unreachable!()
        };
        for (item, mode) in items.iter_mut().zip(modes) {
            item.mode = mode;
        }
    }
}

fn entry_captures(
    entries: &[LoweredEntry],
    clause_bounds: &HashMap<ControlEntryId, HashSet<ValueId>>,
    entry_id: ControlEntryId,
    physical: bool,
    memo: &mut HashMap<ControlEntryId, Vec<ValueId>>,
) -> Vec<ValueId> {
    if let Some(captures) = memo.get(&entry_id) {
        return captures.clone();
    }

    let entry = &entries[entry_id.as_u32() as usize];
    let mut bound = clause_bounds.get(&entry_id).cloned().unwrap_or_default();
    bound.extend(entry.params.iter().copied());
    if let Some(value) = entry.origin.input_value() {
        bound.insert(value);
    }
    bound.extend(values_defined_by_steps(&entry.steps));

    let mut needed = if physical {
        entry
            .steps
            .iter()
            .filter_map(|step| match step {
                LoweredStep::List {
                    retention: Some(retention),
                    ..
                } => Some(retention.source),
                _ => None,
            })
            .collect()
    } else {
        used_values_in_entry(entry)
    };
    for child in child_entries(entry.tail.clone()) {
        for capture in entry_captures(entries, clause_bounds, child, physical, memo) {
            if !bound.contains(&capture) {
                needed.insert(capture);
            }
        }
    }
    needed.retain(|value| !bound.contains(value));
    let mut ordered = needed.into_iter().collect::<Vec<_>>();
    ordered.sort_by_key(|value| value.as_u32());
    for capture in &entry.captures {
        if !ordered.contains(capture) {
            ordered.push(*capture);
        }
    }
    ordered.sort_by_key(|value| value.as_u32());
    memo.insert(entry_id, ordered.clone());
    ordered
}

fn used_values_in_entry(entry: &LoweredEntry) -> HashSet<ValueId> {
    let mut out = HashSet::new();
    collect_used_values(&entry.steps, &mut out);
    collect_tail_used_values(&entry.tail, &mut out);
    out
}

fn collect_tail_used_values(tail: &LoweredTail, out: &mut HashSet<ValueId>) {
    match tail {
        LoweredTail::Value { value, .. } => {
            out.insert(*value);
        }
        LoweredTail::DirectCall { args, .. } => {
            for arg in args {
                out.insert(arg.value);
            }
        }
        LoweredTail::ClosureCall { callee, args, .. } => {
            out.insert(*callee);
            for arg in args {
                out.insert(arg.value);
            }
        }
        LoweredTail::If { cond, .. } => {
            out.insert(*cond);
        }
        LoweredTail::Dispatch { inputs, bindings, .. } => {
            out.extend(inputs.iter().copied());
            out.extend(bindings.pinned.iter().copied());
            out.extend(bindings.prepared.iter().copied());
        }
        LoweredTail::Receive(receive) => {
            let bindings = &receive.bindings;
            let after = &receive.after;
            out.extend(bindings.pinned.iter().copied());
            out.extend(bindings.prepared.iter().copied());
            if let Some(after) = after {
                out.insert(after.timeout);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
}

/// Every value identity retained by a lowered body's executable surface.
/// Running this after artifact pruning gives downstream products the exact
/// value-type subset that can still be interpreted or lowered.
pub(super) fn retained_value_ids(body: &LoweredBody) -> HashSet<ValueId> {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return HashSet::new();
    };
    let mut retained = HashSet::new();
    for clause in clauses {
        retained.extend(clause.params.iter().copied());
        retained.extend(values_defined_by_steps(&clause.projections));
        collect_used_values(&clause.projections, &mut retained);
    }
    for entry in entries {
        retained.extend(entry.params.iter().copied());
        retained.extend(entry.captures.iter().copied());
        retained.extend(entry.physical_captures.iter().copied());
        retained.extend(entry.steps.iter().filter_map(|step| match step {
            LoweredStep::List {
                retention: Some(retention),
                ..
            } => Some(retention.source),
            _ => None,
        }));
        if let Some(value) = entry.origin.input_value() {
            retained.insert(value);
        }
        retained.extend(values_defined_by_steps(&entry.steps));
        retained.extend(used_values_in_entry(entry));
    }
    retained
}

fn collect_used_values(steps: &[LoweredStep], out: &mut HashSet<ValueId>) {
    for step in steps {
        match step {
            LoweredStep::Const { .. } | LoweredStep::FunctionRef { .. } => {}
            LoweredStep::Tuple { items, .. } => out.extend(items.iter().map(|item| item.value)),
            LoweredStep::List { items, tail, .. } => {
                out.extend(items.iter().copied());
                if let Some(tail) = tail {
                    out.insert(*tail);
                }
            }
            LoweredStep::Map { entries, .. } => {
                for (key, value) in entries {
                    out.insert(key.value);
                    out.insert(*value);
                }
            }
            LoweredStep::MapUpdate { base, entries, .. } => {
                out.insert(*base);
                for (key, value) in entries {
                    out.insert(key.value);
                    out.insert(*value);
                }
            }
            LoweredStep::Struct { fields, .. } => out.extend(fields.iter().map(|(_, value)| *value)),
            LoweredStep::Bitstring { fields, .. } => {
                for field in fields {
                    out.insert(field.value);
                    if let Some(LoweredBitSize::Value(size)) = field.spec.size {
                        out.insert(size);
                    }
                }
            }
            LoweredStep::Lambda { captures, .. } => out.extend(captures.iter().copied()),
            LoweredStep::BinaryOp { left, right, .. } => {
                out.insert(*left);
                out.insert(*right);
            }
            LoweredStep::UnaryOp { input, .. } => {
                out.insert(*input);
            }
            LoweredStep::MapIndex { base, key, .. } => {
                out.insert(*base);
                out.insert(key.value);
            }
            LoweredStep::FieldAccess { base, .. } | LoweredStep::AssertStruct { source: base, .. } => {
                out.insert(*base);
            }
            LoweredStep::RequireMapValue { source, .. } => {
                out.insert(*source);
            }
            LoweredStep::AssertLiteral { source, .. }
            | LoweredStep::AssertTuple { source, .. }
            | LoweredStep::AssertEmptyList { source } => {
                out.insert(*source);
            }
            LoweredStep::TupleField { source, .. } => {
                out.insert(*source);
            }
            LoweredStep::AssertSame { source, value } => {
                out.insert(*source);
                out.insert(*value);
            }
            LoweredStep::SplitList { source, .. } => {
                out.insert(*source);
            }
            LoweredStep::BitstringInit { source, .. } | LoweredStep::AssertBitstringDone { reader: source } => {
                out.insert(*source);
            }
            LoweredStep::BitstringRead { reader, spec, .. } => {
                out.insert(*reader);
                if let Some(LoweredBitSize::Value(size)) = spec.size {
                    out.insert(size);
                }
            }
        }
    }
}

fn child_entries(tail: LoweredTail) -> Vec<ControlEntryId> {
    match tail {
        LoweredTail::Value { dest, .. }
        | LoweredTail::DirectCall { dest, .. }
        | LoweredTail::ClosureCall { dest, .. } => match dest {
            ControlDestination::Return => Vec::new(),
            ControlDestination::Deliver(entry) => vec![entry],
        },
        LoweredTail::If {
            then_entry, else_entry, ..
        } => vec![then_entry, else_entry],
        LoweredTail::Dispatch { dispatch, .. } => {
            let mut children = dispatch.outcomes.iter().map(|edge| edge.target).collect::<Vec<_>>();
            children.push(dispatch.miss_entry);
            children
        }
        LoweredTail::Receive(receive) => {
            let mut children = receive.outcomes.iter().map(|edge| edge.target).collect::<Vec<_>>();
            if let Some(after) = &receive.after {
                children.push(after.entry);
            }
            children
        }
        LoweredTail::Halt { .. } => Vec::new(),
    }
}

fn lambda_free_names(clauses: &[LambdaClause]) -> HashSet<String> {
    let mut free = HashSet::new();
    for clause in clauses {
        let mut bound = HashSet::new();
        for param in &clause.params {
            bind_pattern_names(&param.node, &mut bound);
        }
        if let Some(guard) = &clause.guard {
            collect_expr_free_names(&guard.node, &mut bound, &mut free);
        }
        collect_expr_free_names(&clause.body.node, &mut bound, &mut free);
    }
    free
}

fn bind_pattern_names(pattern: &Pattern, bound: &mut HashSet<String>) {
    match pattern {
        Pattern::Var(name) | Pattern::Pinned(name) => {
            bound.insert(name.clone());
        }
        Pattern::Tuple(items) => {
            for item in items {
                bind_pattern_names(&item.node, bound);
            }
        }
        Pattern::List(items, tail) => {
            for item in items {
                bind_pattern_names(&item.node, bound);
            }
            if let Some(tail) = tail {
                bind_pattern_names(&tail.node, bound);
            }
        }
        Pattern::As(name, inner) => {
            bound.insert(name.clone());
            bind_pattern_names(&inner.node, bound);
        }
        Pattern::Map(entries) => {
            for (key, value) in entries {
                bind_pattern_names(&key.node, bound);
                bind_pattern_names(&value.node, bound);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, value) in fields {
                bind_pattern_names(&value.node, bound);
            }
        }
        Pattern::Bitstring(fields) => {
            for field in fields {
                bind_pattern_names(&field.value.node, bound);
            }
        }
        Pattern::Wildcard
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil => {}
    }
}

fn collect_expr_free_names(expr: &Expr, bound: &mut HashSet<String>, free: &mut HashSet<String>) {
    match expr {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Module(_)
        | Expr::FnRef { .. }
        | Expr::CaptureArg(_) => {}
        Expr::Capture(body) => collect_expr_free_names(&body.node, bound, free),
        Expr::Var(name) => {
            if !bound.contains(name) {
                free.insert(name.clone());
            }
        }
        Expr::List(items, tail) => {
            for item in items {
                collect_expr_free_names(&item.node, bound, free);
            }
            if let Some(tail) = tail {
                collect_expr_free_names(&tail.node, bound, free);
            }
        }
        Expr::Tuple(items) => {
            for item in items {
                collect_expr_free_names(&item.node, bound, free);
            }
        }
        Expr::Bitstring(fields) => {
            for field in fields {
                collect_expr_free_names(&field.value.node, bound, free);
            }
        }
        Expr::Map(entries) => {
            for (key, value) in entries {
                collect_expr_free_names(&key.node, bound, free);
                collect_expr_free_names(&value.node, bound, free);
            }
        }
        Expr::MapUpdate(base, entries) => {
            collect_expr_free_names(&base.node, bound, free);
            for (key, value) in entries {
                collect_expr_free_names(&key.node, bound, free);
                collect_expr_free_names(&value.node, bound, free);
            }
        }
        Expr::Struct { fields, .. } => {
            for (_, value) in fields {
                collect_expr_free_names(&value.node, bound, free);
            }
        }
        Expr::Index(base, key) => {
            collect_expr_free_names(&base.node, bound, free);
            collect_expr_free_names(&key.node, bound, free);
        }
        Expr::Call(callee, args) | Expr::ClosureCall(callee, args) => {
            collect_expr_free_names(&callee.node, bound, free);
            for arg in args {
                collect_expr_free_names(&arg.node, bound, free);
            }
        }
        Expr::BinOp(_, left, right) => {
            collect_expr_free_names(&left.node, bound, free);
            collect_expr_free_names(&right.node, bound, free);
        }
        Expr::UnOp(_, expr) | Expr::Ascribe(expr, _) | Expr::Quote(expr) | Expr::Unquote(expr) => {
            collect_expr_free_names(&expr.node, bound, free)
        }
        Expr::If(cond, then_expr, else_expr) => {
            collect_expr_free_names(&cond.node, bound, free);
            let mut then_bound = bound.clone();
            collect_expr_free_names(&then_expr.node, &mut then_bound, free);
            if let Some(else_expr) = else_expr {
                let mut else_bound = bound.clone();
                collect_expr_free_names(&else_expr.node, &mut else_bound, free);
            }
        }
        Expr::Case(subject, clauses) => {
            if let Some(subject) = subject {
                collect_expr_free_names(&subject.node, bound, free);
            }
            collect_match_clause_free_names(clauses, bound, free);
        }
        Expr::Cond(arms) => {
            for (test, body) in arms {
                let mut test_bound = bound.clone();
                collect_expr_free_names(&test.node, &mut test_bound, free);
                let mut body_bound = bound.clone();
                collect_expr_free_names(&body.node, &mut body_bound, free);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            let saved = bound.clone();
            for binding in bindings {
                match binding {
                    WithBinding::Bare(expr) => collect_expr_free_names(&expr.node, bound, free),
                    WithBinding::Match(pattern, expr) => {
                        collect_expr_free_names(&expr.node, bound, free);
                        collect_pattern_free_names(&pattern.node, bound, free);
                        bind_pattern_names(&pattern.node, bound);
                    }
                }
            }
            collect_expr_free_names(&body.node, bound, free);
            *bound = saved;
            collect_match_clause_free_names(else_clauses, bound, free);
        }
        Expr::Receive { clauses, after } => {
            collect_match_clause_free_names(clauses, bound, free);
            if let Some(after) = after {
                collect_expr_free_names(&after.timeout.node, bound, free);
                collect_expr_free_names(&after.body.node, bound, free);
            }
        }
        Expr::Match(pattern, rhs) => {
            collect_expr_free_names(&rhs.node, bound, free);
            collect_pattern_free_names(&pattern.node, bound, free);
            bind_pattern_names(&pattern.node, bound);
        }
        Expr::Block(exprs) => {
            for expr in exprs {
                collect_expr_free_names(&expr.node, bound, free);
            }
        }
        Expr::Lambda { clauses, .. } => {
            for clause in clauses {
                let mut lambda_bound = bound.clone();
                for param in &clause.params {
                    bind_pattern_names(&param.node, &mut lambda_bound);
                }
                if let Some(guard) = &clause.guard {
                    collect_expr_free_names(&guard.node, &mut lambda_bound, free);
                }
                collect_expr_free_names(&clause.body.node, &mut lambda_bound, free);
            }
        }
    }
}

fn collect_pattern_free_names(pattern: &Pattern, bound: &mut HashSet<String>, free: &mut HashSet<String>) {
    match pattern {
        Pattern::Pinned(name) => {
            if !bound.contains(name) {
                free.insert(name.clone());
            }
        }
        Pattern::Tuple(items) => {
            for item in items {
                collect_pattern_free_names(&item.node, bound, free);
            }
        }
        Pattern::List(items, tail) => {
            for item in items {
                collect_pattern_free_names(&item.node, bound, free);
            }
            if let Some(tail) = tail {
                collect_pattern_free_names(&tail.node, bound, free);
            }
        }
        Pattern::As(_, inner) => collect_pattern_free_names(&inner.node, bound, free),
        Pattern::Map(entries) => {
            for (key, value) in entries {
                collect_pattern_free_names(&key.node, bound, free);
                collect_pattern_free_names(&value.node, bound, free);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, value) in fields {
                collect_pattern_free_names(&value.node, bound, free);
            }
        }
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_pattern_free_names(&field.value.node, bound, free);
            }
        }
        Pattern::Wildcard
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil => {}
    }
}

fn collect_match_clause_free_names(clauses: &[MatchClause], bound: &mut HashSet<String>, free: &mut HashSet<String>) {
    for clause in clauses {
        let mut clause_bound = bound.clone();
        collect_pattern_free_names(&clause.pattern.node, &mut clause_bound, free);
        bind_pattern_names(&clause.pattern.node, &mut clause_bound);
        if let Some(guard) = &clause.guard {
            collect_expr_free_names(&guard.node, &mut clause_bound, free);
        }
        collect_expr_free_names(&clause.body.node, &mut clause_bound, free);
    }
}

fn match_rows(clauses: &[MatchClause]) -> Vec<PatternRow<super::super::types::Ty>> {
    clauses
        .iter()
        .enumerate()
        .map(|(index, clause)| PatternRow {
            patterns: vec![clause.pattern.clone()],
            preconditions: Vec::new(),
            guard: clause.guard.clone(),
            body_id: index as PatternBodyId,
        })
        .collect()
}

fn emit_local_dispatch_error(
    tel: &impl crate::telemetry::Telemetry,
    label: &str,
    span: Span,
    error: PatternDispatchError,
) -> FatalError {
    match error {
        PatternDispatchError::SourcePattern(SourcePatternError::UnsupportedGuardExpr) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 {label} guards must be dispatch-pure"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(SourcePatternError::UnknownPinned(name))
        | PatternDispatchError::SourcePattern(SourcePatternError::UnknownGuardVar(name)) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNBOUND,
                format!("compiler2 {label} guard references unknown name `{name}`"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(SourcePatternError::UnsupportedMapKey) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 {label} patterns require literal map keys"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(SourcePatternError::DispatchMatrix(message)) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 {label} dispatch could not be planned: {message}"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(
            SourcePatternError::UnknownSubject(_)
            | SourcePatternError::UnresolvedStruct(_)
            | SourcePatternError::RowPatternArity { .. }
            | SourcePatternError::NonMonotonicBodyId { .. },
        ) => {
            panic!("compiler2 built an invalid local dispatch row set: {error:?}")
        }
        PatternDispatchError::SourcePattern(SourcePatternError::GuardCallCycle(name, arity)) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 {label} guard helper cycle detected through `{name}/{arity}`"),
                span,
            ),
        ),
        PatternDispatchError::MatrixBuild(error) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 {label} dispatch matrix is invalid: {error:?}"),
                span,
            ),
        ),
        PatternDispatchError::Compile(error) => emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 {label} dispatch could not be compiled: {error:?}"),
                span,
            ),
        ),
    }
}

fn expr_name(expr: &Expr) -> &'static str {
    match expr {
        Expr::Int(_) => "Int",
        Expr::Float(_) => "Float",
        Expr::Binary(_) => "Binary",
        Expr::Atom(_) => "Atom",
        Expr::Bool(_) => "Bool",
        Expr::Nil => "Nil",
        Expr::Var(_) => "Var",
        Expr::FnRef { .. } => "FnRef",
        Expr::Module(_) => "Module",
        Expr::Capture(_) => "Capture",
        Expr::CaptureArg(_) => "CaptureArg",
        Expr::List(_, _) => "List",
        Expr::Tuple(_) => "Tuple",
        Expr::Bitstring(_) => "Bitstring",
        Expr::Map(_) => "Map",
        Expr::MapUpdate(_, _) => "MapUpdate",
        Expr::Struct { .. } => "Struct",
        Expr::Index(_, _) => "Index",
        Expr::Call(_, _) => "Call",
        Expr::ClosureCall(_, _) => "ClosureCall",
        Expr::Ascribe(_, _) => "Ascribe",
        Expr::BinOp(_, _, _) => "BinOp",
        Expr::UnOp(_, _) => "UnOp",
        Expr::If(_, _, _) => "If",
        Expr::Case(_, _) => "Case",
        Expr::Cond(_) => "Cond",
        Expr::With(_, _, _) => "With",
        Expr::Receive { .. } => "Receive",
        Expr::Match(_, _) => "Match",
        Expr::Block(_) => "Block",
        Expr::Lambda { .. } => "Lambda",
        Expr::Quote(_) => "Quote",
        Expr::Unquote(_) => "Unquote",
    }
}

fn quoted_binop_atom(op: crate::ast::BinOp) -> &'static str {
    match op {
        crate::ast::BinOp::Add => "+",
        crate::ast::BinOp::Sub => "-",
        crate::ast::BinOp::Mul => "*",
        crate::ast::BinOp::Div => "/",
        crate::ast::BinOp::Rem => "%",
        crate::ast::BinOp::Eq => "==",
        crate::ast::BinOp::Neq => "!=",
        crate::ast::BinOp::Lt => "<",
        crate::ast::BinOp::LtEq => "<=",
        crate::ast::BinOp::Gt => ">",
        crate::ast::BinOp::GtEq => ">=",
        crate::ast::BinOp::And => "and",
        crate::ast::BinOp::Or => "or",
        crate::ast::BinOp::Pipe => "|>",
        crate::ast::BinOp::Cons => "|",
        crate::ast::BinOp::ListConcat => "++",
        crate::ast::BinOp::ListSubtract => "--",
        crate::ast::BinOp::BinConcat => "<>",
        crate::ast::BinOp::Range => "..",
        crate::ast::BinOp::RangeStep => "//",
        crate::ast::BinOp::In => "in",
        crate::ast::BinOp::NotIn => "not in",
    }
}

fn quoted_unop_atom(op: crate::ast::UnOp) -> &'static str {
    match op {
        crate::ast::UnOp::Neg => "-",
        crate::ast::UnOp::Not => "not",
    }
}

fn direct_call_name(expr: &Spanned<Expr>, env: &HashMap<String, ValueId>) -> Option<CallableName> {
    let mut current = &expr.node;
    loop {
        match current {
            Expr::Var(name) => {
                if env.contains_key(name) {
                    return None;
                }
                break;
            }
            Expr::Module(_) => break,
            Expr::Index(target, _) => {
                current = &target.node;
            }
            _ => return None,
        }
    }
    CallableName::from_expr(&expr.node)
}

fn direct_operator_name(op: crate::ast::BinOp) -> Option<&'static str> {
    match op {
        crate::ast::BinOp::Add => Some("+"),
        crate::ast::BinOp::Sub => Some("-"),
        crate::ast::BinOp::Mul => Some("*"),
        crate::ast::BinOp::Div => Some("/"),
        crate::ast::BinOp::Rem => Some("%"),
        crate::ast::BinOp::Eq => Some("=="),
        crate::ast::BinOp::Neq => Some("!="),
        crate::ast::BinOp::Lt => Some("<"),
        crate::ast::BinOp::LtEq => Some("<="),
        crate::ast::BinOp::Gt => Some(">"),
        crate::ast::BinOp::GtEq => Some(">="),
        crate::ast::BinOp::And
        | crate::ast::BinOp::Or
        | crate::ast::BinOp::Pipe
        | crate::ast::BinOp::Cons
        | crate::ast::BinOp::ListConcat
        | crate::ast::BinOp::ListSubtract
        | crate::ast::BinOp::BinConcat
        | crate::ast::BinOp::Range
        | crate::ast::BinOp::RangeStep
        | crate::ast::BinOp::In
        | crate::ast::BinOp::NotIn => None,
    }
}

fn quoted_alias_segments(name: &str) -> Option<Vec<&str>> {
    let segments = name.split('.').collect::<Vec<_>>();
    if segments.len() < 2 {
        return None;
    }
    if segments.iter().all(|segment| {
        let mut chars = segment.chars();
        matches!(chars.next(), Some(ch) if ch.is_uppercase()) && chars.all(|ch| ch.is_alphanumeric() || ch == '_')
    }) {
        Some(segments)
    } else {
        None
    }
}

fn literal_from_pattern(pattern: &Pattern) -> Option<GroundValue> {
    Some(match pattern {
        Pattern::Int(value) => GroundValue::Int(*value),
        Pattern::Float(value) => GroundValue::from_f64(*value),
        Pattern::Binary(value) => GroundValue::Binary(value.clone()),
        Pattern::Atom(value) => GroundValue::Atom(value.clone()),
        Pattern::Bool(value) => GroundValue::Bool(*value),
        Pattern::Nil => GroundValue::Nil,
        Pattern::Wildcard
        | Pattern::Var(_)
        | Pattern::Tuple(_)
        | Pattern::List(_, _)
        | Pattern::Map(_)
        | Pattern::Struct { .. }
        | Pattern::Pinned(_)
        | Pattern::As(_, _)
        | Pattern::Bitstring(_) => return None,
    })
}

fn pattern_name(pattern: &Pattern) -> &'static str {
    match pattern {
        Pattern::Wildcard => "Wildcard",
        Pattern::Var(_) => "Var",
        Pattern::Int(_) => "Int",
        Pattern::Float(_) => "Float",
        Pattern::Binary(_) => "Binary",
        Pattern::Atom(_) => "Atom",
        Pattern::Bool(_) => "Bool",
        Pattern::Nil => "Nil",
        Pattern::Tuple(_) => "Tuple",
        Pattern::List(_, _) => "List",
        Pattern::Map(_) => "Map",
        Pattern::Struct { .. } => "Struct",
        Pattern::Pinned(_) => "Pinned",
        Pattern::As(_, _) => "As",
        Pattern::Bitstring(_) => "Bitstring",
    }
}

fn emit_job_diagnostic(tel: &impl crate::telemetry::Telemetry, diagnostic: Diagnostic) -> FatalError {
    emit_through(tel, std::slice::from_ref(&diagnostic));
    FatalError
}

/// The compile-time constant of a literal expression, for positions where
/// the lowering records values alongside their known constants (map keys).
fn expr_literal(expr: &Expr) -> Option<GroundValue> {
    match expr {
        Expr::Int(value) => Some(GroundValue::Int(*value)),
        Expr::Float(value) => Some(GroundValue::from_f64(*value)),
        Expr::Binary(value) => Some(GroundValue::Binary(value.clone())),
        Expr::Atom(value) => Some(GroundValue::Atom(value.clone())),
        Expr::Bool(value) => Some(GroundValue::Bool(*value)),
        Expr::Nil => Some(GroundValue::Nil),
        _ => None,
    }
}
