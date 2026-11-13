//! Compiler2 body-lowering jobs and helpers.
//!
//! This module lowers one defined function at a time into Compiler2's
//! structured body form. It owns the local lowering algorithm, lambda capture
//! discovery, and generated-function definition path.

use crate::compiler2::{ValueMap, ValueSet};
use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ast::{
    AfterClause, BinOp, BitField, BitSize, CallableName, Callee, CatchClause, Expr, FnClause, LambdaClause,
    MatchClause, Pattern, RescueClause, Spanned, UnOp, Var, VarContext, WithBinding,
};
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{
    LastResort, PatternBodyId, PatternDispatchError, PatternRow, SourcePatternError, SourcePatternRows,
    pattern_dispatch_from_source, pattern_dispatch_from_source_with_resolver,
};
use fz_runtime::any_value::ValueKind;

use crate::function_surface::FunctionSurface;
use crate::ground_value::GroundValue;
use crate::modules::identity::{ModuleDenotation, ModuleName};
use crate::source::{SourceMap, Span};

use super::super::body::{
    BodyTables, CallArg, CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, ControlEntryOrigin,
    DispatchBindings, LoweredBitField, LoweredBitFieldSpec, LoweredBitSize, LoweredBody, LoweredClause, LoweredEntry,
    LoweredMapKey, LoweredStep, LoweredTail, ReceiveAfter, SubjectOriginRoot, ValueId, step_used_values,
};
use super::super::code::SourceOwner;
use super::super::drive::{FactKey, JobEffects, current_uses};
use super::super::identity::{FunctionId, FunctionSource, ModuleId};
use super::super::module_interface::{InterfaceCallableKind, InterfaceRequester};
use super::super::namespace::{CallableQualifier, Namespace, NamespaceSymbol};
use super::super::quoted_expander::emit_surface_read_error;
use super::super::scheduler::FatalError;
use super::super::source::{QuotedAstNode, QuotedSourceCursor, QuotedSourceError};
use super::super::world::World;
use super::dispatch::{
    collect_guard_calls_in_expr, hoist_zero_argument_guard_calls, resolve_guard_callee, resolve_guard_callee_checked,
};

mod storage_roots;
use storage_roots::{LaterUses, StorageRootIndex, entries_reached_from};

type Output = FactKey;
type Changed = FactKey;

#[derive(Debug)]
struct ExprClause {
    span: Span,
    params: Vec<ValueId>,
    projections: Vec<ExprStep>,
    body: ExprBlock,
}

#[derive(Debug)]
struct ExprBlock {
    span: Span,
    steps: Vec<ExprStep>,
    result: ValueId,
}

impl ExprBlock {
    fn view(&self) -> BlockView<'_> {
        BlockView {
            span: self.span,
            steps: &self.steps,
            result: self.result,
        }
    }
}

/// The steps of a block still to be planned. Resuming after a step is the
/// suffix of the same steps.
#[derive(Debug, Clone, Copy)]
struct BlockView<'a> {
    span: Span,
    steps: &'a [ExprStep],
    result: ValueId,
}

impl<'a> BlockView<'a> {
    fn after(self, index: usize) -> Self {
        Self {
            steps: &self.steps[index + 1..],
            ..self
        }
    }
}

#[derive(Debug)]
struct ExprDispatch {
    plan: Rc<crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>>,
    arm_blocks: Vec<ExprOutcome>,
    /// Where a subject no arm claims goes, or `None` when the plan raises
    /// its last resort instead.
    miss_block: Option<ExprBlock>,
}

#[derive(Debug)]
struct ExprOutcome {
    arguments: Box<[super::super::body::OutcomeArgument]>,
    block: ExprBlock,
}

#[derive(Debug)]
struct ExprReceiveAfter {
    span: Span,
    timeout: ValueId,
    body: ExprBlock,
}

#[derive(Debug)]
struct ExprReceive {
    value: ValueId,
    bindings: DispatchBindings,
    dispatch: Rc<crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>>,
    outcomes: Vec<ExprOutcome>,
    after: Option<ExprReceiveAfter>,
    captures: Vec<ValueId>,
}

/// A `try` body run under a handler. The handler block receives the raise's
/// kind, value and exception name as `params`; the body block pops the handler
/// it ran under before anything that must not be protected, such as `else`
/// clauses.
#[derive(Debug)]
struct ExprTry {
    value: ValueId,
    body: ExprBlock,
    handler: ExprBlock,
    params: Vec<ValueId>,
    captures: Vec<ValueId>,
}

/// The clause of a `try` whose body a handler row runs: a rescue clause, which
/// may wrap the raised value in an `ErlangError` first, or a catch clause.
#[derive(Debug, Clone, Copy)]
enum HandlerClause {
    Rescue { clause: usize, wraps: bool },
    Catch { clause: usize },
}

/// One dispatch row of a handler, and the clause whose body it runs.
#[derive(Debug, Clone)]
struct HandlerArm {
    row: PatternRow<super::super::types::Ty>,
    clause: HandlerClause,
}

impl HandlerArm {
    fn rescue(row: PatternRow<super::super::types::Ty>, clause: usize, wraps: bool) -> Self {
        Self {
            row,
            clause: HandlerClause::Rescue { clause, wraps },
        }
    }

    fn catch(row: PatternRow<super::super::types::Ty>, clause: usize) -> Self {
        Self {
            row,
            clause: HandlerClause::Catch { clause },
        }
    }
}

/// The clauses of one `try`, as the source wrote them.
struct TrySections<'a> {
    body: &'a Spanned<Expr>,
    rescue: &'a [RescueClause],
    catch: &'a [CatchClause],
    else_clauses: &'a [MatchClause],
    after: Option<&'a Spanned<Expr>>,
}

const ERROR_KIND: &str = "error";
const ERLANG_ERROR: &str = "Elixir.ErlangError";

#[derive(Debug)]
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
    /// `%{base | k: v, ...}`. `value` is the updated map when `ok`, which is
    /// false when `base` lacks one of the keys.
    MapUpdate {
        value: ValueId,
        ok: ValueId,
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
    Try(Box<ExprTry>),
    PopHandler,
    RequireMapValue {
        value: ValueId,
        source: ValueId,
        key: GroundValue,
    },
    TupleField {
        value: ValueId,
        source: ValueId,
        index: usize,
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
}

/// The facts `lower_function` cannot conclude without: the function's own
/// definition.
pub(super) fn lower_function_gates(world: &World, function: FunctionId) -> Vec<FactKey> {
    if world.function_defined_revision(function).is_none() {
        return vec![FactKey::FunctionDefined(function)];
    }
    Vec::new()
}

/// Lowers one demanded function into Compiler2's structured body form.
///
/// This job reads the frozen function definition and emits one reusable body
/// fact keyed by `FunctionId`. It lowers only that function, plus any lambda
/// definitions it syntactically owns, and leaves unrelated bodies cold.
///
/// An extern has no body of its own -- its wire ABI is resolved once, by its
/// own `FunctionContract` (`jobs/contract.rs`) -- so nothing ever demands
/// `LoweredBody` for one, and this job never runs for one either.
pub(super) fn lower_function(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
) -> Result<JobEffects, FatalError> {
    if let Some(gate) = lower_function_gates(world, function).into_iter().next() {
        return Ok(JobEffects::wait_on_current(gate));
    }
    let (source, surface) = world.function_definition(function);
    debug_assert!(
        surface.extern_abi.is_none(),
        "an extern has no LoweredBody; nothing should ever demand one for {function:?}"
    );

    let mut reads = vec![FactKey::FunctionDefined(function)];
    let mut waits = HashSet::new();
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

    let mut lowerer = Lowerer::new(world, tel, function, &source, &surface);
    let (body, mut outputs, mut changed) = lowerer.lower()?;
    emit_ownership_work(
        tel,
        function,
        lowerer.ownership_steps_scanned,
        lowerer.ownership_pairs_compared,
    );
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

/// What ownership construction did while lowering this function.
/// `steps_scanned` counts the steps it read in sequence; everything else it
/// asks -- where a value is defined, what a later step uses -- is a table
/// lookup, so the count stays proportional to the body instead of to the
/// constructions the body contains. `pairs_compared` counts the tuple items
/// it set against a later use to decide whether the two can overlap.
fn emit_ownership_work(
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
    steps_scanned: u64,
    pairs_compared: u64,
) {
    tel.dispatch(
        &["fz", "compiler2", "lowered_body", "ownership"],
        &crate::measurements! { steps_scanned: steps_scanned, pairs_compared: pairs_compared },
        &crate::metadata! { function_id: u64::from(function.as_u32()) },
    );
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
        Expr::Try {
            body,
            rescue,
            catch,
            else_clauses,
            after,
        } => {
            collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, body, reads, waits)?;
            for clause in catch {
                for pattern in [&clause.kind, &clause.value] {
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
                }
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
            for clause in rescue {
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
            if let Some(after) = after {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, after, reads, waits)?;
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
        Expr::Quote(_, splices) => {
            // The quote's own text is data, not code, until whatever it
            // expands into is spliced somewhere and decoded on its own; only
            // its already-decoded `unquote` splices run here, so only they
            // can need a fact.
            for expr in splices {
                collect_local_dispatch_requirements(world, tel, namespace, owner_module, owner, expr, reads, waits)?;
            }
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
        | Expr::Alias(_)
        | Expr::Module(_)
        | Expr::BoundFunction(_)
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
        Pattern::Both(left, right) => {
            collect_local_pattern_requirements(world, tel, namespace, owner_module, owner, left, reads, waits)?;
            collect_local_pattern_requirements(world, tel, namespace, owner_module, owner, right, reads, waits)?;
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

struct Lowerer<'w, 'tel, 'f, T: crate::telemetry::Telemetry> {
    world: &'w mut World,
    telemetry: &'tel T,
    owner: FunctionId,
    namespace: Namespace,
    source: &'f FunctionSource,
    surface: &'f FunctionSurface,
    next_value: u32,
    next_callsite: u32,
    generated: Vec<Output>,
    generated_changed: Vec<Changed>,
    generated_ids: Vec<FunctionId>,
    ownership_steps_scanned: u64,
    ownership_pairs_compared: u64,
}

struct QuoteLowerer<'a, 'w, 'tel, 'f, 'env, 'steps, 'q, T: crate::telemetry::Telemetry> {
    lowerer: &'a mut Lowerer<'w, 'tel, 'f, T>,
    env: &'env mut HashMap<Var, ValueId>,
    steps: &'steps mut Vec<ExprStep>,
    /// Every `unquote(e)` inside this quote, already decoded in the same
    /// walk order this lowering walk encounters them. `next_splice` tracks
    /// how many have been taken so far.
    splices: &'q [Spanned<Expr>],
    next_splice: usize,
}

impl<'a, 'w, 'tel, 'f, 'env, 'steps, 'q, T: crate::telemetry::Telemetry>
    QuoteLowerer<'a, 'w, 'tel, 'f, 'env, 'steps, 'q, T>
{
    fn new(
        lowerer: &'a mut Lowerer<'w, 'tel, 'f, T>,
        env: &'env mut HashMap<Var, ValueId>,
        steps: &'steps mut Vec<ExprStep>,
        splices: &'q [Spanned<Expr>],
    ) -> Self {
        Self {
            lowerer,
            env,
            steps,
            splices,
            next_splice: 0,
        }
    }

    /// Walks a quoted-source node and reconstructs the equivalent quoted
    /// value: literals and lists and 2-tuples recurse structurally, and every
    /// `{head, meta, args}` node either splices an `unquote`, binds a call to
    /// its callable, or builds a variable reference. One case per shape, not
    /// one per language construct, so anything Elixir can quote, fz can too.
    fn lower(&mut self, cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<ValueId, FatalError> {
        match self.ast_node(cursor, sources)? {
            Some(node) => self.lower_ast_node(&node, sources),
            None => self.lower_literal(cursor, sources),
        }
    }

    fn ast_node(&self, cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<Option<QuotedAstNode>, FatalError> {
        cursor.ast_node(sources).map_err(|error| self.surface_error(error))
    }

    fn surface_error(&self, error: QuotedSourceError) -> FatalError {
        emit_surface_read_error(self.lowerer.telemetry, "compiler2 quote lowering", &error)
    }

    fn lower_literal(&mut self, cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<ValueId, FatalError> {
        match cursor.root().tag() {
            ValueKind::INT => {
                let value = cursor.int_value().map_err(|error| self.surface_error(error))?;
                Ok(self.lowerer.push_const(self.steps, GroundValue::Int(value)))
            }
            ValueKind::FLOAT => {
                let value = cursor
                    .root()
                    .load_float()
                    .map_err(|error| self.surface_error(error.into()))?;
                Ok(self.lowerer.push_const(self.steps, GroundValue::from_f64(value)))
            }
            ValueKind::ATOM => {
                let atom = cursor.atom_name().map_err(|error| self.surface_error(error))?;
                let literal = match atom.as_str() {
                    "true" => GroundValue::Bool(true),
                    "false" => GroundValue::Bool(false),
                    "nil" => GroundValue::Nil,
                    _ => GroundValue::Atom(atom),
                };
                Ok(self.lowerer.push_const(self.steps, literal))
            }
            ValueKind::BITSTRING | ValueKind::PROCBIN => {
                let bytes = cursor.raw_bytes().map_err(|error| self.surface_error(error))?;
                Ok(self.lowerer.push_const(self.steps, GroundValue::Binary(bytes)))
            }
            ValueKind::LIST => {
                let items = cursor.list_items().map_err(|error| self.surface_error(error))?;
                let values = items
                    .iter()
                    .map(|item| self.lower(item, sources))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.push_list(values, None))
            }
            ValueKind::STRUCT => {
                let items = cursor.tuple_items().map_err(|error| self.surface_error(error))?;
                let values = items
                    .iter()
                    .map(|item| self.lower(item, sources))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.push_tuple(values))
            }
            other => Err(self.surface_error(QuotedSourceError::new(format!(
                "unsupported quoted source runtime kind {other:?}"
            )))),
        }
    }

    fn lower_ast_node(&mut self, node: &QuotedAstNode, sources: &SourceMap) -> Result<ValueId, FatalError> {
        let span = node.span.unwrap_or(Span::DUMMY);
        if node.tail.root().tag() != ValueKind::LIST {
            let name = node.head.atom_name().map_err(|error| self.surface_error(error))?;
            return self.lower_variable(&name, span);
        }

        let args = node.tail.list_items().map_err(|error| self.surface_error(error))?;

        if node.head.root().tag() == ValueKind::ATOM {
            let name = node.head.atom_name().map_err(|error| self.surface_error(error))?;
            if name == "unquote" && args.len() == 1 {
                return self.lower_unquote();
            }
            let values = args
                .iter()
                .map(|arg| self.lower(arg, sources))
                .collect::<Result<Vec<_>, _>>()?;
            let bound = self.resolve_quoted_callable(&name, values.len());
            return Ok(self.lower_call_node(&name, bound, values, span));
        }

        let head = self.lower(&node.head, sources)?;
        let values = args
            .iter()
            .map(|arg| self.lower(arg, sources))
            .collect::<Result<Vec<_>, _>>()?;
        let tail = self.push_list(values, None);
        Ok(self.push_ast_node(head, tail, span))
    }

    /// `unquote(e)` splices `e`'s runtime value in place: `e` was already
    /// decoded alongside the quote itself, so lowering just takes the next
    /// one in walk order and lowers it as an ordinary expression, in the
    /// surrounding scope, exactly as if it had been written there directly.
    fn lower_unquote(&mut self) -> Result<ValueId, FatalError> {
        let index = self.next_splice;
        self.next_splice += 1;
        let expr = self.splices[index].clone();
        self.lowerer.lower_expr(&expr, self.env, self.steps)
    }

    /// The callable this quoted call names here, where the quote is written.
    /// `None` leaves the call unclassified, to be resolved in whatever context
    /// the quoted syntax is inserted into.
    ///
    /// This asks the same question `decode_named_expr` asks when reading the
    /// call back, but from the opposite end: `decode_named_expr` dispatches
    /// on `name` structurally before ever consulting a retained callable, so
    /// a structural spelling such as `+` or `if` decodes as its form no
    /// matter what this resolves it to. Classifying every spelling here,
    /// including one that is also a real callable's name, is therefore safe.
    fn resolve_quoted_callable(&mut self, name: &str, arity: usize) -> Option<FunctionId> {
        match self
            .lowerer
            .world
            .lookup_callable_namespace(self.lowerer.namespace, name, arity)?
        {
            NamespaceSymbol::Function(function)
            | NamespaceSymbol::Macro(function)
            | NamespaceSymbol::Callable(function) => Some(function),
            NamespaceSymbol::Module(_) | NamespaceSymbol::Type(_) | NamespaceSymbol::Splice(_) => None,
        }
    }

    fn lower_variable(&mut self, name: &str, span: Span) -> Result<ValueId, FatalError> {
        let head = self.lowerer.push_const(self.steps, GroundValue::Atom(name.to_string()));
        // Every variable this quote's own body writes is, by construction,
        // written inside this macro's quote. Its tail carries the macro's
        // `FunctionId` as an unstamped marker; the walk in `stamp_hygiene`
        // (quoted_expander.rs) rewrites it to `Var{context: Macro(fid, ordinal)}`
        // once this expansion's ordinal is known, right after the macro runs.
        let owner = i64::from(self.lowerer.owner.as_u32());
        let tail = self.lowerer.push_const(self.steps, GroundValue::Int(owner));
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

    /// A call node whose head is display spelling and whose metadata retains
    /// the callable, when the call was classified here.
    fn lower_call_node(
        &mut self,
        spelling: &str,
        bound: Option<FunctionId>,
        args: Vec<ValueId>,
        span: Span,
    ) -> ValueId {
        let head = self
            .lowerer
            .push_const(self.steps, GroundValue::Atom(spelling.to_string()));
        let tail = self.push_list(args, None);
        let entries = self.bound_callable_entries(bound);
        let meta = self.push_meta(span, entries);
        self.push_tuple(vec![head, meta, tail])
    }

    fn bound_callable_entries(&mut self, bound: Option<FunctionId>) -> Vec<(LoweredMapKey, ValueId)> {
        let Some(function) = bound else {
            return Vec::new();
        };
        let literal = GroundValue::Atom(super::super::source::META_BOUND_CALLABLE_KEY.to_string());
        let key = self.lowerer.push_const(self.steps, literal.clone());
        let coordinate = self
            .lowerer
            .push_const(self.steps, GroundValue::Int(i64::from(function.as_u32())));
        vec![(
            LoweredMapKey {
                value: key,
                literal: Some(literal),
            },
            coordinate,
        )]
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

impl<'w, 'tel, 'f, T: crate::telemetry::Telemetry> Lowerer<'w, 'tel, 'f, T> {
    fn new(
        world: &'w mut World,
        telemetry: &'tel T,
        owner: FunctionId,
        source: &'f FunctionSource,
        surface: &'f FunctionSurface,
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
            ownership_steps_scanned: 0,
            ownership_pairs_compared: 0,
        }
    }

    fn lower(&mut self) -> Result<(LoweredBody, Vec<Output>, Vec<Changed>), FatalError> {
        let mut clause_defs = Vec::new();
        for clause in &self.surface.clauses {
            clause_defs.push(self.lower_clause(clause)?);
        }
        let body = self.plan_clauses(clause_defs);

        Ok((
            body,
            std::mem::take(&mut self.generated),
            std::mem::take(&mut self.generated_changed),
        ))
    }

    fn lower_clause(&mut self, clause: &FnClause) -> Result<ExprClause, FatalError> {
        let mut env = HashMap::new();
        let mut projections = Vec::new();
        let mut params = Vec::new();
        if self.surface.is_macro {
            let value = self.fresh_value();
            params.push(value);
            env.insert(Var::user("__CALLER__"), value);
        }
        for capture in &self.source.capture_params {
            let value = self.fresh_value();
            params.push(value);
            env.insert(capture.clone(), value);
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
        env: HashMap<Var, ValueId>,
    ) -> Result<ExprBlock, FatalError> {
        match &expr.node {
            Expr::Block(statements) if !statements.is_empty() => self.lower_statements(expr.span, statements, env),
            _ => self.lower_statements(expr.span, std::slice::from_ref(expr), env),
        }
    }

    /// Lowers a body's statements in order. A match among them is a decision
    /// whose one arm is the rest of the statements, so the names it binds are
    /// the arm's and its value waits at no join; the arm's result is the
    /// body's, or the matched value when the match comes last.
    fn lower_statements(
        &mut self,
        span: Span,
        statements: &[Spanned<Expr>],
        mut env: HashMap<Var, ValueId>,
    ) -> Result<ExprBlock, FatalError> {
        let mut steps = Vec::new();
        let mut result = None;
        for (index, statement) in statements.iter().enumerate() {
            let Expr::Match(pattern, rhs) = &statement.node else {
                result = Some(self.lower_expr(statement, &mut env, &mut steps)?);
                continue;
            };
            let value = self.lower_expr(rhs, &mut env, &mut steps)?;
            let rest = &statements[index + 1..];
            match self.lower_match(pattern, value, &mut env, &mut steps, MatchArm::Rest(span, rest))? {
                Some(decided) => {
                    return Ok(ExprBlock {
                        span,
                        steps,
                        result: decided,
                    });
                }
                None => result = Some(value),
            }
        }
        Ok(ExprBlock {
            span,
            steps,
            result: result.expect("a body has at least one statement"),
        })
    }

    fn lower_expr(
        &mut self,
        expr: &Spanned<Expr>,
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        match &expr.node {
            Expr::Int(value) => Ok(self.push_const(steps, GroundValue::Int(*value))),
            Expr::Float(value) => Ok(self.push_const(steps, GroundValue::from_f64(*value))),
            Expr::Binary(value) => Ok(self.push_const(steps, GroundValue::Binary(value.clone()))),
            Expr::Atom(value) => Ok(self.push_const(steps, GroundValue::Atom(value.clone()))),
            Expr::Bool(value) => Ok(self.push_const(steps, GroundValue::Bool(*value))),
            Expr::Nil => Ok(self.push_const(steps, GroundValue::Nil)),
            Expr::Alias(alias) => self.lower_alias(alias, expr.span, steps),
            Expr::Module(module) => Ok(QuoteLowerer::new(self, env, steps, &[]).lower_module(module, expr.span)),
            Expr::Var(name) => {
                if let Some(value) = env.get(name) {
                    return Ok(*value);
                }
                if let VarContext::Macro(function, _) = name.context {
                    let macro_name = self.world.function_ref(function).display_name();
                    return Err(emit_job_diagnostic(
                        self.telemetry,
                        Diagnostic::error(
                            codes::LOWER_UNBOUND,
                            format!(
                                "compiler2 lowering found unbound variable `{}` (context {macro_name})",
                                name.name
                            ),
                            expr.span,
                        ),
                    ));
                }
                if matches!(name.context, VarContext::Generated(_)) {
                    return Err(emit_job_diagnostic(
                        self.telemetry,
                        Diagnostic::error(
                            codes::LOWER_UNBOUND,
                            format!("compiler2 lowering found unbound generated variable `{}`", name.name),
                            expr.span,
                        ),
                    ));
                }
                match self.world.lookup_namespace(self.namespace, &name.name) {
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
                let keys = lowered.iter().map(|(key, _)| key.value).collect();
                let updated = self.fresh_value();
                let ok = self.fresh_value();
                steps.push(ExprStep::MapUpdate {
                    value: updated,
                    ok,
                    base,
                    entries: lowered,
                });
                self.lower_update_key_check(expr.span, updated, ok, base, keys, steps)
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
                if let Some(callee) = direct_callee(target, args.len(), env) {
                    let value = self.fresh_value();
                    steps.push(ExprStep::DirectCall {
                        value,
                        callsite,
                        callee: self.resolve_callee(&callee, args.len(), target.span, "direct runtime callee")?,
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
            Expr::BinOp(op @ (BinOp::And | BinOp::Or), left, right) => {
                self.lower_strict_boolean_binop(*op, expr.span, left, right, env, steps)
            }
            Expr::UnOp(UnOp::Not, input) => self.lower_strict_not(expr.span, input, env, steps),
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
                self.lower_match(pattern, value, env, steps, MatchArm::Value)?;
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
            Expr::Try {
                body,
                rescue,
                catch,
                else_clauses,
                after,
            } => self.lower_try(
                expr.span,
                TrySections {
                    body,
                    rescue,
                    catch,
                    else_clauses,
                    after: after.as_deref(),
                },
                env,
                steps,
            ),
            Expr::Lambda { occurrence, clauses } => self.lower_lambda(*occurrence, expr.span, clauses, env, steps),
            Expr::Quote(cursor, splices) => {
                let source_map = self.world.source_map();
                QuoteLowerer::new(self, env, steps, splices).lower(cursor, &source_map.borrow())
            }
            Expr::Unquote(_) => Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "compiler2 lowering found `unquote` outside `quote`".to_string(),
                    expr.span,
                ),
            )),
            Expr::BoundFunction(_) => Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "a retained callable is a call's callee, not a value".to_string(),
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

    /// The callable a quoted call retained, once this world confirms it can be
    /// called here. Nothing consults a name: the target was chosen where the
    /// call was quoted. What is checked is what the world knows about that
    /// exact function — that it exists, that the call supplies its arity, that
    /// it is a function rather than a macro, and, when nothing has declared it
    /// yet, that its module owes an export.
    fn retained_callee(&mut self, function: FunctionId, arity: usize, span: Span) -> Result<FunctionId, FatalError> {
        let Some(symbol) = self.world.retained_callable_symbol(function) else {
            return Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "quoted call retains a callable this compiler does not know".to_string(),
                    span,
                ),
            ));
        };
        let declared = self.world.function_ref(function).arity;
        let supplies_arity = if self.world.function_variadic(function) {
            arity >= declared
        } else {
            arity == declared
        };
        if !supplies_arity {
            return Err(self.retained_callee_error(function, span, format!("supplies {arity} arg(s)")));
        }
        match symbol {
            NamespaceSymbol::Function(function) => Ok(function),
            NamespaceSymbol::Macro(_) => {
                Err(self.retained_callee_error(function, span, "is a macro and expands, it is not called".to_string()))
            }
            // Nothing has declared this function and its module has published
            // no interface. The name path would have recorded an expectation
            // here, and so does this one: an owner that never exports it is a
            // diagnostic at the interface boundary, not a silent placeholder.
            NamespaceSymbol::Callable(function) => {
                self.expect_retained_export(function, span);
                Ok(function)
            }
            NamespaceSymbol::Module(_) | NamespaceSymbol::Type(_) | NamespaceSymbol::Splice(_) => {
                Err(self.retained_callee_error(function, span, "is not a callable".to_string()))
            }
        }
    }

    fn retained_callee_error(&self, function: FunctionId, span: Span, complaint: String) -> FatalError {
        let label = self.world.function_ref(function).label();
        emit_job_diagnostic(
            self.telemetry,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("quoted call retains `{label}`, which {complaint}"),
                span,
            ),
        )
    }

    /// Records that the retained callee's module owes this export, the same
    /// obligation `resolve_module_callee` records for a name.
    fn expect_retained_export(&mut self, function: FunctionId, span: Span) {
        let reference = self.world.function_ref(function);
        let module = reference.module;
        let name = reference.name().to_string();
        let arity = reference.arity;
        let requester = self.interface_requester(span);
        self.world.reference_module_interface_callable(
            module,
            name,
            arity,
            InterfaceCallableKind::PublicFunction,
            Some(requester),
        );
    }

    fn resolve_direct_callee(&mut self, name: &str, arity: usize, span: Span) -> Result<FunctionId, FatalError> {
        let function = self.resolve_runtime_function(name, arity, span, "direct runtime callee")?;
        Ok(function)
    }

    fn resolve_callee(
        &mut self,
        callee: &Callee,
        arity: usize,
        span: Span,
        context: &str,
    ) -> Result<FunctionId, FatalError> {
        match callee {
            Callee::Bound(function) => self.retained_callee(*function, arity, span),
            Callee::Name(name) => self.resolve_callable_name(name, arity, span, context),
        }
    }

    fn resolve_callable_name(
        &mut self,
        name: &CallableName,
        arity: usize,
        span: Span,
        context: &str,
    ) -> Result<FunctionId, FatalError> {
        match self.world.callable_name_qualifier(self.namespace, name) {
            CallableQualifier::Unqualified => self.resolve_runtime_function(&name.name, arity, span, context),
            CallableQualifier::Module(module) => self.resolve_module_callee(module, &name.name, arity, span),
            CallableQualifier::Unbound => Err(self.unbound_runtime_function(&name.to_string(), arity, span, context)),
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
        env: &mut HashMap<Var, ValueId>,
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
        env: &mut HashMap<Var, ValueId>,
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
        env: &mut HashMap<Var, ValueId>,
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
        env: &HashMap<Var, ValueId>,
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
        env: &HashMap<Var, ValueId>,
    ) -> Result<Option<LoweredBitSize>, FatalError> {
        Ok(match size {
            None => None,
            Some(BitSize::Literal(value)) => Some(LoweredBitSize::Literal(*value)),
            Some(BitSize::Var(name)) => Some(LoweredBitSize::Value(self.bit_size_value(name, span, env)?)),
            Some(BitSize::ByteSizeOf(name)) => Some(LoweredBitSize::ByteSizeOf(self.bit_size_value(name, span, env)?)),
        })
    }

    fn bit_size_value(&mut self, name: &Var, span: Span, env: &HashMap<Var, ValueId>) -> Result<ValueId, FatalError> {
        env.get(name).copied().ok_or_else(|| {
            emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNBOUND,
                    format!("compiler2 lowering found unbound bit size name `{name}`"),
                    span,
                ),
            )
        })
    }

    fn lower_alias(
        &mut self,
        alias: &ModuleName,
        span: Span,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let atom = self
            .world
            .module_alias_atom(self.source.owner_module, self.namespace, alias)
            .ok_or_else(|| {
                emit_job_diagnostic(
                    self.telemetry,
                    Diagnostic::error(
                        codes::LOWER_UNBOUND,
                        format!("compiler2 could not resolve module `{alias}`"),
                        span,
                    ),
                )
            })?;
        Ok(self.push_const(steps, GroundValue::Atom(atom)))
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
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        self.lower_case_raising(span, subject, clauses, LastResort::case_clause(), env, steps)
    }

    /// `left and right` and `left or right` are a `case` on `left`: the one
    /// boolean that does not decide hands over to `right`, which is evaluated
    /// only then, and a left that is no boolean at all raises
    /// `BadBooleanError`. A left whose type is a boolean cannot reach that
    /// raise, so the dispatch leaves it out.
    fn lower_strict_boolean_binop(
        &mut self,
        op: BinOp,
        span: Span,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let decides_on = matches!(op, BinOp::Or);
        let arms = [
            (decides_on, Spanned::new(Expr::Bool(decides_on), span)),
            (!decides_on, right.clone()),
        ];
        let operator = if decides_on { "or" } else { "and" };
        self.lower_boolean_case(span, left, arms, LastResort::bad_boolean(operator), env, steps)
    }

    /// `not input` is a `case` on `input` that swaps the two booleans and
    /// raises `ArgumentError` on anything else.
    fn lower_strict_not(
        &mut self,
        span: Span,
        input: &Spanned<Expr>,
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let arms = [
            (true, Spanned::new(Expr::Bool(false), span)),
            (false, Spanned::new(Expr::Bool(true), span)),
        ];
        self.lower_boolean_case(span, input, arms, LastResort::argument_error(), env, steps)
    }

    fn lower_boolean_case(
        &mut self,
        span: Span,
        subject: &Spanned<Expr>,
        arms: [(bool, Spanned<Expr>); 2],
        last_resort: LastResort,
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let clauses = arms.map(|(literal, body)| MatchClause {
            pattern: Spanned::new(Pattern::Bool(literal), span),
            guard: None,
            body,
            span,
        });
        self.lower_case_raising(span, subject, &clauses, last_resort, env, steps)
    }

    fn lower_case_raising(
        &mut self,
        span: Span,
        subject: &Spanned<Expr>,
        clauses: &[MatchClause],
        last_resort: LastResort,
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let subject_value = self.lower_expr(subject, env, steps)?;
        let plan = self.compile_match_dispatch("case", span, 1, match_rows(clauses), Some(last_resort))?;
        let bindings = self.lower_dispatch_bindings(&plan, env, steps)?;
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
                plan: Rc::new(plan),
                arm_blocks,
                miss_block: None,
            }),
        });
        Ok(value)
    }

    fn lower_cond(
        &mut self,
        span: Span,
        arms: &[(Spanned<Expr>, Spanned<Expr>)],
        env: &mut HashMap<Var, ValueId>,
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
        env: &mut HashMap<Var, ValueId>,
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
        mut env: HashMap<Var, ValueId>,
    ) -> Result<ExprBlock, FatalError> {
        let Some(((cond, body), rest)) = arms.split_first() else {
            return Err(emit_job_diagnostic(
                self.telemetry,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "expected -> clauses for :do in \"cond\"".to_string(),
                    span,
                ),
            ));
        };

        let mut steps = Vec::new();
        let cond_value = self.lower_expr(cond, &mut env, &mut steps)?;
        let arm_block = self.lower_expr_as_block(body, env.clone())?;
        let (last_resort, miss_block) = if rest.is_empty() {
            (Some(LastResort::cond_clause()), None)
        } else {
            (None, Some(self.lower_cond_block(span, rest, env)?))
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
                plan: Rc::new(self.compile_bool_true_dispatch(span, last_resort)?),
                arm_blocks: vec![ExprOutcome {
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

    /// `%{base | k: v}` answers the updated map when `base` has every key,
    /// and raises `KeyError` naming a missing one otherwise, as Elixir's
    /// `put_map_exact` does. The update itself reports the miss, so the check
    /// is one test of `ok`; only a miss pays for finding which key it was.
    fn lower_update_key_check(
        &mut self,
        span: Span,
        updated: ValueId,
        ok: ValueId,
        base: ValueId,
        keys: Vec<ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let key_list = self.fresh_value();
        let raised = self.fresh_value();
        let callee = self.resolve_callee(&update_key_error_callee(), 2, span, "map update key check")?;
        let miss_block = ExprBlock {
            span,
            steps: vec![
                ExprStep::List {
                    value: key_list,
                    items: keys,
                    tail: None,
                },
                ExprStep::DirectCall {
                    value: raised,
                    callsite: self.fresh_callsite(span),
                    callee,
                    args: [base, key_list]
                        .into_iter()
                        .map(|value| CallArg {
                            value,
                            ascription: None,
                            ownership: crate::fz_ir::OwnershipMode::Share,
                        })
                        .collect(),
                },
            ],
            result: raised,
        };
        let value = self.fresh_value();
        steps.push(ExprStep::Dispatch {
            value,
            inputs: vec![ok],
            bindings: DispatchBindings {
                pinned: Vec::new(),
                prepared: Vec::new(),
            },
            dispatch: Box::new(ExprDispatch {
                plan: Rc::new(self.compile_bool_true_dispatch(span, None)?),
                arm_blocks: vec![ExprOutcome {
                    arguments: Box::default(),
                    block: ExprBlock {
                        span,
                        steps: Vec::new(),
                        result: updated,
                    },
                }],
                miss_block: Some(miss_block),
            }),
        });
        Ok(value)
    }

    fn lower_with_block(
        &mut self,
        span: Span,
        bindings: &[WithBinding],
        body: &Spanned<Expr>,
        else_clauses: &[MatchClause],
        mut env: HashMap<Var, ValueId>,
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
                let plan = self.compile_single_pattern_dispatch("with", pattern, span, None)?;
                let mut success_env = env.clone();
                let arguments = self.bind_outcome_arguments(&plan.outcomes[0], &mut success_env);
                let success_block = self.lower_with_block(span, rest, body, else_clauses, success_env)?;
                let miss_block = Some(self.lower_with_fail_block(span, matched, else_clauses, env.clone())?);
                let bindings = self.lower_dispatch_bindings(&plan, &env, &mut steps)?;
                let value = self.fresh_value();
                steps.push(ExprStep::Dispatch {
                    value,
                    inputs: vec![matched],
                    bindings,
                    dispatch: Box::new(ExprDispatch {
                        plan: Rc::new(plan),
                        arm_blocks: vec![ExprOutcome {
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
        env: HashMap<Var, ValueId>,
    ) -> Result<ExprBlock, FatalError> {
        if else_clauses.is_empty() {
            return Ok(ExprBlock {
                span,
                steps: Vec::new(),
                result: failed,
            });
        }
        self.lower_clause_dispatch_block("with else", span, failed, else_clauses, LastResort::with_clause(), env)
    }

    /// A case over `subject` whose arms are `clauses`; `last_resort` is what
    /// is raised when none matches.
    fn lower_clause_dispatch_block(
        &mut self,
        label: &str,
        span: Span,
        subject: ValueId,
        clauses: &[MatchClause],
        last_resort: LastResort,
        env: HashMap<Var, ValueId>,
    ) -> Result<ExprBlock, FatalError> {
        let plan = self.compile_match_dispatch(label, span, 1, match_rows(clauses), Some(last_resort))?;
        let mut steps = Vec::new();
        let bindings = self.lower_dispatch_bindings(&plan, &env, &mut steps)?;
        let arm_blocks = clauses
            .iter()
            .enumerate()
            .map(|(index, clause)| self.lower_match_clause_block(&plan.outcomes[index], clause, env.clone()))
            .collect::<Result<Vec<_>, _>>()?;
        let value = self.fresh_value();
        steps.push(ExprStep::Dispatch {
            value,
            inputs: vec![subject],
            bindings,
            dispatch: Box::new(ExprDispatch {
                plan: Rc::new(plan),
                arm_blocks,
                miss_block: None,
            }),
        });
        Ok(ExprBlock {
            span,
            steps,
            result: value,
        })
    }

    fn lower_receive(
        &mut self,
        span: Span,
        clauses: &[MatchClause],
        after: Option<&AfterClause>,
        env: &mut HashMap<Var, ValueId>,
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
        let mut rows = match_rows(clauses);
        let mut hoisted = Vec::new();
        for row in &mut rows {
            row.guard = row
                .guard
                .as_ref()
                .map(|guard| hoist_zero_argument_guard_calls(guard, &mut hoisted));
        }
        for call in hoisted {
            let value = self.lower_expr(&call.call, env, steps)?;
            env.insert(call.name, value);
        }
        let plan = self.compile_match_dispatch("receive", span, 1, rows, None)?;
        let bindings = self.lower_dispatch_bindings(&plan, env, steps)?;
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
            dispatch: Rc::new(plan),
            outcomes,
            after,
            captures,
        })));
        Ok(value)
    }

    /// `try` in its general form, as the nesting Erlang's `try` compiles to:
    /// `after` is the outermost layer and `rescue` the next; `else` is a case
    /// over the body's value that runs once the rescue handler is popped.
    ///
    /// The `after` layer runs its expression twice over, once per way out: on
    /// the success path right after its handler is popped, and in the handler
    /// itself, which then re-raises what it was handed.
    fn lower_try(
        &mut self,
        span: Span,
        sections: TrySections<'_>,
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let TrySections {
            body,
            rescue,
            catch,
            else_clauses,
            after,
        } = sections;
        let Some(after) = after else {
            if rescue.is_empty() && catch.is_empty() {
                self.warn_try_else_only(span);
            }
            return self.lower_handled(span, body, (rescue, catch), else_clauses, env, steps);
        };
        let mut protected_steps = Vec::new();
        let result = self.lower_handled(span, body, (rescue, catch), else_clauses, env, &mut protected_steps)?;
        protected_steps.push(ExprStep::PopHandler);
        let protected = ExprBlock {
            span,
            steps: protected_steps,
            result,
        };

        let params = vec![self.fresh_value(), self.fresh_value(), self.fresh_value()];
        let mut handler_steps = Vec::new();
        self.lower_expr(after, &mut env.clone(), &mut handler_steps)?;
        let reraise = self.compile_match_dispatch("after", span, 2, Vec::new(), Some(LastResort::reraise()))?;
        let bindings = self.lower_dispatch_bindings(&reraise, env, &mut handler_steps)?;
        let reraised = self.fresh_value();
        handler_steps.push(ExprStep::Dispatch {
            value: reraised,
            inputs: vec![params[0], params[1]],
            bindings,
            dispatch: Box::new(ExprDispatch {
                plan: Rc::new(reraise),
                arm_blocks: Vec::new(),
                miss_block: None,
            }),
        });
        let handler = ExprBlock {
            span,
            steps: handler_steps,
            result: reraised,
        };

        let mut free = HashSet::new();
        collect_expr_free_names(&after.node, &mut HashSet::new(), &mut free);
        let captures = self.capture_values(free, env);
        let value = self.fresh_value();
        steps.push(ExprStep::Try(Box::new(ExprTry {
            value,
            body: protected,
            handler,
            params,
            captures,
        })));
        self.lower_expr(after, &mut env.clone(), steps)?;
        Ok(value)
    }

    /// Elixir's own warning for a `try` that has an `else` and nothing else
    /// to protect or run: a `case` says the same thing.
    fn warn_try_else_only(&mut self, span: Span) {
        let diagnostic = super::super::source_diagnostics::try_else_only_diagnostic(span);
        super::super::drive::ExecutionContext::new(self.world, self.telemetry).emit_warning_once(diagnostic);
    }

    /// `try do body rescue clauses catch clauses else clauses end`: the body
    /// runs under a handler whose block dispatches over the delivered (kind,
    /// value, exception name) whose last resort is the re-raise: a raise no
    /// clause matches continues, with its kind, to the next handler out. The
    /// `else` clauses match the body's
    /// value after the handler is popped, so neither the handler's clauses nor
    /// a miss reach them.
    fn lower_handled(
        &mut self,
        span: Span,
        body: &Spanned<Expr>,
        (rescue, catch): (&[RescueClause], &[CatchClause]),
        else_clauses: &[MatchClause],
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let mut body = self.lower_expr_as_block(body, env.clone())?;
        if rescue.is_empty() && catch.is_empty() {
            steps.extend(body.steps);
            return self.push_try_else(span, body.result, else_clauses, env, steps);
        }
        let params = vec![self.fresh_value(), self.fresh_value(), self.fresh_value()];
        let raised = params[1];
        body.steps.push(ExprStep::PopHandler);
        body.result = self.push_try_else(span, body.result, else_clauses, env, &mut body.steps)?;

        let arms = self.handler_arms(rescue, catch);
        let rows = arms.iter().map(|arm| arm.row.clone()).collect();
        let plan = self.compile_match_dispatch(
            if catch.is_empty() { "rescue" } else { "catch" },
            span,
            params.len(),
            rows,
            Some(LastResort::reraise()),
        )?;
        let mut handler_steps = Vec::new();
        let bindings = self.lower_dispatch_bindings(&plan, env, &mut handler_steps)?;
        let mut free = HashSet::new();
        collect_rescue_clause_free_names(rescue, &mut HashSet::new(), &mut free);
        collect_catch_clause_free_names(catch, &mut HashSet::new(), &mut free);
        let captures = self.capture_values(free, env);
        let arm_blocks = plan
            .outcomes
            .iter()
            .map(|outcome| {
                let arm = &arms[outcome.body_id as usize];
                self.lower_handler_arm(outcome, arm.clause, (rescue, catch), raised, env.clone())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let dispatch_value = self.fresh_value();
        handler_steps.push(ExprStep::Dispatch {
            value: dispatch_value,
            inputs: params.clone(),
            bindings,
            dispatch: Box::new(ExprDispatch {
                plan: Rc::new(plan),
                arm_blocks,
                miss_block: None,
            }),
        });
        let handler = ExprBlock {
            span,
            steps: handler_steps,
            result: dispatch_value,
        };

        let value = self.fresh_value();
        steps.push(ExprStep::Try(Box::new(ExprTry {
            value,
            body,
            handler,
            params,
            captures,
        })));
        Ok(value)
    }

    /// The `else` clauses of a `try` as a case over the body's value. A value
    /// no clause matches raises `TryClauseError`. With no `else` clauses the
    /// value is the try's own.
    fn push_try_else(
        &mut self,
        span: Span,
        value: ValueId,
        else_clauses: &[MatchClause],
        env: &HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        if else_clauses.is_empty() {
            return Ok(value);
        }
        let block = self.lower_clause_dispatch_block(
            "try else",
            span,
            value,
            else_clauses,
            LastResort::try_clause(),
            env.clone(),
        )?;
        steps.extend(block.steps);
        Ok(block.result)
    }

    /// The handler's dispatch rows over the subjects (kind, value, exception
    /// name): the rescue rows, then one row per catch clause, as Elixir orders
    /// them.
    fn handler_arms(&mut self, rescue: &[RescueClause], catch: &[CatchClause]) -> Vec<HandlerArm> {
        let mut arms = self.rescue_arms(rescue);
        arms.extend(catch.iter().enumerate().map(|(clause, catch)| {
            HandlerArm::catch(
                PatternRow {
                    patterns: vec![
                        catch.kind.clone(),
                        catch.value.clone(),
                        Spanned::new(Pattern::Wildcard, catch.span),
                    ],
                    preconditions: Vec::new(),
                    guard: catch.guard.clone(),
                    body_id: 0,
                },
                clause,
            )
        }));
        for (index, arm) in arms.iter_mut().enumerate() {
            arm.row.body_id = index as PatternBodyId;
        }
        arms
    }

    /// One dispatch row per exception a rescue clause names. Rescue rows match
    /// kind `error` only, so a throw or an exit never reaches a rescue clause.
    /// A clause that admits a non-exception value (`ErlangError`, or a bare
    /// variable) gets a wrap row matching a nil exception name; its arm wraps
    /// the value in an `%ErlangError{}` before the clause body runs.
    fn rescue_arms(&mut self, rescue: &[RescueClause]) -> Vec<HandlerArm> {
        let mut arms = Vec::new();
        for (clause, rescue) in rescue.iter().enumerate() {
            let span = rescue.span;
            let pattern = |pattern: Pattern| Spanned::new(pattern, span);
            let error = pattern(Pattern::Atom(ERROR_KIND.to_string()));
            let bound = rescue.binding.clone().map(Pattern::Var).unwrap_or(Pattern::Wildcard);
            let wrap_row = PatternRow {
                patterns: vec![error.clone(), pattern(Pattern::Wildcard), pattern(Pattern::Nil)],
                preconditions: Vec::new(),
                guard: None,
                body_id: 0,
            };
            if rescue.exceptions.is_empty() {
                if rescue.binding.is_some() {
                    arms.push(HandlerArm::rescue(wrap_row, clause, true));
                }
                arms.push(HandlerArm::rescue(
                    PatternRow {
                        patterns: vec![error, pattern(bound), pattern(Pattern::Wildcard)],
                        preconditions: Vec::new(),
                        guard: None,
                        body_id: 0,
                    },
                    clause,
                    false,
                ));
                continue;
            }
            for exception in &rescue.exceptions {
                let atom = self
                    .world
                    .module_alias_atom(self.source.owner_module, self.namespace, exception)
                    .unwrap_or_else(|| exception.atom_name());
                let wraps = atom == ERLANG_ERROR;
                arms.push(HandlerArm::rescue(
                    PatternRow {
                        patterns: vec![error.clone(), pattern(bound.clone()), pattern(Pattern::Atom(atom))],
                        preconditions: Vec::new(),
                        guard: None,
                        body_id: 0,
                    },
                    clause,
                    false,
                ));
                if wraps {
                    arms.push(HandlerArm::rescue(wrap_row.clone(), clause, true));
                }
            }
        }
        arms
    }

    fn lower_handler_arm(
        &mut self,
        outcome: &crate::dispatch_matrix::pattern::PatternDispatchOutcome,
        arm: HandlerClause,
        (rescue, catch): (&[RescueClause], &[CatchClause]),
        raised: ValueId,
        mut env: HashMap<Var, ValueId>,
    ) -> Result<ExprOutcome, FatalError> {
        let arguments = self.bind_outcome_arguments(outcome, &mut env);
        let mut steps = Vec::new();
        let body = match arm {
            HandlerClause::Rescue { clause, wraps } => {
                let clause = &rescue[clause];
                if let (true, Some(binding)) = (wraps, &clause.binding) {
                    let wrapped = self.push_erlang_error(raised, &mut steps);
                    env.insert(binding.clone(), wrapped);
                }
                &clause.body
            }
            HandlerClause::Catch { clause } => &catch[clause].body,
        };
        let result = self.lower_expr(body, &mut env, &mut steps)?;
        Ok(ExprOutcome {
            arguments,
            block: ExprBlock {
                span: body.span,
                steps,
                result,
            },
        })
    }

    /// `%ErlangError{original: raised}`: how a raised non-exception value
    /// presents itself to a rescue clause.
    fn push_erlang_error(&mut self, raised: ValueId, steps: &mut Vec<ExprStep>) -> ValueId {
        let module = self.push_const(steps, GroundValue::Atom(ERLANG_ERROR.to_string()));
        let flag = self.push_const(steps, GroundValue::Bool(true));
        let entries = [("__struct__", module), ("__exception__", flag), ("original", raised)]
            .into_iter()
            .map(|(key, value)| {
                let literal = GroundValue::Atom(key.to_string());
                let key = self.push_const(steps, literal.clone());
                (
                    LoweredMapKey {
                        value: key,
                        literal: Some(literal),
                    },
                    value,
                )
            })
            .collect();
        let value = self.fresh_value();
        steps.push(ExprStep::Map {
            value,
            entries,
            quoted_span: None,
        });
        value
    }

    fn capture_values(&mut self, free: HashSet<Var>, env: &HashMap<Var, ValueId>) -> Vec<ValueId> {
        let mut captures = free
            .into_iter()
            .filter_map(|name| env.get(&name).copied())
            .collect::<Vec<_>>();
        captures.sort_by_key(|value| value.as_u32());
        captures.dedup();
        captures
    }

    fn lower_match_clause_block(
        &mut self,
        outcome: &crate::dispatch_matrix::pattern::PatternDispatchOutcome,
        clause: &MatchClause,
        mut env: HashMap<Var, ValueId>,
    ) -> Result<ExprOutcome, FatalError> {
        let arguments = self.bind_outcome_arguments(outcome, &mut env);
        let block = self.lower_expr_as_block(&clause.body, env)?;
        Ok(ExprOutcome { arguments, block })
    }

    fn bind_outcome_arguments(
        &mut self,
        outcome: &crate::dispatch_matrix::pattern::PatternDispatchOutcome,
        env: &mut HashMap<Var, ValueId>,
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
        input_count: usize,
        rows: Vec<PatternRow<super::super::types::Ty>>,
        last_resort: Option<LastResort>,
    ) -> Result<crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>, FatalError> {
        let source = SourcePatternRows::lexical(input_count, rows);
        let source = match last_resort {
            Some(last_resort) => source.raising(last_resort),
            None => source,
        };
        let namespace = self.namespace;
        let redundancy_check = (source.rows.len() > 1).then(|| source.clone());
        let mut resolver = super::super::dispatch::SourcePatternResolver {
            world: self.world,
            namespace,
            owner: self.source.owner_module,
            guard: |world: &mut World, callee: &Callee, arity: usize| {
                let callee = resolve_guard_callee_checked(world, namespace, callee, arity);
                Ok(Some(world.guard_callee(callee)))
            },
        };
        let plan = pattern_dispatch_from_source_with_resolver(source, &mut resolver)
            .map_err(|error| emit_local_dispatch_error(self.telemetry, label, span, error))?;
        if let Some(source) = redundancy_check {
            let redundant_rows = crate::dispatch_matrix::pattern::source::find_redundant_rows_with_resolver(
                &source,
                &plan,
                &mut resolver,
            );
            for redundant in redundant_rows {
                let always_matches_span = source.rows[redundant.always_matches as usize].patterns[0].span;
                let always_matches_line = self.world.source_map().borrow().locate(always_matches_span).line;
                let diagnostic = super::super::source_diagnostics::redundant_clause_diagnostic(
                    source.rows[redundant.body_id as usize].patterns[0].span,
                    always_matches_line,
                );
                super::super::drive::ExecutionContext::new(self.world, self.telemetry).emit_warning_once(diagnostic);
            }
        }
        Ok(plan)
    }

    fn compile_single_pattern_dispatch(
        &mut self,
        label: &str,
        pattern: &Spanned<Pattern>,
        span: Span,
        last_resort: Option<LastResort>,
    ) -> Result<crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>, FatalError> {
        self.compile_match_dispatch(
            label,
            span,
            1,
            vec![PatternRow {
                patterns: vec![pattern.clone()],
                preconditions: Vec::new(),
                guard: None,
                body_id: 0,
            }],
            last_resort,
        )
    }

    fn compile_bool_true_dispatch(
        &mut self,
        span: Span,
        last_resort: Option<LastResort>,
    ) -> Result<crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>, FatalError> {
        let rows = SourcePatternRows::lexical(
            1,
            vec![PatternRow {
                patterns: vec![Spanned::new(Pattern::Bool(true), span)],
                preconditions: Vec::new(),
                guard: None,
                body_id: 0,
            }],
        );
        let rows = match last_resort {
            Some(last_resort) => rows.raising(last_resort),
            None => rows,
        };
        pattern_dispatch_from_source(rows)
            .map_err(|error| emit_local_dispatch_error(self.telemetry, "cond", span, error))
    }

    /// Local dispatch rows carry no prematch, so every pin names a binding the
    /// enclosing environment already holds and resolves there by name.
    fn lower_dispatch_bindings(
        &mut self,
        plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>,
        env: &HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<DispatchBindings, FatalError> {
        let pinned = plan
            .pinned
            .iter()
            .map(|pinned| {
                env.get(&pinned.name).copied().ok_or_else(|| {
                    emit_job_diagnostic(
                        self.telemetry,
                        Diagnostic::error(codes::LOWER_UNBOUND, pinned.undefined_message(), pinned.span),
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
        env: &HashMap<Var, ValueId>,
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
        env: &HashMap<Var, ValueId>,
    ) -> Result<ExprReceiveAfter, FatalError> {
        Ok(ExprReceiveAfter {
            span: after.span,
            timeout,
            body: self.lower_expr_as_block(&after.body, env.clone())?,
        })
    }

    fn lower_lambda(
        &mut self,
        occurrence: crate::ast::LambdaOccurrence,
        span: Span,
        clauses: &[LambdaClause],
        env: &HashMap<Var, ValueId>,
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
            extern_abi: None,
            extern_param_tokens: Vec::new(),
            extern_ret_tokens: crate::ast::TypeExprBody(Vec::new()),
            extern_constraints: Vec::new(),
            extern_raises: None,
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
        for clause in clauses {
            let projections = clause.projections.iter().map(lower_projection_step).collect::<Vec<_>>();
            let entry = self.plan_block(
                clause.body.view(),
                ControlEntryOrigin::Clause,
                ControlDestination::Return,
                Vec::new(),
                Vec::new(),
                &mut entries,
            );
            lowered.push(LoweredClause {
                span: clause.span,
                params: clause.params,
                projections,
                entry,
            });
        }
        let mut body = LoweredBody::clauses(lowered, entries, self.generated_ids.clone());
        self.construct_entry_captures(&mut body);
        body.with_value_count(self.next_value as usize)
    }

    fn construct_entry_captures(&mut self, body: &mut LoweredBody) {
        use super::super::executable_facts::{TransportOrigin, collect_callsite_return_origins, collect_value_origins};
        use crate::fz_ir::ListRewritePermission;
        let scanned = Cell::new(0);
        let compared = Cell::new(0);
        let clause_bounds = clause_bounds(body);
        let origins = collect_value_origins(body, &collect_callsite_return_origins(body));
        let LoweredBody::Clauses { entries, .. } = body;
        let constructions = scan_steps(entries, &scanned)
            .filter_map(|(entry, step, instruction)| {
                let LoweredStep::List {
                    items, tail: Some(_), ..
                } = instruction
                else {
                    return None;
                };
                (items.len() == 1).then_some((entry, step, items[0]))
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
                TransportOrigin::OutcomeSubject { owner, subject }
                    if let Some(input) = decision_input_value(body, *owner, *subject) =>
                {
                    input
                }
                TransportOrigin::OutcomeSubject { owner, subject } => {
                    let LoweredBody::Clauses { entries, .. } = body;
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
            body.retain_list_source(
                ControlEntryId::from_u32(*entry as u32),
                *step,
                source,
                ListRewritePermission::RetainOnly,
            );
        }
        let LoweredBody::Clauses { entries, tables, .. } = body;
        let semantic = compute_entry_captures(entries, tables, &clause_bounds, false);
        let mut physical = compute_entry_captures(entries, tables, &clause_bounds, true);
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
        construct_tuple_ownership(body, &origins, &scanned, &compared);
        for (entry, step, _, _) in sources {
            let permission = if list_can_rewrite(body, &origins, entry, step) {
                ListRewritePermission::Rewrite
            } else {
                ListRewritePermission::RetainOnly
            };
            body.set_list_rewrite_permission(ControlEntryId::from_u32(entry as u32), step, permission);
        }
        self.ownership_steps_scanned += scanned.get();
        self.ownership_pairs_compared += compared.get();
    }

    fn plan_block(
        &mut self,
        block: BlockView<'_>,
        origin: ControlEntryOrigin,
        dest: ControlDestination,
        params: Vec<ValueId>,
        captures: Vec<ValueId>,
        entries: &mut Vec<LoweredEntry>,
    ) -> ControlEntryId {
        let (steps, tail) = self.plan_steps(block, dest, entries);
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
        block: BlockView<'_>,
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
                            block.after(index),
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
                            block.after(index),
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
                            block.after(index),
                            ControlEntryOrigin::DeliveredResume { value: *value },
                            dest,
                            Vec::new(),
                            Vec::new(),
                            entries,
                        );
                        ControlDestination::Deliver(resume)
                    };
                    let then_entry = self.plan_block(
                        then_block.view(),
                        ControlEntryOrigin::Branch,
                        branch_dest.clone(),
                        Vec::new(),
                        Vec::new(),
                        entries,
                    );
                    let else_entry = self.plan_block(
                        else_block.view(),
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
                            block.after(index),
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
                        .map(|arm| {
                            let params = arm.arguments.iter().map(|argument| argument.parameter).collect();
                            let target = self.plan_block(
                                arm.block.view(),
                                ControlEntryOrigin::Branch,
                                branch_dest.clone(),
                                params,
                                Vec::new(),
                                entries,
                            );
                            super::super::body::OutcomeEdge {
                                target,
                                arguments: arm.arguments.clone(),
                            }
                        })
                        .collect::<Vec<_>>();
                    let miss_entry = dispatch.miss_block.as_ref().map(|miss_block| {
                        self.plan_block(
                            miss_block.view(),
                            ControlEntryOrigin::Branch,
                            branch_dest,
                            Vec::new(),
                            Vec::new(),
                            entries,
                        )
                    });
                    return (
                        lowered,
                        LoweredTail::Dispatch {
                            inputs: inputs.clone(),
                            bindings: bindings.clone(),
                            dispatch: Box::new(ControlDispatch::new(dispatch.plan.clone(), outcomes, miss_entry)),
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
                            block.after(index),
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
                                outcome.block.view(),
                                ControlEntryOrigin::ReceiveOutcome,
                                branch_dest.clone(),
                                outcome.arguments.iter().map(|argument| argument.parameter).collect(),
                                captures.clone(),
                                entries,
                            );
                            super::super::body::OutcomeEdge {
                                arguments: outcome.arguments.clone(),
                                target,
                            }
                        })
                        .collect::<Vec<_>>();
                    let after = after.as_ref().map(|after| {
                        let entry = self.plan_block(
                            after.body.view(),
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
                ExprStep::Try(try_step) => {
                    let value = try_step.value;
                    let branch_dest = if index + 1 == block.steps.len() && value == block.result {
                        dest
                    } else {
                        let resume = self.plan_block(
                            block.after(index),
                            ControlEntryOrigin::DeliveredResume { value },
                            dest,
                            Vec::new(),
                            Vec::new(),
                            entries,
                        );
                        ControlDestination::Deliver(resume)
                    };
                    let body = self.plan_block(
                        try_step.body.view(),
                        ControlEntryOrigin::Branch,
                        branch_dest.clone(),
                        Vec::new(),
                        Vec::new(),
                        entries,
                    );
                    let handler = self.plan_block(
                        try_step.handler.view(),
                        ControlEntryOrigin::Handler,
                        branch_dest,
                        try_step.params.clone(),
                        try_step.captures.clone(),
                        entries,
                    );
                    return (lowered, LoweredTail::Try { body, handler });
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

    /// `pattern = value` is a decision of one row that raises `MatchError`
    /// when the row does not match. Its arm binds the pattern's names, and
    /// what follows the match reads them there. A pattern that binds without
    /// asking anything, such as a lone name, needs no decision at all.
    /// Lowers `pattern = value`. A pattern that wins at its root binds in
    /// place and answers `None`. Otherwise the match is a decision: when its
    /// value is consumed, its arm binds the names into `env` and delivers the
    /// value onward; when the rest of a body follows it, that rest is its
    /// arm, and the decision's own value is the body's result.
    fn lower_match(
        &mut self,
        pattern: &Spanned<Pattern>,
        value: ValueId,
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
        arm: MatchArm<'_>,
    ) -> Result<Option<ValueId>, FatalError> {
        let plan =
            self.compile_single_pattern_dispatch("match", pattern, pattern.span, Some(LastResort::match_error()))?;
        if plan.is_direct_outcome() {
            self.bind_pattern(&pattern.node, pattern.span, value, env, steps)?;
            return Ok(None);
        }
        let bindings = self.lower_dispatch_bindings(&plan, env, steps)?;
        let matched_value = ExprBlock {
            span: pattern.span,
            steps: Vec::new(),
            result: value,
        };
        let (arguments, block, decided) = match arm {
            MatchArm::Value => (self.bind_outcome_arguments(&plan.outcomes[0], env), matched_value, None),
            MatchArm::Rest(span, rest) => {
                let mut arm_env = env.clone();
                let arguments = self.bind_outcome_arguments(&plan.outcomes[0], &mut arm_env);
                let block = if rest.is_empty() {
                    matched_value
                } else {
                    self.lower_statements(span, rest, arm_env)?
                };
                (arguments, block, Some(self.fresh_value()))
            }
        };
        steps.push(ExprStep::Dispatch {
            value: decided.unwrap_or_else(|| self.fresh_value()),
            inputs: vec![value],
            bindings,
            dispatch: Box::new(ExprDispatch {
                plan: Rc::new(plan),
                arm_blocks: vec![ExprOutcome { arguments, block }],
                miss_block: None,
            }),
        });
        Ok(decided)
    }

    fn bind_pattern(
        &mut self,
        pattern: &Pattern,
        span: Span,
        source: ValueId,
        env: &mut HashMap<Var, ValueId>,
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
            Pattern::Both(left, right) => {
                self.bind_pattern(&left.node, left.span, source, env, steps)?;
                self.bind_pattern(&right.node, right.span, source, env, steps)
            }
            Pattern::Map(entries) => self.lower_map_pattern(entries, source, env, steps),
            Pattern::Struct { module, fields } => self.lower_struct_pattern(module, fields, span, source, env, steps),
            Pattern::Bitstring(fields) => self.lower_bitstring_pattern(fields, source, env, steps),
        }
    }

    fn lower_map_pattern(
        &mut self,
        entries: &[(Spanned<Pattern>, Spanned<Pattern>)],
        source: ValueId,
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
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
            self.bind_pattern(&value_pattern.node, value_pattern.span, value, env, steps)?;
        }
        Ok(())
    }

    fn lower_struct_pattern(
        &mut self,
        module: &crate::ast::ModuleTarget,
        fields: &[(String, Spanned<Pattern>)],
        span: Span,
        source: ValueId,
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
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
            self.bind_pattern(&pattern.node, pattern.span, value, env, steps)?;
        }
        Ok(())
    }

    fn lower_bitstring_pattern(
        &mut self,
        fields: &[BitField<Spanned<Pattern>>],
        source: ValueId,
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
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
            self.bind_pattern(&field.value.node, field.value.span, value, env, steps)?;
            reader = next_reader;
        }
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
        ExprStep::MapUpdate {
            value,
            ok,
            base,
            entries,
        } => LoweredStep::MapUpdate {
            value: *value,
            ok: *ok,
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
        ExprStep::RequireMapValue { value, source, key } => LoweredStep::RequireMapValue {
            value: *value,
            source: *source,
            key: key.clone(),
        },
        ExprStep::TupleField { value, source, index } => LoweredStep::TupleField {
            value: *value,
            source: *source,
            index: *index,
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
        ExprStep::PopHandler => LoweredStep::PopHandler,
        ExprStep::DirectCall { .. }
        | ExprStep::ClosureCall { .. }
        | ExprStep::If { .. }
        | ExprStep::Dispatch { .. }
        | ExprStep::Receive(_)
        | ExprStep::Try(_) => {
            panic!("control steps should be lowered into tails before projection conversion")
        }
    }
}

/// What the arm of a match decision does once the pattern has bound.
enum MatchArm<'a> {
    /// The match's value is consumed where it stands: the arm delivers it.
    Value,
    /// The rest of a body follows the match: the arm is that rest.
    Rest(Span, &'a [Spanned<Expr>]),
}

/// The value a decision was handed for `subject`, when `subject` is one of
/// its inputs: that value is the subject.
fn decision_input_value(
    body: &LoweredBody,
    owner: ControlEntryId,
    subject: crate::dispatch_matrix::SubjectId,
) -> Option<ValueId> {
    let LoweredBody::Clauses { entries, .. } = body;
    let LoweredTail::Dispatch { inputs, dispatch, .. } = &entries[owner.as_u32() as usize].tail else {
        return None;
    };
    let crate::dispatch_matrix::SubjectSource::Input { ordinal } = &dispatch.plan.graph.subject(subject)?.source else {
        return None;
    };
    inputs.get(*ordinal as usize).copied()
}

/// The values a clause binds before its entry runs: the clause parameters and
/// everything its projections define.
fn clause_bounds(body: &LoweredBody) -> HashMap<ControlEntryId, ValueSet> {
    let LoweredBody::Clauses { clauses, tables, .. } = body;
    clauses
        .iter()
        .enumerate()
        .map(|(index, clause)| {
            let mut bound = clause.params.iter().copied().collect::<ValueSet>();
            bound.extend(tables.clause_defines(index));
            (clause.entry, bound)
        })
        .collect()
}

/// Every step in the body with its position, counted as the scan reads it.
///
/// Ownership construction is entitled to a fixed number of passes over the
/// steps; the count is published on the lowering job so a pass that starts
/// searching the body again says so in the telemetry.
fn scan_steps<'a>(
    entries: &'a [LoweredEntry],
    scanned: &'a Cell<u64>,
) -> impl Iterator<Item = (usize, usize, &'a LoweredStep)> + 'a {
    entries.iter().enumerate().flat_map(move |(entry, block)| {
        block.steps.iter().enumerate().map(move |(step, instruction)| {
            scanned.set(scanned.get() + 1);
            (entry, step, instruction)
        })
    })
}

fn compute_entry_captures(
    entries: &[LoweredEntry],
    tables: &BodyTables,
    clause_bounds: &HashMap<ControlEntryId, ValueSet>,
    physical: bool,
) -> Vec<Vec<ValueId>> {
    let mut memo = HashMap::new();
    for entry_id in 0..entries.len() {
        let entry_id = ControlEntryId::from_u32(entry_id as u32);
        let _ = entry_captures(entries, tables, clause_bounds, entry_id, physical, &mut memo);
    }
    (0..entries.len())
        .map(|index| memo.remove(&ControlEntryId::from_u32(index as u32)).unwrap_or_default())
        .collect()
}

fn list_source_origin(
    body: &LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
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
            let LoweredBody::Clauses { entries, .. } = body;
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
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
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
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    root: ValueId,
    path: &[crate::dispatch_matrix::ProjectionKind],
) -> Option<(ValueId, usize)> {
    use crate::dispatch_matrix::ProjectionKind;
    if let Some(ProjectionKind::TupleField(index)) = path.first()
        && let Some(super::super::executable_facts::TransportOrigin::TupleValue(items)) = origins.get(&root)
    {
        return items.get(*index as usize).map(|item| (*item, 1));
    }
    let LoweredStep::List { items, tail, .. } = body.value_definition(root)? else {
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
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    entry: usize,
    step: usize,
) -> bool {
    use super::super::executable_facts::TransportOrigin;
    let LoweredBody::Clauses { entries, .. } = body;
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
        .any(|operand| value_may_retain_source(body, origins, *operand, &source, Some(*value), &mut ValueSet::new()))
        && !source_used_after(body, origins, entry, step, &source)
}

fn source_used_after(
    body: &LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    entry: usize,
    step: usize,
    source: &SourcePath,
) -> bool {
    let LoweredBody::Clauses { entries, .. } = body;
    let exempt = match entries[entry].steps.get(step) {
        Some(LoweredStep::List { value, .. } | LoweredStep::Tuple { value, .. }) => Some(*value),
        _ => None,
    };
    any_later_ownership_use(body, entry, step, |value, role| match role {
        super::super::body::ValueRole::Semantic => {
            value_may_retain_source(body, origins, value, source, exempt, &mut ValueSet::new())
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

/// Whether any use that can still happen after `step` of `entry` competes for
/// ownership.
///
/// Later means later in this entry, or anywhere in the entries it reaches: a
/// reached entry runs in full, so its first step is as "later" as its last.
/// Both questions are answered from the body's use tables, so the walk costs
/// one visit per reachable entry and one per use it offers, never a search
/// through the body's steps.
fn any_later_ownership_use(
    body: &LoweredBody,
    entry: usize,
    step: usize,
    mut competes: impl FnMut(ValueId, super::super::body::ValueRole) -> bool,
) -> bool {
    use super::super::body::ValueRole;
    let LoweredBody::Clauses { entries, tables, .. } = body;
    let mut pending = vec![(ControlEntryId::from_u32(entry as u32), step as u32 + 1)];
    let mut visited = HashSet::new();
    while let Some((block_id, start)) = pending.pop() {
        if !visited.insert(block_id) {
            continue;
        }
        if tables
            .entry_retentions_from(block_id, start)
            .any(|source| competes(source, ValueRole::Physical))
        {
            return true;
        }
        let used = tables.entry_uses_from(block_id, start).collect::<ValueSet>();
        if used.keys().any(|value| competes(value, ValueRole::Semantic)) {
            return true;
        }
        let block = &entries[block_id.as_u32() as usize];
        pending.extend(child_entries(&block.tail).into_iter().map(|child| (child, 0)));
    }
    false
}

fn value_is_new_owner_projection(
    body: &LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
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
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
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
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    value: ValueId,
    source: &SourcePath,
    exempt: Option<ValueId>,
    visiting: &mut ValueSet,
) -> bool {
    use super::super::executable_facts::TransportOrigin;
    if exempt.is_some_and(|owner| value_is_new_owner_projection(body, origins, value, owner)) {
        return false;
    }
    if SubjectOriginRoot::Value(value) == source.0 || !visiting.mark(value) {
        return true;
    }
    if let Some((root, path)) = origin_source_path(body, origins, &TransportOrigin::LocalValue(value))
        && root == source.0
    {
        visiting.unmark(&value);
        return source.1.starts_with(&path);
    }
    let retained = if let Some(origin) = origins.get(&value) {
        origin_may_retain_source(body, origins, origin, source, exempt, visiting)
    } else {
        match body.value_definition(value) {
            Some(
                LoweredStep::Const { .. }
                | LoweredStep::FunctionRef { .. }
                | LoweredStep::UnaryOp { .. }
                | LoweredStep::BinaryOp { .. }
                | LoweredStep::Bitstring { .. },
            ) => false,
            Some(step) => {
                let mut operands = Vec::new();
                step_used_values(step, &mut operands);
                if let LoweredStep::List {
                    retention: Some(retention),
                    ..
                } = step
                {
                    let identity = origin_source_path(body, origins, &TransportOrigin::LocalValue(retention.source));
                    if identity.as_ref().is_none_or(|identity| identity == source) {
                        visiting.unmark(&value);
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
    visiting.unmark(&value);
    retained
}

fn origin_may_retain_source(
    body: &LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    origin: &super::super::executable_facts::TransportOrigin,
    source: &SourcePath,
    exempt: Option<ValueId>,
    visiting: &mut ValueSet,
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
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    left: ValueId,
    right: ValueId,
) -> bool {
    values_overlap_inner(body, origins, left, right, None, &mut ValueMap::new())
}

fn values_overlap_inner(
    body: &LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    left: ValueId,
    right: ValueId,
    exempt: Option<ValueId>,
    visited: &mut ValueMap<ValueSet>,
) -> bool {
    use super::super::executable_facts::TransportOrigin;
    if !visited.or_default(left).mark(right) {
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
    value_may_retain_source(body, origins, left, &right_path, exempt, &mut ValueSet::new())
        || value_may_retain_source(body, origins, right, &left_path, exempt, &mut ValueSet::new())
        || construction_children(body, origins, left)
            .into_iter()
            .any(|child| values_overlap_inner(body, origins, child, right, exempt, visited))
        || construction_children(body, origins, right)
            .into_iter()
            .any(|child| values_overlap_inner(body, origins, left, child, exempt, visited))
}

fn construction_children(
    body: &LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
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
    match body.value_definition(value) {
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
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
) {
    use super::super::executable_facts::TransportOrigin;
    use crate::fz_ir::OwnershipMode;
    let LoweredBody::Clauses { entries, .. } = body;
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
                        let LoweredBody::Clauses { entries, .. } = &*body;
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
                                value_may_retain_source(body, origins, *arg, &source, None, &mut ValueSet::new())
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
        let LoweredBody::Clauses { entries, .. } = body;
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
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    scanned: &Cell<u64>,
    compared: &Cell<u64>,
) {
    use crate::fz_ir::OwnershipMode;
    let LoweredBody::Clauses { entries, .. } = body;
    let tuples = scan_steps(entries, scanned)
        .filter_map(|(entry, step, instruction)| match instruction {
            LoweredStep::Tuple { value, items } => Some((
                entry,
                step,
                *value,
                items.iter().map(|item| item.value).collect::<Vec<_>>(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    let index = StorageRootIndex::new(body, origins);
    let mut reached = (usize::MAX, HashSet::new());
    for (entry, step, result, items) in tuples {
        if reached.0 != entry {
            reached = (entry, entries_reached_from(body, entry));
        }
        let later = LaterUses::after(entry, step, &reached.1);
        let modes = items
            .iter()
            .enumerate()
            .map(|(position, item)| {
                let peers_overlap = items
                    .iter()
                    .enumerate()
                    .any(|(peer, other)| position != peer && values_overlap(body, origins, *item, *other));
                let shares =
                    peers_overlap || tuple_item_has_old_owner(body, origins, &index, &later, result, *item, compared);
                if shares {
                    OwnershipMode::Share
                } else {
                    OwnershipMode::Transfer
                }
            })
            .collect::<Vec<_>>();
        let LoweredBody::Clauses { entries, .. } = body;
        let LoweredStep::Tuple { items, .. } = &mut entries[entry].steps[step] else {
            unreachable!()
        };
        for (item, mode) in items.iter_mut().zip(modes) {
            item.mode = mode;
        }
    }
}

/// Whether a use after the step `later` follows can still reach the storage
/// the tuple `result` would hand over with `item`. An item with a bounded
/// footprint is set only against the later uses that share one of its roots; an
/// open item is set against every later use.
fn tuple_item_has_old_owner(
    body: &LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    index: &StorageRootIndex,
    later: &LaterUses<'_>,
    result: ValueId,
    item: ValueId,
    compared: &Cell<u64>,
) -> bool {
    use super::super::body::ValueRole;
    let overlaps = |value: ValueId| {
        compared.set(compared.get() + 1);
        values_overlap_inner(body, origins, value, item, Some(result), &mut ValueMap::new())
    };
    let retains = |value: ValueId| {
        origin_source_path(
            body,
            origins,
            &super::super::executable_facts::TransportOrigin::LocalValue(value),
        )
        .is_none_or(|source| value_may_retain_source(body, origins, item, &source, Some(result), &mut ValueSet::new()))
    };
    let Some(competitors) = index.competitors_after(item, later) else {
        return any_later_ownership_use(body, later.entry(), later.step(), |value, role| match role {
            ValueRole::Semantic => overlaps(value),
            ValueRole::Physical => retains(value),
        });
    };
    later.retained_sources(body).any(retains) || competitors.into_iter().any(overlaps)
}

fn entry_captures(
    entries: &[LoweredEntry],
    tables: &BodyTables,
    clause_bounds: &HashMap<ControlEntryId, ValueSet>,
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
        bound.mark(value);
    }
    bound.extend(tables.entry_defines(entry_id));

    let mut needed = if physical {
        tables.entry_retentions_from(entry_id, 0).collect::<ValueSet>()
    } else {
        tables.entry_uses_from(entry_id, 0).collect::<ValueSet>()
    };
    for child in child_entries(&entry.tail) {
        for capture in entry_captures(entries, tables, clause_bounds, child, physical, memo) {
            if !bound.contains(&capture) {
                needed.mark(capture);
            }
        }
    }
    needed.retain(|value, _| !bound.contains(value));
    let mut ordered = needed.keys().collect::<Vec<_>>();
    for capture in &entry.captures {
        if !ordered.contains(capture) {
            ordered.push(*capture);
        }
    }
    ordered.sort_by_key(|value| value.as_u32());
    memo.insert(entry_id, ordered.clone());
    ordered
}

/// Every value identity retained by a lowered body's executable surface.
/// Running this after artifact pruning gives downstream products the exact
/// value-type subset that can still be interpreted or lowered.
pub(super) fn retained_value_ids(body: &LoweredBody) -> ValueSet {
    let LoweredBody::Clauses {
        clauses,
        entries,
        tables,
        ..
    } = body;
    let mut retained = ValueSet::new();
    for (index, clause) in clauses.iter().enumerate() {
        retained.extend(clause.params.iter().copied());
        retained.extend(tables.clause_defines(index));
        retained.extend(tables.clause_uses(index));
    }
    for (index, entry) in entries.iter().enumerate() {
        let entry_id = ControlEntryId::from_u32(index as u32);
        retained.extend(entry.params.iter().copied());
        retained.extend(entry.captures.iter().copied());
        retained.extend(entry.physical_captures.iter().copied());
        retained.extend(tables.entry_retentions_from(entry_id, 0));
        if let Some(value) = entry.origin.input_value() {
            retained.mark(value);
        }
        retained.extend(tables.entry_defines(entry_id));
        retained.extend(tables.entry_uses_from(entry_id, 0));
    }
    retained
}

fn child_entries(tail: &LoweredTail) -> Vec<ControlEntryId> {
    match tail {
        LoweredTail::Value { dest, .. }
        | LoweredTail::DirectCall { dest, .. }
        | LoweredTail::ClosureCall { dest, .. } => match dest {
            ControlDestination::Return => Vec::new(),
            ControlDestination::Deliver(entry) => vec![*entry],
        },
        LoweredTail::If {
            then_entry, else_entry, ..
        } => vec![*then_entry, *else_entry],
        LoweredTail::Dispatch { dispatch, .. } => dispatch.successors().collect(),
        LoweredTail::Receive(receive) => {
            let mut children = receive.outcomes.iter().map(|edge| edge.target).collect::<Vec<_>>();
            if let Some(after) = &receive.after {
                children.push(after.entry);
            }
            children
        }
        LoweredTail::Try { body, handler } => vec![*body, *handler],
        LoweredTail::Unreachable => Vec::new(),
    }
}

fn lambda_free_names(clauses: &[LambdaClause]) -> HashSet<Var> {
    let mut free = HashSet::new();
    for clause in clauses {
        let mut bound = HashSet::new();
        // A pin in a parameter names a value bound before the clause began, so
        // the lambda has to close over it just like a body reference. Free
        // names come first, against the empty pre-pattern scope, because the
        // parameters bind nothing a sibling parameter's pin may reach.
        for param in &clause.params {
            collect_pattern_free_names(&param.node, &mut bound, &mut free);
        }
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

fn bind_pattern_names(pattern: &Pattern, bound: &mut HashSet<Var>) {
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
        Pattern::Both(left, right) => {
            bind_pattern_names(&left.node, bound);
            bind_pattern_names(&right.node, bound);
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

fn collect_expr_free_names(expr: &Expr, bound: &mut HashSet<Var>, free: &mut HashSet<Var>) {
    match expr {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Alias(_)
        | Expr::Module(_)
        | Expr::BoundFunction(_)
        | Expr::FnRef { .. }
        | Expr::CaptureArg(_) => {}
        // A quote's own text names quoted data, not a real reference to
        // anything in the enclosing scope. Its `unquote` splices are
        // ordinary code, already decoded, so they contribute captures like
        // any other expression.
        Expr::Quote(_, splices) => {
            for spliced in splices {
                collect_expr_free_names(&spliced.node, bound, free);
            }
        }
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
        Expr::UnOp(_, expr) | Expr::Ascribe(expr, _) | Expr::Unquote(expr) => {
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
        Expr::Try {
            body,
            rescue,
            catch,
            else_clauses,
            after,
        } => {
            collect_expr_free_names(&body.node, &mut bound.clone(), free);
            collect_rescue_clause_free_names(rescue, bound, free);
            collect_catch_clause_free_names(catch, bound, free);
            collect_match_clause_free_names(else_clauses, bound, free);
            if let Some(after) = after {
                collect_expr_free_names(&after.node, &mut bound.clone(), free);
            }
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

fn collect_pattern_free_names(pattern: &Pattern, bound: &mut HashSet<Var>, free: &mut HashSet<Var>) {
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
        Pattern::Both(left, right) => {
            collect_pattern_free_names(&left.node, bound, free);
            collect_pattern_free_names(&right.node, bound, free);
        }
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

fn collect_match_clause_free_names(clauses: &[MatchClause], bound: &mut HashSet<Var>, free: &mut HashSet<Var>) {
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

fn collect_rescue_clause_free_names(clauses: &[RescueClause], bound: &mut HashSet<Var>, free: &mut HashSet<Var>) {
    for clause in clauses {
        let mut clause_bound = bound.clone();
        clause_bound.extend(clause.binding.iter().cloned());
        collect_expr_free_names(&clause.body.node, &mut clause_bound, free);
    }
}

fn collect_catch_clause_free_names(clauses: &[CatchClause], bound: &mut HashSet<Var>, free: &mut HashSet<Var>) {
    for clause in clauses {
        let mut clause_bound = bound.clone();
        for pattern in [&clause.kind, &clause.value] {
            collect_pattern_free_names(&pattern.node, &mut clause_bound, free);
            bind_pattern_names(&pattern.node, &mut clause_bound);
        }
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
        // Local rows are matched inside a live scope, so their pins are carried
        // to `lower_dispatch_bindings` and resolved by name there; the producer
        // never refuses one here.
        PatternDispatchError::SourcePattern(
            SourcePatternError::UnknownSubject(_)
            | SourcePatternError::UnresolvedStruct(_)
            | SourcePatternError::RowPatternArity { .. }
            | SourcePatternError::NonMonotonicBodyId { .. }
            | SourcePatternError::UndefinedPins(_)
            | SourcePatternError::GuardExternClass { .. }
            | SourcePatternError::ParamAnnotation { .. },
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
        Expr::Alias(_) => "Alias",
        Expr::Module(_) => "Module",
        Expr::BoundFunction(_) => "BoundFunction",
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
        Expr::Try { .. } => "Try",
        Expr::Match(_, _) => "Match",
        Expr::Block(_) => "Block",
        Expr::Lambda { .. } => "Lambda",
        Expr::Quote(_, _) => "Quote",
        Expr::Unquote(_) => "Unquote",
    }
}

/// The callable this call target names, unless a local of that name shadows it.
///
/// Which shapes name a callable is [`Callee`]'s question; the only thing added
/// here is that a bound local wins over a same-spelled definition.
/// `Map.update_key_error/2`, named exactly so no alias in scope can
/// redirect it.
fn update_key_error_callee() -> Callee {
    Callee::Name(CallableName {
        module: Some(crate::ast::ModuleTarget::Exact(ModuleDenotation::Named(
            ModuleName::from_segments(vec!["Map".to_string()]),
        ))),
        name: "update_key_error".to_string(),
    })
}

fn direct_callee(expr: &Spanned<Expr>, arity: usize, env: &HashMap<Var, ValueId>) -> Option<Callee> {
    let mut current = &expr.node;
    loop {
        match current {
            Expr::Var(name) => {
                if env.contains_key(name) {
                    return None;
                }
                break;
            }
            Expr::Alias(_) | Expr::Module(_) | Expr::BoundFunction(_) => break,
            Expr::Index(target, _) => {
                current = &target.node;
            }
            _ => return None,
        }
    }
    Callee::for_call(&expr.node, arity)
}

fn direct_operator_name(op: crate::ast::BinOp) -> Option<&'static str> {
    match op {
        crate::ast::BinOp::Add
        | crate::ast::BinOp::Sub
        | crate::ast::BinOp::Mul
        | crate::ast::BinOp::Div
        | crate::ast::BinOp::Rem => op.arithmetic_function(),
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
        | Pattern::Both(_, _)
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
        Pattern::Both(_, _) => "Both",
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
