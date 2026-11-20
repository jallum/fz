//! Compiler2 body-lowering jobs and helpers.
//!
//! This module lowers one defined function at a time into Compiler2's
//! structured body form. It owns the local lowering algorithm, lambda capture
//! discovery, and generated-function definition path.

use crate::compiler2::{ValueMap, ValueSet};
use crate::fast_hash::{HashMap, HashSet};
use std::borrow::Cow;
use std::cell::Cell;
use std::rc::Rc;

use crate::ast::{
    AfterClause, BinOp, BitField, BitSize, CallableName, Callee, CatchClause, Expr, FnClause, LambdaClause,
    MatchClause, Pattern, RescueClause, Spanned, TryForm, UnOp, Var, VarContext, WithBinding,
};
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::dispatch_matrix::pattern::{
    LastResort, PatternBodyId, PatternDispatchError, PatternRow, SourcePatternError, SourcePatternRows,
    pattern_dispatch_from_source, pattern_dispatch_from_source_with_resolver,
};
use fz_runtime::any_value::ValueKind;

use crate::function_surface::FunctionSurface;
use crate::ground_value::GroundValue;
use crate::literal_term::LiteralTerm;
use crate::modules::identity::{ModuleDenotation, ModuleName};
use crate::source::{SourceMap, Span};

use super::super::body::{
    BodyTables, CallArg, CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, ControlEntryOrigin,
    DirectCallee, DispatchBindings, LoweredBitField, LoweredBitFieldSpec, LoweredBitSize, LoweredBody, LoweredClause,
    LoweredEntry, LoweredMapKey, LoweredStep, LoweredTail, OutcomeArgument, ReceiveAfter, SubjectOriginRoot,
    SubjectOwner, SubjectPath, ValueId, step_used_values,
};
use super::super::code::SourceOwner;
use super::super::drive::{FactKey, JobEffects, current_uses, emit_job_diagnostic};
use super::super::identity::{FunctionId, FunctionSource, ModuleId};
use super::super::module_interface::{InterfaceCallableKind, InterfaceRequester};
use super::super::namespace::{Namespace, NamespaceSymbol};
use super::super::quoted_expander::emit_surface_read_error;
use super::super::source::{QuotedAstNode, QuotedSourceCursor, QuotedSourceError};
use super::super::world::World;
use super::dispatch::{
    collect_guard_calls_in_expr, hoist_zero_argument_guard_calls, resolve_guard_callee, resolve_guard_callee_checked,
};
use fz_engine::{FactUse, FatalError};

mod storage_roots;
use storage_roots::{LaterUses, StorageRootIndex, entries_reached_from};

type Output = FactKey;
type Changed = FactKey;

#[derive(Debug)]
struct ExprClause {
    span: Span,
    params: Vec<ValueId>,
    arguments: Box<[super::super::body::OutcomeArgument]>,
    body: ExprBlock,
}

#[derive(Debug)]
struct ExprBlock {
    span: Span,
    steps: Vec<ExprStep>,
    result: ValueId,
}

impl ExprBlock {
    fn into_pending(self) -> PendingBlock {
        PendingBlock {
            span: self.span,
            steps: self.steps.into_iter(),
            result: self.result,
            unplaced: Unplaced::default(),
        }
    }
}

/// The steps of a block still to be planned, taken front to back. What is
/// left after a step is the block that resumes there.
struct PendingBlock {
    span: Span,
    steps: std::vec::IntoIter<ExprStep>,
    result: ValueId,
    /// Ground constants an earlier block met and left for the first step
    /// here that reads one.
    unplaced: Unplaced,
}

impl PendingBlock {
    /// Whether nothing remains but the value of the step that was just taken.
    fn resumes_nothing_after(&self, value: ValueId) -> bool {
        self.steps.len() == 0 && value == self.result
    }
}

/// Ground constants whose definition waits for the step that reads them. A
/// constant has no effect, so it is computed where it is used: ahead of its
/// first reader in the block, or in the block that resumes after a call when
/// the call does not read it, instead of in a frame carried across the call.
#[derive(Default)]
struct Unplaced(Vec<(ValueId, LiteralTerm)>);

impl Unplaced {
    fn hold(&mut self, value: ValueId, literal: LiteralTerm) {
        self.0.push((value, literal));
    }

    /// Places the constants among `operands` ahead of the step that reads them.
    fn place_read_by(&mut self, operands: &[ValueId], lowered: &mut Vec<LoweredStep>) {
        let (read, rest): (Vec<_>, Vec<_>) = std::mem::take(&mut self.0)
            .into_iter()
            .partition(|(value, _)| operands.contains(value));
        self.0 = rest;
        lowered.extend(
            read.into_iter()
                .map(|(value, literal)| LoweredStep::Const { value, literal }),
        );
    }

    /// Places the constants a call reads ahead of it, and, when no block
    /// resumes after the call, the rest as well.
    fn place_before_call(
        &mut self,
        operands: &[ValueId],
        rest: &PendingBlock,
        call: ValueId,
        lowered: &mut Vec<LoweredStep>,
    ) {
        if rest.resumes_nothing_after(call) {
            self.place_all(lowered);
        } else {
            self.place_read_by(operands, lowered);
        }
    }

    /// Places every constant, for a step whose nested blocks may read any.
    fn place_all(&mut self, lowered: &mut Vec<LoweredStep>) {
        lowered.extend(
            std::mem::take(&mut self.0)
                .into_iter()
                .map(|(value, literal)| LoweredStep::Const { value, literal }),
        );
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
    form: TryForm,
}

const ERROR_KIND: &str = "error";
const ERLANG_ERROR: &str = "Elixir.ErlangError";
const STACKTRACE_OUTSIDE_A_HANDLER_CLAUSE: &str =
    "__STACKTRACE__ is available only inside catch and rescue clauses of try expressions";

#[derive(Debug)]
enum ExprStep {
    Const {
        value: ValueId,
        literal: LiteralTerm,
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
        callee: DirectCallee,
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
}

/// The facts `lower_function` cannot conclude without: the function's own
/// definition, and the entry plan that hands each clause the values its
/// pattern binds.
pub(super) fn lower_function_gates(world: &World, function: FunctionId) -> Vec<FactKey> {
    if world.function_defined_revision(function).is_none() {
        return vec![FactKey::FunctionDefined(function)];
    }
    let entry_plan = FactKey::EntryDispatch(function);
    if !world.has_fact(&entry_plan) {
        return vec![entry_plan];
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
    let (source, surface) = (Rc::clone(source), Rc::clone(surface));
    debug_assert!(
        surface.extern_abi.is_none(),
        "an extern has no LoweredBody; nothing should ever demand one for {function:?}"
    );

    let mut reads = vec![FactKey::FunctionDefined(function)];
    let mut waits = HashSet::default();
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

    for diagnostic in super::scope::unused_variable_diagnostics(&surface.clauses) {
        super::super::drive::ExecutionContext::new(world, tel).emit_warning_once(diagnostic);
    }
    let entry_plan = world.entry_dispatch(function);
    let mut lowerer = Lowerer::new(world, tel, function, &source, &surface);
    let (body, mut outputs, mut changed) = lowerer.lower(entry_plan)?;
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
    // The plan is read as a concluded answer: a redefinition outdates it before
    // its own job has re-run, and a body lowered against the outdated plan
    // would bind names the new head does not have.
    let mut reads = current_uses(reads);
    reads.push(FactUse::concluded(FactKey::EntryDispatch(function)));
    Ok(JobEffects {
        reads,
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
            form: _,
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
                for exception in &clause.exceptions {
                    let module = world.resolve_module_name(namespace, &exception.node);
                    record_struct_reference(
                        world,
                        tel,
                        owner_module,
                        owner,
                        module,
                        std::iter::empty(),
                        exception.span,
                        reads,
                        waits,
                    )?;
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
            let module = world.resolve_module_target(namespace, module);
            record_struct_reference(
                world,
                tel,
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
            let module = world.resolve_module_target(namespace, module);
            record_struct_reference(
                world,
                tel,
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
/// mirror `source_publish.rs`'s `collect_type_references` (same
/// expectation store, so a non-struct module or bad field is diagnosed at
/// the requester regardless of whether the reference came from a type
/// position or a body position), and the `StructDefined` wait half mirrors
/// every other consumer in this file (`lower_function`'s extern-contract loop,
/// `plan_entry_dispatch`, `derive_function_contract`) — `Mod`'s field *order*
/// is unknown until `StructDefined(Mod)` publishes, so the caller must wait
/// rather than guess an order from the literal/pattern's own field list.
///
/// `module_id` is the module the name resolves to in the reference's own
/// namespace, the same one the later `Lowerer` pass consumes.
#[allow(clippy::too_many_arguments)]
pub(super) fn record_struct_reference<'a>(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    owner_module: ModuleId,
    owner: SourceOwner,
    module_id: ModuleId,
    fields: impl Iterator<Item = &'a str>,
    span: Span,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<(), FatalError> {
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
    ///
    /// Everything but an `unquote` is known here, so a subtree that holds none
    /// is one constant and only the nodes above an `unquote` are built.
    fn lower(&mut self, cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<ValueId, FatalError> {
        let quoted = self.quoted(cursor, sources)?;
        Ok(self.value(quoted))
    }

    fn quoted(&mut self, cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<Quoted, FatalError> {
        match self.ast_node(cursor, sources)? {
            Some(node) => self.lower_ast_node(&node, sources),
            None => self.lower_literal(cursor, sources),
        }
    }

    fn each_quoted(&mut self, cursors: &[QuotedSourceCursor], sources: &SourceMap) -> Result<Vec<Quoted>, FatalError> {
        cursors.iter().map(|cursor| self.quoted(cursor, sources)).collect()
    }

    fn ast_node(&self, cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<Option<QuotedAstNode>, FatalError> {
        cursor.ast_node(sources).map_err(|error| self.surface_error(error))
    }

    fn surface_error(&self, error: QuotedSourceError) -> FatalError {
        emit_surface_read_error(self.lowerer.telemetry, "compiler2 quote lowering", &error)
    }

    fn lower_literal(&mut self, cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<Quoted, FatalError> {
        let ground = match cursor.root().tag() {
            ValueKind::INT => GroundValue::Int(cursor.int_value().map_err(|error| self.surface_error(error))?),
            ValueKind::FLOAT => GroundValue::from_f64(
                cursor
                    .root()
                    .load_float()
                    .map_err(|error| self.surface_error(error.into()))?,
            ),
            ValueKind::ATOM => {
                let atom = cursor.atom_name().map_err(|error| self.surface_error(error))?;
                match atom.as_str() {
                    "true" => GroundValue::Bool(true),
                    "false" => GroundValue::Bool(false),
                    "nil" => GroundValue::Nil,
                    _ => GroundValue::Atom(atom.to_string()),
                }
            }
            ValueKind::BITSTRING | ValueKind::BINVIEW => {
                GroundValue::Binary(cursor.raw_bytes().map_err(|error| self.surface_error(error))?)
            }
            ValueKind::LIST => {
                let items = cursor.list_items().map_err(|error| self.surface_error(error))?;
                let items = self.each_quoted(&items, sources)?;
                return Ok(self.list(items));
            }
            ValueKind::STRUCT => {
                let items = cursor.tuple_items().map_err(|error| self.surface_error(error))?;
                let items = self.each_quoted(&items, sources)?;
                return Ok(self.tuple(items));
            }
            other => {
                return Err(self.surface_error(QuotedSourceError::new(format!(
                    "unsupported quoted source runtime kind {other:?}"
                ))));
            }
        };
        Ok(Quoted::Constant(ground.into()))
    }

    fn lower_ast_node(&mut self, node: &QuotedAstNode, sources: &SourceMap) -> Result<Quoted, FatalError> {
        if node.tail.root().tag() != ValueKind::LIST {
            let name = node.head.atom_name().map_err(|error| self.surface_error(error))?;
            return Ok(self.lower_variable(&name));
        }

        let args = node.tail.list_items().map_err(|error| self.surface_error(error))?;

        if node.head.root().tag() == ValueKind::ATOM {
            let name = node.head.atom_name().map_err(|error| self.surface_error(error))?;
            if name == "unquote" && args.len() == 1 {
                return self.lower_unquote().map(Quoted::Built);
            }
            let values = self.each_quoted(&args, sources)?;
            let bound = self.resolve_quoted_callable(&name, values.len());
            return Ok(self.lower_call_node(&name, bound, values));
        }

        let head = self.quoted(&node.head, sources)?;
        let values = self.each_quoted(&args, sources)?;
        let tail = self.list(values);
        Ok(self.ast_node_of(head, tail))
    }

    /// `unquote(e)` splices `e`'s runtime value in place: `e` was already
    /// decoded alongside the quote itself, so lowering just takes the next
    /// one in walk order and lowers it as an ordinary expression, in the
    /// surrounding scope, exactly as if it had been written there directly.
    fn lower_unquote(&mut self) -> Result<ValueId, FatalError> {
        let index = self.next_splice;
        self.next_splice += 1;
        let splices = self.splices;
        self.lowerer.lower_expr(&splices[index], self.env, self.steps)
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

    fn lower_variable(&mut self, name: &str) -> Quoted {
        let head = Quoted::Constant(GroundValue::Atom(name.to_string()).into());
        // Every variable this quote's own body writes is, by construction,
        // written inside this macro's quote. Its tail carries the macro's
        // `FunctionId` as an unstamped marker; the walk in `stamp_hygiene`
        // (quoted_expander.rs) rewrites it to `Var{context: Macro(fid, ordinal)}`
        // once this expansion's ordinal is known, right after the macro runs.
        let owner = i64::from(self.lowerer.owner.as_u32());
        let tail = Quoted::Constant(GroundValue::Int(owner).into());
        self.ast_node_of(head, tail)
    }

    fn lower_module(&mut self, module: &ModuleDenotation) -> ValueId {
        let (tag, paths) = module.quoted_parts();
        let mut identity = vec![LiteralTerm::from(GroundValue::Atom(tag.into()))];
        identity.extend(paths.map(|path| module_path(path.segments().iter())));
        let node = LiteralTerm::Tuple(vec![
            GroundValue::Atom("__aliases__".into()).into(),
            meta(Some(LiteralTerm::Tuple(identity)), None),
            module_path(module.display_segments()),
        ]);
        self.lowerer.push_literal(self.steps, node)
    }

    /// A call node whose head is display spelling and whose metadata retains
    /// the callable, when the call was classified here.
    fn lower_call_node(&mut self, spelling: &str, bound: Option<FunctionId>, args: Vec<Quoted>) -> Quoted {
        let head = Quoted::Constant(GroundValue::Atom(spelling.to_string()).into());
        let tail = self.list(args);
        self.tuple(vec![head, Quoted::Constant(meta(None, bound)), tail])
    }

    fn ast_node_of(&mut self, head: Quoted, tail: Quoted) -> Quoted {
        self.tuple(vec![head, Quoted::Constant(meta(None, None)), tail])
    }

    /// The step value that holds `quoted`.
    fn value(&mut self, quoted: Quoted) -> ValueId {
        match quoted {
            Quoted::Constant(term) => self.lowerer.push_literal(self.steps, term),
            Quoted::Built(value) => value,
        }
    }

    fn tuple(&mut self, items: Vec<Quoted>) -> Quoted {
        match all_constant(items) {
            Ok(terms) => Quoted::Constant(LiteralTerm::Tuple(terms)),
            Err(items) => {
                let items = items.into_iter().map(|item| self.value(item)).collect();
                let value = self.lowerer.fresh_value();
                self.steps.push(ExprStep::Tuple { value, items });
                Quoted::Built(value)
            }
        }
    }

    fn list(&mut self, items: Vec<Quoted>) -> Quoted {
        match all_constant(items) {
            Ok(terms) => Quoted::Constant(LiteralTerm::List(terms)),
            Err(items) => {
                let items = items.into_iter().map(|item| self.value(item)).collect();
                let value = self.lowerer.fresh_value();
                self.steps.push(ExprStep::List {
                    value,
                    items,
                    tail: None,
                });
                Quoted::Built(value)
            }
        }
    }
}

/// A quoted subtree: a constant when nothing in it is unquoted, and otherwise
/// the step value that builds it.
enum Quoted {
    Constant(LiteralTerm),
    Built(ValueId),
}

/// The terms of `items` when every one is a constant, and `items` back when
/// one of them is built.
fn all_constant(items: Vec<Quoted>) -> Result<Vec<LiteralTerm>, Vec<Quoted>> {
    if items.iter().any(|item| matches!(item, Quoted::Built(_))) {
        return Err(items);
    }
    Ok(items
        .into_iter()
        .map(|item| match item {
            Quoted::Constant(term) => term,
            Quoted::Built(_) => unreachable!("every item is a constant"),
        })
        .collect())
}

fn module_path<'s>(segments: impl Iterator<Item = &'s String>) -> LiteralTerm {
    LiteralTerm::List(
        segments
            .map(|segment| GroundValue::Atom(segment.clone()).into())
            .collect(),
    )
}

/// A node's metadata keyword list, in the order `QuotedSourceBuilder::meta`
/// writes it. A quoted node carries no span: it takes the span of the macro
/// call that expands it.
fn meta(module: Option<LiteralTerm>, bound: Option<FunctionId>) -> LiteralTerm {
    let entry = |key: &str, value| LiteralTerm::Tuple(vec![GroundValue::Atom(key.to_string()).into(), value]);
    let module = module.map(|identity| entry(super::super::source::META_MODULE_KEY, identity));
    let bound = bound.map(|function| {
        entry(
            super::super::source::META_BOUND_CALLABLE_KEY,
            GroundValue::Int(i64::from(function.as_u32())).into(),
        )
    });
    LiteralTerm::List(module.into_iter().chain(bound).collect())
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

    fn lower(
        &mut self,
        entry_plan: Rc<crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>>,
    ) -> Result<(LoweredBody, Vec<Output>, Vec<Changed>), FatalError> {
        let mut clause_defs = Vec::new();
        for (index, clause) in self.surface.clauses.iter().enumerate() {
            clause_defs.push(self.lower_clause(clause, &entry_plan, index as u32)?);
        }
        let body = self.plan_clauses(clause_defs, entry_plan);

        Ok((
            body,
            std::mem::take(&mut self.generated),
            std::mem::take(&mut self.generated_changed),
        ))
    }

    /// A clause takes the function's inputs, and a name its head binds to one
    /// of them is that input. The winning outcome of the entry plan hands it
    /// the value of every other name its head binds. The macro's caller and a
    /// lambda's captures arrive as leading inputs.
    fn lower_clause(
        &mut self,
        clause: &FnClause,
        entry_plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>,
        body_id: u32,
    ) -> Result<ExprClause, FatalError> {
        let input_count = usize::from(self.surface.is_macro) + self.source.capture_params.len() + clause.params.len();
        let params: Vec<ValueId> = (0..input_count).map(|_| self.fresh_value()).collect();
        let mut env = HashMap::default();
        let arguments = self.bind_outcome_arguments(
            entry_plan.outcome_of_body(body_id),
            |subject| entry_plan.subject_input(subject).map(|ordinal| params[ordinal]),
            &mut env,
        );
        let body = self.lower_expr_as_block(&clause.body, env)?;

        Ok(ExprClause {
            span: clause.span,
            params,
            arguments,
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
            Expr::Alias(alias) => Ok(self.lower_alias(alias, steps)),
            Expr::Module(module) => Ok(QuoteLowerer::new(self, env, steps, &[]).lower_module(module)),
            Expr::Var(name) => {
                if let Some(value) = env.get(name) {
                    return Ok(*value);
                }
                if name.name == crate::ast::STACKTRACE {
                    return Err(emit_job_diagnostic(
                        self.telemetry,
                        Diagnostic::error(codes::LOWER_UNBOUND, STACKTRACE_OUTSIDE_A_HANDLER_CLAUSE, expr.span),
                    ));
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
            Expr::List(..) | Expr::Tuple(_) | Expr::Map(_)
                if let Some(constant) = LiteralTerm::constant(&expr.node) =>
            {
                Ok(self.push_literal(steps, constant))
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
                self.lower_update_key_check(expr.span, ok, base, keys, steps)?;
                Ok(updated)
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
                let callee = direct_callee(target, args.len(), env);
                let module = match (&callee, module_value_callee(target)) {
                    (None, Some((module, function))) => Some((self.lower_expr(module, env, steps)?, function)),
                    _ => None,
                };
                let lowered_args = self.lower_call_args(args, env, steps)?;
                let callsite = self.fresh_callsite(expr.span);
                if let Some(callee) = callee {
                    let value = self.fresh_value();
                    let callee = self.resolve_callee(&callee, args.len(), target.span, "direct runtime callee")?;
                    steps.push(ExprStep::DirectCall {
                        value,
                        callsite,
                        callee: DirectCallee::Function(callee),
                        args: lowered_args,
                    });
                    return Ok(value);
                }
                if let Some((module, function)) = module {
                    let value = self.fresh_value();
                    steps.push(ExprStep::DirectCall {
                        value,
                        callsite,
                        callee: DirectCallee::ModuleValue {
                            module,
                            function: function.to_string(),
                        },
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
                        callee: DirectCallee::Function(self.resolve_direct_callee(name, 2, expr.span)?),
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
                            literal: GroundValue::Nil.into(),
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
                form,
            } => self.lower_try(
                expr.span,
                TrySections {
                    body,
                    rescue,
                    catch,
                    else_clauses,
                    after: after.as_deref(),
                    form: *form,
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
            NamespaceSymbol::Callable(function) => self.retained_export(function, span),
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

    /// The retained callee as its module exports it, asked the same way
    /// `resolve_module_callee` asks for a name.
    fn retained_export(&mut self, function: FunctionId, span: Span) -> Result<FunctionId, FatalError> {
        let reference = self.world.function_ref(function);
        let module = reference.module;
        let name = reference.name().to_string();
        let arity = reference.arity;
        let requester = self.interface_requester(span);
        self.world
            .module_public_function(module, &name, arity, requester)
            .map_err(|diagnostic| emit_job_diagnostic(self.telemetry, *diagnostic))
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
            None => self.resolve_runtime_function(&name.name, arity, span, context),
            Some(module) => self.resolve_module_callee(module, &name.name, arity, span),
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
        let requester = self.interface_requester(span);
        self.world
            .module_public_function(module, name, arity, requester)
            .map_err(|diagnostic| emit_job_diagnostic(self.telemetry, *diagnostic))
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
        let module_id = self.world.resolve_module_target(self.namespace, module);
        self.name_module_as_value(module_id);
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
            let value = match by_name.remove(field.as_str()) {
                Some(expr) => self.lower_expr(expr, env, steps)?,
                None => self.lower_omitted_struct_field(module_id, &field, span, steps)?,
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

    /// The value a struct literal gives a field it does not name: the
    /// field's declared default, or nil.
    fn lower_omitted_struct_field(
        &mut self,
        module: ModuleId,
        field: &str,
        span: Span,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let default = self
            .world
            .struct_def(module)
            .and_then(|def| def.defaults.get(field))
            .map(|default| default.expr(span));
        match default {
            Some(default) => self.lower_expr(&default, &mut HashMap::default(), steps),
            None => Ok(self.push_const(steps, GroundValue::Nil)),
        }
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

    fn lower_alias(&mut self, alias: &ModuleName, steps: &mut Vec<ExprStep>) -> ValueId {
        let module = self.world.resolve_module_name(self.namespace, alias);
        let atom = self
            .world
            .module_name(module)
            .expect("a resolved module name is a named module")
            .atom_name();
        self.name_module_as_value(module);
        self.push_const(steps, GroundValue::Atom(atom))
    }

    /// This body writes `module`'s name as a value, so a value can name it.
    fn name_module_as_value(&mut self, module: super::super::identity::ModuleId) {
        self.generated.push(FactKey::NameableModules);
        if self.world.note_nameable_module(module) {
            self.generated_changed.push(FactKey::NameableModules);
        }
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
    ///
    /// The check is a guard: code after it reads the update's own value, which
    /// the guard's passing arm proves is the updated map. The guard's result is
    /// only its verdict, so the raise on the miss arm never joins the map.
    fn lower_update_key_check(
        &mut self,
        span: Span,
        ok: ValueId,
        base: ValueId,
        keys: Vec<ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<(), FatalError> {
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
                    callee: DirectCallee::Function(callee),
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
                        result: ok,
                    },
                }],
                miss_block: Some(miss_block),
            }),
        });
        Ok(())
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
                let arguments = self.bind_outcome_arguments(&plan.outcomes[0], |_| None, &mut success_env);
                let success_block = self.lower_with_block(span, rest, body, else_clauses, success_env)?;
                let miss_block = Some(self.lower_with_fail_block(span, matched, else_clauses, &env)?);
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
        env: &HashMap<Var, ValueId>,
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
        env: &HashMap<Var, ValueId>,
    ) -> Result<ExprBlock, FatalError> {
        let plan = self.compile_match_dispatch(label, span, 1, match_rows(clauses), Some(last_resort))?;
        let mut steps = Vec::new();
        let bindings = self.lower_dispatch_bindings(&plan, env, &mut steps)?;
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
            form,
        } = sections;
        let Some(after) = after else {
            if rescue.is_empty() && catch.is_empty() {
                self.warn_try_else_only(span, form);
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

        let free = super::scope::free_names(&after.node);
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
    fn warn_try_else_only(&mut self, span: Span, form: TryForm) {
        let diagnostic = super::super::source_diagnostics::try_else_only_diagnostic(span, form);
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

        let (rows, clauses): (Vec<_>, Vec<_>) = self
            .handler_arms(rescue, catch)
            .into_iter()
            .map(|arm| (arm.row, arm.clause))
            .unzip();
        let plan = self.compile_match_dispatch(
            if catch.is_empty() { "rescue" } else { "catch" },
            span,
            params.len(),
            rows,
            Some(LastResort::reraise()),
        )?;
        let mut handler_steps = Vec::new();
        let bindings = self.lower_dispatch_bindings(&plan, env, &mut handler_steps)?;
        let free = super::scope::handler_free_names(rescue, catch);
        let captures = self.capture_values(free, env);
        let arm_blocks = plan
            .outcomes
            .iter()
            .map(|outcome| {
                let clause = clauses[outcome.body_id as usize];
                self.lower_handler_arm(outcome, clause, (rescue, catch), raised, env.clone())
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
        let block =
            self.lower_clause_dispatch_block("try else", span, value, else_clauses, LastResort::try_clause(), env)?;
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
            let bound = rescue
                .binding
                .as_ref()
                .map_or(Pattern::Wildcard, |binding| Pattern::Var(binding.node.clone()));
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
                let atom = self.world.module_alias_atom(self.namespace, &exception.node);
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
        let arguments = self.bind_outcome_arguments(outcome, |_| None, &mut env);
        let mut steps = Vec::new();
        let body = match arm {
            HandlerClause::Rescue { clause, wraps } => {
                let clause = &rescue[clause];
                if let (true, Some(binding)) = (wraps, &clause.binding) {
                    let wrapped = self.push_erlang_error(raised, &mut steps);
                    env.insert(binding.node.clone(), wrapped);
                }
                &clause.body
            }
            HandlerClause::Catch { clause } => &catch[clause].body,
        };
        self.bind_stacktrace_where_read(body, &mut env, &mut steps);
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

    /// `%ErlangError{original: raised}`, every field of the struct present:
    /// how a raised non-exception value presents itself to a rescue clause.
    fn push_erlang_error(&mut self, raised: ValueId, steps: &mut Vec<ExprStep>) -> ValueId {
        let module = self.push_const(steps, GroundValue::Atom(ERLANG_ERROR.to_string()));
        let flag = self.push_const(steps, GroundValue::Bool(true));
        let no_reason = self.push_const(steps, GroundValue::Nil);
        let entries = [
            ("__struct__", module),
            (fz_runtime::failure::EXCEPTION_FIELD, flag),
            ("original", raised),
            ("reason", no_reason),
        ]
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
        steps.push(ExprStep::Map { value, entries });
        value
    }

    /// `__STACKTRACE__` is a variable a rescue or catch clause binds. fz keeps
    /// no stacktraces, so the clause binds it to the empty list, and only when
    /// its body reads the name. A closure inside the clause captures it as it
    /// captures any other variable.
    fn bind_stacktrace_where_read(
        &mut self,
        body: &Spanned<Expr>,
        env: &mut HashMap<Var, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) {
        let stacktrace = Var::user(crate::ast::STACKTRACE);
        if !super::scope::free_names(&body.node).contains(&stacktrace) {
            return;
        }
        let value = self.fresh_value();
        steps.push(ExprStep::List {
            value,
            items: Vec::new(),
            tail: None,
        });
        env.insert(stacktrace, value);
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
        let arguments = self.bind_outcome_arguments(outcome, |_| None, &mut env);
        let block = self.lower_expr_as_block(&clause.body, env)?;
        Ok(ExprOutcome { arguments, block })
    }

    /// Binds each name an outcome's pattern binds. A name whose subject
    /// `input_of` finds is bound to that value as it stands; every other name
    /// is a fresh parameter, and the edge hands it the subject's value.
    fn bind_outcome_arguments(
        &mut self,
        outcome: &crate::dispatch_matrix::pattern::PatternDispatchOutcome,
        input_of: impl Fn(crate::dispatch_matrix::SubjectId) -> Option<ValueId>,
        env: &mut HashMap<Var, ValueId>,
    ) -> Box<[super::super::body::OutcomeArgument]> {
        let mut arguments = Vec::new();
        for binding in &outcome.bindings {
            if let Some(input) = input_of(binding.source) {
                env.insert(binding.name.clone(), input);
                continue;
            }
            let parameter = self.fresh_value();
            env.insert(binding.name.clone(), parameter);
            arguments.push(super::super::body::OutcomeArgument {
                subject: binding.source,
                parameter,
                role: super::super::body::ValueRole::Semantic,
            });
        }
        arguments.into_boxed_slice()
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
        let mut resolver = super::super::dispatch::SourcePatternResolver {
            world: self.world,
            namespace,
            guard: |world: &mut World, callee: &Callee, arity: usize| {
                let callee = resolve_guard_callee_checked(world, namespace, callee, arity);
                Ok(Some(world.guard_callee(callee)))
            },
        };
        let plan = pattern_dispatch_from_source_with_resolver(&source, &mut resolver)
            .map_err(|error| emit_local_dispatch_error(self.telemetry, label, span, error))?;
        if source.rows.len() > 1 {
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
        let literal = match key
            .as_dispatch_shape()
            .expect("materialize_dispatch_const only ever sees a dispatch-matrix const")
        {
            DispatchShape::Int(n) => GroundValue::Int(n),
            DispatchShape::Float(bits) => GroundValue::Float(bits),
            DispatchShape::Utf8Binary(bytes) => GroundValue::Binary(bytes.to_vec()),
            DispatchShape::Atom(name) => GroundValue::Atom(name.to_string()),
            DispatchShape::Bool(flag) => GroundValue::Bool(flag),
            DispatchShape::Nil => GroundValue::Nil,
        };
        Ok(self.push_const(steps, literal))
    }

    fn receive_capture_values(
        &mut self,
        clauses: &[MatchClause],
        after: Option<&AfterClause>,
        env: &HashMap<Var, ValueId>,
    ) -> Vec<ValueId> {
        let free =
            super::scope::receive_free_names(clauses, after.map(|after| (&after.timeout.node, &after.body.node)));
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
            extern_delivers: None,
            variadic: false,
            attrs: Vec::new(),
            span,
        };
        let mut capture_params = super::scope::lambda_free_names(clauses)
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

        steps.push(ExprStep::Lambda {
            value,
            function,
            captures,
        });
        Ok(value)
    }

    fn plan_clauses(
        &mut self,
        clauses: Vec<ExprClause>,
        entry_plan: Rc<crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>>,
    ) -> LoweredBody {
        let mut lowered = Vec::with_capacity(clauses.len());
        let mut entries = Vec::new();
        for clause in clauses {
            let params = clause.arguments.iter().map(|argument| argument.parameter).collect();
            let entry = self.plan_block(
                clause.body.into_pending(),
                ControlEntryOrigin::Clause,
                ControlDestination::Return,
                params,
                Vec::new(),
                &mut entries,
            );
            lowered.push(LoweredClause {
                span: clause.span,
                params: clause.params,
                arguments: clause.arguments,
                entry,
            });
        }
        let mut body = LoweredBody::clauses(lowered, entries, std::mem::take(&mut self.generated_ids))
            .with_entry_plan(entry_plan)
            .with_value_count(self.next_value as usize);
        drop_unread_outcome_arguments(&mut body);
        self.construct_entry_captures(&mut body);
        body
    }

    fn construct_entry_captures(&mut self, body: &mut LoweredBody) {
        use super::super::executable_facts::{TransportOrigin, collect_value_origins};
        use crate::fz_ir::RewritePermission;
        let scanned = Cell::new(0);
        let compared = Cell::new(0);
        let origins = collect_value_origins(body);
        let LoweredBody::Clauses { entries, .. } = &*body;
        let mut sources = Vec::new();
        let mut updates = Vec::new();
        for (entry, step, instruction) in scan_steps(entries, &scanned) {
            match instruction {
                LoweredStep::List {
                    items, tail: Some(_), ..
                } => {
                    let Some(&head) = items.first().filter(|_| items.len() == 1) else {
                        continue;
                    };
                    if let Some(origin) = list_source_origin(body, &origins, head) {
                        sources.push((entry, step, head, origin));
                    }
                }
                LoweredStep::MapUpdate { .. } => updates.push((entry, step)),
                _ => {}
            }
        }
        for (entry, step, head, origin) in &sources {
            let source = match origin {
                TransportOrigin::LocalValue(source) => *source,
                TransportOrigin::OutcomeSubject { owner, subject }
                    if let Some(input) = decision_input_value(body, *owner, *subject) =>
                {
                    input
                }
                TransportOrigin::OutcomeSubject { owner, subject } => {
                    let (target, existing) = body.decision_edge_of(*owner, *head, *subject);
                    if let Some(existing) = existing {
                        existing
                    } else {
                        let parameter = self.fresh_value();
                        let LoweredBody::Clauses {
                            entries, value_count, ..
                        } = body;
                        *value_count = self.next_value as usize;
                        entries[target.as_u32() as usize].params.push(parameter);
                        entries[target.as_u32() as usize].physical_params.push(parameter);
                        let arguments = body.decision_arguments_mut(*owner, target);
                        let mut handed = std::mem::take(arguments).into_vec();
                        handed.push(super::super::body::OutcomeArgument {
                            subject: *subject,
                            parameter,
                            role: super::super::body::ValueRole::Physical,
                        });
                        *arguments = handed.into_boxed_slice();
                        parameter
                    }
                }
                _ => unreachable!("a list source is a local value or a plan-owned subject"),
            };
            body.retain_list_source(
                ControlEntryId::from_u32(*entry as u32),
                *step,
                source,
                RewritePermission::RetainOnly,
            );
        }
        let value_count = body.value_count();
        let clause_bounds = clause_bounds(body);
        let LoweredBody::Clauses {
            clauses,
            entries,
            tables,
            ..
        } = body;
        let semantic = compute_entry_captures(entries, tables, &clause_bounds, value_count, false);
        let mut physical = compute_entry_captures(entries, tables, &clause_bounds, value_count, true);
        for entry in entries.iter() {
            let LoweredTail::Receive(receive) = &entry.tail else {
                continue;
            };
            let targets = receive
                .outcomes
                .iter()
                .map(|edge| edge.target)
                .chain(receive.after.iter().map(|after| after.entry));
            let mut shared = targets
                .clone()
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
        super::capture_owners::record_capture_owners(entries, clauses.iter().map(|clause| clause.entry));
        let origins = collect_value_origins(body);
        construct_call_ownership(body, &origins);
        construct_tuple_ownership(body, &origins, &scanned, &compared);
        let rebuilds = sources
            .into_iter()
            .map(|(entry, step, _, _)| (entry, step))
            .chain(updates);
        for (entry, step) in rebuilds {
            let permission = if can_rewrite(body, &origins, entry, step) {
                RewritePermission::Rewrite
            } else {
                RewritePermission::RetainOnly
            };
            body.set_rewrite_permission(ControlEntryId::from_u32(entry as u32), step, permission);
        }
        self.ownership_steps_scanned += scanned.get();
        self.ownership_pairs_compared += compared.get();
    }

    fn plan_block(
        &mut self,
        block: PendingBlock,
        origin: ControlEntryOrigin,
        dest: ControlDestination,
        params: Vec<ValueId>,
        captures: Vec<ValueId>,
        entries: &mut Vec<LoweredEntry>,
    ) -> ControlEntryId {
        let span = block.span;
        let (steps, tail) = self.plan_steps(block, dest, entries);
        let entry_id = ControlEntryId::from_u32(entries.len() as u32);
        entries.push(LoweredEntry {
            span,
            origin,
            params,
            captures,
            capture_owners: Vec::new(),
            physical_captures: Vec::new(),
            physical_params: Vec::new(),
            steps,
            tail,
        });
        entry_id
    }

    /// Where the value of a control step goes: out of the block when the step
    /// is the block's last and its result, otherwise into an entry that plans
    /// the rest of the block.
    ///
    /// `unplaced` are the constants the step does not read; the rest of the
    /// block places them.
    fn plan_continuation(
        &mut self,
        mut rest: PendingBlock,
        value: ValueId,
        dest: ControlDestination,
        unplaced: Unplaced,
        entries: &mut Vec<LoweredEntry>,
    ) -> ControlDestination {
        if rest.resumes_nothing_after(value) {
            debug_assert!(
                unplaced.0.is_empty(),
                "a call that resumes nothing has placed its constants"
            );
            return dest;
        }
        rest.unplaced = unplaced;
        let resume = self.plan_block(
            rest,
            ControlEntryOrigin::DeliveredResume { value },
            dest,
            Vec::new(),
            Vec::new(),
            entries,
        );
        ControlDestination::Deliver(resume)
    }

    fn plan_steps(
        &mut self,
        mut block: PendingBlock,
        dest: ControlDestination,
        entries: &mut Vec<LoweredEntry>,
    ) -> (Vec<LoweredStep>, LoweredTail) {
        let mut lowered = Vec::new();
        let mut unplaced = std::mem::take(&mut block.unplaced);
        while let Some(step) = block.steps.next() {
            match step {
                ExprStep::DirectCall {
                    value,
                    callsite,
                    callee,
                    args,
                } => {
                    let operands = callee
                        .module_value()
                        .into_iter()
                        .chain(args.iter().map(|arg| arg.value));
                    unplaced.place_before_call(&operands.collect::<Vec<_>>(), &block, value, &mut lowered);
                    let dest = self.plan_continuation(block, value, dest, unplaced, entries);
                    return (
                        lowered,
                        LoweredTail::DirectCall {
                            value,
                            callsite,
                            callee,
                            args,
                            dest,
                        },
                    );
                }
                ExprStep::ClosureCall {
                    value,
                    callsite,
                    callee,
                    args,
                } => {
                    let operands = std::iter::once(callee).chain(args.iter().map(|arg| arg.value));
                    unplaced.place_before_call(&operands.collect::<Vec<_>>(), &block, value, &mut lowered);
                    let dest = self.plan_continuation(block, value, dest, unplaced, entries);
                    return (
                        lowered,
                        LoweredTail::ClosureCall {
                            value,
                            callsite,
                            callee,
                            args,
                            dest,
                        },
                    );
                }
                ExprStep::If {
                    value,
                    cond,
                    then_block,
                    else_block,
                } => {
                    unplaced.place_all(&mut lowered);
                    let branch_dest = self.plan_continuation(block, value, dest, Unplaced::default(), entries);
                    let then_entry = self.plan_block(
                        then_block.into_pending(),
                        ControlEntryOrigin::Branch,
                        branch_dest.clone(),
                        Vec::new(),
                        Vec::new(),
                        entries,
                    );
                    let else_entry = self.plan_block(
                        else_block.into_pending(),
                        ControlEntryOrigin::Branch,
                        branch_dest,
                        Vec::new(),
                        Vec::new(),
                        entries,
                    );
                    return (
                        lowered,
                        LoweredTail::If {
                            cond,
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
                    let ExprDispatch {
                        plan,
                        arm_blocks,
                        miss_block,
                    } = *dispatch;
                    unplaced.place_all(&mut lowered);
                    let branch_dest = self.plan_continuation(block, value, dest, Unplaced::default(), entries);
                    let outcomes = arm_blocks
                        .into_iter()
                        .map(|arm| {
                            let params = arm.arguments.iter().map(|argument| argument.parameter).collect();
                            let target = self.plan_block(
                                arm.block.into_pending(),
                                ControlEntryOrigin::Branch,
                                branch_dest.clone(),
                                params,
                                Vec::new(),
                                entries,
                            );
                            super::super::body::OutcomeEdge {
                                target,
                                arguments: arm.arguments,
                            }
                        })
                        .collect::<Vec<_>>();
                    let miss_entry = miss_block.map(|miss_block| {
                        self.plan_block(
                            miss_block.into_pending(),
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
                            inputs,
                            bindings,
                            dispatch: Box::new(ControlDispatch::new(plan, outcomes, miss_entry)),
                        },
                    );
                }
                ExprStep::Receive(receive) => {
                    let ExprReceive {
                        value,
                        bindings,
                        dispatch,
                        outcomes,
                        after,
                        captures,
                    } = *receive;
                    unplaced.place_all(&mut lowered);
                    let branch_dest = self.plan_continuation(block, value, dest, Unplaced::default(), entries);
                    let receive_dest = branch_dest.clone();
                    let outcomes = outcomes
                        .into_iter()
                        .map(|outcome| {
                            let target = self.plan_block(
                                outcome.block.into_pending(),
                                ControlEntryOrigin::ReceiveOutcome,
                                branch_dest.clone(),
                                outcome.arguments.iter().map(|argument| argument.parameter).collect(),
                                captures.clone(),
                                entries,
                            );
                            super::super::body::OutcomeEdge {
                                arguments: outcome.arguments,
                                target,
                            }
                        })
                        .collect::<Vec<_>>();
                    let after = after.map(|after| {
                        let entry = self.plan_block(
                            after.body.into_pending(),
                            ControlEntryOrigin::ReceiveOutcome,
                            branch_dest,
                            Vec::new(),
                            captures,
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
                            bindings,
                            dispatch,
                            outcomes,
                            after,
                            dest: receive_dest,
                        })),
                    );
                }
                ExprStep::Try(try_step) => {
                    let ExprTry {
                        value,
                        body,
                        handler,
                        params,
                        captures,
                    } = *try_step;
                    unplaced.place_all(&mut lowered);
                    let branch_dest = self.plan_continuation(block, value, dest, Unplaced::default(), entries);
                    let body = self.plan_block(
                        body.into_pending(),
                        ControlEntryOrigin::Branch,
                        branch_dest.clone(),
                        Vec::new(),
                        Vec::new(),
                        entries,
                    );
                    let handler = self.plan_block(
                        handler.into_pending(),
                        ControlEntryOrigin::Handler,
                        branch_dest,
                        params,
                        captures,
                        entries,
                    );
                    return (lowered, LoweredTail::Try { body, handler });
                }
                ExprStep::Const {
                    value,
                    literal: literal @ LiteralTerm::Ground(_),
                } => unplaced.hold(value, literal),
                step => {
                    let step = lower_straight_step(step);
                    let mut operands = Vec::new();
                    step_used_values(&step, &mut operands);
                    unplaced.place_read_by(&operands, &mut lowered);
                    lowered.push(step);
                }
            }
        }
        unplaced.place_all(&mut lowered);
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
            bind_unasked_pattern(&pattern.node, value, env);
            return Ok(None);
        }
        let bindings = self.lower_dispatch_bindings(&plan, env, steps)?;
        let matched_value = ExprBlock {
            span: pattern.span,
            steps: Vec::new(),
            result: value,
        };
        let (arguments, block, decided) = match arm {
            MatchArm::Value => (
                self.bind_outcome_arguments(&plan.outcomes[0], |_| None, env),
                matched_value,
                None,
            ),
            MatchArm::Rest(span, rest) => {
                let mut arm_env = env.clone();
                let arguments = self.bind_outcome_arguments(&plan.outcomes[0], |_| None, &mut arm_env);
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

    fn push_const(&mut self, steps: &mut Vec<ExprStep>, literal: GroundValue) -> ValueId {
        self.push_literal(steps, literal.into())
    }

    fn push_literal(&mut self, steps: &mut Vec<ExprStep>, literal: LiteralTerm) -> ValueId {
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

/// Binds the names of a pattern that asks nothing: its dispatch is a
/// direct outcome, so every name is the matched value itself.
fn bind_unasked_pattern(pattern: &Pattern, source: ValueId, env: &mut HashMap<Var, ValueId>) {
    match pattern {
        Pattern::Wildcard
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil
        | Pattern::Pinned(_) => {}
        Pattern::Var(name) => {
            env.insert(name.clone(), source);
        }
        Pattern::Both(left, right) => {
            bind_unasked_pattern(&left.node, source, env);
            bind_unasked_pattern(&right.node, source, env);
        }
        Pattern::Tuple(_) | Pattern::List(..) | Pattern::Map(_) | Pattern::Struct { .. } | Pattern::Bitstring(_) => {
            unreachable!("a pattern that destructures asks a question; its dispatch is never a direct outcome")
        }
    }
}

fn lower_straight_step(step: ExprStep) -> LoweredStep {
    match step {
        ExprStep::Const { value, literal } => LoweredStep::Const { value, literal },
        ExprStep::Tuple { value, items } => LoweredStep::Tuple {
            value,
            items: items.into_iter().map(crate::fz_ir::OwnershipUse::share).collect(),
        },
        ExprStep::List { value, items, tail } => LoweredStep::List {
            value,
            items,
            tail,
            retention: None,
        },
        ExprStep::Map { value, entries } => LoweredStep::Map { value, entries },
        ExprStep::MapUpdate {
            value,
            ok,
            base,
            entries,
        } => LoweredStep::MapUpdate {
            value,
            ok,
            base,
            entries,
            rewrite: crate::fz_ir::RewritePermission::RetainOnly,
        },
        ExprStep::Struct { value, module, fields } => LoweredStep::Struct { value, module, fields },
        ExprStep::Bitstring { value, fields } => LoweredStep::Bitstring { value, fields },
        ExprStep::FunctionRef { value, function } => LoweredStep::FunctionRef { value, function },
        ExprStep::Lambda {
            value,
            function,
            captures,
        } => LoweredStep::Lambda {
            value,
            function,
            captures,
        },
        ExprStep::BinaryOp { value, op, left, right } => LoweredStep::BinaryOp { value, op, left, right },
        ExprStep::UnaryOp { value, op, input } => LoweredStep::UnaryOp { value, op, input },
        ExprStep::MapIndex { value, base, key } => LoweredStep::MapIndex { value, base, key },
        ExprStep::FieldAccess { value, base, field } => LoweredStep::FieldAccess { value, base, field },
        ExprStep::PopHandler => LoweredStep::PopHandler,
        ExprStep::DirectCall { .. }
        | ExprStep::ClosureCall { .. }
        | ExprStep::If { .. }
        | ExprStep::Dispatch { .. }
        | ExprStep::Receive(_)
        | ExprStep::Try(_) => {
            panic!("control steps should be lowered into tails before straight-line conversion")
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

/// The value a `case` decision was handed for `subject`, when `subject` is one
/// of its inputs: that value is the subject, and every arm still has it in
/// scope. A function's inputs are not in scope in its clauses, which see only
/// what the entry plan hands them.
fn decision_input_value(
    body: &LoweredBody,
    owner: SubjectOwner,
    subject: crate::dispatch_matrix::SubjectId,
) -> Option<ValueId> {
    if matches!(owner, SubjectOwner::Clause(_)) {
        return None;
    }
    match body.dispatch_subject_origin(owner, subject) {
        (SubjectOriginRoot::Value(input), path) if path.is_empty() => Some(input),
        _ => None,
    }
}

/// The values a clause binds before its entry runs: the clause parameters.
fn clause_bounds(body: &LoweredBody) -> HashMap<ControlEntryId, ValueSet> {
    let LoweredBody::Clauses { clauses, .. } = body;
    clauses
        .iter()
        .map(|clause| {
            let mut bound = ValueSet::for_values(body.value_count());
            bound.extend(clause.params.iter().copied());
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
    value_count: usize,
    physical: bool,
) -> Vec<Vec<ValueId>> {
    let mut memo = HashMap::default();
    for entry_id in 0..entries.len() {
        let entry_id = ControlEntryId::from_u32(entry_id as u32);
        record_entry_captures(
            entries,
            tables,
            clause_bounds,
            value_count,
            entry_id,
            physical,
            &mut memo,
        );
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
            let SubjectSource::Projection(projection) = body.decision_plan(*owner).subject(*subject) else {
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
        TransportOrigin::LocalValue(value) => (*value, SubjectPath::new()),
        TransportOrigin::Projection { source, kind } => (*source, SubjectPath::from_elem(kind, 1)),
        TransportOrigin::OutcomeSubject { owner, subject } => {
            let (source, path) = body.dispatch_subject_origin(*owner, *subject);
            match source {
                SubjectOriginRoot::Value(value) => (value, path),
                SubjectOriginRoot::MailboxMessage(_) => return Some((source, path.into_iter().cloned().collect())),
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
    path.extend(suffix.into_iter().cloned());
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

/// Whether the construction at `step` of `entry` may store into the source
/// it rebuilds -- a list step's retained cell, an update's base -- rather than
/// allocate. Nothing it stores may hold the source, and nothing that can run
/// after it may use the source. The runtime asks the other half, whether
/// anything outside this body holds it.
fn can_rewrite(
    body: &LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    entry: usize,
    step: usize,
) -> bool {
    use super::super::executable_facts::TransportOrigin;
    let LoweredBody::Clauses { entries, .. } = body;
    let (value, source, operands): (ValueId, ValueId, Vec<ValueId>) = match &entries[entry].steps[step] {
        LoweredStep::List {
            value,
            items,
            tail,
            retention: Some(retention),
        } => (*value, retention.source, items.iter().chain(tail).copied().collect()),
        LoweredStep::MapUpdate {
            value, base, entries, ..
        } => (
            *value,
            *base,
            entries.iter().flat_map(|(key, value)| [key.value, *value]).collect(),
        ),
        _ => return false,
    };
    let Some(source) = origin_source_path(body, origins, &TransportOrigin::LocalValue(source)) else {
        return false;
    };
    !operands
        .iter()
        .any(|operand| value_retains_source(body, origins, *operand, &source, Some(value)))
        && !source_used_after(body, origins, entry, step, &source)
}

/// Whether anything that can run after `step` of `entry` uses `source`. The
/// step's own result does not count, nor does an update's verdict `ok`, an
/// atom that holds nothing.
fn source_used_after(
    body: &LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    entry: usize,
    step: usize,
    source: &SourcePath,
) -> bool {
    let LoweredBody::Clauses { entries, .. } = body;
    let (exempt, verdict) = match entries[entry].steps.get(step) {
        Some(LoweredStep::List { value, .. } | LoweredStep::Tuple { value, .. }) => (Some(*value), None),
        Some(LoweredStep::MapUpdate { value, ok, .. }) => (Some(*value), Some(*ok)),
        _ => (None, None),
    };
    let missed = update_miss_entry(body, entry, step);
    any_later_ownership_use(body, entry, step, missed, |value, role| match role {
        super::super::body::ValueRole::Semantic => {
            Some(value) != verdict && value_retains_source(body, origins, value, source, exempt)
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

/// The entry an update at `step` of `entry` falls to when a key is missing.
///
/// An update that misses writes nothing, so its base reaches that entry
/// untouched: the base's uses there never see a rewrite.
fn update_miss_entry(body: &LoweredBody, entry: usize, step: usize) -> Option<ControlEntryId> {
    let LoweredBody::Clauses { entries, .. } = body;
    let block = &entries[entry];
    let LoweredStep::MapUpdate { ok, .. } = block.steps.get(step)? else {
        return None;
    };
    let is_last_step = step + 1 == block.steps.len();
    match &block.tail {
        LoweredTail::Dispatch { inputs, dispatch, .. } if is_last_step && inputs.as_slice() == [*ok] => {
            dispatch.miss_entry
        }
        _ => None,
    }
}

/// Whether any use that can still happen after `step` of `entry` competes for
/// ownership.
///
/// Later means later in this entry, or anywhere in the entries it reaches: a
/// reached entry runs in full, so its first step is as "later" as its last.
/// Both questions are answered from the body's use tables, so the walk costs
/// one visit per reachable entry and one per use it offers, never a search
/// through the body's steps. The uses of `unclaimed`, an entry that runs only
/// when the step gave up its claim, are not counted; the entries it reaches are.
fn any_later_ownership_use(
    body: &LoweredBody,
    entry: usize,
    step: usize,
    unclaimed: Option<ControlEntryId>,
    mut competes: impl FnMut(ValueId, super::super::body::ValueRole) -> bool,
) -> bool {
    use super::super::body::ValueRole;
    let LoweredBody::Clauses { entries, tables, .. } = body;
    let mut pending = vec![(ControlEntryId::from_u32(entry as u32), step as u32 + 1)];
    let mut visited = HashSet::default();
    while let Some((block_id, start)) = pending.pop() {
        if !visited.insert(block_id) {
            continue;
        }
        let block = &entries[block_id.as_u32() as usize];
        pending.extend(child_entries(&block.tail).map(|child| (child, 0)));
        if unclaimed == Some(block_id) {
            continue;
        }
        if tables
            .entry_retentions_from(block_id, start)
            .any(|source| competes(source, ValueRole::Physical))
        {
            return true;
        }
        let mut used = ValueSet::for_values(body.value_count());
        used.extend(tables.entry_uses_from(block_id, start));
        if used.iter().any(|value| competes(value, ValueRole::Semantic)) {
            return true;
        }
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

fn value_retains_source(
    body: &LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    value: ValueId,
    source: &SourcePath,
    exempt: Option<ValueId>,
) -> bool {
    let mut visiting = ValueSet::for_values(body.value_count());
    value_may_retain_source(body, origins, value, source, exempt, &mut visiting)
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
        visiting.unmark(value);
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
                        visiting.unmark(value);
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
    visiting.unmark(value);
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
    values_overlap_inner(body, origins, left, right, None, &mut HashSet::default())
}

/// The deliverers of `value` when it is a join of several: each a local
/// value or the call that delivers it.
fn join_deliverers(
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
    value: ValueId,
) -> Option<&[super::super::executable_facts::TransportOrigin]> {
    match origins.get(&value)? {
        super::super::executable_facts::TransportOrigin::Join(deliverers) => Some(deliverers),
        _ => None,
    }
}

/// The value a join receives from `deliverer`: the local value, or the result
/// of the delivering call.
fn delivered_value(body: &LoweredBody, deliverer: &super::super::executable_facts::TransportOrigin) -> Option<ValueId> {
    use super::super::executable_facts::TransportOrigin;
    match deliverer {
        TransportOrigin::LocalValue(value) => Some(*value),
        TransportOrigin::CallsiteReturn(callsite) | TransportOrigin::ClosureCallReturn { callsite, .. } => {
            match body.callsite_tail(*callsite)? {
                LoweredTail::DirectCall { value, .. } | LoweredTail::ClosureCall { value, .. } => Some(*value),
                _ => None,
            }
        }
        _ => None,
    }
}

fn values_overlap_inner(
    body: &LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
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
    if let Some(deliverers) = join_deliverers(origins, left) {
        return deliverers.iter().any(|deliverer| {
            delivered_value(body, deliverer)
                .is_none_or(|left| values_overlap_inner(body, origins, left, right, exempt, visited))
        });
    }
    if let Some(deliverers) = join_deliverers(origins, right) {
        return deliverers.iter().any(|deliverer| {
            delivered_value(body, deliverer)
                .is_none_or(|right| values_overlap_inner(body, origins, left, right, exempt, visited))
        });
    }
    let Some(left_path) = origin_source_path(body, origins, &TransportOrigin::LocalValue(left)) else {
        return true;
    };
    let Some(right_path) = origin_source_path(body, origins, &TransportOrigin::LocalValue(right)) else {
        return true;
    };
    value_retains_source(body, origins, left, &right_path, exempt)
        || value_retains_source(body, origins, right, &left_path, exempt)
        || construction_children(body, origins, left)
            .iter()
            .any(|&child| values_overlap_inner(body, origins, child, right, exempt, visited))
        || construction_children(body, origins, right)
            .iter()
            .any(|&child| values_overlap_inner(body, origins, left, child, exempt, visited))
}

fn construction_children<'a>(
    body: &'a LoweredBody,
    origins: &'a ValueMap<super::super::executable_facts::TransportOrigin>,
    value: ValueId,
) -> Cow<'a, [ValueId]> {
    use super::super::executable_facts::TransportOrigin;
    use crate::dispatch_matrix::ProjectionKind;
    let Some((value, path)) = origin_source_path(body, origins, &TransportOrigin::LocalValue(value)) else {
        return Cow::Borrowed(&[]);
    };
    let SubjectOriginRoot::Value(value) = value else {
        return Cow::Borrowed(&[]);
    };
    if path.is_empty() {
        match origins.get(&value) {
            Some(TransportOrigin::TupleValue(items)) => return Cow::Borrowed(items),
            Some(TransportOrigin::CallableValue(producer)) => return Cow::Borrowed(&producer.captures),
            _ => {}
        }
    }
    let owned = match body.value_definition(value) {
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
    };
    Cow::Owned(owned)
}

fn construct_call_ownership(
    body: &mut LoweredBody,
    origins: &ValueMap<super::super::executable_facts::TransportOrigin>,
) {
    use super::super::executable_facts::TransportOrigin;
    use crate::fz_ir::OwnershipMode;
    let LoweredBody::Clauses { entries, .. } = &*body;
    let entry_count = entries.len();
    for index in 0..entry_count {
        let LoweredBody::Clauses { entries, .. } = &*body;
        let (args, dest) = match &entries[index].tail {
            LoweredTail::DirectCall { args, dest, .. } | LoweredTail::ClosureCall { args, dest, .. } => (args, dest),
            _ => continue,
        };
        let modes = args
            .iter()
            .enumerate()
            .map(|(arg_index, arg)| {
                let arg = arg.value;
                let peers_overlap = args.iter().enumerate().any(|(peer_index, peer)| {
                    arg_index != peer_index && values_overlap(body, origins, arg, peer.value)
                });
                let retained_overlap = if let ControlDestination::Deliver(target) = dest {
                    let target = &entries[target.as_u32() as usize];
                    target
                        .captures
                        .iter()
                        .any(|capture| values_overlap(body, origins, arg, *capture))
                        || target.physical_captures.iter().any(|capture| {
                            if let Some(deliverers) = join_deliverers(origins, *capture) {
                                return deliverers.iter().any(|deliverer| {
                                    delivered_value(body, deliverer)
                                        .and_then(|value| {
                                            origin_source_path(body, origins, &TransportOrigin::LocalValue(value))
                                        })
                                        .is_none_or(|source| value_retains_source(body, origins, arg, &source, None))
                                });
                            }
                            let Some(source) =
                                origin_source_path(body, origins, &TransportOrigin::LocalValue(*capture))
                            else {
                                return true;
                            };
                            value_retains_source(body, origins, arg, &source, None)
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
        let LoweredBody::Clauses { entries, .. } = &mut *body;
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
    let LoweredBody::Clauses { entries, .. } = &*body;
    let tuples = scan_steps(entries, scanned)
        .filter_map(|(entry, step, instruction)| {
            matches!(instruction, LoweredStep::Tuple { .. }).then_some((entry, step))
        })
        .collect::<Vec<_>>();
    let index = StorageRootIndex::new(body, origins);
    let mut reached = (usize::MAX, HashSet::default());
    for (entry, step) in tuples {
        let LoweredBody::Clauses { entries, .. } = &*body;
        let LoweredStep::Tuple { value: result, items } = &entries[entry].steps[step] else {
            unreachable!()
        };
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
                    .any(|(peer, other)| position != peer && values_overlap(body, origins, item.value, other.value));
                let shares = peers_overlap
                    || tuple_item_has_old_owner(body, origins, &index, &later, *result, item.value, compared);
                if shares {
                    OwnershipMode::Share
                } else {
                    OwnershipMode::Transfer
                }
            })
            .collect::<Vec<_>>();
        let LoweredBody::Clauses { entries, .. } = &mut *body;
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
        values_overlap_inner(body, origins, value, item, Some(result), &mut HashSet::default())
    };
    let retains = |value: ValueId| {
        origin_source_path(
            body,
            origins,
            &super::super::executable_facts::TransportOrigin::LocalValue(value),
        )
        .is_none_or(|source| value_retains_source(body, origins, item, &source, Some(result)))
    };
    let Some(competitors) = index.competitors_after(item, later) else {
        return any_later_ownership_use(body, later.entry(), later.step(), None, |value, role| match role {
            ValueRole::Semantic => overlaps(value),
            ValueRole::Physical => retains(value),
        });
    };
    later.retained_sources(body).any(retains) || competitors.into_iter().any(overlaps)
}

/// Records in `memo` the values `entry_id` and the entries below it read
/// without defining, in value order.
fn record_entry_captures(
    entries: &[LoweredEntry],
    tables: &BodyTables,
    clause_bounds: &HashMap<ControlEntryId, ValueSet>,
    value_count: usize,
    entry_id: ControlEntryId,
    physical: bool,
    memo: &mut HashMap<ControlEntryId, Vec<ValueId>>,
) {
    if memo.contains_key(&entry_id) {
        return;
    }

    let entry = &entries[entry_id.as_u32() as usize];
    let mut needed = ValueSet::for_values(value_count);
    if physical {
        needed.extend(tables.entry_retentions_from(entry_id, 0));
    } else {
        needed.extend(tables.entry_uses_from(entry_id, 0));
    }
    for child in child_entries(&entry.tail) {
        record_entry_captures(entries, tables, clause_bounds, value_count, child, physical, memo);
        needed.extend(memo[&child].iter().copied());
    }
    if let Some(bound) = clause_bounds.get(&entry_id) {
        needed.subtract(bound);
    }
    let defined_here = entry
        .params
        .iter()
        .copied()
        .chain(entry.origin.input_value())
        .chain(tables.entry_defines(entry_id));
    for value in defined_here {
        needed.unmark(value);
    }
    let mut ordered = needed.iter().collect::<Vec<_>>();
    for capture in &entry.captures {
        if !ordered.contains(capture) {
            ordered.push(*capture);
        }
    }
    ordered.sort_by_key(|value| value.as_u32());
    memo.insert(entry_id, ordered);
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
    let mut retained = ValueSet::for_values(body.value_count());
    for clause in clauses {
        retained.extend(clause.params.iter().copied());
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

/// An outcome edge carries only what its target reads. A binding nothing in
/// the arm reads (`_x`, or a name only a guard reads, which the dispatch plan
/// reads from its subject itself) is dropped from the edge and from the
/// target's parameters, so it is neither extracted nor handed over. A receive
/// would otherwise box it into the park record's out-slot.
///
/// A function clause is an arm of the function's entry plan, and its
/// arguments are pruned the same way. Its parameters, the function's inputs,
/// are its calling convention and belong to no edge.
fn drop_unread_outcome_arguments(body: &mut LoweredBody) {
    use super::super::body::ValueRole;
    let LoweredBody::Clauses {
        clauses,
        entries,
        tables,
        ..
    } = body;
    let unread_in = |entries: &[LoweredEntry], target: ControlEntryId, arguments: &[OutcomeArgument]| {
        let read = values_read_from(entries, tables, target);
        arguments
            .iter()
            .filter(|argument| argument.role == ValueRole::Semantic && !read.contains(&argument.parameter))
            .map(|argument| argument.parameter)
            .collect::<HashSet<_>>()
    };
    let mut unread = Vec::new();
    for (owner, entry) in entries.iter().enumerate() {
        for (index, edge) in entry.tail.outcome_edges().iter().enumerate() {
            unread.extend(
                unread_in(entries, edge.target, &edge.arguments)
                    .into_iter()
                    .map(|parameter| (owner, index, parameter)),
            );
        }
    }
    let unread_by_clause = clauses
        .iter()
        .map(|clause| unread_in(entries, clause.entry, &clause.arguments))
        .collect::<Vec<_>>();
    for (owner, index, parameter) in unread {
        let edge = &mut entries[owner].tail.outcome_edges_mut()[index];
        let target = edge.target.as_u32() as usize;
        edge.arguments = std::mem::take(&mut edge.arguments)
            .into_iter()
            .filter(|argument| argument.parameter != parameter)
            .collect();
        entries[target].params.retain(|param| *param != parameter);
    }
    for (clause, unread) in clauses.iter_mut().zip(unread_by_clause) {
        clause.arguments = std::mem::take(&mut clause.arguments)
            .into_iter()
            .filter(|argument| !unread.contains(&argument.parameter))
            .collect();
        entries[clause.entry.as_u32() as usize]
            .params
            .retain(|param| !unread.contains(param));
    }
}

/// The values read by `entry` or by any entry it can reach.
fn values_read_from(
    entries: &[LoweredEntry],
    tables: &super::super::body::BodyTables,
    entry: ControlEntryId,
) -> HashSet<ValueId> {
    let mut read = HashSet::default();
    let mut visited = HashSet::default();
    let mut pending = vec![entry];
    while let Some(entry) = pending.pop() {
        if !visited.insert(entry) {
            continue;
        }
        read.extend(tables.entry_uses_from(entry, 0));
        pending.extend(child_entries(&entries[entry.as_u32() as usize].tail));
    }
    read
}

pub(super) fn child_entries(tail: &LoweredTail) -> impl Iterator<Item = ControlEntryId> + '_ {
    let beside_the_outcomes = match tail {
        LoweredTail::Value { dest, .. }
        | LoweredTail::DirectCall { dest, .. }
        | LoweredTail::ClosureCall { dest, .. } => match dest {
            ControlDestination::Return => [None, None],
            ControlDestination::Deliver(entry) => [Some(*entry), None],
        },
        LoweredTail::If {
            then_entry, else_entry, ..
        } => [Some(*then_entry), Some(*else_entry)],
        LoweredTail::Dispatch { dispatch, .. } => [dispatch.miss_entry, None],
        LoweredTail::Receive(receive) => [receive.after.as_ref().map(|after| after.entry), None],
        LoweredTail::Try { body, handler } => [Some(*body), Some(*handler)],
        LoweredTail::Unreachable => [None, None],
    };
    tail.outcome_edges()
        .iter()
        .map(|edge| edge.target)
        .chain(beside_the_outcomes.into_iter().flatten())
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
                format!("compiler2 {label} patterns require a map key to be a literal or a pinned variable"),
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

/// The module expression and function name of a call on a module value:
/// `m.f(a)`, where `m` is any expression that is not a module name.
fn module_value_callee(target: &Spanned<Expr>) -> Option<(&Spanned<Expr>, &str)> {
    let Expr::Index(module, function) = &target.node else {
        return None;
    };
    let Expr::Atom(function) = &function.node else {
        return None;
    };
    Some((module, function))
}

fn direct_callee(expr: &Spanned<Expr>, arity: usize, env: &HashMap<Var, ValueId>) -> Option<Callee> {
    if matches!(expr.node, Expr::Var(_)) {
        return Callee::for_call(&expr.node, arity);
    }
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
