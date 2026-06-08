//! Compiler2 body-lowering jobs and helpers.
//!
//! This module lowers one defined function at a time into Compiler2's
//! structured body form. It owns the local lowering algorithm, lambda capture
//! discovery, and generated-function definition path.

use std::collections::{HashMap, HashSet};

use crate::ast::{
    AfterClause, BitField, BitSize, Expr, FnClause, FnDef, LambdaClause, MatchClause, Pattern, Spanned, WithBinding,
};
use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{
    PatternBodyId, PatternDispatchError, PatternGuardExpr, PatternRow, SourcePatternError, SourcePatternRows,
    pattern_dispatch_from_source, pattern_dispatch_from_source_with_guard_resolver,
};
use crate::ir_lower::{extern_symbol_from_name, lower_extern_signature};

use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, ControlEntryOrigin, DirectCallee,
    DispatchBindings, Literal, LoweredBitField, LoweredBitFieldSpec, LoweredBitSize, LoweredBody, LoweredClause,
    LoweredEntry, LoweredExtern, LoweredStep, LoweredTail, ReceiveAfter, ReceiveClause, ValueId,
};
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::facts::FactValue;
use super::super::identity::{FunctionDef, FunctionId};
use super::super::namespace::{Namespace, NamespaceSymbol};
use super::super::scheduler::FatalError;
use super::super::world::World;
use super::dispatch::{collect_guard_calls_in_expr, resolve_guard_callee, resolve_guard_callee_checked};

type Output = (FactKey, FactValue);

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
    arm_blocks: Vec<ExprBlock>,
    miss_block: ExprBlock,
}

#[derive(Debug, Clone)]
struct ExprReceiveClause {
    span: Span,
    bound_names: Vec<String>,
    params: Vec<ValueId>,
    body: ExprBlock,
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
    clauses: Vec<ExprReceiveClause>,
    after: Option<ExprReceiveAfter>,
    captures: Vec<ValueId>,
}

#[derive(Debug, Clone)]
enum ExprStep {
    Const {
        value: ValueId,
        literal: Literal,
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
        entries: Vec<(ValueId, ValueId)>,
    },
    MapUpdate {
        value: ValueId,
        base: ValueId,
        entries: Vec<(ValueId, ValueId)>,
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
    NamedFunctionRef {
        value: ValueId,
        name: String,
        arity: usize,
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
        key: ValueId,
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
        literal: Literal,
    },
    AssertStruct {
        source: ValueId,
        module: super::super::identity::ModuleId,
    },
    RequireMapValue {
        value: ValueId,
        source: ValueId,
        key: Literal,
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
pub(super) fn lower_function(world: &mut World<'_>, function: FunctionId) -> Result<JobEffects, FatalError> {
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };
    let def = world.function_definition(function);
    if def.ast.is_macro {
        return Err(emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 cannot lower macro `{}` as a runtime body", def.ast.name),
                def.ast.span,
            ),
        ));
    }

    let mut reads = vec![FactKey::FunctionDefined(function)];
    let mut waits = HashSet::new();
    let mut follow_up = HashSet::new();
    for clause in &def.ast.clauses {
        if let Some(guard) = &clause.guard {
            collect_local_dispatch_requirements(world, def.namespace, guard, &mut reads, &mut waits, &mut follow_up)?;
        }
        collect_local_dispatch_requirements(
            world,
            def.namespace,
            &clause.body,
            &mut reads,
            &mut waits,
            &mut follow_up,
        )?;
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads,
            waits: waits.into_iter().collect(),
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    let mut lowerer = Lowerer::new(world, function, &def);
    let (body, mut outputs) = lowerer.lower()?;
    let revision = lowerer.world.define_lowered_body(function, body);
    outputs.push((FactKey::LoweredBody(function), FactValue::presence(revision)));
    Ok(JobEffects {
        reads,
        outputs,
        ..JobEffects::default()
    })
}

fn collect_local_dispatch_requirements(
    world: &mut World<'_>,
    namespace: Namespace,
    expr: &Spanned<Expr>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(), FatalError> {
    match &expr.node {
        Expr::Case(subject, clauses) => {
            if let Some(subject) = subject {
                collect_local_dispatch_requirements(world, namespace, subject, reads, waits, follow_up)?;
            }
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_local_guard_requirements(world, namespace, guard, reads, waits, follow_up)?;
                }
                collect_local_dispatch_requirements(world, namespace, &clause.body, reads, waits, follow_up)?;
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for binding in bindings {
                match binding {
                    WithBinding::Match(_, expr) | WithBinding::Bare(expr) => {
                        collect_local_dispatch_requirements(world, namespace, expr, reads, waits, follow_up)?;
                    }
                }
            }
            collect_local_dispatch_requirements(world, namespace, body, reads, waits, follow_up)?;
            for clause in else_clauses {
                if let Some(guard) = &clause.guard {
                    collect_local_guard_requirements(world, namespace, guard, reads, waits, follow_up)?;
                }
                collect_local_dispatch_requirements(world, namespace, &clause.body, reads, waits, follow_up)?;
            }
        }
        Expr::If(cond, then_expr, else_expr) => {
            collect_local_dispatch_requirements(world, namespace, cond, reads, waits, follow_up)?;
            collect_local_dispatch_requirements(world, namespace, then_expr, reads, waits, follow_up)?;
            if let Some(else_expr) = else_expr {
                collect_local_dispatch_requirements(world, namespace, else_expr, reads, waits, follow_up)?;
            }
        }
        Expr::Cond(arms) => {
            for (cond, body) in arms {
                collect_local_dispatch_requirements(world, namespace, cond, reads, waits, follow_up)?;
                collect_local_dispatch_requirements(world, namespace, body, reads, waits, follow_up)?;
            }
        }
        Expr::Receive { clauses, after } => {
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_local_guard_requirements(world, namespace, guard, reads, waits, follow_up)?;
                }
                collect_local_dispatch_requirements(world, namespace, &clause.body, reads, waits, follow_up)?;
            }
            if let Some(after) = after {
                collect_local_dispatch_requirements(world, namespace, &after.timeout, reads, waits, follow_up)?;
                collect_local_dispatch_requirements(world, namespace, &after.body, reads, waits, follow_up)?;
            }
        }
        Expr::Match(_, rhs)
        | Expr::Ascribe(rhs, _)
        | Expr::UnOp(_, rhs)
        | Expr::Capture(rhs)
        | Expr::Quote(rhs)
        | Expr::Unquote(rhs) => {
            collect_local_dispatch_requirements(world, namespace, rhs, reads, waits, follow_up)?;
        }
        Expr::BinOp(_, left, right) | Expr::Index(left, right) => {
            collect_local_dispatch_requirements(world, namespace, left, reads, waits, follow_up)?;
            collect_local_dispatch_requirements(world, namespace, right, reads, waits, follow_up)?;
        }
        Expr::Call(target, args) | Expr::ClosureCall(target, args) => {
            collect_local_dispatch_requirements(world, namespace, target, reads, waits, follow_up)?;
            for arg in args {
                collect_local_dispatch_requirements(world, namespace, arg, reads, waits, follow_up)?;
            }
        }
        Expr::List(items, tail) => {
            for item in items {
                collect_local_dispatch_requirements(world, namespace, item, reads, waits, follow_up)?;
            }
            if let Some(tail) = tail {
                collect_local_dispatch_requirements(world, namespace, tail, reads, waits, follow_up)?;
            }
        }
        Expr::Tuple(items) => {
            for item in items {
                collect_local_dispatch_requirements(world, namespace, item, reads, waits, follow_up)?;
            }
        }
        Expr::Bitstring(fields) => {
            for field in fields {
                collect_local_dispatch_requirements(world, namespace, &field.value, reads, waits, follow_up)?;
            }
        }
        Expr::Map(entries) | Expr::MapUpdate(_, entries) => {
            if let Expr::MapUpdate(base, _) = &expr.node {
                collect_local_dispatch_requirements(world, namespace, base, reads, waits, follow_up)?;
            }
            for (key, value) in entries {
                collect_local_dispatch_requirements(world, namespace, key, reads, waits, follow_up)?;
                collect_local_dispatch_requirements(world, namespace, value, reads, waits, follow_up)?;
            }
        }
        Expr::Struct { fields, .. } => {
            for (_, value) in fields {
                collect_local_dispatch_requirements(world, namespace, value, reads, waits, follow_up)?;
            }
        }
        Expr::Block(exprs) => {
            for expr in exprs {
                collect_local_dispatch_requirements(world, namespace, expr, reads, waits, follow_up)?;
            }
        }
        Expr::Lambda(_) => {}
        Expr::CaptureArg(_)
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

fn collect_local_guard_requirements(
    world: &mut World<'_>,
    namespace: Namespace,
    guard: &Spanned<Expr>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(), FatalError> {
    let mut calls = Vec::new();
    collect_guard_calls_in_expr(guard, &mut calls).map_err(|span| {
        emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                "compiler2 case/with guards must be dispatch-pure".to_string(),
                span,
            ),
        )
    })?;
    for call in calls {
        let callee = resolve_guard_callee(world, namespace, &call)?;
        let fact = FactKey::GuardDispatch(callee);
        if world.fact_revision(fact.clone()).is_some() {
            reads.push(fact);
        } else {
            waits.insert(fact);
            follow_up.insert(Job::ReifyGuardDispatch(callee));
        }
    }
    Ok(())
}

struct Lowerer<'w, 'tel> {
    world: &'w mut World<'tel>,
    owner: FunctionId,
    namespace: Namespace,
    def: FunctionDef,
    next_value: u32,
    next_callsite: u32,
    generated: Vec<Output>,
    generated_ids: Vec<FunctionId>,
}

impl<'w, 'tel> Lowerer<'w, 'tel> {
    fn new(world: &'w mut World<'tel>, owner: FunctionId, def: &FunctionDef) -> Self {
        Self {
            world,
            owner,
            namespace: def.namespace,
            def: def.clone(),
            next_value: 0,
            next_callsite: 0,
            generated: Vec::new(),
            generated_ids: Vec::new(),
        }
    }

    fn lower(&mut self) -> Result<(LoweredBody, Vec<Output>), FatalError> {
        if let Some(abi) = self.def.ast.extern_abi.clone() {
            let type_env = self.world.function_type_env(self.owner).map_err(|error| {
                emit_job_diagnostic(
                    self.world,
                    Diagnostic::error(
                        codes::RESOLVE_TYPE_ALIAS,
                        format!(
                            "compiler2 could not resolve extern return type for `{}`: {}",
                            self.def.ast.name, error.msg
                        ),
                        error.span,
                    ),
                )
            })?;
            let signature =
                lower_extern_signature(self.world.types_mut(), &self.def.ast, &type_env).map_err(|error| {
                    emit_job_diagnostic(
                        self.world,
                        Diagnostic::error(codes::LOWER_UNSUPPORTED, error.to_string(), self.def.ast.name_span),
                    )
                })?;
            return Ok((
                LoweredBody::Extern {
                    signature: LoweredExtern {
                        abi,
                        symbol: extern_symbol_from_name(&self.def.ast.name).to_string(),
                        params: signature.params,
                        variadic: self.def.ast.variadic,
                        ret: signature.ret,
                        return_ty: signature.return_ty,
                        semantic_contract: signature.semantic_contract,
                    },
                },
                Vec::new(),
            ));
        }

        let mut clause_defs = Vec::new();
        for clause in self.def.ast.clauses.clone() {
            clause_defs.push(self.lower_clause(&clause)?);
        }
        let (clauses, entries) = self.plan_clauses(clause_defs);

        Ok((
            LoweredBody::Clauses {
                clauses,
                entries,
                generated: self.generated_ids.clone(),
            },
            std::mem::take(&mut self.generated),
        ))
    }

    fn lower_clause(&mut self, clause: &FnClause) -> Result<ExprClause, FatalError> {
        let mut env = HashMap::new();
        let mut projections = Vec::new();
        let mut params = Vec::new();
        for capture in self.def.capture_params.clone() {
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
            Expr::Int(value) => Ok(self.push_const(steps, Literal::Int(*value))),
            Expr::Float(value) => Ok(self.push_const(steps, Literal::Float(*value))),
            Expr::Binary(value) => Ok(self.push_const(steps, Literal::Binary(value.clone()))),
            Expr::Atom(value) => Ok(self.push_const(steps, Literal::Atom(value.clone()))),
            Expr::Bool(value) => Ok(self.push_const(steps, Literal::Bool(*value))),
            Expr::Nil => Ok(self.push_const(steps, Literal::Nil)),
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
                    Some(NamespaceSymbol::Macro(_)) => Err(emit_job_diagnostic(
                        self.world,
                        Diagnostic::error(
                            codes::LOWER_UNSUPPORTED,
                            format!("compiler2 lowering expected expanded macro-free value `{name}`"),
                            expr.span,
                        ),
                    )),
                    Some(NamespaceSymbol::Module(_)) | None => Err(emit_job_diagnostic(
                        self.world,
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
                match self.world.lookup_callable_namespace(self.namespace, name, *arity) {
                    Some(NamespaceSymbol::Function(function)) => {
                        steps.push(ExprStep::FunctionRef { value, function });
                    }
                    Some(NamespaceSymbol::Macro(_)) => {
                        return Err(emit_job_diagnostic(
                            self.world,
                            Diagnostic::error(
                                codes::LOWER_UNSUPPORTED,
                                format!("compiler2 lowering expected expanded macro-free fn ref `{name}/{arity}`"),
                                expr.span,
                            ),
                        ));
                    }
                    Some(NamespaceSymbol::Module(_)) | None => {
                        steps.push(ExprStep::NamedFunctionRef {
                            value,
                            name: name.clone(),
                            arity: *arity,
                        });
                    }
                }
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
                    lowered.push((self.lower_expr(key, env, steps)?, self.lower_expr(value, env, steps)?));
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
                    lowered.push((self.lower_expr(key, env, steps)?, self.lower_expr(value, env, steps)?));
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
                    let key = self.lower_expr(key, env, steps)?;
                    steps.push(ExprStep::MapIndex { value, base, key });
                }
                Ok(value)
            }
            Expr::Call(target, args) => {
                let lowered_args = self.lower_call_args(args, env, steps)?;
                let callsite = self.fresh_callsite();
                if let Some(name) = direct_call_name(target, env) {
                    let value = self.fresh_value();
                    steps.push(ExprStep::DirectCall {
                        value,
                        callsite,
                        callee: self.resolve_direct_callee(&name, args.len(), target.span)?,
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
                    callsite: self.fresh_callsite(),
                    callee,
                    args: lowered_args,
                });
                Ok(value)
            }
            Expr::BinOp(op, left, right) => {
                let left = self.lower_expr(left, env, steps)?;
                let right = self.lower_expr(right, env, steps)?;
                let value = self.fresh_value();
                steps.push(ExprStep::BinaryOp {
                    value,
                    op: *op,
                    left,
                    right,
                });
                Ok(value)
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
                    return Ok(self.push_const(steps, Literal::Nil));
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
                            literal: Literal::Nil,
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
                self.world,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    "compiler2 lowering expected headless case to be expanded by the pipe desugar".to_string(),
                    expr.span,
                ),
            )),
            Expr::Cond(arms) => self.lower_cond(expr.span, arms, env, steps),
            Expr::With(bindings, body, else_clauses) => {
                self.lower_with(expr.span, bindings, body, else_clauses, env, steps)
            }
            Expr::Receive { clauses, after } => self.lower_receive(expr.span, clauses, after.as_deref(), env, steps),
            Expr::Lambda(clauses) => self.lower_lambda(expr.span, clauses, env, steps),
            Expr::Capture(_) | Expr::CaptureArg(_) | Expr::Quote(_) | Expr::Unquote(_) => Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("compiler2 does not lower `{}` yet", expr_name(&expr.node)),
                    expr.span,
                ),
            )),
        }
    }

    fn resolve_direct_callee(&mut self, name: &str, arity: usize, span: Span) -> Result<DirectCallee, FatalError> {
        Ok(
            match self.world.lookup_callable_namespace(self.namespace, name, arity) {
                Some(NamespaceSymbol::Function(function)) => DirectCallee::Function(function),
                Some(NamespaceSymbol::Macro(_)) => {
                    return Err(emit_job_diagnostic(
                        self.world,
                        Diagnostic::error(
                            codes::LOWER_UNSUPPORTED,
                            format!("compiler2 lowering expected expanded macro-free call `{name}/{arity}`"),
                            span,
                        ),
                    ));
                }
                Some(NamespaceSymbol::Module(_)) => DirectCallee::Named {
                    name: name.to_string(),
                    arity,
                },
                None => {
                    if let Some(fixed_arity) = self.world.min_variadic_arity(self.namespace, name)
                        && arity < fixed_arity
                    {
                        return Err(emit_job_diagnostic(
                            self.world,
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
                    DirectCallee::Named {
                        name: name.to_string(),
                        arity,
                    }
                }
            },
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
            });
        }
        Ok(lowered)
    }

    fn lower_struct_expr(
        &mut self,
        span: Span,
        module: &crate::modules::identity::ModuleName,
        fields: &[(String, Spanned<Expr>)],
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let module_id = self.resolve_struct_module(module, span)?;
        let Some(order) = self.world.module_struct_fields(module_id).map(|fields| fields.to_vec()) else {
            return Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("compiler2 does not know the schema for struct `{}`", module.dotted()),
                    span,
                ),
            ));
        };
        let mut by_name = fields
            .iter()
            .map(|(name, expr)| (name.as_str(), expr))
            .collect::<HashMap<_, _>>();
        let mut lowered = Vec::with_capacity(order.len());
        for field in order {
            let value = if let Some(expr) = by_name.remove(field.as_str()) {
                self.lower_expr(expr, env, steps)?
            } else {
                self.push_const(steps, Literal::Nil)
            };
            lowered.push((field, value));
        }
        if let Some((name, _)) = by_name.into_iter().next() {
            return Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("struct `{}` does not define field `{}`", module.dotted(), name),
                    span,
                ),
            ));
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
                    self.world,
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
        module: &crate::modules::identity::ModuleName,
        span: Span,
    ) -> Result<super::super::identity::ModuleId, FatalError> {
        self.world
            .resolve_module_name(self.def.owner_module, self.namespace, module)
            .ok_or_else(|| {
                emit_job_diagnostic(
                    self.world,
                    Diagnostic::error(
                        codes::LOWER_UNBOUND,
                        format!("compiler2 could not resolve struct module `{}`", module.dotted()),
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
            .map(|clause| self.lower_match_clause_block(subject_value, clause, env.clone()))
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
                arm_blocks: vec![arm_block],
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
                let success_block =
                    self.lower_match_success_block(matched, pattern, rest, body, else_clauses, env.clone(), span)?;
                let miss_block = self.lower_with_fail_block(span, matched, else_clauses, env.clone())?;
                let plan = self.compile_single_pattern_dispatch("with", pattern, span)?;
                let bindings = self.lower_dispatch_bindings(&plan, &[matched], &env, &mut steps, pattern.span)?;
                let value = self.fresh_value();
                steps.push(ExprStep::Dispatch {
                    value,
                    inputs: vec![matched],
                    bindings,
                    dispatch: Box::new(ExprDispatch {
                        plan,
                        arm_blocks: vec![success_block],
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

    fn lower_match_success_block(
        &mut self,
        subject: ValueId,
        pattern: &Spanned<Pattern>,
        remaining_bindings: &[WithBinding],
        body: &Spanned<Expr>,
        else_clauses: &[MatchClause],
        mut env: HashMap<String, ValueId>,
        span: Span,
    ) -> Result<ExprBlock, FatalError> {
        let mut steps = Vec::new();
        self.bind_pattern(&pattern.node, pattern.span, subject, &mut env, &mut steps)?;
        let rest = self.lower_with_block(span, remaining_bindings, body, else_clauses, env)?;
        steps.extend(rest.steps);
        Ok(ExprBlock {
            span: pattern.span,
            steps,
            result: rest.result,
        })
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
            .map(|clause| self.lower_match_clause_block(failed, clause, env.clone()))
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
                self.world,
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
        let clauses = clauses
            .iter()
            .map(|clause| self.lower_receive_clause(clause, env.clone()))
            .collect::<Result<Vec<_>, _>>()?;
        let after = after
            .map(|after| self.lower_receive_after(after, timeout.expect("receive after should have a timeout"), env))
            .transpose()?;
        let value = self.fresh_value();
        steps.push(ExprStep::Receive(Box::new(ExprReceive {
            value,
            bindings,
            dispatch: plan,
            clauses,
            after,
            captures,
        })));
        Ok(value)
    }

    fn lower_match_clause_block(
        &mut self,
        subject: ValueId,
        clause: &MatchClause,
        mut env: HashMap<String, ValueId>,
    ) -> Result<ExprBlock, FatalError> {
        let mut steps = Vec::new();
        self.bind_pattern(&clause.pattern.node, clause.pattern.span, subject, &mut env, &mut steps)?;
        let body = self.lower_expr_as_block(&clause.body, env)?;
        steps.extend(body.steps);
        Ok(ExprBlock {
            span: clause.span,
            steps,
            result: body.result,
        })
    }

    fn compile_match_dispatch(
        &mut self,
        label: &str,
        span: Span,
        rows: Vec<PatternRow<super::super::types::Ty>>,
    ) -> Result<crate::dispatch_matrix::pattern::PatternDispatchPlan<super::super::types::Ty>, FatalError> {
        let source = SourcePatternRows { input_count: 1, rows };
        let mut resolver = |name: &str,
                            arity: usize,
                            args: Vec<PatternGuardExpr<super::super::types::Ty>>|
         -> Result<Option<PatternGuardExpr<super::super::types::Ty>>, SourcePatternError> {
            let callee = resolve_guard_callee_checked(self.world, self.namespace, name, arity);
            Ok(Some(PatternGuardExpr::Dispatch {
                inputs: args,
                dispatch: Box::new(self.world.guard_dispatch(callee)),
            }))
        };
        pattern_dispatch_from_source_with_guard_resolver(source, &mut resolver)
            .map_err(|error| emit_local_dispatch_error(self.world, label, span, error))
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
        .map_err(|error| emit_local_dispatch_error(self.world, "cond", span, error))
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
                            self.world,
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
                        self.world,
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
            .map(|key| self.materialize_dispatch_const(key, steps, span))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(DispatchBindings { pinned, prepared })
    }

    fn materialize_dispatch_const(
        &mut self,
        key: &crate::dispatch_matrix::DispatchConst,
        steps: &mut Vec<ExprStep>,
        span: Span,
    ) -> Result<ValueId, FatalError> {
        let value = self.fresh_value();
        match key {
            crate::dispatch_matrix::DispatchConst::Int(n) => steps.push(ExprStep::Const {
                value,
                literal: Literal::Int(*n),
            }),
            crate::dispatch_matrix::DispatchConst::FloatBits(bits) => steps.push(ExprStep::Const {
                value,
                literal: Literal::Float(f64::from_bits(*bits)),
            }),
            crate::dispatch_matrix::DispatchConst::Utf8Binary(bytes) => steps.push(ExprStep::Const {
                value,
                literal: Literal::Binary(bytes.clone()),
            }),
            crate::dispatch_matrix::DispatchConst::AtomName(name) => steps.push(ExprStep::Const {
                value,
                literal: Literal::Atom(name.clone()),
            }),
            crate::dispatch_matrix::DispatchConst::Bool(flag) => steps.push(ExprStep::Const {
                value,
                literal: Literal::Bool(*flag),
            }),
            crate::dispatch_matrix::DispatchConst::Nil => steps.push(ExprStep::Const {
                value,
                literal: Literal::Nil,
            }),
            crate::dispatch_matrix::DispatchConst::EmptyList => {
                return Err(emit_job_diagnostic(
                    self.world,
                    Diagnostic::error(
                        codes::LOWER_UNSUPPORTED,
                        "compiler2 local dispatch does not materialize an empty-list prepared key".to_string(),
                        span,
                    ),
                ));
            }
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

    fn lower_receive_clause(
        &mut self,
        clause: &MatchClause,
        mut env: HashMap<String, ValueId>,
    ) -> Result<ExprReceiveClause, FatalError> {
        let mut bound_names = Vec::new();
        collect_pattern_bound_names(&clause.pattern.node, &mut bound_names);
        let params = bound_names
            .iter()
            .map(|name| {
                let value = self.fresh_value();
                env.insert(name.clone(), value);
                value
            })
            .collect::<Vec<_>>();
        let body = self.lower_expr_as_block(&clause.body, env)?;
        Ok(ExprReceiveClause {
            span: clause.span,
            bound_names,
            params,
            body,
        })
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
                    literal: Literal::Nil,
                },
                ExprStep::Halt { atom: atom.to_string() },
            ],
            result: value,
        }
    }

    fn lower_lambda(
        &mut self,
        span: Span,
        clauses: &[LambdaClause],
        env: &HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
    ) -> Result<ValueId, FatalError> {
        let ast = FnDef {
            name: format!("#lambda:{}:{}-{}", self.owner.as_u32(), span.start, span.end),
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
            is_private: true,
            extern_abi: None,
            extern_param_tokens: Vec::new(),
            extern_ret_tokens: crate::ast::TypeExprBody(Vec::new()),
            extern_constraints: Vec::new(),
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

        let (function, revision) =
            self.world
                .define_generated_function(self.owner, self.namespace, capture_params, ast);
        self.generated
            .push((FactKey::FunctionDefined(function), FactValue::presence(revision)));
        self.generated_ids.push(function);

        let captures = captures.into_iter().collect::<Vec<_>>();
        let value = self.fresh_value();
        steps.push(ExprStep::Lambda {
            value,
            function,
            captures,
        });
        Ok(value)
    }

    fn plan_clauses(&mut self, clauses: Vec<ExprClause>) -> (Vec<LoweredClause>, Vec<LoweredEntry>) {
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
        let captures = compute_entry_captures(&entries, &clause_bounds);
        for (entry, captures) in entries.iter_mut().zip(captures) {
            entry.captures = captures;
        }
        (lowered, entries)
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
                            ControlEntryOrigin::CallResume { value: *value },
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
                            callee: callee.clone(),
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
                            ControlEntryOrigin::CallResume { value: *value },
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
                            ControlEntryOrigin::LocalResume { value: *value },
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
                            ControlEntryOrigin::LocalResume { value: *value },
                            dest,
                            Vec::new(),
                            Vec::new(),
                            entries,
                        );
                        ControlDestination::Deliver(resume)
                    };
                    let arm_entries = dispatch
                        .arm_blocks
                        .iter()
                        .cloned()
                        .map(|arm| {
                            self.plan_block(
                                arm,
                                ControlEntryOrigin::Branch,
                                branch_dest.clone(),
                                Vec::new(),
                                Vec::new(),
                                entries,
                            )
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
                                arm_entries,
                                miss_entry,
                            }),
                        },
                    );
                }
                ExprStep::Receive(receive) => {
                    let value = receive.value;
                    let bindings = &receive.bindings;
                    let dispatch = &receive.dispatch;
                    let clauses = &receive.clauses;
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
                            ControlEntryOrigin::LocalResume { value },
                            dest,
                            Vec::new(),
                            Vec::new(),
                            entries,
                        );
                        ControlDestination::Deliver(resume)
                    };
                    let clauses = clauses
                        .iter()
                        .map(|clause| ReceiveClause {
                            span: clause.span,
                            bound_names: clause.bound_names.clone(),
                            entry: self.plan_block(
                                clause.body.clone(),
                                ControlEntryOrigin::Receive,
                                branch_dest.clone(),
                                clause.params.clone(),
                                captures.clone(),
                                entries,
                            ),
                        })
                        .collect::<Vec<_>>();
                    let after = after.as_ref().map(|after| ReceiveAfter {
                        span: after.span,
                        timeout: after.timeout,
                        entry: self.plan_block(
                            after.body.clone(),
                            ControlEntryOrigin::Receive,
                            branch_dest,
                            Vec::new(),
                            captures.clone(),
                            entries,
                        ),
                    });
                    return (
                        lowered,
                        LoweredTail::Receive(Box::new(super::super::body::LoweredReceive {
                            bindings: bindings.clone(),
                            dispatch: dispatch.clone(),
                            clauses,
                            after,
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
                    literal: Literal::Int(*value),
                });
                Ok(())
            }
            Pattern::Float(value) => {
                steps.push(ExprStep::AssertLiteral {
                    source,
                    literal: Literal::Float(*value),
                });
                Ok(())
            }
            Pattern::Binary(value) => {
                steps.push(ExprStep::AssertLiteral {
                    source,
                    literal: Literal::Binary(value.clone()),
                });
                Ok(())
            }
            Pattern::Atom(value) => {
                steps.push(ExprStep::AssertLiteral {
                    source,
                    literal: Literal::Atom(value.clone()),
                });
                Ok(())
            }
            Pattern::Bool(value) => {
                steps.push(ExprStep::AssertLiteral {
                    source,
                    literal: Literal::Bool(*value),
                });
                Ok(())
            }
            Pattern::Nil => {
                steps.push(ExprStep::AssertLiteral {
                    source,
                    literal: Literal::Nil,
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
                        self.world,
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
                    self.world,
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
        module: &crate::modules::identity::ModuleName,
        fields: &[(String, Spanned<Pattern>)],
        span: Span,
        source: ValueId,
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<ExprStep>,
        with_asserts: bool,
    ) -> Result<(), FatalError> {
        let module_id = self.resolve_struct_module(module, span)?;
        let Some(order) = self.world.module_struct_fields(module_id).map(|fields| fields.to_vec()) else {
            return Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("compiler2 does not know the schema for struct `{}`", module.dotted()),
                    span,
                ),
            ));
        };
        let mut by_name = fields
            .iter()
            .map(|(name, pattern)| (name.as_str(), pattern))
            .collect::<HashMap<_, _>>();
        steps.push(ExprStep::AssertStruct {
            source,
            module: module_id,
        });
        for (index, field) in order.iter().enumerate() {
            let Some(pattern) = by_name.remove(field.as_str()) else {
                continue;
            };
            let value = self.fresh_value();
            steps.push(ExprStep::TupleField { value, source, index });
            if with_asserts {
                self.apply_pattern(&pattern.node, pattern.span, value, env, steps)?;
            } else {
                self.bind_pattern(&pattern.node, pattern.span, value, env, steps)?;
            }
        }
        if let Some((name, pattern)) = by_name.into_iter().next() {
            return Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("struct `{}` does not define field `{}`", module.dotted(), name),
                    pattern.span,
                ),
            ));
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
                literal: Literal::Bool(true),
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

    fn push_const(&mut self, steps: &mut Vec<ExprStep>, literal: Literal) -> ValueId {
        let value = self.fresh_value();
        steps.push(ExprStep::Const { value, literal });
        value
    }

    fn fresh_value(&mut self) -> ValueId {
        let value = ValueId::from_u32(self.next_value);
        self.next_value += 1;
        value
    }

    fn fresh_callsite(&mut self) -> CallSiteId {
        let value = CallSiteId::from_u32(self.next_callsite);
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
            items: items.clone(),
        },
        ExprStep::List { value, items, tail } => LoweredStep::List {
            value: *value,
            items: items.clone(),
            tail: *tail,
        },
        ExprStep::Map { value, entries } => LoweredStep::Map {
            value: *value,
            entries: entries.clone(),
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
        ExprStep::NamedFunctionRef { value, name, arity } => LoweredStep::NamedFunctionRef {
            value: *value,
            name: name.clone(),
            arity: *arity,
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
            key: *key,
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
    let mut out = HashSet::new();
    for step in steps {
        match step {
            LoweredStep::Const { value, .. }
            | LoweredStep::Tuple { value, .. }
            | LoweredStep::List { value, .. }
            | LoweredStep::Map { value, .. }
            | LoweredStep::MapUpdate { value, .. }
            | LoweredStep::Struct { value, .. }
            | LoweredStep::Bitstring { value, .. }
            | LoweredStep::FunctionRef { value, .. }
            | LoweredStep::NamedFunctionRef { value, .. }
            | LoweredStep::Lambda { value, .. }
            | LoweredStep::BinaryOp { value, .. }
            | LoweredStep::UnaryOp { value, .. }
            | LoweredStep::MapIndex { value, .. }
            | LoweredStep::FieldAccess { value, .. }
            | LoweredStep::RequireMapValue { value, .. }
            | LoweredStep::TupleField { value, .. } => {
                out.insert(*value);
            }
            LoweredStep::SplitList { head, tail, .. } => {
                out.insert(*head);
                out.insert(*tail);
            }
            LoweredStep::BitstringInit { reader, .. } => {
                out.insert(*reader);
            }
            LoweredStep::BitstringRead {
                ok, value, next_reader, ..
            } => {
                out.insert(*ok);
                out.insert(*value);
                out.insert(*next_reader);
            }
            LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertStruct { .. }
            | LoweredStep::AssertTuple { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::AssertSame { .. }
            | LoweredStep::AssertBitstringDone { .. } => {}
        }
    }
    out
}

fn compute_entry_captures(
    entries: &[LoweredEntry],
    clause_bounds: &HashMap<ControlEntryId, HashSet<ValueId>>,
) -> Vec<Vec<ValueId>> {
    let mut memo = HashMap::new();
    for entry_id in 0..entries.len() {
        let entry_id = ControlEntryId::from_u32(entry_id as u32);
        let _ = entry_captures(entries, clause_bounds, entry_id, &mut memo);
    }
    (0..entries.len())
        .map(|index| memo.remove(&ControlEntryId::from_u32(index as u32)).unwrap_or_default())
        .collect()
}

fn entry_captures(
    entries: &[LoweredEntry],
    clause_bounds: &HashMap<ControlEntryId, HashSet<ValueId>>,
    entry_id: ControlEntryId,
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

    let mut needed = used_values_in_entry(entry);
    for child in child_entries(entry.tail.clone()) {
        for capture in entry_captures(entries, clause_bounds, child, memo) {
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
    match &entry.tail {
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
    out
}

fn collect_used_values(steps: &[LoweredStep], out: &mut HashSet<ValueId>) {
    for step in steps {
        match step {
            LoweredStep::Const { .. } | LoweredStep::FunctionRef { .. } | LoweredStep::NamedFunctionRef { .. } => {}
            LoweredStep::Tuple { items, .. } => out.extend(items.iter().copied()),
            LoweredStep::List { items, tail, .. } => {
                out.extend(items.iter().copied());
                if let Some(tail) = tail {
                    out.insert(*tail);
                }
            }
            LoweredStep::Map { entries, .. } => {
                for (key, value) in entries {
                    out.insert(*key);
                    out.insert(*value);
                }
            }
            LoweredStep::MapUpdate { base, entries, .. } => {
                out.insert(*base);
                for (key, value) in entries {
                    out.insert(*key);
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
                out.insert(*key);
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
            let mut children = dispatch.arm_entries.clone();
            children.push(dispatch.miss_entry);
            children
        }
        LoweredTail::Receive(receive) => {
            let mut children = receive.clauses.iter().map(|clause| clause.entry).collect::<Vec<_>>();
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

fn collect_pattern_bound_names(pattern: &Pattern, out: &mut Vec<String>) {
    match pattern {
        Pattern::Var(name) => out.push(name.clone()),
        Pattern::As(name, inner) => {
            out.push(name.clone());
            collect_pattern_bound_names(&inner.node, out);
        }
        Pattern::Tuple(items) => {
            for item in items {
                collect_pattern_bound_names(&item.node, out);
            }
        }
        Pattern::List(items, tail) => {
            for item in items {
                collect_pattern_bound_names(&item.node, out);
            }
            if let Some(tail) = tail {
                collect_pattern_bound_names(&tail.node, out);
            }
        }
        Pattern::Map(entries) => {
            for (_, value) in entries {
                collect_pattern_bound_names(&value.node, out);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, value) in fields {
                collect_pattern_bound_names(&value.node, out);
            }
        }
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_pattern_bound_names(&field.value.node, out);
            }
        }
        Pattern::Wildcard
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil
        | Pattern::Pinned(_) => {}
    }
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
        Expr::Lambda(clauses) => {
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

fn emit_local_dispatch_error(world: &World<'_>, label: &str, span: Span, error: PatternDispatchError) -> FatalError {
    match error {
        PatternDispatchError::SourcePattern(SourcePatternError::UnsupportedGuardExpr) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 {label} guards must be dispatch-pure"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(SourcePatternError::UnknownPinned(name))
        | PatternDispatchError::SourcePattern(SourcePatternError::UnknownGuardVar(name)) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNBOUND,
                format!("compiler2 {label} guard references unknown name `{name}`"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(SourcePatternError::UnsupportedMapKey) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 {label} patterns require literal map keys"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(SourcePatternError::DispatchMatrix(message)) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 {label} dispatch could not be planned: {message}"),
                span,
            ),
        ),
        PatternDispatchError::SourcePattern(
            SourcePatternError::UnknownSubject(_)
            | SourcePatternError::RowPatternArity { .. }
            | SourcePatternError::NonMonotonicBodyId { .. },
        ) => {
            panic!("compiler2 built an invalid local dispatch row set: {error:?}")
        }
        PatternDispatchError::SourcePattern(SourcePatternError::GuardCallCycle(name, arity)) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 {label} guard helper cycle detected through `{name}/{arity}`"),
                span,
            ),
        ),
        PatternDispatchError::MatrixBuild(error) => emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("compiler2 {label} dispatch matrix is invalid: {error:?}"),
                span,
            ),
        ),
        PatternDispatchError::Compile(error) => emit_job_diagnostic(
            world,
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
        Expr::Lambda(_) => "Lambda",
        Expr::Quote(_) => "Quote",
        Expr::Unquote(_) => "Unquote",
    }
}

fn direct_call_name(expr: &Spanned<Expr>, env: &HashMap<String, ValueId>) -> Option<String> {
    let mut path = Vec::new();
    let mut current = &expr.node;
    loop {
        match current {
            Expr::Var(name) => {
                if env.contains_key(name) {
                    return None;
                }
                path.push(name.clone());
                path.reverse();
                return Some(path.join("."));
            }
            Expr::Index(target, key) => {
                let Expr::Atom(name) = &key.node else {
                    return None;
                };
                path.push(name.clone());
                current = &target.node;
            }
            _ => return None,
        }
    }
}

fn literal_from_pattern(pattern: &Pattern) -> Option<Literal> {
    Some(match pattern {
        Pattern::Int(value) => Literal::Int(*value),
        Pattern::Float(value) => Literal::Float(*value),
        Pattern::Binary(value) => Literal::Binary(value.clone()),
        Pattern::Atom(value) => Literal::Atom(value.clone()),
        Pattern::Bool(value) => Literal::Bool(*value),
        Pattern::Nil => Literal::Nil,
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

fn emit_job_diagnostic(world: &World<'_>, diagnostic: Diagnostic) -> FatalError {
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    FatalError
}
