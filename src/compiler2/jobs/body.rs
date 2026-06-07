//! Compiler2 body-lowering jobs and helpers.
//!
//! This module lowers one defined function at a time into Compiler2's
//! structured body form. It owns the local lowering algorithm, lambda capture
//! discovery, and generated-function definition path.

use std::collections::{HashMap, HashSet};

use crate::ast::{Expr, FnClause, FnDef, LambdaClause, MatchClause, Pattern, Spanned, WithBinding};
use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;

use super::super::body::{
    CallSiteId, DirectCallee, Literal, LoweredBlock, LoweredBody, LoweredClause, LoweredStep, ValueId,
};
use super::super::drive::{FactKey, JobEffects};
use super::super::facts::FactValue;
use super::super::identity::{FunctionDef, FunctionId};
use super::super::namespace::{Namespace, NamespaceSymbol};
use super::super::scheduler::FatalError;
use super::super::world::World;

type Output = (FactKey, FactValue);

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

    let mut lowerer = Lowerer::new(world, function, &def);
    let (body, mut outputs) = lowerer.lower()?;
    let revision = lowerer.world.define_lowered_body(function, body);
    outputs.push((FactKey::LoweredBody(function), FactValue::presence(revision)));
    Ok(JobEffects {
        reads: vec![FactKey::FunctionDefined(function)],
        outputs,
        ..JobEffects::default()
    })
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
            return Ok((
                LoweredBody::Extern {
                    abi,
                    arity: self.def.ast.arity(),
                },
                Vec::new(),
            ));
        }

        let mut clauses = Vec::new();
        for clause in self.def.ast.clauses.clone() {
            clauses.push(self.lower_clause(&clause)?);
        }

        Ok((
            LoweredBody::Clauses {
                clauses,
                generated: self.generated_ids.clone(),
            },
            std::mem::take(&mut self.generated),
        ))
    }

    fn lower_clause(&mut self, clause: &FnClause) -> Result<LoweredClause, FatalError> {
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

        Ok(LoweredClause {
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
    ) -> Result<LoweredBlock, FatalError> {
        let mut steps = Vec::new();
        let result = self.lower_expr(expr, &mut env, &mut steps)?;
        Ok(LoweredBlock {
            span: expr.span,
            steps,
            result,
        })
    }

    fn lower_expr(
        &mut self,
        expr: &Spanned<Expr>,
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<LoweredStep>,
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
                        steps.push(LoweredStep::FunctionRef { value, function });
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
                        steps.push(LoweredStep::FunctionRef { value, function });
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
                        steps.push(LoweredStep::NamedFunctionRef {
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
                steps.push(LoweredStep::List {
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
                steps.push(LoweredStep::Tuple { value, items: lowered });
                Ok(value)
            }
            Expr::Index(base, key) => {
                let base = self.lower_expr(base, env, steps)?;
                let key = self.lower_expr(key, env, steps)?;
                let value = self.fresh_value();
                steps.push(LoweredStep::MapIndex { value, base, key });
                Ok(value)
            }
            Expr::Call(target, args) => {
                let mut lowered_args = Vec::with_capacity(args.len());
                for arg in args {
                    lowered_args.push(self.lower_expr(arg, env, steps)?);
                }
                let callsite = self.fresh_callsite();
                if let Some(name) = direct_call_name(target, env) {
                    let value = self.fresh_value();
                    steps.push(LoweredStep::DirectCall {
                        value,
                        callsite,
                        callee: self.resolve_direct_callee(&name, args.len(), target.span)?,
                        args: lowered_args,
                    });
                    return Ok(value);
                }
                let callee = self.lower_expr(target, env, steps)?;
                let value = self.fresh_value();
                steps.push(LoweredStep::ClosureCall {
                    value,
                    callsite,
                    callee,
                    args: lowered_args,
                });
                Ok(value)
            }
            Expr::ClosureCall(target, args) => {
                let callee = self.lower_expr(target, env, steps)?;
                let mut lowered_args = Vec::with_capacity(args.len());
                for arg in args {
                    lowered_args.push(self.lower_expr(arg, env, steps)?);
                }
                let value = self.fresh_value();
                steps.push(LoweredStep::ClosureCall {
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
                steps.push(LoweredStep::BinaryOp {
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
                steps.push(LoweredStep::UnaryOp { value, op: *op, input });
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
                    LoweredBlock {
                        span: nil_span,
                        steps: vec![LoweredStep::Const {
                            value: result,
                            literal: Literal::Nil,
                        }],
                        result,
                    }
                };
                let value = self.fresh_value();
                steps.push(LoweredStep::If {
                    value,
                    cond,
                    then_block,
                    else_block,
                });
                Ok(value)
            }
            Expr::Lambda(clauses) => self.lower_lambda(expr.span, clauses, env, steps),
            Expr::Capture(_)
            | Expr::CaptureArg(_)
            | Expr::Bitstring(_)
            | Expr::Map(_)
            | Expr::MapUpdate(_, _)
            | Expr::Struct { .. }
            | Expr::Case(_, _)
            | Expr::Cond(_)
            | Expr::With(_, _, _)
            | Expr::Receive { .. }
            | Expr::Quote(_)
            | Expr::Unquote(_) => Err(emit_job_diagnostic(
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
                Some(NamespaceSymbol::Module(_)) | None => DirectCallee::Named {
                    name: name.to_string(),
                    arity,
                },
            },
        )
    }

    fn lower_lambda(
        &mut self,
        span: Span,
        clauses: &[LambdaClause],
        env: &HashMap<String, ValueId>,
        steps: &mut Vec<LoweredStep>,
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
            extern_params: Vec::new(),
            extern_ret_tokens: crate::ast::TypeExprBody(Vec::new()),
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
        steps.push(LoweredStep::Lambda {
            value,
            function,
            captures,
        });
        Ok(value)
    }

    fn apply_pattern(
        &mut self,
        pattern: &Pattern,
        span: Span,
        source: ValueId,
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<LoweredStep>,
    ) -> Result<(), FatalError> {
        match pattern {
            Pattern::Wildcard => Ok(()),
            Pattern::Var(name) => {
                env.insert(name.clone(), source);
                Ok(())
            }
            Pattern::Int(value) => {
                steps.push(LoweredStep::AssertLiteral {
                    source,
                    literal: Literal::Int(*value),
                });
                Ok(())
            }
            Pattern::Float(value) => {
                steps.push(LoweredStep::AssertLiteral {
                    source,
                    literal: Literal::Float(*value),
                });
                Ok(())
            }
            Pattern::Binary(value) => {
                steps.push(LoweredStep::AssertLiteral {
                    source,
                    literal: Literal::Binary(value.clone()),
                });
                Ok(())
            }
            Pattern::Atom(value) => {
                steps.push(LoweredStep::AssertLiteral {
                    source,
                    literal: Literal::Atom(value.clone()),
                });
                Ok(())
            }
            Pattern::Bool(value) => {
                steps.push(LoweredStep::AssertLiteral {
                    source,
                    literal: Literal::Bool(*value),
                });
                Ok(())
            }
            Pattern::Nil => {
                steps.push(LoweredStep::AssertLiteral {
                    source,
                    literal: Literal::Nil,
                });
                Ok(())
            }
            Pattern::Tuple(items) => {
                steps.push(LoweredStep::AssertTuple {
                    source,
                    arity: items.len(),
                });
                for (index, item) in items.iter().enumerate() {
                    let value = self.fresh_value();
                    steps.push(LoweredStep::TupleField { value, source, index });
                    self.apply_pattern(&item.node, item.span, value, env, steps)?;
                }
                Ok(())
            }
            Pattern::List(items, tail) => {
                if items.is_empty() && tail.is_none() {
                    steps.push(LoweredStep::AssertEmptyList { source });
                    return Ok(());
                }
                let mut current = source;
                for item in items {
                    let head = self.fresh_value();
                    let tail_value = self.fresh_value();
                    steps.push(LoweredStep::SplitList {
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
                    steps.push(LoweredStep::AssertEmptyList { source: current });
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
                steps.push(LoweredStep::AssertSame { source, value: pinned });
                Ok(())
            }
            Pattern::Map(_) | Pattern::Struct { .. } | Pattern::Bitstring(_) => Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!("compiler2 does not lower `{}` patterns yet", pattern_name(pattern)),
                    span,
                ),
            )),
        }
    }

    fn bind_pattern(
        &mut self,
        pattern: &Pattern,
        span: Span,
        source: ValueId,
        env: &mut HashMap<String, ValueId>,
        steps: &mut Vec<LoweredStep>,
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
                    steps.push(LoweredStep::TupleField { value, source, index });
                    self.bind_pattern(&item.node, item.span, value, env, steps)?;
                }
                Ok(())
            }
            Pattern::List(items, tail) => {
                let mut current = source;
                for item in items {
                    let head = self.fresh_value();
                    let tail_value = self.fresh_value();
                    steps.push(LoweredStep::SplitList {
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
            Pattern::Map(_) | Pattern::Struct { .. } | Pattern::Bitstring(_) => Err(emit_job_diagnostic(
                self.world,
                Diagnostic::error(
                    codes::LOWER_UNSUPPORTED,
                    format!(
                        "compiler2 does not lower `{}` clause projections yet",
                        pattern_name(pattern)
                    ),
                    span,
                ),
            )),
        }
    }

    fn push_const(&mut self, steps: &mut Vec<LoweredStep>, literal: Literal) -> ValueId {
        let value = self.fresh_value();
        steps.push(LoweredStep::Const { value, literal });
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
        Pattern::Wildcard
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil
        | Pattern::Bitstring(_) => {}
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
        Pattern::Wildcard
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil
        | Pattern::Bitstring(_) => {}
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
