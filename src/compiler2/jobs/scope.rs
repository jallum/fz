//! The scoping rules of a function body, walked once: where each name is
//! bound, and which binding each reference reaches. Lowering asks two
//! questions of it: which names an expression reads from outside itself (what
//! a nested block or lambda captures), and which bindings nothing reads (the
//! unused-variable warning).

use crate::ast::{
    BitSize, CatchClause, Expr, FnClause, LambdaClause, MatchClause, Pattern, RescueClause, Spanned, Var, VarContext,
    WithBinding,
};
use crate::diag::{Diagnostic, codes};
use crate::fast_hash::{HashMap, HashSet};
use crate::source::Span;

type BindingId = usize;

/// One place a name is bound.
struct Binding {
    var: Var,
    span: Span,
    /// The name was already bound where this binding was made.
    shadows: bool,
    used: bool,
}

#[derive(Default)]
pub(super) struct ScopeWalk {
    scope: HashMap<Var, BindingId>,
    bindings: Vec<Binding>,
    free: HashSet<Var>,
}

/// The names `expr` reads that it does not bind itself.
pub(super) fn free_names(expr: &Expr) -> HashSet<Var> {
    let mut walk = ScopeWalk::default();
    walk.expr(expr);
    walk.free
}

/// The names a lambda's clauses read from the scope around the lambda.
pub(super) fn lambda_free_names(clauses: &[LambdaClause]) -> HashSet<Var> {
    let mut walk = ScopeWalk::default();
    walk.lambda_clauses(clauses);
    walk.free
}

/// The names a `receive` reads from the scope around it: its clauses and its
/// `after`.
pub(super) fn receive_free_names(clauses: &[MatchClause], after: Option<(&Expr, &Expr)>) -> HashSet<Var> {
    let mut walk = ScopeWalk::default();
    walk.match_clauses(clauses);
    if let Some((timeout, body)) = after {
        walk.expr(timeout);
        walk.expr(body);
    }
    walk.free
}

/// The names a `try`'s `rescue` and `catch` clauses read from the scope
/// around them.
pub(super) fn handler_free_names(rescue: &[RescueClause], catch: &[CatchClause]) -> HashSet<Var> {
    let mut walk = ScopeWalk::default();
    walk.rescue_clauses(rescue);
    walk.catch_clauses(catch);
    walk.free
}

/// Elixir's warning for every variable a function clause binds and never
/// reads, clause by clause. A name that starts with an underscore, and a name
/// a macro wrote, is not warned about.
pub(super) fn unused_variable_diagnostics(clauses: &[FnClause]) -> Vec<Diagnostic> {
    clauses
        .iter()
        .flat_map(|clause| {
            let mut walk = ScopeWalk::default();
            walk.clause(&clause.params, clause.guard.as_ref(), &clause.body);
            walk.bindings
        })
        .filter(|binding| !binding.used && is_warned(&binding.var))
        .map(|binding| unused_variable_diagnostic(&binding))
        .collect()
}

fn is_warned(var: &Var) -> bool {
    var.context == VarContext::User && !var.name.starts_with('_')
}

fn unused_variable_diagnostic(binding: &Binding) -> Diagnostic {
    let advice = if binding.shadows {
        "there is a variable with the same name in the context, use the pin operator (^) to match on it or prefix \
         this variable with underscore if it is not meant to be used"
    } else {
        "if the variable is not meant to be used, prefix it with an underscore"
    };
    Diagnostic::warning(
        codes::LOWER_UNUSED_VARIABLE,
        format!("variable \"{}\" is unused ({advice})", binding.var.name),
        binding.span,
    )
}

impl ScopeWalk {
    fn reference(&mut self, var: &Var) {
        match self.scope.get(var) {
            Some(&binding) => self.bindings[binding].used = true,
            None => {
                self.free.insert(var.clone());
            }
        }
    }

    /// Walks `walk` in a scope of its own: nothing it binds is seen after it.
    fn branch(&mut self, walk: impl FnOnce(&mut Self)) {
        let saved = self.scope.clone();
        walk(self);
        self.scope = saved;
    }

    /// Binds the names of `patterns`, matched together as one head. A pin
    /// reads the scope before the head; a name written twice in the head is
    /// bound by its first occurrence and compared by the rest.
    fn bind_head<'p>(&mut self, patterns: impl IntoIterator<Item = &'p Spanned<Pattern>>) {
        let mut head = HashMap::default();
        for pattern in patterns {
            self.pattern(pattern, &mut head);
        }
        self.scope.extend(head);
    }

    fn bind(&mut self, var: &Var, span: Span, head: &mut HashMap<Var, BindingId>) {
        match head.get(var) {
            Some(&binding) => self.bindings[binding].used = true,
            None => {
                let binding = self.bindings.len();
                self.bindings.push(Binding {
                    var: var.clone(),
                    span,
                    shadows: self.scope.contains_key(var),
                    used: false,
                });
                head.insert(var.clone(), binding);
            }
        }
    }

    fn pattern(&mut self, pattern: &Spanned<Pattern>, head: &mut HashMap<Var, BindingId>) {
        match &pattern.node {
            Pattern::Var(var) => self.bind(var, pattern.span, head),
            Pattern::Pinned(var) => self.reference(var),
            Pattern::Tuple(items) => {
                for item in items {
                    self.pattern(item, head);
                }
            }
            Pattern::List(items, tail) => {
                for item in items.iter().chain(tail.as_deref()) {
                    self.pattern(item, head);
                }
            }
            Pattern::Both(left, right) => {
                self.pattern(left, head);
                self.pattern(right, head);
            }
            Pattern::Map(entries) => {
                for (key, value) in entries {
                    self.pattern(key, head);
                    self.pattern(value, head);
                }
            }
            Pattern::Struct { fields, .. } => {
                for (_, value) in fields {
                    self.pattern(value, head);
                }
            }
            Pattern::Bitstring(fields) => {
                for field in fields {
                    match &field.spec.size {
                        Some(BitSize::Var(var)) => match head.get(var) {
                            Some(&binding) => self.bindings[binding].used = true,
                            None => self.reference(var),
                        },
                        Some(BitSize::ByteSizeOf(var)) => self.reference(var),
                        Some(BitSize::Literal(_)) | None => {}
                    }
                    self.pattern(&field.value, head);
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

    fn clause<'p>(
        &mut self,
        params: impl IntoIterator<Item = &'p Spanned<Pattern>>,
        guard: Option<&Spanned<Expr>>,
        body: &Spanned<Expr>,
    ) {
        self.branch(|walk| {
            walk.bind_head(params);
            if let Some(guard) = guard {
                walk.expr(&guard.node);
            }
            walk.expr(&body.node);
        });
    }

    fn lambda_clauses(&mut self, clauses: &[LambdaClause]) {
        for clause in clauses {
            self.clause(&clause.params, clause.guard.as_ref(), &clause.body);
        }
    }

    fn match_clauses(&mut self, clauses: &[MatchClause]) {
        for clause in clauses {
            self.clause([&clause.pattern], clause.guard.as_ref(), &clause.body);
        }
    }

    fn rescue_clauses(&mut self, clauses: &[RescueClause]) {
        for clause in clauses {
            self.branch(|walk| {
                if let Some(binding) = &clause.binding {
                    let mut head = HashMap::default();
                    walk.bind(&binding.node, binding.span, &mut head);
                    walk.scope.extend(head);
                }
                walk.expr(&clause.body.node);
            });
        }
    }

    fn catch_clauses(&mut self, clauses: &[CatchClause]) {
        for clause in clauses {
            self.clause([&clause.kind, &clause.value], clause.guard.as_ref(), &clause.body);
        }
    }

    fn exprs<'e>(&mut self, exprs: impl IntoIterator<Item = &'e Spanned<Expr>>) {
        for expr in exprs {
            self.expr(&expr.node);
        }
    }

    fn expr(&mut self, expr: &Expr) {
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
            // A quote's own text names quoted data, not a reference to
            // anything in the enclosing scope. Its `unquote` splices are
            // ordinary code, already decoded.
            Expr::Quote(_, splices) => self.exprs(splices),
            Expr::Capture(body) => self.expr(&body.node),
            Expr::Var(var) => self.reference(var),
            Expr::List(items, tail) => self.exprs(items.iter().chain(tail.as_deref())),
            Expr::Tuple(items) => self.exprs(items),
            Expr::Bitstring(fields) => {
                for field in fields {
                    self.expr(&field.value.node);
                    match &field.spec.size {
                        Some(BitSize::Var(var) | BitSize::ByteSizeOf(var)) => self.reference(var),
                        Some(BitSize::Literal(_)) | None => {}
                    }
                }
            }
            Expr::Map(entries) => self.exprs(entries.iter().flat_map(|(key, value)| [key, value])),
            Expr::MapUpdate(base, entries) => {
                self.expr(&base.node);
                self.exprs(entries.iter().flat_map(|(key, value)| [key, value]));
            }
            Expr::Struct { fields, .. } => self.exprs(fields.iter().map(|(_, value)| value)),
            Expr::Index(base, key) => self.exprs([&**base, &**key]),
            Expr::Call(callee, args) => {
                if !matches!(callee.node, Expr::Var(_)) {
                    self.expr(&callee.node);
                }
                self.exprs(args);
            }
            Expr::ClosureCall(callee, args) => {
                self.expr(&callee.node);
                self.exprs(args);
            }
            Expr::BinOp(_, left, right) => self.exprs([&**left, &**right]),
            Expr::UnOp(_, expr) | Expr::Ascribe(expr, _) | Expr::Unquote(expr) => self.expr(&expr.node),
            Expr::If(condition, then_expr, else_expr) => {
                self.expr(&condition.node);
                self.branch(|walk| walk.expr(&then_expr.node));
                if let Some(else_expr) = else_expr {
                    self.branch(|walk| walk.expr(&else_expr.node));
                }
            }
            Expr::Case(subject, clauses) => {
                if let Some(subject) = subject {
                    self.expr(&subject.node);
                }
                self.match_clauses(clauses);
            }
            Expr::Cond(arms) => {
                for (test, body) in arms {
                    self.branch(|walk| walk.expr(&test.node));
                    self.branch(|walk| walk.expr(&body.node));
                }
            }
            Expr::With(bindings, body, else_clauses) => {
                self.branch(|walk| {
                    for binding in bindings {
                        match binding {
                            WithBinding::Bare(expr) => walk.expr(&expr.node),
                            WithBinding::Match(pattern, expr) => {
                                walk.expr(&expr.node);
                                walk.bind_head([pattern]);
                            }
                        }
                    }
                    walk.expr(&body.node);
                });
                self.match_clauses(else_clauses);
            }
            Expr::Try {
                body,
                rescue,
                catch,
                else_clauses,
                after,
                form: _,
            } => {
                self.branch(|walk| walk.expr(&body.node));
                self.rescue_clauses(rescue);
                self.catch_clauses(catch);
                self.match_clauses(else_clauses);
                if let Some(after) = after {
                    self.branch(|walk| walk.expr(&after.node));
                }
            }
            Expr::Receive { clauses, after } => {
                self.match_clauses(clauses);
                if let Some(after) = after {
                    self.exprs([&after.timeout, &after.body]);
                }
            }
            Expr::Match(pattern, value) => {
                self.expr(&value.node);
                self.bind_head([pattern]);
            }
            Expr::Block(exprs) => self.exprs(exprs),
            Expr::Lambda { clauses, .. } => self.lambda_clauses(clauses),
        }
    }
}
