//! What a handler's dispatch reads besides what the runtime delivers.
//!
//! The runtime hands a handler the raise's kind and value. A `catch` clause
//! that reads the reason sees the Erlang reason Elixir binds for an error fz's
//! runtime raised as a struct (`%MatchError{term: 1}` is `{:badmatch, 1}`).
//! The reason is a source call over the delivered values, made only for a
//! handler with such a clause, and through a module value so that only an
//! analysed call reaches the library function.

use crate::ast::{CatchClause, Expr, Pattern, Spanned, Var, VarContext};
use crate::modules::identity::ModuleName;
use crate::source::Span;

use super::super::scope::free_names;

const HANDLER_SUBJECTS_CONTEXT: &str = "fz_handler_subjects";

/// The names the reason call reads: the handler's delivered kind and value,
/// and the module `Exception` as a value.
pub(super) struct SubjectNames {
    pub(super) kind: Var,
    pub(super) raised: Var,
    pub(super) library: Var,
}

impl SubjectNames {
    pub(super) fn new() -> Self {
        let minted = |index: i64, name: &str| Var {
            name: name.to_string(),
            context: VarContext::minted(HANDLER_SUBJECTS_CONTEXT, index),
        };
        Self {
            kind: minted(0, "kind"),
            raised: minted(1, "raised"),
            library: minted(2, "library"),
        }
    }

    /// The atom of the module the conversions are called on.
    pub(super) fn library_atom() -> String {
        ModuleName::from_segments(vec!["Exception".to_string()]).atom_name()
    }
}

/// Whether a `catch` clause reads the reason of an error: its value pattern
/// binds or tests something the clause then uses, and its kind pattern can
/// match `:error`. A clause that only hands the reason back to
/// `Exception.__rethrow__(kind, reason)` does not read it: the value rethrown is
/// the one delivered, whole.
/// The callee `Exception.__rethrow__`, written qualified or, inside the library,
/// imported.
fn rethrows(callee: &Expr) -> bool {
    match callee {
        Expr::Var(name) => name.name == RETHROW,
        Expr::Index(_, function) => matches!(&function.node, Expr::Atom(name) if name == RETHROW),
        _ => false,
    }
}

const RETHROW: &str = "__rethrow__";

pub(super) fn reads_reason(clause: &CatchClause) -> bool {
    let kind_can_be_error = !matches!(&clause.kind.node, Pattern::Atom(kind) if kind != "error");
    kind_can_be_error && !ignores(&clause.value.node, clause)
}

fn ignores(value: &Pattern, clause: &CatchClause) -> bool {
    match value {
        Pattern::Wildcard => true,
        Pattern::Var(var) => var.name.starts_with('_') || !used_beyond_reraise(var, clause),
        _ => false,
    }
}

fn used_beyond_reraise(reason: &Var, clause: &CatchClause) -> bool {
    let guard_reads = clause
        .guard
        .as_ref()
        .is_some_and(|guard| free_names(&guard.node).contains(reason));
    let statements = match &clause.body.node {
        Expr::Block(statements) => statements.as_slice(),
        _ => std::slice::from_ref(&clause.body),
    };
    guard_reads
        || statements.iter().any(|statement| {
            !reraises(statement, &clause.kind.node, reason) && free_names(&statement.node).contains(reason)
        })
}

/// `__rethrow__(kind, reason)`, over the clause's own kind and reason.
fn reraises(statement: &Spanned<Expr>, kind: &Pattern, reason: &Var) -> bool {
    let Expr::Call(callee, args) = &statement.node else {
        return false;
    };
    let (Pattern::Var(kind), [raised_kind, raised]) = (kind, args.as_slice()) else {
        return false;
    };
    let is_var = |expr: &Spanned<Expr>, var: &Var| matches!(&expr.node, Expr::Var(read) if read == var);
    rethrows(&callee.node) && is_var(raised_kind, kind) && is_var(raised, reason)
}

pub(super) struct Build {
    span: Span,
}

impl Build {
    pub(super) fn new(span: Span) -> Self {
        Self { span }
    }

    fn expr(&self, expr: Expr) -> Spanned<Expr> {
        Spanned::new(expr, self.span)
    }

    fn var(&self, var: &Var) -> Spanned<Expr> {
        self.expr(Expr::Var(var.clone()))
    }

    fn library_call(&self, names: &SubjectNames, function: &str, args: Vec<Spanned<Expr>>) -> Spanned<Expr> {
        let callee = Expr::Index(
            Box::new(self.var(&names.library)),
            Box::new(self.expr(Expr::Atom(function.to_string()))),
        );
        self.expr(Expr::Call(Box::new(self.expr(callee)), args))
    }

    /// The reason a `catch` clause reads: `Exception.__reason__(kind, raised)`.
    pub(super) fn reason(&self, names: &SubjectNames) -> Spanned<Expr> {
        self.library_call(
            names,
            "__reason__",
            vec![self.var(&names.kind), self.var(&names.raised)],
        )
    }
}
