//! Code that runs while a module is being defined.
//!
//! Elixir runs a module's body when it defines the module. fz reads a body as
//! forms, and runs an expression in it only where a form needs a value, such
//! as a `defstruct` field list that calls something. Such an expression
//! becomes the body of a private macro of the module that escapes its value,
//! as `Macro.escape(expr)` does. Running that macro is running the expression
//! in the module's namespace as the walk has it, and what comes back is the
//! quoted code that rebuilds its value, ready to stand where the expression
//! stood.

use crate::source::Span;

use super::drive::JobEffects;
use super::source::{QuotedSourceError, QuotedSourceMetadata, QuotedSourceRoot};

/// A value the walk has, or the waits it needs before it can have it.
pub(crate) enum Evaluated<T> {
    Value(T),
    Blocked(Box<JobEffects>),
}

/// The name of the macro that evaluates the `ordinal`-th definition-time
/// expression of a module. A name no source can write, so it shadows nothing.
pub(crate) fn evaluator_name(ordinal: usize) -> String {
    format!("{EVALUATOR_PREFIX}{ordinal}__")
}

/// Whether `name` is an evaluator's. An evaluator stands for an expression
/// the source wrote, so a diagnostic points at that expression and never
/// names the evaluator.
pub(crate) fn is_evaluator_name(name: &str) -> bool {
    name.starts_with(EVALUATOR_PREFIX)
}

const EVALUATOR_PREFIX: &str = "__definition_time_";

/// `defmacro <name>(), do: <escape>(<expr>)`, published as private, and the
/// call that runs it. `escape` is the library function, given as its module
/// and name, that turns the value into quoted code.
pub(crate) struct Evaluator {
    pub(crate) definition: QuotedSourceRoot,
    pub(crate) invocation: QuotedSourceRoot,
}

pub(crate) fn evaluator(
    expr: &QuotedSourceRoot,
    escape: (&str, &str),
    name: &str,
    span: Span,
) -> Result<Evaluator, QuotedSourceError> {
    let (module, function) = escape;
    let builder = expr.builder();
    let meta = QuotedSourceMetadata {
        span: Some(span),
        ..QuotedSourceMetadata::default()
    };
    let dot = builder.ast_node(
        builder.atom("."),
        &meta,
        builder.list(&[builder.atom(&format!("Elixir.{module}")), builder.atom(function)])?,
    )?;
    let body = builder.call_callee(dot, &meta, &[expr.root()])?;
    let head = builder.call(name, &meta, &[])?;
    let do_kw = builder.list(&[builder.keyword("do", body)?])?;
    let clause = builder.call("defmacro", &meta, &[head, do_kw])?;
    Ok(Evaluator {
        definition: expr.subroot(builder.list(&[clause])?),
        invocation: expr.subroot(builder.call(name, &meta, &[])?),
    })
}
