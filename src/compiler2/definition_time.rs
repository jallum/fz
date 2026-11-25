//! Code that runs while a module is being defined.
//!
//! Elixir runs a module's body when it defines the module. fz reads a body as
//! forms, and runs an expression in it only where a form needs a value, such
//! as a `defstruct` field list that calls something. Such an expression
//! becomes the body of a private macro of the module that escapes its value,
//! as `Macro.escape(expr)` does. Running that macro is running the expression
//! in the module's namespace as the walk has it, and what comes back is the
//! quoted code that rebuilds its value, ready to stand where the expression
//! stood. A definition with an `unquote` in it runs the same way, as the
//! `quote` of the definition: the macro's value is the definition with each
//! `unquote` replaced by its value.

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

/// What the evaluator's macro makes of the source it holds.
#[derive(Clone, Copy)]
pub(crate) enum Evaluation<'a> {
    /// The quoted code that rebuilds the value of the expression, by the
    /// library function that escapes it, given as its module and name.
    Escape(&'a str, &'a str),
    /// The quoted code of the source itself, with each `unquote` in it
    /// replaced by its value.
    Quote,
}

/// `defmacro <name>(), do: <what the evaluation makes>`, published as
/// private, and the call that runs it.
pub(crate) struct Evaluator {
    pub(crate) definition: QuotedSourceRoot,
    pub(crate) invocation: QuotedSourceRoot,
}

pub(crate) fn evaluator(
    expr: &QuotedSourceRoot,
    evaluation: Evaluation,
    name: &str,
    span: Span,
) -> Result<Evaluator, QuotedSourceError> {
    let builder = expr.builder();
    let meta = QuotedSourceMetadata {
        span: Some(span),
        ..QuotedSourceMetadata::default()
    };
    let body = match evaluation {
        Evaluation::Escape(module, function) => {
            let dot = builder.ast_node(
                builder.atom("."),
                &meta,
                builder.list(&[builder.atom(&format!("Elixir.{module}")), builder.atom(function)])?,
            )?;
            builder.call_callee(dot, &meta, &[expr.root()])?
        }
        Evaluation::Quote => {
            let quoted = builder.list(&[builder.keyword("do", expr.root())?])?;
            builder.call("quote", &meta, &[quoted])?
        }
    };
    let head = builder.call(name, &meta, &[])?;
    let do_kw = builder.list(&[builder.keyword("do", body)?])?;
    let clause = builder.call("defmacro", &meta, &[head, do_kw])?;
    Ok(Evaluator {
        definition: expr.subroot(builder.list(&[clause])?),
        invocation: expr.subroot(builder.call(name, &meta, &[])?),
    })
}
