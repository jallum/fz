//! What a decision raises when no row of its plan claims the subject.
//!
//! Every construct that decides between rows ends, in Elixir, in an exception
//! of its own: a function head in `FunctionClauseError`, `=` in `MatchError`,
//! `case` in `CaseClauseError` and so on. A plan carries that exception from
//! the moment it is built, so each backend lowers a `Fail` the same way for
//! every construct: build the exception and raise it.

use std::borrow::Cow;

/// What a plan does at a `Fail`: raise an exception worded the way Elixir
/// words it, or continue a raise that arrived.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LastResort {
    /// Raise a new exception.
    Exception {
        /// The exception module's atom, such as `Elixir.MatchError`.
        exception: Cow<'static, str>,
        /// The whole message, or the lead of a message that goes on to show
        /// the subject.
        message: String,
        /// Whether the message shows the plan's subject, its first input, on a
        /// line of its own after the lead.
        shows_subject: bool,
    },
    /// Continue the raise a handler was delivered, with the plan's first two
    /// inputs as its kind and value.
    Reraise,
}

impl LastResort {
    /// No head of `function` takes the arguments. `function` is the name
    /// Elixir gives it, such as `M.f/1` or `anonymous fn/1 in M.g/0`.
    pub(crate) fn function_clause(function: &str) -> Self {
        Self::fixed(
            "Elixir.FunctionClauseError",
            format!("no function clause matching in {function}"),
        )
    }

    /// The left side of `=` does not match the right.
    pub(crate) fn match_error() -> Self {
        Self::showing("Elixir.MatchError", "no match of right hand side value:")
    }

    /// No clause of a `case` matches.
    pub(crate) fn case_clause() -> Self {
        Self::showing("Elixir.CaseClauseError", "no case clause matching:")
    }

    /// No condition of a `cond` is truthy.
    pub(crate) fn cond_clause() -> Self {
        Self::fixed(
            "Elixir.CondClauseError",
            "no cond clause evaluated to a truthy value".to_string(),
        )
    }

    /// A `with` clause failed and no `else` clause matches what it returned.
    pub(crate) fn with_clause() -> Self {
        Self::showing("Elixir.WithClauseError", "no with clause matching:")
    }

    /// No `else` clause of a `try` matches the value its body produced.
    pub(crate) fn try_clause() -> Self {
        Self::showing("Elixir.TryClauseError", "no try clause matching:")
    }

    /// The left side of `and` or `or` is not a boolean.
    pub(crate) fn bad_boolean(operator: &str) -> Self {
        Self::showing(
            "Elixir.BadBooleanError",
            &format!("expected a boolean on left-side of \"{operator}\", got:"),
        )
    }

    /// `not` was given something other than a boolean.
    pub(crate) fn argument_error() -> Self {
        Self::fixed("Elixir.ArgumentError", "argument error".to_string())
    }

    /// Nothing in a handler's clauses takes the raise it was delivered, so it
    /// continues to the next handler out with the kind it arrived with.
    pub(crate) fn reraise() -> Self {
        Self::Reraise
    }

    /// The exception module's atom, for a last resort that raises one.
    pub(crate) fn exception(&self) -> Option<&str> {
        match self {
            Self::Exception { exception, .. } => Some(exception),
            Self::Reraise => None,
        }
    }

    /// The message, or its lead when the subject follows, for a last resort
    /// that raises an exception.
    #[cfg(test)]
    pub(crate) fn message(&self) -> Option<&str> {
        match self {
            Self::Exception { message, .. } => Some(message),
            Self::Reraise => None,
        }
    }

    /// How many of the plan's leading inputs the last resort reads: the
    /// subject a message shows, or the kind and value a re-raise continues
    /// with.
    pub(crate) fn consumed_inputs(&self) -> usize {
        match self {
            Self::Exception {
                shows_subject: true, ..
            } => 1,
            Self::Exception { .. } => 0,
            Self::Reraise => 2,
        }
    }

    /// The failure an extern declares with `raises:`: the exception it names,
    /// raised with the message the declaration gives.
    pub fn declared(exception: String, message: String) -> Self {
        Self::Exception {
            exception: Cow::Owned(exception),
            message,
            shows_subject: false,
        }
    }

    fn fixed(exception: &'static str, message: String) -> Self {
        Self::Exception {
            exception: Cow::Borrowed(exception),
            message,
            shows_subject: false,
        }
    }

    fn showing(exception: &'static str, lead: &str) -> Self {
        Self::Exception {
            exception: Cow::Borrowed(exception),
            message: lead.to_string(),
            shows_subject: true,
        }
    }
}

#[cfg(test)]
#[path = "last_resort_test.rs"]
mod last_resort_test;
