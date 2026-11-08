//! What a decision raises when no row of its plan claims the subject.
//!
//! Every construct that decides between rows ends, in Elixir, in an exception
//! of its own: a function head in `FunctionClauseError`, `=` in `MatchError`,
//! `case` in `CaseClauseError` and so on. A plan carries that exception from
//! the moment it is built, so each backend lowers a `Fail` the same way for
//! every construct: build the exception and raise it.

/// The exception a plan raises at a `Fail`, worded the way Elixir words it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct LastResort {
    /// The exception module's atom, such as `Elixir.MatchError`.
    pub(crate) exception: &'static str,
    /// The whole message, or the lead of a message that goes on to show the
    /// subject.
    pub(crate) message: String,
    /// Whether the message shows the plan's subject, its first input, on a
    /// line of its own after the lead.
    pub(crate) shows_subject: bool,
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

    fn fixed(exception: &'static str, message: String) -> Self {
        Self {
            exception,
            message,
            shows_subject: false,
        }
    }

    fn showing(exception: &'static str, lead: &str) -> Self {
        Self {
            exception,
            message: lead.to_string(),
            shows_subject: true,
        }
    }
}

#[cfg(test)]
#[path = "last_resort_test.rs"]
mod last_resort_test;
