//! What a decision raises when no row of its plan claims the subject.
//!
//! Every construct that decides between rows ends, in Elixir, in an exception
//! of its own: a function head in `FunctionClauseError`, `=` in `MatchError`,
//! `case` in `CaseClauseError` and so on. A plan carries that exception from
//! the moment it is built, so each backend lowers a `Fail` the same way for
//! every construct: build the exception from its fields and raise it.

use std::borrow::Cow;

/// What one field of a raised exception holds.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FieldTerm {
    /// The plan's subject, its first input.
    Subject,
    /// An atom, by name.
    Atom(Cow<'static, str>),
    /// An integer.
    Int(i64),
    /// A binary of text.
    Text(String),
}

impl FieldTerm {
    const NIL: Self = Self::Atom(Cow::Borrowed("nil"));
}

/// What a plan does at a `Fail`: raise an exception carrying the fields
/// Elixir gives it, or continue a raise that arrived. The exception's module
/// words its message from those fields when one is asked for.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LastResort {
    /// Raise a new exception.
    Exception {
        /// The exception module's atom, such as `Elixir.MatchError`.
        exception: Cow<'static, str>,
        /// Every field of the exception's struct, in the order it declares
        /// them, with what each holds.
        fields: Vec<(&'static str, FieldTerm)>,
    },
    /// Continue the raise a handler was delivered, with the plan's first two
    /// inputs as its kind and value.
    Reraise,
}

impl LastResort {
    /// No head of the function takes the arguments. `module` is the atom of
    /// the module that defines it, when one does, and `function` the name
    /// Elixir gives it: its own, or `-f/1-fun-0-` for a lambda inside `f/1`.
    pub(crate) fn function_clause(module: Option<String>, function: String, arity: u32) -> Self {
        Self::raising(
            "Elixir.FunctionClauseError",
            vec![
                (
                    "module",
                    module.map_or(FieldTerm::NIL, |module| FieldTerm::Atom(Cow::Owned(module))),
                ),
                ("function", FieldTerm::Atom(Cow::Owned(function))),
                ("arity", FieldTerm::Int(i64::from(arity))),
                ("kind", FieldTerm::NIL),
                ("args", FieldTerm::NIL),
                ("clauses", FieldTerm::NIL),
            ],
        )
    }

    /// The left side of `=` does not match the right.
    pub(crate) fn match_error() -> Self {
        Self::about_the_subject("Elixir.MatchError")
    }

    /// No implementation of the protocol whose atom is `protocol` takes the
    /// receiver.
    pub(crate) fn protocol_undefined(protocol: String) -> Self {
        Self::raising(
            "Elixir.Protocol.UndefinedError",
            vec![
                ("protocol", FieldTerm::Atom(Cow::Owned(protocol))),
                ("value", FieldTerm::Subject),
                ("message", FieldTerm::NIL),
                ("description", FieldTerm::Text(String::new())),
            ],
        )
    }

    /// No clause of a `case` matches.
    pub(crate) fn case_clause() -> Self {
        Self::about_the_subject("Elixir.CaseClauseError")
    }

    /// No condition of a `cond` is truthy.
    pub(crate) fn cond_clause() -> Self {
        Self::raising("Elixir.CondClauseError", Vec::new())
    }

    /// A `with` clause failed and no `else` clause matches what it returned.
    pub(crate) fn with_clause() -> Self {
        Self::about_the_subject("Elixir.WithClauseError")
    }

    /// No `else` clause of a `try` matches the value its body produced.
    pub(crate) fn try_clause() -> Self {
        Self::about_the_subject("Elixir.TryClauseError")
    }

    /// The left side of `and` or `or` is not a boolean.
    pub(crate) fn bad_boolean(operator: &'static str) -> Self {
        Self::raising(
            "Elixir.BadBooleanError",
            vec![
                ("term", FieldTerm::Subject),
                ("operator", FieldTerm::Atom(Cow::Borrowed(operator))),
            ],
        )
    }

    /// `not` was given something other than a boolean.
    pub(crate) fn argument_error() -> Self {
        Self::declared("Elixir.ArgumentError".to_string(), "argument error".to_string())
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

    /// Every atom the raised exception is built from: its module's, each
    /// field's key, and each field value that is an atom.
    pub(crate) fn atoms(&self) -> impl Iterator<Item = &str> {
        let (exception, fields) = match self {
            Self::Exception { exception, fields } => (Some(exception.as_ref()), fields.as_slice()),
            Self::Reraise => (None, [].as_slice()),
        };
        let of_fields = fields.iter().flat_map(|(key, term)| {
            let value = match term {
                FieldTerm::Atom(name) => Some(name.as_ref()),
                FieldTerm::Subject | FieldTerm::Int(_) | FieldTerm::Text(_) => None,
            };
            std::iter::once(*key).chain(value)
        });
        exception.into_iter().chain(of_fields)
    }

    /// How many of the plan's leading inputs the last resort reads: the
    /// subject an exception carries, or the kind and value a re-raise
    /// continues with.
    pub(crate) fn consumed_inputs(&self) -> usize {
        match self {
            Self::Exception { fields, .. } => usize::from(fields.iter().any(|(_, term)| *term == FieldTerm::Subject)),
            Self::Reraise => 2,
        }
    }

    /// The failure an extern declares with `raises:`: the exception it names,
    /// raised with the message the declaration gives.
    pub fn declared(exception: String, message: String) -> Self {
        Self::Exception {
            exception: Cow::Owned(exception),
            fields: vec![("message", FieldTerm::Text(message))],
        }
    }

    fn raising(exception: &'static str, fields: Vec<(&'static str, FieldTerm)>) -> Self {
        Self::Exception {
            exception: Cow::Borrowed(exception),
            fields,
        }
    }

    fn about_the_subject(exception: &'static str) -> Self {
        Self::raising(exception, vec![("term", FieldTerm::Subject)])
    }
}

#[cfg(test)]
#[path = "last_resort_test.rs"]
mod last_resort_test;
