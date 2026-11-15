//! What a decision raises when no row of its plan claims the subject.
//!
//! Every construct that decides between rows ends, in Elixir, in an exception
//! of its own: a function head in `FunctionClauseError`, `=` in `MatchError`,
//! `case` in `CaseClauseError` and so on. A plan carries that exception from
//! the moment it is built, so each backend lowers a `Fail` the same way for
//! every construct: build the exception from its fields and raise it.

use std::borrow::Cow;

use crate::ground_value::GroundValue;
use crate::literal_term::LiteralTerm;

/// What one field of a raised exception holds.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FieldTerm {
    /// The plan's subject, its first input.
    Subject,
    /// A value written out in full.
    Literal(LiteralTerm),
}

impl FieldTerm {
    const NIL: Self = Self::Literal(LiteralTerm::Ground(GroundValue::Nil));

    fn atom(name: impl Into<String>) -> Self {
        Self::Literal(LiteralTerm::Ground(GroundValue::Atom(name.into())))
    }

    fn text(text: impl Into<String>) -> Self {
        Self::Literal(LiteralTerm::Ground(GroundValue::Binary(text.into().into_bytes())))
    }
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
        fields: Vec<(Cow<'static, str>, FieldTerm)>,
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
                ("module", module.map_or(FieldTerm::NIL, FieldTerm::atom)),
                ("function", FieldTerm::atom(function)),
                (
                    "arity",
                    FieldTerm::Literal(LiteralTerm::Ground(GroundValue::Int(i64::from(arity)))),
                ),
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
                ("protocol", FieldTerm::atom(protocol)),
                ("value", FieldTerm::Subject),
                ("message", FieldTerm::NIL),
                ("description", FieldTerm::text("")),
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
            vec![("term", FieldTerm::Subject), ("operator", FieldTerm::atom(operator))],
        )
    }

    /// `not` was given something other than a boolean.
    pub(crate) fn argument_error() -> Self {
        Self::raising(
            "Elixir.ArgumentError",
            vec![("message", FieldTerm::text("argument error"))],
        )
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
    /// field's key, and each atom a field's value writes.
    pub(crate) fn atoms(&self) -> impl Iterator<Item = &str> {
        let mut atoms = Vec::new();
        if let Self::Exception { exception, fields } = self {
            atoms.push(exception.as_ref());
            for (key, term) in fields {
                atoms.push(key.as_ref());
                if let FieldTerm::Literal(literal) = term {
                    literal.each_ground(&mut |value| atoms.extend(atom_name(value)));
                }
            }
        }
        atoms.into_iter()
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

    /// The failure an extern declares with `raises:`: a struct of the
    /// exception it names, each field holding what `fields` gives it.
    pub fn declared(exception: String, fields: Vec<(String, LiteralTerm)>) -> Self {
        Self::Exception {
            exception: Cow::Owned(exception),
            fields: fields
                .into_iter()
                .map(|(name, value)| (Cow::Owned(name), FieldTerm::Literal(value)))
                .collect(),
        }
    }

    fn raising(exception: &'static str, fields: Vec<(&'static str, FieldTerm)>) -> Self {
        Self::Exception {
            exception: Cow::Borrowed(exception),
            fields: fields
                .into_iter()
                .map(|(name, term)| (Cow::Borrowed(name), term))
                .collect(),
        }
    }

    fn about_the_subject(exception: &'static str) -> Self {
        Self::raising(exception, vec![("term", FieldTerm::Subject)])
    }
}

/// The atom `value` is at run time: `nil`, `true` and `false` are atoms.
fn atom_name(value: &GroundValue) -> Option<&str> {
    match value {
        GroundValue::Atom(name) => Some(name),
        GroundValue::Nil => Some("nil"),
        GroundValue::Bool(true) => Some("true"),
        GroundValue::Bool(false) => Some("false"),
        GroundValue::Int(_) | GroundValue::Float(_) | GroundValue::Binary(_) | GroundValue::Utf8Binary(_) => None,
    }
}

#[cfg(test)]
#[path = "last_resort_test.rs"]
mod last_resort_test;
