//! What a decision raises when no row of its plan claims the subject.
//!
//! Every construct that decides between rows ends, in Elixir, in an exception
//! of its own: a function head in `FunctionClauseError`, `=` in `MatchError`,
//! `case` in `CaseClauseError` and so on. A plan carries that exception from
//! the moment it is built, so each backend lowers a `Fail` the same way for
//! every construct: build the struct of the exception's module and raise it.
//! A last resort names only the fields it sets; the module's declaration gives
//! the rest, in its order, each holding its default.

use std::borrow::Cow;

use crate::ground_value::GroundValue;
use crate::literal_term::LiteralTerm;

/// What one field of a raised exception, or one element of its reason, holds.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FieldTerm {
    /// The plan's subject, its first input.
    Subject,
    /// A value written out in full.
    Literal(LiteralTerm),
}

impl FieldTerm {
    fn atom(name: impl Into<String>) -> Self {
        Self::Literal(LiteralTerm::Ground(GroundValue::Atom(name.into())))
    }

    fn text(text: impl Into<String>) -> Self {
        Self::Literal(LiteralTerm::Ground(GroundValue::Binary(text.into().into_bytes())))
    }
}

/// What a raised struct holds in one field of its declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RaisedField<'a> {
    /// The plan's subject, its first input.
    Subject,
    /// A value written out in full: one the last resort sets, or the
    /// field's default.
    Literal(&'a LiteralTerm),
}

/// The Erlang reason a failure raises beside its exception, which a `catch`
/// binds where a `rescue` binds the exception: an atom, or a tuple whose
/// elements are written out or are the plan's subject.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ReasonTerm {
    /// An atom such as `:badarg`.
    Atom(Cow<'static, str>),
    /// A tuple such as `{:badmatch, subject}`.
    Tuple(Vec<FieldTerm>),
}

impl ReasonTerm {
    /// The reason `{tag, subject}`: an atom tagging the plan's subject.
    fn tagged_subject(tag: &'static str) -> Self {
        Self::Tuple(vec![FieldTerm::atom(tag), FieldTerm::Subject])
    }

    fn uses_subject(&self) -> bool {
        matches!(self, Self::Tuple(elements) if elements.contains(&FieldTerm::Subject))
    }
}

/// What a plan does at a `Fail`: raise a struct of an exception's module, or
/// continue a raise that arrived. The exception's module words its message
/// from its fields when one is asked for.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LastResort {
    /// Raise a new exception.
    Exception {
        /// The exception module's atom, such as `Elixir.MatchError`.
        exception: Cow<'static, str>,
        /// The fields this failure sets, with what each holds. Every other
        /// field of the exception's struct holds its default.
        fields: Vec<(Cow<'static, str>, FieldTerm)>,
        /// The Erlang reason a `catch` binds, when the failure has one. A
        /// raise without one has the exception itself for its reason.
        reason: Option<ReasonTerm>,
    },
    /// Continue the raise a handler was delivered, with the plan's first
    /// three inputs as its kind, value and reason.
    Reraise,
    /// Raise an error whose value and Erlang reason are the plan's first two
    /// inputs.
    Raise,
}

impl LastResort {
    /// No head of the function takes the arguments. `module` is the atom of
    /// the module that defines it, when one does, and `function` the name
    /// Elixir gives it: its own, or `-f/1-fun-0-` for a lambda inside `f/1`.
    pub(crate) fn function_clause(module: Option<String>, function: String, arity: u32) -> Self {
        Self::raising(
            "Elixir.FunctionClauseError",
            vec![
                ("function", FieldTerm::atom(function)),
                (
                    "arity",
                    FieldTerm::Literal(LiteralTerm::Ground(GroundValue::Int(i64::from(arity)))),
                ),
            ]
            .into_iter()
            .chain(module.map(|module| ("module", FieldTerm::atom(module))))
            .collect(),
            Some(ReasonTerm::Atom(Cow::Borrowed("function_clause"))),
        )
    }

    /// The left side of `=` does not match the right.
    pub(crate) fn match_error() -> Self {
        Self::about_the_subject("Elixir.MatchError", "badmatch")
    }

    /// No implementation of the protocol whose atom is `protocol` takes the
    /// receiver.
    pub(crate) fn protocol_undefined(protocol: String) -> Self {
        Self::raising(
            "Elixir.Protocol.UndefinedError",
            vec![("protocol", FieldTerm::atom(protocol)), ("value", FieldTerm::Subject)],
            None,
        )
    }

    /// No clause of a `case` matches.
    pub(crate) fn case_clause() -> Self {
        Self::about_the_subject("Elixir.CaseClauseError", "case_clause")
    }

    /// No condition of a `cond` is truthy.
    pub(crate) fn cond_clause() -> Self {
        Self::raising(
            "Elixir.CondClauseError",
            Vec::new(),
            Some(ReasonTerm::Atom(Cow::Borrowed("cond_clause"))),
        )
    }

    /// A `with` clause failed and no `else` clause matches what it returned.
    pub(crate) fn with_clause() -> Self {
        Self::about_the_subject("Elixir.WithClauseError", "else_clause")
    }

    /// No `else` clause of a `try` matches the value its body produced.
    pub(crate) fn try_clause() -> Self {
        Self::about_the_subject("Elixir.TryClauseError", "try_clause")
    }

    /// The left side of `and` or `or` is not a boolean.
    pub(crate) fn bad_boolean(operator: &'static str) -> Self {
        Self::raising(
            "Elixir.BadBooleanError",
            vec![("term", FieldTerm::Subject), ("operator", FieldTerm::atom(operator))],
            Some(ReasonTerm::Tuple(vec![
                FieldTerm::atom("badbool"),
                FieldTerm::atom(operator),
                FieldTerm::Subject,
            ])),
        )
    }

    /// `not` was given something other than a boolean.
    pub(crate) fn argument_error() -> Self {
        Self::raising(
            "Elixir.ArgumentError",
            Vec::new(),
            Some(ReasonTerm::Atom(Cow::Borrowed("badarg"))),
        )
    }

    /// Nothing in a handler's clauses takes the raise it was delivered, so it
    /// continues to the next handler out with the kind it arrived with.
    pub(crate) fn reraise() -> Self {
        Self::Reraise
    }

    /// A raise whose value and Erlang reason are both written where it is
    /// raised: the plan's first two inputs.
    pub(crate) fn raise() -> Self {
        Self::Raise
    }

    /// The exception module's atom, for a last resort that raises one.
    pub(crate) fn exception(&self) -> Option<&str> {
        match self {
            Self::Exception { exception, .. } => Some(exception),
            Self::Reraise | Self::Raise => None,
        }
    }

    /// The reason a `catch` binds for this failure, when it declares one.
    pub(crate) fn reason(&self) -> Option<&ReasonTerm> {
        match self {
            Self::Exception { reason, .. } => reason.as_ref(),
            Self::Reraise | Self::Raise => None,
        }
    }

    /// Every atom the fields this failure sets, and its reason, write.
    pub(crate) fn atoms(&self) -> impl Iterator<Item = String> {
        let mut atoms = Vec::new();
        if let Self::Exception { fields, reason, .. } = self {
            let reasons = match reason {
                Some(ReasonTerm::Atom(name)) => vec![FieldTerm::atom(name.to_string())],
                Some(ReasonTerm::Tuple(elements)) => elements.clone(),
                None => Vec::new(),
            };
            for term in fields.iter().map(|(_, term)| term).chain(&reasons) {
                if let FieldTerm::Literal(literal) = term {
                    literal.each_ground(&mut |value| atoms.extend(atom_name(value).map(str::to_owned)));
                }
            }
        }
        atoms.into_iter()
    }

    /// What each field of the raised struct holds, given the fields its
    /// exception declares in order and the default of each: what this
    /// failure sets, or the default. A failure that sets a field the
    /// exception does not declare has no struct to raise, and the error
    /// names the field. So does a field that holds a function: a backend
    /// builds the struct from written values, and a function is compiled
    /// code.
    pub(crate) fn struct_fields<'a>(
        &'a self,
        declared: &'a [String],
        defaults: &'a [LiteralTerm],
    ) -> Result<Vec<(&'a str, RaisedField<'a>)>, String> {
        let Self::Exception { exception, fields, .. } = self else {
            return Err("a raise of written values builds no struct".to_string());
        };
        if let Some((stray, _)) = fields
            .iter()
            .find(|(name, _)| !declared.iter().any(|field| field == name))
        {
            return Err(format!("exception `{exception}` declares no field `{stray}`"));
        }
        declared
            .iter()
            .zip(defaults)
            .map(|(field, default)| {
                let set = fields.iter().find(|(name, _)| name == field);
                let held = match set {
                    Some((_, FieldTerm::Subject)) => RaisedField::Subject,
                    Some((_, FieldTerm::Literal(value))) => RaisedField::Literal(value),
                    None => RaisedField::Literal(default),
                };
                match held {
                    RaisedField::Literal(term) if term.holds_a_function() => Err(format!(
                        "exception `{exception}` holds a function in its field `{field}`, which a backend cannot build"
                    )),
                    held => Ok((field.as_str(), held)),
                }
            })
            .collect()
    }

    /// How many of the plan's leading inputs the last resort reads: the
    /// subject an exception or its reason carries, the value and reason a
    /// raise writes, or the kind, value and reason a re-raise continues with.
    pub(crate) fn consumed_inputs(&self) -> usize {
        match self {
            Self::Exception { fields, reason, .. } => usize::from(
                fields.iter().any(|(_, term)| *term == FieldTerm::Subject)
                    || reason.as_ref().is_some_and(ReasonTerm::uses_subject),
            ),
            Self::Reraise => 3,
            Self::Raise => 2,
        }
    }

    /// The failure an extern declares with `raises:`: a struct of the
    /// exception it names, whose `message` is the declaration's text, and the
    /// Erlang reason the declaration names, when it names one.
    pub fn declared(exception: String, message: &str, reason: Option<&str>) -> Self {
        Self::Exception {
            exception: Cow::Owned(exception),
            fields: vec![(Cow::Borrowed("message"), FieldTerm::text(message))],
            reason: reason.map(|reason| ReasonTerm::Atom(Cow::Owned(reason.to_string()))),
        }
    }

    fn raising(exception: &'static str, fields: Vec<(&'static str, FieldTerm)>, reason: Option<ReasonTerm>) -> Self {
        Self::Exception {
            exception: Cow::Borrowed(exception),
            fields: fields
                .into_iter()
                .map(|(name, term)| (Cow::Borrowed(name), term))
                .collect(),
            reason,
        }
    }

    fn about_the_subject(exception: &'static str, reason_tag: &'static str) -> Self {
        Self::raising(
            exception,
            vec![("term", FieldTerm::Subject)],
            Some(ReasonTerm::tagged_subject(reason_tag)),
        )
    }
}

/// The atom `value` is at run time: `nil`, `true` and `false` are atoms.
pub(crate) fn atom_name(value: &GroundValue) -> Option<&str> {
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
