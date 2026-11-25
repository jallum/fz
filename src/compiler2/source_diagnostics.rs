use crate::ast::TryForm;
use crate::diag::{Diagnostic, codes};
use crate::source::Span;

use super::quoted_surface::UngroupedClause;

/// A clause the compiler proves can never run, because an earlier clause
/// already matches everything that could reach it. Elixir raises the same
/// warning in the same words (module/types/pattern.ex:1594).
pub(crate) fn redundant_clause_diagnostic(clause_span: Span, always_matches_line: u32) -> Diagnostic {
    Diagnostic::warning(
        codes::TYPE_REDUNDANT_CLAUSE,
        format!("this clause cannot match because a previous clause at line {always_matches_line} always matches"),
        clause_span,
    )
    .with_label("unreachable")
}

/// A module name defined a second time. Elixir warns in these words at the
/// later definition and keeps it.
pub(crate) fn redefined_module_diagnostic(span: Span, module: &str) -> Diagnostic {
    Diagnostic::warning(
        codes::RESOLVE_MODULE_REDEFINED,
        format!("redefining module {module} (current version defined in memory)"),
        span,
    )
}

/// A clause of a name and arity written after another function's clause,
/// apart from the clauses written before it. Elixir warns in these words at
/// the later clause; when the clause before it has the same name and another
/// arity, the words leave out "and arity".
pub(crate) fn ungrouped_clause_diagnostic(clause: &UngroupedClause, first_file: &str, first_line: u32) -> Diagnostic {
    let same = if clause.follows_same_name {
        "name"
    } else {
        "name and arity (number of arguments)"
    };
    Diagnostic::warning(
        codes::RESOLVE_UNGROUPED_CLAUSES,
        format!(
            "clauses with the same {same} should be grouped together, \"{} {}/{}\" was previously defined ({first_file}:{first_line})",
            clause.head, clause.name, clause.arity
        ),
        clause.span,
    )
}

/// `@name` read where the module has not set it. Elixir warns in these words
/// and reads `nil`.
pub(crate) fn undefined_attribute_diagnostic(span: Span, name: &str) -> Diagnostic {
    Diagnostic::warning(
        codes::LOWER_UNDEFINED_ATTRIBUTE,
        format!(
            "undefined module attribute @{name}, please remove access to @{name} or explicitly set it before access"
        ),
        span,
    )
}

/// A `try` with an `else` and none of `rescue`, `catch` or `after`. Elixir
/// warns in these words, naming the form that wrote the `try`, and compiles
/// it as the `case` it is.
pub(crate) fn try_else_only_diagnostic(span: Span, form: TryForm) -> Diagnostic {
    Diagnostic::warning(
        codes::LOWER_TRY_ELSE_ONLY,
        format!(
            "\"else\" shouldn't be used as the only clause in \"{}\", use \"case\" instead",
            form.keyword()
        ),
        span,
    )
}

/// A `defimpl` that omits a callback its protocol declares. Elixir's
/// behaviour checker raises the same warning, in the same words, for a
/// `@behaviour` that skips a callback (`module/behaviour.ex:17`); this is
/// its protocol counterpart. When the implementation defines the same
/// name at a different arity, that arity is named too, since it is almost
/// always the answer the author is looking for.
pub(crate) fn protocol_missing_callback_diagnostic(
    span: Span,
    callback_name: &str,
    callback_arity: usize,
    protocol: &str,
    implementation: &str,
    other_arity: Option<usize>,
) -> Diagnostic {
    let diagnostic = Diagnostic::warning(
        codes::PROTOCOL_MISSING_CALLBACK,
        format!(
            "function {callback_name}/{callback_arity} required by protocol {protocol} is not implemented \
             (in module {implementation})"
        ),
        span,
    );
    match other_arity {
        Some(arity) => diagnostic.with_note(format!("{implementation} defines {callback_name}/{arity} instead")),
        None => diagnostic,
    }
}

/// A `defimpl` naming a module that exists but was never declared with
/// `defprotocol`. Elixir raises this exact wording, as an `ArgumentError`,
/// from `Protocol.assert_protocol!/1` (`lib/elixir/lib/protocol.ex`) when the
/// named module has no `__protocol__/1`.
pub(crate) fn not_a_protocol_diagnostic(span: Span, module: &str) -> Diagnostic {
    Diagnostic::error(
        codes::RESOLVE_NOT_A_PROTOCOL,
        format!("{module} is not a protocol"),
        span,
    )
}

#[cfg(test)]
#[path = "source_diagnostics_test.rs"]
mod source_diagnostics_test;
