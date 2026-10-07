use crate::diag::{Diagnostic, codes};
use crate::source::Span;

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
