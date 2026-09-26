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

#[cfg(test)]
#[path = "source_diagnostics_test.rs"]
mod source_diagnostics_test;
