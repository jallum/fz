//! Top-level rendering helper. Every pipeline driver (main.rs, repl.rs,
//! test_runner.rs) goes through `render_to_stderr` so the renderer is the
//! single source of user-facing diagnostic text.

use super::diagnostic::{Diagnostic, Diagnostics, Severity};
use super::render::Renderer;
use super::source_map::SourceMap;

/// Render `diags` to stderr in the project's standard format. Color
/// auto-detected (`NO_COLOR` honored).
pub fn render_to_stderr(sm: &SourceMap, diags: &Diagnostics) {
    let renderer = Renderer::new(sm);
    let mut stderr = std::io::stderr().lock();
    let _ = renderer.emit_all(diags, &mut stderr);
}

/// Render a single diagnostic to stderr.
pub fn render_one_to_stderr(sm: &SourceMap, d: &Diagnostic) {
    let renderer = Renderer::new(sm);
    let mut stderr = std::io::stderr().lock();
    let _ = renderer.emit(d, &mut stderr);
}

/// Render every diagnostic to stderr; if any is an error, exit(1)
/// after rendering. Warnings render and the function returns normally.
///
/// fz-0z4.5 — shared sink for the analysis/presentation/control-flow
/// split: pure check functions return `Vec<Diagnostic>`; this is the
/// one place that decides "render + maybe halt." Replaces the
/// hand-rolled render+exit pattern at every front-end gate.
pub fn report_or_exit(diags: &[Diagnostic], sm: &SourceMap) {
    if diags.is_empty() {
        return;
    }
    let renderer = Renderer::new(sm);
    let mut stderr = std::io::stderr().lock();
    for d in diags {
        let _ = renderer.emit(d, &mut stderr);
    }
    if diags.iter().any(|d| d.severity == Severity::Error) {
        drop(stderr);
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::diagnostic::DiagCode;
    use crate::diag::span::Span;

    #[test]
    fn empty_diags_returns_normally() {
        let sm = SourceMap::new();
        report_or_exit(&[], &sm);
        // If we reach this line, the function did not exit.
    }

    #[test]
    fn warnings_only_returns_normally() {
        let sm = SourceMap::new();
        let d = Diagnostic::warning(DiagCode("W0001"), "test warning", Span::DUMMY);
        report_or_exit(&[d], &sm);
        // Warnings print but do not halt.
    }

    // Note: testing the error-exit path requires either a subprocess
    // harness or refactoring the predicate out for in-process
    // verification. Both are out of scope here — the predicate is a
    // one-line `diags.iter().any(|d| d.severity == Severity::Error)`
    // and the exit call is the same `process::exit(1)` used at every
    // other fail-fast site.
}
