//! Top-level rendering helper. Every pipeline driver (main.rs, repl.rs,
//! test_runner.rs) goes through `render_to_stderr` so the renderer is the
//! single source of user-facing diagnostic text.

use super::diagnostic::{Diagnostic, Diagnostics};
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
