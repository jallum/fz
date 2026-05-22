//! Top-level rendering helper. Every pipeline driver (main.rs, repl.rs,
//! test_runner.rs) goes through `render_to_stderr` so the renderer is the
//! single source of user-facing diagnostic text.
//!
//! fz-ndf.9 — diagnostics now flow through the telemetry bus:
//! - `report_through(tel, diags)` emits each diagnostic as a
//!   `[fz, diag, error|warning|note|help]` event with the `Diagnostic`
//!   in metadata. Printing is the renderer-handler's responsibility.
//! - `report_or_exit(diags, sm)` is preserved as a stable surface for
//!   callers that don't yet thread their own telemetry; it constructs
//!   a one-shot `ConfiguredTelemetry` with a `DiagRenderer` attached,
//!   routes through `report_through`, then exits on error severity.

use std::cell::RefCell;
use std::rc::Rc;

use super::diagnostic::{Diagnostic, Diagnostics, Severity};
use super::render::Renderer;
use super::source_map::SourceMap;
use crate::telemetry::{ConfiguredTelemetry, DiagRenderer, Measurements, Telemetry};

/// Render `diags` to stderr in the project's standard format. Color
/// auto-detected (`NO_COLOR` honored).
pub fn render_to_stderr(sm: &SourceMap, diags: &Diagnostics) {
    let renderer = Renderer::new(sm);
    let mut stderr = std::io::stderr().lock();
    let _ = renderer.emit_all(diags, &mut stderr);
}

/// Render diagnostics into a deterministic, color-free string. This is
/// the same user-facing format as stderr, just without terminal policy.
pub fn render_to_string(sm: &SourceMap, diags: &Diagnostics) -> String {
    let renderer = Renderer::new(sm).with_color_disabled();
    let mut out = Vec::new();
    let _ = renderer.emit_all(diags, &mut out);
    String::from_utf8(out).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
}

/// Render one diagnostic into a deterministic, color-free string.
pub fn render_one_to_string(sm: &SourceMap, d: &Diagnostic) -> String {
    let renderer = Renderer::new(sm).with_color_disabled();
    let mut out = Vec::new();
    let _ = renderer.emit(d, &mut out);
    String::from_utf8(out).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
}

/// Render a single diagnostic to stderr.
pub fn render_one_to_stderr(sm: &SourceMap, d: &Diagnostic) {
    let renderer = Renderer::new(sm);
    let mut stderr = std::io::stderr().lock();
    let _ = renderer.emit(d, &mut stderr);
}

/// Emit each diagnostic as a telemetry event in the `[fz, diag, *]`
/// family. Printing is delegated to whatever renderer-handler the bus
/// has attached (typically `DiagRenderer`). No exit decision — callers
/// inspect the slice themselves or use `report_or_exit` which combines
/// emission with exit-on-error.
pub fn report_through(tel: &dyn Telemetry, diags: &[Diagnostic]) {
    for d in diags {
        let name: &'static [&'static str] = match d.severity {
            Severity::Error => &["fz", "diag", "error"],
            Severity::Warning => &["fz", "diag", "warning"],
            Severity::Note => &["fz", "diag", "note"],
            Severity::Help => &["fz", "diag", "help"],
        };
        let md = crate::metadata! { diagnostic: d.clone() };
        tel.execute(name, &Measurements::new(), &md);
    }
}

/// Render every diagnostic to stderr; if any is an error, exit(1)
/// after rendering. Warnings render and the function returns normally.
///
/// fz-ndf.9 — internally constructs a one-shot `ConfiguredTelemetry`
/// with a `DiagRenderer` attached for stderr, then routes through
/// `report_through`. The user-facing behavior is unchanged byte-for-byte;
/// what changed is that diagnostics now flow through the unified bus.
/// (The `SourceMap` is cloned into the renderer — clone is cheap: file
/// bytes are `Arc<str>` so they're shared, and line indexes are at most
/// a couple of `Vec<u32>` per file.)
pub fn report_or_exit(diags: &[Diagnostic], sm: &SourceMap) {
    if diags.is_empty() {
        return;
    }
    let sm_shared = Rc::new(RefCell::new(sm.clone()));
    let tel = ConfiguredTelemetry::new();
    tel.attach(
        &["fz", "diag"],
        Box::new(DiagRenderer::new_stderr(sm_shared)),
    );
    report_through(&tel, diags);
    if diags.iter().any(|d| d.severity == Severity::Error) {
        std::process::exit(1);
    }
}

/// Same emission shape as `report_or_exit`, but the caller supplies the
/// telemetry. Use this from any code path that has already constructed
/// a bus (e.g. a long-lived driver bus); it skips the one-shot
/// construction and exits on error severity.
pub fn report_or_exit_through(tel: &dyn Telemetry, diags: &[Diagnostic]) {
    if diags.is_empty() {
        return;
    }
    report_through(tel, diags);
    if diags.iter().any(|d| d.severity == Severity::Error) {
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

    #[test]
    fn render_to_string_is_color_free_and_deterministic() {
        let mut sm = SourceMap::new();
        let fid = sm.add_file("test.fz", "fn main(), do: :ok\n");
        let mut ds = Diagnostics::new();
        ds.push(
            Diagnostic::warning(
                DiagCode("test/warning"),
                "test warning",
                Span::new(fid, 0, 2),
            )
            .with_label("here"),
        );
        let rendered = render_to_string(&sm, &ds);
        assert!(rendered.contains("warning[test/warning]: test warning"));
        assert!(rendered.contains("test.fz:1:1"));
        assert!(!rendered.contains("\x1b["));
    }

    // Note: testing the error-exit path requires either a subprocess
    // harness or refactoring the predicate out for in-process
    // verification. Both are out of scope here — the predicate is a
    // one-line `diags.iter().any(|d| d.severity == Severity::Error)`
    // and the exit call is the same `process::exit(1)` used at every
    // other fail-fast site.

    // -- fz-ndf.9 — telemetry seam --

    #[test]
    fn report_through_emits_event_per_diagnostic() {
        use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());

        let mut sm = SourceMap::new();
        let fid = sm.add_file("a.fz", "fn x(), do: :ok\n");
        let warn = Diagnostic::warning(DiagCode("a/w"), "warned", Span::new(fid, 0, 1));
        let err = Diagnostic::error(DiagCode("a/e"), "broken", Span::new(fid, 2, 3));

        report_through(&tel, &[warn.clone(), err.clone()]);

        assert_eq!(cap.count(&["fz", "diag", "warning"]), 1);
        assert_eq!(cap.count(&["fz", "diag", "error"]), 1);
        let w_ev = cap.last(&["fz", "diag", "warning"]).unwrap();
        assert!(matches!(
            w_ev.metadata.get("diagnostic"),
            Some(Value::Diagnostic(_))
        ));
    }

    #[test]
    fn report_through_event_name_matches_severity() {
        use crate::telemetry::{Capture, ConfiguredTelemetry};

        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());

        let d_note = Diagnostic {
            severity: Severity::Note,
            ..Diagnostic::warning(DiagCode("x/n"), "n", Span::DUMMY)
        };
        let d_help = Diagnostic {
            severity: Severity::Help,
            ..Diagnostic::warning(DiagCode("x/h"), "h", Span::DUMMY)
        };
        report_through(&tel, &[d_note, d_help]);
        assert_eq!(cap.count(&["fz", "diag", "note"]), 1);
        assert_eq!(cap.count(&["fz", "diag", "help"]), 1);
    }

    #[test]
    fn report_or_exit_renders_byte_identical_to_legacy_path() {
        // Build a small fixture, render via render_to_string (legacy direct
        // path), then drive the new bus-routed path into a captured writer
        // and compare bytes.
        use crate::diag::style::ColorMode;
        use crate::telemetry::{ConfiguredTelemetry, DiagRenderer};

        let mut sm = SourceMap::new();
        let fid = sm.add_file("t.fz", "fn main(), do: :ok\n");
        let mut ds = Diagnostics::new();
        ds.push(
            Diagnostic::warning(DiagCode("test/w"), "headline", Span::new(fid, 0, 2))
                .with_label("here"),
        );
        ds.push(Diagnostic::error(
            DiagCode("test/e"),
            "boom",
            Span::new(fid, 3, 5),
        ));

        let expected = render_to_string(&sm, &ds);

        let buf: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(Vec::new()));
        let sm_shared = Rc::new(RefCell::new(sm.clone()));
        let tel = ConfiguredTelemetry::new();
        tel.attach(
            &["fz", "diag"],
            Box::new(DiagRenderer::new_to_writer(
                sm_shared,
                buf.clone(),
                ColorMode::Never,
            )),
        );
        report_through(&tel, &ds.as_slice());
        let actual = String::from_utf8(buf.borrow().clone()).unwrap();
        assert_eq!(actual, expected);
    }
}
