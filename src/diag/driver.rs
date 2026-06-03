//! fz-ndf.9 — diagnostics now flow through the telemetry bus:
//! - `report_through(tel, diags)` emits each diagnostic as a
//!   `[fz, diag, error|warning]` event with the `Diagnostic`
//!   in metadata. Printing is the renderer-handler's responsibility.

use super::diagnostic::{Diagnostic, Severity};
use super::render::Renderer;
use super::source_map::SourceMap;
use crate::telemetry::Telemetry;
use crate::telemetry::value::opaque;
use crate::telemetry::{Metadata, Value};
use std::process::exit;

/// Render one diagnostic into a deterministic, color-free string.
pub fn render_one_to_string(sm: &SourceMap, d: &Diagnostic) -> String {
    let renderer = Renderer::new(sm).with_color_disabled();
    let mut out = Vec::new();
    let _ = renderer.emit(d, &mut out);
    String::from_utf8(out).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
}

/// Emit each diagnostic as a telemetry event in the `[fz, diag, *]`
/// family. Printing is delegated to whatever renderer-handler the bus
/// has attached (typically `DiagRenderer`). No exit decision — callers
/// inspect the slice themselves or use `report_or_exit_through` which
/// combines emission with exit-on-error.
pub fn emit_through(tel: &dyn Telemetry, sm: Option<&SourceMap>, diags: &[Diagnostic]) {
    for d in diags {
        let (name, severity): (&'static [&'static str], &'static str) = match d.severity {
            Severity::Error => (&["fz", "diag", "error"], "error"),
            Severity::Warning => (&["fz", "diag", "warning"], "warning"),
        };
        let mut metadata = vec![
            ("severity", Value::from(severity)),
            ("code", Value::from(d.code.0)),
            ("message", Value::from(d.message.as_str())),
            ("diagnostic", opaque(d)),
        ];
        if let Some(sm) = sm {
            metadata.push(("source_map", opaque(sm)));
        }
        tel.event(name, Metadata::from_pairs(metadata));
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
    emit_through(tel, None, diags);
    if diags.iter().any(|d| d.severity == Severity::Error) {
        exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::Diagnostics;
    use crate::diag::diagnostic::DiagCode;
    use crate::diag::span::Span;
    use crate::telemetry::capture::vec_writer;
    use std::cell::RefCell;
    use std::rc::Rc;

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

        emit_through(&tel, None, &[warn.clone(), err.clone()]);

        assert_eq!(cap.count(&["fz", "diag", "warning"]), 1);
        assert_eq!(cap.count(&["fz", "diag", "error"]), 1);
        let w_ev = cap.last(&["fz", "diag", "warning"]).unwrap();
        assert!(w_ev.metadata.get("diagnostic").is_none());
        assert!(matches!(w_ev.metadata.get("code"), Some(Value::Str(_))));
        assert!(matches!(w_ev.metadata.get("message"), Some(Value::Str(_))));
    }

    #[test]
    fn report_or_exit_renders_byte_identical_to_direct_path() {
        // Build a small fixture, render via render_to_string (direct
        // path), then drive the new bus-routed path into a captured writer
        // and compare bytes.
        use crate::diag::style::ColorMode;
        use crate::telemetry::{ConfiguredTelemetry, DiagRenderer};

        let mut sm = SourceMap::new();
        let fid = sm.add_file("t.fz", "fn main(), do: :ok\n");
        let mut ds = Diagnostics::new();
        ds.push(Diagnostic::warning(DiagCode("test/w"), "headline", Span::new(fid, 0, 2)).with_label("here"));
        ds.push(Diagnostic::error(DiagCode("test/e"), "boom", Span::new(fid, 3, 5)));

        let expected = render_diagnostics_to_string(&sm, ds.as_slice());

        let (buf, w) = vec_writer();
        let sm_shared = Rc::new(RefCell::new(sm.clone()));
        let tel = ConfiguredTelemetry::new();
        tel.attach(
            &["fz", "diag"],
            Box::new(DiagRenderer::new_to_writer(sm_shared, w, ColorMode::Never)),
        );
        emit_through(&tel, None, ds.as_slice());
        let actual = String::from_utf8(buf.borrow().clone()).unwrap();
        assert_eq!(actual, expected);
    }

    fn render_diagnostics_to_string(sm: &SourceMap, diags: &[Diagnostic]) -> String {
        let renderer = Renderer::new(sm).with_color_disabled();
        let mut out = Vec::new();
        for diag in diags {
            renderer.emit(diag, &mut out).unwrap();
        }
        String::from_utf8(out).unwrap()
    }
}
