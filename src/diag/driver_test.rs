use super::*;
use crate::diag::Diagnostics;
use crate::diag::diagnostic::DiagCode;
use crate::diag::render::Renderer;
use crate::source::{SourceMap, Span};
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
    use crate::telemetry::{Capture, ConfiguredTelemetry};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    cap.install(&tel, &[]);
    let observed = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&observed);
    tel.attach_raw_event1::<Diagnostic, _>(&["fz", "diag"], move |_, _, _, diagnostic| {
        sink.borrow_mut()
            .push((diagnostic.severity, diagnostic.code.0, diagnostic.message.clone()));
    });

    let mut sm = SourceMap::new();
    let fid = sm.add_code(Some("a.fz"), "fn x(), do: :ok\n");
    let warn = Diagnostic::warning(DiagCode("a/w"), "warned", Span::new(fid, 0, 1));
    let err = Diagnostic::error(DiagCode("a/e"), "broken", Span::new(fid, 2, 3));

    emit_through(&tel, &[warn, err]);

    assert_eq!(cap.count(&["fz", "diag", "warning"]), 1);
    assert_eq!(cap.count(&["fz", "diag", "error"]), 1);
    let w_ev = cap.last(&["fz", "diag", "warning"]).unwrap();
    assert!(w_ev.metadata.get("diagnostic").is_none());
    assert_eq!(
        observed.borrow().as_slice(),
        &[
            (Severity::Warning, "a/w", "warned".to_string()),
            (Severity::Error, "a/e", "broken".to_string()),
        ]
    );
}

#[test]
fn report_or_exit_renders_byte_identical_to_direct_path() {
    // Build a small fixture, render via render_to_string (direct
    // path), then drive the new bus-routed path into a captured writer
    // and compare bytes.
    use crate::diag::style::ColorMode;
    use crate::telemetry::{ConfiguredTelemetry, diag_render::DiagRenderer};

    let mut sm = SourceMap::new();
    let fid = sm.add_code(Some("t.fz"), "fn main(), do: :ok\n");
    let mut ds = Diagnostics::new();
    ds.push(Diagnostic::warning(DiagCode("test/w"), "headline", Span::new(fid, 0, 2)).with_label("here"));
    ds.push(Diagnostic::error(DiagCode("test/e"), "boom", Span::new(fid, 3, 5)));

    let expected = render_diagnostics_to_string(&sm, ds.as_slice());

    let (buf, w) = vec_writer();
    let sm_shared = Rc::new(RefCell::new(sm.clone()));
    let tel = ConfiguredTelemetry::new();
    DiagRenderer::new_to_writer(sm_shared, w, ColorMode::Never).install(&tel);
    emit_through(&tel, ds.as_slice());
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
