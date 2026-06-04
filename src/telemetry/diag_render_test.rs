use super::*;
use crate::diag::diagnostic::{DiagCode, Diagnostic, Diagnostics};
use crate::diag::render::Renderer;
use crate::diag::span::{FileId, Span};
use crate::metadata;
use crate::telemetry::bus::ConfiguredTelemetry;
use crate::telemetry::capture::vec_writer;
use crate::telemetry::sink::Telemetry;
use crate::telemetry::value::opaque;

fn fixture() -> (Rc<RefCell<SourceMap>>, FileId) {
    let mut sm = SourceMap::new();
    let fid = sm.add_file("test.fz", "fn main(), do: :ok\n");
    (Rc::new(RefCell::new(sm)), fid)
}

#[test]
fn renders_warning_identically_to_render_to_string() {
    let (sm, fid) = fixture();
    let (buf, w) = vec_writer();
    let t = ConfiguredTelemetry::new();
    t.attach(
        &["fz", "diag"],
        Box::new(DiagRenderer::new_to_writer(sm.clone(), w, ColorMode::Never)),
    );

    let d = Diagnostic::warning(DiagCode("test/warning"), "test warning", Span::new(fid, 0, 2)).with_label("here");
    t.event(&["fz", "diag", "warning"], metadata! { diagnostic: opaque(&d) });

    let actual = String::from_utf8(buf.borrow().clone()).unwrap();
    let expected = render_diagnostics_to_string(&sm.borrow(), &Diagnostics::from_one(d));
    assert_eq!(actual, expected);
}

#[test]
fn renders_error_identically_to_render_to_string() {
    let (sm, fid) = fixture();
    let (buf, w) = vec_writer();
    let t = ConfiguredTelemetry::new();
    t.attach(
        &["fz", "diag"],
        Box::new(DiagRenderer::new_to_writer(sm.clone(), w, ColorMode::Never)),
    );

    let d = Diagnostic::error(DiagCode("test/error"), "test error", Span::new(fid, 3, 7))
        .with_note("first note")
        .with_help("did you mean foo?");
    t.event(&["fz", "diag", "error"], metadata! { diagnostic: opaque(&d) });

    let actual = String::from_utf8(buf.borrow().clone()).unwrap();
    let expected = render_diagnostics_to_string(&sm.borrow(), &Diagnostics::from_one(d));
    assert_eq!(actual, expected);
}

#[test]
fn ignores_events_without_diagnostic_metadata() {
    let (sm, _fid) = fixture();
    let (buf, w) = vec_writer();
    let t = ConfiguredTelemetry::new();
    t.attach(&["fz"], Box::new(DiagRenderer::new_to_writer(sm, w, ColorMode::Never)));
    t.emit(&["fz", "lex", "tokens_built"]);
    assert!(buf.borrow().is_empty());
}

#[test]
fn multiple_diagnostics_concatenate_in_order() {
    let (sm, fid) = fixture();
    let (buf, w) = vec_writer();
    let t = ConfiguredTelemetry::new();
    t.attach(
        &["fz", "diag"],
        Box::new(DiagRenderer::new_to_writer(sm.clone(), w, ColorMode::Never)),
    );

    let d1 = Diagnostic::warning(DiagCode("a/1"), "first", Span::new(fid, 0, 1));
    let d2 = Diagnostic::error(DiagCode("a/2"), "second", Span::new(fid, 2, 3));
    t.event(&["fz", "diag", "warning"], metadata! { diagnostic: opaque(&d1) });
    t.event(&["fz", "diag", "error"], metadata! { diagnostic: opaque(&d2) });

    let mut ds = Diagnostics::new();
    ds.push(d1);
    ds.push(d2);
    let expected = render_diagnostics_to_string(&sm.borrow(), &ds);
    let actual = String::from_utf8(buf.borrow().clone()).unwrap();
    assert_eq!(actual, expected);
}

fn render_diagnostics_to_string(sm: &SourceMap, diags: &Diagnostics) -> String {
    let renderer = Renderer::new(sm).with_color_disabled();
    let mut out = Vec::new();
    for diag in diags.as_slice() {
        renderer.emit(diag, &mut out).unwrap();
    }
    String::from_utf8(out).unwrap()
}
