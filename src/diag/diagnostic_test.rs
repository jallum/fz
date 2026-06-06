use super::*;
use crate::compiler::source::{FileId, Span};

fn s(start: u32, end: u32) -> Span {
    Span::new(FileId(0), start, end)
}

#[test]
fn error_constructor_carries_severity_and_code() {
    let code = DiagCode("type/unreachable-arm");
    let d = Diagnostic::error(code, "the then branch is never reachable", s(0, 5));
    assert_eq!(d.severity, Severity::Error);
    assert_eq!(d.code, code);
    assert_eq!(d.message, "the then branch is never reachable");
    assert_eq!(d.primary.span, s(0, 5));
    assert!(d.primary.label.is_empty());
    assert!(d.notes.is_empty());
}

#[test]
fn builder_methods_chain() {
    let d = Diagnostic::warning(DiagCode("test/code"), "headline", s(0, 5))
        .with_label("primary label")
        .with_secondary(s(10, 15), "secondary label")
        .with_note("first note")
        .with_note("second note")
        .with_help("did you mean foo?");
    assert_eq!(d.primary.label, "primary label");
    assert_eq!(d.secondaries.len(), 1);
    assert_eq!(d.secondaries[0].span, s(10, 15));
    assert_eq!(d.notes, vec!["first note", "second note"]);
    assert_eq!(d.helps, vec!["did you mean foo?"]);
}

#[test]
fn diagnostics_accumulator_tracks_len() {
    let mut ds = Diagnostics::new();
    assert_eq!(ds.len(), 0);
    ds.push(Diagnostic::warning(DiagCode("a/b"), "warn", s(0, 1)));
    ds.push(Diagnostic::error(DiagCode("a/c"), "err", s(0, 1)));
    assert_eq!(ds.len(), 2);
}

#[test]
fn diagnostics_extend_merges_lists() {
    let mut a = Diagnostics::new();
    a.push(Diagnostic::warning(DiagCode("a/1"), "x", s(0, 1)));
    let mut b = Diagnostics::new();
    b.push(Diagnostic::error(DiagCode("a/2"), "y", s(2, 3)));
    b.push(Diagnostic::error(DiagCode("a/3"), "z", s(4, 5)));
    a.extend(b);
    assert_eq!(a.len(), 3);
}

#[test]
fn diagnostic_code_renders_as_its_string() {
    let c = DiagCode("foo/bar");
    assert_eq!(format!("{}", c), "foo/bar");
}
