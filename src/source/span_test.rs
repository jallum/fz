use std::mem::size_of;

use super::*;
use crate::source::SourceMap;

fn source_version() -> SourceVersion {
    let mut sources = SourceMap::new();
    sources.add_code(Some("span-test.fz"), "0123456789abcdef")
}

#[test]
fn dummy_is_dummy() {
    assert!(Span::DUMMY.is_dummy());
    assert!(!Span::new(source_version(), 0, 1).is_dummy());
}

#[test]
#[should_panic(expected = "span end must not precede its start")]
fn inverted_span_has_no_length() {
    Span::new(source_version(), 2, 1).length();
}

#[test]
fn merge_returns_enclosing() {
    let version = source_version();
    let a = Span::new(version, 4, 8);
    let b = Span::new(version, 6, 12);
    let m = a.merge(b);
    assert_eq!(m, Span::new(version, 4, 12));
}

#[test]
fn merge_disjoint_ranges_unions_outer_bounds() {
    let version = source_version();
    let a = Span::new(version, 0, 4);
    let b = Span::new(version, 10, 12);
    let m = a.merge(b);
    assert_eq!(m, Span::new(version, 0, 12));
}

#[test]
fn merge_with_dummy_returns_other() {
    let a = Span::new(source_version(), 4, 8);
    assert_eq!(a.merge(Span::DUMMY), a);
    assert_eq!(Span::DUMMY.merge(a), a);
}

#[test]
fn span_is_copy_12_bytes() {
    assert_eq!(size_of::<Span>(), 12);
    let a = Span::new(source_version(), 1, 2);
    let b = a;
    assert_eq!(a, b);
}
