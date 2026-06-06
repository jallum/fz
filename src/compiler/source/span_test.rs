use std::mem::size_of;

use super::*;

#[test]
fn dummy_is_dummy() {
    assert!(Span::DUMMY.is_dummy());
    assert!(!Span::new(FileId(0), 0, 1).is_dummy());
}

#[test]
fn merge_returns_enclosing() {
    let a = Span::new(FileId(0), 4, 8);
    let b = Span::new(FileId(0), 6, 12);
    let m = a.merge(b);
    assert_eq!(m, Span::new(FileId(0), 4, 12));
}

#[test]
fn merge_disjoint_ranges_unions_outer_bounds() {
    let a = Span::new(FileId(0), 0, 4);
    let b = Span::new(FileId(0), 10, 12);
    let m = a.merge(b);
    assert_eq!(m, Span::new(FileId(0), 0, 12));
}

#[test]
fn merge_with_dummy_returns_other() {
    let a = Span::new(FileId(0), 4, 8);
    assert_eq!(a.merge(Span::DUMMY), a);
    assert_eq!(Span::DUMMY.merge(a), a);
}

#[test]
fn span_is_copy_12_bytes() {
    assert_eq!(size_of::<Span>(), 12);
    let a = Span::new(FileId(0), 1, 2);
    let b = a;
    assert_eq!(a, b);
}
