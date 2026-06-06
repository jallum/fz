use super::*;

fn sm_with(name: &str, src: &str) -> (SourceMap, FileId) {
    let mut sm = SourceMap::new();
    let f = sm.add_file(name.to_string(), src.to_string());
    (sm, f)
}

#[test]
fn add_file_assigns_sequential_ids() {
    let mut sm = SourceMap::new();
    let a = sm.add_file("a".to_string(), "one".to_string());
    let b = sm.add_file("b".to_string(), "two".to_string());
    assert_eq!(a, FileId(0));
    assert_eq!(b, FileId(1));
    assert_eq!(sm.file_count(), 2);
}

#[test]
fn locate_first_line_first_col() {
    let (sm, f) = sm_with("t", "abc\ndef\n");
    let loc = sm.locate(Span::new(f, 0, 1));
    assert_eq!(loc.line, 1);
    assert_eq!(loc.col, 1);
    assert_eq!(loc.line_start, 0);
    assert_eq!(loc.line_end, 3);
}

#[test]
fn locate_second_line() {
    let (sm, f) = sm_with("t", "abc\ndef\n");
    let loc = sm.locate(Span::new(f, 5, 6));
    assert_eq!(loc.line, 2);
    assert_eq!(loc.col, 2);
    assert_eq!(loc.line_start, 4);
    assert_eq!(loc.line_end, 7);
}

#[test]
fn locate_at_eof_no_trailing_newline() {
    let (sm, f) = sm_with("t", "ab\nc");
    let loc = sm.locate(Span::new(f, 2, 3));
    assert_eq!(loc.line, 1);
    assert_eq!(loc.col, 3);
    assert_eq!(loc.line_start, 0);
    assert_eq!(loc.line_end, 2);
}

#[test]
fn locate_on_three_lines() {
    let (sm, f) = sm_with("t", "ab\ncd\nefgh");
    let loc = sm.locate(Span::new(f, 8, 13));
    assert_eq!(loc.line, 3);
    assert_eq!(loc.col, 3);
    assert_eq!(loc.line_start, 6);
    assert_eq!(loc.line_end, 10);
}

#[test]
fn multi_file_isolation() {
    let mut sm = SourceMap::new();
    let a = sm.add_file("a".to_string(), "x\ny".to_string());
    let b = sm.add_file("b".to_string(), "zz".to_string());
    let la = sm.locate(Span::new(a, 2, 3));
    let lb = sm.locate(Span::new(b, 1, 2));
    assert_eq!(la.file, a);
    assert_eq!(la.line, 2);
    assert_eq!(lb.file, b);
    assert_eq!(lb.line, 1);
}

#[test]
fn line_starts_cached_once() {
    let mut sm = SourceMap::new();
    let f = sm.add_file("a".to_string(), "a\nb\nc".to_string());
    let l1 = sm.locate(Span::new(f, 2, 3));
    let l2 = sm.locate(Span::new(f, 2, 3));
    assert_eq!(l1, l2);
}
