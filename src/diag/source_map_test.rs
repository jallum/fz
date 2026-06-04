use super::*;

fn sm_with(name: &str, src: &str) -> (SourceMap, FileId) {
    let mut sm = SourceMap::new();
    let id = sm.add_file(name, src);
    (sm, id)
}

#[test]
fn add_file_assigns_sequential_ids() {
    let mut sm = SourceMap::new();
    let a = sm.add_file("a", "x");
    let b = sm.add_file("b", "y");
    assert_eq!(a, FileId(0));
    assert_eq!(b, FileId(1));
}

#[test]
fn locate_first_line_first_col() {
    let (sm, f) = sm_with("t", "abc\ndef\n");
    let loc = sm.locate(Span::new(f, 0, 1));
    assert_eq!(loc.line, 1);
    assert_eq!(loc.col, 1);
    assert_eq!(loc.line_start, 0);
    assert_eq!(loc.line_end, 3); // "abc"
}

#[test]
fn locate_second_line() {
    let (sm, f) = sm_with("t", "abc\ndef\n");
    let loc = sm.locate(Span::new(f, 5, 6)); // 'e' in "def"
    assert_eq!(loc.line, 2);
    assert_eq!(loc.col, 2);
    assert_eq!(loc.line_start, 4);
    assert_eq!(loc.line_end, 7); // "def"
}

#[test]
fn locate_at_eof_no_trailing_newline() {
    let (sm, f) = sm_with("t", "abc");
    let loc = sm.locate(Span::new(f, 2, 3));
    assert_eq!(loc.line, 1);
    assert_eq!(loc.col, 3);
    assert_eq!(loc.line_start, 0);
    assert_eq!(loc.line_end, 3);
}

#[test]
fn locate_on_three_lines() {
    let (sm, f) = sm_with("t", "one\ntwo\nthree");
    let loc = sm.locate(Span::new(f, 8, 13));
    assert_eq!(loc.line, 3);
    assert_eq!(loc.col, 1);
    assert_eq!(
        &sm.file(f).bytes[loc.line_start as usize..loc.line_end as usize],
        "three"
    );
}

#[test]
fn multi_file_isolation() {
    let mut sm = SourceMap::new();
    let a = sm.add_file("a", "abc");
    let b = sm.add_file("b", "def");
    assert_eq!(sm.file(a).bytes.as_ref(), "abc");
    assert_eq!(sm.file(b).bytes.as_ref(), "def");
}

#[test]
fn intern_dedups_on_name_and_content() {
    let mut sm = SourceMap::new();
    let a = sm.intern("t", "abc");
    let b = sm.intern("t", "abc");
    assert_eq!(a, b, "same (name, bytes) interns to the same FileId");
    assert_eq!(sm.file_count(), 1);
}

#[test]
fn intern_distinguishes_different_content() {
    let mut sm = SourceMap::new();
    let a = sm.intern("t", "abc");
    let b = sm.intern("t", "abd");
    assert_ne!(a, b, "same name + different bytes are distinct files");
    assert_eq!(sm.file_count(), 2);
}

#[test]
fn intern_distinguishes_different_name() {
    let mut sm = SourceMap::new();
    let a = sm.intern("a", "abc");
    let b = sm.intern("b", "abc");
    assert_ne!(a, b, "different name + same bytes are distinct files");
    assert_eq!(sm.file_count(), 2);
}

#[test]
fn line_starts_cached_once() {
    let (sm, f) = sm_with("t", "a\nb\nc");
    // Call locate twice; the second call should hit the cache. We can't
    // observe the cache directly, but we can verify the result is stable.
    let l1 = sm.locate(Span::new(f, 2, 3));
    let l2 = sm.locate(Span::new(f, 2, 3));
    assert_eq!(l1, l2);
    assert_eq!(l1.line, 2);
}
