use super::*;
use crate::diag::diagnostic::DiagCode;
use crate::source::{Id as CodeId, SourceMap, Span};

const TEST_ERROR: DiagCode = DiagCode("test/error");
const TEST_WARNING: DiagCode = DiagCode("test/warning");

fn rebuild(src: &str) -> (SourceMap, CodeId) {
    let mut sm = SourceMap::new();
    let id = sm.add_code(Some("input.fz"), src);
    (sm, id)
}

fn render(diag: &Diagnostic, sm: &SourceMap) -> String {
    let mut buf: Vec<u8> = Vec::new();
    Renderer::new(sm).with_color_disabled().emit(diag, &mut buf).unwrap();
    String::from_utf8(buf).unwrap()
}

// DROP: diagnostic header/location rendering layout; pure infrastructure
#[test]
fn header_and_location_layout() {
    let src = "fn main() do\n  if x == 1, do: :ok\nend\n";
    let (sm, f) = rebuild(src);
    // Underline the `x == 1` part.
    let span = Span::new(f, 18, 24);
    let d = Diagnostic::warning(TEST_WARNING, "the then branch is never reachable", span).with_label("in fn `main`");
    let out = render(&d, &sm);
    let expected = "\
warning[test/warning]: the then branch is never reachable
  --> input.fz:2:6
   |
 2 |   if x == 1, do: :ok
   |      ^^^^^^ in fn `main`
   |

";
    assert_eq!(out, expected);
}

#[test]
fn dummy_span_emits_generated_marker() {
    let (sm, _) = rebuild("");
    let d = Diagnostic::warning(TEST_WARNING, "synthesized", Span::DUMMY).with_note("background context");
    let out = render(&d, &sm);
    assert!(out.contains("--> <generated>"));
    assert!(out.contains("note: background context"));
}

// DROP: diagnostic notes and help lines rendering; pure infrastructure
#[test]
fn notes_and_helps_render() {
    let src = "fn main() do 1 end\n";
    let (sm, f) = rebuild(src);
    let d = Diagnostic::error(TEST_ERROR, "synthetic", Span::new(f, 0, 2))
        .with_note("first note")
        .with_note("second note")
        .with_help("did you mean `fn`?");
    let out = render(&d, &sm);
    assert!(out.contains("= note: first note"));
    assert!(out.contains("= note: second note"));
    assert!(out.contains("= help: did you mean `fn`?"));
}

// DROP: secondary span rendered as own block; pure infrastructure
#[test]
fn secondary_span_gets_its_own_block() {
    let src = "fn main() do\n  x = 1\n  y = 2\nend\n";
    let (sm, f) = rebuild(src);
    let primary = Span::new(f, 15, 16); // `x` on line 2
    let secondary = Span::new(f, 23, 24); // `y` on line 3
    let d = Diagnostic::warning(TEST_WARNING, "x is shadowed by y", primary)
        .with_label("first binding")
        .with_secondary(secondary, "second binding shadows");
    let out = render(&d, &sm);
    // Primary block:
    assert!(out.contains("--> input.fz:2:3"));
    assert!(out.contains("^ first binding"));
    // Secondary block:
    assert!(out.contains("--> input.fz:3:3"));
    assert!(out.contains("- second binding shadows"));
}

// DROP: tab expansion aligns caret in diagnostic output; pure infrastructure
#[test]
fn tab_expansion_aligns_caret() {
    // Source uses a tab before `let x`. The caret on `x` should land
    // at column 5 (tab=4 + 0 chars of indent, then 'l','e','t',' ','x').
    // i.e. col 8+1=9.
    let src = "\tlet x = 1\n";
    let (sm, f) = rebuild(src);
    // Underline `x` only — byte offset 5 (after \t + "let "), len 1.
    let span = Span::new(f, 5, 6);
    let d = Diagnostic::warning(TEST_WARNING, "bad x", span);
    let out = render(&d, &sm);
    // After tab expansion: "    let x = 1". `x` is at column 9 (1-based).
    // The underline line should have 8 spaces before `^`.
    let underline_line = out.lines().find(|l| l.contains("^")).unwrap();
    let pos = underline_line.find('^').unwrap();
    // Account for gutter prefix "  | " (4 chars in this layout).
    let after_pipe = underline_line.find('|').unwrap() + 2;
    assert_eq!(pos - after_pipe, 8, "got line {:?}", underline_line);
}

// DROP: color-disabled mode emits no ANSI escapes; pure infrastructure
#[test]
fn color_off_produces_no_escapes() {
    let src = "fn main(), do: 1\n";
    let (sm, f) = rebuild(src);
    let d = Diagnostic::error(TEST_ERROR, "x", Span::new(f, 0, 1));
    let out = render(&d, &sm);
    assert!(!out.contains("\x1b["), "no ANSI escapes when color disabled");
}
