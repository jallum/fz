use super::*;
use crate::diag::codes::{LEX_UNEXPECTED_CHAR, TYPE_UNREACHABLE_ARM};
use crate::diag::span::FileId;
use crate::frontend::macros::expand_program;
use crate::frontend::resolve::flatten_modules;
use crate::ir_lower::lower_program;
use crate::telemetry::Telemetry;

fn rebuild(src: &str) -> (SourceMap, FileId) {
    let mut sm = SourceMap::new();
    let id = sm.add_file("input.fz", src);
    (sm, id)
}

fn render(diag: &Diagnostic, sm: &SourceMap) -> String {
    let mut buf: Vec<u8> = Vec::new();
    Renderer::new(sm).with_color_disabled().emit(diag, &mut buf).unwrap();
    String::from_utf8(buf).unwrap()
}

#[test]
fn header_and_location_layout() {
    let src = "fn main() do\n  if x == 1, do: :ok\nend\n";
    let (sm, f) = rebuild(src);
    // Underline the `x == 1` part.
    let span = Span::new(f, 18, 24);
    let d = Diagnostic::warning(TYPE_UNREACHABLE_ARM, "the then branch is never reachable", span)
        .with_label("in fn `main`");
    let out = render(&d, &sm);
    let expected = "\
warning[type/unreachable-arm]: the then branch is never reachable
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
    let d = Diagnostic::warning(TYPE_UNREACHABLE_ARM, "synthesized", Span::DUMMY).with_note("background context");
    let out = render(&d, &sm);
    assert!(out.contains("--> <generated>"));
    assert!(out.contains("note: background context"));
}

#[test]
fn notes_and_helps_render() {
    let src = "fn main() do 1 end\n";
    let (sm, f) = rebuild(src);
    let d = Diagnostic::error(LEX_UNEXPECTED_CHAR, "synthetic", Span::new(f, 0, 2))
        .with_note("first note")
        .with_note("second note")
        .with_help("did you mean `fn`?");
    let out = render(&d, &sm);
    assert!(out.contains("= note: first note"));
    assert!(out.contains("= note: second note"));
    assert!(out.contains("= help: did you mean `fn`?"));
}

#[test]
fn secondary_span_gets_its_own_block() {
    let src = "fn main() do\n  x = 1\n  y = 2\nend\n";
    let (sm, f) = rebuild(src);
    let primary = Span::new(f, 15, 16); // `x` on line 2
    let secondary = Span::new(f, 23, 24); // `y` on line 3
    let d = Diagnostic::warning(TYPE_UNREACHABLE_ARM, "x is shadowed by y", primary)
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

#[test]
fn tab_expansion_aligns_caret() {
    // Source uses a tab before `let x`. The caret on `x` should land
    // at column 5 (tab=4 + 0 chars of indent, then 'l','e','t',' ','x').
    // i.e. col 8+1=9.
    let src = "\tlet x = 1\n";
    let (sm, f) = rebuild(src);
    // Underline `x` only — byte offset 5 (after \t + "let "), len 1.
    let span = Span::new(f, 5, 6);
    let d = Diagnostic::warning(TYPE_UNREACHABLE_ARM, "bad x", span);
    let out = render(&d, &sm);
    // After tab expansion: "    let x = 1". `x` is at column 9 (1-based).
    // The underline line should have 8 spaces before `^`.
    let underline_line = out.lines().find(|l| l.contains("^")).unwrap();
    let pos = underline_line.find('^').unwrap();
    // Account for gutter prefix "  | " (4 chars in this layout).
    let after_pipe = underline_line.find('|').unwrap() + 2;
    assert_eq!(pos - after_pipe, 8, "got line {:?}", underline_line);
}

#[test]
fn color_off_produces_no_escapes() {
    let src = "fn main(), do: 1\n";
    let (sm, f) = rebuild(src);
    let d = Diagnostic::error(LEX_UNEXPECTED_CHAR, "x", Span::new(f, 0, 1));
    let out = render(&d, &sm);
    assert!(!out.contains("\x1b["), "no ANSI escapes when color disabled");
}

/// Drive a fixture through lex → parse → resolve → macros → lower
/// and return the rendered first-error diagnostic. Panics if the
/// pipeline completes without an error (the fixture must exercise
/// one of these stages).
fn run_pipeline_for_fixture(src: &str, id: FileId, sm: &SourceMap, rel: &str, tel: &dyn Telemetry) -> String {
    use crate::parser::Parser;
    use crate::parser::lexer::Lexer;
    let toks = match Lexer::with_file_and_source_name(src, id, "<test>").tokenize(tel) {
        Err(e) => return render(&e.to_diagnostic(), sm),
        Ok(t) => t,
    };
    let prog = match Parser::new(toks).parse_program(tel) {
        Err(e) => return render(&e.to_diagnostic(), sm),
        Ok(p) => p,
    };
    let mut ct = crate::types::new();
    let mut prog = match flatten_modules(&mut ct, prog, tel) {
        Err(e) => return render(&e.to_diagnostic(), sm),
        Ok(p) => p,
    };
    if let Err(e) = expand_program(&mut prog) {
        return render(&e.to_diagnostic(), sm);
    }
    if let Err(e) = lower_program(&mut crate::types::new(), &prog, tel) {
        return render(&e.to_diagnostic(), sm);
    }
    panic!("fixture {} completed pipeline successfully — expected an error", rel);
}

/// Golden-file fixtures: any directory under `fixtures/errors/` with
/// an `input.fz` + `expected.txt` pair drives the pipeline
/// and compares the rendered diagnostic to the golden file. Fixtures
/// with only `input.fz` (no expected) are reserved for later tickets
/// and silently skipped.
#[test]
fn fixture_golden_outputs_match() {
    use std::fs;
    use std::path::Path;

    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures").join("errors");
    let mut compared = 0;
    for entry in fs::read_dir(&root).expect("read fixtures/errors") {
        let entry = entry.expect("entry");
        let path = entry.path();
        if !path.is_dir() {
            continue;
        }
        let input_path = path.join("input.fz");
        let expected_path = path.join("expected.txt");
        if !expected_path.exists() || !input_path.exists() {
            continue;
        }

        let src = fs::read_to_string(&input_path).expect("read input.fz");
        let expected = fs::read_to_string(&expected_path).expect("read expected.txt");
        let name = input_path.to_string_lossy().to_string();

        // Strip CARGO_MANIFEST_DIR prefix so file paths in expected.txt
        // match what `fz run` emits with a relative path. The fixture
        // was captured with a workspace-relative path; we register
        // the file under that same relative name.
        let rel = name
            .strip_prefix(env!("CARGO_MANIFEST_DIR"))
            .map(|s| s.trim_start_matches('/').to_string())
            .unwrap_or(name.clone());

        let mut sm = SourceMap::new();
        let id = sm.add_file(rel.clone(), src.clone());
        // Drive the full pipeline (lex → parse → resolve → macros →
        // lower) and capture whichever stage's diagnostic the fixture
        // is exercising. Codegen errors aren't covered here because
        // most are backend-plumbing failures without a real source
        // span; the verify/define paths that DO have spans are
        // covered by integration tests, not goldens.
        let actual = run_pipeline_for_fixture(&src, id, &sm, &rel, &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(
            actual.trim_end(),
            expected.trim_end(),
            "fixture {} mismatch:\n--- actual ---\n{}\n--- expected ---\n{}",
            rel,
            actual,
            expected
        );
        compared += 1;
    }
    assert!(compared >= 1, "expected at least one fixture with expected.txt");
}
