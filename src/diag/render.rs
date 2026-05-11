//! Diagnostic renderer (fz-ul4.20.6).
//!
//! Hand-rolled, ASCII-only by default, NO_COLOR-honoring. The format mirrors
//! rustc:
//!
//! ```text
//! warning[type/unreachable-arm]: the then branch is never reachable
//!   --> fixtures/example.fz:12:7
//!    |
//! 12 |   if x == "hello", do: :got_str
//!    |   ^^^^^^^^^^^^^^^ in fn `check`
//!    |
//!    = note: narrowing `x` in this branch leaves no possible values
//! ```
//!
//! Three input pieces: a `Diagnostic`, a `SourceMap` (to resolve span
//! offsets to file/line/col/snippet), and a `ColorMode`. Output is byte
//! stream — caller chooses stderr/stdout/buffer.

use std::io::{self, Write};

use super::diagnostic::{Diagnostic, Diagnostics, Severity, SpanLabel};
use super::source_map::SourceMap;
use super::span::Span;
use super::style::{self, ColorMode};

pub struct Renderer<'a> {
    pub sm: &'a SourceMap,
    pub color: ColorMode,
    pub tab_width: u32,
    /// When true, the renderer's color decision is forced by `color`; the
    /// `Auto` case relies on a TTY probe of stderr.
    use_color: bool,
}

impl<'a> Renderer<'a> {
    pub fn new(sm: &'a SourceMap) -> Self {
        let use_color = style::use_color_for_stderr(ColorMode::Auto);
        Self {
            sm,
            color: ColorMode::Auto,
            tab_width: 4,
            use_color,
        }
    }

    pub fn with_color(mut self, mode: ColorMode) -> Self {
        self.color = mode;
        self.use_color = mode.use_color(true) && match mode {
            ColorMode::Auto => style::use_color_for_stderr(ColorMode::Auto),
            ColorMode::Always => true,
            ColorMode::Never => false,
        };
        self
    }

    /// Force-disable color regardless of mode. Used by tests so golden
    /// files don't carry escape sequences.
    pub fn with_color_disabled(mut self) -> Self {
        self.color = ColorMode::Never;
        self.use_color = false;
        self
    }

    pub fn emit(&self, d: &Diagnostic, out: &mut impl Write) -> io::Result<()> {
        // Compute gutter width: the largest line number across primary
        // and all secondaries determines the gutter padding.
        let gutter = self.gutter_width(d);

        // Header: severity[code]: message
        self.header(d, out)?;

        // Location + snippet block for the primary span.
        self.location_arrow(d.primary.span, gutter, out)?;
        self.snippet_block(&d.primary, gutter, /*primary=*/ true, out)?;

        // Secondary blocks — for v1, each gets its own block. Folding
        // adjacent secondaries into the primary block is a v2 polish.
        for sec in &d.secondaries {
            self.location_arrow(sec.span, gutter, out)?;
            self.snippet_block(sec, gutter, /*primary=*/ false, out)?;
        }

        // Notes / helps / lineage trailers.
        for note in &d.notes {
            self.trailer("note", note, gutter, out)?;
        }
        for help in &d.helps {
            self.trailer("help", help, gutter, out)?;
        }
        for &exp in &d.expanded_from {
            self.expanded_trailer(exp, gutter, out)?;
        }
        // Final blank line so consecutive diagnostics don't run together.
        writeln!(out)?;
        Ok(())
    }

    pub fn emit_all(&self, diags: &Diagnostics, out: &mut impl Write) -> io::Result<()> {
        for d in diags.iter() {
            self.emit(d, out)?;
        }
        Ok(())
    }

    // ---- internals ----

    fn gutter_width(&self, d: &Diagnostic) -> usize {
        let mut max_line: u32 = 0;
        let mut consider = |span: Span| {
            if !span.is_dummy() {
                let loc = self.sm.locate(span);
                if loc.line > max_line {
                    max_line = loc.line;
                }
            }
        };
        consider(d.primary.span);
        for s in &d.secondaries {
            consider(s.span);
        }
        std::cmp::max(2, line_digit_count(max_line))
    }

    fn header(&self, d: &Diagnostic, out: &mut impl Write) -> io::Result<()> {
        let (label, color) = match d.severity {
            Severity::Error => ("error", style::RED),
            Severity::Warning => ("warning", style::YELLOW),
            Severity::Note => ("note", style::CYAN),
            Severity::Help => ("help", style::GREEN),
        };
        if self.use_color {
            writeln!(out, "{bold}{c}{l}{reset}{bold}[{code}]:{reset} {msg}",
                bold = style::BOLD, c = color, l = label, reset = style::RESET,
                code = d.code, msg = d.message)
        } else {
            writeln!(out, "{}[{}]: {}", label, d.code, d.message)
        }
    }

    fn location_arrow(&self, span: Span, _gutter: usize, out: &mut impl Write) -> io::Result<()> {
        // rustc-style fixed 2-space prefix before the arrow, regardless
        // of gutter width. Keeps the visual alignment of `-->` stable
        // across diagnostics whose source spans nothing wider than 99
        // lines (the gutter sits inside this prefix when line numbers
        // grow; the alignment to `|` is what matters for snippets).
        if span.is_dummy() {
            writeln!(out, "  --> <generated>")?;
            return Ok(());
        }
        let loc = self.sm.locate(span);
        let file = &self.sm.file(loc.file).name;
        writeln!(out, "  --> {}:{}:{}", file, loc.line, loc.col)
    }

    fn snippet_block(
        &self,
        sl: &SpanLabel,
        gutter: usize,
        primary: bool,
        out: &mut impl Write,
    ) -> io::Result<()> {
        if sl.span.is_dummy() {
            // No snippet, but emit a "(generated)" marker so the label
            // still has somewhere to attach.
            if !sl.label.is_empty() {
                writeln!(out, "{:>pad$} = {}", "", sl.label, pad = gutter)?;
            }
            return Ok(());
        }
        let loc = self.sm.locate(sl.span);
        let f = self.sm.file(loc.file);
        let source_line = &f.bytes.as_bytes()[loc.line_start as usize..loc.line_end as usize];
        let (expanded_line, byte_to_col) = expand_tabs(source_line, self.tab_width as usize);

        // Source line itself.
        writeln!(out, "{:>pad$} |", "", pad = gutter)?;
        if self.use_color {
            writeln!(out, "{n:>pad$} | {line}", n = loc.line, pad = gutter, line = expanded_line)?;
        } else {
            writeln!(out, "{n:>pad$} | {line}", n = loc.line, pad = gutter, line = expanded_line)?;
        }

        // Underline. Compute start/end column in expanded coords.
        let local_start = (sl.span.start.saturating_sub(loc.line_start)) as usize;
        // If span spans into next lines, clamp to end of current line.
        let local_end_byte = std::cmp::min(sl.span.end, loc.line_end) as usize - loc.line_start as usize;
        let start_col = byte_to_col.get(local_start).copied().unwrap_or(0);
        let end_col = byte_to_col.get(local_end_byte).copied()
            .unwrap_or(expanded_line.chars().count());
        let pad_before = " ".repeat(start_col);
        let underline_len = std::cmp::max(1, end_col.saturating_sub(start_col));
        let glyph = if primary { '^' } else { '-' };
        let underline: String = std::iter::repeat(glyph).take(underline_len).collect();

        let (color_pre, color_post) = if self.use_color {
            let c = if primary { style::RED } else { style::CYAN };
            (format!("{}{}", style::BOLD, c), style::RESET.to_string())
        } else {
            (String::new(), String::new())
        };

        if sl.label.is_empty() {
            writeln!(out, "{:>pad$} | {pre}{underline}{post}",
                "", pad = gutter, pre = color_pre, underline = format!("{}{}", pad_before, underline),
                post = color_post)?;
        } else {
            writeln!(out, "{:>pad$} | {pre}{underline}{post} {label}",
                "", pad = gutter, pre = color_pre,
                underline = format!("{}{}", pad_before, underline),
                post = color_post, label = sl.label)?;
        }
        // Closing rule line.
        writeln!(out, "{:>pad$} |", "", pad = gutter)?;
        Ok(())
    }

    fn trailer(&self, kind: &str, text: &str, gutter: usize, out: &mut impl Write) -> io::Result<()> {
        let (color_pre, color_post) = if self.use_color {
            let c = match kind {
                "note" => style::CYAN,
                "help" => style::GREEN,
                _ => style::BLUE,
            };
            (format!("{}{}", style::BOLD, c), style::RESET.to_string())
        } else {
            (String::new(), String::new())
        };
        writeln!(out, "{:>pad$} = {pre}{kind}{post}: {text}",
            "", pad = gutter,
            pre = color_pre, kind = kind, post = color_post, text = text)
    }

    fn expanded_trailer(&self, span: Span, gutter: usize, out: &mut impl Write) -> io::Result<()> {
        if span.is_dummy() {
            writeln!(out, "{:>pad$} = expanded from <generated>", "", pad = gutter)
        } else {
            let loc = self.sm.locate(span);
            let file = &self.sm.file(loc.file).name;
            writeln!(out, "{empty:>pad$} = expanded from {file}:{line}:{col}",
                empty = "", pad = gutter, file = file, line = loc.line, col = loc.col)
        }
    }
}

fn line_digit_count(n: u32) -> usize {
    if n == 0 { return 1; }
    let mut k = 0u32;
    let mut v = n;
    while v > 0 { v /= 10; k += 1; }
    k as usize
}

/// Expand tabs in `line` to spaces at `tab_width` stops. Returns the
/// expanded line plus a `byte_to_col` table: `out[byte_idx]` is the
/// display column position where the byte at that index starts.
/// `out[line.len()]` is the total display width.
fn expand_tabs(line: &[u8], tab_width: usize) -> (String, Vec<usize>) {
    let mut out = String::with_capacity(line.len() + 4);
    let mut col = 0usize;
    let mut map: Vec<usize> = Vec::with_capacity(line.len() + 1);
    for &b in line {
        map.push(col);
        if b == b'\t' {
            let stop = tab_width - (col % tab_width);
            for _ in 0..stop {
                out.push(' ');
            }
            col += stop;
        } else if b == b'\r' {
            // Trailing CR before LF; render as nothing.
        } else {
            // Render as a single char. Non-ASCII byte counts as 1 display
            // column in v1 (ASCII-clean fixtures keep this honest).
            out.push(b as char);
            col += 1;
        }
    }
    map.push(col);
    (out, map)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::codes::{LEX_UNEXPECTED_CHAR, TYPE_UNREACHABLE_ARM};
    use crate::diag::span::FileId;

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
        let d = Diagnostic::warning(TYPE_UNREACHABLE_ARM, "synthesized", Span::DUMMY)
            .with_note("background context");
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
    fn expanded_from_trailer_renders() {
        let src = "test(:foo) do\n  assert_eq(1, 2)\nend\n";
        let (sm, f) = rebuild(src);
        let primary = Span::new(f, 16, 31);
        let call_span = Span::new(f, 0, 13);
        let d = Diagnostic::error(TYPE_UNREACHABLE_ARM, "expanded code failed", primary)
            .with_expanded_from(call_span);
        let out = render(&d, &sm);
        assert!(out.contains("= expanded from input.fz:1:1"),
            "got:\n{}", out);
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

    #[test]
    fn color_on_emits_escape_in_header() {
        let src = "fn main(), do: 1\n";
        let (sm, f) = rebuild(src);
        let mut buf: Vec<u8> = Vec::new();
        let r = Renderer::new(&sm).with_color(ColorMode::Always);
        let d = Diagnostic::error(LEX_UNEXPECTED_CHAR, "x", Span::new(f, 0, 1));
        r.emit(&d, &mut buf).unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.contains("\x1b["), "ANSI escapes expected, got:\n{}", out);
    }

    /// Golden-file fixtures: any directory under `fixtures/errors/` with
    /// an `input.fz` + `expected.txt` pair drives the lex/parse stages
    /// and compares the rendered diagnostic to the golden file. Fixtures
    /// with only `input.fz` (no expected) are reserved for later tickets
    /// and silently skipped.
    #[test]
    fn fixture_golden_outputs_match() {
        use crate::lexer::Lexer;
        use crate::parser::Parser;
        use std::fs;
        use std::path::Path;

        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures").join("errors");
        let mut compared = 0;
        for entry in fs::read_dir(&root).expect("read fixtures/errors") {
            let entry = entry.expect("entry");
            let path = entry.path();
            if !path.is_dir() { continue; }
            let input_path = path.join("input.fz");
            let expected_path = path.join("expected.txt");
            if !expected_path.exists() || !input_path.exists() { continue; }

            let src = fs::read_to_string(&input_path).expect("read input.fz");
            let expected = fs::read_to_string(&expected_path).expect("read expected.txt");
            let name = input_path.to_string_lossy().to_string();

            // Strip CARGO_MANIFEST_DIR prefix so file paths in expected.txt
            // match what `fz run` emits with a relative path. The fixture
            // was captured with a workspace-relative path; we register
            // the file under that same relative name.
            let rel = name.strip_prefix(env!("CARGO_MANIFEST_DIR"))
                .map(|s| s.trim_start_matches('/').to_string())
                .unwrap_or(name.clone());

            let mut sm = SourceMap::new();
            let id = sm.add_file(rel.clone(), src.clone());
            let lex = Lexer::with_file(&src, id).tokenize();
            let actual = match lex {
                Err(e) => render(&e.to_diagnostic(), &sm),
                Ok(toks) => match Parser::new(toks).parse_program() {
                    Err(e) => render(&e.to_diagnostic(), &sm),
                    Ok(_) => panic!("fixture {} parsed successfully — expected an error", rel),
                },
            };
            assert_eq!(actual.trim_end(), expected.trim_end(),
                "fixture {} mismatch:\n--- actual ---\n{}\n--- expected ---\n{}",
                rel, actual, expected);
            compared += 1;
        }
        assert!(compared >= 1, "expected at least one fixture with expected.txt");
    }

    #[test]
    fn emit_all_renders_each_with_blank_separator() {
        let src = "fn main(), do: 1\n";
        let (sm, f) = rebuild(src);
        let mut ds = Diagnostics::new();
        ds.push(Diagnostic::warning(TYPE_UNREACHABLE_ARM, "first", Span::new(f, 0, 2)));
        ds.push(Diagnostic::warning(TYPE_UNREACHABLE_ARM, "second", Span::new(f, 3, 7)));
        let mut buf: Vec<u8> = Vec::new();
        Renderer::new(&sm).with_color_disabled().emit_all(&ds, &mut buf).unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.contains("first"));
        assert!(out.contains("second"));
        // Two diagnostics → trailing blank between them.
        let n_blank_pairs = out.matches("\n\n").count();
        assert!(n_blank_pairs >= 2, "expected blank-line separators, got:\n{}", out);
    }
}
