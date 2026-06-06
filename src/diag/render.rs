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

use std::cmp::{max, min};
use std::io::{self, Write};
use std::iter::repeat_n;

use crate::compiler::source::{SourceMap, Span};

use super::diagnostic::{Diagnostic, Severity, SpanLabel};
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
        self.use_color = mode.use_color(true)
            && match mode {
                ColorMode::Auto => style::use_color_for_stderr(ColorMode::Auto),
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

    pub fn emit(&self, d: &Diagnostic, out: &mut dyn Write) -> io::Result<()> {
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
        // Final blank line so consecutive diagnostics don't run together.
        writeln!(out)?;
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
        max(2, line_digit_count(max_line))
    }

    fn header(&self, d: &Diagnostic, out: &mut dyn Write) -> io::Result<()> {
        let (label, color) = match d.severity {
            Severity::Error => ("error", style::RED),
            Severity::Warning => ("warning", style::YELLOW),
        };
        if self.use_color {
            writeln!(
                out,
                "{bold}{c}{l}{reset}{bold}[{code}]:{reset} {msg}",
                bold = style::BOLD,
                c = color,
                l = label,
                reset = style::RESET,
                code = d.code,
                msg = d.message
            )
        } else {
            writeln!(out, "{}[{}]: {}", label, d.code, d.message)
        }
    }

    fn location_arrow(&self, span: Span, _gutter: usize, out: &mut dyn Write) -> io::Result<()> {
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
        let file = self.sm.name(loc.code_id).unwrap_or("<unnamed>");
        writeln!(out, "  --> {}:{}:{}", file, loc.line, loc.col)
    }

    fn snippet_block(&self, sl: &SpanLabel, gutter: usize, primary: bool, out: &mut dyn Write) -> io::Result<()> {
        if sl.span.is_dummy() {
            // No snippet, but emit a "(generated)" marker so the label
            // still has somewhere to attach.
            if !sl.label.is_empty() {
                writeln!(out, "{:>pad$} = {}", "", sl.label, pad = gutter)?;
            }
            return Ok(());
        }
        let loc = self.sm.locate(sl.span);
        let f = self.sm.code(loc.code_id);
        let source_line = &f.bytes.as_bytes()[loc.line_start as usize..loc.line_end as usize];
        let (expanded_line, byte_to_col) = expand_tabs(source_line, self.tab_width as usize);

        // Source line itself. Color is applied to the underline glyph
        // below (color_pre / color_post), not to the source bytes —
        // showing the source verbatim keeps copy-paste from the
        // terminal lossless. Inline-coloring the spanned bytes would
        // be a real diagnostics-polish feature (filed separately).
        writeln!(out, "{:>pad$} |", "", pad = gutter)?;
        writeln!(
            out,
            "{n:>pad$} | {line}",
            n = loc.line,
            pad = gutter,
            line = expanded_line
        )?;

        // Underline. Compute start/end column in expanded coords.
        let local_start = (sl.span.start.saturating_sub(loc.line_start)) as usize;
        // If span spans into next lines, clamp to end of current line.
        let local_end_byte = min(sl.span.end, loc.line_end) as usize - loc.line_start as usize;
        let start_col = byte_to_col.get(local_start).copied().unwrap_or(0);
        let end_col = byte_to_col
            .get(local_end_byte)
            .copied()
            .unwrap_or(expanded_line.chars().count());
        let pad_before = " ".repeat(start_col);
        let underline_len = max(1, end_col.saturating_sub(start_col));
        let glyph = if primary { '^' } else { '-' };
        let underline: String = repeat_n(glyph, underline_len).collect();

        let (color_pre, color_post) = if self.use_color {
            let c = if primary { style::RED } else { style::CYAN };
            (format!("{}{}", style::BOLD, c), style::RESET.to_string())
        } else {
            (String::new(), String::new())
        };

        if sl.label.is_empty() {
            writeln!(
                out,
                "{:>pad$} | {pre}{pad_before}{underline}{post}",
                "",
                pad = gutter,
                pre = color_pre,
                pad_before = pad_before,
                underline = underline,
                post = color_post
            )?;
        } else {
            writeln!(
                out,
                "{:>pad$} | {pre}{pad_before}{underline}{post} {label}",
                "",
                pad = gutter,
                pre = color_pre,
                pad_before = pad_before,
                underline = underline,
                post = color_post,
                label = sl.label
            )?;
        }
        // Closing rule line.
        writeln!(out, "{:>pad$} |", "", pad = gutter)?;
        Ok(())
    }

    fn trailer(&self, kind: &str, text: &str, gutter: usize, out: &mut dyn Write) -> io::Result<()> {
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
        writeln!(
            out,
            "{:>pad$} = {pre}{kind}{post}: {text}",
            "",
            pad = gutter,
            pre = color_pre,
            kind = kind,
            post = color_post,
            text = text
        )
    }
}

fn line_digit_count(n: u32) -> usize {
    if n == 0 {
        return 1;
    }
    let mut k = 0u32;
    let mut v = n;
    while v > 0 {
        v /= 10;
        k += 1;
    }
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
#[path = "render_test.rs"]
mod render_test;
