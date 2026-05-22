//! SourceMap: owns source files and resolves spans to display location.
//!
//! Files are added via `add_file` which assigns a FileId. Spans index into
//! `bytes` directly; `locate(span)` computes line/col on demand from a
//! lazily-built line-offset index.

use std::sync::Arc;

use super::span::{FileId, Span};

#[derive(Clone)]
pub struct SourceFile {
    pub name: String,
    pub bytes: Arc<str>,
    /// Lazily computed on first `locate` for this file. Each entry is the
    /// byte offset of the start of a line; line 1 starts at byte 0.
    line_starts: std::sync::OnceLock<Vec<u32>>,
}

impl SourceFile {
    fn new(name: String, bytes: Arc<str>) -> Self {
        Self {
            name,
            bytes,
            line_starts: std::sync::OnceLock::new(),
        }
    }

    fn line_starts(&self) -> &[u32] {
        self.line_starts.get_or_init(|| {
            let mut v = vec![0u32];
            for (i, b) in self.bytes.as_bytes().iter().enumerate() {
                if *b == b'\n' {
                    let next = (i + 1) as u32;
                    if (next as usize) <= self.bytes.len() {
                        v.push(next);
                    }
                }
            }
            v
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Location {
    pub file: FileId,
    /// 1-based line number of `span.start`.
    pub line: u32,
    /// 1-based display column at `span.start`. v1 = byte-count within line
    /// (ASCII-clean fixtures). The .20.6 renderer is where tab expansion
    /// and unicode width handling land.
    pub col: u32,
    /// Byte range `[start, end)` of the line containing `span.start`. Used
    /// by the renderer to extract the source snippet.
    pub line_start: u32,
    pub line_end: u32,
}

#[derive(Default, Clone)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    pub fn new() -> Self {
        Self { files: Vec::new() }
    }

    pub fn add_file(&mut self, name: impl Into<String>, bytes: impl Into<Arc<str>>) -> FileId {
        let id = FileId(self.files.len() as u32);
        self.files.push(SourceFile::new(name.into(), bytes.into()));
        id
    }

    pub fn file(&self, id: FileId) -> &SourceFile {
        &self.files[id.0 as usize]
    }

    pub fn file_count(&self) -> usize {
        self.files.len()
    }

    /// Returns the location of `span.start`. Panics on DUMMY spans —
    /// callers are responsible for the is_dummy guard.
    pub fn locate(&self, span: Span) -> Location {
        assert!(!span.is_dummy(), "SourceMap::locate on DUMMY span");
        let f = self.file(span.file);
        let starts = f.line_starts();
        let off = span.start;
        // Binary search for the line whose start <= off.
        let idx = match starts.binary_search(&off) {
            Ok(i) => i,
            Err(i) => i - 1, // i is the insertion point; previous start is our line
        };
        let line_start = starts[idx];
        let line_end = starts.get(idx + 1).copied().unwrap_or(f.bytes.len() as u32);
        // Trim trailing '\n' from the snippet range so the renderer doesn't
        // draw an empty next-line. `line_end` here points at the '\n' itself
        // (or EOF). The renderer will read line_start..line_end inclusive of
        // any '\r' but exclusive of '\n', which is what we want.
        let line_end = if line_end > line_start
            && f.bytes.as_bytes().get((line_end - 1) as usize) == Some(&b'\n')
        {
            line_end - 1
        } else {
            line_end
        };
        Location {
            file: span.file,
            line: (idx + 1) as u32,
            col: off - line_start + 1,
            line_start,
            line_end,
        }
    }

    /// Slice of source bytes covered by `span`. Convenient for tests and
    /// for the renderer when it wants the exact lexeme.
    pub fn span_text(&self, span: Span) -> &str {
        let f = self.file(span.file);
        &f.bytes[span.start as usize..span.end as usize]
    }
}

#[cfg(test)]
mod tests {
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
    fn span_text_extracts_lexeme() {
        let (sm, f) = sm_with("t", "fn foo()");
        let s = Span::new(f, 3, 6);
        assert_eq!(sm.span_text(s), "foo");
    }

    #[test]
    fn multi_file_isolation() {
        let mut sm = SourceMap::new();
        let a = sm.add_file("a", "abc");
        let b = sm.add_file("b", "def");
        assert_eq!(sm.span_text(Span::new(a, 0, 3)), "abc");
        assert_eq!(sm.span_text(Span::new(b, 0, 3)), "def");
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
}
