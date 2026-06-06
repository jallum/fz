//! SourceMap: owns source code and resolves spans to display location.
//!
//! Code is added via `add_code`, which assigns a `FileId`. Optional display
//! names are stored separately from the code bytes; spans index into `bytes`
//! directly and `locate(span)` computes line/col on demand from a lazily-built
//! line-offset index.

use std::sync::{Arc, OnceLock};

use super::{FileId, Span};

#[derive(Clone)]
pub struct Code {
    pub id: FileId,
    pub bytes: Arc<str>,
    /// Lazily computed on first `locate` for this file. Each entry is the
    /// byte offset of the start of a line; line 1 starts at byte 0.
    line_starts: OnceLock<Vec<u32>>,
}

impl Code {
    fn new(id: FileId, bytes: Arc<str>) -> Self {
        Self {
            id,
            bytes,
            line_starts: OnceLock::new(),
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
    codes: Vec<Code>,
    names: Vec<Option<String>>,
}

impl SourceMap {
    pub fn new() -> Self {
        Self {
            codes: Vec::new(),
            names: Vec::new(),
        }
    }

    pub fn add_code<N>(&mut self, name: Option<N>, bytes: impl Into<Arc<str>>) -> FileId
    where
        N: Into<String>,
    {
        let id = FileId(self.codes.len() as u32);
        self.codes.push(Code::new(id, bytes.into()));
        self.names.push(name.map(Into::into));
        id
    }

    pub fn code(&self, id: FileId) -> &Code {
        &self.codes[id.0 as usize]
    }

    pub fn name(&self, id: FileId) -> Option<&str> {
        self.names[id.0 as usize].as_deref()
    }

    pub fn file_count(&self) -> usize {
        self.codes.len()
    }

    /// Returns the location of `span.start`. Panics on DUMMY spans —
    /// callers are responsible for the is_dummy guard.
    pub fn locate(&self, span: Span) -> Location {
        assert!(!span.is_dummy(), "SourceMap::locate on DUMMY span");
        let f = self.code(span.file);
        let starts = f.line_starts();
        let off = span.start;
        let idx = match starts.binary_search(&off) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let line_start = starts[idx];
        let line_end = starts.get(idx + 1).copied().unwrap_or(f.bytes.len() as u32);
        let line_end = if line_end > line_start && f.bytes.as_bytes().get((line_end - 1) as usize) == Some(&b'\n') {
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
}

#[cfg(test)]
#[path = "source_map_test.rs"]
mod source_map_test;
