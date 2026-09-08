//! SourceMap: owns source code and resolves spans to display location.
//!
//! Code is added via `add_code`, which assigns an immutable `SourceVersion`.
//! Each entry owns its optional display name and shared bytes; spans index into
//! those bytes directly and `locate(span)` computes line/col on demand from a
//! lazily-built line-offset index.

use std::sync::{Arc, OnceLock};

use super::{SourceVersion, Span};

#[derive(Debug, Clone)]
pub struct Code {
    pub name: Option<Arc<str>>,
    pub bytes: Arc<str>,
    /// Lazily computed on first `locate` for this file. Each entry is the
    /// byte offset of the start of a line; line 1 starts at byte 0.
    line_starts: OnceLock<Vec<u32>>,
}

impl Code {
    fn new(name: Option<Arc<str>>, bytes: Arc<str>) -> Self {
        Self {
            name,
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
    pub source_version: SourceVersion,
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

#[derive(Debug, Default, Clone)]
pub struct SourceMap {
    codes: Vec<Code>,
}

impl SourceMap {
    #[cfg(test)]
    pub fn new() -> Self {
        Self { codes: Vec::new() }
    }

    pub fn add_code<N>(&mut self, name: Option<N>, bytes: impl Into<Arc<str>>) -> SourceVersion
    where
        N: Into<String>,
    {
        let id = SourceVersion::from_index(self.codes.len());
        let name = name.map(Into::into).map(Arc::<str>::from);
        self.codes.push(Code::new(name, bytes.into()));
        id
    }

    pub fn code(&self, id: SourceVersion) -> &Code {
        &self.codes[id.index()]
    }

    pub fn name(&self, id: SourceVersion) -> Option<&str> {
        self.code(id).name.as_deref()
    }

    pub(crate) fn code_count(&self) -> usize {
        self.codes.len()
    }

    /// Constructs provenance only after proving that its encoded version and
    /// byte range name an exact location in this source authority.
    pub(crate) fn checked_span(&self, version: u32, start: u32, end: u32) -> Option<Span> {
        if version == SourceVersion::NONE.as_u32() || end < start {
            return None;
        }
        let source_version = SourceVersion::from_encoded(version);
        let code = self.codes.get(source_version.index())?;
        (end as usize <= code.bytes.len()).then(|| Span::new(source_version, start, end))
    }

    /// Returns the location of `span.start`. Panics on DUMMY spans —
    /// callers are responsible for the is_dummy guard.
    pub fn locate(&self, span: Span) -> Location {
        assert!(!span.is_dummy(), "SourceMap::locate on DUMMY span");
        let f = self.code(span.source_version);
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
            source_version: span.source_version,
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
