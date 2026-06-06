//! Span: byte-offset source position keyed by FileId.
//!
//! Spans are intentionally narrow (Copy, 12 bytes) and carry no source bytes.
//! The SourceMap holds the bytes; the renderer resolves spans to display
//! line/col on demand. This keeps the AST/IR cheap to copy.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(pub u32);

impl FileId {
    /// Sentinel for "no file" — used by Span::DUMMY.
    pub const NONE: FileId = FileId(u32::MAX);
}

/// A half-open byte range `[start, end)` within a single source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

/// Where an AST node's span came from. `Source` — the common case — means a
/// real token in the user's source produced this node. `Expanded` records
/// that the node was synthesized by a macro: `macro_call` is the span of
/// the user's `Foo(args)` invocation, `definition` (when present) is the
/// span of `defmacro Foo …` so a diagnostic can point at the macro itself.
///
/// The renderer (.20.6) consults this when drawing the trailer:
///   = expanded from `<macro>` at file:line:col
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanOrigin {
    Source,
    Expanded { macro_call: Span, definition: Option<Span> },
}

impl Span {
    /// The "no source position available" sentinel. Used for AST/IR nodes
    /// synthesized after parsing (macro expansion, compiler-generated
    /// continuations, etc.). The renderer treats DUMMY as "(generated)" —
    /// no snippet, just the lineage trailer if any.
    pub const DUMMY: Span = Span {
        file: FileId::NONE,
        start: 0,
        end: 0,
    };

    pub const fn new(file: FileId, start: u32, end: u32) -> Self {
        Self { file, start, end }
    }

    pub const fn is_dummy(self) -> bool {
        self.file.0 == FileId::NONE.0
    }

    /// Merge two spans into one covering both. Returns `self` if `other` is
    /// DUMMY (and vice versa). If the two spans live in different files
    /// (rare — only happens in the test_runner's prelude+user splice when
    /// a parser construct straddles the boundary, which it shouldn't), the
    /// result is `self` to keep the parser's span tracking total.
    pub fn merge(self, other: Span) -> Span {
        if self.is_dummy() {
            return other;
        }
        if other.is_dummy() {
            return self;
        }
        if self.file != other.file {
            return self;
        }
        Span {
            file: self.file,
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

#[cfg(test)]
#[path = "span_test.rs"]
mod span_test;
