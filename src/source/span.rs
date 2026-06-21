//! Span: byte-offset source position keyed by source::Id.
//!
//! Spans are intentionally narrow (Copy, 12 bytes) and carry no source bytes.
//! The SourceMap holds the bytes; the renderer resolves spans to display
//! line/col on demand. This keeps the AST/IR cheap to copy.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id(pub u32);

impl Id {
    /// Sentinel for "no file" — used by Span::DUMMY.
    pub const NONE: Id = Id(u32::MAX);
}

/// A half-open byte range `[start, end)` within a single source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub code_id: Id,
    pub start: u32,
    pub end: u32,
}

/// Where an AST node's span came from. `Source` — the common case — means a
/// real token in the user's source produced this node. `Expanded` records
/// that the node was synthesized by a macro: `macro_call` is the span of
/// the user's `Foo(args)` invocation, `definition` (when present) is the
/// span of `defmacro Foo …` so a diagnostic can point at the macro itself.
///
/// The renderer consults this when drawing the trailer:
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
        code_id: Id::NONE,
        start: 0,
        end: 0,
    };

    pub const fn new(code_id: Id, start: u32, end: u32) -> Self {
        Self { code_id, start, end }
    }

    pub const fn is_dummy(self) -> bool {
        self.code_id.0 == Id::NONE.0
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
        if self.code_id != other.code_id {
            return self;
        }
        Span {
            code_id: self.code_id,
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

#[cfg(test)]
#[path = "span_test.rs"]
mod span_test;
