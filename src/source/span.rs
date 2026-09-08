//! Span: byte-offset source position keyed by `SourceVersion`.
//!
//! Spans are intentionally narrow (Copy, 12 bytes) and carry no source bytes.
//! The SourceMap holds the bytes; the renderer resolves spans to display
//! line/col on demand. This keeps the AST/IR cheap to copy.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceVersion(u32);

impl SourceVersion {
    /// Sentinel for "no file" — used by Span::DUMMY.
    pub const NONE: SourceVersion = SourceVersion(u32::MAX);

    pub(super) const fn from_encoded(raw: u32) -> Self {
        Self(raw)
    }

    pub(crate) const fn from_index(index: usize) -> Self {
        Self(index as u32)
    }

    pub(crate) const fn index(self) -> usize {
        self.0 as usize
    }

    pub const fn as_u32(self) -> u32 {
        self.0
    }
}

/// A half-open byte range `[start, end)` within a single source file.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq, Hash)]
pub struct Span {
    pub source_version: SourceVersion,
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
        source_version: SourceVersion::NONE,
        start: 0,
        end: 0,
    };

    pub const fn new(source_version: SourceVersion, start: u32, end: u32) -> Self {
        Self {
            source_version,
            start,
            end,
        }
    }

    pub const fn is_dummy(self) -> bool {
        self.source_version.0 == SourceVersion::NONE.0
    }

    pub(crate) const fn length(self) -> u32 {
        assert!(self.end >= self.start, "span end must not precede its start");
        self.end - self.start
    }

    /// Merge two spans into one covering both. Returns `self` if `other` is
    /// DUMMY (and vice versa). Spans from different immutable versions cannot
    /// be merged; the result is `self` to keep span tracking total.
    pub fn merge(self, other: Span) -> Span {
        if self.is_dummy() {
            return other;
        }
        if other.is_dummy() {
            return self;
        }
        if self.source_version != other.source_version {
            return self;
        }
        Span {
            source_version: self.source_version,
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

#[cfg(test)]
#[path = "span_test.rs"]
mod span_test;
