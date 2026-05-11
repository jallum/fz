//! Span: byte-offset source position keyed by FileId.
//!
//! Spans are intentionally narrow (Copy, 12 bytes) and carry no source bytes.
//! The SourceMap holds the bytes; the renderer resolves spans to display
//! line/col on demand. This keeps the AST/IR cheap to copy.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

    pub const fn len(self) -> u32 {
        self.end - self.start
    }

    pub const fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// Merge two spans into one covering both. Both must be non-DUMMY and
    /// in the same file. Returns `self` if `other` is DUMMY (and vice versa).
    pub fn merge(self, other: Span) -> Span {
        if self.is_dummy() {
            return other;
        }
        if other.is_dummy() {
            return self;
        }
        debug_assert_eq!(
            self.file, other.file,
            "Span::merge across files (self={:?}, other={:?})",
            self, other
        );
        Span {
            file: self.file,
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dummy_is_dummy() {
        assert!(Span::DUMMY.is_dummy());
        assert!(!Span::new(FileId(0), 0, 1).is_dummy());
    }

    #[test]
    fn len_and_is_empty() {
        let s = Span::new(FileId(0), 4, 10);
        assert_eq!(s.len(), 6);
        assert!(!s.is_empty());
        let z = Span::new(FileId(0), 4, 4);
        assert!(z.is_empty());
        assert_eq!(z.len(), 0);
    }

    #[test]
    fn merge_returns_enclosing() {
        let a = Span::new(FileId(0), 4, 8);
        let b = Span::new(FileId(0), 6, 12);
        let m = a.merge(b);
        assert_eq!(m, Span::new(FileId(0), 4, 12));
    }

    #[test]
    fn merge_disjoint_ranges_unions_outer_bounds() {
        let a = Span::new(FileId(0), 0, 4);
        let b = Span::new(FileId(0), 10, 12);
        let m = a.merge(b);
        assert_eq!(m, Span::new(FileId(0), 0, 12));
    }

    #[test]
    fn merge_with_dummy_returns_other() {
        let a = Span::new(FileId(0), 4, 8);
        assert_eq!(a.merge(Span::DUMMY), a);
        assert_eq!(Span::DUMMY.merge(a), a);
    }

    #[test]
    fn span_is_copy_12_bytes() {
        assert_eq!(std::mem::size_of::<Span>(), 12);
        let a = Span::new(FileId(0), 1, 2);
        let _b = a; // moves are copies
        let _c = a;
    }
}
