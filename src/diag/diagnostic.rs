//! Diagnostic value type (fz-ul4.20.5).
//!
//! `Diagnostic` is the structured form that every error/warning in the
//! pipeline produces. The renderer (.20.6) consumes it; .20.7 wires every
//! existing error site through this type.

use super::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Note,
    Help,
}

/// Stable, grep-able diagnostic identifier — format `<stage>/<kind>`.
/// Constants for every code live in `src/diag/codes.rs`; this struct just
/// wraps the underlying `&'static str` so the renderer can match on it
/// and the test suite can refer to codes by name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DiagCode(pub &'static str);

impl std::fmt::Display for DiagCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}

/// A span with an optional short label rendered under the caret. Long
/// explanation belongs in `Diagnostic.notes`; keep labels to a phrase.
#[derive(Debug, Clone)]
pub struct SpanLabel {
    pub span: Span,
    pub label: String,
}

impl SpanLabel {
    pub fn new(span: Span, label: impl Into<String>) -> Self {
        Self {
            span,
            label: label.into(),
        }
    }

    pub fn bare(span: Span) -> Self {
        Self {
            span,
            label: String::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: DiagCode,
    /// Headline. One short sentence. Renders on the first line.
    pub message: String,
    /// Primary span: the one location the diagnostic is "about".
    pub primary: SpanLabel,
    /// Secondary spans, drawn after the primary block.
    pub secondaries: Vec<SpanLabel>,
    /// `= note: <text>` lines rendered under the primary block.
    pub notes: Vec<String>,
    /// `= help: <text>` lines. Text-only in v1; structured fixits later.
    pub helps: Vec<String>,
    /// Macro-expansion lineage. When the offending node carries
    /// `SpanOrigin::Expanded`, the producer populates this with the
    /// `macro_call` (and `definition` when known) so the renderer can
    /// emit "= expanded from `<macro>` at <file>:<line>:<col>" trailers.
    pub expanded_from: Vec<Span>,
}

impl Diagnostic {
    pub fn error(code: DiagCode, message: impl Into<String>, primary: Span) -> Self {
        Self::new(Severity::Error, code, message, primary)
    }

    pub fn warning(code: DiagCode, message: impl Into<String>, primary: Span) -> Self {
        Self::new(Severity::Warning, code, message, primary)
    }

    fn new(severity: Severity, code: DiagCode, message: impl Into<String>, primary: Span) -> Self {
        Self {
            severity,
            code,
            message: message.into(),
            primary: SpanLabel::bare(primary),
            secondaries: Vec::new(),
            notes: Vec::new(),
            helps: Vec::new(),
            expanded_from: Vec::new(),
        }
    }

    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.primary.label = label.into();
        self
    }

    pub fn with_secondary(mut self, span: Span, label: impl Into<String>) -> Self {
        self.secondaries.push(SpanLabel::new(span, label));
        self
    }

    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.helps.push(help.into());
        self
    }

    pub fn with_expanded_from(mut self, span: Span) -> Self {
        self.expanded_from.push(span);
        self
    }
}

/// Accumulator for diagnostics. Stages return `Result<T, Diagnostics>`;
/// warnings ride along an `Ok` via the type's `extend` semantics. v1
/// stages may bail on the first error, but the wire format already
/// supports multi-error so "collect all parse errors" later doesn't
/// break consumers.
#[derive(Debug, Default, Clone)]
pub struct Diagnostics {
    diags: Vec<Diagnostic>,
}

impl Diagnostics {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_one(d: Diagnostic) -> Self {
        Self { diags: vec![d] }
    }

    pub fn push(&mut self, d: Diagnostic) {
        self.diags.push(d);
    }

    pub fn extend(&mut self, other: Diagnostics) {
        self.diags.extend(other.diags);
    }

    pub fn has_errors(&self) -> bool {
        self.diags.iter().any(|d| d.severity == Severity::Error)
    }

    pub fn is_empty(&self) -> bool {
        self.diags.is_empty()
    }

    pub fn len(&self) -> usize {
        self.diags.len()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Diagnostic> {
        self.diags.iter()
    }

    /// fz-d5b — slice view for callers that want to pass the whole
    /// collection to `report_or_exit` without cloning.
    pub fn as_slice(&self) -> &[Diagnostic] {
        &self.diags
    }

    pub fn into_vec(self) -> Vec<Diagnostic> {
        self.diags
    }
}

impl From<Diagnostic> for Diagnostics {
    fn from(d: Diagnostic) -> Self {
        Self::from_one(d)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::span::{FileId, Span};

    fn s(start: u32, end: u32) -> Span {
        Span::new(FileId(0), start, end)
    }

    #[test]
    fn error_constructor_carries_severity_and_code() {
        let code = DiagCode("type/unreachable-arm");
        let d = Diagnostic::error(code, "the then branch is never reachable", s(0, 5));
        assert_eq!(d.severity, Severity::Error);
        assert_eq!(d.code, code);
        assert_eq!(d.message, "the then branch is never reachable");
        assert_eq!(d.primary.span, s(0, 5));
        assert!(d.primary.label.is_empty());
        assert!(d.notes.is_empty());
    }

    #[test]
    fn builder_methods_chain() {
        let d = Diagnostic::warning(DiagCode("test/code"), "headline", s(0, 5))
            .with_label("primary label")
            .with_secondary(s(10, 15), "secondary label")
            .with_note("first note")
            .with_note("second note")
            .with_help("did you mean foo?")
            .with_expanded_from(s(20, 30));
        assert_eq!(d.primary.label, "primary label");
        assert_eq!(d.secondaries.len(), 1);
        assert_eq!(d.secondaries[0].span, s(10, 15));
        assert_eq!(d.notes, vec!["first note", "second note"]);
        assert_eq!(d.helps, vec!["did you mean foo?"]);
        assert_eq!(d.expanded_from, vec![s(20, 30)]);
    }

    #[test]
    fn diagnostics_accumulator_tracks_errors() {
        let mut ds = Diagnostics::new();
        assert!(ds.is_empty());
        assert!(!ds.has_errors());
        ds.push(Diagnostic::warning(DiagCode("a/b"), "warn", s(0, 1)));
        assert!(!ds.has_errors());
        ds.push(Diagnostic::error(DiagCode("a/c"), "err", s(0, 1)));
        assert!(ds.has_errors());
        assert_eq!(ds.len(), 2);
    }

    #[test]
    fn diagnostics_extend_merges_lists() {
        let mut a = Diagnostics::new();
        a.push(Diagnostic::warning(DiagCode("a/1"), "x", s(0, 1)));
        let mut b = Diagnostics::new();
        b.push(Diagnostic::error(DiagCode("a/2"), "y", s(2, 3)));
        b.push(Diagnostic::error(DiagCode("a/3"), "z", s(4, 5)));
        a.extend(b);
        assert_eq!(a.len(), 3);
        assert!(a.has_errors());
    }

    #[test]
    fn diagnostic_code_renders_as_its_string() {
        let c = DiagCode("foo/bar");
        assert_eq!(format!("{}", c), "foo/bar");
    }
}
