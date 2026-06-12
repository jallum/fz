//! Diagnostic value type (fz-ul4.20.5).
//!
//! `Diagnostic` is the structured form that every error/warning in the
//! pipeline produces. The renderer (.20.6) consumes it; .20.7 wires every
//! existing error site through this type.

use std::fmt::{self, Display, Formatter};

use crate::compiler::source::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

/// Stable, grep-able diagnostic identifier — format `<stage>/<kind>`.
/// Constants for every code live in `src/diag/codes.rs`; this struct just
/// wraps the underlying `&'static str` so the renderer can match on it
/// and the test suite can refer to codes by name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DiagCode(pub &'static str);

impl Display for DiagCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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

    pub fn from_vec(diags: Vec<Diagnostic>) -> Self {
        Self { diags }
    }

    pub fn push(&mut self, d: Diagnostic) {
        self.diags.push(d);
    }

    pub fn extend(&mut self, other: Diagnostics) {
        self.diags.extend(other.diags);
    }

    pub fn len(&self) -> usize {
        self.diags.len()
    }

    /// fz-d5b — slice view for callers that want to pass the whole
    /// collection to `report_or_exit` without cloning.
    pub fn as_slice(&self) -> &[Diagnostic] {
        &self.diags
    }
}

impl From<Diagnostic> for Diagnostics {
    fn from(d: Diagnostic) -> Self {
        Self::from_one(d)
    }
}

#[cfg(test)]
#[path = "diagnostic_test.rs"]
mod diagnostic_test;
