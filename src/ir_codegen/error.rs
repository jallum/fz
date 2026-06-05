use crate::diag::codes::CODEGEN_SCHEMA_MISSING;
use crate::diag::{Diagnostic, Span};
use std::error::Error;
use std::fmt::{self, Display, Formatter};

/// Errors from `compile()`. Backend-plumbing failures carry `Span::DUMMY`
/// because they're internal — no fz source position maps to "cranelift
/// refused to declare a host function". Per-fn verify/define paths
/// populate `span` so the diagnostic underlines the offending fn.
#[derive(Debug, Clone)]
pub struct CodegenError {
    pub message: String,
    pub span: Span,
}
impl CodegenError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span: Span::DUMMY,
        }
    }
    pub fn with_span(mut self, span: Span) -> Self {
        self.span = span;
        self
    }
    pub fn to_diagnostic(&self) -> Diagnostic {
        Diagnostic::error(CODEGEN_SCHEMA_MISSING, format!("codegen: {}", self.message), self.span)
    }
}
impl Display for CodegenError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "codegen: {}", self.message)
    }
}
impl Error for CodegenError {}
impl From<String> for CodegenError {
    fn from(s: String) -> Self {
        Self::new(s)
    }
}
