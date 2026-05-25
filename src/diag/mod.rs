//! Diagnostic infrastructure (fz-ul4.20 arc).
//!
//! `span` and `source_map` are the .20.1 foundations: byte-offset Spans
//! keyed by FileId, plus a SourceMap that owns the files and resolves
//! display location on demand.
//!
//! Later children of .20 add the Diagnostic type (.20.5) and the renderer
//! (.20.6) into this module.

pub mod codes;
pub mod diagnostic;
pub mod driver;
pub mod render;
pub mod source_map;
pub mod span;
pub mod style;

pub use diagnostic::{Diagnostic, Diagnostics};
pub use driver::{render_one_to_string, report_or_exit_through};
pub use source_map::SourceMap;
pub use span::{FileId, Span, SpanOrigin};

// Location / SourceFile are part of the .20.6 renderer's input surface;
// no consumer references them yet, so the explicit re-exports stay out
// of the public surface until .20.6 needs them.
