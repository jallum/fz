//! Diagnostic infrastructure (fz-ul4.20 arc).
//!
//! Source-location primitives live in `compiler::source`; this module owns the
//! structured diagnostic value, rendering, and driver glue that consume those
//! source facts.

pub mod codes;
pub mod diagnostic;
pub mod driver;
pub mod render;
pub mod style;

pub use diagnostic::{Diagnostic, Diagnostics};
pub use driver::{emit_through, render_one_to_string, report_or_exit_through};
