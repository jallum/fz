//! Diagnostic infrastructure (fz-ul4.20 arc).
//!
//! Source-location primitives live in `source`; this module owns the
//! structured diagnostic value, rendering, and driver glue that consume those
//! source facts.

pub mod codes;
pub mod diagnostic;
pub mod driver;
#[cfg(test)]
pub mod render;
#[cfg(test)]
pub mod style;

pub use diagnostic::{Diagnostic, Diagnostics};
