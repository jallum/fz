//! Open-shape map keys are concrete singleton values.
//!
//! The atom/int projection lives on [`crate::ground_value::GroundValue`] so
//! that `ground_value` stays the crate's single leaf definition of "a ground
//! literal value" and its narrowings; this module re-exports it rather than
//! keeping a second copy.
pub use crate::ground_value::MapKey;
