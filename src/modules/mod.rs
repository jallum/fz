//! Module subsystem facade.
//!
//! Keep module identity, public contracts, runtime-library source, and the
//! compiler-owned execution pipeline behind this package boundary.

pub(crate) mod identity;
pub(crate) mod interface;
pub(crate) mod pipeline;
pub(crate) mod runtime_library;
