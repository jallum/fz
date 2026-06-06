//! Module subsystem facade.
//!
//! Keep graph traversal, interfaces, identities, and runtime-library module
//! provenance behind this package boundary. Compiler stages should use the
//! narrow types they need instead of depending on every module
//! implementation detail directly.

pub(crate) mod graph;
pub(crate) mod identity;
pub(crate) mod interface;
pub(crate) mod pipeline;
pub(crate) mod runtime_library;
