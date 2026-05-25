//! Cheney garbage collection: forwarding, tracing, marker I/O.

pub(in crate::heap) mod forward;
pub(in crate::heap) mod forwarding;
pub(in crate::heap) mod trace;
