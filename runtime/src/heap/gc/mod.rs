//! Cheney garbage collection: from-space, forwarding, tracing, marker I/O.

use crate::any_value::ValueKind;

pub(super) mod forward;
pub(super) mod forwarding;
mod from_space;
mod holes;
pub(super) mod roots;
pub(super) mod trace;

/// A to-space object queued for scanning, with the kind that picks its tracer.
#[derive(Clone, Copy)]
pub(super) struct CopiedObject {
    pub(super) ptr: *mut u8,
    pub(super) kind: ValueKind,
}

pub(super) use forward::Tracer;
pub(super) use from_space::FromSpace;
