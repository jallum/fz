//! Cheney garbage collection: forwarding, tracing, marker I/O.

use crate::any_value::ValueKind;

pub(super) mod forward;
pub(super) mod forwarding;
pub(super) mod trace;

/// A to-space object queued for scanning, with the kind that picks its tracer.
#[derive(Clone, Copy)]
pub(super) struct CopiedObject {
    pub(super) ptr: *mut u8,
    pub(super) kind: ValueKind,
}

pub(super) use forward::{forward_any_value_ref_root, forward_heap_value};
pub(super) use trace::{
    cheney_trace_closure, cheney_trace_list, cheney_trace_map, cheney_trace_resource, cheney_trace_struct,
};
