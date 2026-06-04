//! Cheney garbage collection: forwarding, tracing, marker I/O.

pub(super) mod forward;
pub(super) mod forwarding;
pub(super) mod trace;

pub(super) use forward::{cheney_forward_strict_bits, forward_any_value_ref_root};
pub(super) use trace::{
    cheney_trace_closure, cheney_trace_list, cheney_trace_map, cheney_trace_resource, cheney_trace_struct,
};
