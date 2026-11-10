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

/// What a collection knows about from-space beyond the literal bit.
///
/// The collector decides "copy or leave" from the pointer's own literal bit.
/// A debug build also keeps the from-space block ranges and checks that the bit
/// agrees with where the pointer lies: an untagged pointer is in from-space, a
/// tagged one is not, and neither is in to-space. A release build keeps nothing.
pub(super) struct FromSpace {
    #[cfg(debug_assertions)]
    ranges: Vec<(*mut u8, *mut u8)>,
}

impl FromSpace {
    /// The from-space of a collection about to start: every block `heap` owns now.
    pub(super) fn of(heap: &super::Heap) -> Self {
        #[cfg(debug_assertions)]
        {
            Self {
                ranges: heap.block_ranges().collect(),
            }
        }
        #[cfg(not(debug_assertions))]
        {
            let _ = heap;
            Self {}
        }
    }

    /// Debug-only: assert that `literal` agrees with where `p` lies.
    #[inline]
    pub(super) fn assert_classified(&self, heap: &super::Heap, p: *mut u8, literal: bool) {
        #[cfg(debug_assertions)]
        {
            use super::ref_io::ptr_in_ranges;
            let in_from_space = ptr_in_ranges(p, self.ranges.iter().copied());
            assert_eq!(
                in_from_space,
                !literal,
                "{p:p} is {} but lies {} from-space",
                if literal {
                    "tagged literal"
                } else {
                    "an untagged heap pointer"
                },
                if in_from_space { "in" } else { "outside" },
            );
            assert!(
                !ptr_in_ranges(p, heap.block_ranges()),
                "{p:p} lies in to-space while it is being forwarded"
            );
        }
        #[cfg(not(debug_assertions))]
        let _ = (heap, p, literal);
    }
}

pub(super) use forward::{forward_any_value_ref_root, forward_heap_value};
pub(super) use trace::{
    cheney_trace_closure, cheney_trace_list, cheney_trace_map, cheney_trace_resource, cheney_trace_struct,
};
