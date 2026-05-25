//! Oversized-object fragment list + shared CopiedObject queue entry.

use super::block_pool::SIZE_TABLE;
use std::alloc::Layout;

#[derive(Clone, Copy)]
pub(super) struct CopiedObject {
    pub(super) ptr: *mut u8,
    pub(super) tag: u64,
}

/// fz-q8d.4 — objects larger than the largest size_class are allocated as
/// their own system-allocator backed fragment, bypassing the bump arena.
/// Threshold is the largest entry of `SIZE_TABLE`; anything strictly
/// larger goes to fragments.
pub(super) const FRAGMENT_THRESHOLD: usize = SIZE_TABLE[SIZE_TABLE.len() - 1];

/// fz-q8d.4 — a single oversized allocation outside the bump arena.
/// Participates in GC via a mark bit instead of being copied.
pub(super) struct Fragment {
    pub(super) ptr: *mut u8,
    pub(super) size: usize,
    pub(super) layout: Layout,
    pub(super) mark: bool,
}

pub(super) fn mark_fragment_for_tracing(
    p: *mut u8,
    tag: u64,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
) -> bool {
    let Some(idx) = classify_fragment(p, fragments) else {
        return false;
    };
    if !fragments[idx].mark {
        fragments[idx].mark = true;
        frag_queue.push(CopiedObject { ptr: p, tag });
    }
    true
}

pub(super) fn classify_fragment(p: *mut u8, fragments: &[Fragment]) -> Option<usize> {
    fragments
        .iter()
        .position(|f| p >= f.ptr && p < unsafe { f.ptr.add(f.size) })
}
