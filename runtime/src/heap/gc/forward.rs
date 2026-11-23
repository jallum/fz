//! Cheney forwarding: the collector's context and the one primitive that moves
//! a value's object from from-space into to-space.

use super::super::Heap;
use super::super::ref_io::strict_object_size;
use super::super::schema::SchemaRegistry;
use super::super::stats::GcStats;
use super::forwarding::{forwarded_target, write_forwarding_marker};
use super::{CopiedObject, FromSpace};
use crate::any_value::{AnyValueRef, AnyValueRefPacking, ValueKind};
use std::ptr::{copy_nonoverlapping, write};

/// One collection's working state: what moves, where it goes, and the queue of
/// copied objects whose own edges are still to be forwarded.
pub(in super::super) struct Tracer<'a> {
    pub(super) from_space: FromSpace,
    pub(super) heap: &'a mut Heap,
    pub(super) schemas: &'a SchemaRegistry,
    pub(super) worklist: Vec<CopiedObject>,
    pub(super) stats: GcStats,
}

impl<'a> Tracer<'a> {
    pub(in super::super) fn new(
        from_space: FromSpace,
        heap: &'a mut Heap,
        schemas: &'a SchemaRegistry,
        stats: GcStats,
    ) -> Self {
        Self {
            from_space,
            heap,
            schemas,
            worklist: Vec::new(),
            stats,
        }
    }

    /// The collection's stats and how many objects it kept.
    pub(in super::super) fn finish(self) -> (GcStats, u64) {
        (self.stats, self.worklist.len() as u64)
    }

    /// Forward a root. A boxed scalar root is the one place a scalar box is
    /// copied: its 16 bytes move and the root points at the copy. Any other root
    /// forwards as the word it is.
    pub(in super::super) fn forward_root(&mut self, root: &mut AnyValueRef) {
        let kind = root.tag();
        if kind.is_boxed_scalar() {
            let p = root.storage_addr();
            if self.from_space.moves(self.heap, p, root.is_literal()) {
                let copy = self.copy_scalar_box(p);
                *root = AnyValueRef::from_scalar_slot(kind, copy as *const u64).expect("forwarded scalar root ref");
            }
            return;
        }
        let word = self.forward(root.raw_word(), kind);
        *root = AnyValueRef::from_raw_word(word).expect("forwarded root ref");
    }

    /// Forward the value stored in `slot`, whose kind is `kind`, and store the
    /// word that results. A slot that holds no heap reference is not touched.
    ///
    /// # Safety
    /// `slot` must be a readable, writable word in a to-space object.
    #[inline(always)]
    pub(super) unsafe fn forward_slot(&mut self, slot: *mut u64, kind: ValueKind) {
        if kind.is_heap() {
            unsafe { write(slot, self.forward(slot.read(), kind)) };
        }
    }

    /// The word that names `word`'s object after the collection: `word`
    /// itself unless `kind` is a heap kind whose non-null object this
    /// collection moves, in which case the object is copied (once) and the
    /// word names the copy. Only the address bits change, so a word that
    /// carries a tag above its address keeps it.
    ///
    /// Inlined into every trace loop because the trace's speed depends on it;
    /// leaving it to the optimizer lets a codegen-unit split change the choice.
    #[inline(always)]
    pub(super) fn forward(&mut self, word: u64, kind: ValueKind) -> u64 {
        if !kind.is_heap() {
            return word;
        }
        let packing = AnyValueRefPacking::current();
        let addr = packing.raw_address(word) as *mut u8;
        if addr.is_null() || !self.from_space.moves(self.heap, addr, packing.is_literal(word)) {
            return word;
        }
        let copy = self.copy_object(kind, addr);
        (word & !packing.address_mask()) | copy as u64
    }

    /// Move the object of `kind` at `p` into to-space unless an earlier visit
    /// already did, and return its to-space address.
    fn copy_object(&mut self, kind: ValueKind, p: *mut u8) -> *mut u8 {
        if let Some(forwarded) = forwarded_target(p, kind) {
            return forwarded;
        }
        let size = strict_object_size(kind, p, self.schemas);
        let copy = self.copy_to_space(p, size);
        self.stats.copied_objects += 1;
        self.stats.copied_bytes += size as u64;
        write_forwarding_marker(p, kind, copy);
        self.worklist.push(CopiedObject { ptr: copy, kind });
        copy
    }

    fn copy_scalar_box(&mut self, p: *mut u8) -> *mut u8 {
        let copy = self.copy_to_space(p, 16);
        self.stats.copied_objects += 1;
        self.stats.copied_bytes += 16;
        copy
    }

    /// Copy `size` bytes at `p` to where the heap's to-space bump places them,
    /// so to-space is the tip plus the overflow blocks it parks.
    fn copy_to_space(&mut self, p: *mut u8, size: usize) -> *mut u8 {
        let dst = self.heap.bump_to_space(size);
        unsafe {
            copy_nonoverlapping(p, dst, size);
        }
        dst
    }
}

#[cfg(test)]
#[path = "forward_test.rs"]
mod forward_test;
