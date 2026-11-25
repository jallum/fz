//! Cheney forwarding: the collector's context and the one primitive that moves
//! a value's object from from-space into to-space.

use super::super::Heap;
use super::super::ref_io::strict_object_size;
use super::super::schema::SchemaRegistry;
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
    scalar_boxes: u64,
}

impl<'a> Tracer<'a> {
    pub(in super::super) fn new(from_space: FromSpace, heap: &'a mut Heap, schemas: &'a SchemaRegistry) -> Self {
        let worklist = std::mem::take(&mut heap.worklist);
        Self {
            from_space,
            heap,
            schemas,
            worklist,
            scalar_boxes: 0,
        }
    }

    /// How many objects the collection kept, and how many scalar boxes its
    /// roots copied besides. Every kept object went through the worklist, so
    /// its length is the count; a scalar box is copied without being queued.
    /// The worklist goes back to the heap emptied, with the capacity it grew
    /// to.
    pub(in super::super) fn finish(self) -> (u64, u64) {
        let Self {
            heap,
            mut worklist,
            scalar_boxes,
            ..
        } = self;
        let kept = worklist.len() as u64;
        worklist.clear();
        heap.worklist = worklist;
        (kept, scalar_boxes)
    }

    /// Forward a root. A boxed scalar root is the one place a scalar box is
    /// copied: its 16 bytes move and the root points at the copy. Any other root
    /// forwards as the word it is.
    pub(in super::super) fn forward_root(&mut self, root: &mut AnyValueRef) {
        let kind = root.tag();
        debug_assert!(
            !kind.is_destination(),
            "a root is a value; a destination names only a slot"
        );
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
        // One range test sorts out the scalar kinds a slot mostly holds; only a
        // kind inside the range (the heap kinds, pid, reference, destination)
        // looks further.
        if kind.may_need_forwarding() {
            if kind.is_heap() {
                unsafe { write(slot, self.forward(slot.read(), kind)) };
            } else if kind.is_destination() {
                unsafe { write(slot, self.forward_destination(slot.read())) };
            }
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
        write_forwarding_marker(p, kind, copy);
        self.worklist.push(CopiedObject { ptr: copy, kind });
        copy
    }

    fn copy_scalar_box(&mut self, p: *mut u8) -> *mut u8 {
        let copy = self.copy_to_space(p, 16);
        self.scalar_boxes += 1;
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
