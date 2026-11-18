//! A heap's one off-heap list.
//!
//! Every object on a heap that owns a reference outside the heap (a `BinRef`
//! holding a `SharedBin`, a resource stub holding a `Resource`) is on one
//! intrusive chain per generation (`Heap::off_heap_head`,
//! `Heap::off_heap_old_head`), linked through the `off_heap_next` word in its
//! payload. This module owns what walks that chain:
//!
//!   * `OffHeap` — the chain's two object kinds, told apart by the kind tag
//!     in each link.
//!   * `sweep` — the post-Cheney sweep: rewrites survivors to their
//!     to-space copy and releases dead entries' references.
//!   * `drop_all`, `release_chain` — release every entry
//!     when a heap or a gift is dropped.

use crate::any_value::{ValueKind, heap_kind_from_tagged, heap_object_word, heap_word_addr};
use crate::bits::{BinRef, shared_bin_release};
use crate::heap::{Generation, Heap, StubCounts, forwarded_target};
use crate::resource::{ResourceStub, fz_resource_release, fz_resource_release_deferred};

/// An object on a heap's one off-heap chain: a BinRef or a resource stub. Both
/// are 16 bytes with the shared pointer first and the link second, and each
/// link names its object by the kind tag of its heap object word, as OTP tells
/// a ProcBin (OTP's name for a BinRef) from a magic binary on its one off-heap list.
#[derive(Clone, Copy)]
pub(crate) enum OffHeap {
    BinRef(BinRef),
    Resource(ResourceStub),
}

impl OffHeap {
    /// The object a chain link names. A link is a heap object word: the
    /// object's kind rides above its address.
    fn named_by(link: u64) -> Self {
        let addr = heap_word_addr(link);
        match heap_kind_from_tagged(link) {
            Some(ValueKind::BINREF) => Self::BinRef(unsafe { BinRef::from_raw(addr) }),
            Some(ValueKind::RESOURCE) => Self::Resource(unsafe { ResourceStub::from_raw(addr) }),
            _ => panic!("off-heap chain link {link:#x} names neither a BinRef nor a resource stub"),
        }
    }

    fn kind(&self) -> ValueKind {
        match self {
            Self::BinRef(_) => ValueKind::BINREF,
            Self::Resource(_) => ValueKind::RESOURCE,
        }
    }

    fn addr(&self) -> *mut u8 {
        match self {
            Self::BinRef(binref) => binref.as_raw(),
            Self::Resource(stub) => stub.as_raw(),
        }
    }

    /// The same kind of object at `addr`: where a survivor's to-space copy is.
    ///
    /// # Safety
    /// `addr` must point at a live object of this kind.
    unsafe fn same_kind_at(&self, addr: *mut u8) -> Self {
        match self {
            Self::BinRef(_) => Self::BinRef(unsafe { BinRef::from_raw(addr) }),
            Self::Resource(_) => Self::Resource(unsafe { ResourceStub::from_raw(addr) }),
        }
    }

    fn link(&self) -> u64 {
        match self {
            Self::BinRef(binref) => binref.off_heap_next(),
            Self::Resource(stub) => stub.off_heap_next(),
        }
    }

    fn set_link(&self, next: u64) {
        match self {
            Self::BinRef(binref) => binref.off_heap_next_set(next),
            Self::Resource(stub) => stub.off_heap_next_set(next),
        }
    }

    /// Drop the off-heap reference this object holds.
    fn release(&self) {
        match self {
            Self::BinRef(binref) => unsafe { shared_bin_release(binref.shared_raw()) },
            Self::Resource(stub) => unsafe { fz_resource_release(stub.shared_raw()) },
        }
    }
}

/// Point the link of the object that `link` names at `next`.
pub(crate) fn set_next(link: u64, next: u64) {
    OffHeap::named_by(link).set_link(next);
}

// ===== off-heap sweep + drop =====================================================

/// Decide every object on the chain a collection of `generation` examines: the
/// young chain, and for a major collection the old chain too. This is the one
/// place a dead object is handled, after a collection's trace and when a
/// process exits (a process exit is a major sweep with nothing live). Each
/// object is visited once, `visits` counting the chain links followed.
///
/// An object carrying a forwarding marker survived: it is relinked to its
/// to-space copy, on the old chain, which a minor sweep leaves otherwise
/// untouched and a major sweep rebuilds. Any other object is dead and drops its
/// off-heap reference. A dead BinRef releases its SharedBin synchronously. A
/// dead Resource whose last reference this was pushes its destructor (a literal
/// closure word) and raw payload onto `pending_dtors`, unless it was claimed;
/// the destructor is fz code and runs at the scheduler boundary, never inside
/// the sweep.
///
/// Returns the capacity of the SharedBins the surviving BinRefs hold.
///
/// A survivor's from-space word 0 holds a forwarding marker, so its off-heap
/// pointer is read from the to-space copy. Must run before the from-space is
/// released, since dead objects live there.
pub fn sweep(heap: &mut Heap, generation: Generation, visits: &mut u64, survived: &mut StubCounts) -> usize {
    let mut survivor_binary_bytes = 0;
    let mut new_old_head = match generation {
        Generation::Minor => heap.off_heap_old_head,
        Generation::Major => 0,
    };
    let old_head = (generation == Generation::Major).then_some(heap.off_heap_old_head);
    for head in std::iter::once(heap.off_heap_head).chain(old_head) {
        let mut cur_bits = head;
        while cur_bits != 0 {
            *visits += 1;
            let object = OffHeap::named_by(cur_bits);
            let next = object.link();
            match forwarded_target(object.addr(), object.kind()) {
                Some(to_p) => {
                    let copy = unsafe { object.same_kind_at(to_p) };
                    if let OffHeap::BinRef(binref) = object {
                        survived.record(binref.site());
                    }
                    if let OffHeap::BinRef(kept) = copy {
                        survivor_binary_bytes += unsafe { (*kept.shared_raw()).capacity() };
                    }
                    copy.set_link(new_old_head);
                    new_old_head = heap_object_word(to_p, object.kind());
                }
                None => match object {
                    OffHeap::BinRef(binref) => unsafe { shared_bin_release(binref.shared_raw()) },
                    OffHeap::Resource(stub) => {
                        if let Some(dtor) = unsafe { fz_resource_release_deferred(stub.shared_raw()) } {
                            heap.pending_dtors.push_back(dtor);
                        }
                    }
                },
            }
            cur_bits = next;
        }
    }
    heap.off_heap_old_head = new_old_head;
    heap.off_heap_head = 0;
    survivor_binary_bytes
}

/// Drop every object on the young and old chains, releasing each off-heap
/// reference. Called from `Heap::drop` before pool reclaim.
pub fn drop_all(heap: &mut Heap) {
    release_chain(heap.off_heap_head);
    release_chain(heap.off_heap_old_head);
    heap.off_heap_head = 0;
    heap.off_heap_old_head = 0;
}

/// Release every object on the chain that starts at `head_bits`: each BinRef
/// drops its SharedBin reference and each Resource stub drops its Resource
/// reference. The chain's memory is left to its owner.
pub(crate) fn release_chain(head_bits: u64) {
    let mut cur_bits = head_bits;
    while cur_bits != 0 {
        let object = OffHeap::named_by(cur_bits);
        cur_bits = object.link();
        object.release();
    }
}

#[cfg(test)]
#[path = "off_heap_test.rs"]
mod off_heap_test;
