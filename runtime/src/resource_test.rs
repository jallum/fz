use super::*;
use crate::any_value::{AnyValueRef, heap_kind_from_tagged};
use crate::heap::{Generation, Heap, SIZE_TABLE, SchemaRegistry};
use std::cell::RefCell;
use std::rc::Rc;
use std::thread;

fn fresh_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

/// The destructor word every test resource carries; no test dispatches it.
const DESTRUCTOR: u64 = 0xD7;
const PAYLOAD: u64 = 0xfeed;

fn resource() -> ResourceHandle {
    ResourceHandle::new(PAYLOAD, DESTRUCTOR)
}

#[test]
fn a_resource_is_16_aligned_so_its_address_is_never_a_forwarding_marker() {
    // The stub holds this address in the word Cheney forwards through, so
    // an address with a set low nibble would read as forwarded.
    assert_eq!(align_of::<Resource>(), 16);
    assert_eq!(size_of::<Resource>(), RESOURCE_BYTES);
    assert_eq!(resource().as_raw() as usize % 16, 0);
}

/// The stub is the shared pointer and the chain link and nothing else: the
/// destructor lives on the shared Resource, so the stub is one 16-byte
/// allocation unit.
#[test]
fn a_resource_stub_is_16_bytes() {
    assert_eq!(RESOURCE_STUB_SIZE, 16);
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let rs = alloc_resource(&mut heap, resource());
    let tagged = heap_object_word(rs.as_raw(), ValueKind::RESOURCE);
    assert_eq!(object_size(tagged), 16);
}

#[test]
fn alloc_retain_release_pattern() {
    let p = resource().into_raw();
    unsafe {
        assert_eq!((*p).payload, PAYLOAD);
        assert_eq!((*p).destructor, DESTRUCTOR);
        fz_resource_retain(p);
        fz_resource_retain(p);
        assert_eq!((*p).refcount.load(Ordering::Relaxed), 3);
        fz_resource_release(p);
        fz_resource_release(p);
        assert_eq!((*p).refcount.load(Ordering::Relaxed), 1);
        fz_resource_release(p);
    }
}

#[test]
fn claiming_a_resource_disarms_its_fallback_destructor() {
    let handle = resource();
    assert!(unsafe { (*handle.as_raw()).claim() });
    assert!(!unsafe { (*handle.as_raw()).claim() }, "claim is one-shot");
    assert_eq!(
        unsafe { fz_resource_release_deferred(handle.into_raw()) },
        None,
        "a claimed resource queues no destructor"
    );
}

#[test]
fn an_alias_in_another_thread_observes_the_same_claim() {
    let handle = resource();
    let alias = handle.clone().into_raw() as usize;
    assert!(unsafe { (*handle.as_raw()).claim() });
    let observed = thread::spawn(move || unsafe { (*(alias as *mut Resource)).claim() })
        .join()
        .expect("claim observer thread should not panic");
    assert!(!observed, "the shared lifecycle admits exactly one claimant");
    drop(handle);
    assert_eq!(unsafe { fz_resource_release_deferred(alias as *mut Resource) }, None);
}

#[test]
fn handle_clone_retains_and_drop_releases() {
    let handle = resource();
    let second = handle.clone();
    assert_eq!(unsafe { (*handle.as_raw()).refcount.load(Ordering::Relaxed) }, 2);
    drop(handle);
    assert_eq!(unsafe { (*second.as_raw()).refcount.load(Ordering::Relaxed) }, 1);
}

/// Whichever thread drops the last reference is the one handed the
/// destructor: it queues exactly once.
#[test]
fn the_last_release_on_a_worker_hands_back_the_destructor_once() {
    let handle = resource();
    let address = handle.clone().into_raw() as usize;
    assert_eq!(unsafe { fz_resource_release_deferred(handle.into_raw()) }, None);
    let queued = thread::spawn(move || unsafe { fz_resource_release_deferred(address as *mut Resource) })
        .join()
        .unwrap();
    assert_eq!(queued, Some((DESTRUCTOR, PAYLOAD)));
}

#[test]
fn the_final_release_returns_the_destructor_closure_word_and_the_raw_payload() {
    let handle = resource();
    let second = handle.clone().into_raw();
    assert_eq!(unsafe { fz_resource_release_deferred(handle.into_raw()) }, None);
    assert_eq!(unsafe { (*second).refcount.load(Ordering::Relaxed) }, 1);
    assert_eq!(
        unsafe { fz_resource_release_deferred(second) },
        Some((DESTRUCTOR, PAYLOAD))
    );
}

#[test]
fn alloc_resource_pushes_into_the_off_heap_chain() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let rs = alloc_resource(&mut heap, resource());
    let tagged = heap_object_word(rs.as_raw() as *const u8, ValueKind::RESOURCE);
    assert_eq!(heap_kind_from_tagged(tagged), Some(ValueKind::RESOURCE));
    assert_eq!(object_size(tagged), RESOURCE_STUB_SIZE);
    assert_eq!(heap.off_heap_head, tagged);
    assert_eq!(rs.off_heap_next(), 0);
    assert_eq!(rs.payload(), PAYLOAD);
    assert_eq!(rs.destructor(), DESTRUCTOR);
    assert_eq!(rs.refcount(), 1);
}

/// A resource nothing reaches leaves the off-heap chain at a collection and queues
/// its destructor word with its raw payload: the queue holds no heap word, so
/// it needs no root and no collection can move it.
#[test]
fn a_dead_unclaimed_resource_queues_its_destructor_and_raw_payload() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    alloc_resource(&mut heap, resource());
    heap.collect_tagged(&mut null_mut());
    assert_eq!(heap.off_heap_head, 0, "dead Resource swept from the off-heap chain");
    assert_eq!(heap.pending_dtors, [(DESTRUCTOR, PAYLOAD)]);
}

/// A resource whose owner claimed it queues nothing when it dies.
#[test]
fn a_dead_claimed_resource_queues_nothing() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    assert!(alloc_resource(&mut heap, resource()).claim());
    heap.collect_tagged(&mut null_mut());
    assert!(heap.pending_dtors.is_empty());
}

/// The exit sweep is the collection sweep with nothing live.
#[test]
fn the_exit_sweep_queues_each_resource_destructor_newest_first() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    alloc_resource(&mut heap, ResourceHandle::new(1, DESTRUCTOR));
    alloc_resource(&mut heap, ResourceHandle::new(2, DESTRUCTOR));
    heap.release_resources_at_exit();
    assert_eq!(heap.pending_dtors, [(DESTRUCTOR, 2), (DESTRUCTOR, 1)]);
}

/// A resource that survives a collection keeps the destructor it was made
/// with, on the one shared Resource its relinked stub points at.
#[test]
fn a_resource_that_survives_a_collection_keeps_its_destructor() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let rs = alloc_resource(&mut heap, resource());
    let mut root = heap_object_word(rs.as_raw() as *const u8, ValueKind::RESOURCE) as *mut u8;
    heap.collect_tagged(&mut root);
    let moved = unsafe { ResourceStub::from_raw(resource_addr_from_tagged(root as u64).unwrap()) };
    assert_eq!(moved.destructor(), DESTRUCTOR);
    assert_eq!(moved.payload(), PAYLOAD);
    assert!(heap.pending_dtors.is_empty());
}

/// A sent resource is a second stub on the same Resource, so the destructor
/// is the one the sender made, and runs once when the last stub dies.
#[test]
fn a_deep_copied_resource_shares_its_resource_and_destructor() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut receiver = Heap::new(SIZE_TABLE[0], fresh_registry());
    let sent = alloc_resource(&mut sender, resource());
    let view = sender.view();
    let src = AnyValueRef::from_heap_object(ValueKind::RESOURCE, sent.as_raw() as *const u8).expect("ref");
    let copied = crate::heap::deep_copy_any_value_ref(src, &view, &mut receiver);
    let copy = unsafe { ResourceStub::from_raw(copied.resource_addr().expect("resource")) };
    assert_eq!(copy.shared_raw(), sent.shared_raw());
    assert_eq!(copy.destructor(), DESTRUCTOR);
    assert_eq!(copy.refcount(), 2);
    sender.release_resources_at_exit();
    assert!(sender.pending_dtors.is_empty(), "the receiver's stub still holds it");
    receiver.release_resources_at_exit();
    assert_eq!(receiver.pending_dtors, [(DESTRUCTOR, PAYLOAD)]);
}

/// A dead resource's destructor is queued by the collection that examines its
/// chain: a young one by the minor collection, an old one only by a major
/// collection, which is when OTP's full sweep finds an old resource dead.
#[test]
fn a_dead_old_resource_queues_its_destructor_at_the_next_major_collection_and_a_young_one_at_a_minor() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let old = alloc_resource(&mut heap, ResourceHandle::new(1, DESTRUCTOR));
    let mut roots = [AnyValueRef::from_raw_word(heap_object_word(old.as_raw(), ValueKind::RESOURCE)).expect("root")];
    assert_eq!(heap.collect_stats(&mut roots).generation, Generation::Minor);
    assert!(heap.pending_dtors.is_empty());

    alloc_resource(&mut heap, ResourceHandle::new(2, DESTRUCTOR));
    let stats = heap.collect_stats(&mut []);
    assert_eq!(stats.generation, Generation::Minor);
    assert_eq!(
        heap.pending_dtors,
        [(DESTRUCTOR, 2)],
        "the young resource's destructor is queued"
    );

    let mut cell = heap.alloc_list_cons_slot(AnyValue::int(0), crate::any_value::EMPTY_LIST);
    for head in 1..100 {
        cell = heap.alloc_list_cons_slot(AnyValue::int(head), cell);
    }
    let mut roots = [AnyValueRef::from_raw_word(cell).expect("list root")];
    assert_eq!(heap.collect_stats(&mut roots).generation, Generation::Minor);
    assert_eq!(
        heap.pending_dtors.len(),
        1,
        "a minor collection does not look at the old resource"
    );

    let stats = heap.collect_stats(&mut roots);
    assert_eq!(stats.generation, Generation::Major);
    assert_eq!(
        heap.pending_dtors,
        [(DESTRUCTOR, 2), (DESTRUCTOR, 1)],
        "the major collection found the old resource dead"
    );
}

#[test]
fn resource_forwarding_marker_through_gc() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let rs = alloc_resource(&mut heap, resource());
    let from = rs.as_raw();
    let shared = rs.shared_raw();
    let mut root = heap_object_word(from as *const u8, ValueKind::RESOURCE) as *mut u8;
    heap.collect_tagged(&mut root);
    let to = resource_addr_from_tagged(root as u64).unwrap();
    assert_ne!(to, from);
    assert_eq!(unsafe { ResourceStub::from_raw(to).shared_raw() }, shared);
    assert_eq!(
        heap.off_heap_old_head,
        heap_object_word(to as *const u8, ValueKind::RESOURCE)
    );
    assert_eq!(heap.off_heap_head, 0);
    assert!(heap.pending_dtors.is_empty());
}

#[test]
fn binrefs_and_resources_interleave_on_one_chain() {
    use crate::bits::{SharedBinHandle, alloc_buffer_view};
    use crate::heap::StubSite;
    let first_bin = SharedBinHandle::from_bytes(&[1, 2, 3]);
    let second_bin = SharedBinHandle::from_bytes(&[4, 5]);
    {
        let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
        let pb1 = alloc_buffer_view(
            &mut heap,
            first_bin.clone(),
            first_bin.bytes_len() as u64 * 8,
            StubSite::FilledBuffer,
        );
        let rs1 = alloc_resource(&mut heap, resource());
        let pb2 = alloc_buffer_view(
            &mut heap,
            second_bin.clone(),
            second_bin.bytes_len() as u64 * 8,
            StubSite::FilledBuffer,
        );
        let rs2 = alloc_resource(&mut heap, resource());
        let rs2_bits = heap_object_word(rs2.as_raw(), ValueKind::RESOURCE);
        let pb2_bits = pb2.binref().word();
        let pb1_bits = pb1.binref().word();
        let rs1_bits = heap_object_word(rs1.as_raw(), ValueKind::RESOURCE);
        assert_eq!(heap.off_heap_head, rs2_bits);
        assert_eq!(rs2.off_heap_next(), pb2_bits);
        assert_eq!(pb2.binref().off_heap_next(), rs1_bits);
        assert_eq!(rs1.off_heap_next(), pb1_bits);
        assert_eq!(pb1.binref().off_heap_next(), 0);
    }
    for bin in [first_bin, second_bin] {
        assert_eq!(
            unsafe { (*bin.as_raw()).refcount.load(Ordering::Relaxed) },
            1,
            "the binary chain releases its exact edge"
        );
    }
}
