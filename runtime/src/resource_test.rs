use super::*;
use crate::heap::{Heap, SIZE_TABLE, SchemaRegistry};
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{Arc, Barrier, atomic};
use std::thread;

fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

unsafe extern "C" fn observe_destruction(payload: u64) {
    let drops = unsafe { Arc::from_raw(payload as *const atomic::AtomicUsize) };
    drops.fetch_add(1, Ordering::Relaxed);
}

fn observed_resource() -> (ResourceHandle, Arc<atomic::AtomicUsize>) {
    let drops = Arc::new(atomic::AtomicUsize::new(0));
    let payload = Arc::into_raw(Arc::clone(&drops)) as u64;
    (ResourceHandle::new(payload, observe_destruction), drops)
}

#[test]
fn independent_allocators_do_not_share_lifetime_observations() {
    let (own, own_drops) = observed_resource();
    let barrier = Barrier::new(2);
    let (observed, (unrelated_drops, before)) = thread::scope(|scope| {
        let worker = scope.spawn(|| {
            let (unrelated, drops) = observed_resource();
            barrier.wait();
            barrier.wait();
            let before = drops.load(Ordering::Relaxed);
            drop(unrelated);
            (drops, before)
        });
        barrier.wait();
        drop(own);
        let observed = own_drops.load(Ordering::Relaxed);
        barrier.wait();
        (observed, worker.join().unwrap())
    });
    assert_eq!(
        observed, 1,
        "another allocator cannot change this owner's lifetime observation"
    );
    assert_eq!(before, 0, "the independent object remains live after the first release");
    assert_eq!(unrelated_drops.load(Ordering::Relaxed), 1);
    assert_eq!(Arc::strong_count(&own_drops), 1);
    assert_eq!(Arc::strong_count(&unrelated_drops), 1);
}

#[test]
fn resource_is_24_bytes() {
    assert_eq!(size_of::<Resource>(), 24);
}

#[test]
fn alloc_retain_release_pattern() {
    let (handle, drops) = observed_resource();
    let p = handle.into_raw();
    unsafe {
        assert_eq!((*p).payload, Arc::as_ptr(&drops) as u64);
        fz_resource_retain(p);
        fz_resource_retain(p);
        assert_eq!((*p).refcount.load(Ordering::Relaxed), 3);
        fz_resource_release(p);
        fz_resource_release(p);
        assert_eq!((*p).refcount.load(Ordering::Relaxed), 1);
        assert_eq!(drops.load(Ordering::Relaxed), 0);
        fz_resource_release(p);
    }
    assert_eq!(drops.load(Ordering::Relaxed), 1);
    assert_eq!(
        Arc::strong_count(&drops),
        1,
        "the exact payload-owned observer edge is consumed"
    );
}

#[test]
fn alloc_release_immediately_fires_dtor() {
    let (handle, drops) = observed_resource();
    unsafe { fz_resource_release(handle.into_raw()) };
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

#[test]
fn handle_drop_releases() {
    let (handle, drops) = observed_resource();
    assert_eq!(drops.load(Ordering::Relaxed), 0);
    drop(handle);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

#[test]
fn handle_clone_balanced_drops_fire_once() {
    let (handle, drops) = observed_resource();
    let second = handle.clone();
    assert_eq!(unsafe { (*handle.as_raw()).refcount.load(Ordering::Relaxed) }, 2);
    drop(handle);
    assert_eq!(drops.load(Ordering::Relaxed), 0);
    drop(second);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

#[test]
fn last_worker_release_fires_the_resource_destructor_once() {
    let (handle, drops) = observed_resource();
    let address = handle.clone().into_raw() as usize;
    drop(handle);
    assert_eq!(drops.load(Ordering::Relaxed), 0);
    thread::spawn(move || {
        drop(unsafe { ResourceHandle::from_raw_already_retained(address as *mut Resource) });
    })
    .join()
    .unwrap();
    assert_eq!(drops.load(Ordering::Relaxed), 1);
    assert_eq!(Arc::strong_count(&drops), 1);
}

#[test]
fn deferred_release_returns_the_exact_payload_without_running_the_inline_destructor() {
    let (handle, drops) = observed_resource();
    let second = handle.clone().into_raw();
    let expected = Arc::as_ptr(&drops) as u64;
    assert_eq!(unsafe { fz_resource_release_deferred(handle.into_raw()) }, None);
    assert_eq!(unsafe { (*second).refcount.load(Ordering::Relaxed) }, 1);
    assert_eq!(drops.load(Ordering::Relaxed), 0);
    let payload = unsafe { fz_resource_release_deferred(second) };
    assert_eq!(payload, Some(expected));
    assert_eq!(
        drops.load(Ordering::Relaxed),
        0,
        "deferred release does not dispatch the inline destructor"
    );
    unsafe { observe_destruction(payload.unwrap()) };
    assert_eq!(drops.load(Ordering::Relaxed), 1);
    assert_eq!(Arc::strong_count(&drops), 1);
}

#[test]
fn noop_dtor_is_safe() {
    let p = resource_alloc(123, fz_resource_destructor_noop);
    unsafe {
        assert_eq!((*p).payload, 123);
        fz_resource_release(p);
    }
}

#[test]
fn alloc_resource_pushes_into_mso_chain() {
    let (handle, drops) = observed_resource();
    let mut heap = Heap::new(SIZE_TABLE[0], empty_registry());
    let rs = alloc_resource(&mut heap, handle, AnyValue::nil_atom());
    let tagged = heap_object_word(rs.as_raw() as *const u8, ValueKind::RESOURCE);
    assert_eq!(tagged & TAG_MASK, TAG_RESOURCE);
    assert_eq!(object_size(tagged), RESOURCE_STUB_SIZE);
    assert_eq!(heap.mso_head, tagged);
    assert_eq!(rs.mso_next(), 0);
    assert_eq!(rs.payload(), Arc::as_ptr(&drops) as u64);
    assert_eq!(rs.refcount(), 1);
    assert_eq!(drops.load(Ordering::Relaxed), 0);
    drop(heap);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

#[test]
fn unrooted_resource_dies_in_gc_and_sweep_fires_dtor() {
    let (handle, drops) = observed_resource();
    let mut heap = Heap::new(SIZE_TABLE[0], empty_registry());
    alloc_resource(&mut heap, handle, AnyValue::nil_atom());
    heap.gc(&mut null_mut());
    assert_eq!(heap.mso_head, 0, "dead Resource swept from MSO");
    assert_eq!(drops.load(Ordering::Relaxed), 1);
    drop(heap);
    assert_eq!(
        drops.load(Ordering::Relaxed),
        1,
        "heap drop cannot repeat the swept destructor"
    );
}

#[test]
fn resource_forwarding_marker_through_gc() {
    let (handle, drops) = observed_resource();
    let mut heap = Heap::new(SIZE_TABLE[0], empty_registry());
    let rs = alloc_resource(&mut heap, handle, AnyValue::nil_atom());
    let from = rs.as_raw();
    let shared = rs.shared_raw();
    let mut root = heap_object_word(from as *const u8, ValueKind::RESOURCE) as *mut u8;
    heap.gc(&mut root);
    let to = resource_addr_from_tagged(root as u64).unwrap();
    assert_ne!(to, from);
    assert_eq!(unsafe { ResourceStub::from_raw(to).shared_raw() }, shared);
    assert_eq!(heap.mso_head, heap_object_word(to as *const u8, ValueKind::RESOURCE));
    assert_eq!(drops.load(Ordering::Relaxed), 0);
    drop(heap);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

#[test]
fn mixed_mso_chain_with_procbin_and_resource() {
    use crate::procbin::{SharedBinHandle, alloc_procbin};
    let (first, first_drops) = observed_resource();
    let (second, second_drops) = observed_resource();
    let first_bin = SharedBinHandle::from_bytes(&[1, 2, 3], 24);
    let second_bin = SharedBinHandle::from_bytes(&[4, 5], 16);
    {
        let mut heap = Heap::new(SIZE_TABLE[0], empty_registry());
        let pb1 = alloc_procbin(&mut heap, first_bin.clone());
        let rs1 = alloc_resource(&mut heap, first, AnyValue::nil_atom());
        let pb2 = alloc_procbin(&mut heap, second_bin.clone());
        let rs2 = alloc_resource(&mut heap, second, AnyValue::nil_atom());
        let rs2_bits = heap_object_word(rs2.as_raw(), ValueKind::RESOURCE);
        let pb2_bits = heap_object_word(pb2.as_raw(), ValueKind::PROCBIN);
        let pb1_bits = heap_object_word(pb1.as_raw(), ValueKind::PROCBIN);
        let rs1_bits = heap_object_word(rs1.as_raw(), ValueKind::RESOURCE);
        assert_eq!(heap.mso_head, rs2_bits);
        assert_eq!(rs2.mso_next(), pb2_bits);
        assert_eq!(pb2.mso_next(), rs1_bits);
        assert_eq!(rs1.mso_next(), pb1_bits);
        assert_eq!(pb2.mso_next() & TAG_MASK, TAG_RESOURCE);
        assert_eq!(pb1.mso_next(), 0);
    }
    assert_eq!(first_drops.load(Ordering::Relaxed), 1);
    assert_eq!(second_drops.load(Ordering::Relaxed), 1);
    for bin in [first_bin, second_bin] {
        assert_eq!(
            unsafe { (*bin.as_raw()).refcount.load(Ordering::Relaxed) },
            1,
            "the mixed chain releases its exact binary edge"
        );
    }
}
