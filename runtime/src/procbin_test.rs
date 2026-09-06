use super::*;
use crate::any_value::object_size;
use crate::heap::{Heap, SIZE_TABLE, SchemaRegistry};
use std::cell::RefCell;
use std::rc::Rc;
use std::slice::from_raw_parts;
use std::sync::{Arc, Barrier, atomic};
use std::thread;

fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

#[test]
fn independent_allocators_do_not_share_lifetime_observations() {
    let (own, own_drops) = observed_bin();
    let barrier = Barrier::new(2);
    let (observed, unrelated_drops) = thread::scope(|scope| {
        let worker = scope.spawn(|| {
            let (unrelated, drops) = observed_bin();
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
    let (unrelated_drops, before) = unrelated_drops;
    assert_eq!(before, 0, "the independent object remains live after the first release");
    assert_eq!(unrelated_drops.load(Ordering::Relaxed), 1);
    assert_eq!(Arc::strong_count(&own_drops), 1);
    assert_eq!(Arc::strong_count(&unrelated_drops), 1);
}

fn observed_bin() -> (SharedBinHandle, Arc<atomic::AtomicUsize>) {
    unsafe extern "C" fn destroy(p: *mut SharedBin) {
        let bytes = unsafe { from_raw_parts((*p).bytes_ptr, size_of::<usize>()) };
        let observer = usize::from_ne_bytes(bytes.try_into().unwrap()) as *const atomic::AtomicUsize;
        let drops = unsafe { Arc::from_raw(observer) };
        unsafe { shared_bin_destructor_heap(p) };
        drops.fetch_add(1, Ordering::Relaxed);
    }
    let drops = Arc::new(atomic::AtomicUsize::new(0));
    let observer = Arc::into_raw(Arc::clone(&drops)) as usize;
    let handle = SharedBinHandle::from_bytes(&observer.to_ne_bytes(), usize::BITS.into());
    // Install before publication or retain. The payload owns one observer edge;
    // the real heap destructor still reclaims the byte buffer and header.
    unsafe { (*handle.as_raw()).destructor = destroy };
    (handle, drops)
}

#[test]
fn alloc_retain_release_free_pattern() {
    let (handle, drops) = observed_bin();
    let p = handle.into_raw();
    unsafe {
        shared_bin_retain(p);
        shared_bin_retain(p);
        assert_eq!((*p).refcount.load(Ordering::Relaxed), 3);
        shared_bin_release(p);
        shared_bin_release(p);
        assert_eq!((*p).refcount.load(Ordering::Relaxed), 1);
        assert_eq!(drops.load(Ordering::Relaxed), 0);
        shared_bin_release(p);
    }
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

#[test]
fn alloc_release_immediately_frees() {
    let (handle, drops) = observed_bin();
    unsafe { shared_bin_release(handle.into_raw()) };
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

#[test]
fn bytes_preserved_across_retain_release() {
    let p = shared_bin_alloc(&[0xde, 0xad, 0xbe, 0xef], 32);
    unsafe {
        shared_bin_retain(p);
        let len = (*p).bytes_len;
        let payload = from_raw_parts((*p).bytes_ptr, len);
        assert_eq!(payload, &[0xde, 0xad, 0xbe, 0xef][..]);
        assert_eq!((*p).bit_len, 32);
        shared_bin_release(p);
        let payload = from_raw_parts((*p).bytes_ptr, len);
        assert_eq!(payload, &[0xde, 0xad, 0xbe, 0xef][..]);
        shared_bin_release(p);
    }
}

#[test]
fn concurrent_retain_release_frees_on_the_last_workers_release() {
    let (handle, drops) = observed_bin();
    let barrier = Barrier::new(3);
    thread::scope(|scope| {
        let mut workers = Vec::new();
        for _ in 0..2 {
            let address = handle.clone().into_raw() as usize;
            let barrier = &barrier;
            workers.push(scope.spawn(move || {
                let owner = unsafe { SharedBinHandle::from_raw_already_retained(address as *mut SharedBin) };
                barrier.wait();
                for _ in 0..100 {
                    drop(owner.clone());
                }
                drop(owner);
            }));
        }
        drop(handle);
        let before = drops.load(Ordering::Relaxed);
        barrier.wait();
        for worker in workers {
            worker.join().unwrap();
        }
        assert_eq!(before, 0);
    });
    assert_eq!(drops.load(Ordering::Relaxed), 1);
    assert_eq!(
        Arc::strong_count(&drops),
        1,
        "the final worker consumes the observer edge"
    );
}

/// fz-wu9 — every heap-allocated SharedBin's buffer has a trailing
/// zero byte at offset `bytes_len` (not counted toward bytes_len /
/// bit_len). Underwrites the cstring extern marshal contract.
#[test]
fn shared_bin_alloc_has_trailing_nul() {
    // Non-empty payload.
    let p = shared_bin_alloc(b"hello", 40);
    unsafe {
        assert_eq!((*p).bytes_len, 5);
        assert_eq!(*(*p).bytes_ptr.add(5), 0, "trailing NUL after 'hello'");
        shared_bin_release(p);
    }
    // Empty payload — still gets a trailing zero at offset 0.
    let p = shared_bin_alloc(b"", 0);
    unsafe {
        assert_eq!((*p).bytes_len, 0);
        assert_eq!(*(*p).bytes_ptr, 0, "trailing NUL on empty payload");
        shared_bin_release(p);
    }
    // Payload containing internal zeros (rare but legal).
    let p = shared_bin_alloc(&[1u8, 0, 2, 0, 3], 40);
    unsafe {
        assert_eq!((*p).bytes_len, 5);
        assert_eq!(*(*p).bytes_ptr.add(5), 0, "trailing NUL after embedded-zero payload");
        shared_bin_release(p);
    }
}

/// Heap-allocated bin's destructor field equals `shared_bin_destructor_heap`.
#[test]
fn alloc_installs_heap_destructor() {
    let p = shared_bin_alloc(&[0u8; 4], 32);
    unsafe {
        let d = (*p).destructor as *const () as usize;
        let want = shared_bin_destructor_heap as *const () as usize;
        assert_eq!(d, want);
        shared_bin_release(p);
    }
}

/// SharedBinHandle Drop releases.
#[test]
fn handle_drop_releases() {
    let (handle, drops) = observed_bin();
    assert_eq!(Arc::strong_count(&drops), 2, "the allocation owns one observer edge");
    assert_eq!(drops.load(Ordering::Relaxed), 0);
    drop(handle);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
    assert_eq!(
        Arc::strong_count(&drops),
        1,
        "final free consumes exactly that observer edge"
    );
}

/// SharedBinHandle Clone retains; the destructor fires exactly when
/// the second Drop runs.
#[test]
fn handle_clone_retains_then_balanced_drops_free() {
    let (h, drops) = observed_bin();
    let p = h.as_raw();
    let h2 = h.clone();
    unsafe {
        assert_eq!((*p).refcount.load(Ordering::Relaxed), 2);
    }
    drop(h);
    unsafe {
        assert_eq!((*p).refcount.load(Ordering::Relaxed), 1);
    }
    drop(h2);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

/// alloc_procbin pushes onto MSO chain; Heap::drop releases SharedBin.
#[test]
fn alloc_procbin_pushes_into_mso_chain() {
    let (handle, drops) = observed_bin();
    {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let pb = alloc_procbin(&mut h, handle);
        let tagged = heap_object_word(pb.as_raw() as *const u8, ValueKind::PROCBIN);
        assert_eq!(tagged & TAG_MASK, TAG_PROCBIN);
        assert_eq!(object_size(tagged), 16);
        assert_eq!(h.mso_head, tagged);
        assert_eq!(pb.mso_next(), 0);
        assert_eq!(drops.load(Ordering::Relaxed), 0);
    }
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

/// Three ProcBins on one heap: intrusive chain links latest → earlier.
#[test]
fn mso_chain_threads_through_procbins_and_frees_every_entry() {
    let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
    let (first, first_drops) = observed_bin();
    let (second, second_drops) = observed_bin();
    let (third, third_drops) = observed_bin();
    let pb1 = alloc_procbin(&mut h, first);
    let pb2 = alloc_procbin(&mut h, second);
    let pb3 = alloc_procbin(&mut h, third);
    let pb1_bits = heap_object_word(pb1.as_raw() as *const u8, ValueKind::PROCBIN);
    let pb2_bits = heap_object_word(pb2.as_raw() as *const u8, ValueKind::PROCBIN);
    let pb3_bits = heap_object_word(pb3.as_raw() as *const u8, ValueKind::PROCBIN);
    assert_eq!(h.mso_head, pb3_bits);
    assert_eq!(pb3.mso_next(), pb2_bits);
    assert_eq!(pb2.mso_next(), pb1_bits);
    assert_eq!(pb1.mso_next(), 0);
    for drops in [&first_drops, &second_drops, &third_drops] {
        assert_eq!(drops.load(Ordering::Relaxed), 0);
    }
    drop(h);
    for drops in [first_drops, second_drops, third_drops] {
        assert_eq!(drops.load(Ordering::Relaxed), 1);
    }
}

#[test]
fn unrooted_shared_bin_is_freed_once_by_gc_not_again_by_heap_drop() {
    let (handle, drops) = observed_bin();
    let mut heap = Heap::new(SIZE_TABLE[0], empty_registry());
    alloc_procbin(&mut heap, handle);
    heap.gc(&mut std::ptr::null_mut());
    assert_eq!(drops.load(Ordering::Relaxed), 1);
    assert_eq!(heap.mso_head, 0);
    drop(heap);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

#[test]
fn copied_shared_bin_is_freed_only_when_the_last_heap_releases_it() {
    let (handle, drops) = observed_bin();
    let mut source = Heap::new(SIZE_TABLE[0], empty_registry());
    let mut destination = Heap::new(SIZE_TABLE[0], empty_registry());
    let pb = alloc_procbin(&mut source, handle);
    crate::heap::deep_copy_slot(
        AnyValue::heap_ptr(pb.as_raw(), ValueKind::PROCBIN),
        &source,
        &mut destination,
        &mut std::collections::HashMap::new(),
    );
    drop(source);
    assert_eq!(
        drops.load(Ordering::Relaxed),
        0,
        "the copied heap still owns the binary"
    );
    drop(destination);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
    assert_eq!(Arc::strong_count(&drops), 1);
}
