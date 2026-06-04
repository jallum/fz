use super::*;
use crate::any_value::object_size;
use crate::heap::{Heap, SIZE_TABLE, SchemaRegistry};
use std::cell::RefCell;
use std::hint::spin_loop;
use std::rc::Rc;
use std::slice::from_raw_parts;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::thread;

fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

/// RAII guard: snapshots `live_count()` on construction; Drop asserts
/// the count returned to baseline. Use in scopes where every bin
/// allocated must also be freed before the guard goes out of scope.
pub(crate) struct LiveCountGuard {
    baseline: usize,
}
impl LiveCountGuard {
    pub(crate) fn snap() -> Self {
        Self { baseline: live_count() }
    }
    pub(crate) fn baseline(&self) -> usize {
        self.baseline
    }
}
impl Drop for LiveCountGuard {
    fn drop(&mut self) {
        assert_eq!(
            live_count(),
            self.baseline,
            "LiveCountGuard: live_count did not return to baseline"
        );
    }
}

#[test]
#[serial_test::serial]
fn alloc_retain_release_free_pattern() {
    let g = LiveCountGuard::snap();
    let p = shared_bin_alloc(&[1, 2, 3, 4], 32);
    assert_eq!(live_count(), g.baseline() + 1);
    unsafe {
        shared_bin_retain(p);
        shared_bin_retain(p);
        assert_eq!((*p).refcount.load(Ordering::Relaxed), 3);
        shared_bin_release(p);
        shared_bin_release(p);
        assert_eq!((*p).refcount.load(Ordering::Relaxed), 1);
        shared_bin_release(p);
    }
}

#[test]
#[serial_test::serial]
fn alloc_release_immediately_frees() {
    let _g = LiveCountGuard::snap();
    let p = shared_bin_alloc(b"hello", 40);
    unsafe { shared_bin_release(p) };
}

#[test]
#[serial_test::serial]
fn bytes_preserved_across_retain_release() {
    let _g = LiveCountGuard::snap();
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
#[serial_test::serial]
fn concurrent_retain_release_is_consistent() {
    let _g = LiveCountGuard::snap();
    let p = shared_bin_alloc(&[7; 64], 512);
    let p_addr = p as usize;
    let start = Arc::new(AtomicBool::new(false));
    let mut handles = Vec::new();
    for _ in 0..2 {
        let start = start.clone();
        handles.push(thread::spawn(move || {
            while !start.load(Ordering::Acquire) {
                spin_loop();
            }
            let p = p_addr as *mut SharedBin;
            for _ in 0..100 {
                unsafe {
                    shared_bin_retain(p);
                    shared_bin_release(p);
                }
            }
        }));
    }
    start.store(true, Ordering::Release);
    for h in handles {
        h.join().unwrap();
    }
    unsafe {
        assert_eq!((*p).refcount.load(Ordering::Relaxed), 1);
        shared_bin_release(p);
    }
}

/// fz-wu9 — every heap-allocated SharedBin's buffer has a trailing
/// zero byte at offset `bytes_len` (not counted toward bytes_len /
/// bit_len). Underwrites the cstring extern marshal contract.
#[test]
#[serial_test::serial]
fn shared_bin_alloc_has_trailing_nul() {
    let _g = LiveCountGuard::snap();
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
#[serial_test::serial]
fn alloc_installs_heap_destructor() {
    let _g = LiveCountGuard::snap();
    let p = shared_bin_alloc(&[0u8; 4], 32);
    unsafe {
        let d = (*p).destructor as *const () as usize;
        let want = shared_bin_destructor_heap as *const () as usize;
        assert_eq!(d, want);
        shared_bin_release(p);
    }
}

/// Construct a SharedBin manually with a test destructor that flips
/// an AtomicBool; retain/release exactly to zero fires it once.
#[test]
#[serial_test::serial]
fn custom_destructor_fires_exactly_once() {
    static FIRED: atomic::AtomicUsize = atomic::AtomicUsize::new(0);
    unsafe extern "C" fn test_dtor(_p: *mut SharedBin) {
        FIRED.fetch_add(1, atomic::Ordering::Relaxed);
    }
    FIRED.store(0, atomic::Ordering::Relaxed);
    // Allocate bytes + bin without entering shared_bin_alloc (so the
    // global LIVE_COUNT isn't touched and the test destructor isn't
    // shared_bin_destructor_heap). We leak both — test_dtor is a no-op.
    let bytes: Box<[u8]> = vec![0u8; 4].into_boxed_slice();
    let bytes_len = bytes.len();
    let bytes_ptr = Box::leak(bytes).as_ptr();
    let bin = Box::new(SharedBin {
        refcount: AtomicUsize::new(1),
        bit_len: 32,
        bytes_ptr,
        bytes_len,
        destructor: test_dtor,
    });
    let p = Box::into_raw(bin);
    unsafe {
        shared_bin_retain(p);
        shared_bin_release(p);
        assert_eq!(FIRED.load(atomic::Ordering::Relaxed), 0, "still has 1 ref");
        shared_bin_release(p);
    }
    assert_eq!(FIRED.load(atomic::Ordering::Relaxed), 1, "fired exactly once");
    // Reclaim manually so we don't actually leak. test_dtor was a noop.
    unsafe {
        let _ = Box::from_raw(p);
        let _ = Box::from_raw(slice_from_raw_parts_mut(bytes_ptr as *mut u8, bytes_len));
    }
}

/// SharedBinHandle Drop releases.
#[test]
#[serial_test::serial]
fn handle_drop_releases() {
    let g = LiveCountGuard::snap();
    {
        let _h = SharedBinHandle::from_bytes(&[1, 2, 3], 24);
        assert_eq!(live_count(), g.baseline() + 1);
    }
}

/// SharedBinHandle Clone retains; the destructor fires exactly when
/// the second Drop runs.
#[test]
#[serial_test::serial]
fn handle_clone_retains_then_balanced_drops_free() {
    let g = LiveCountGuard::snap();
    let h = SharedBinHandle::from_bytes(&[0xab, 0xcd], 16);
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
    assert_eq!(live_count(), g.baseline());
}

/// alloc_procbin pushes onto MSO chain; Heap::drop releases SharedBin.
#[test]
#[serial_test::serial]
fn alloc_procbin_pushes_into_mso_chain() {
    let g = LiveCountGuard::snap();
    {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let handle = SharedBinHandle::from_bytes(&[1, 2, 3, 4], 32);
        let pb = alloc_procbin(&mut h, handle);
        let tagged = heap_object_word(pb.as_raw() as *const u8, ValueKind::PROCBIN);
        assert_eq!(tagged & TAG_MASK, TAG_PROCBIN);
        assert_eq!(object_size(tagged), 16);
        assert_eq!(h.mso_head, tagged);
        assert_eq!(pb.mso_next(), 0);
        assert_eq!(live_count(), g.baseline() + 1);
    }
}

/// Three ProcBins on one heap: intrusive chain links latest → earlier.
#[test]
#[serial_test::serial]
fn mso_chain_threads_through_procbins() {
    let _g = LiveCountGuard::snap();
    let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
    let pb1 = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1], 8));
    let pb2 = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[2], 8));
    let pb3 = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[3], 8));
    let pb1_bits = heap_object_word(pb1.as_raw() as *const u8, ValueKind::PROCBIN);
    let pb2_bits = heap_object_word(pb2.as_raw() as *const u8, ValueKind::PROCBIN);
    let pb3_bits = heap_object_word(pb3.as_raw() as *const u8, ValueKind::PROCBIN);
    assert_eq!(h.mso_head, pb3_bits);
    assert_eq!(pb3.mso_next(), pb2_bits);
    assert_eq!(pb2.mso_next(), pb1_bits);
    assert_eq!(pb1.mso_next(), 0);
}

/// Heap::drop releases every chain entry.
#[test]
#[serial_test::serial]
fn heap_drop_releases_all_chain_entries() {
    let g = LiveCountGuard::snap();
    {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1, 2], 16));
        let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[3, 4, 5], 24));
        assert_eq!(live_count(), g.baseline() + 2);
    }
}
