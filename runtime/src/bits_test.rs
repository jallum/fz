use super::*;
use crate::any_value::AnyValue;
use crate::heap::{Heap, SHARED_BIN_THRESHOLD_BYTES, SIZE_TABLE, SchemaRegistry};
use std::cell::RefCell;
use std::rc::Rc;
use std::slice::from_raw_parts;
use std::sync::{Arc, Barrier, atomic};
use std::thread;

/// A view of `bit_len` bits that starts `byte_offset` bytes into a buffer that
/// enters the heap with it, as a buffer does when a message copy brings it.
fn window_of_new_buffer(
    heap: &mut Heap,
    handle: SharedBinHandle,
    byte_offset: usize,
    bit_len: u64,
    site: StubSite,
) -> BinView {
    let first = unsafe { handle.bytes_ptr().add(byte_offset) };
    let binref = alloc_binref(heap, handle, site);
    alloc_view(heap, binref, first, bit_len, site)
}

pub(crate) fn fresh_registry() -> Rc<RefCell<SchemaRegistry>> {
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

pub(crate) fn observed_bin() -> (SharedBinHandle, Arc<atomic::AtomicUsize>) {
    unsafe extern "C" fn destroy(p: *mut SharedBin) {
        let bytes = unsafe { from_raw_parts((*p).bytes_ptr, size_of::<usize>()) };
        let observer = usize::from_ne_bytes(bytes.try_into().unwrap()) as *const atomic::AtomicUsize;
        let drops = unsafe { Arc::from_raw(observer) };
        unsafe { shared_bin_destructor_heap(p) };
        drops.fetch_add(1, Ordering::Relaxed);
    }
    let drops = Arc::new(atomic::AtomicUsize::new(0));
    let observer = Arc::into_raw(Arc::clone(&drops)) as usize;
    let handle = SharedBinHandle::from_bytes(&observer.to_ne_bytes());
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
    let p = shared_bin_alloc(&[0xde, 0xad, 0xbe, 0xef]);
    unsafe {
        shared_bin_retain(p);
        let len = (*p).bytes_len;
        let payload = from_raw_parts((*p).bytes_ptr, len);
        assert_eq!(payload, &[0xde, 0xad, 0xbe, 0xef][..]);
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

/// Every heap-allocated SharedBin's buffer has a trailing
/// zero byte at offset `bytes_len` (not counted toward bytes_len /
/// bit_len). Underwrites the c_string extern marshal contract.
#[test]
fn shared_bin_alloc_has_trailing_nul() {
    // Non-empty payload.
    let p = shared_bin_alloc(b"hello");
    unsafe {
        assert_eq!((*p).bytes_len, 5);
        assert_eq!(*(*p).bytes_ptr.add(5), 0, "trailing NUL after 'hello'");
        shared_bin_release(p);
    }
    // Empty payload — still gets a trailing zero at offset 0.
    let p = shared_bin_alloc(b"");
    unsafe {
        assert_eq!((*p).bytes_len, 0);
        assert_eq!(*(*p).bytes_ptr, 0, "trailing NUL on empty payload");
        shared_bin_release(p);
    }
    // Payload containing internal zeros (rare but legal).
    let p = shared_bin_alloc(&[1u8, 0, 2, 0, 3]);
    unsafe {
        assert_eq!((*p).bytes_len, 5);
        assert_eq!(*(*p).bytes_ptr.add(5), 0, "trailing NUL after embedded-zero payload");
        shared_bin_release(p);
    }
}

/// A heap-backed binary is one allocation: its bytes begin where its header
/// ends.
#[test]
fn a_heap_binary_keeps_its_bytes_right_after_its_header() {
    let p = shared_bin_alloc_with_room(b"hello", 100);
    unsafe {
        assert_eq!((*p).bytes_ptr as usize, p as usize + SHARED_BIN_BYTES);
        shared_bin_release(p);
    }
}

/// An append moves the trailing NUL to the new end, because the room beyond the
/// written bytes is not zeroed: the byte after each end reads 0 and the byte
/// after that is not assumed to.
#[test]
fn an_append_writes_the_trailing_nul_at_the_new_end() {
    let p = shared_bin_alloc_with_room(b"ab", 8);
    unsafe {
        shared_bin_append(p, b"cde");
        let bytes = from_raw_parts((*p).bytes_ptr, (*p).bytes_len + 1);
        assert_eq!(bytes, b"abcde\0");
        shared_bin_append(p, b"f");
        assert_eq!(*(*p).bytes_ptr.add(6), 0);
        shared_bin_release(p);
    }
}

/// In debug builds the room a binary has not written holds `UNWRITTEN_BYTE`, so
/// a reader of room beyond the NUL fails loudly.
#[cfg(debug_assertions)]
#[test]
fn a_binarys_unwritten_room_is_poisoned_in_debug_builds() {
    let p = shared_bin_alloc_with_room(b"ab", 8);
    unsafe {
        assert_eq!(*(*p).bytes_ptr.add(3), crate::heap::UNWRITTEN_BYTE);
        shared_bin_release(p);
    }
}

/// Heap-allocated bin's destructor field equals `shared_bin_destructor_heap`.
#[test]
fn alloc_installs_heap_destructor() {
    let p = shared_bin_alloc(&[0u8; 4]);
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

// ===== views ==========================================================

/// A tail of a shared binary is another view of the SAME bytes: same
/// SharedBin, pointer advanced by the offset, length shortened. Nothing is
/// copied, which is the whole point — a scanner takes one of these per byte.
#[test]
fn a_view_stub_names_the_parents_bytes_rather_than_copying_them() {
    let bytes: Vec<u8> = (0..200u8).collect();
    let handle = SharedBinHandle::from_bytes(&bytes);
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let whole = alloc_buffer_view(
        &mut h,
        handle.clone(),
        handle.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let tail = window_of_new_buffer(&mut h, handle, 70, (200 - 70) * 8, StubSite::FilledBuffer);

    assert_eq!(
        whole.shared_raw(),
        tail.shared_raw(),
        "a suffix shares the parent's buffer instead of allocating its own"
    );
    assert_eq!(tail.byte_offset(), 70);
    assert_eq!(tail.bit_len(), (200 - 70) * 8);
    assert_eq!(tail.bytes_len(), 200 - 70);
    assert_eq!(unsafe { *tail.bytes_ptr() }, 70);
    assert_eq!(unsafe { *tail.bytes_ptr().add(129) }, 199);
}

/// A suffix ends where the parent's buffer ends, so it inherits the
/// invisible trailing NUL that every SharedBin buffer carries. That is what lets
/// `fz_binary_as_cstring` hand a tail straight to C without flattening it.
#[test]
fn a_suffix_inherits_the_parents_trailing_nul() {
    let bytes: Vec<u8> = vec![b'x'; 200];
    let handle = SharedBinHandle::from_bytes(&bytes);
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let tail = window_of_new_buffer(&mut h, handle, 199, 8, StubSite::FilledBuffer);
    assert_eq!(tail.bytes_len(), 1);
    assert_eq!(unsafe { *tail.bytes_ptr().add(tail.bytes_len()) }, 0);
}

/// The parent buffer outlives the whole-binary stub as long as any suffix
/// still views it: each stub owns its own reference edge.
#[test]
fn a_suffix_keeps_the_shared_bytes_alive_after_the_whole_binary_is_gone() {
    let (handle, drops) = observed_bin();
    let mut whole_heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut tail_heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    alloc_buffer_view(
        &mut whole_heap,
        handle.clone(),
        handle.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let tail = window_of_new_buffer(
        &mut tail_heap,
        handle.clone(),
        4,
        handle.bytes_len() as u64 * 8 - 4 * 8,
        StubSite::FilledBuffer,
    );
    drop(handle);
    drop(whole_heap);
    assert_eq!(
        drops.load(Ordering::Relaxed),
        0,
        "the surviving suffix still owns the bytes"
    );
    assert_eq!(tail.byte_offset(), 4);
    drop(tail_heap);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

/// Cheney moves the stub; the offset moves with it, so the survivor still
/// names the same tail.
#[test]
fn gc_preserves_a_suffixs_offset() {
    let bytes: Vec<u8> = (0..200u8).collect();
    let handle = SharedBinHandle::from_bytes(&bytes);
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let tail = window_of_new_buffer(&mut h, handle, 70, (200 - 70) * 8, StubSite::FilledBuffer);
    let mut roots =
        [crate::any_value::AnyValueRef::from_heap_object(ValueKind::BINVIEW, tail.as_raw()).expect("binview ref")];
    h.collect_stats(&mut roots);
    let moved = unsafe { BinView::from_raw(roots[0].binview_addr().expect("survivor")) };
    assert_eq!(moved.byte_offset(), 70);
    assert_eq!(moved.bit_len(), (200 - 70) * 8);
    assert_eq!(unsafe { *moved.bytes_ptr() }, 70);
}

/// A BinRef holds its SharedBin's address in word 0, and that is the
/// word the collector overwrites with a forwarding marker, which is a set low
/// nibble. A live BinRef whose SharedBin address had a set low nibble would read
/// as forwarded, so the sweep would treat the SharedBin itself as a to-space
/// stub and write into it. 16-alignment is what makes a real pointer and a
/// marker distinguishable.
#[test]
fn a_shared_bin_address_is_never_mistakable_for_a_forwarding_marker() {
    assert_eq!(align_of::<SharedBin>(), 16);
    // Many at once: at 8-alignment about half of these would end in 8.
    let bins: Vec<SharedBinHandle> = (0..64u8).map(|i| SharedBinHandle::from_bytes(&[i; 8])).collect();
    for bin in &bins {
        let addr = bin.as_raw() as u64;
        assert_eq!(addr % 16, 0, "SharedBin at {addr:#x} is not 16-aligned");
        assert_eq!(addr & 0xF, 0, "SharedBin at {addr:#x} has a set low nibble");
    }
}

// ===== loom verification of retain/release ordering =========================
//
// Enabled only under `RUSTFLAGS="--cfg loom"`. The two-thread model
// constructs a SharedBin with an observed destructor, spawns two children that
// each retain+release, then the "main" thread performs the final
// release. Across every legal interleaving loom can produce, the test
// destructor must fire exactly once.
//
// Run: `RUSTFLAGS="--cfg loom" cargo test --release -p fz-runtime loom_`.
#[cfg(all(test, loom))]
mod loom_tests {
    use super::super::*;
    use loom::sync::Arc;
    use loom::sync::atomic::{AtomicBool, Ordering as LoomOrdering};

    // Destructor for the loom test sets a flag on a loom-instrumented
    // `AtomicBool` handed out via the thread-local `LOOM_FLAG` slot. The
    // model asserts the destructor fires exactly once per iteration.
    loom::thread_local! {
        static LOOM_FLAG: std::cell::RefCell<Option<Arc<AtomicBool>>> =
            std::cell::RefCell::new(None);
    }

    unsafe extern "C" fn loom_dtor(_p: *mut SharedBin) {
        LOOM_FLAG.with(|c| {
            let flag = c.borrow();
            let f = flag.as_ref().expect("LOOM_FLAG not installed");
            // Use SeqCst so loom treats the destructor invocation as a
            // single, observable event in the model.
            let prev = f.swap(true, LoomOrdering::SeqCst);
            assert!(!prev, "destructor fired more than once");
        });
    }

    fn install_loom_flag(flag: Arc<AtomicBool>) {
        LOOM_FLAG.with(|c| *c.borrow_mut() = Some(flag));
    }

    /// Build a SharedBin manually with `loom_dtor` installed and
    /// `refcount = 1`. Returns the raw pointer. The byte buffer is a
    /// constant we never free — loom_dtor doesn't reclaim it; the bin
    /// itself is also leaked at end of model iteration. Each loom
    /// model run allocates a fresh one, which is acceptable: loom
    /// runs are tens of thousands of iterations, each allocating one
    /// 40-byte bin and one Box that loom_dtor leaves intact.
    fn build_loom_sharedbin() -> *mut SharedBin {
        static PAYLOAD: [u8; 4] = [0, 0, 0, 0];
        let bin = Box::new(SharedBin {
            refcount: AtomicUsize::new(1),
            bytes_ptr: PAYLOAD.as_ptr(),
            bytes_len: PAYLOAD.len(),
            destructor: loom_dtor,
        });
        Box::into_raw(bin)
    }

    #[test]
    fn loom_retain_release_two_threads() {
        loom::model(|| {
            let flag = Arc::new(AtomicBool::new(false));
            install_loom_flag(flag.clone());
            let p = build_loom_sharedbin();
            let p_addr = p as usize;

            let f1 = flag.clone();
            let t1 = loom::thread::spawn(move || {
                install_loom_flag(f1);
                let p = p_addr as *mut SharedBin;
                unsafe {
                    shared_bin_retain(p);
                    shared_bin_release(p);
                }
            });
            let f2 = flag.clone();
            let t2 = loom::thread::spawn(move || {
                install_loom_flag(f2);
                let p = p_addr as *mut SharedBin;
                unsafe {
                    shared_bin_retain(p);
                    shared_bin_release(p);
                }
            });
            t1.join().unwrap();
            t2.join().unwrap();
            // Main thread's final release fires the destructor.
            unsafe { shared_bin_release(p_addr as *mut SharedBin) };
            assert!(flag.load(LoomOrdering::SeqCst), "destructor must fire on last release");
        });
    }
}

/// A window in the middle of a buffer is a view too: the stub's own length, not
/// the distance to the buffer's end, says where it stops.
#[test]
fn a_middle_slice_is_a_view_with_its_own_length() {
    let bytes: Vec<u8> = (0..200u8).collect();
    let handle = SharedBinHandle::from_bytes(&bytes);
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let middle = window_of_new_buffer(&mut h, handle, 70, 100 * 8, StubSite::FilledBuffer);

    assert_eq!(middle.byte_offset(), 70);
    assert_eq!(middle.bit_len(), 100 * 8);
    assert_eq!(middle.bytes_len(), 100);
    assert_eq!(unsafe { from_raw_parts(middle.bytes_ptr(), 100) }, &bytes[70..170]);
    assert!(!middle.ends_at_buffer_end());
}

/// `Heap::alloc_bitstring_slice` shares the bytes of a slice above the
/// threshold and copies one at or below it, wherever in the buffer it sits.
#[test]
fn a_slice_above_the_threshold_is_a_view_and_below_it_a_copy() {
    let bytes: Vec<u8> = (0..200u8).collect();
    let handle = SharedBinHandle::from_bytes(&bytes);
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let whole = alloc_buffer_view(&mut h, handle, 200 * 8, StubSite::FilledBuffer);
    let (big, small) = unsafe {
        (
            h.alloc_bitstring_slice(whole, 10, 100),
            h.alloc_bitstring_slice(whole, 10, SHARED_BIN_THRESHOLD_BYTES as u64),
        )
    };
    assert_eq!(big.kind(), ValueKind::BINVIEW);
    assert_eq!(small.kind(), ValueKind::BITSTRING);
    let word = big.heap_object_word().unwrap();
    assert_eq!(unsafe { bitstring_bit_len(word) }, 100 * 8);
    assert_eq!(
        unsafe { from_raw_parts(bitstring_byte_ptr(word), 100) },
        &bytes[10..110]
    );
}

/// A copy to another heap names the same window, not the buffer's whole tail.
#[test]
fn a_deep_copy_of_a_middle_slice_keeps_its_length() {
    let bytes: Vec<u8> = (0..200u8).collect();
    let handle = SharedBinHandle::from_bytes(&bytes);
    let mut source = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut destination = Heap::new(SIZE_TABLE[0], fresh_registry());
    let middle = window_of_new_buffer(&mut source, handle, 70, 100 * 8, StubSite::FilledBuffer);
    let copied = crate::heap::deep_copy_slot(
        AnyValue::heap_ptr(middle.as_raw(), ValueKind::BINVIEW),
        &source.view(),
        &mut destination,
    );
    let copy = unsafe { BinView::from_raw(copied.heap_addr().unwrap()) };
    assert_eq!((copy.byte_offset(), copy.bytes_len()), (70, 100));
    assert_eq!(unsafe { from_raw_parts(copy.bytes_ptr(), 100) }, &bytes[70..170]);
}

/// Cheney moves the stub; its length moves with it.
#[test]
fn gc_preserves_a_middle_slices_length() {
    let bytes: Vec<u8> = (0..200u8).collect();
    let handle = SharedBinHandle::from_bytes(&bytes);
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let middle = window_of_new_buffer(&mut h, handle, 70, 100 * 8, StubSite::FilledBuffer);
    let mut roots =
        [crate::any_value::AnyValueRef::from_heap_object(ValueKind::BINVIEW, middle.as_raw()).expect("binview ref")];
    h.collect_stats(&mut roots);
    let moved = unsafe { BinView::from_raw(roots[0].binview_addr().expect("survivor")) };
    assert_eq!((moved.byte_offset(), moved.bytes_len()), (70, 100));
    assert_eq!(unsafe { from_raw_parts(moved.bytes_ptr(), 100) }, &bytes[70..170]);
}

// ===== Concatenation appends into spare room =================================

fn concat(heap: &mut Heap, left: AnyValue, right: &[u8]) -> BinView {
    let view = left.heap_addr().map(|addr| unsafe { BinView::from_raw(addr) });
    let left_bytes = unsafe {
        let word = left.heap_object_word().unwrap();
        from_raw_parts(bitstring_byte_ptr(word), bitstring_bit_len(word) as usize / 8)
    };
    let joined = unsafe { heap.alloc_concatenation(left_bytes, view, right) };
    unsafe {
        BinView::from_raw(
            joined
                .heap_addr()
                .expect("a concatenation above the threshold is a BinView"),
        )
    }
}

fn as_value(pb: BinView) -> AnyValue {
    AnyValue::heap_ptr(pb.as_raw(), ValueKind::BINVIEW)
}

fn view_bytes(pb: &BinView) -> &[u8] {
    unsafe { from_raw_parts(pb.bytes_ptr(), pb.bytes_len()) }
}

fn first_view(heap: &mut Heap) -> BinView {
    let head = heap.alloc_bitstring(&[b'a'; 100], 100 * 8);
    concat(heap, head, b"b")
}

/// A concatenation whose left side ends where its buffer's written bytes end
/// writes into the buffer's room: the result is a longer view of the same
/// buffer, and the old view keeps its bytes and length.
#[test]
fn appending_into_spare_room_returns_a_longer_view_of_the_same_buffer() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let first = first_view(&mut heap);
    let first_bytes = view_bytes(&first).to_vec();
    let second = concat(&mut heap, as_value(first), b"cd");
    assert_eq!(second.shared_raw(), first.shared_raw());
    assert_eq!(second.bytes_ptr(), first.bytes_ptr());
    assert_eq!(second.bytes_len(), 103);
    assert_eq!(&view_bytes(&second)[100..], b"bcd");
    assert_eq!(first.bytes_len(), 101);
    assert_eq!(view_bytes(&first), first_bytes.as_slice());
}

/// The old view no longer ends at its buffer's end, so its C string is a
/// terminated copy; the new view ends there and goes to C as it is.
#[test]
fn after_an_append_the_old_views_c_string_is_a_terminated_copy() {
    let mut process = crate::process::Process::new(fresh_registry());
    let first = first_view(&mut process.heap);
    let second = concat(&mut process.heap, as_value(first), b"cd");
    assert!(second.ends_at_buffer_end());
    assert!(!first.ends_at_buffer_end());
    unsafe {
        let old = crate::extern_binary::fz_binary_as_cstring(&mut process, as_value(first).ref_word().raw_word());
        assert_ne!(old, first.bytes_ptr(), "the old view is copied");
        assert_eq!(*old.add(101), 0, "the copy is NUL-terminated");
        assert_eq!(from_raw_parts(old, 101), view_bytes(&first));
        let new = crate::extern_binary::fz_binary_as_cstring(&mut process, as_value(second).ref_word().raw_word());
        assert_eq!(new, second.bytes_ptr());
        assert_eq!(*new.add(103), 0);
    }
}

/// A buffer made reachable from another heap is never appended to again.
#[test]
fn a_buffer_that_crossed_to_another_heap_is_never_appended_to() {
    let mut source = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut destination = Heap::new(SIZE_TABLE[0], fresh_registry());
    let first = first_view(&mut source);
    let copied = crate::heap::deep_copy_slot(as_value(first), &source.view(), &mut destination);
    assert_eq!(unsafe { (*first.shared_raw()).spare() }, 0);
    let second = concat(&mut source, as_value(first), b"cd");
    assert_ne!(
        second.shared_raw(),
        first.shared_raw(),
        "a frozen buffer is not written"
    );
    let copy = unsafe { BinView::from_raw(copied.heap_addr().unwrap()) };
    assert_eq!(copy.bytes_len(), 101);
    assert_eq!(view_bytes(&copy), view_bytes(&first));
}

/// Room too small for the right side means a new buffer, with the left side
/// and the right side each written once.
#[test]
fn a_buffer_without_enough_room_gives_a_new_buffer_with_room_to_grow() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut current = first_view(&mut heap);
    let first_buffer = current.shared_raw();
    let spare = unsafe { (*first_buffer).spare() };
    assert_eq!(spare, 101, "a result of 101 bytes gets as much room again");
    let big = vec![b'z'; spare + 1];
    current = concat(&mut heap, as_value(current), &big);
    assert_ne!(current.shared_raw(), first_buffer);
    assert_eq!(current.bytes_len(), 101 + spare + 1);
    assert_eq!(unsafe { (*current.shared_raw()).spare() }, current.bytes_len());
    assert_eq!(&view_bytes(&current)[..100], &[b'a'; 100][..]);
    assert_eq!(&view_bytes(&current)[101..], big.as_slice());
}

/// Only a view that ends at the written end appends; an earlier view of the
/// same buffer gets a copy.
#[test]
fn a_view_that_ends_before_the_written_end_does_not_append() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let first = first_view(&mut heap);
    let second = concat(&mut heap, as_value(first), b"cd");
    let sibling = concat(&mut heap, as_value(first), b"XY");
    assert_ne!(sibling.shared_raw(), second.shared_raw());
    assert_eq!(&view_bytes(&second)[100..], b"bcd");
    assert_eq!(&view_bytes(&sibling)[100..], b"bXY");
}

/// Buffers that no concatenation allocated have no room: a plain copy of
/// bytes, and the static buffers the compiler bakes.
#[test]
fn a_buffer_no_concatenation_allocated_has_no_spare_room() {
    let handle = SharedBinHandle::from_bytes(&[7; 200]);
    assert_eq!(unsafe { (*handle.as_raw()).spare() }, 0);
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let whole = alloc_buffer_view(&mut heap, handle, 200 * 8, StubSite::FilledBuffer);
    let longer = concat(&mut heap, as_value(whole), b"x");
    assert_ne!(longer.shared_raw(), whole.shared_raw());
    assert_eq!(whole.bytes_len(), 200);
}

/// The compiler writes a zero where `room` lives, and a zero means no room.
#[test]
fn a_static_buffer_with_a_zero_room_word_has_no_spare_room() {
    unsafe extern "C" fn noop(_: *mut SharedBin) {}
    static PAYLOAD: [u8; 8] = [1; 8];
    let sb = SharedBin {
        refcount: AtomicUsize::new(1),
        bytes_ptr: PAYLOAD.as_ptr(),
        bytes_len: 8,
        destructor: noop,
        room: 0,
    };
    assert_eq!(sb.spare(), 0);
}

/// A buffer with no spare room has nothing for a message copy to close, so the
/// copy only reads it. A compiler-baked static buffer is one, and every
/// scheduler thread that sends a view of it reads the same word.
#[test]
fn a_message_copy_never_writes_into_a_buffer_with_no_room() {
    unsafe extern "C" fn noop(_: *mut SharedBin) {}
    static PAYLOAD: [u8; 100] = [3; 100];
    let baked: &'static mut SharedBin = Box::leak(Box::new(SharedBin {
        refcount: AtomicUsize::new(1),
        bytes_ptr: PAYLOAD.as_ptr(),
        bytes_len: PAYLOAD.len(),
        destructor: noop,
        room: 0,
    }));
    let baked: *mut SharedBin = baked;
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut receiver = Heap::new(SIZE_TABLE[0], fresh_registry());
    let handle = unsafe { SharedBinHandle::retain_from_raw(baked) };
    let literal = alloc_buffer_view(&mut sender, handle, 100 * 8, StubSite::StaticLiteral);
    let copied = crate::heap::deep_copy_slot(as_value(literal), &sender.view(), &mut receiver);
    assert_eq!(
        unsafe { (*baked).room },
        0,
        "the copy stored into the buffer's room word"
    );
    assert_eq!(copied.kind(), crate::any_value::ValueKind::BINVIEW);
}

/// A concatenated buffer is freed whole by the last release, whatever its
/// room, written bytes or frozen state were.
#[test]
fn a_concatenated_buffer_is_freed_whole_whether_or_not_it_was_frozen() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let first = first_view(&mut heap);
    let second = concat(&mut heap, as_value(first), b"cd");
    unsafe { shared_bin_freeze(second.shared_raw()) };
    drop(heap); // releases both stubs; the allocator tests flag a wrong size under miri/asan
}

fn bin_of(value: AnyValue) -> Bin {
    unsafe { Bin::of_stored(value.raw(), value.kind()) }
}

/// Intent: a binary is its bits, wherever they are stored: an inline
/// bitstring and a view of a shared buffer that hold the same bits are equal.
#[test]
fn a_bin_reads_the_same_bits_from_an_inline_bitstring_and_a_view() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let inline = heap.alloc_bitstring(b"owner", 40);
    let view = alloc_buffer_view(
        &mut heap,
        SharedBinHandle::from_bytes(b"owner"),
        40,
        StubSite::FilledBuffer,
    );
    let view = AnyValue::heap_ptr(view.as_raw(), ValueKind::BINVIEW);
    assert!(bin_of(inline) == bin_of(view));
    assert_eq!(bin_of(inline).cmp(&bin_of(view)), std::cmp::Ordering::Equal);
}

/// Intent: bits past the last one are padding, not value.
#[test]
fn a_bin_ignores_the_padding_of_a_partial_last_byte() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let padded = bin_of(heap.alloc_bitstring(&[0xff, 0b1011_1111], 11));
    let clean = bin_of(heap.alloc_bitstring(&[0xff, 0b1010_0000], 11));
    let lower = bin_of(heap.alloc_bitstring(&[0xff, 0b1000_0000], 11));
    assert!(padded == clean);
    assert_eq!(padded.cmp(&clean), std::cmp::Ordering::Equal);
    assert!(lower != clean);
    assert_eq!(lower.cmp(&clean), std::cmp::Ordering::Less);
}

/// Intent: binaries order by their bytes, and a prefix sorts before every
/// binary it begins.
#[test]
fn a_bin_orders_by_bytes_and_a_prefix_comes_first() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut bin = |bytes: &[u8]| bin_of(heap.alloc_bitstring(bytes, bytes.len() as u64 * 8));
    let (ab, abc, b) = (bin(b"ab"), bin(b"abc"), bin(b"b"));
    assert_eq!(ab.cmp(&abc), std::cmp::Ordering::Less);
    assert_eq!(abc.cmp(&b), std::cmp::Ordering::Less);
    assert_eq!(b.cmp(&ab), std::cmp::Ordering::Greater);
    assert!(ab != abc);
}

/// Intent: two binaries of different lengths are unequal on their lengths
/// alone; the shorter one's bytes are never read past.
#[test]
fn bins_of_different_lengths_are_unequal_before_any_byte_is_read() {
    let bytes = [7u8];
    let one = Bin::new(bytes.as_ptr(), 8);
    let unreadable = Bin::new(std::ptr::null(), 16);
    assert!(one != unreadable);
}

/// A binary's first word is its length in both forms: a view keeps its bit
/// length where a small bitstring keeps its own, below the shared mark, so the
/// one header read answers either.
#[test]
fn a_view_keeps_its_length_where_a_small_bitstring_does() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let view = first_view(&mut heap);
    assert!(view.share());
    let header_length = unsafe { crate::any_value::bitstring_bit_len(view.as_raw()) };
    assert_eq!(header_length, 101 * 8);
    assert_eq!(view.bit_len(), 101 * 8);
    assert!(view.is_shared());
    assert_eq!(view_bytes(&view).len(), 101);
}

/// A buffer too long for a binary's header to count is refused when it is
/// allocated, so every view of a buffer has a length its header can hold.
#[test]
#[should_panic(expected = "longer than a header can count")]
fn a_buffer_longer_than_a_header_can_count_is_refused() {
    let too_long = (crate::any_value::BINARY_MAX_BIT_LEN / 8 + 1) as usize;
    shared_bin_alloc_with(too_long, 0, |_| {});
}
