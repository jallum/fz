use super::*;
use crate::any_value::{AnyValue, object_size};
use crate::bits::bits_test::{fresh_registry, observed_bin};
use crate::bits::{BINVIEW_BYTES, alloc_buffer_view};
use crate::heap::{Heap, SIZE_TABLE, StubSite};
use crate::sync::Ordering;
use std::sync::Arc;

/// A fresh buffer's BinRef is the chain's only entry and its view a 32-byte
/// heap object of its own kind; dropping the heap releases the SharedBin.
#[test]
fn dropping_a_heap_releases_the_buffer_its_binref_holds() {
    let (handle, drops) = observed_bin();
    {
        let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
        let handle_bits = handle.bytes_len() as u64 * 8;
        let pb = alloc_buffer_view(&mut h, handle, handle_bits, StubSite::FilledBuffer);
        let tagged = heap_object_word(pb.as_raw() as *const u8, ValueKind::BINVIEW);
        assert_eq!(heap_kind_from_tagged(tagged), Some(ValueKind::BINVIEW));
        assert_eq!(object_size(tagged), BINVIEW_BYTES);
        assert_eq!(h.off_heap_head, pb.binref().word());
        assert_eq!(pb.binref().off_heap_next(), 0);
        assert_eq!(drops.load(Ordering::Relaxed), 0);
    }
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

/// Three BinRefs on one heap: intrusive chain links latest → earlier.
#[test]
fn off_heap_chain_threads_through_binrefs_and_frees_every_entry() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (first, first_drops) = observed_bin();
    let (second, second_drops) = observed_bin();
    let (third, third_drops) = observed_bin();
    let first_bits = first.bytes_len() as u64 * 8;
    let pb1 = alloc_buffer_view(&mut h, first, first_bits, StubSite::FilledBuffer);
    let second_bits = second.bytes_len() as u64 * 8;
    let pb2 = alloc_buffer_view(&mut h, second, second_bits, StubSite::FilledBuffer);
    let third_bits = third.bytes_len() as u64 * 8;
    let pb3 = alloc_buffer_view(&mut h, third, third_bits, StubSite::FilledBuffer);
    let pb1_bits = pb1.binref().word();
    let pb2_bits = pb2.binref().word();
    let pb3_bits = pb3.binref().word();
    assert_eq!(h.off_heap_head, pb3_bits);
    assert_eq!(pb3.binref().off_heap_next(), pb2_bits);
    assert_eq!(pb2.binref().off_heap_next(), pb1_bits);
    assert_eq!(pb1.binref().off_heap_next(), 0);
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
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let handle_bits = handle.bytes_len() as u64 * 8;
    alloc_buffer_view(&mut heap, handle, handle_bits, StubSite::FilledBuffer);
    heap.collect_tagged(&mut std::ptr::null_mut());
    assert_eq!(drops.load(Ordering::Relaxed), 1);
    assert_eq!(heap.off_heap_head, 0);
    drop(heap);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

#[test]
fn copied_shared_bin_is_freed_only_when_the_last_heap_releases_it() {
    let (handle, drops) = observed_bin();
    let mut source = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut destination = Heap::new(SIZE_TABLE[0], fresh_registry());
    let handle_bits = handle.bytes_len() as u64 * 8;
    let pb = alloc_buffer_view(&mut source, handle, handle_bits, StubSite::FilledBuffer);
    crate::heap::deep_copy_slot(
        AnyValue::heap_ptr(pb.as_raw(), ValueKind::BINVIEW),
        &source.view(),
        &mut destination,
        &mut crate::heap::AddressMap::default(),
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
