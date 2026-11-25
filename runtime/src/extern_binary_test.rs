use super::*;
use crate::any_value::{AnyValueRef, ValueKind};
use crate::bits::{BinView, SharedBinHandle, alloc_binref, alloc_view};
use crate::heap::Heap;
use crate::heap::SchemaRegistry;
use crate::heap::StubSite;
use crate::process::Process;
use std::cell::RefCell;
use std::rc::Rc;
use std::slice::from_raw_parts;

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

fn fresh_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

/// Heap-allocated inline Bitstring goes through as_ptr cleanly and the
/// byte at `bytes_len` reads as 0 via the c_string helper.
#[test]
fn ptr_and_cstring_on_inline_bitstring() {
    let mut process = Process::new(fresh_registry());
    let h = &mut process.heap;
    let payload = b"/tmp/fz-fixture";
    let p = h
        .alloc_bitstring(payload, (payload.len() as u64) * 8)
        .heap_addr()
        .expect("bitstring");
    let v = AnyValueRef::from_heap_object(ValueKind::BITSTRING, p)
        .expect("bitstring ref")
        .raw_word();
    unsafe {
        let bp = fz_binary_as_ptr(v);
        assert!(!bp.is_null());
        let read = from_raw_parts(bp, payload.len());
        assert_eq!(read, payload);

        let cs = fz_binary_as_cstring(&mut process, v);
        assert!(!cs.is_null());
        assert_eq!(*cs.add(payload.len()), 0, "trailing NUL must be reachable");
    }
}

/// Above-threshold payload routes through BinView → SharedBin; both
/// helpers still work and the NUL is reachable.
#[test]
fn ptr_and_cstring_on_binview() {
    let mut process = Process::new(fresh_registry());
    let h = &mut process.heap;
    // Large enough to cross SHARED_BIN_THRESHOLD_BYTES.
    let payload: Vec<u8> = (0..4096u32).map(|i| (i & 0xff) as u8).collect();
    let p = h
        .alloc_bitstring(&payload, (payload.len() as u64) * 8)
        .heap_addr()
        .expect("binview");
    let v = AnyValueRef::from_heap_object(ValueKind::BINVIEW, p)
        .expect("binview ref")
        .raw_word();
    unsafe {
        let bp = fz_binary_as_ptr(v);
        let read = from_raw_parts(bp, payload.len());
        assert_eq!(read, payload.as_slice());

        let cs = fz_binary_as_cstring(&mut process, v);
        assert_eq!(*cs.add(payload.len()), 0);
    }
}

fn view_word(process: &mut Process, bytes: &[u8], offset: u64, len: u64) -> u64 {
    let handle = SharedBinHandle::from_bytes(bytes);
    let view = window_of_new_buffer(
        &mut process.heap,
        handle,
        offset as usize,
        len * 8,
        StubSite::FilledBuffer,
    );
    AnyValueRef::from_heap_object(ValueKind::BINVIEW, view.as_raw())
        .expect("binview ref")
        .raw_word()
}

/// A view that ends where its buffer ends has the buffer's NUL right after
/// it, so C gets the very bytes the view names and nothing is copied.
#[test]
fn cstring_of_a_tail_view_points_into_the_shared_buffer() {
    let mut process = Process::new(fresh_registry());
    let bytes: Vec<u8> = (1..=200u8).collect();
    let v = view_word(&mut process, &bytes, 150, 50);
    let before = process.heap.node.alloc_stats().binview.allocs;
    unsafe {
        let cs = fz_binary_as_cstring(&mut process, v);
        assert_eq!(cs, fz_binary_as_ptr(v), "a tail needs no copy");
        assert_eq!(from_raw_parts(cs, 51), &[&bytes[150..], &[0u8][..]].concat()[..]);
    }
    assert_eq!(process.heap.node.alloc_stats().binview.allocs, before);
}

/// A view that ends before its buffer does has the next byte of the parent
/// after it, not a NUL, so the c_string is a NUL-terminated copy of exactly
/// the view's bytes.
#[test]
fn cstring_of_a_middle_view_is_a_nul_terminated_copy_of_the_slice() {
    let mut process = Process::new(fresh_registry());
    let bytes: Vec<u8> = (1..=200u8).collect();
    let v = view_word(&mut process, &bytes, 50, 100);
    unsafe {
        let cs = fz_binary_as_cstring(&mut process, v);
        assert_ne!(cs, fz_binary_as_ptr(v), "a middle view has no NUL after it");
        assert_eq!(from_raw_parts(cs, 101), &[&bytes[50..150], &[0u8][..]].concat()[..]);
    }
}
