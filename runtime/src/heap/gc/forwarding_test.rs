use super::*;
use crate::any_value::{
    AnyValue, AnyValueRef, ClosureDenotationId, EMPTY_LIST_BITS, bitstring_bit_len, bitstring_bytes_ptr,
    bitstring_header_word, closure_capture_set, closure_capture_value, closure_denotation, closure_header_word,
    heap_object_word, list_addr_from_tagged, map_count, map_destination_header_word, map_header_word,
    struct_addr_from_tagged, struct_header_word, struct_schema_id,
};
use crate::heap::SHARED_BIN_THRESHOLD_BYTES;
use crate::heap::{Heap, SIZE_TABLE, Schema, SchemaRegistry};
use crate::procbin::{SharedBinHandle, alloc_procbin};
use std::cell::RefCell;
use std::rc::Rc;

const LOW_NIBBLE: u64 = 0xF;

fn registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

fn collect_one(heap: &mut Heap, kind: ValueKind, addr: *mut u8) -> AnyValueRef {
    let mut roots = [AnyValueRef::from_heap_object(kind, addr).expect("heap root")];
    heap.collect(&mut roots);
    roots[0]
}

/// Four words the way a collector sees an object: only `marker_word` is ever
/// consulted, so the other words may hold anything.
fn object_with(words: [u64; 2], kind: ValueKind) -> Option<*mut u8> {
    let mut object = [0u64; 4];
    object[..2].copy_from_slice(&words);
    forwarded_target(object.as_ptr() as *const u8, kind)
}

#[test]
fn a_marker_is_the_target_with_a_set_nibble_and_decodes_back_to_the_target() {
    let mut from = [0u64; 4];
    let mut to = [0u64; 4];
    // Align the stand-in objects to 16 bytes the way the heap does.
    let from_p = (from.as_mut_ptr() as usize).next_multiple_of(16) as *mut u8;
    let to_p = (to.as_mut_ptr() as usize).next_multiple_of(16) as *mut u8;
    for kind in [
        ValueKind::LIST,
        ValueKind::STRUCT,
        ValueKind::CLOSURE,
        ValueKind::MAP,
        ValueKind::BITSTRING,
        ValueKind::PROCBIN,
        ValueKind::RESOURCE,
    ] {
        unsafe { std::ptr::write_bytes(from_p, 0, 16) };
        assert_eq!(forwarded_target(from_p, kind), None, "{kind:?}: fresh object is live");
        write_forwarding_marker(from_p, kind, to_p);
        assert_eq!(
            forwarded_target(from_p, kind),
            Some(to_p),
            "{kind:?}: marker decodes to the target"
        );
    }
}

#[test]
fn the_predicate_reads_only_the_kinds_marker_word() {
    // Every kind but List keeps its marker in word 0; the old second-word
    // "confirm" is gone, so word 1 never changes the answer.
    for kind in [
        ValueKind::STRUCT,
        ValueKind::CLOSURE,
        ValueKind::MAP,
        ValueKind::BITSTRING,
        ValueKind::PROCBIN,
        ValueKind::RESOURCE,
    ] {
        assert_eq!(
            object_with([0x40, 8], kind),
            None,
            "{kind:?}: payload 8 beside a clear marker is live"
        );
        assert_eq!(
            object_with([0x40, 0x1], kind),
            None,
            "{kind:?}: a set nibble in word 1 is not a marker"
        );
        assert!(
            object_with([0x41, 0], kind).is_some(),
            "{kind:?}: a set nibble in word 0 is a marker whatever follows"
        );
    }
    // A list cons keeps its marker in the link word, so its head may be any
    // value, including one with a set low nibble.
    assert_eq!(object_with([0x1, 0], ValueKind::LIST), None);
    assert_eq!(object_with([8, 0x10], ValueKind::LIST), None);
    assert!(object_with([0, 0x41], ValueKind::LIST).is_some());
}

#[test]
fn live_headers_of_every_kind_have_a_clear_low_nibble() {
    for schema_id in [0, 1, 8, 24, 40, u32::MAX] {
        assert_eq!(
            struct_header_word(schema_id) & LOW_NIBBLE,
            0,
            "struct schema {schema_id}"
        );
    }
    for bit_len in [0, 1, 8, 72, 0x48, u32::MAX as u64] {
        assert_eq!(
            bitstring_header_word(bit_len) & LOW_NIBBLE,
            0,
            "bitstring {bit_len} bits"
        );
    }
    for count in [0usize, 1, 8, 15, 4096] {
        assert_eq!(map_header_word(count) & LOW_NIBBLE, 0, "map of {count}");
    }
    for (capacity, filled) in [(0usize, 0usize), (1, 1), (8, 8), (15, 3), (4096, 4095)] {
        assert_eq!(
            map_destination_header_word(capacity, filled) & LOW_NIBBLE,
            0,
            "map destination {filled}/{capacity}"
        );
    }
    for (denotation, captured, halt, arity) in [
        (0, 0, 0, 0),
        (1, 1, 1, 1),
        (u32::MAX >> 1, 0x3FFF, 3, 4095),
        (73, 8, 0, 8),
    ] {
        let word = closure_header_word(ClosureDenotationId::user(denotation), captured, halt, arity);
        assert_eq!(word & LOW_NIBBLE, 0, "closure {denotation}/{captured}/{halt}/{arity}");
    }
}

#[test]
fn a_list_cell_whose_head_reads_like_a_marker_survives_a_collection() {
    let mut heap = Heap::new(SIZE_TABLE[0], registry());
    let mut tail = EMPTY_LIST_BITS;
    for head in [0x11, 8, 1, 0x48, 0xF] {
        tail = heap.alloc_list_cons_slot(AnyValue::int(head), tail);
    }
    let old = list_addr_from_tagged(tail).unwrap();
    let moved = collect_one(&mut heap, ValueKind::LIST, old);
    let mut cur = moved.list_addr().unwrap();
    assert_ne!(cur, old);
    let mut heads = Vec::new();
    while !cur.is_null() {
        let cell = unsafe { &*(cur as *const crate::any_value::ListCons) };
        heads.push(cell.head_value());
        cur = cell.tail_addr() as *mut u8;
    }
    let expected: Vec<AnyValue> = [0xF, 0x48, 1, 8, 0x11].into_iter().map(AnyValue::int).collect();
    assert_eq!(heads, expected);
}

#[test]
fn a_struct_whose_schema_id_ends_in_8_and_first_field_is_8_survives_a_collection() {
    let reg = registry();
    let mut ids = Vec::new();
    for arity in 1..=48 {
        ids.push(reg.borrow_mut().register(Schema::tuple_of_arity(arity)));
    }
    let mut heap = Heap::new(SIZE_TABLE[0], reg);
    let mut roots = Vec::new();
    for &id in ids.iter().filter(|id| **id & LOW_NIBBLE as u32 == 8) {
        let obj = heap.alloc_struct(id);
        unsafe {
            heap.write_field_slot(obj, 0, AnyValue::int(8));
            heap.write_field_slot(obj, 8, AnyValue::int(8));
        }
        roots.push(AnyValueRef::from_heap_object(ValueKind::STRUCT, obj).unwrap());
    }
    assert!(roots.len() >= 2, "the registry reached more than one id ending in 8");
    let schema_ids: Vec<u32> = roots
        .iter()
        .map(|r| unsafe { struct_schema_id(r.struct_addr().unwrap()) })
        .collect();
    heap.collect(&mut roots);
    for (root, schema_id) in roots.iter().zip(schema_ids) {
        let moved = struct_addr_from_tagged(root.heap_object_word().unwrap()).unwrap();
        assert_eq!(unsafe { struct_schema_id(moved) }, schema_id);
        assert_eq!(heap.read_field_slot(moved, 0), AnyValue::int(8));
        assert_eq!(heap.read_field_slot(moved, 8), AnyValue::int(8));
    }
}

#[test]
fn a_closure_whose_header_and_capture_read_like_a_marker_survives_a_collection() {
    let mut heap = Heap::new(SIZE_TABLE[0], registry());
    let bits = heap.alloc_closure_slots(ClosureDenotationId::user(8), 8, 1, 0);
    let old = crate::any_value::closure_addr_from_tagged(bits).unwrap();
    unsafe { closure_capture_set(old, 0, AnyValue::int(8)) };
    let moved = collect_one(&mut heap, ValueKind::CLOSURE, old).closure_addr().unwrap();
    assert_ne!(moved, old);
    assert_eq!(unsafe { closure_denotation(moved) }, ClosureDenotationId::user(8));
    assert_eq!(unsafe { crate::any_value::closure_arity(moved) }, 8);
    assert_eq!(unsafe { closure_capture_value(moved, 0) }, AnyValue::int(8));
}

#[test]
fn a_map_whose_count_and_first_entry_read_like_a_marker_survives_a_collection() {
    let mut heap = Heap::new(SIZE_TABLE[0], registry());
    let entries: Vec<(AnyValue, AnyValue)> = (0..8).map(|k| (AnyValue::int(k), AnyValue::int(8))).collect();
    let bits = heap.alloc_map_slots(&entries);
    let old = crate::any_value::map_addr_from_tagged(bits).unwrap();
    let moved = collect_one(&mut heap, ValueKind::MAP, old).map_addr().unwrap();
    assert_ne!(moved, old);
    assert_eq!(unsafe { map_count(moved) }, 8);
    for k in 0..8 {
        assert_eq!(unsafe { crate::any_value::map_entry(moved, k) }.1, AnyValue::int(8));
    }
}

#[test]
fn an_inline_bitstring_whose_bytes_read_like_a_marker_survives_a_collection() {
    let mut heap = Heap::new(SIZE_TABLE[0], registry());
    let payload = [8u8, 0, 0, 0, 0, 0, 0, 0, 1];
    let value = heap.alloc_bitstring(&payload, 72);
    let old = value.heap_addr().unwrap();
    let moved = collect_one(&mut heap, ValueKind::BITSTRING, old)
        .bitstring_addr()
        .unwrap();
    assert_ne!(moved, old);
    assert_eq!(unsafe { bitstring_bit_len(moved) }, 72);
    let bytes = unsafe { std::slice::from_raw_parts(bitstring_bytes_ptr(moved), payload.len()) };
    assert_eq!(bytes, payload);
}

#[test]
fn a_procbin_stub_over_bytes_that_read_like_a_marker_survives_a_collection() {
    let mut heap = Heap::new(SIZE_TABLE[0], registry());
    let mut bytes = vec![0u8; SHARED_BIN_THRESHOLD_BYTES + 1];
    bytes[0] = 8;
    bytes[8] = 1;
    let handle = SharedBinHandle::from_bytes(&bytes, bytes.len() as u64 * 8);
    let stub = alloc_procbin(&mut heap, handle, 0);
    let (old, shared) = (stub.as_raw(), stub.shared_raw());
    let moved = collect_one(&mut heap, ValueKind::PROCBIN, old).procbin_addr().unwrap();
    assert_ne!(moved, old);
    let moved = unsafe { crate::procbin::ProcBin::from_raw(moved) };
    assert_eq!(moved.shared_raw(), shared);
    assert_eq!(moved.bit_len(), bytes.len() as u64 * 8);
}

#[test]
fn the_heap_word_of_a_live_object_is_never_a_marker() {
    let mut heap = Heap::new(SIZE_TABLE[0], registry());
    let list = heap.alloc_list_cons_slot(AnyValue::int(1), EMPTY_LIST_BITS);
    let word = heap_object_word(list_addr_from_tagged(list).unwrap(), ValueKind::LIST);
    assert_eq!(
        word & LOW_NIBBLE,
        0,
        "a heap word carries the kind in its high bits, not the low"
    );
}
