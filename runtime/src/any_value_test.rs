use super::*;
use std::mem;

#[test]
fn list_cons_size_is_16() {
    assert_eq!(mem::size_of::<ListCons>(), 16);
}

#[test]
fn list_cons_layout() {
    let bits = alloc_list_cons_raw_kind(7, ValueKind::INT, EMPTY_LIST);
    let p = list_addr_from_tagged(bits).expect("tagged list ptr");
    unsafe {
        let cons = &*(p as *mut ListCons);
        assert_eq!(cons.head_kind(), ValueKind::INT);
        assert_eq!(cons.head as i64, 7);
        assert_eq!(cons.tail_bits(), EMPTY_LIST);
        assert_eq!(cons.link & TAG_MASK, 0);
        assert_eq!((cons.link & LIST_LINK_KIND_MASK) >> LIST_LINK_KIND_SHIFT, TAG_KIND_INT);
        assert!(!cons.aliased());
    }
}

#[test]
fn list_cons_chain() {
    // [1, 2, 3]
    let l3 = alloc_list_cons_raw_kind(3, ValueKind::INT, EMPTY_LIST);
    let l2 = alloc_list_cons_raw_kind(2, ValueKind::INT, l3);
    let l1 = alloc_list_cons_raw_kind(1, ValueKind::INT, l2);
    unsafe {
        let c1 = &*(list_addr_from_tagged(l1).unwrap() as *mut ListCons);
        assert_eq!(c1.head_value(), AnyValue::int(1));
        let c2 = &*(list_addr_from_tagged(c1.tail_bits()).unwrap() as *mut ListCons);
        assert_eq!(c2.head_value(), AnyValue::int(2));
        let c3 = &*(list_addr_from_tagged(c2.tail_bits()).unwrap() as *mut ListCons);
        assert_eq!(c3.head_value(), AnyValue::int(3));
        assert_eq!(c3.tail_bits(), EMPTY_LIST);
    }
}

#[test]
fn alloc_struct_zeros_payload_and_sets_prefix() {
    let p = alloc_struct(7, 24);
    unsafe {
        assert_eq!(struct_schema_id(p), 7);
        assert_eq!(struct_flags(p), 0);
        assert_eq!(struct_size_for_payload(24), 32);
        let payload = p.add(8);
        for i in 0..24 {
            assert_eq!(*payload.add(i), 0);
        }
    }
}

#[test]
fn pointer_alignment_satisfies_tag_zero_low_bits() {
    let p = alloc_struct(0, 0);
    assert_eq!((p as u64) & TAG_MASK, 0);
}

#[test]
fn tag_constants_all_distinct() {
    let tags = [
        TAG_NULL,
        TAG_LIST,
        TAG_MAP,
        TAG_STRUCT,
        TAG_CLOSURE,
        TAG_BITSTRING,
        TAG_PROCBIN,
        TAG_RESOURCE,
        TAG_FWD,
        TAG_KIND_INT,
        TAG_KIND_FLOAT,
        TAG_KIND_ATOM,
    ];
    for (i, a) in tags.iter().enumerate() {
        for b in tags.iter().skip(i + 1) {
            assert_ne!(a, b);
        }
    }
}

#[test]
fn tag_constants_fit_in_4_bits() {
    for tag in [
        TAG_NULL,
        TAG_LIST,
        TAG_MAP,
        TAG_STRUCT,
        TAG_CLOSURE,
        TAG_BITSTRING,
        TAG_PROCBIN,
        TAG_RESOURCE,
        TAG_FWD,
        TAG_KIND_INT,
        TAG_KIND_FLOAT,
        TAG_KIND_ATOM,
    ] {
        assert!(tag <= TAG_MASK);
    }
}

#[test]
fn kind_round_trip() {
    let addr = 0x1000_u64;
    for tag in [
        TAG_LIST,
        TAG_MAP,
        TAG_STRUCT,
        TAG_CLOSURE,
        TAG_BITSTRING,
        TAG_PROCBIN,
        TAG_RESOURCE,
    ] {
        let tagged = addr | tag;
        assert_eq!(tagged & TAG_MASK, tag);
        assert_eq!(tagged & !TAG_MASK, addr);
    }
}

#[test]
fn strict_heap_kind_comes_from_pointer_low_bits() {
    let addr = 0x1000 as *const u8;
    for (kind, tag) in [
        (ValueKind::LIST, TAG_LIST),
        (ValueKind::MAP, TAG_MAP),
        (ValueKind::STRUCT, TAG_STRUCT),
        (ValueKind::CLOSURE, TAG_CLOSURE),
        (ValueKind::BITSTRING, TAG_BITSTRING),
        (ValueKind::PROCBIN, TAG_PROCBIN),
        (ValueKind::RESOURCE, TAG_RESOURCE),
    ] {
        let bits = heap_object_word(addr, kind);

        assert_eq!(bits, 0x1000 | tag);
        assert_eq!(heap_kind_from_tagged(bits), Some(kind));
        assert_eq!(heap_addr_from_tagged(bits), Some(0x1000 as *mut u8));
    }
}

#[test]
fn value_kind_rejects_non_value_tags() {
    assert_eq!(ValueKind::new(TAG_FWD as u8), None);
    assert_eq!(ValueKind::new(9), None);
    assert_eq!(ValueKind::new(10), None);
    assert_eq!(ValueKind::new(11), None);
    assert_eq!(ValueKind::new(12), None);
}

#[test]
fn any_value_constructors_use_canonical_value_kind_tags() {
    let null = AnyValue::null();
    assert_eq!(null.raw(), 0);
    assert_eq!(null.kind(), ValueKind::NULL);

    let int = AnyValue::int(-12);
    assert_eq!(int.raw() as i64, -12);
    assert_eq!(int.kind(), ValueKind::INT);

    let atom = AnyValue::atom(42);
    assert_eq!(atom.raw(), 42);
    assert_eq!(atom.kind(), ValueKind::ATOM);

    let float = AnyValue::float(3.5);
    assert_eq!(f64::from_bits(float.raw()), 3.5);
    assert_eq!(float.kind(), ValueKind::FLOAT);

    let heap = AnyValue::heap_ptr(0x1000 as *mut u8, ValueKind::MAP);
    assert_eq!(heap.raw(), 0x1000);
    assert_eq!(heap.kind(), ValueKind::MAP);
    assert_eq!(heap.heap_object_word(), Some(0x1000 | TAG_MAP));
}

#[test]
fn any_value_round_trip_without_packed_scalar_tags() {
    let values = [
        AnyValue::int(-12),
        AnyValue::atom(42),
        AnyValue::null(),
        AnyValue::bool_atom(true),
        AnyValue::bool_atom(false),
        AnyValue::empty_list(),
    ];

    for value in values {
        let decoded = AnyValue::decode_parts(value.raw(), value.kind().tag()).expect("value slot parts");
        assert_eq!(decoded, value);
    }

    assert_eq!(AnyValue::int(7).raw(), 7);
    assert_eq!(AnyValue::atom(TRUE_ATOM_ID).raw(), TRUE_ATOM_ID as u64);
    assert_eq!(AnyValue::nil_atom().raw(), NIL_ATOM_ID as u64);
    assert_eq!(AnyValue::bool_atom(true).raw(), TRUE_ATOM_ID as u64);
    assert_eq!(AnyValue::bool_atom(false).raw(), FALSE_ATOM_ID as u64);
    assert_eq!(AnyValue::empty_list().raw(), 0);
}

#[test]
fn any_value_decode_parts_uses_low_kind_nibble() {
    let decoded = AnyValue::decode_parts(0, TAG_MASK as u8 + 1).expect("masked kind byte");
    assert_eq!(decoded, AnyValue::null());
}

#[test]
fn any_value_decodes_side_band_parts_without_packed_tags() {
    let looks_like_packed_int = 0x11;
    let decoded =
        AnyValue::decode_parts(looks_like_packed_int, ValueKind::LIST.tag()).expect("strict side-band decode");

    assert_eq!(decoded.raw(), looks_like_packed_int);
    assert_eq!(decoded.kind(), ValueKind::LIST);
}

#[test]
fn any_value_decodes_tagged_heap_bits_from_low_four_bits() {
    let decoded = AnyValue::decode_tagged_heap_bits(0x2000 | TAG_RESOURCE).expect("heap bits");

    assert_eq!(decoded.raw(), 0x2000);
    assert_eq!(decoded.kind(), ValueKind::RESOURCE);
    assert_eq!(decoded.heap_addr(), Some(0x2000 as *mut u8));
}

#[test]
fn list_cons_stores_canonical_head_kind_in_link_high_bits() {
    let cons = ListCons::new(2.5f64.to_bits(), ValueKind::FLOAT, EMPTY_LIST);

    assert_eq!(cons.head, 2.5f64.to_bits());
    assert_eq!(cons.head_kind(), ValueKind::FLOAT);
    assert_eq!(cons.head_value(), AnyValue::float(2.5));
    assert_eq!(cons.tail_bits(), EMPTY_LIST);
    assert_eq!(cons.link & TAG_MASK, 0);
    assert_eq!(
        (cons.link & LIST_LINK_KIND_MASK) >> LIST_LINK_KIND_SHIFT,
        TAG_KIND_FLOAT
    );
}

#[test]
fn list_link_keeps_alias_bit_in_high_metadata() {
    let tail = alloc_list_cons_raw_kind(3, ValueKind::INT, EMPTY_LIST);
    let mut cons = ListCons::new(7, ValueKind::INT, tail);

    assert_eq!(cons.tail_bits(), tail);
    assert!(!cons.aliased());

    cons.mark_aliased();

    assert!(cons.aliased());
    assert_eq!(cons.head_kind(), ValueKind::INT);
    assert_eq!(cons.tail_bits(), tail);
    assert_ne!(cons.link & LIST_LINK_ALIAS_MASK, 0);
    assert_eq!(cons.link & TAG_MASK, 0);
}

#[test]
fn list_link_tail_rewrite_preserves_high_metadata() {
    let old_tail = alloc_list_cons_raw_kind(1, ValueKind::INT, EMPTY_LIST);
    let new_tail = alloc_list_cons_raw_kind(2, ValueKind::INT, EMPTY_LIST);
    let mut cons = ListCons::new(7, ValueKind::ATOM, old_tail);
    cons.mark_aliased();

    cons.set_tail_bits(new_tail);

    assert_eq!(cons.head_kind(), ValueKind::ATOM);
    assert!(cons.aliased());
    assert_eq!(cons.tail_bits(), new_tail);
}

#[test]
fn forwarding_marker_distinguishable() {
    for heap_tag in [
        TAG_LIST,
        TAG_MAP,
        TAG_STRUCT,
        TAG_CLOSURE,
        TAG_BITSTRING,
        TAG_PROCBIN,
        TAG_RESOURCE,
    ] {
        assert_ne!(TAG_FWD, heap_tag);
    }
}

#[test]
fn forward_marker_distinguishable_from_pointers() {
    let addr = 0x1000_u64;
    let marker = addr | TAG_FWD;
    for heap_tag in [
        TAG_LIST,
        TAG_MAP,
        TAG_STRUCT,
        TAG_CLOSURE,
        TAG_BITSTRING,
        TAG_PROCBIN,
        TAG_RESOURCE,
    ] {
        assert_ne!(marker, addr | heap_tag);
    }
}

#[test]
fn is_forwarded_detects_marker() {
    let mut words = [0_u64; 2];
    let to_space = 0x2000_u64;
    words[0] = (to_space & !TAG_MASK) | TAG_FWD;

    let found = is_forwarded(words.as_ptr() as *const u8);

    assert_eq!(found, Some(to_space as *const u8));
}

#[test]
fn object_size_returns_list_size() {
    let ptr_with_tag = 0x1000_u64 | TAG_LIST;
    assert_eq!(object_size(ptr_with_tag), 16);
}

#[test]
fn object_size_dispatches_from_pointer_tag_and_object_local_metadata() {
    #[repr(align(16))]
    struct AlignedWords([u64; 8]);

    let mut words = AlignedWords([0; 8]);
    let addr = words.0.as_mut_ptr() as *mut u8;
    let write_word0 = |value| unsafe {
        ptr::write(addr as *mut u64, value);
    };

    write_word0(3);
    assert_eq!(
        object_size(heap_object_word(addr, ValueKind::MAP)),
        map_size_for_count(3)
    );

    write_word0(7);
    assert_eq!(
        object_size_with_struct_payload(heap_object_word(addr, ValueKind::STRUCT), |schema| {
            assert_eq!(schema, 7);
            24
        }),
        struct_size_for_payload(24)
    );

    write_word0((closure_flags_pack(2, 0) as u64) << 32);
    assert_eq!(
        object_size(heap_object_word(addr, ValueKind::CLOSURE)),
        closure_size_for_count(2)
    );

    write_word0(17);
    assert_eq!(
        object_size(heap_object_word(addr, ValueKind::BITSTRING)),
        bitstring_size_for_bit_len(17)
    );
    assert_eq!(object_size(heap_object_word(addr, ValueKind::PROCBIN)), 16);
    assert_eq!(object_size(heap_object_word(addr, ValueKind::RESOURCE)), 48);
}

#[test]
fn immediate_tags_not_used_for_pointers() {
    let p = alloc_struct(0, 0) as u64;
    assert_eq!(p & TAG_MASK, TAG_NULL);
    assert_ne!(p & TAG_MASK, TAG_KIND_INT);
    assert_ne!(p & TAG_MASK, TAG_KIND_FLOAT);
    assert_ne!(p & TAG_MASK, TAG_KIND_ATOM);
}

#[test]
fn any_value_recognizes_explicit_list_typed_pointer() {
    let addr = 0x1000 as *mut u8;
    let tv = AnyValue::heap_ptr(addr, ValueKind::LIST);

    assert_eq!(tv.kind(), ValueKind::LIST);
    assert_eq!(tv.heap_addr(), Some(addr));
    assert_eq!(tv.heap_object_word(), Some(0x1000 | TAG_LIST));
}
