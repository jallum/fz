use super::*;
use super::fragment::FRAGMENT_THRESHOLD;
use super::ref_io::value_ref_addr;
use crate::fz_value::ValueKind;
use std::cell::RefCell;
use std::rc::Rc;

    use crate::fz_value::ValueKind;

    fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
        Rc::new(RefCell::new(SchemaRegistry::new()))
    }

    fn heap_root(bits: u64) -> AnyValue {
        AnyValue::decode_tagged_heap_bits(bits).expect("tagged heap root")
    }

    fn root_bits(value: AnyValue) -> u64 {
        crate::fz_value::value
            .heap_object_word()
            .expect("heap root bits")
    }

    fn tagged_bits(value: AnyValue) -> u64 {
        crate::fz_value::value
            .heap_object_word()
            .expect("tagged heap bits")
    }

    fn alloc_int_list_cons(heap: &mut Heap, head: i64, tail_bits: u64) -> u64 {
        heap.alloc_list_cons_slot(AnyValue::int(head), tail_bits)
    }

    #[test]
    fn tagged_ref_list_reads_scalar_head_and_heap_tail() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let tail_bits = h.alloc_list_cons_slot(AnyValue::atom(9), crate::fz_value::EMPTY_LIST_BITS);
        let tail_addr = crate::fz_value::list_addr_from_tagged(tail_bits).expect("tail addr");
        let list_bits = h.alloc_list_cons_slot(AnyValue::int(42), tail_bits);
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("list addr");
        let list_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr).expect("list ref");

        assert_eq!(h.read_list_head_ref(list_ref).unwrap().load_int(), Ok(42));
        assert_eq!(
            h.read_list_tail_ref(list_ref).unwrap().list_addr(),
            Ok(tail_addr)
        );
        assert_eq!(
            h.read_list_tail_ref(
                TaggedValueRef::from_heap_object(TaggedValueTag::List, tail_addr)
                    .expect("tail ref")
            )
            .unwrap()
            .tag(),
            TaggedValueTag::EmptyList
        );
    }

    #[test]
    fn tagged_ref_list_reads_heap_object_head() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let child_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
        let child_addr = crate::fz_value::map_addr_from_tagged(child_bits).expect("map addr");
        let list_bits = h.alloc_list_cons_slot(
            AnyValue::heap_ptr(child_addr, ValueKind::MAP),
            crate::fz_value::EMPTY_LIST_BITS,
        );
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("list addr");
        let list_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr).expect("list ref");

        assert_eq!(
            h.read_list_head_ref(list_ref).unwrap().map_addr(),
            Ok(child_addr)
        );
    }

    #[test]
    fn tagged_ref_map_lookup_reads_scalar_and_heap_values() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let child_bits =
            h.alloc_list_cons_slot(AnyValue::atom(1), crate::fz_value::EMPTY_LIST_BITS);
        let child_addr = crate::fz_value::list_addr_from_tagged(child_bits).expect("child addr");
        let map_bits = h.alloc_map_slots(&[
            (AnyValue::int(1), AnyValue::int(10)),
            (
                AnyValue::atom(2),
                AnyValue::heap_ptr(child_addr, ValueKind::LIST),
            ),
        ]);
        let map_addr = crate::fz_value::map_addr_from_tagged(map_bits).expect("map addr");
        let map_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Map, map_addr).expect("map ref");
        let int_key_slot = 1u64;
        let atom_key_slot = 2u64;
        let missing_key_slot = 3u64;

        let scalar = h
            .read_map_value_ref(
                map_ref,
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &int_key_slot)
                    .expect("int key"),
            )
            .unwrap()
            .expect("present int key");
        assert_eq!(scalar.load_int(), Ok(10));

        let heap_value = h
            .read_map_value_ref(
                map_ref,
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, &atom_key_slot)
                    .expect("atom key"),
            )
            .unwrap()
            .expect("present atom key");
        assert_eq!(heap_value.list_addr(), Ok(child_addr));

        assert_eq!(
            h.read_map_value_ref(
                map_ref,
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, &missing_key_slot)
                    .expect("missing key"),
            )
            .unwrap(),
            None
        );
    }

    #[test]
    fn tagged_ref_struct_reads_scalar_and_heap_fields() {
        let reg = empty_registry();
        let schema_id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let child_bits =
            h.alloc_list_cons_slot(AnyValue::atom(1), crate::fz_value::EMPTY_LIST_BITS);
        let child_addr = crate::fz_value::list_addr_from_tagged(child_bits).expect("child addr");
        let obj = h.alloc_struct(schema_id);
        h.write_field_slot(obj, 0, AnyValue::float(2.5));
        h.write_field_slot(obj, 8, AnyValue::heap_ptr(child_addr, ValueKind::LIST));
        let obj_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Struct, obj).expect("struct ref");

        assert_eq!(
            h.read_struct_field_ref(obj_ref, 0).unwrap().load_float(),
            Ok(2.5)
        );
        assert_eq!(
            h.read_struct_field_ref(obj_ref, 8).unwrap().list_addr(),
            Ok(child_addr)
        );
    }

    #[test]
    fn tagged_ref_closure_capture_reads_are_ported() {
        let reg = empty_registry();
        let schema_id = reg.borrow_mut().register(Schema::tuple_of_arity(0));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let child_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
        let child_addr = crate::fz_value::map_addr_from_tagged(child_bits).expect("child addr");
        let closure_bits = h.alloc_closure(
            schema_id,
            2,
            0,
            0xfeed,
            &[
                AnyValue::atom(7),
                AnyValue::heap_ptr(child_addr, ValueKind::MAP),
            ],
        );
        let closure_addr =
            crate::fz_value::closure_addr_from_tagged(closure_bits).expect("closure addr");
        let closure_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Closure, closure_addr)
            .expect("closure ref");

        assert_eq!(
            h.read_closure_capture_ref(closure_ref, 0)
                .unwrap()
                .load_atom(),
            Ok(7)
        );
        assert_eq!(
            h.read_closure_capture_ref(closure_ref, 1)
                .unwrap()
                .map_addr(),
            Ok(child_addr)
        );
    }

    #[test]
    fn typed_list_construction_writes_scalar_head_and_heap_tail() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let tail_bits = h.alloc_list_cons_slot(AnyValue::atom(1), crate::fz_value::EMPTY_LIST_BITS);
        let tail_addr = crate::fz_value::list_addr_from_tagged(tail_bits).expect("tail addr");
        let tail_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, tail_addr).expect("tail ref");

        let list_ref = h.alloc_list_cons_int(42, tail_ref).expect("list ref");

        assert_eq!(h.read_list_head_ref(list_ref).unwrap().load_int(), Ok(42));
        assert_eq!(
            h.read_list_tail_ref(list_ref).unwrap().list_addr(),
            Ok(tail_addr)
        );
    }

    #[test]
    #[should_panic(
        expected = "alloc_list_cons_ref head requires a heap/sentinel ref; use the typed scalar write path"
    )]
    fn list_ref_construction_rejects_scalar_head() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let head_slot = 42u64;
        let head_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &head_slot).expect("head ref");

        let _ = h.alloc_list_cons_ref(head_ref, TaggedValueRef::empty_list());
    }

    #[test]
    fn tagged_ref_list_construction_rejects_non_list_tail() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let head_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
        let head_addr = crate::fz_value::map_addr_from_tagged(head_bits).expect("head addr");
        let tail_slot = 2u64;
        let head_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Map, head_addr).expect("head ref");
        let tail_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &tail_slot).expect("tail ref");

        assert_eq!(
            h.alloc_list_cons_ref(head_ref, tail_ref),
            Err(TaggedValueRefError::ExpectedTag {
                expected: TaggedValueTag::List,
                found: TaggedValueTag::Int
            })
        );
    }

    #[test]
    fn tagged_ref_map_construction_and_put_write_scalar_and_heap_values() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let child_bits =
            h.alloc_list_cons_slot(AnyValue::atom(1), crate::fz_value::EMPTY_LIST_BITS);
        let child_addr = crate::fz_value::list_addr_from_tagged(child_bits).expect("child addr");
        let child_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, child_addr).expect("child ref");
        let int_key_slot = 1u64;
        let atom_key_slot = 2u64;
        let int_any_value = 10u64;
        let int_key =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &int_key_slot).expect("int key");
        let atom_key = TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, &atom_key_slot)
            .expect("atom key");

        let map_ref = h
            .alloc_map_refs(&[(
                int_key,
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &int_any_value)
                    .expect("int value"),
            )])
            .expect("map ref");
        assert_eq!(
            h.read_map_value_ref(map_ref, int_key)
                .unwrap()
                .expect("int key")
                .load_int(),
            Ok(10)
        );
        assert_eq!(
            h.read_map_value_ref(map_ref, AnyValue::int(1))
                .unwrap()
                .expect("int key by slot")
                .load_int(),
            Ok(10)
        );

        let map_ref = h
            .map_put_ref(map_ref, atom_key, child_ref)
            .expect("put child");
        assert_eq!(
            h.read_map_value_ref(map_ref, atom_key)
                .unwrap()
                .expect("atom key")
                .list_addr(),
            Ok(child_addr)
        );
        assert_eq!(
            h.read_map_value_ref(map_ref, AnyValue::atom(2))
                .unwrap()
                .expect("atom key by slot")
                .list_addr(),
            Ok(child_addr)
        );

        let map_ref = h
            .map_put_int(map_ref, int_key, 11)
            .expect("replace int key");
        assert_eq!(
            h.read_map_value_ref(map_ref, int_key)
                .unwrap()
                .expect("int key")
                .load_int(),
            Ok(11)
        );
    }

    #[test]
    #[should_panic(
        expected = "map_put_ref value requires a heap/sentinel ref; use the typed scalar write path"
    )]
    fn map_put_ref_rejects_scalar_value() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let key_slot = 1u64;
        let any_value = 2u64;
        let key_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &key_slot).expect("key ref");
        let value_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &any_value).expect("value ref");
        let map_bits = h.alloc_map_slots(&[]);
        let map_addr = crate::fz_value::map_addr_from_tagged(map_bits).expect("map addr");
        let map_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Map, map_addr).expect("map ref");

        let _ = h.map_put_ref(map_ref, key_ref, value_ref);
    }

    #[test]
    fn tagged_ref_struct_and_closure_writes_store_scalar_and_heap_values() {
        let reg = empty_registry();
        let struct_schema = reg.borrow_mut().register(Schema::tuple_of_arity(2));
        let closure_schema = reg.borrow_mut().register(Schema::tuple_of_arity(0));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let child_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
        let child_addr = crate::fz_value::map_addr_from_tagged(child_bits).expect("child addr");
        let child_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Map, child_addr).expect("child ref");
        let scalar_slot = 99u64;
        let scalar_ref = TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, &scalar_slot)
            .expect("scalar ref");

        let struct_addr = h.alloc_struct(struct_schema);
        let struct_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Struct, struct_addr)
            .expect("struct ref");
        h.write_struct_field_ref(struct_ref, 0, scalar_ref)
            .expect("write scalar field");
        h.write_struct_field_ref(struct_ref, 8, child_ref)
            .expect("write heap field");
        assert_eq!(
            h.read_struct_field_ref(struct_ref, 0).unwrap().load_atom(),
            Ok(99)
        );
        assert_eq!(
            h.read_struct_field_ref(struct_ref, 8).unwrap().map_addr(),
            Ok(child_addr)
        );

        let closure_bits = h.alloc_closure_slots(closure_schema, 2, 0);
        let closure_addr =
            crate::fz_value::closure_addr_from_tagged(closure_bits).expect("closure addr");
        let closure_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Closure, closure_addr)
            .expect("closure ref");
        h.write_closure_capture_ref(closure_ref, 0, scalar_ref)
            .expect("write scalar capture");
        h.write_closure_capture_ref(closure_ref, 1, child_ref)
            .expect("write heap capture");
        assert_eq!(
            h.read_closure_capture_ref(closure_ref, 0)
                .unwrap()
                .load_atom(),
            Ok(99)
        );
        assert_eq!(
            h.read_closure_capture_ref(closure_ref, 1)
                .unwrap()
                .map_addr(),
            Ok(child_addr)
        );
    }

    #[test]
    fn tagged_ref_heap_writes_are_traced_by_gc() {
        let reg = empty_registry();
        let struct_schema = reg.borrow_mut().register(Schema::tuple_of_arity(1));
        let closure_schema = reg.borrow_mut().register(Schema::tuple_of_arity(0));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let key_slot = 1u64;
        let key_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &key_slot).expect("key ref");

        let child_map_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
        let child_map_addr =
            crate::fz_value::map_addr_from_tagged(child_map_bits).expect("child map addr");
        let child_map_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Map, child_map_addr)
            .expect("child map ref");
        let list_ref = h
            .alloc_list_cons_ref(child_map_ref, TaggedValueRef::empty_list())
            .expect("list ref");

        let child_list_bits =
            h.alloc_list_cons_slot(AnyValue::atom(3), crate::fz_value::EMPTY_LIST_BITS);
        let child_list_addr =
            crate::fz_value::list_addr_from_tagged(child_list_bits).expect("child list addr");
        let child_list_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, child_list_addr)
                .expect("child list ref");
        let map_ref = h
            .alloc_map_refs(&[(key_ref, child_list_ref)])
            .expect("map ref");

        let struct_addr = h.alloc_struct(struct_schema);
        let struct_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Struct, struct_addr)
            .expect("struct ref");
        h.write_struct_field_ref(struct_ref, 0, child_list_ref)
            .expect("write struct field");

        let closure_bits = h.alloc_closure_slots(closure_schema, 1, 0);
        let closure_addr =
            crate::fz_value::closure_addr_from_tagged(closure_bits).expect("closure addr");
        let closure_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Closure, closure_addr)
            .expect("closure ref");
        h.write_closure_capture_ref(closure_ref, 0, child_map_ref)
            .expect("write closure capture");

        let mut root = std::ptr::null_mut();
        let mut roots = [
            AnyValue::heap_ptr(list_ref.list_addr().unwrap(), ValueKind::LIST),
            AnyValue::heap_ptr(map_ref.map_addr().unwrap(), ValueKind::MAP),
            AnyValue::heap_ptr(struct_ref.struct_addr().unwrap(), ValueKind::STRUCT),
            AnyValue::heap_ptr(closure_ref.closure_addr().unwrap(), ValueKind::CLOSURE),
        ];

        h.gc_with_extra_root_slots(&mut root, &mut roots);

        let moved_list_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::List, roots[0].raw() as *const u8)
                .expect("moved list ref");
        let moved_list_head = h.read_list_head_ref(moved_list_ref).unwrap().map_addr();

        let moved_map_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Map, roots[1].raw() as *const u8)
                .expect("moved map ref");
        let moved_map_value = h
            .read_map_value_ref(moved_map_ref, key_ref)
            .unwrap()
            .expect("map value")
            .list_addr();

        let moved_struct_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Struct, roots[2].raw() as *const u8)
                .expect("moved struct ref");
        let moved_struct_field = h
            .read_struct_field_ref(moved_struct_ref, 0)
            .unwrap()
            .list_addr();

        let moved_closure_ref =
            TaggedValueRef::from_heap_object(TaggedValueTag::Closure, roots[3].raw() as *const u8)
                .expect("moved closure ref");
        let moved_closure_capture = h
            .read_closure_capture_ref(moved_closure_ref, 0)
            .unwrap()
            .map_addr();

        assert_eq!(moved_list_head, moved_closure_capture);
        assert_eq!(moved_map_value, moved_struct_field);
    }

    #[test]
    fn schema_registry_register_and_get() {
        let mut reg = SchemaRegistry::new();
        let id_a = reg.register(Schema {
            name: "A".into(),
            size: 0,
            fields: vec![],
        });
        let id_b = reg.register(Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor {
                    offset: 0,
                    kind: FieldKind::AnyValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::AnyValue,
                },
            ],
        });
        assert_eq!(id_a, 0);
        assert_eq!(id_b, 1);
        assert_eq!(reg.get(id_a).name, "A");
        assert_eq!(reg.get(id_b).name, "Pair");
    }

    /// fz-wu9 / fz-3ld.9 — every strict inline Bitstring allocation reserves
    /// at least one zero byte past its payload at offset
    /// `bytes_ptr + ceil(bit_len/8)`. Mirrors the SharedBin invariant covered
    /// by procbin.rs::shared_bin_alloc_has_trailing_nul.
    #[test]
    fn alloc_bitstring_inline_has_trailing_nul() {
        let mut h = Heap::new(1024, empty_registry());
        // Cover lengths around the 16-byte-alignment boundary so the
        // formerly-zero pad cases get exercised.
        for n in [0usize, 1, 7, 8, 9, 15, 16, 17, 24, 25] {
            let bytes: Vec<u8> = (0..n).map(|i| (i as u8) ^ 0xff).collect();
            let bit_len = (n as u64) * 8;
            let p = h.alloc_bitstring(&bytes, bit_len);
            unsafe {
                assert_eq!(crate::fz_value::bitstring_bit_len(p), bit_len);
                assert_eq!(
                    crate::fz_value::bitstring_size_for_bit_len(bit_len),
                    crate::fz_value::object_size(crate::fz_value::heap_object_word(
                        p,
                        crate::fz_value::ValueKind::BITSTRING
                    ))
                );
                let payload = crate::fz_value::bitstring_bytes_ptr(p);
                for (i, expected) in bytes.iter().enumerate().take(n) {
                    assert_eq!(
                        *payload.add(i),
                        *expected,
                        "payload byte {} at len {}",
                        i,
                        n
                    );
                }
                assert_eq!(
                    *payload.add(n),
                    0,
                    "trailing NUL at offset {} for payload len {}",
                    n,
                    n
                );
            }
        }
    }

    #[test]
    fn alloc_bumps_and_tracks() {
        let mut h = Heap::new(1024, empty_registry());
        let p = h.alloc_list_cons_slot(AnyValue::int(1), crate::fz_value::EMPTY_LIST);
        assert!(crate::fz_value::list_addr_from_tagged(p).is_some());
        assert_eq!(h.live_count(), 1);
        assert_eq!(h.bytes_used(), 16);
    }

    #[test]
    fn heap_pointers_are_16_aligned() {
        let mut h = Heap::new(1024, empty_registry());
        for _ in 0..10 {
            let p = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
            let addr = crate::fz_value::list_addr_from_tagged(p).expect("tagged list ptr");
            assert_eq!((addr as usize) & 15, 0);
        }
    }

    /// Bump overflow triggers a grow at the next size_class. Old block is
    /// abandoned; new block holds further allocations. `bytes_used`
    /// covers both. The next gc() returns both blocks to the pool.
    #[test]
    fn alloc_grows_to_next_size_class_on_overflow() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        // SIZE_TABLE[0] = 1024 bytes -> 64 headerless cons cells fit exactly.
        // Allocate 80 to force grow.
        let initial_block = h.block_start;
        let initial_class = h.size_class;
        for _ in 0..80 {
            let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        }
        assert_ne!(h.block_start, initial_block, "grow must move block_start");
        assert!(h.size_class > initial_class, "grow must bump size_class");
        assert_eq!(h.block_size, SIZE_TABLE[h.size_class as usize]);
        assert!(!h.abandoned_blocks.is_empty());
        assert_eq!(h.live_count(), 80);
    }

    /// `should_gc` flips once `bytes_used` crosses `gc_threshold_bytes`;
    /// `clear_should_gc_flag` resets it. The flag is independent of `gc()`
    /// itself — the scheduler reads it at park-time.
    #[test]
    fn pressure_flag_set_when_threshold_crossed() {
        let mut h = Heap::new(1024, empty_registry());
        h.gc_threshold_bytes = 64; // two cons cells.
        assert!(!h.should_gc());
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        assert!(!h.should_gc(), "1 cell at 16 bytes under 64");
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        assert!(!h.should_gc(), "2 cells at 32 bytes under 64");
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        assert!(h.should_gc(), "4 cells at 64 bytes at threshold");
        h.clear_should_gc_flag();
        assert!(!h.should_gc());
    }

    /// With a null root, Cheney recycles the arena: from-space is freed,
    /// to-space is a fresh empty block, live_count goes to zero.
    #[test]
    fn gc_with_null_root_recycles_arena() {
        let mut h = Heap::new(1024, empty_registry());
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
        assert_eq!(h.live_count(), 2);
        let mut root: *mut u8 = std::ptr::null_mut();
        h.gc(&mut root);
        assert_eq!(h.gc_run_count, 1);
        assert_eq!(h.live_count(), 0, "no root → nothing copied");
        assert_eq!(h.bytes_used(), 0, "to-space is empty");
        assert!(root.is_null());
    }

    /// A rooted list survives Cheney: every cell is copied to to-space,
    /// the root pointer is rewritten to the new head, and from-space is
    /// freed. Live count matches the chain length.
    #[test]
    fn gc_copies_rooted_list_and_rewrites_root() {
        let mut h = Heap::new(1024, empty_registry());
        // Build [1, 2, 3] — head ptr is n1.
        let n3 = alloc_int_list_cons(&mut h, 3, crate::fz_value::EMPTY_LIST);
        let n2 = alloc_int_list_cons(&mut h, 2, n3);
        let n1 = alloc_int_list_cons(&mut h, 1, n2);
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(n1)];
        let old_n1 = n1 as usize;
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        let root_ptr = crate::fz_value::list_addr_from_tagged(root_bits(roots[0])).unwrap();
        assert_ne!(
            root_ptr as usize, old_n1,
            "root should be rewritten to to-space"
        );
        assert_eq!(h.live_count(), 3, "all three cells copied");
        // Walk the new list and verify integers match.
        let mut cur = root_ptr as *mut ListCons;
        let mut sum = 0i64;
        let mut count = 0;
        while !cur.is_null() {
            let cons = unsafe { &*cur };
            sum += cons.head as i64;
            count += 1;
            cur = if cons.tail_addr() == 0 {
                std::ptr::null_mut()
            } else {
                cons.tail_addr() as *mut ListCons
            };
        }
        assert_eq!(count, 3);
        assert_eq!(sum, 6);
    }

    #[test]
    fn any_value_roots_forward_only_heap_values() {
        let mut h = Heap::new(1024, empty_registry());
        let list_bits = alloc_int_list_cons(&mut h, 1, crate::fz_value::EMPTY_LIST);
        let old_list = crate::fz_value::list_addr_from_tagged(list_bits).unwrap();
        let mut roots = [
            AnyValue::int(i64::MAX),
            AnyValue::float(1.5),
            AnyValue::decode_tagged_heap_bits(list_bits).unwrap(),
        ];
        let mut mailbox = std::collections::VecDeque::new();

        h.gc_any_value_roots_with_process_roots(&mut roots, &mut mailbox);

        assert_eq!(roots[0], AnyValue::int(i64::MAX));
        assert_eq!(roots[1], AnyValue::float(1.5));
        let new_list = roots[2].raw() as *mut u8;
        assert_ne!(new_list, old_list);
        let head = unsafe { (*(new_list as *const crate::fz_value::ListCons)).head_value() };
        assert_eq!(head.kind, ValueKind::INT);
        assert_eq!(head.raw as i64, 1);
    }

    #[test]
    fn tagged_ref_root_gc_forwards_heap_ref() {
        let mut h = Heap::new(1024, empty_registry());
        let list_bits = alloc_int_list_cons(&mut h, 1, crate::fz_value::EMPTY_LIST);
        let old_list = crate::fz_value::list_addr_from_tagged(list_bits).unwrap();
        let mut roots =
            [TaggedValueRef::from_heap_object(TaggedValueTag::List, old_list).expect("list ref")];
        let mut root = std::ptr::null_mut();

        let stats = h.gc_with_tagged_ref_roots(&mut root, &mut roots);

        let new_list = roots[0].list_addr().expect("forwarded list ref");
        assert_ne!(new_list, old_list);
        let head = unsafe { (*(new_list as *const crate::fz_value::ListCons)).head_value() };
        assert_eq!(head, AnyValue::int(1));
        assert_eq!(stats.root_heap_edges, 1);
        assert_eq!(stats.root_scalar_slots, 0);
    }

    #[test]
    fn tagged_ref_root_gc_copies_scalar_box_without_tracing_payload() {
        let mut h = Heap::new(1024, empty_registry());
        let decoy_bits = alloc_int_list_cons(&mut h, 99, crate::fz_value::EMPTY_LIST);
        let decoy_addr = crate::fz_value::list_addr_from_tagged(decoy_bits).unwrap();
        let scalar = h.alloc(8);
        unsafe {
            std::ptr::write(scalar as *mut u64, decoy_addr as u64);
        }
        let mut roots =
            [
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, scalar as *const u64)
                    .expect("scalar root ref"),
            ];
        let mut root = std::ptr::null_mut();

        let stats = h.gc_with_tagged_ref_roots(&mut root, &mut roots);

        assert_ne!(value_ref_addr(roots[0]), scalar);
        assert_eq!(roots[0].load_int().unwrap(), decoy_addr as i64);
        assert_eq!(stats.root_scalar_slots, 1);
        assert_eq!(stats.root_heap_edges, 0);
        assert_eq!(stats.copied_objects, 1);
        assert_eq!(stats.copied_bytes, 16);
    }

    #[test]
    fn tagged_ref_root_gc_preserves_static_scalar_ref() {
        static STATIC_INT: u64 = 42;
        let mut h = Heap::new(1024, empty_registry());
        let original = TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &STATIC_INT)
            .expect("static scalar ref");
        let mut roots = [original];
        let mut root = std::ptr::null_mut();

        let stats = h.gc_with_tagged_ref_roots(&mut root, &mut roots);

        assert_eq!(roots[0], original);
        assert_eq!(roots[0].load_int().unwrap(), 42);
        assert_eq!(stats.root_scalar_slots, 1);
        assert_eq!(stats.copied_objects, 0);
    }

    #[test]
    fn gc_stats_prove_scalar_list_head_is_copied_but_not_traced() {
        let mut h = Heap::new(1024, empty_registry());
        let decoy_bits = alloc_int_list_cons(&mut h, 99, crate::fz_value::EMPTY_LIST);
        let decoy_addr = crate::fz_value::list_addr_from_tagged(decoy_bits).unwrap();
        let live_bits = h.alloc_list_cons_slot(
            AnyValue::new(decoy_addr as u64, ValueKind::INT),
            crate::fz_value::EMPTY_LIST,
        );
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(live_bits)];

        let stats = h.gc_with_extra_root_slots(&mut root, &mut roots);

        assert_eq!(stats.copied_objects, 1);
        assert_eq!(stats.copied_bytes, 16);
        assert_eq!(stats.live_objects, 1);
        assert_eq!(stats.list_head_scalar_slots, 1);
        assert_eq!(stats.list_head_heap_edges, 0);
        assert_eq!(h.last_gc_stats, stats);
        let moved =
            crate::fz_value::list_addr_from_tagged(root_bits(roots[0])).expect("moved live list");
        let moved_head = unsafe { (*(moved as *const ListCons)).head_value() };
        assert_eq!(moved_head.kind(), ValueKind::INT);
        assert_eq!(moved_head.raw(), decoy_addr as u64);
    }

    #[test]
    fn gc_stats_count_struct_slots_by_layout_kind() {
        let reg = empty_registry();
        let schema_id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
        let mut h = Heap::new(1024, reg);
        let decoy_bits = alloc_int_list_cons(&mut h, 1, crate::fz_value::EMPTY_LIST);
        let decoy_addr = crate::fz_value::list_addr_from_tagged(decoy_bits).unwrap();
        let child_bits = alloc_int_list_cons(&mut h, 2, crate::fz_value::EMPTY_LIST);
        let child_addr = crate::fz_value::list_addr_from_tagged(child_bits).unwrap();
        let tuple = h.alloc_struct(schema_id);
        h.write_field_slot(tuple, 0, AnyValue::new(decoy_addr as u64, ValueKind::INT));
        h.write_field_slot(tuple, 8, AnyValue::heap_ptr(child_addr, ValueKind::LIST));
        let mut root =
            crate::fz_value::heap_object_word(tuple, crate::fz_value::ValueKind::STRUCT) as *mut u8;

        let stats = h.gc(&mut root);

        assert_eq!(stats.copied_objects, 2);
        assert_eq!(stats.struct_scalar_slots, 1);
        assert_eq!(stats.struct_heap_edges, 1);
        assert_eq!(stats.list_head_scalar_slots, 1);
        assert_eq!(h.live_count(), 2);
        let moved = crate::fz_value::struct_addr_from_tagged(root as u64).expect("moved struct");
        assert_eq!(h.read_field_slot(moved, 0).raw(), decoy_addr as u64);
        assert_ne!(h.read_field_slot(moved, 8).raw() as *mut u8, child_addr);
    }

    #[test]
    fn gc_stats_count_map_and_closure_slots_by_layout_kind() {
        let mut h = Heap::new(1024, empty_registry());
        let map_child_bits = alloc_int_list_cons(&mut h, 3, crate::fz_value::EMPTY_LIST);
        let map_child_addr = crate::fz_value::list_addr_from_tagged(map_child_bits).unwrap();
        let closure_child_bits = alloc_int_list_cons(&mut h, 4, crate::fz_value::EMPTY_LIST);
        let closure_child_addr =
            crate::fz_value::list_addr_from_tagged(closure_child_bits).unwrap();
        let map_bits = h.alloc_map_slots(&[(
            AnyValue::atom(7),
            AnyValue::heap_ptr(map_child_addr, ValueKind::LIST),
        )]);
        let closure_bits = h.alloc_closure(
            0,
            2,
            0,
            0,
            &[
                AnyValue::int(5),
                AnyValue::heap_ptr(closure_child_addr, ValueKind::LIST),
            ],
        );
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(map_bits), heap_root(closure_bits)];

        let stats = h.gc_with_extra_root_slots(&mut root, &mut roots);

        assert_eq!(stats.copied_objects, 4);
        assert_eq!(stats.root_heap_edges, 2);
        assert_eq!(stats.map_scalar_slots, 1);
        assert_eq!(stats.map_heap_edges, 1);
        assert_eq!(stats.closure_scalar_slots, 1);
        assert_eq!(stats.closure_heap_edges, 1);
        assert_eq!(stats.list_head_scalar_slots, 2);
        let moved_map = crate::fz_value::map_addr_from_tagged(root_bits(roots[0])).unwrap();
        let moved_closure = crate::fz_value::closure_addr_from_tagged(root_bits(roots[1])).unwrap();
        let (_, moved_map_value) = unsafe { crate::fz_value::map_entry(moved_map, 0) };
        let moved_capture = unsafe { crate::fz_value::closure_capture_value(moved_closure, 1) };
        assert_ne!(moved_map_value.raw() as *mut u8, map_child_addr);
        assert_ne!(moved_capture.raw() as *mut u8, closure_child_addr);
    }

    #[test]
    fn process_root_gc_forwards_runnable_closure_and_process_roots() {
        let mut h = Heap::new(1024, empty_registry());
        let captured_bits = alloc_int_list_cons(&mut h, 10, crate::fz_value::EMPTY_LIST);
        let mailbox_bits = alloc_int_list_cons(&mut h, 20, crate::fz_value::EMPTY_LIST);
        let closure_bits = h.alloc_closure_slots(0, 1, 0);
        let old_closure = crate::fz_value::closure_addr_from_tagged(closure_bits).unwrap();
        let old_capture = crate::fz_value::list_addr_from_tagged(captured_bits).unwrap();
        let old_mailbox = crate::fz_value::list_addr_from_tagged(mailbox_bits).unwrap();
        let closure_addr = crate::fz_value::closure_addr_from_tagged(closure_bits).unwrap();
        unsafe {
            crate::fz_value::closure_capture_set(
                closure_addr,
                0,
                AnyValue::decode_tagged_heap_bits(captured_bits).unwrap(),
            );
        }
        let mut root = closure_bits as *mut u8;
        let mut mailbox = std::collections::VecDeque::from([TaggedValueRef::from_heap_object(
            TaggedValueTag::List,
            crate::fz_value::list_addr_from_tagged(mailbox_bits).unwrap(),
        )
        .expect("mailbox list ref")]);
        h.gc_process_roots(&mut root, &mut mailbox);

        let new_closure = crate::fz_value::closure_addr_from_tagged(root as u64).unwrap();
        assert_ne!(new_closure, old_closure);
        let new_capture = unsafe { crate::fz_value::closure_capture_value(new_closure, 0) };
        assert_ne!(new_capture.raw() as *mut u8, old_capture);
        assert_ne!(mailbox[0].list_addr().unwrap(), old_mailbox);
    }

    /// Cheney drops unreachable objects: a cell allocated alongside the
    /// root chain but not pointed to by it is discarded. live_count
    /// shrinks to the chain length.
    #[test]
    fn gc_drops_unreachable_objects() {
        let mut h = Heap::new(1024, empty_registry());
        let _orphan = alloc_int_list_cons(&mut h, 99, crate::fz_value::EMPTY_LIST);
        let kept = alloc_int_list_cons(&mut h, 7, crate::fz_value::EMPTY_LIST);
        assert_eq!(h.live_count(), 2);
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(kept)];
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        assert_eq!(h.live_count(), 1, "orphan dropped, kept survives");
        let new_cons =
            crate::fz_value::list_addr_from_tagged(root_bits(roots[0])).unwrap() as *mut ListCons;
        let head = unsafe { (*new_cons).head };
        assert_eq!(head as i64, 7);
    }

    #[test]
    fn list_head_can_be_a_tagged_list_without_int_collision() {
        let mut h = Heap::new(1024, empty_registry());
        let child_bits = alloc_int_list_cons(&mut h, 7, crate::fz_value::EMPTY_LIST);
        let parent_bits =
            h.alloc_list_cons_slot(heap_root(child_bits), crate::fz_value::EMPTY_LIST);
        let parent = crate::fz_value::list_addr_from_tagged(parent_bits).expect("parent list ptr");
        let cons = unsafe { &*(parent as *const ListCons) };
        assert_eq!(cons.head_kind(), ValueKind::LIST);
        assert_eq!(
            cons.head,
            crate::fz_value::list_addr_from_tagged(child_bits).unwrap() as u64
        );
    }

    #[test]
    fn deep_copy_tagged_list_preserves_nested_list_head() {
        let mut src = Heap::new(1024, empty_registry());
        let mut dst = Heap::new(1024, empty_registry());
        let child_bits = alloc_int_list_cons(&mut src, 7, crate::fz_value::EMPTY_LIST);
        let parent_bits =
            src.alloc_list_cons_slot(heap_root(child_bits), crate::fz_value::EMPTY_LIST);
        let mut forwarding = std::collections::HashMap::new();

        let copied = deep_copy_slot(heap_root(parent_bits), &src, &mut dst, &mut forwarding);
        let copied_parent = crate::fz_value::list_addr_from_tagged(tagged_bits(copied))
            .expect("copied parent list ptr");
        let parent = unsafe { &*(copied_parent as *const ListCons) };
        assert_eq!(parent.head_kind(), ValueKind::LIST);

        let copied_child = parent.head as *mut u8;
        assert_ne!(
            copied_child,
            crate::fz_value::list_addr_from_tagged(child_bits).unwrap()
        );
        let child = unsafe { &*(copied_child as *const ListCons) };
        assert_eq!(child.head_kind(), ValueKind::INT);
        assert_eq!(child.head as i64, 7);
        assert_eq!(child.tail_bits(), crate::fz_value::EMPTY_LIST);
    }

    #[test]
    #[serial_test::serial]
    fn deep_copy_strict_heap_kinds_dispatch_from_pointer_tags() {
        use crate::resource::{ResourceHandle, ResourceStub, alloc_resource};

        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
        let mut src = Heap::new(SIZE_TABLE[0], reg.clone());
        let mut dst = Heap::new(SIZE_TABLE[0], reg);

        let list_bits = alloc_int_list_cons(&mut src, 7, crate::fz_value::EMPTY_LIST);

        let struct_p = src.alloc_struct(pair_id);
        src.write_field_slot(struct_p, 0, heap_root(list_bits));
        src.write_field_slot(struct_p, 8, AnyValue::int(11));

        let closure_bits = src.alloc_closure(pair_id, 1, 0, 0x1234, &[heap_root(list_bits)]);

        let bitstring_p = src.alloc_bitstring(b"abc", 24);

        let procbin = alloc_procbin(&mut src, SharedBinHandle::from_bytes(&[1, 2, 3, 4], 32));

        let resource_closure = heap_root(closure_bits);
        let resource = alloc_resource(
            &mut src,
            ResourceHandle::new(0xfeed, crate::resource::fz_resource_destructor_noop),
            resource_closure,
        );

        let entries = [
            (
                AnyValue::new(1, ValueKind::ATOM),
                AnyValue::heap_ptr(
                    crate::fz_value::list_addr_from_tagged(list_bits).unwrap(),
                    ValueKind::LIST,
                ),
            ),
            (
                AnyValue::new(2, ValueKind::ATOM),
                AnyValue::heap_ptr(struct_p, ValueKind::STRUCT),
            ),
            (
                AnyValue::new(3, ValueKind::ATOM),
                AnyValue::heap_ptr(
                    crate::fz_value::closure_addr_from_tagged(closure_bits).unwrap(),
                    ValueKind::CLOSURE,
                ),
            ),
            (
                AnyValue::new(4, ValueKind::ATOM),
                AnyValue::heap_ptr(bitstring_p, ValueKind::BITSTRING),
            ),
            (
                AnyValue::new(5, ValueKind::ATOM),
                AnyValue::heap_ptr(procbin.as_raw(), ValueKind::PROCBIN),
            ),
            (
                AnyValue::new(7, ValueKind::ATOM),
                AnyValue::heap_ptr(resource.as_raw(), ValueKind::RESOURCE),
            ),
        ];
        let map_bits = src.alloc_map_slots(&entries);
        let mut forwarding = std::collections::HashMap::new();

        let copied = deep_copy_slot(heap_root(map_bits), &src, &mut dst, &mut forwarding);
        let copied_map = crate::fz_value::map_addr_from_tagged(tagged_bits(copied)).unwrap();

        let copied_values = (0..entries.len())
            .map(|i| unsafe { crate::fz_value::map_entry(copied_map as *const u8, i).1 })
            .collect::<Vec<_>>();
        for (i, value) in copied_values.iter().enumerate() {
            assert_eq!(value.kind, entries[i].1.kind);
            assert_ne!(
                value.raw & !crate::fz_value::TAG_MASK,
                entries[i].1.raw & !crate::fz_value::TAG_MASK,
                "heap entry {} moved/copied",
                i
            );
        }

        let copied_struct = copied_values[1].raw as *mut u8;
        let copied_struct_list = dst.read_field_slot(copied_struct, 0);
        assert_eq!(copied_struct_list.kind(), ValueKind::LIST);
        assert!(!copied_struct_list.heap_addr().unwrap().is_null());

        let copied_closure = copied_values[2].raw as *mut u8;
        let copied_capture =
            unsafe { crate::fz_value::closure_capture_value(copied_closure as *const u8, 0) };
        assert!(crate::fz_value::list_addr_from_tagged(tagged_bits(copied_capture)).is_some());

        let copied_resource = unsafe { ResourceStub::from_raw(copied_values[5].raw as *mut u8) };
        assert_eq!(copied_resource.payload(), 0xfeed);
    }

    /// Acceptance (fz-siu.10 / §6.6): spawn under load shows no per-spawn
    /// malloc after warm-up. After dropping a Heap, its block goes to the
    /// pool; the next Heap::new of the same size_class pulls from the
    /// pool, no malloc required. Repeating spawn+drop with a fixed pool
    /// occupancy proves the cache is doing its job.
    #[test]
    fn pool_caches_blocks_across_heap_drops() {
        pool_drain_for_test();
        assert_eq!(pool_total_cached_blocks(), 0, "test starts with empty pool");

        // Warm-up: create + drop one Heap. Drop returns the block.
        {
            let _h = Heap::new(SIZE_TABLE[0], empty_registry());
        }
        assert_eq!(pool_total_cached_blocks(), 1, "first drop fills the pool");

        // Subsequent spawn-equivalents (Heap::new + drop) must not increase
        // the pool occupancy — they pull from the cache, return the same
        // block. The acceptance "no per-spawn malloc": occupancy stays at
        // 1 across N create+drop cycles.
        for _ in 0..50 {
            let _h = Heap::new(SIZE_TABLE[0], empty_registry());
            assert_eq!(pool_total_cached_blocks(), 0, "alloc drained the cache");
            // _h dropped here → returns the block to the pool.
        }
        assert_eq!(
            pool_total_cached_blocks(),
            1,
            "pool stayed at 1 cached block"
        );

        pool_drain_for_test();
    }

    #[test]
    fn size_table_first_entry_is_1k() {
        assert_eq!(SIZE_TABLE[0], 1024);
    }

    #[test]
    fn size_table_is_monotonic_and_16_aligned() {
        for i in 1..SIZE_TABLE.len() {
            assert!(
                SIZE_TABLE[i] > SIZE_TABLE[i - 1],
                "non-monotonic at {}: {} <= {}",
                i,
                SIZE_TABLE[i],
                SIZE_TABLE[i - 1]
            );
            assert_eq!(
                SIZE_TABLE[i] % 16,
                0,
                "entry {} ({}) not 16-aligned",
                i,
                SIZE_TABLE[i]
            );
        }
    }

    #[test]
    fn size_table_tail_is_geometric_ish() {
        // Tail entries grow ~×1.2 (after the Fibonacci low end). Sample
        // index 20 → 21: ratio in [1.18, 1.23].
        let ratio = SIZE_TABLE[21] as f64 / SIZE_TABLE[20] as f64;
        assert!(
            ratio > 1.18 && ratio < 1.23,
            "tail ratio out of expected range: {}",
            ratio
        );
    }

    #[test]
    fn pick_size_class_smallest_fit() {
        assert_eq!(pick_size_class(0), 0);
        assert_eq!(pick_size_class(1024), 0);
        assert_eq!(pick_size_class(1025), 1);
        assert_eq!(pick_size_class(SIZE_TABLE[5]), 5);
        assert_eq!(pick_size_class(SIZE_TABLE[5] + 1), 6);
    }

    #[test]
    fn pick_size_class_clamps_on_tail_no_panic() {
        // Far past the last entry — must clamp, not panic.
        let class = pick_size_class(usize::MAX);
        assert_eq!(class as usize, SIZE_TABLE.len() - 1);
    }

    /// Acceptance: under increasing load, gc picks ascending size_class
    /// values. Build progressively longer rooted chains; each gc tracks
    /// to a higher class as live_bytes grows past each SIZE_TABLE step.
    #[test]
    fn gc_picks_ascending_size_class_as_live_grows() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let mut last_class: i32 = -1;
        // Build chains of growing length and gc each time. Working set
        // doubles each iteration to ensure size_class climbs.
        for power in 6..=12 {
            let len = 1usize << power; // 64, 128, ..., 4096 cells
            // Build a chain of `len` cons cells, rooted at head.
            let mut tail = crate::fz_value::EMPTY_LIST;
            for i in 0..len {
                tail = alloc_int_list_cons(&mut h, i as i64, tail);
            }
            let mut root = std::ptr::null_mut();
            let mut roots = [heap_root(tail)];
            h.gc_with_extra_root_slots(&mut root, &mut roots);
            let live_bytes = len * 16;
            let expected_min = pick_size_class(live_bytes); // without slack
            assert!(
                h.size_class >= expected_min,
                "size_class {} should fit live_bytes {}",
                h.size_class,
                live_bytes
            );
            assert!(
                (h.size_class as i32) > last_class || last_class < 0,
                "size_class did not climb: prev={}, now={}",
                last_class,
                h.size_class
            );
            last_class = h.size_class as i32;
            // Drop the root so next iteration starts fresh.
            let _ = root; // reachable until here
        }
    }

    /// last_gc_live_bytes is set correctly after GC and used for to-space sizing.
    /// First GC uses bytes_used() as upper bound; subsequent GCs use
    /// last_gc_live_bytes * 2 (50% post-GC target occupancy).
    #[test]
    fn gc_updates_last_gc_live_bytes() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        assert_eq!(h.last_gc_live_bytes, 0, "zero before first gc");
        // Build [1, 2, 3].
        let n3 = alloc_int_list_cons(&mut h, 3, crate::fz_value::EMPTY_LIST);
        let n2 = alloc_int_list_cons(&mut h, 2, n3);
        let n1 = alloc_int_list_cons(&mut h, 1, n2);
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(n1)];
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        assert_eq!(h.last_gc_live_bytes, 3 * 16, "three cons cells = 48 bytes");

        // Second GC with same live set: to-space sizing = 48 * 2 = 96,
        // clamped to SIZE_TABLE[0]. live bytes stay the same.
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        assert_eq!(h.last_gc_live_bytes, 3 * 16, "live bytes unchanged");
        assert_eq!(h.size_class, 0, "tiny live set stays at smallest class");
    }

    /// Watermark is set to 75% of block. After alloc crossing watermark,
    /// FZ_SHOULD_YIELD is set; it can be cleared externally.
    #[test]
    fn watermark_is_75_percent_of_block() {
        crate::yield_flag::clear();
        let h = Heap::new(SIZE_TABLE[0], empty_registry());
        let expected = unsafe { h.block_start.add(SIZE_TABLE[0] * 3 / 4) };
        assert_eq!(h.gc_watermark, expected);
        crate::yield_flag::clear(); // cleanup
    }

    /// Large struct (200-byte payload, well past the old 64-byte cap)
    /// allocates without panic; grow promotes to a larger size_class as needed.
    #[test]
    fn alloc_large_struct_succeeds_and_grows_size_class() {
        let reg = empty_registry();
        // Build a schema whose payload is 200 bytes of typed value fields.
        let n_fields = 200 / 8; // 25 any values
        let mut fields = Vec::with_capacity(n_fields);
        for i in 0..n_fields {
            fields.push(FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::AnyValue,
            });
        }
        let id = reg.borrow_mut().register(Schema {
            name: "Big".into(),
            size: (n_fields * 8) as u32,
            fields,
        });
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let p = h.alloc_struct(id);
        unsafe {
            assert_eq!(crate::fz_value::struct_schema_id(p), id);
            // total = 8 + 200 = 208, rounded to 208.
            assert_eq!(crate::fz_value::struct_size_for_payload(200), 208);
        }
    }

    #[test]
    fn struct_layout_size_correct() {
        let reg = empty_registry();
        let id = reg.borrow_mut().register(Schema::tuple_of_arity(3));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let before = h.bytes_used();

        let p = h.alloc_struct(id);

        assert_eq!(Schema::tuple_of_arity(3).allocation_payload_size(), 32);
        assert_eq!(h.bytes_used() - before, 48);
        unsafe {
            assert_eq!(crate::fz_value::struct_schema_id(p), id);
            assert_eq!(crate::fz_value::struct_flags(p), 0);
        }
    }

    #[test]
    fn struct_field_read_at_new_offset() {
        let reg = empty_registry();
        let id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let p = h.alloc_struct(id);

        h.write_field_slot(p, 0, AnyValue::int(11));
        h.write_field_slot(p, 8, AnyValue::int(22));

        unsafe {
            assert_eq!(std::ptr::read(p.add(8) as *const u64), 11);
            assert_eq!(std::ptr::read(p.add(16) as *const u64), 22);
            assert_eq!(std::ptr::read(p.add(24) as *const u8), ValueKind::INT.tag());
            assert_eq!(std::ptr::read(p.add(25) as *const u8), ValueKind::INT.tag());
        }
        assert_eq!(h.read_field_slot(p, 0), AnyValue::int(11));
        assert_eq!(h.read_field_slot(p, 8), AnyValue::int(22));
    }

    #[test]
    fn struct_forwarding_marker_through_gc() {
        let reg = empty_registry();
        let id = reg.borrow_mut().register(Schema::tuple_of_arity(1));
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let p = h.alloc_struct(id);
        let old_addr = p;
        h.write_field_slot(p, 0, AnyValue::int(9));
        let mut root =
            crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::STRUCT) as *mut u8;

        h.gc(&mut root);

        let new_p = crate::fz_value::struct_addr_from_tagged(root as u64).expect("forwarded root");
        assert_ne!(new_p as *const u8, old_addr);
        assert_eq!(h.read_field_slot(new_p, 0), AnyValue::int(9));
        assert_eq!(
            crate::fz_value::is_forwarded(old_addr),
            Some(new_p as *const u8)
        );
    }

    /// Map with 5 entries exercises both alloc and the Cheney trace path
    /// (Map walks each entry's typed children).
    #[test]
    fn alloc_large_map_round_trips_through_gc() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let entries: Vec<(AnyValue, AnyValue)> = (0..5)
            .map(|i| {
                (
                    AnyValue::new(i as u64, ValueKind::INT),
                    AnyValue::new((i * 10) as u64, ValueKind::INT),
                )
            })
            .collect();
        let bits = h.alloc_map_slots(&entries);
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(bits)];
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        assert_eq!(h.live_count(), 1, "map survives GC");
        let new_p = crate::fz_value::map_addr_from_tagged(root_bits(roots[0])).unwrap();
        unsafe {
            let count = crate::fz_value::map_count(new_p as *const u8);
            assert_eq!(count, 5);
        }
    }

    #[test]
    fn map_layout_size_correct() {
        for count in [0usize, 1, 2, 3, 7, 8, 9] {
            let entries: Vec<(AnyValue, AnyValue)> = (0..count)
                .map(|i| {
                    (
                        AnyValue::new(i as u64, ValueKind::INT),
                        AnyValue::new((i + 10) as u64, ValueKind::INT),
                    )
                })
                .collect();
            let mut h = Heap::new(1024, empty_registry());
            let bits = h.alloc_map_slots(&entries);
            assert_eq!(
                crate::fz_value::object_size(bits),
                crate::fz_value::map_size_for_count(count)
            );
        }
    }

    #[test]
    fn closure_layout_zero_captures() {
        let mut h = Heap::new(1024, empty_registry());
        let bits = h.alloc_closure(42, 0, 2, 0xfeed_beef, &[]);
        assert_eq!(
            bits & crate::fz_value::TAG_MASK,
            crate::fz_value::TAG_CLOSURE
        );
        assert_eq!(crate::fz_value::object_size(bits), 16);
        let p = crate::fz_value::closure_addr_from_tagged(bits).unwrap();
        assert_eq!(unsafe { crate::fz_value::closure_schema_id(p) }, 42);
        assert_eq!(unsafe { crate::fz_value::closure_halt_kind(p) }, 2);
        assert_eq!(unsafe { crate::fz_value::closure_fn_ptr(p) }, 0xfeed_beef);
    }

    #[test]
    fn closure_layout_n_captures() {
        let mut h = Heap::new(1024, empty_registry());
        let captures = [AnyValue::int(10), AnyValue::int(20)];
        let bits = h.alloc_closure(7, captures.len(), 1, 0x1234, &captures);
        assert_eq!(crate::fz_value::object_size(bits), 48);
        let p = crate::fz_value::closure_addr_from_tagged(bits).unwrap();
        assert_eq!(unsafe { crate::fz_value::closure_captured_count(p) }, 2);
        for (i, expected) in captures.iter().enumerate() {
            let got = unsafe { crate::fz_value::closure_capture_value(p, i) };
            assert_eq!(got, *expected);
        }
    }

    #[test]
    fn closure_forwarding_marker() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let bits = h.alloc_closure(12, 0, 0, 0x7777, &[]);
        let old = crate::fz_value::closure_addr_from_tagged(bits).unwrap();
        let mut root = bits as *mut u8;
        h.gc(&mut root);
        let new_bits = root as u64;
        let new_p = crate::fz_value::closure_addr_from_tagged(new_bits).unwrap();
        assert_ne!(old, new_p);
        assert_eq!(
            unsafe { crate::fz_value::closure_schema_id(new_p as *const u8) },
            12
        );
        assert_eq!(
            unsafe { crate::fz_value::closure_fn_ptr(new_p as *const u8) },
            0x7777
        );
        let marker = unsafe { std::ptr::read(old as *const u64) };
        assert_eq!(marker & crate::fz_value::TAG_MASK, crate::fz_value::TAG_FWD);
        let confirm = unsafe { std::ptr::read(old.add(8) as *const u64) };
        assert_eq!(confirm, crate::fz_value::TAG_FWD);
    }

    #[test]
    fn strict_heap_decoder_accepts_static_closure_pointer() {
        let mut storage = crate::process::AlignedClosureStorage::zeroed();
        let bits = crate::fz_value::heap_object_word(
            storage.as_ptr() as *const u8,
            crate::fz_value::ValueKind::CLOSURE,
        );

        let value = heap_root(bits);

        assert_eq!(value.kind(), ValueKind::CLOSURE);
        assert_eq!(value.raw(), storage.as_ptr() as u64);
    }

    #[test]
    fn closure_fn_id_preserved_in_schema_id() {
        let mut h = Heap::new(1024, empty_registry());
        let bits = h.alloc_closure_slots(99, 0, 0);
        let p = crate::fz_value::closure_addr_from_tagged(bits).unwrap();
        assert_eq!(unsafe { crate::fz_value::closure_schema_id(p) }, 99);
    }

    #[test]
    fn map_packed_tags_round_trip() {
        let cases = [1usize, 2, 3, 7, 8, 9];
        for count in cases {
            let entries: Vec<(AnyValue, AnyValue)> = (0..count)
                .map(|i| {
                    let key_kind = if i % 2 == 0 {
                        ValueKind::ATOM
                    } else {
                        ValueKind::INT
                    };
                    let value_kind = if i % 3 == 0 {
                        ValueKind::FLOAT
                    } else {
                        ValueKind::INT
                    };
                    (
                        AnyValue::new(i as u64, key_kind),
                        AnyValue::new((100 + i) as u64, value_kind),
                    )
                })
                .collect();
            let mut h = Heap::new(1024, empty_registry());
            let bits = h.alloc_map_slots(&entries);
            let p = crate::fz_value::map_addr_from_tagged(bits).unwrap();
            for (i, expected) in entries.iter().enumerate() {
                let got = unsafe { crate::fz_value::map_entry(p, i) };
                assert_eq!(got, *expected);
            }
        }
    }

    #[test]
    fn map_float_value_is_unboxed_raw_bits() {
        let mut h = Heap::new(1024, empty_registry());
        let f = std::f64::consts::PI;
        let bits = h.alloc_map_slots(&[(
            AnyValue::new(0, ValueKind::ATOM),
            AnyValue::new(f.to_bits(), ValueKind::FLOAT),
        )]);
        let p = crate::fz_value::map_addr_from_tagged(bits).unwrap();
        let (_, value) = unsafe { crate::fz_value::map_entry(p, 0) };
        assert_eq!(value.kind, ValueKind::FLOAT);
        assert_eq!(value.raw, f.to_bits());
        assert_eq!(h.live_count(), 1, "map allocation should not box the float");
    }

    #[test]
    fn map_int_value_stores_full_i64_range() {
        let mut h = Heap::new(1024, empty_registry());
        let value = i64::MIN;
        let bits = h.alloc_map_slots(&[(
            AnyValue::new(1, ValueKind::ATOM),
            AnyValue::new(value as u64, ValueKind::INT),
        )]);
        let p = crate::fz_value::map_addr_from_tagged(bits).unwrap();
        let (_, got) = unsafe { crate::fz_value::map_entry(p, 0) };
        assert_eq!(got.kind, ValueKind::INT);
        assert_eq!(got.raw as i64, value);
    }

    #[test]
    fn deep_copy_tagged_map_preserves_nested_list_value() {
        let mut src = Heap::new(1024, empty_registry());
        let mut dst = Heap::new(1024, empty_registry());
        let child_bits = alloc_int_list_cons(&mut src, 7, crate::fz_value::EMPTY_LIST);
        let child_ptr = crate::fz_value::list_addr_from_tagged(child_bits).unwrap();
        let map_bits = src.alloc_map_slots(&[(
            AnyValue::new(1, ValueKind::ATOM),
            AnyValue::heap_ptr(child_ptr, ValueKind::LIST),
        )]);
        let mut forwarding = std::collections::HashMap::new();
        let copied = deep_copy_slot(heap_root(map_bits), &src, &mut dst, &mut forwarding);
        let copied_map = crate::fz_value::map_addr_from_tagged(tagged_bits(copied)).unwrap();
        let (_, value) = unsafe { crate::fz_value::map_entry(copied_map as *const u8, 0) };
        assert_eq!(value.kind, ValueKind::LIST);
        assert_ne!(value.raw as *mut u8, child_ptr);
        let copied_list = unsafe { &*(value.raw as *const ListCons) };
        assert_eq!(copied_list.head_kind(), ValueKind::INT);
        assert_eq!(copied_list.head as i64, 7);
    }

    #[test]
    fn gc_map_count_twelve_does_not_collide_with_forwarding_tag() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let entries: Vec<(AnyValue, AnyValue)> = (0..12)
            .map(|i| {
                (
                    AnyValue::new(i as u64, ValueKind::INT),
                    AnyValue::new((i * 2) as u64, ValueKind::INT),
                )
            })
            .collect();
        let bits = h.alloc_map_slots(&entries);
        let old = crate::fz_value::map_addr_from_tagged(bits).unwrap();
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(bits)];
        h.gc_with_extra_root_slots(&mut root, &mut roots);
        let new_p = crate::fz_value::map_addr_from_tagged(root_bits(roots[0])).unwrap();
        assert_ne!(new_p, old);
        assert_eq!(
            unsafe { crate::fz_value::map_count(new_p as *const u8) },
            12
        );
    }

    /// Acceptance: ≥10 GC cycles with the same small live working set
    /// keep the arena bounded. Block size may grow once to fit per-cycle
    /// garbage but does not increase without bound; no abandoned blocks
    /// remain post-GC; live_count stays at the rooted chain length.
    /// (§6.4 / fz-siu.8 acceptance.)
    #[test]
    fn gc_keeps_arena_bounded_across_many_cycles() {
        let mut h = Heap::new(1024, empty_registry());
        // Rooted [1, 2, 3] — the live working set across every cycle.
        let n3 = alloc_int_list_cons(&mut h, 3, crate::fz_value::EMPTY_LIST);
        let n2 = alloc_int_list_cons(&mut h, 2, n3);
        let n1 = alloc_int_list_cons(&mut h, 1, n2);
        let mut root = std::ptr::null_mut();
        let mut roots = [heap_root(n1)];
        for _ in 0..15 {
            // Per-cycle garbage that overflows the 1 KiB initial block,
            // forcing grow → abandon → reclaim at next gc().
            for _ in 0..100 {
                let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), crate::fz_value::EMPTY_LIST);
            }
            h.gc_with_extra_root_slots(&mut root, &mut roots);
            // Post-gc invariants.
            assert_eq!(h.live_count(), 3, "rooted chain survives");
            assert_eq!(h.abandoned_blocks.len(), 0, "abandoned blocks reclaimed");
        }
        // After the working-set-fits-in-block point, block_size stays put.
        // Generous upper bound: 32× initial guards against runaway growth.
        assert!(
            h.block_size <= 1024 * 32,
            "block_size grew unboundedly: {}",
            h.block_size
        );
    }

    /// Cycle (a.0 = b, b.0 = a) doesn't loop the collector: forwarding
    /// pointers in from-space short-circuit revisits.
    #[test]
    fn gc_handles_cycle_via_forwarding() {
        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor {
                    offset: 0,
                    kind: FieldKind::AnyValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::AnyValue,
                },
            ],
        });
        let mut h = Heap::new(1024, reg.clone());
        let a = h.alloc_struct(pair_id);
        let b = h.alloc_struct(pair_id);
        h.write_field_slot(a, 0, AnyValue::heap_ptr(b, ValueKind::STRUCT));
        h.write_field_slot(a, 8, AnyValue::nil_atom());
        h.write_field_slot(b, 0, AnyValue::heap_ptr(a, ValueKind::STRUCT));
        h.write_field_slot(b, 8, AnyValue::nil_atom());
        let mut root =
            crate::fz_value::heap_object_word(a as *const u8, crate::fz_value::ValueKind::STRUCT)
                as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.live_count(), 2);
    }

    // ===== fz-q8d.1 — ProcBin + intrusive MSO + post-Cheney sweep =========

    use crate::procbin::{
        ProcBin, SharedBinHandle, alloc_procbin, bitstring_bit_len, bitstring_byte_ptr, live_count,
    };

    /// Walk the heap's MSO chain and return the contained tagged pointers
    /// in chain order (head → tail).
    fn mso_chain(h: &Heap) -> Vec<u64> {
        let mut out = Vec::new();
        let mut cur_bits = h.mso_head;
        while cur_bits != 0 {
            let addr = (cur_bits & !crate::fz_value::TAG_MASK) as *mut u8;
            let next = match cur_bits & crate::fz_value::TAG_MASK {
                crate::fz_value::TAG_PROCBIN => unsafe { ProcBin::from_raw(addr).mso_next() },
                crate::fz_value::TAG_RESOURCE => unsafe {
                    crate::resource::ResourceStub::from_raw(addr).mso_next()
                },
                tag => panic!("unexpected MSO tag {tag:#x}"),
            };
            out.push(cur_bits);
            cur_bits = next;
        }
        out
    }

    /// `alloc_procbin` writes a strict 16-byte ProcBin and pushes onto the chain.
    #[test]
    #[serial_test::serial]
    fn alloc_procbin_pushes_into_mso_chain_with_strict_layout() {
        let baseline = live_count();
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let pb = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1, 2, 3, 4], 32));
            let tagged = crate::fz_value::heap_object_word(
                pb.as_raw() as *const u8,
                crate::fz_value::ValueKind::PROCBIN,
            );
            assert_eq!(
                tagged & crate::fz_value::TAG_MASK,
                crate::fz_value::TAG_PROCBIN
            );
            assert_eq!(crate::fz_value::object_size(tagged), 16);
            assert_eq!(mso_chain(&h), vec![tagged]);
        }
        assert_eq!(live_count(), baseline);
    }

    /// A rooted ProcBin survives Cheney: chain rewritten to to-space copy.
    #[test]
    #[serial_test::serial]
    fn procbin_survives_gc_via_mso_rewrite() {
        let baseline = live_count();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let pb = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[0xaa; 8], 64));
        let shared_p = pb.shared_raw();
        let from_pb = pb.as_raw();
        let mut root = crate::fz_value::heap_object_word(
            from_pb as *const u8,
            crate::fz_value::ValueKind::PROCBIN,
        ) as *mut u8;
        assert_eq!(live_count(), baseline + 1);
        h.gc(&mut root);
        let new_pb = crate::fz_value::procbin_addr_from_tagged(root as u64).unwrap();
        assert_ne!(new_pb, from_pb, "ProcBin should have moved to to-space");
        assert_eq!(
            mso_chain(&h),
            vec![crate::fz_value::heap_object_word(
                new_pb as *const u8,
                crate::fz_value::ValueKind::PROCBIN
            )],
            "chain rewritten"
        );
        assert_eq!(live_count(), baseline + 1, "shared bin unchanged across GC");
        let pb_to = unsafe { ProcBin::from_raw(new_pb) };
        assert_eq!(pb_to.shared_raw(), shared_p);
        drop(h);
        assert_eq!(live_count(), baseline);
    }

    /// Unrooted ProcBin: MSO sweep releases its SharedBin.
    #[test]
    #[serial_test::serial]
    fn procbin_dies_in_gc_and_sweep_releases_shared_bin() {
        let baseline = live_count();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[0x55; 16], 128));
        assert_eq!(live_count(), baseline + 1);
        let mut root: *mut u8 = std::ptr::null_mut();
        h.gc(&mut root);
        assert_eq!(h.mso_head, 0, "dead ProcBin swept from MSO");
        assert_eq!(live_count(), baseline);
    }

    /// Mixed live/dead ProcBins: sweep must read the next link from
    /// from-space while reading the survivor's shared_ptr from to-space.
    #[test]
    #[serial_test::serial]
    fn procbin_mso_chain_intact_through_gc_partial_survival() {
        let baseline = live_count();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let _dead_tail = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1], 8));
        let live = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[2], 8));
        let _dead_head = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[3], 8));
        let live_from = live.as_raw();
        let live_shared = live.shared_raw();
        assert_eq!(mso_chain(&h).len(), 3);
        assert_eq!(live_count(), baseline + 3);

        let mut root = crate::fz_value::heap_object_word(
            live_from as *const u8,
            crate::fz_value::ValueKind::PROCBIN,
        ) as *mut u8;
        h.gc(&mut root);

        let live_to = crate::fz_value::procbin_addr_from_tagged(root as u64).unwrap();
        assert_ne!(live_to, live_from);
        assert_eq!(
            mso_chain(&h),
            vec![crate::fz_value::heap_object_word(
                live_to as *const u8,
                crate::fz_value::ValueKind::PROCBIN
            )]
        );
        assert_eq!(
            unsafe { ProcBin::from_raw(live_to).shared_raw() },
            live_shared
        );
        assert_eq!(live_count(), baseline + 1);
        drop(h);
        assert_eq!(live_count(), baseline);
    }

    /// Heap::drop releases every chain entry's shared_ptr.
    #[test]
    #[serial_test::serial]
    fn heap_drop_releases_all_mso_shared_refs() {
        let baseline = live_count();
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1, 2], 16));
            let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[3, 4, 5], 24));
            assert_eq!(live_count(), baseline + 2);
            assert_eq!(mso_chain(&h).len(), 2);
        }
        assert_eq!(live_count(), baseline);
    }

    // ===== deep_copy_slot handles ProcBin via retain =====================

    /// Cross-heap deep_copy of a ProcBin shares the SharedBin.
    #[test]
    #[serial_test::serial]
    fn deep_copy_procbin_shares_via_retain() {
        let baseline = live_count();
        let mut src = Heap::new(SIZE_TABLE[0], empty_registry());
        let mut dst = Heap::new(SIZE_TABLE[0], empty_registry());
        let src_pb = alloc_procbin(&mut src, SharedBinHandle::from_bytes(&[7, 8, 9, 10], 32));
        let shared_p = src_pb.shared_raw();
        let mut fwd = std::collections::HashMap::new();
        let copied = deep_copy_slot(
            AnyValue::heap_ptr(src_pb.as_raw(), ValueKind::PROCBIN),
            &src,
            &mut dst,
            &mut fwd,
        );
        let dst_p = crate::fz_value::procbin_addr_from_tagged(tagged_bits(copied)).unwrap();
        let dst_pb = unsafe { ProcBin::from_raw(dst_p) };
        assert_ne!(dst_p, src_pb.as_raw());
        assert_eq!(dst_pb.shared_raw(), shared_p);
        assert_eq!(mso_chain(&src).len(), 1);
        assert_eq!(mso_chain(&dst).len(), 1);
        unsafe {
            assert_eq!((*shared_p).refcount.load(crate::sync::Ordering::Relaxed), 2);
        }
        assert_eq!(live_count(), baseline + 1);
        drop(dst);
        unsafe {
            assert_eq!((*shared_p).refcount.load(crate::sync::Ordering::Relaxed), 1);
        }
        assert_eq!(mso_chain(&src).len(), 1);
        drop(src);
        assert_eq!(live_count(), baseline);
    }

    /// Shared structure: a tuple containing the same ProcBin twice
    /// deep-copies to a single retained reference (refcount 2, not 3).
    #[test]
    #[serial_test::serial]
    fn deep_copy_procbin_dedup_via_forwarding_map() {
        let baseline = live_count();
        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor {
                    offset: 0,
                    kind: FieldKind::AnyValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::AnyValue,
                },
            ],
        });
        let mut src = Heap::new(SIZE_TABLE[0], reg.clone());
        let mut dst = Heap::new(SIZE_TABLE[0], reg);
        let src_pb = alloc_procbin(&mut src, SharedBinHandle::from_bytes(&[0xab, 0xcd], 16));
        let shared_p = src_pb.shared_raw();
        let proc_bits = crate::fz_value::heap_object_word(
            src_pb.as_raw() as *const u8,
            crate::fz_value::ValueKind::PROCBIN,
        );
        let pair = src.alloc_struct(pair_id);
        let proc_value = heap_root(proc_bits);
        src.write_field_slot(pair, 0, proc_value);
        src.write_field_slot(pair, 8, proc_value);
        let mut fwd = std::collections::HashMap::new();
        let _ = deep_copy_slot(
            AnyValue::heap_ptr(pair, ValueKind::STRUCT),
            &src,
            &mut dst,
            &mut fwd,
        );
        assert_eq!(mso_chain(&dst).len(), 1, "dedup");
        unsafe {
            assert_eq!((*shared_p).refcount.load(crate::sync::Ordering::Relaxed), 2);
        }
        drop(dst);
        drop(src);
        assert_eq!(live_count(), baseline);
    }

    // ===== alloc_bitstring threshold + dispatch ===========================

    #[test]
    fn alloc_bitstring_small_stays_inline() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let bytes: Vec<u8> = (0..32u8).collect();
        let p = h.alloc_bitstring(&bytes, 256);
        let tagged = crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::BITSTRING);
        unsafe {
            assert_eq!(
                tagged & crate::fz_value::TAG_MASK,
                crate::fz_value::TAG_BITSTRING
            );
            assert_eq!(bitstring_bit_len(tagged as *const u8), 256);
            let pay = bitstring_byte_ptr(tagged as *const u8);
            for (i, expected) in bytes.iter().enumerate().take(32) {
                assert_eq!(*pay.add(i), *expected);
            }
        }
        assert_eq!(h.mso_head, 0);
    }

    #[test]
    #[serial_test::serial]
    fn alloc_bitstring_large_routes_to_shared_zone() {
        let baseline = live_count();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let bytes: Vec<u8> = (0..128u8).collect();
        let p = h.alloc_bitstring(&bytes, 1024);
        let tagged = crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::PROCBIN);
        unsafe {
            assert_eq!(
                tagged & crate::fz_value::TAG_MASK,
                crate::fz_value::TAG_PROCBIN
            );
            assert_eq!(crate::fz_value::object_size(tagged), 16);
            assert_eq!(bitstring_bit_len(tagged as *const u8), 1024);
            let pay = bitstring_byte_ptr(tagged as *const u8);
            for (i, expected) in bytes.iter().enumerate().take(128) {
                assert_eq!(*pay.add(i), *expected);
            }
        }
        assert_eq!(mso_chain(&h).len(), 1);
        assert_eq!(live_count(), baseline + 1);
        drop(h);
        assert_eq!(live_count(), baseline);
    }

    /// Full spawn-and-share scenario at the heap layer.
    #[test]
    #[serial_test::serial]
    fn shared_heap_acceptance_spawn_and_share() {
        const N: usize = 4;
        let baseline = live_count();
        let payload: Vec<u8> = (0..128u8).collect();
        let mut sender = Heap::new(SIZE_TABLE[0], empty_registry());
        let bs_in_sender = sender.alloc_bitstring(&payload, 1024);
        assert_eq!(live_count(), baseline + 1);

        let mut receivers: Vec<Heap> = (0..N)
            .map(|_| Heap::new(SIZE_TABLE[0], empty_registry()))
            .collect();
        let sender_bits = crate::fz_value::heap_object_word(
            bs_in_sender as *const u8,
            crate::fz_value::ValueKind::PROCBIN,
        );
        let mut receiver_roots: Vec<u64> = Vec::with_capacity(N);
        for r in receivers.iter_mut() {
            let mut fwd = std::collections::HashMap::new();
            let copied = deep_copy_slot(heap_root(sender_bits), &sender, r, &mut fwd);
            receiver_roots.push(tagged_bits(copied));
        }
        let sender_pb = unsafe { ProcBin::from_raw(bs_in_sender) };
        let shared_p = sender_pb.shared_raw();
        unsafe {
            assert_eq!(
                (*shared_p).refcount.load(crate::sync::Ordering::Relaxed),
                1 + N
            );
        }
        assert_eq!(live_count(), baseline + 1);

        for (r, root_ptr) in receivers.iter_mut().zip(receiver_roots.iter_mut()) {
            let mut root_u8 = *root_ptr as *mut u8;
            r.gc(&mut root_u8);
            *root_ptr = root_u8 as u64;
            let chain = mso_chain(r);
            assert_eq!(chain.len(), 1);
            assert_eq!(chain[0], *root_ptr);
        }
        assert_eq!(live_count(), baseline + 1);

        for root_ptr in &receiver_roots {
            unsafe {
                assert_eq!(bitstring_bit_len(*root_ptr as *const u8), 1024);
                let bp = bitstring_byte_ptr(*root_ptr as *const u8);
                for (i, expected) in payload.iter().enumerate() {
                    assert_eq!(*bp.add(i), *expected);
                }
            }
        }

        let _ = receiver_roots;
        drop(receivers);
        unsafe {
            assert_eq!((*shared_p).refcount.load(crate::sync::Ordering::Relaxed), 1);
        }
        assert_eq!(live_count(), baseline + 1);

        drop(sender);
        assert_eq!(live_count(), baseline);
    }

    // ===== fz-q8d.4 — heap fragments ======================================

    /// Oversized allocations land in the fragment list, bypass the bump
    /// arena, and report their size via `bytes_used()`.
    #[test]
    fn alloc_oversized_routes_to_fragment_list() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let want = SIZE_TABLE[SIZE_TABLE.len() - 1] + 16;
        let p = h.alloc(want);
        assert!(!p.is_null());
        assert_eq!(h.fragments.len(), 1);
        assert_eq!(h.fragments[0].size, (want + 15) & !15);
        // bytes_used includes the fragment size.
        assert!(h.bytes_used() >= h.fragments[0].size);
    }

    /// Rooted oversized struct survives GC; mark bit cycles back to false.
    #[test]
    fn rooted_fragment_survives_gc() {
        let reg = empty_registry();
        // A schema large enough that alloc_struct routes to fragments.
        let n_fields = (FRAGMENT_THRESHOLD + 256) / 8; // payload size > threshold
        let mut fields = Vec::with_capacity(n_fields);
        for i in 0..n_fields {
            fields.push(FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::AnyValue,
            });
        }
        let id = reg.borrow_mut().register(Schema {
            name: "Big".into(),
            size: (n_fields * 8) as u32,
            fields,
        });
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let big = h.alloc_struct(id);
        assert_eq!(h.fragments.len(), 1);
        let frag_ptr = h.fragments[0].ptr;
        let mut root =
            crate::fz_value::heap_object_word(big as *const u8, crate::fz_value::ValueKind::STRUCT)
                as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.fragments.len(), 1, "fragment survives");
        assert_eq!(h.fragments[0].ptr, frag_ptr, "fragment did not move");
        assert!(!h.fragments[0].mark, "mark reset post-GC");
        // Root is unchanged because the fragment did not move.
        assert_eq!(
            crate::fz_value::struct_addr_from_tagged(root as u64),
            Some(big)
        );
    }

    /// Unrooted oversized object is freed by GC; fragment list shrinks.
    #[test]
    fn unrooted_fragment_is_freed_by_gc() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let _ = h.alloc(FRAGMENT_THRESHOLD + 16);
        assert_eq!(h.fragments.len(), 1);
        let mut root: *mut u8 = std::ptr::null_mut();
        h.gc(&mut root);
        assert!(h.fragments.is_empty(), "unrooted fragment freed");
    }

    /// Three fragments, two rooted: the unrooted one is reclaimed.
    #[test]
    fn mixed_fragment_liveness() {
        let reg = empty_registry();
        let n_fields = (FRAGMENT_THRESHOLD + 256) / 8;
        let mut fields = Vec::with_capacity(n_fields);
        for i in 0..n_fields {
            fields.push(FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::AnyValue,
            });
        }
        let id = reg.borrow_mut().register(Schema {
            name: "Big".into(),
            size: (n_fields * 8) as u32,
            fields,
        });
        let mut h = Heap::new(SIZE_TABLE[0], reg.clone());
        let a = h.alloc_struct(id);
        let _b_dead = h.alloc_struct(id);
        let c = h.alloc_struct(id);
        assert_eq!(h.fragments.len(), 3);
        // We can only thread one root pointer through `gc`; package a
        // pair {a, c} into a typed tuple in the bump arena; that becomes a
        // root containing both.
        let pair_id = reg.borrow_mut().register(Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor {
                    offset: 0,
                    kind: FieldKind::AnyValue,
                },
                FieldDescriptor {
                    offset: 8,
                    kind: FieldKind::AnyValue,
                },
            ],
        });
        let pair = h.alloc_struct(pair_id);
        h.write_field_slot(pair, 0, AnyValue::heap_ptr(a, ValueKind::STRUCT));
        h.write_field_slot(pair, 8, AnyValue::heap_ptr(c, ValueKind::STRUCT));
        let mut root = crate::fz_value::heap_object_word(
            pair as *const u8,
            crate::fz_value::ValueKind::STRUCT,
        ) as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.fragments.len(), 2, "the unrooted fragment was reclaimed");
    }

    /// Fragment → fragment edge: the head fragment holds a pointer at
    /// payload offset 0 to a second fragment. Rooting the head must
    /// keep both alive.
    #[test]
    fn fragment_to_fragment_edge_survives_gc() {
        let reg = empty_registry();
        let n_fields = (FRAGMENT_THRESHOLD + 256) / 8;
        let mut fields = Vec::with_capacity(n_fields);
        for i in 0..n_fields {
            fields.push(FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::AnyValue,
            });
        }
        let id = reg.borrow_mut().register(Schema {
            name: "Big".into(),
            size: (n_fields * 8) as u32,
            fields,
        });
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let head = h.alloc_struct(id);
        let tail = h.alloc_struct(id);
        h.write_field_slot(head, 0, AnyValue::heap_ptr(tail, ValueKind::STRUCT));
        let mut root = crate::fz_value::heap_object_word(
            head as *const u8,
            crate::fz_value::ValueKind::STRUCT,
        ) as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.fragments.len(), 2, "both fragments survive");
    }

    /// Fragment → to-space edge: a fragment holds a pointer to a
    /// normal heap-resident List cons. Rooting the fragment must
    /// preserve the cons and move it to to-space.
    #[test]
    fn fragment_to_block_edge_promotes_block_object() {
        let reg = empty_registry();
        let n_fields = (FRAGMENT_THRESHOLD + 256) / 8;
        let mut fields = Vec::with_capacity(n_fields);
        for i in 0..n_fields {
            fields.push(FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::AnyValue,
            });
        }
        let id = reg.borrow_mut().register(Schema {
            name: "Big".into(),
            size: (n_fields * 8) as u32,
            fields,
        });
        let mut h = Heap::new(SIZE_TABLE[0], reg);
        let cons = alloc_int_list_cons(&mut h, 7, crate::fz_value::EMPTY_LIST);
        let big = h.alloc_struct(id);
        h.write_field_slot(big, 0, heap_root(cons));
        let mut root =
            crate::fz_value::heap_object_word(big as *const u8, crate::fz_value::ValueKind::STRUCT)
                as *mut u8;
        h.gc(&mut root);
        assert_eq!(h.fragments.len(), 1, "fragment survives");
        let child_value = h.read_field_slot(big, 0);
        assert_eq!(child_value.kind(), crate::fz_value::ValueKind::LIST);
        let child = child_value.raw() as *mut u8;
        unsafe {
            let cons = &*(child as *const ListCons);
            assert_eq!(cons.head_kind(), crate::fz_value::ValueKind::INT);
            assert_eq!(cons.head as i64, 7);
        }
    }

    /// Heap::drop with live fragments deallocates them (no leak).
    /// Verified indirectly: drop without panic, and a follow-up alloc
    /// at the same allocator gets a fresh pointer.
    #[test]
    fn heap_drop_releases_fragments_without_leak() {
        // Two heaps in sequence: first holds a fragment then drops; the
        // drop frees the fragment. Second heap can allocate without
        // tripping anything in the allocator's reuse path.
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let _ = h.alloc(FRAGMENT_THRESHOLD + 16);
            assert_eq!(h.fragments.len(), 1);
        }
        let mut h2 = Heap::new(SIZE_TABLE[0], empty_registry());
        let p = h2.alloc(FRAGMENT_THRESHOLD + 16);
        assert!(!p.is_null());
    }

    #[test]
    #[serial_test::serial]
    fn procbin_round_trips_through_bitstring_dispatchers() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let bytes: Vec<u8> = (0..100u8).collect();
        let p = h.alloc_bitstring(&bytes, 800);
        let tagged = crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::PROCBIN);
        let bl = unsafe { bitstring_bit_len(tagged as *const u8) };
        let bp = unsafe { bitstring_byte_ptr(tagged as *const u8) };
        assert_eq!(bl, 800);
        let recovered: Vec<u8> = (0..100).map(|i| unsafe { *bp.add(i) }).collect();
        assert_eq!(recovered, bytes);
    }
