use super::*;
use crate::any_value::{AnyValue, AnyValueRef, EMPTY_LIST_BITS, ValueKind, closure_size_for_count};
use crate::heap::{Schema, SchemaRegistry};
use crate::procbin::{bitstring_bit_len, bitstring_byte_ptr};
use crate::process::{DEFAULT_REDUCTIONS_PER_QUANTUM, Process, YIELD_REASON_REDUCTIONS};
use std::cell::RefCell;
use std::rc::Rc;

/// Run `f` with a fresh Process. The process is threaded explicitly — the
/// runtime no longer has an ambient `CURRENT_PROCESS`, so BIFs and helpers
/// take it as a parameter.
fn with_process<R>(f: impl FnOnce(&mut Process) -> R) -> R {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut proc = Box::new(Process::new(schemas));
    f(&mut proc)
}

fn map_int_value_by_atom_name(process: &Process, map_ref_word: u64, name: &str) -> i64 {
    let map_ref = AnyValueRef::from_raw_word(map_ref_word).expect("stats map ref");
    let map_addr = map_ref.map_addr().expect("stats map addr");
    let count = unsafe { map_count(map_addr as *const u8) };
    for i in 0..count {
        let (key, value) = unsafe { map_entry(map_addr as *const u8, i) };
        if key.kind() == ValueKind::ATOM && process.node.atom_name(key.raw() as u32).as_deref() == Some(name) {
            if let AnyValue::Int(value) = value {
                return value;
            }
            panic!("stats key {name} was not an integer: {value:?}");
        }
    }
    panic!("stats key {name} not found");
}

fn range_ref(process: &mut Process, first: i64, last: i64, step: i64) -> u64 {
    let schema_id = process.heap.register_schema(Schema::range());
    let p = process.heap.alloc_struct(schema_id);
    process.heap.write_field_slot(p, 0, AnyValue::int(first));
    process.heap.write_field_slot(p, 8, AnyValue::int(last));
    process.heap.write_field_slot(p, 16, AnyValue::int(step));
    AnyValueRef::from_heap_object(ValueKind::STRUCT, p)
        .expect("range ref")
        .raw_word()
}

#[test]
fn list_cons_predicate_rejects_empty_list() {
    with_process(|process| {
        let empty = AnyValueRef::empty_list().raw_word();
        assert_eq!(fz_list_is_cons(empty), 0, "[] is list-typed, but it is not a cons cell");

        let cons_bits = process.heap.alloc_list_cons_slot(AnyValue::int(1), EMPTY_LIST_BITS);
        let cons_addr = list_addr_from_tagged(cons_bits).expect("cons addr");
        let cons = AnyValueRef::from_heap_object(ValueKind::LIST, cons_addr)
            .expect("cons ref")
            .raw_word();
        assert_eq!(fz_list_is_cons(cons), 1, "a heap list cell is a cons cell");
    });
}

#[test]
fn range_constructor_reuses_schema_and_renders_like_elixir() {
    with_process(|process| {
        let process_ptr = process as *mut Process;

        let ascending = range_ref(process, 1, 10, 1);
        let stepped = range_ref(process, 1, 10, 2);
        let descending = range_ref(process, 10, 1, -1);

        assert_eq!(
            process.heap.schemas_registry().borrow().len(),
            1,
            "all ranges share the canonical Range schema"
        );
        assert_eq!(
            render_value(
                process_ptr,
                AnyValue::from_ref(AnyValueRef::from_raw_word(ascending).unwrap()).unwrap()
            ),
            "1..10"
        );
        assert_eq!(
            render_value(
                process_ptr,
                AnyValue::from_ref(AnyValueRef::from_raw_word(stepped).unwrap()).unwrap()
            ),
            "1..10//2"
        );
        assert_eq!(
            render_value(
                process_ptr,
                AnyValue::from_ref(AnyValueRef::from_raw_word(descending).unwrap()).unwrap()
            ),
            "10..1//-1"
        );
    });
}

#[test]
fn range_equality_comes_from_struct_fields() {
    with_process(|process| {
        let process_ptr = process as *mut Process;
        let a = range_ref(process, 1, 3, 1);
        let b = range_ref(process, 1, 3, 1);
        let c = range_ref(process, 1, 3, 2);

        assert_eq!(fz_value_eq_ref(process_ptr, a, b), 1);
        assert_eq!(fz_value_eq_ref(process_ptr, a, c), 0);
    });
}

#[test]
fn process_heap_alloc_stats_returns_pre_materialization_snapshot() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut proc_owned = Process::new(schemas);
    let process = &mut proc_owned;
    process.heap.reset_alloc_stats();
    let _ = process.heap.alloc_list_cons_slot(AnyValue::int(1), EMPTY_LIST_BITS);

    let stats_ref = fz_process_heap_alloc_stats(process);
    assert_eq!(map_int_value_by_atom_name(process, stats_ref, "allocs"), 1);
    assert_eq!(map_int_value_by_atom_name(process, stats_ref, "list_cons_allocs"), 1);
    assert_eq!(map_int_value_by_atom_name(process, stats_ref, "map_allocs"), 0);
    assert_eq!(map_int_value_by_atom_name(process, stats_ref, "scheduler_yields"), 0);
    assert_eq!(map_int_value_by_atom_name(process, stats_ref, "interpreter_yields"), 0);
    assert_eq!(
        map_int_value_by_atom_name(process, stats_ref, "reductions_remaining"),
        DEFAULT_REDUCTIONS_PER_QUANTUM as i64
    );
    assert_eq!(
        map_int_value_by_atom_name(process, stats_ref, "reductions_per_quantum"),
        DEFAULT_REDUCTIONS_PER_QUANTUM as i64
    );
    assert_eq!(map_int_value_by_atom_name(process, stats_ref, "reductions_executed"), 0);
    assert_eq!(map_int_value_by_atom_name(process, stats_ref, "reduction_yields"), 0);
    assert_eq!(
        map_int_value_by_atom_name(process, stats_ref, "allocation_pressure_yields"),
        0
    );
    assert_eq!(map_int_value_by_atom_name(process, stats_ref, "yield_reasons"), 0);
    assert_eq!(
        map_int_value_by_atom_name(process, stats_ref, "max_yield_continuation_bytes"),
        0
    );
    assert_eq!(
        map_int_value_by_atom_name(process, stats_ref, "min_yield_continuation_margin_before_bytes",),
        0
    );
    assert_eq!(
        map_int_value_by_atom_name(process, stats_ref, "min_yield_continuation_margin_after_bytes"),
        0
    );

    let after = process.heap.alloc_stats_snapshot();
    assert_eq!(after.list_cons.allocs, 1);
    assert_eq!(after.map.allocs, 1);
    assert_eq!(after.total.allocs, 2);
}

#[test]
fn frame_alloc_records_on_installed_process() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut proc_owned = Process::new(schemas);
    let process = &mut proc_owned;
    process.heap.reset_alloc_stats();

    let _ = fz_alloc_frame_for_test(process, 7, 17);

    let stats = process.heap.alloc_stats_snapshot();
    assert_eq!(stats.frame.allocs, 1);
    assert_eq!(stats.frame.bytes, 32);
    assert_eq!(stats.total.allocs, 1);
    assert_eq!(stats.total.bytes, 32);
}

/// fz-axu.14 (R1) — valid UTF-8 byte-aligned bitstring → 1.
#[test]
fn fz_bitstring_valid_utf8_accepts_byte_aligned_utf8() {
    with_process(|process| {
        let bytes = "héllo".as_bytes();
        let bits = fz_alloc_bitstring_const(
            process,
            bytes.as_ptr() as u64,
            bytes.len() as u64,
            (bytes.len() * 8) as u64,
        );
        assert_eq!(fz_bitstring_valid_utf8(bits), 1);
    });
}

#[test]
fn yield_mid_flight_report_stashes_runnable_closure() {
    with_process(|process| {
        let bits = process.heap.alloc_closure_slots(0, 0, 0);
        let closure_addr = closure_addr_from_tagged(bits).expect("closure addr");
        let closure_ref = AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr)
            .expect("closure ref")
            .raw_word();
        let ret = fz_yield_mid_flight_report(process, closure_ref, -1, YIELD_REASON_REDUCTIONS as u32);
        assert_eq!(ret as u64, YIELD_PTR);
        assert_eq!(process.runnable_ptr(), closure_addr);
        assert_eq!(process.scheduler_yields, 1);
        assert_eq!(process.reductions_remaining, -1);
        assert_eq!(process.reduction_yields, 1);
        assert_eq!(process.yield_reasons, YIELD_REASON_REDUCTIONS);
        assert_eq!(process.max_yield_continuation_bytes, closure_size_for_count(0) as u64);
        assert!(process.min_yield_continuation_margin_after_bytes > 0);
    });
}

/// Invalid byte sequence → 0.
#[test]
fn fz_bitstring_valid_utf8_rejects_bad_bytes() {
    with_process(|process| {
        let bytes = [0xffu8, 0xffu8];
        let bits = fz_alloc_bitstring_const(process, bytes.as_ptr() as u64, 2, 16);
        assert_eq!(fz_bitstring_valid_utf8(bits), 0);
    });
}

/// Non-byte-aligned bitstring → 0 even if the byte payload would
/// be valid UTF-8 — UTF-8 is byte-oriented.
#[test]
fn fz_bitstring_valid_utf8_rejects_non_byte_aligned() {
    with_process(|process| {
        let bytes = [b'h'];
        let bits = fz_alloc_bitstring_const(process, bytes.as_ptr() as u64, 1, 7);
        assert_eq!(fz_bitstring_valid_utf8(bits), 0);
    });
}

/// Brand-mint is identity at the bits level.
#[test]
fn fz_brand_bitstring_as_utf8_is_identity() {
    assert_eq!(fz_brand_bitstring_as_utf8(0x1234_5678_9abc_def0), 0x1234_5678_9abc_def0);
    assert_eq!(fz_brand_bitstring_as_utf8(0), 0);
}

#[test]
fn ref_projection_helpers_load_scalar_payloads() {
    let int_slot = -42_i64 as u64;
    let float_slot = 3.5_f64.to_bits();
    let atom_slot = 17_u64;
    let int_ref = AnyValueRef::from_scalar_slot(ValueKind::INT, &int_slot).expect("int ref");
    let float_ref = AnyValueRef::from_scalar_slot(ValueKind::FLOAT, &float_slot).expect("float ref");
    let atom_ref = AnyValueRef::from_scalar_slot(ValueKind::ATOM, &atom_slot).expect("atom ref");

    assert_eq!(fz_ref_tag(int_ref.raw_word()), ValueKind::INT.tag());
    assert_eq!(fz_ref_load_int(int_ref.raw_word()), -42);
    assert_eq!(fz_ref_load_float(float_ref.raw_word()), 3.5);
    assert_eq!(fz_ref_load_atom(atom_ref.raw_word()), 17);
}

#[test]
fn map_typed_get_projects_expected_scalar_value() {
    with_process(|process| {
        let key_slot = 1u64;
        let key_ref = AnyValueRef::from_scalar_slot(ValueKind::ATOM, &key_slot).expect("key ref");
        let map_bits = process.heap.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(42))]);
        let map_addr = map_addr_from_tagged(map_bits).expect("map addr");
        let map_ref = AnyValueRef::from_heap_object(ValueKind::MAP, map_addr).expect("map ref");

        assert_eq!(map_get_int_impl(process, map_ref.raw_word(), key_ref.raw_word()), 42);
    });
}

#[test]
fn typed_map_put_ffi_round_trips_atom_key_int_value() {
    with_process(|process| {
        let key = fz_box_atom_for_any(process, 1);
        let map = fz_map_put_int(process, fz_map_empty(process), key, 42);
        let map_ref = AnyValueRef::from_raw_word(map).expect("map ref");
        let got = fz_map_get_ref(process, map_ref.raw_word(), key);
        assert_eq!(fz_ref_load_int(got), 42);
    });
}

#[test]
#[should_panic(expected = "fz_ref_load_int")]
fn map_typed_get_panics_on_wrong_scalar_type() {
    with_process(|process| {
        let key_slot = 1u64;
        let key_ref = AnyValueRef::from_scalar_slot(ValueKind::ATOM, &key_slot).expect("key ref");
        let map_bits = process.heap.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::atom(7))]);
        let map_addr = map_addr_from_tagged(map_bits).expect("map addr");
        let map_ref = AnyValueRef::from_heap_object(ValueKind::MAP, map_addr).expect("map ref");

        let _ = map_get_int_impl(process, map_ref.raw_word(), key_ref.raw_word());
    });
}

/// fz-cty.8 — small (<= threshold) payload allocates inline Bitstring.
#[test]
fn alloc_bitstring_const_small_payload_is_inline() {
    with_process(|process| {
        let bytes: [u8; 3] = [0xaa, 0xbb, 0xcc];
        let ref_word = fz_alloc_bitstring_const(process, bytes.as_ptr() as u64, 3, 24);
        let bitstring_ref = AnyValueRef::from_raw_word(ref_word).expect("bitstring ref");
        let addr = bitstring_ref.bitstring_addr().expect("bitstring addr");
        let bits = heap_object_word(addr, ValueKind::BITSTRING);
        unsafe {
            assert_eq!(
                bits & TAG_MASK,
                TAG_BITSTRING,
                "small payload should pick the strict inline Bitstring tag"
            );
            assert_eq!(bitstring_bit_len(bits as *const u8), 24);
            let bp = bitstring_byte_ptr(bits as *const u8);
            assert_eq!(from_raw_parts(bp, 3), &bytes);
        }
    });
}

/// fz-q8d.2 — `fz_alloc_procbin_from_static` retains the static
/// SharedBin's anchor (climbing 1 → 2), allocates a ProcBin that
/// owns the new edge, and returns it as a tagged ProcBin pointer. When
/// the holding heap drops, the anchor is preserved (refcount stays
/// at 1) — the static SharedBin lives forever.
#[test]
#[serial_test::serial]
fn alloc_procbin_from_static_preserves_anchor() {
    use crate::procbin::SharedBin;
    use crate::sync::{AtomicUsize, Ordering};
    // Construct a "static" SharedBin by hand. Its destructor is a
    // noop pointer so the test owns its lifetime explicitly.
    static PAYLOAD: [u8; 8] = [0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe];
    unsafe extern "C" fn noop(_: *mut SharedBin) {}
    let mut sb = SharedBin {
        refcount: AtomicUsize::new(1),
        bit_len: 64,
        bytes_ptr: PAYLOAD.as_ptr(),
        bytes_len: PAYLOAD.len(),
        destructor: noop,
    };
    let sb_ptr = &mut sb as *mut SharedBin;
    with_process(|process| {
        let ref_word = fz_alloc_procbin_from_static(process, sb_ptr as u64);
        let procbin_ref = AnyValueRef::from_raw_word(ref_word).expect("procbin ref");
        let addr = procbin_ref.procbin_addr().expect("procbin addr");
        let bits = heap_object_word(addr, ValueKind::PROCBIN);
        unsafe {
            assert_eq!(bits & TAG_MASK, TAG_PROCBIN);
            assert_eq!(object_size(bits), 16);
            assert_eq!(bitstring_bit_len(bits as *const u8), 64);
            let bp = bitstring_byte_ptr(bits as *const u8);
            assert_eq!(from_raw_parts(bp, 8), &PAYLOAD[..]);
            // retain climbed anchor 1 -> 2.
            assert_eq!(sb.refcount.load(Ordering::Relaxed), 2);
        }
        // When the with_process drops the temp Process, the heap drop
        // releases the ProcBin's edge, returning refcount to the
        // anchor value 1.
    });
    assert_eq!(sb.refcount.load(Ordering::Relaxed), 1, "anchor preserved");
}

/// fz-cty.8 — large (> threshold) payload routes through ProcBin / SharedBin.
#[test]
#[serial_test::serial]
fn alloc_bitstring_const_large_payload_is_procbin() {
    with_process(|process| {
        let payload: Vec<u8> = (0..70u8).collect(); // 70 > SHARED_BIN_THRESHOLD_BYTES (64)
        let ref_word = fz_alloc_bitstring_const(process, payload.as_ptr() as u64, payload.len() as u64, 70 * 8);
        let procbin_ref = AnyValueRef::from_raw_word(ref_word).expect("procbin ref");
        let addr = procbin_ref.procbin_addr().expect("procbin addr");
        let bits = heap_object_word(addr, ValueKind::PROCBIN);
        unsafe {
            assert_eq!(bits & TAG_MASK, TAG_PROCBIN);
            assert_eq!(object_size(bits), 16);
            assert_eq!(bitstring_bit_len(bits as *const u8), 70 * 8);
            let bp = bitstring_byte_ptr(bits as *const u8);
            assert_eq!(from_raw_parts(bp, payload.len()), payload.as_slice());
        }
    });
}
