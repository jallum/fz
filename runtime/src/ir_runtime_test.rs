use super::*;
use crate::any_value::{
    AnyValue, AnyValueRef, EMPTY_LIST_BITS, ValueKind, closure_size_for_count, list_addr_from_tagged, map_entry,
};
use crate::exec_ctx::Argv;
use crate::heap::{Schema, SchemaRegistry};
use crate::procbin::{PROCBIN_BYTES, bitstring_bit_len, bitstring_byte_ptr};
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

#[test]
fn scheduler_exports_forward_exact_words_and_send_returns_the_original_message() {
    #[derive(Default)]
    struct Calls {
        closure: u64,
        receiver: u32,
        message: u64,
    }

    extern "C" fn spawn(_sender: *mut Process, scheduler: *mut (), closure: u64) -> u32 {
        let calls = unsafe { &mut *(scheduler as *mut Calls) };
        calls.closure = closure;
        37
    }

    extern "C" fn send(_sender: *mut Process, scheduler: *mut (), receiver: u32, message: u64) {
        let calls = unsafe { &mut *(scheduler as *mut Calls) };
        calls.receiver = receiver;
        calls.message = message;
    }

    with_process(|process| {
        let process_ptr = process as *mut Process;
        let closure = process
            .heap
            .alloc_list_cons_int(1, AnyValueRef::empty_list())
            .expect("representative boxed closure lane")
            .raw_word();
        let message = process
            .heap
            .alloc_list_cons_int(2, AnyValueRef::empty_list())
            .expect("boxed message")
            .raw_word();
        let mut calls = Calls::default();
        let mut ctx = ExecCtx {
            scheduler: &mut calls as *mut Calls as *mut (),
            spawn: Some(spawn),
            send: Some(send),
            ..ExecCtx::empty()
        };
        process.ctx = &mut ctx;

        assert_eq!(fz_spawn(process_ptr, closure), 37);
        assert_eq!(fz_send(process_ptr, 41, message), message);
        assert_eq!(calls.closure, closure);
        assert_eq!(calls.receiver, 41);
        assert_eq!(calls.message, message);
    });
}

#[test]
fn total_arithmetic_exports_return_initialized_result_and_canonical_status_at_boundaries() {
    assert_eq!(
        fz_op_neg_i(i64::MIN),
        FzIntegerArithmeticResult {
            result: i64::MIN,
            failed: 1,
        }
    );
    assert_eq!(
        fz_op_add_ii(i64::MAX, 1),
        FzIntegerArithmeticResult {
            result: i64::MIN,
            failed: 1,
        }
    );
    assert_eq!(
        fz_op_sub_ii(i64::MIN, 1),
        FzIntegerArithmeticResult {
            result: i64::MAX,
            failed: 1,
        }
    );
    assert_eq!(
        fz_op_mul_ii(i64::MAX, 2),
        FzIntegerArithmeticResult { result: -2, failed: 1 }
    );
    assert_eq!(fz_op_div_ii(1, 0), FzIntegerArithmeticResult { result: 0, failed: 1 });
    assert_eq!(
        fz_op_div_ii(i64::MIN, -1),
        FzIntegerArithmeticResult { result: 0, failed: 1 }
    );
    assert_eq!(fz_op_rem_ii(1, 0), FzIntegerArithmeticResult { result: 0, failed: 1 });
    assert_eq!(
        fz_op_rem_ii(i64::MIN, -1),
        FzIntegerArithmeticResult { result: 0, failed: 0 }
    );
    for failed in [
        fz_op_add_ff(f64::MAX, f64::MAX),
        fz_op_div_ii_to_float(1, 0),
        fz_op_div_ii_to_float(1, -0),
        fz_op_div_ff(1.0, -0.0),
        fz_op_rem_ff(1.0, 0.0),
    ] {
        assert_eq!(failed, FzFloatArithmeticResult { result: 0.0, failed: 1 });
    }
    assert_eq!(
        fz_op_rem_ff(-7.5, 2.0),
        FzFloatArithmeticResult {
            result: -1.5,
            failed: 0
        }
    );
    assert_eq!(fz_op_neg_f(0.0).to_bits(), (-0.0f64).to_bits());
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
    unsafe { process.heap.write_field_slot(p, 0, AnyValue::int(first)) };
    unsafe { process.heap.write_field_slot(p, 8, AnyValue::int(last)) };
    unsafe { process.heap.write_field_slot(p, 16, AnyValue::int(step)) };
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
            crate::heap::SchemaRegistry::new().len() + 1,
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

/// Valid UTF-8 byte-aligned bitstring → 1.
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
fn utf8_prefix_names_the_first_impossible_byte() {
    let cases: &[(&[u8], Result<usize, usize>)] = &[
        (&[], Ok(0)),
        (&[0x7f], Ok(1)),
        (&[0xc2, 0x80], Ok(2)),
        (&[0xe0, 0xa0, 0x80], Ok(3)),
        (&[0xed, 0x9f, 0xbf], Ok(3)),
        (&[0xf0, 0x90, 0x80, 0x80], Ok(4)),
        (&[0xf4, 0x8f, 0xbf, 0xbf], Ok(4)),
        (&[0x80], Err(0)),
        (&[0xc0, 0x80], Err(0)),
        (&[0xc2, b'A'], Err(1)),
        (&[0xe0, 0x80, 0x80], Err(1)),
        (&[0xed, 0xa0, 0x80], Err(1)),
        (&[0xe1, 0x80, b'A'], Err(2)),
        (&[0xf0, 0x80, 0x80, 0x80], Err(1)),
        (&[0xf4, 0x90, 0x80, 0x80], Err(1)),
        (&[0xf1, 0x80, 0x80, b'A'], Err(3)),
        (&[0xc2], Err(1)),
        (&[0xe1, 0x80], Err(2)),
    ];

    for &(bytes, expected) in cases {
        assert_eq!(utf8_prefix(bytes), expected, "bytes={bytes:?}");
    }
}

#[test]
fn utf8_prefix_accepts_every_unicode_scalar() {
    let mut buffer = [0; 4];
    for scalar in 0..=char::MAX as u32 {
        let Some(codepoint) = char::from_u32(scalar) else {
            continue;
        };
        let encoded = codepoint.encode_utf8(&mut buffer);
        assert_eq!(utf8_prefix(encoded.as_bytes()), Ok(encoded.len()), "U+{scalar:04X}");
    }
}

#[test]
fn fz_bitstring_utf8_prefix_exposes_width_or_encoded_error_offset() {
    with_process(|process| {
        let cases: &[(&[u8], i64)] = &[
            (&[0xf0, 0x9f, 0x98, 0x80], 4),
            (&[0xff], -1),
            (&[0xc2, b'A'], -2),
            (&[0xe1, 0x80, b'A'], -3),
            (&[0xf1, 0x80, 0x80, b'A'], -4),
            (&[0xe1, 0x80], -3),
        ];

        for &(bytes, expected) in cases {
            let bits = fz_alloc_bitstring_const(
                process,
                bytes.as_ptr() as u64,
                bytes.len() as u64,
                (bytes.len() * 8) as u64,
            );
            assert_eq!(fz_bitstring_utf8_prefix(bits), expected, "bytes={bytes:?}");
        }
    });
}

#[test]
fn yield_mid_flight_report_stashes_runnable_closure() {
    with_process(|process| {
        let bits = process
            .heap
            .alloc_closure_slots(crate::any_value::ClosureDenotationId::user(0), 0, 0, 0);
        let closure_addr = closure_addr_from_tagged(bits).expect("closure addr");
        let closure_ref = AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr)
            .expect("closure ref")
            .raw_word();
        let ret = fz_yield_mid_flight_report(process, closure_ref, -1, YIELD_REASON_REDUCTIONS as u32);
        assert_eq!(ret as u64, YIELD_PTR);
        assert_eq!(
            process.runnable_closure().map(|closure| closure.storage_addr()),
            Some(closure_addr)
        );
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
        let bytes = *b"h";
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
        let key_atom = process.node.intern_atom("key");
        let key_slot = u64::from(key_atom);
        let key_ref = AnyValueRef::from_scalar_slot(ValueKind::ATOM, &key_slot).expect("key ref");
        let map_bits = process
            .heap
            .alloc_map_slots(&[(AnyValue::atom(key_atom), AnyValue::int(42))]);
        let map_addr = map_addr_from_tagged(map_bits).expect("map addr");
        let map_ref = AnyValueRef::from_heap_object(ValueKind::MAP, map_addr).expect("map ref");

        assert_eq!(map_get_int_impl(process, map_ref.raw_word(), key_ref.raw_word()), 42);
    });
}

#[test]
fn typed_map_put_ffi_round_trips_atom_key_int_value() {
    with_process(|process| {
        let key_atom = process.node.intern_atom("key");
        let key = fz_box_atom_for_any(process, key_atom as u64);
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
        let key_atom = process.node.intern_atom("key");
        let value_atom = process.node.intern_atom("value");
        let key_slot = u64::from(key_atom);
        let key_ref = AnyValueRef::from_scalar_slot(ValueKind::ATOM, &key_slot).expect("key ref");
        let map_bits = process
            .heap
            .alloc_map_slots(&[(AnyValue::atom(key_atom), AnyValue::atom(value_atom))]);
        let map_addr = map_addr_from_tagged(map_bits).expect("map addr");
        let map_ref = AnyValueRef::from_heap_object(ValueKind::MAP, map_addr).expect("map ref");

        let _ = map_get_int_impl(process, map_ref.raw_word(), key_ref.raw_word());
    });
}

/// Small (<= threshold) payload allocates inline Bitstring.
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
                bitstring_ref.tag(),
                ValueKind::BITSTRING,
                "small payload should pick the inline Bitstring kind"
            );
            assert_eq!(bitstring_bit_len(bits), 24);
            let bp = bitstring_byte_ptr(bits);
            assert_eq!(from_raw_parts(bp, 3), &bytes);
        }
    });
}

/// `fz_alloc_procbin_from_static` retains the static
/// SharedBin's anchor (climbing 1 → 2), allocates a ProcBin that
/// owns the new edge, and returns it as a tagged ProcBin pointer. When
/// the holding heap drops, the anchor is preserved (refcount stays
/// at 1) — the static SharedBin lives forever.
#[test]
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
            assert_eq!(procbin_ref.tag(), ValueKind::PROCBIN);
            assert_eq!(object_size(bits), PROCBIN_BYTES);
            assert_eq!(bitstring_bit_len(bits), 64);
            let bp = bitstring_byte_ptr(bits);
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

/// Large (> threshold) payload routes through ProcBin / SharedBin.
#[test]
fn alloc_bitstring_const_large_payload_is_procbin() {
    with_process(|process| {
        let payload: Vec<u8> = (0..70u8).collect(); // 70 > SHARED_BIN_THRESHOLD_BYTES (64)
        let ref_word = fz_alloc_bitstring_const(process, payload.as_ptr() as u64, payload.len() as u64, 70 * 8);
        let procbin_ref = AnyValueRef::from_raw_word(ref_word).expect("procbin ref");
        let addr = procbin_ref.procbin_addr().expect("procbin addr");
        let bits = heap_object_word(addr, ValueKind::PROCBIN);
        unsafe {
            assert_eq!(procbin_ref.tag(), ValueKind::PROCBIN);
            assert_eq!(object_size(bits), PROCBIN_BYTES);
            assert_eq!(bitstring_bit_len(bits), 70 * 8);
            let bp = bitstring_byte_ptr(bits);
            assert_eq!(from_raw_parts(bp, payload.len()), payload.as_slice());
        }
    });
}

fn list_ref_from_bits(bits: u64) -> AnyValueRef {
    let addr = list_addr_from_tagged(bits).expect("list addr");
    AnyValueRef::from_heap_object(ValueKind::LIST, addr).expect("list ref")
}

#[test]
fn list_retention_ref_normalizes_dynamic_head_once() {
    with_process(|process| {
        let source = process.heap.alloc_list_cons_slot(AnyValue::int(42), EMPTY_LIST_BITS);
        let source_ref = list_ref_from_bits(source);
        let head_ref = fz_list_head_ref(source_ref.raw_word());
        let tail_ref = fz_list_tail_ref(source_ref.raw_word());
        process
            .heap
            .mark_published_ref_aliased(source_ref)
            .expect("share source");
        let result = fz_list_reuse_or_cons_ref(process, source_ref.raw_word(), head_ref, tail_ref, 0);
        assert_eq!(
            result,
            source_ref.raw_word(),
            "unchanged shared cell survives a dynamic head"
        );
        assert_eq!((process.list_retention_attempts, process.list_retention_hits), (1, 1));
        let other = process.heap.alloc_list_cons_slot(AnyValue::int(7), EMPTY_LIST_BITS);
        let changed_head = fz_list_head_ref(list_ref_from_bits(other).raw_word());
        let result = fz_list_reuse_or_cons_ref(process, source_ref.raw_word(), changed_head, tail_ref, 1);
        assert_ne!(result, source_ref.raw_word(), "shared changed source allocates");
        assert_eq!((process.list_retention_attempts, process.list_retention_hits), (2, 1));
        for permission in [0, 1] {
            let source = process.heap.alloc_list_cons_slot(AnyValue::int(42), EMPTY_LIST_BITS);
            let source = list_ref_from_bits(source).raw_word();
            let result = fz_list_reuse_or_cons_ref(process, source, changed_head, tail_ref, permission);
            assert_eq!(
                result == source,
                permission == 1,
                "only explicit permission rewrites an unshared changed cell"
            );
        }
        assert_eq!((process.list_retention_attempts, process.list_retention_hits), (4, 2));
    });
}

#[test]
fn list_reuse_or_cons_parts_updates_process_counters() {
    with_process(|process| {
        let old_tail = process.heap.alloc_list_cons_slot(AnyValue::int(1), EMPTY_LIST_BITS);
        let new_tail = process.heap.alloc_list_cons_slot(AnyValue::int(2), EMPTY_LIST_BITS);
        let source = process.heap.alloc_list_cons_slot(AnyValue::int(0), old_tail);
        let reused_word = fz_list_reuse_or_cons_parts(
            process as *mut Process,
            list_ref_from_bits(source).raw_word(),
            7,
            ValueKind::ATOM.tag() as u64,
            list_ref_from_bits(new_tail).raw_word(),
            1,
        );

        assert_eq!(reused_word, list_ref_from_bits(source).raw_word());
        assert_eq!(process.list_retention_attempts, 1);
        assert_eq!(process.list_retention_hits, 1);

        let old_tail = process.heap.alloc_list_cons_slot(AnyValue::int(3), EMPTY_LIST_BITS);
        let new_tail = process.heap.alloc_list_cons_slot(AnyValue::int(4), EMPTY_LIST_BITS);
        let source = process.heap.alloc_list_cons_slot(AnyValue::int(9), old_tail);
        let source_ref = list_ref_from_bits(source);
        process
            .heap
            .mark_published_ref_aliased(source_ref)
            .expect("publish source");
        let fallback_word = fz_list_reuse_or_cons_parts(
            process as *mut Process,
            source_ref.raw_word(),
            11,
            ValueKind::INT.tag() as u64,
            list_ref_from_bits(new_tail).raw_word(),
            1,
        );

        assert_ne!(fallback_word, source_ref.raw_word());
        assert_eq!(process.list_retention_attempts, 2);
        assert_eq!(process.list_retention_hits, 1);
    });
}

fn tuple_ref(process: &mut Process, schema_id: u32, fields: &[AnyValue]) -> AnyValueRef {
    let tuple = process.heap.alloc_struct(schema_id);
    for (index, field) in fields.iter().enumerate() {
        let field = process.heap.box_any_value_ref(*field);
        let object = AnyValueRef::from_heap_object(ValueKind::STRUCT, tuple as *const u8).expect("tuple object");
        unsafe {
            process
                .heap
                .write_struct_field_ref(object, (index * 8) as u32, field)
                .expect("tuple field");
        }
    }
    AnyValueRef::from_heap_object(ValueKind::STRUCT, tuple as *const u8).expect("tuple object")
}

#[test]
fn tuple_primitives_answer_for_every_value_they_are_handed() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let pair = schemas.borrow_mut().register(Schema::tuple_of_arity(2));
    let named = schemas.borrow_mut().register(Schema::named_struct(
        crate::module_name::ModuleName::from_segments(vec!["Point".to_string()]),
        ["x".to_string(), "y".to_string()],
    ));
    let mut process = Box::new(Process::new(schemas));
    let process_ptr: *mut Process = &mut *process;
    let tuple = tuple_ref(&mut process, pair, &[AnyValue::int(7), AnyValue::int(8)]);
    let record = tuple_ref(&mut process, named, &[AnyValue::int(1), AnyValue::int(2)]);
    let integer = process.heap.box_any_value_ref(AnyValue::int(5));

    assert_eq!(fz_tuple_size(process_ptr, tuple.raw_word()), 2);
    assert_eq!(fz_tuple_size(process_ptr, record.raw_word()), -1);
    assert_eq!(fz_tuple_size(process_ptr, integer.raw_word()), -1);

    let second = AnyValueRef::from_raw_word(fz_tuple_elem(process_ptr, tuple.raw_word(), 1)).expect("element ref");
    assert_eq!(second.load_int(), Ok(8));
    for outside in [
        (tuple.raw_word(), 2),
        (tuple.raw_word(), -1),
        (record.raw_word(), 0),
        (integer.raw_word(), 0),
    ] {
        let answer = AnyValueRef::from_raw_word(fz_tuple_elem(process_ptr, outside.0, outside.1)).expect("nil ref");
        assert_eq!(
            answer.raw_word(),
            nil_atom_ref().raw_word(),
            "outside the tuple the answer is nil"
        );
    }
}

#[test]
fn list_length_counts_a_proper_list_and_refuses_every_other_value() {
    with_process(|process| {
        let mut list = AnyValueRef::empty_list();
        assert_eq!(fz_list_length(list.raw_word()), 0);
        for head in [3, 2, 1] {
            list = process.heap.alloc_list_cons_int(head, list).expect("cons");
        }
        assert_eq!(fz_list_length(list.raw_word()), 3);

        let integer = process.heap.box_any_value_ref(AnyValue::int(5));
        assert_eq!(fz_list_length(integer.raw_word()), -1);
    });
}

fn binary_bytes(word: u64) -> Vec<u8> {
    let p = bitstring_like_word(word).expect("a binary");
    unsafe { std::slice::from_raw_parts(bitstring_byte_ptr(p), (bitstring_bit_len(p) / 8) as usize).to_vec() }
}

fn list_of_binaries(mut word: u64) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    loop {
        let list = AnyValueRef::from_raw_word(word).expect("a list");
        if list.is_empty_list() {
            return out;
        }
        out.push(binary_bytes(list_head_ref(list).expect("head").raw_word()));
        word = list_tail_ref(list).expect("tail").raw_word();
    }
}

#[test]
fn system_argv_lists_each_driver_argument_as_a_binary_of_its_exact_bytes() {
    let argv = Argv::new(vec![
        b"--flag=1".to_vec(),
        Vec::new(),
        vec![0xff, 0xfe],
        "é ü".as_bytes().to_vec(),
    ]);
    with_process(|process| {
        let mut ctx = ExecCtx {
            argv: &argv,
            ..ExecCtx::empty()
        };
        process.ctx = &mut ctx;
        let list = fz_system_argv(process);
        assert_eq!(
            list_of_binaries(list),
            [
                b"--flag=1".to_vec(),
                Vec::new(),
                vec![0xff, 0xfe],
                "é ü".as_bytes().to_vec()
            ]
        );
    });
}

#[test]
fn system_argv_is_the_empty_list_when_the_driver_gave_no_arguments() {
    with_process(|process| {
        let mut ctx = ExecCtx::empty();
        process.ctx = &mut ctx;
        assert!(list_of_binaries(fz_system_argv(process)).is_empty());
    });
}

#[test]
fn a_module_name_atom_renders_as_its_alias_like_elixir_inspect() {
    with_process(|process| {
        let process_ptr = process as *mut Process;
        // A linked module seeds the reserved ids first; this bare process does not.
        for reserved in ["nil", "true", "false"] {
            process.node.intern_atom(reserved);
        }
        let render = |name: &str| render_value(process_ptr, AnyValue::atom(process.node.intern_atom(name)));

        assert_eq!(render("Elixir.Foo.Bar"), "Foo.Bar");
        assert_eq!(render("Elixir"), "Elixir");
        assert_eq!(
            render("Foo"),
            ":Foo",
            "a capitalised atom outside the Elixir root is a plain atom"
        );
        assert_eq!(render("ok"), ":ok");
    });
}

#[test]
fn float_prefix_reads_elixirs_prefix_and_reports_its_length() {
    let cases: &[(&str, Option<(f64, usize)>)] = &[
        ("1e3", Some((1000.0, 3))),
        ("1.", Some((1.0, 1))),
        ("1.e3", Some((1.0, 1))),
        (".5", None),
        ("1.5x", Some((1.5, 3))),
        ("+1.5", Some((1.5, 4))),
        ("-2.5e-3", Some((-0.0025, 7))),
        ("1e", Some((1.0, 1))),
        ("1e+", Some((1.0, 1))),
        ("1e+2x", Some((100.0, 4))),
        ("1_000.5", Some((1.0, 1))),
        ("", None),
        ("-", None),
        ("1e400", None),
        ("0.1", Some((0.1, 3))),
        ("1.5.5", Some((1.5, 3))),
    ];
    for (text, expected) in cases {
        assert_eq!(float_prefix(text.as_bytes()), *expected, "{text:?}");
    }
}

unsafe extern "C" {
    fn fopen(path: *const std::ffi::c_char, mode: *const std::ffi::c_char) -> *mut std::ffi::c_void;
    fn fclose(stream: *mut std::ffi::c_void) -> std::ffi::c_int;
}

fn lines_of(contents: &[u8]) -> Vec<Vec<u8>> {
    let path = std::env::temp_dir().join(format!("fz_read_line_{}_{}.tmp", std::process::id(), contents.len()));
    std::fs::write(&path, contents).expect("write temp file");
    let c_path = std::ffi::CString::new(path.to_str().expect("utf8 path")).expect("no NUL");
    let stream = unsafe { fopen(c_path.as_ptr(), c"rb".as_ptr()) };
    assert!(!stream.is_null(), "fopen {path:?}");
    let mut lines = Vec::new();
    loop {
        let line = read_line_bytes(stream);
        if line.is_empty() {
            break;
        }
        lines.push(line);
    }
    unsafe { fclose(stream) };
    std::fs::remove_file(&path).expect("remove temp file");
    lines
}

#[test]
fn read_line_folds_crlf_to_lf_and_keeps_blank_and_unterminated_lines() {
    let cases: &[(&[u8], &[&[u8]])] = &[
        (b"a\nb\n\nc", &[b"a\n", b"b\n", b"\n", b"c"]),
        (b"a\r\nb\n", &[b"a\n", b"b\n"]),
        (b"a\r", &[b"a\r"]),
        (b"a\r\r\n", &[b"a\r\n"]),
        (b"a\rb\n", &[b"a\rb\n"]),
        (b"\r\n", &[b"\n"]),
        (b"", &[]),
        (b"x", &[b"x"]),
    ];
    for (contents, expected) in cases {
        let expected: Vec<Vec<u8>> = expected.iter().map(|line| line.to_vec()).collect();
        assert_eq!(lines_of(contents), expected, "{contents:?}");
    }
}

#[test]
fn a_struct_answers_its_module_and_a_map_answers_its_struct_entry() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let named = schemas.borrow_mut().register(Schema::named_struct(
        crate::module_name::ModuleName::from_segments(vec!["Point".to_string()]),
        ["x".to_string()],
    ));
    let mut process = Box::new(Process::new(schemas));
    let process_ptr: *mut Process = &mut *process;
    let record = tuple_ref(&mut process, named, &[AnyValue::int(1)]);
    let key = process.node.intern_atom("__struct__");
    let module = process.node.intern_atom("Elixir.Oops");
    let map_bits = process
        .heap
        .alloc_map_slots(&[(AnyValue::atom(key), AnyValue::atom(module))]);
    let map = AnyValueRef::from_heap_object(
        ValueKind::MAP,
        crate::any_value::map_addr_from_tagged(map_bits).unwrap(),
    )
    .expect("map ref");

    let of_struct =
        AnyValueRef::from_raw_word(fz_struct_module(process_ptr, record.raw_word())).expect("struct answer");
    let of_map = AnyValueRef::from_raw_word(fz_struct_module(process_ptr, map.raw_word())).expect("map answer");

    assert_eq!(
        of_struct.load_atom(),
        Ok(process.node.intern_atom("Elixir.Point") as u64)
    );
    assert_eq!(of_map.load_atom(), Ok(module as u64));
}

#[test]
fn try_push_stores_the_closure_reference_word_codegen_emits_and_try_pop_removes_it() {
    with_process(|process| {
        let template = process
            .heap
            .alloc_closure_slots(crate::any_value::ClosureDenotationId::INTERNAL, 0, 1, 0);
        let template_addr = crate::any_value::closure_addr_from_tagged(template).expect("a closure");
        let template_ref = AnyValueRef::from_heap_object(ValueKind::CLOSURE, template_addr).expect("a closure ref");
        let handler = Handler::Closure(ClosureRef::new(template_ref));

        fz_try_push(process, template_ref.raw_word());
        fz_try_pop(process);
        fz_try_push(process, template_ref.raw_word());

        assert_eq!(
            process.handlers,
            [handler],
            "the handler holds the closure reference as codegen emitted it"
        );

        fz_try_pop(process);

        assert!(process.handlers.is_empty());
    });
}
