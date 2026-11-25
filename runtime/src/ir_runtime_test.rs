use super::*;
use crate::any_value::{
    AnyValue, AnyValueRef, EMPTY_LIST_BITS, SlotLayout, ValueKind, closure_size_for_count, heap_object_word,
    list_addr_from_tagged, map_count, map_entry, struct_is_shared,
};
use crate::bits::{BINVIEW_BYTES, Bin};
use crate::exec_ctx::Argv;
use crate::heap::{Schema, SchemaRegistry};
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

/// Intent: `abs` and the float-to-integer conversions report failure exactly
/// where the answer does not fit a 64-bit integer, and answer as Elixir does
/// everywhere else: half away from zero, and `-0.0` as zero.
#[test]
fn abs_and_float_conversions_fail_only_outside_the_integer_range() {
    let ok = |result| FzIntegerArithmeticResult { result, failed: 0 };
    let failed = FzIntegerArithmeticResult { result: 0, failed: 1 };
    assert_eq!(fz_op_abs_i(-3), ok(3));
    assert_eq!(fz_op_abs_i(i64::MAX), ok(i64::MAX));
    assert_eq!(
        fz_op_abs_i(i64::MIN),
        FzIntegerArithmeticResult {
            result: i64::MIN,
            failed: 1
        }
    );
    assert_eq!(fz_op_abs_f(-0.0).to_bits(), 0.0f64.to_bits());
    assert_eq!(fz_op_abs_f(-2.5), 2.5);

    assert_eq!(fz_op_round_f(2.5), ok(3));
    assert_eq!(fz_op_round_f(-2.5), ok(-3));
    assert_eq!(fz_op_round_f(0.5), ok(1));
    assert_eq!(fz_op_round_f(-0.5), ok(-1));
    assert_eq!(fz_op_round_f(-0.0), ok(0));
    assert_eq!(fz_op_trunc_f(-2.7), ok(-2));
    assert_eq!(fz_op_trunc_f(-0.5), ok(0));
    assert_eq!(fz_op_floor_f(-2.5), ok(-3));
    assert_eq!(fz_op_floor_f(2.5), ok(2));
    assert_eq!(fz_op_ceil_f(-0.5), ok(0));
    assert_eq!(fz_op_ceil_f(2.5), ok(3));

    assert_eq!(fz_op_trunc_f(-9223372036854775808.0), ok(i64::MIN));
    assert_eq!(fz_op_trunc_f(9223372036854774784.0), ok(9223372036854774784));
    for outside in [9223372036854775808.0, -9223372036854777856.0, 1.0e300, -1.0e300] {
        assert_eq!(fz_op_trunc_f(outside), failed, "{outside}");
        assert_eq!(fz_op_round_f(outside), failed, "{outside}");
        assert_eq!(fz_op_floor_f(outside), failed, "{outside}");
        assert_eq!(fz_op_ceil_f(outside), failed, "{outside}");
    }
    assert_eq!(fz_op_round_f(9223372036854775807.5), failed);
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

        let [b_word, b_kind] = stored(AnyValue::from_ref(AnyValueRef::from_raw_word(b).unwrap()).unwrap());
        let [a_word, a_kind] = stored(AnyValue::from_ref(AnyValueRef::from_raw_word(a).unwrap()).unwrap());
        let [c_word, c_kind] = stored(AnyValue::from_ref(AnyValueRef::from_raw_word(c).unwrap()).unwrap());

        assert_eq!(fz_value_eq_ref(process_ptr, a_word, a_kind, b_word, b_kind), 1);
        assert_eq!(fz_value_eq_ref(process_ptr, a_word, a_kind, c_word, c_kind), 0);
    });
}

#[test]
fn system_alloc_stats_returns_pre_materialization_snapshot() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut proc_owned = Process::new(schemas);
    let process = &mut proc_owned;
    let _ = process.heap.alloc_list_cons_slot(AnyValue::int(1), EMPTY_LIST_BITS);

    let stats_ref = fz_system_alloc_stats(process);
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

    // The map the call returns is allocated after its snapshot: the heap now
    // counts the map's own objects, which the returned `map_allocs` and
    // `allocs` did not. How many objects the map takes depends on its size, so
    // the test states the relation, not a count.
    let after = process.heap.node.alloc_stats();
    assert_eq!(after.list_cons.allocs, 1);
    assert!(
        after.map.allocs >= 1,
        "the returned map is allocated after the snapshot"
    );
    assert_eq!(
        after.total.allocs,
        after.list_cons.allocs + after.map.allocs,
        "the cons and the map's objects are the only allocations"
    );
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
fn utf8_scalar_at_reads_every_unicode_scalar_at_any_bit_offset() {
    let mut buffer = [0; 4];
    for scalar in 0..=char::MAX as u32 {
        let Some(codepoint) = char::from_u32(scalar) else {
            continue;
        };
        let encoded = codepoint.encode_utf8(&mut buffer).as_bytes();
        let bits = encoded.len() as u64 * 8;
        assert_eq!(utf8_scalar_at(encoded, 0, bits), Some((scalar, bits)), "U+{scalar:04X}");
    }
    // U+00E9 (C3 A9) written after three bits of padding.
    let unaligned = [0b0001_1000, 0b0111_0101, 0b0010_0000];
    assert_eq!(utf8_scalar_at(&unaligned, 3, 19), Some((0xe9, 16)));
    assert_eq!(
        utf8_scalar_at(&unaligned, 3, 18),
        None,
        "a truncated bit is a truncated sequence"
    );
}

#[test]
fn utf8_scalar_at_misses_what_elixir_rejects() {
    let rejected: &[&[u8]] = &[
        &[],
        &[0x80],
        &[0xc0, 0x80],
        &[0xe0, 0x80, 0x80],
        &[0xed, 0xa0, 0x80],
        &[0xf4, 0x90, 0x80, 0x80],
        &[0xf8, 0x88, 0x80, 0x80, 0x80],
        &[0xe2, 0x82],
    ];
    for bytes in rejected {
        assert_eq!(
            utf8_scalar_at(bytes, 0, bytes.len() as u64 * 8),
            None,
            "bytes={bytes:?}"
        );
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
    let int_ref = AnyValueRef::from_scalar_slot(ValueKind::INT, &int_slot).expect("int ref");
    let float_ref = AnyValueRef::from_scalar_slot(ValueKind::FLOAT, &float_slot).expect("float ref");
    let atom_ref = AnyValueRef::atom(17);

    assert_eq!(fz_type_of(int_ref.raw_word()), ValueKind::INT.tag());
    assert_eq!(fz_ref_load_int(int_ref.raw_word()), -42);
    assert_eq!(fz_ref_load_float(float_ref.raw_word()), 3.5);
    assert_eq!(fz_ref_load_atom(atom_ref.raw_word()), 17);
}

/// A value as the two words an entry takes it in: its stored word and kind.
fn stored(value: AnyValue) -> [u64; 2] {
    let Stored { word, kind } = Stored::of(value);
    [word, kind]
}

#[test]
fn a_put_binds_a_key_to_a_value_each_given_as_word_and_kind() {
    with_process(|process| {
        let key = AnyValue::atom(process.node.intern_atom("key"));
        let [key_word, key_kind] = stored(key);
        let [value_word, value_kind] = stored(AnyValue::int(42));
        let map = fz_map_put(
            process,
            fz_map_empty(process),
            key_word,
            key_kind,
            value_word,
            value_kind,
        );
        assert_eq!(fz_ref_load_int(fz_map_get_ref(process, map, key_word, key_kind)), 42);
    });
}

#[test]
fn a_put_of_an_integer_or_a_float_allocates_only_the_map() {
    with_process(|process| {
        let key = AnyValue::atom(process.node.intern_atom("key"));
        let [key_word, key_kind] = stored(key);
        let empty = fz_map_empty(process);
        for value in [AnyValue::int(i64::MAX), AnyValue::float(2.5)] {
            let before = process.heap.node.alloc_stats();
            let [value_word, value_kind] = stored(value);
            let _ = fz_map_put(process, empty, key_word, key_kind, value_word, value_kind);
            let after = process.heap.node.alloc_stats();
            assert_eq!(
                after.total.allocs - before.total.allocs,
                1,
                "a scalar crosses as its word, so the put makes the map and no box for {value:?}"
            );
        }
    });
}

/// Every comparison entry answers for a pair given as two (word, kind) pairs,
/// and none boxes an operand.
#[test]
fn a_comparison_takes_each_operand_as_word_and_kind_and_boxes_nothing() {
    with_process(|process| {
        let atom = AnyValue::atom(process.node.intern_atom("a"));
        let other_atom = AnyValue::atom(process.node.intern_atom("b"));
        let one = AnyValue::int(1);
        let one_float = AnyValue::float(1.0);
        let cases = [
            // (left, right, `==`, `===`, ordering under widening)
            (one, one, true, true, 0),
            (one, one_float, true, false, 0),
            (one_float, one, true, false, 0),
            (one, AnyValue::float(2.5), false, false, -1),
            (AnyValue::float(2.5), one, false, false, 1),
            (one, atom, false, false, -1),
            (atom, one, false, false, 1),
            (atom, other_atom, false, false, -1),
            (atom, atom, true, true, 0),
        ];
        for (left, right, loose, strict, ordering) in cases {
            let [lw, lk] = stored(left);
            let [rw, rk] = stored(right);
            let before = process.heap.node.alloc_stats();
            let answers = [
                fz_value_eq_widening_ref(process, lw, lk, rw, rk),
                fz_value_eq_ref(process, lw, lk, rw, rk),
                fz_op_eq(process, lw, lk, rw, rk),
                fz_op_neq(process, lw, lk, rw, rk),
                fz_op_identical(process, lw, lk, rw, rk),
                fz_op_not_identical(process, lw, lk, rw, rk),
            ];
            let compared = fz_value_cmp_ref(process, lw, lk, rw, rk);
            let after = process.heap.node.alloc_stats();
            assert_eq!(
                answers,
                [
                    u64::from(loose),
                    u64::from(strict),
                    u64::from(loose),
                    u64::from(!loose),
                    u64::from(strict),
                    u64::from(!strict)
                ],
                "{left:?} against {right:?}"
            );
            assert_eq!(compared, ordering, "{left:?} against {right:?}");
            assert_eq!(
                after.total.allocs, before.total.allocs,
                "{left:?} and {right:?} cross as words, unboxed"
            );
        }
    });
}

#[test]
fn inspect_takes_its_value_as_word_and_kind_and_boxes_nothing() {
    with_process(|process| {
        let options = AnyValueRef::empty_list().raw_word();
        for (value, text) in [
            (AnyValue::int(i64::MAX), "9223372036854775807"),
            (AnyValue::float(2.5), "2.5"),
            (AnyValue::atom(NIL_ATOM_ID), "nil"),
        ] {
            let [word, kind] = stored(value);
            let before = process.heap.node.alloc_stats();
            let plain = fz_inspect(process, word, kind);
            let limited = fz_inspect_with(process, word, kind, options);
            let after = process.heap.node.alloc_stats();
            for rendered in [plain, limited] {
                let rendered = any_value_from_ref_word(rendered, "inspect");
                assert_eq!(
                    crate::any_value::debug::render_value(process, rendered),
                    format!("\"{text}\""),
                    "{value:?}"
                );
            }
            assert_eq!(
                after.scalar_box.allocs, before.scalar_box.allocs,
                "{value:?} crosses as its word, unboxed"
            );
        }
    });
}

#[test]
fn a_struct_field_and_a_closure_capture_take_their_value_as_word_and_kind_and_box_nothing() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let pair = schemas.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut process = Box::new(Process::new(schemas));
    let process: &mut Process = &mut process;
    let child = tuple_ref(process, pair, &[AnyValue::int(1), AnyValue::int(2)]);
    let values = [
        AnyValue::int(i64::MAX),
        AnyValue::float(2.5),
        AnyValue::atom(7),
        AnyValue::from_ref(child).expect("child"),
    ];
    let object = process.heap.alloc_struct(pair);
    let object_ref = AnyValueRef::from_heap_object(ValueKind::STRUCT, object as *const u8).expect("object");
    let layout = SlotLayout::of(2);
    let closure_bits =
        process
            .heap
            .alloc_closure_slots(crate::any_value::ClosureDenotationId::user(0), 0, values.len(), 0);
    let closure_ref = AnyValueRef::from_heap_object(
        ValueKind::CLOSURE,
        closure_addr_from_tagged(closure_bits).expect("closure addr"),
    )
    .expect("closure ref");
    for (index, value) in values.into_iter().enumerate() {
        let [word, kind] = stored(value);
        let slot = index % 2;
        let before = process.heap.node.alloc_stats();
        fz_struct_store_ref(
            process,
            object_ref.raw_word(),
            SlotLayout::slot_offset(slot) as u32,
            layout.kind_offset(slot) as u32,
            word,
            kind,
        );
        fz_closure_set_capture_ref(process, closure_ref.raw_word(), index as u64, word, kind);
        let after = process.heap.node.alloc_stats();
        assert_eq!(
            after.total.allocs, before.total.allocs,
            "{value:?} is stored as its word and kind, boxed nowhere"
        );
        assert_eq!(
            process.heap.read_field_slot(object, (slot * 8) as u32),
            value,
            "the struct field reads back {value:?}"
        );
        assert_eq!(
            any_value_from_ref_word(
                fz_closure_get_capture_ref(closure_ref.raw_word(), index as u64),
                "capture"
            ),
            value,
            "the capture reads back {value:?}"
        );
    }
    assert!(is_shared(child), "a struct stored into a struct field is shared");
}

#[test]
fn a_lookup_takes_its_key_as_word_and_kind_and_boxes_nothing() {
    with_process(|process| {
        let found = AnyValue::atom(process.node.intern_atom("found"));
        let [found_word, found_kind] = stored(found);
        let keys = [AnyValue::int(i64::MAX), AnyValue::float(2.5), AnyValue::atom(7)];
        let map = keys.iter().fold(fz_map_empty(process), |map, key| {
            let [key_word, key_kind] = stored(*key);
            fz_map_put(process, map, key_word, key_kind, found_word, found_kind)
        });
        for key in keys {
            let [key_word, key_kind] = stored(key);
            let before = process.heap.node.alloc_stats();
            let got = fz_map_get_ref(process, map, key_word, key_kind);
            assert_eq!(any_value_from_ref_word(got, "got"), found, "Map.get finds {key:?}");
            assert_eq!(
                fz_map_has_key(process, map, key_word, key_kind),
                1,
                "Map.has_key? finds {key:?}"
            );
            let matched = fz_matcher_map_get_ref(process, map, key_word, key_kind);
            assert_eq!(
                any_value_from_ref_word(matched, "matched"),
                found,
                "a pinned key matches {key:?}"
            );
            let without = fz_map_delete(process, map, key_word, key_kind);
            assert_eq!(fz_map_count(process, without), 2, "Map.delete drops {key:?}");
            let after = process.heap.node.alloc_stats();
            assert_eq!(
                after.total.allocs - before.total.allocs,
                1,
                "only the map Map.delete answers is made; {key:?} crosses as its word, unboxed"
            );
        }
        let [missing_word, missing_kind] = stored(AnyValue::int(8));
        assert_eq!(
            any_value_from_ref_word(fz_map_get_ref(process, map, missing_word, missing_kind), "miss"),
            AnyValue::nil_atom()
        );
        assert_eq!(fz_map_has_key(process, map, missing_word, missing_kind), 0);
        assert_eq!(
            fz_type_of(fz_matcher_map_get_ref(process, map, missing_word, missing_kind)),
            ValueKind::NULL.tag()
        );
    });
}

#[test]
#[should_panic(expected = "fz_ref_load_int")]
fn loading_an_int_from_a_map_value_that_is_an_atom_panics() {
    with_process(|process| {
        let [key_word, key_kind] = stored(AnyValue::atom(process.node.intern_atom("key")));
        let [value_word, value_kind] = stored(AnyValue::atom(process.node.intern_atom("value")));
        let map = fz_map_put(
            process,
            fz_map_empty(process),
            key_word,
            key_kind,
            value_word,
            value_kind,
        );

        let _ = ref_load_int_impl(fz_map_get_ref(process, map, key_word, key_kind));
    });
}

/// The `fz_op_*_bb` functions of two binaries agree, for every pair and every
/// operator, with the generic comparator the other value kinds go through: the
/// bit-level term order and equality, a prefix before what it begins, and the
/// padding of a partial last byte ignored. `===` and `!==` take `==` and `!=`.
#[test]
fn binary_comparison_functions_agree_with_the_generic_comparator() {
    with_process(|process| {
        let samples: [(&[u8], u64); 8] = [
            (b"", 0),
            (b"a", 8),
            (b"ab", 16),
            (b"abc", 24),
            (b"b", 8),
            (&[0b1000_0000], 1),
            (&[0b1000_1111], 1),
            (&[0b1000_0000], 4),
        ];
        let words: Vec<u64> = samples
            .iter()
            .map(|(bytes, bits)| process.heap.alloc_bitstring(bytes, *bits).ref_word().raw_word())
            .collect();
        let kind = ValueKind::BITSTRING.tag() as u64;
        for &left in &words {
            for &right in &words {
                let ordering = fz_value_cmp_ref(process, left, kind, right, kind);
                let equal = fz_value_eq_widening_ref(process, left, kind, right, kind) != 0;
                let answers = [
                    fz_op_eq_bb(process, left, right),
                    fz_op_neq_bb(process, left, right),
                    fz_op_lt_bb(process, left, right),
                    fz_op_lte_bb(process, left, right),
                    fz_op_gt_bb(process, left, right),
                    fz_op_gte_bb(process, left, right),
                ];
                assert_eq!(
                    answers,
                    [equal, !equal, ordering < 0, ordering <= 0, ordering > 0, ordering >= 0].map(u64::from),
                    "{left:#x} against {right:#x}"
                );
            }
        }
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
            assert_eq!(Bin::of_binary(bits).bit_len(), 24);
            let bp = Bin::of_binary(bits).ptr();
            assert_eq!(from_raw_parts(bp, 3), &bytes);
        }
    });
}

/// `fz_alloc_binview_from_static` retains the static
/// SharedBin's anchor (climbing 1 → 2), allocates a BinView that
/// owns the new edge, and returns it as a tagged BinView pointer. When
/// the holding heap drops, the anchor is preserved (refcount stays
/// at 1) — the static SharedBin lives forever.
#[test]
fn alloc_binview_from_static_preserves_anchor() {
    use crate::bits::SharedBin;
    use crate::sync::{AtomicUsize, Ordering};
    // Construct a "static" SharedBin by hand. Its destructor is a
    // noop pointer so the test owns its lifetime explicitly.
    static PAYLOAD: [u8; 8] = [0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe];
    unsafe extern "C" fn noop(_: *mut SharedBin) {}
    let mut sb = SharedBin {
        refcount: AtomicUsize::new(1),
        bytes_ptr: PAYLOAD.as_ptr(),
        bytes_len: PAYLOAD.len(),
        destructor: noop,
        room: 0,
    };
    let sb_ptr = &mut sb as *mut SharedBin;
    with_process(|process| {
        let ref_word = fz_alloc_binview_from_static(process, sb_ptr as u64, 64);
        let binview_ref = AnyValueRef::from_raw_word(ref_word).expect("binview ref");
        let addr = binview_ref.binview_addr().expect("binview addr");
        let bits = heap_object_word(addr, ValueKind::BINVIEW);
        unsafe {
            assert_eq!(binview_ref.tag(), ValueKind::BINVIEW);
            assert_eq!(object_size(bits), BINVIEW_BYTES);
            assert_eq!(Bin::of_binary(bits).bit_len(), 64);
            let bp = Bin::of_binary(bits).ptr();
            assert_eq!(from_raw_parts(bp, 8), &PAYLOAD[..]);
            // retain climbed anchor 1 -> 2.
            assert_eq!(sb.refcount.load(Ordering::Relaxed), 2);
        }
        // When the with_process drops the temp Process, the heap drop
        // releases the BinView's edge, returning refcount to the
        // anchor value 1.
    });
    assert_eq!(sb.refcount.load(Ordering::Relaxed), 1, "anchor preserved");
}

/// Large (> threshold) payload routes through BinView / SharedBin.
#[test]
fn alloc_bitstring_const_large_payload_is_binview() {
    with_process(|process| {
        let payload: Vec<u8> = (0..70u8).collect(); // 70 > SHARED_BIN_THRESHOLD_BYTES (64)
        let ref_word = fz_alloc_bitstring_const(process, payload.as_ptr() as u64, payload.len() as u64, 70 * 8);
        let binview_ref = AnyValueRef::from_raw_word(ref_word).expect("binview ref");
        let addr = binview_ref.binview_addr().expect("binview addr");
        let bits = heap_object_word(addr, ValueKind::BINVIEW);
        unsafe {
            assert_eq!(binview_ref.tag(), ValueKind::BINVIEW);
            assert_eq!(object_size(bits), BINVIEW_BYTES);
            assert_eq!(Bin::of_binary(bits).bit_len(), 70 * 8);
            let bp = Bin::of_binary(bits).ptr();
            assert_eq!(from_raw_parts(bp, payload.len()), payload.as_slice());
        }
    });
}

fn list_ref_from_bits(bits: u64) -> AnyValueRef {
    let addr = list_addr_from_tagged(bits).expect("list addr");
    AnyValueRef::from_heap_object(ValueKind::LIST, addr).expect("list ref")
}

/// The word a list `bits` is passed as to an entry that takes a tail: its address.
fn list_tail_word(bits: u64) -> u64 {
    list_addr_from_tagged(bits).expect("list addr") as u64
}

#[test]
fn list_retention_decodes_a_dynamic_head_ref_once() {
    let reuse = |process: &mut Process, source: u64, head_ref: u64, tail: u64, permission: u64| {
        let head = any_value_ref_from_word(head_ref, "head");
        let tail = Stored::of(AnyValue::from_ref(any_value_ref_from_word(tail, "tail")).expect("tail value"));
        fz_list_reuse_or_cons_parts(
            process,
            source,
            head.storage_raw().expect("list head storage"),
            u64::from(head.tag().tag()),
            tail.word,
            tail.kind,
            permission,
        )
    };
    with_process(|process| {
        let source = process.heap.alloc_list_cons_slot(AnyValue::int(42), EMPTY_LIST_BITS);
        let source_ref = list_ref_from_bits(source);
        let head_ref = fz_list_head_ref(source_ref.raw_word());
        let tail_ref = fz_list_tail_ref(source_ref.raw_word());
        process
            .heap
            .mark_published_ref_aliased(source_ref)
            .expect("share source");
        let result = reuse(process, source_ref.raw_word(), head_ref, tail_ref, 0);
        assert_eq!(
            result,
            source_ref.raw_word(),
            "unchanged shared cell survives a dynamic head"
        );
        assert_eq!((process.list_retention_attempts, process.list_retention_hits), (1, 1));
        let other = process.heap.alloc_list_cons_slot(AnyValue::int(7), EMPTY_LIST_BITS);
        let changed_head = fz_list_head_ref(list_ref_from_bits(other).raw_word());
        let result = reuse(process, source_ref.raw_word(), changed_head, tail_ref, 1);
        assert_ne!(result, source_ref.raw_word(), "shared changed source allocates");
        assert_eq!((process.list_retention_attempts, process.list_retention_hits), (2, 1));
        for permission in [0, 1] {
            let source = process.heap.alloc_list_cons_slot(AnyValue::int(42), EMPTY_LIST_BITS);
            let source = list_ref_from_bits(source).raw_word();
            let result = reuse(process, source, changed_head, tail_ref, permission);
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
            list_tail_word(new_tail),
            ValueKind::LIST.tag() as u64,
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
            list_tail_word(new_tail),
            ValueKind::LIST.tag() as u64,
            1,
        );

        assert_ne!(fallback_word, source_ref.raw_word());
        assert_eq!(process.list_retention_attempts, 2);
        assert_eq!(process.list_retention_hits, 1);
    });
}

fn point_process() -> (Box<Process>, u32) {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let point = schemas.borrow_mut().register(Schema::named_struct(
        crate::module_name::ModuleName::from_segments(vec!["Point".to_string()]),
        ["x".to_string(), "y".to_string()],
    ));
    (Box::new(Process::new(schemas)), point)
}

fn is_shared(value: AnyValueRef) -> bool {
    unsafe { struct_is_shared(value.struct_addr().expect("struct")) }
}

#[test]
fn a_struct_update_rewrites_its_base_only_when_permitted_and_unshared() {
    let (mut process, point) = point_process();
    let process_ptr: *mut Process = &mut *process;
    let unshared = tuple_ref(&mut process, point, &[AnyValue::int(1), AnyValue::int(2)]);
    let rewritten = fz_struct_reuse_or_copy(process_ptr, unshared.raw_word(), 2, 1);
    assert_eq!(
        rewritten,
        unshared.raw_word(),
        "nothing else holds the base, so it is the update"
    );

    let refused = fz_struct_reuse_or_copy(process_ptr, unshared.raw_word(), 2, 0);
    assert_ne!(
        refused,
        unshared.raw_word(),
        "without the compiler's permission the update copies"
    );

    let shared = tuple_ref(&mut process, point, &[AnyValue::int(3), AnyValue::int(4)]);
    fz_mark_published_ref_aliased(process_ptr, shared.raw_word());
    let copied = fz_struct_reuse_or_copy(process_ptr, shared.raw_word(), 2, 1);
    assert_ne!(
        copied,
        shared.raw_word(),
        "a shared base is copied even with permission"
    );
    let copy = AnyValueRef::from_raw_word(copied).expect("copy ref");
    assert!(!is_shared(copy), "the copy is fresh, so the next update may rewrite it");
    assert_eq!(
        process.heap.read_struct_field_ref(copy, 8).and_then(|y| y.load_int()),
        Ok(4),
        "the copy keeps the fields the update does not replace"
    );
    assert_eq!(
        (process.struct_retention_attempts, process.struct_retention_hits),
        (3, 1)
    );
}

#[test]
fn a_struct_becomes_shared_wherever_a_second_holder_can_appear() {
    let (mut process, point) = point_process();
    let process_ptr: *mut Process = &mut *process;
    let fresh = tuple_ref(&mut process, point, &[AnyValue::int(1), AnyValue::int(2)]);
    assert!(!is_shared(fresh), "a struct is born unshared");

    let passed = tuple_ref(&mut process, point, &[AnyValue::int(1), AnyValue::int(2)]);
    fz_mark_published_ref_aliased(process_ptr, passed.raw_word());
    assert!(is_shared(passed), "a struct passed to a call the caller still holds");

    let field = tuple_ref(&mut process, point, &[AnyValue::int(1), AnyValue::int(2)]);
    let outer = process.heap.alloc_struct(point);
    let layout = SlotLayout::of(2);
    let [field_word, field_kind] = stored(AnyValue::from_ref(field).expect("field"));
    fz_struct_store_ref(
        process_ptr,
        AnyValueRef::from_heap_object(ValueKind::STRUCT, outer as *const u8)
            .expect("outer")
            .raw_word(),
        SlotLayout::slot_offset(0) as u32,
        layout.kind_offset(0) as u32,
        field_word,
        field_kind,
    );
    assert!(is_shared(field), "a struct stored into another struct");

    let head = tuple_ref(&mut process, point, &[AnyValue::int(1), AnyValue::int(2)]);
    process
        .heap
        .alloc_list_cons_any(AnyValue::from_ref(head).expect("head"), AnyValue::EmptyList);
    assert!(is_shared(head), "a struct stored as a list head");

    let kept = tuple_ref(&mut process, point, &[AnyValue::int(1), AnyValue::int(2)]);
    let mut roots = [kept];
    process.collect_stats(&mut roots);
    assert!(
        is_shared(roots[0]),
        "a struct a collection keeps is old, and old data is never written"
    );
    let after = fz_struct_reuse_or_copy(process_ptr, roots[0].raw_word(), 2, 1);
    assert_ne!(after, roots[0].raw_word(), "so an update of it copies");
}

fn tuple_ref(process: &mut Process, schema_id: u32, fields: &[AnyValue]) -> AnyValueRef {
    let tuple = process.heap.alloc_struct(schema_id);
    for (index, field) in fields.iter().enumerate() {
        unsafe { process.heap.write_field_slot(tuple, (index * 8) as u32, *field) };
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
fn tuple_put_copies_the_tuple_and_leaves_the_original_alone() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let pair = schemas.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut process = Box::new(Process::new(schemas));
    let process_ptr: *mut Process = &mut *process;
    let tuple = tuple_ref(&mut process, pair, &[AnyValue::int(7), AnyValue::int(8)]);
    let list = process
        .heap
        .alloc_list_cons_int(3, AnyValueRef::empty_list())
        .expect("list");
    let integer = process.heap.box_any_value_ref(AnyValue::int(5));

    let replaced =
        AnyValueRef::from_raw_word(fz_tuple_put(process_ptr, tuple.raw_word(), 1, list.raw_word())).expect("tuple ref");
    assert_ne!(replaced.raw_word(), tuple.raw_word(), "the update is a copy");
    assert_eq!(fz_tuple_size(process_ptr, replaced.raw_word()), 2);
    let read = |tuple: AnyValueRef, index| {
        AnyValueRef::from_raw_word(fz_tuple_elem(process_ptr, tuple.raw_word(), index)).expect("element")
    };
    assert_eq!(read(replaced, 0).load_int(), Ok(7), "the other field is kept");
    assert_eq!(
        read(replaced, 1).raw_word(),
        list.raw_word(),
        "the list is stored and readable"
    );
    assert_eq!(read(tuple, 1).load_int(), Ok(8), "the original keeps its field");

    let again = AnyValueRef::from_raw_word(fz_tuple_put(process_ptr, replaced.raw_word(), 0, integer.raw_word()))
        .expect("tuple ref");
    assert_eq!(read(again, 0).load_int(), Ok(5));
    assert_eq!(read(replaced, 0).load_int(), Ok(7));

    for outside in [(tuple.raw_word(), 2), (tuple.raw_word(), -1), (integer.raw_word(), 0)] {
        assert_eq!(
            fz_tuple_put(process_ptr, outside.0, outside.1, integer.raw_word()),
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
    unsafe { Bin::of_binary(word) }.bytes().to_vec()
}

fn alloc_binary(process: &mut Process, bytes: &[u8]) -> u64 {
    process
        .heap
        .alloc_bitstring(bytes, (bytes.len() * 8) as u64)
        .ref_word()
        .raw_word()
}

#[test]
fn binary_copy_writes_the_repetitions_into_one_inline_binary() {
    with_process(|process| {
        let subject = alloc_binary(process, b"ab");
        let copy = fz_binary_copy(process, subject, 3);
        assert_eq!(binary_bytes(copy), b"ababab");
        assert_eq!(process.heap.node.alloc_stats().shared_bin.allocs, 0);
    });
}

#[test]
fn binary_copy_of_a_large_result_is_one_shared_buffer_of_the_exact_size() {
    with_process(|process| {
        let subject = alloc_binary(process, &[5u8; 100]);
        let before = process.heap.node.alloc_stats().shared_bin.bytes;
        let copy = fz_binary_copy(process, subject, 7);
        assert_eq!(binary_bytes(copy), vec![5u8; 700]);
        assert_eq!(process.heap.node.alloc_stats().shared_bin.bytes - before, 700);
    });
}

#[test]
fn binary_copy_by_zero_or_of_nothing_is_the_empty_binary() {
    with_process(|process| {
        let subject = alloc_binary(process, b"abc");
        assert_eq!(binary_bytes(fz_binary_copy(process, subject, 0)), b"");
        let empty = alloc_binary(process, b"");
        assert_eq!(binary_bytes(fz_binary_copy(process, empty, 9)), b"");
    });
}

#[test]
fn referenced_size_of_an_inline_binary_is_its_own_size() {
    with_process(|process| {
        let subject = alloc_binary(process, b"hello");
        assert_eq!(fz_binary_referenced_size(subject), 5);
    });
}

#[test]
fn referenced_size_of_a_view_is_the_whole_buffer() {
    with_process(|process| {
        let whole = alloc_binary(process, &[1u8; 200]);
        let view = unsafe { process.heap.slice(whole, 400, 1200) };
        let view = view.ref_word().raw_word();
        assert_eq!(binary_bytes(view).len(), 150);
        assert_eq!(fz_binary_referenced_size(view), 200);
        assert_eq!(fz_binary_referenced_size(whole), 200);
    });
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
    fn fgetc(stream: *mut std::ffi::c_void) -> std::ffi::c_int;
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

fn rest_of(contents: &[u8], skipped: usize) -> Vec<u8> {
    let path = std::env::temp_dir().join(format!("fz_read_rest_{}_{}.tmp", std::process::id(), contents.len()));
    std::fs::write(&path, contents).expect("write temp file");
    let c_path = std::ffi::CString::new(path.to_str().expect("utf8 path")).expect("no NUL");
    let stream = unsafe { fopen(c_path.as_ptr(), c"rb".as_ptr()) };
    assert!(!stream.is_null(), "fopen {path:?}");
    for _ in 0..skipped {
        assert_ne!(unsafe { fgetc(stream) }, -1, "skipped bytes exist");
    }
    let rest = read_rest_bytes(stream);
    unsafe { fclose(stream) };
    std::fs::remove_file(&path).expect("remove temp file");
    rest
}

fn pattern(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i % 251) as u8).collect()
}

#[test]
fn read_rest_returns_every_byte_at_and_around_a_block_boundary() {
    for len in [
        0,
        1,
        READ_BLOCK_BYTES - 1,
        READ_BLOCK_BYTES,
        READ_BLOCK_BYTES + 1,
        2 * READ_BLOCK_BYTES,
        4 * READ_BLOCK_BYTES + 1_000,
    ] {
        let contents = pattern(len);
        assert_eq!(rest_of(&contents, 0), contents, "{len} bytes");
    }
}

#[test]
fn read_rest_keeps_crlf_nul_and_high_bytes_and_starts_at_the_stream_position() {
    let contents = b"a\r\nb\0\xff\x80\r";
    assert_eq!(rest_of(contents, 0), contents);
    assert_eq!(rest_of(contents, 3), &contents[3..]);
    assert_eq!(rest_of(contents, contents.len()), b"");
}

#[test]
fn read_rest_entry_allocates_the_bytes_as_one_binary() {
    let contents = pattern(READ_BLOCK_BYTES + 1);
    let path = std::env::temp_dir().join(format!("fz_read_rest_entry_{}.tmp", std::process::id()));
    std::fs::write(&path, &contents).expect("write temp file");
    let c_path = std::ffi::CString::new(path.to_str().expect("utf8 path")).expect("no NUL");
    let stream = unsafe { fopen(c_path.as_ptr(), c"rb".as_ptr()) };
    assert!(!stream.is_null(), "fopen {path:?}");
    with_process(|process| {
        let binary = fz_file_read_rest(process, stream as u64);
        assert_eq!(unsafe { Bin::of_binary(binary) }.bytes(), contents.as_slice());
    });
    unsafe { fclose(stream) };
    std::fs::remove_file(&path).expect("remove temp file");
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

/// Compiled code calls `fz_handler_reserve` only when the handler stack is
/// full; the bytes it answers become the innermost record once compiled code
/// writes the record's trailer.
#[test]
fn handler_reserve_answers_the_bytes_that_become_the_innermost_record() {
    with_process(|process| {
        let record = fz_handler_reserve(process, 32) as *mut u8;
        unsafe { (record.add(24) as *mut u64).write(32) };

        assert_eq!(
            process.handlers.innermost(),
            Some(crate::handler_stack::Innermost::Compiled(record))
        );
        process.pop_handler();
        assert_eq!(process.handlers.innermost(), None);
    });
}

/// Byte length of the first grapheme of `bytes`, asked through the extern.
fn first_grapheme_size(bytes: &[u8]) -> i64 {
    with_process(|process| {
        let bits = fz_alloc_bitstring_const(
            process,
            bytes.as_ptr() as u64,
            bytes.len() as u64,
            bytes.len() as u64 * 8,
        );
        fz_grapheme_size(process, bits)
    })
}

/// A grapheme is an extended grapheme cluster, so the first one of each
/// string below spans every codepoint a reader sees as one character.
#[test]
fn grapheme_size_spans_the_whole_extended_cluster() {
    let cases: [(&str, i64); 7] = [
        ("abc", 1),
        ("\r\nx", 2),
        ("e\u{301}x", 3),
        ("\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}x", 18),
        ("\u{1F1EB}\u{1F1F7}\u{1F1EB}", 8),
        ("\u{1100}\u{1161}\u{11A8}x", 9),
        ("\u{0915}\u{094D}\u{0937}x", 9),
    ];
    for (text, expected) in cases {
        assert_eq!(first_grapheme_size(text.as_bytes()), expected, "{text:?}");
    }
}

/// An invalid byte is its own grapheme, and a cluster never runs across one.
#[test]
fn grapheme_size_treats_an_invalid_byte_as_its_own_grapheme() {
    assert_eq!(first_grapheme_size(&[0xFF]), 1);
    assert_eq!(first_grapheme_size(&[0xFF, b'a']), 1);
    assert_eq!(first_grapheme_size(&[b'e', 0xCC, 0x81, 0xC3]), 3);
}

#[test]
fn fixed_notation_rounds_the_exact_value_and_sends_a_tie_away_from_zero() {
    let cases: &[(f64, usize, &str)] = &[
        (0.05, 0, "0"),
        (0.05, 1, "0.1"),
        (2.675, 1, "2.7"),
        (2.675, 3, "2.675"),
        (2.675, 2, "2.67"),
        (-0.04, 0, "-0"),
        (-0.04, 3, "-0.040"),
        (1.0e10, 1, "10000000000.0"),
        (123456.789, 0, "123457"),
        (9.99, 1, "10.0"),
        (99.5, 0, "100"),
        (2.5, 0, "3"),
        (0.125, 2, "0.13"),
        (-2.5, 0, "-3"),
        (0.0, 2, "0.00"),
    ];
    for &(value, decimals, expected) in cases {
        assert_eq!(fixed_notation(value, decimals), expected, "{value} at {decimals}");
    }
}

#[test]
fn fixed_notation_spells_the_smallest_float_in_full() {
    let text = fixed_notation(f64::from_bits(1), 253);
    assert_eq!(text.len(), "0.".len() + 253);
    assert!(text.bytes().all(|b| b == b'0' || b == b'.'));
}

/// Intent: a pid and a reference inspect in the shape Elixir prints, alone and
/// as a list element, and a protocol error names each by its Elixir kind.
#[test]
fn a_pid_and_a_reference_render_in_elixir_shapes() {
    with_process(|process| {
        let process_ptr = process as *mut Process;
        let pid = AnyValue::Opaque(ValueKind::PID, 7);
        let reference = AnyValue::Opaque(ValueKind::REF, (3 << 32) | 9);
        assert_eq!(render_value(process_ptr, pid), "#PID<0.7.0>");
        assert_eq!(render_value(process_ptr, reference), "#Reference<0.0.3.9>");
        assert_eq!(
            render_value(process_ptr, AnyValue::Opaque(ValueKind::PID, (2 << 15) | 5)),
            "#PID<0.5.2>",
            "a pid past 15 bits carries its serial"
        );

        let tail = process.heap.alloc_list_cons_slot(reference, EMPTY_LIST_BITS);
        let list = process.heap.alloc_list_cons_slot(pid, tail);
        let list = AnyValue::decode_tagged_heap_bits(list).unwrap();
        assert_eq!(
            render_value(process_ptr, list),
            "[#PID<0.7.0>, #Reference<0.0.3.9>]",
            "a cons cell holds a pid or a reference in its own kind"
        );
    });
}

/// Compiled code asks `fz_heap_room` only when its inline bump found the tip
/// full: the answer is room in a fresh tip, which the heap then bumps from.
#[test]
fn fz_heap_room_places_beyond_a_full_tip() {
    with_process(|process| {
        let full = process.heap.bytes_remaining_in_block();
        process.heap.alloc(full);
        let process_ptr: *mut Process = process;

        let placed = fz_heap_room(process_ptr, 48);

        let process = unsafe { &mut *process_ptr };
        assert!(process.heap.is_young(placed), "the object is in the young generation");
        let next = process.heap.alloc(16);
        assert_eq!(
            next,
            unsafe { placed.add(48) },
            "the fresh tip's bump follows the object"
        );
    });
}

/// A huge object is parked alone in a block of its own.
#[test]
fn fz_heap_room_parks_a_huge_object_alone() {
    with_process(|process| {
        let full = process.heap.bytes_remaining_in_block();
        process.heap.alloc(full);
        let huge = full * 8;
        let process_ptr: *mut Process = process;

        let placed = fz_heap_room(process_ptr, huge);

        let process = unsafe { &mut *process_ptr };
        assert!(process.heap.is_young(placed));
        assert!(
            process.heap.bytes_used() >= huge,
            "the heap holds the huge object's block"
        );
    });
}

/// A body frame of `slots` capture slots, its first slot holding `value`, and
/// the reference word that names it.
fn body_frame_holding(process: &mut Process, slots: usize, value: i64) -> u64 {
    let bits = process.heap.alloc_continuation_slots(1, slots);
    let address = closure_addr_from_tagged(bits).expect("frame address");
    let frame = AnyValueRef::from_heap_object(ValueKind::CLOSURE, address)
        .expect("frame ref")
        .raw_word();
    unsafe { crate::any_value::closure_capture_set(address, 1, AnyValue::int(value)) };
    frame
}

fn first_capture(frame: u64) -> i64 {
    let address = closure_addr_from_ref_word(frame, "test frame");
    unsafe { crate::any_value::closure_capture_value(address, 1) }.raw() as i64
}

/// A write goes into a frame young enough for the next minor collection to look
/// inside, and the frame is answered as it is: the tip block's frame, and a
/// frame too large for the tip, which sits alone in a parked young block.
#[test]
fn a_body_frame_in_a_young_block_is_written_where_it_is() {
    with_process(|process| {
        let in_tip = body_frame_holding(process, 4, 7);
        let parked_alone = body_frame_holding(process, 16_000, 8);

        assert_eq!(fz_frame_for_write(process, in_tip), in_tip);
        assert_eq!(fz_frame_for_write(process, parked_alone), parked_alone);
        assert_eq!(process.frame_copies, 0);
    });
}

/// A collection keeps a frame in an old block. A write into it would name a
/// young object from an object the next minor collection does not look inside,
/// so the write goes to a copy at the tip that holds everything the frame did.
#[test]
fn a_body_frame_a_collection_kept_is_copied_to_the_tip_before_a_write() {
    with_process(|process| {
        let frame = body_frame_holding(process, 4, 7);
        let mut roots = [AnyValueRef::from_raw_word(frame).expect("frame root")];
        process.heap.collect_stats(&mut roots);
        let kept = roots[0].raw_word();
        let kept_address = closure_addr_from_ref_word(kept, "kept frame");
        assert!(
            !process.heap.is_young(kept_address),
            "the collection kept the frame old"
        );

        let written = fz_frame_for_write(process, kept);

        let written_address = closure_addr_from_ref_word(written, "written frame");
        assert_ne!(written, kept);
        assert!(process.heap.is_young(written_address), "the copy is at the tip");
        assert_eq!(first_capture(written), 7, "the copy holds what the frame held");
        assert_eq!(process.frame_copies, 1);
    });
}

/// A byte-aligned field taken from the middle of a shared binary is a view of
/// the source's bytes: nothing is copied into a new buffer.
#[test]
fn reading_a_middle_binary_field_of_a_shared_source_builds_a_view() {
    with_process(|process| {
        let bytes: Vec<u8> = (0..200u8).collect();
        let source = process.heap.alloc_bitstring(&bytes, 200 * 8);
        let source_ref = source.ref_word().raw_word();
        let before = process.heap.node.alloc_stats();
        let spec = fz_bs_field_spec(2, 1, 8, 0, 0, 0);
        let field = fz_bs_read_binary_ref(process, source_ref, 50 * 8, spec, 100);
        let after = process.heap.node.alloc_stats();
        let word = AnyValueRef::from_raw_word(field).unwrap().heap_object_word().unwrap();
        unsafe {
            assert_eq!(Bin::of_binary(word).bit_len(), 100 * 8);
            assert_eq!(from_raw_parts(Bin::of_binary(word).ptr(), 100), &bytes[50..150]);
        }
        assert_eq!(
            after.shared_bin.allocs, before.shared_bin.allocs,
            "no bytes were copied"
        );
        assert_eq!(after.binview.allocs, before.binview.allocs + 1);
    });
}

/// A literal baked into the module is viewed in place, and the heap counts
/// its stub under its own site.
#[test]
fn a_static_literal_counts_as_its_own_stub_site() {
    use crate::bits::SharedBin;
    use crate::heap::{StubCounts, StubSite};
    use crate::sync::AtomicUsize;
    static PAYLOAD: [u8; 4] = [1, 2, 3, 4];
    unsafe extern "C" fn noop(_: *mut SharedBin) {}
    let mut sb = SharedBin {
        refcount: AtomicUsize::new(1),
        bytes_ptr: PAYLOAD.as_ptr(),
        bytes_len: PAYLOAD.len(),
        destructor: noop,
        room: 0,
    };
    with_process(|process| {
        let word = fz_alloc_binview_from_static(process, &mut sb as *mut SharedBin as u64, 32);
        let mut roots = [AnyValueRef::from_raw_word(word).expect("binview ref")];
        let stats = process.heap.collect_stats(&mut roots);
        let mut expected = StubCounts::default();
        expected.record(StubSite::StaticLiteral);
        assert_eq!(stats.stubs_made, expected);
        assert_eq!(stats.binrefs_made, expected);
        assert_eq!(stats.stubs_survived, expected);
    });
}

/// A sizeless last `binary` field is the rest of the source and holds whole
/// bytes; a sizeless last `bits` field is the rest at any length.
#[test]
fn a_binary_rest_must_end_on_a_byte_boundary_and_a_bits_rest_need_not() {
    let rest = |ty_tag: u32| fz_bs_field_spec(ty_tag, 0, if ty_tag == 2 { 8 } else { 1 }, 0, 0, 1);
    let (binary, bits) = (rest(2), rest(3));
    let bytes = [1u8, 2];

    assert_eq!(field_end(binary, 0, 8, &bytes, 16), Some(16), "from a byte boundary");
    assert_eq!(field_end(binary, 0, 3, &bytes, 16), None, "13 bits left");
    assert_eq!(field_end(binary, 0, 8, &bytes, 11), None, "3 bits left");
    assert_eq!(
        field_end(binary, 0, 3, &bytes, 11),
        Some(11),
        "8 bits left, between bytes"
    );
    assert_eq!(field_end(bits, 0, 3, &bytes, 16), Some(16));
    assert_eq!(field_end(bits, 0, 8, &bytes, 11), Some(11));
}

/// `byte_size` counts the bytes that hold a bitstring, so a partial last byte
/// counts, and a cursor counts the bytes that hold what is left of its source.
#[test]
fn byte_extent_rounds_a_partial_last_byte_up() {
    with_process(|process| {
        let bytes = [1u8, 2];
        let whole = fz_alloc_bitstring_const(process, bytes.as_ptr() as u64, 2, 16);
        let partial = fz_alloc_bitstring_const(process, bytes.as_ptr() as u64, 2, 11);
        assert_eq!(fz_bitstring_byte_extent(whole, 0), 2);
        assert_eq!(fz_bitstring_byte_extent(partial, 0), 2);
        assert_eq!(fz_bitstring_byte_extent(partial, 3), 1);
        assert_eq!(fz_bitstring_byte_extent(partial, 11), 0);
    });
}

/// `bit_size` counts the bits of a bitstring, a partial last byte only by the
/// bits it holds, and a cursor counts the bits left of its source.
#[test]
fn bit_extent_counts_every_bit_and_a_cursor_what_is_left() {
    with_process(|process| {
        let bytes = [1u8, 2];
        let whole = fz_alloc_bitstring_const(process, bytes.as_ptr() as u64, 2, 16);
        let partial = fz_alloc_bitstring_const(process, bytes.as_ptr() as u64, 2, 11);
        assert_eq!(fz_bitstring_bit_extent(whole, 0), 16);
        assert_eq!(fz_bitstring_bit_extent(partial, 0), 11);
        assert_eq!(fz_bitstring_bit_extent(partial, 3), 8);
        assert_eq!(fz_bitstring_bit_extent(partial, 11), 0);
    });
}

#[test]
fn a_function_reports_the_number_of_arguments_it_takes_not_counting_its_captures() {
    with_process(|process| {
        let process_ptr = process as *mut Process;
        let none = process
            .heap
            .alloc_closure(crate::any_value::ClosureDenotationId::user(0), 0, 0, 0, 0x1234, &[]);
        let two_with_a_capture = process.heap.alloc_closure(
            crate::any_value::ClosureDenotationId::user(1),
            2,
            1,
            0,
            0x1234,
            &[AnyValue::int(9)],
        );

        assert_eq!(fz_function_arity(process_ptr, none), 0);
        assert_eq!(fz_function_arity(process_ptr, two_with_a_capture), 2);
    });
}

#[test]
fn a_named_function_reports_its_module_name_and_arity_and_a_lambda_reports_nothing() {
    use crate::function_denotation::{FunctionDenotation, FunctionOrigin, LambdaOccurrence};
    use crate::module_name::ModuleName;
    use std::sync::Arc;

    with_process(|process| {
        let named_id = crate::any_value::ClosureDenotationId::user(0);
        let lambda_id = crate::any_value::ClosureDenotationId::user(1);
        let top_level_id = crate::any_value::ClosureDenotationId::user(2);
        let named = Arc::new(FunctionDenotation::named(
            Some(ModuleName::from_segments(vec!["Shop".into(), "Cart".into()])),
            "total".into(),
            2,
        ));
        let lambda = Arc::new(FunctionDenotation {
            origin: FunctionOrigin::Generated {
                owner: Arc::clone(&named),
                occurrence: LambdaOccurrence::from_u32(0),
            },
            arity: 1,
        });
        let top_level = Arc::new(FunctionDenotation::named(None, "main".into(), 0));
        process.node.register_closure_denotation(named_id, named);
        process.node.register_closure_denotation(lambda_id, lambda);
        process.node.register_closure_denotation(top_level_id, top_level);
        let process_ptr = process as *mut Process;
        let closure = |process: &mut Process, id, arity| process.heap.alloc_closure(id, arity, 0, 0, 0x1234, &[]);

        let named = closure(process, named_id, 2);
        let answer = AnyValueRef::from_raw_word(fz_function_name(process_ptr, named)).unwrap();
        let module = process.heap.read_list_head_ref(answer).unwrap();
        let rest = process.heap.read_list_tail_ref(answer).unwrap();
        let name = process.heap.read_list_head_ref(rest).unwrap();
        let rest = process.heap.read_list_tail_ref(rest).unwrap();
        let arity = process.heap.read_list_head_ref(rest).unwrap();
        let atom = |process: &Process, value: AnyValueRef| {
            process
                .node
                .atom_name(value.load_atom().unwrap() as u32)
                .unwrap()
                .to_string()
        };
        assert_eq!(atom(process, module), "Elixir.Shop.Cart");
        assert_eq!(atom(process, name), "total");
        assert_eq!(arity.load_int(), Ok(2));
        assert_eq!(
            process.heap.read_list_tail_ref(rest).unwrap(),
            AnyValueRef::empty_list()
        );

        for (id, arity) in [(lambda_id, 1), (top_level_id, 0)] {
            let unnamed = closure(process, id, arity);
            assert_eq!(
                fz_function_name(process_ptr, unnamed),
                AnyValueRef::empty_list().raw_word(),
                "only a named function in a module can be written `&Mod.fun/arity`",
            );
        }
    });
}
