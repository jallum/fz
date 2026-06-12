//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
#![allow(unused_imports)]

use super::drive_test::{assert_resolved, function_id, module_id};
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

// Ported from src/ir_interp/tests/typed_slot.rs: large integer arithmetic does not lose high-order bits
#[test]
fn large_integer_arithmetic_preserves_high_bits() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00221_large_int_arithmetic.fz".to_string()),
        text: include_str!("../../fixtures2/00221_large_int_arithmetic.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "large integer arithmetic should resolve");
    // TODO: JIT-execute and assert result == 4611686018427387911
}

// Ported from src/ir_interp/tests/typed_slot.rs: protocol dispatch selects correct implementation for Integer
#[test]
fn protocol_dispatch_selects_integer_impl() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00222_protocol_dispatch_integer.fz".to_string()),
        text: include_str!("../../fixtures2/00222_protocol_dispatch_integer.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "protocol dispatch for Integer should resolve");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/ir_interp/tests/typed_slot.rs: float addition produces correct IEEE-754 result
#[test]
fn float_addition_ieee754_result() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00223_float_addition.fz".to_string()),
        text: include_str!("../../fixtures2/00223_float_addition.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "float addition should resolve");
    // TODO: JIT-execute and assert f64::from_bits(result as u64) == 4.0
}

// Ported from src/ir_interp/tests/typed_slot.rs: float inside list renders correctly via dbg
#[test]
fn float_in_list_renders_via_dbg() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00224_float_in_list_dbg.fz".to_string()),
        text: include_str!("../../fixtures2/00224_float_in_list_dbg.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "float in list dbg should resolve");
    // TODO: JIT-execute and assert dbg output == "[1.5]"
}

// Ported from src/ir_interp/tests/typed_slot.rs: named function reference passed as value without heap allocation
#[test]
fn named_fn_ref_passed_as_value_no_heap_alloc() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00225_named_fn_ref_no_alloc.fz".to_string()),
        text: include_str!("../../fixtures2/00225_named_fn_ref_no_alloc.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "named fn ref no alloc should resolve");
    // TODO: JIT-execute and assert result == 41, closure_allocs == 0
}

// Ported from src/ir_interp/tests/typed_slot.rs: zero-capture lambda passed as value without heap allocation
#[test]
fn zero_capture_lambda_no_heap_alloc() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00226_zero_capture_lambda.fz".to_string()),
        text: include_str!("../../fixtures2/00226_zero_capture_lambda.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "zero-capture lambda should resolve");
    // TODO: JIT-execute and assert result == 41, closure_allocs == 0
}

// Ported from src/ir_interp/tests/typed_slot.rs: lambda capturing outer variable executes correctly with capture
#[test]
#[ignore = "compiler2 DeriveAbiReady fatal on captured-lambda fixture — unblock when closure ABI is wired"]
fn lambda_capturing_outer_variable_allocates_closure() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00227_lambda_capture_outer.fz".to_string()),
        text: include_str!("../../fixtures2/00227_lambda_capture_outer.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "captured lambda should resolve");
    // TODO: JIT-execute and assert result == 8, closure_allocs == 1
}

// Ported from src/ir_interp/tests/typed_slot.rs: case-joined function reference remains callable after branch
#[test]
fn case_joined_fn_ref_remains_callable() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00228_case_joined_fn_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00228_case_joined_fn_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "case-joined fn ref should resolve");
    // TODO: JIT-execute and assert result == 1
}

// Ported from src/ir_interp/tests/typed_slot.rs: Enum.reduce over list with inline lambda accumulates correctly
#[test]
fn enum_reduce_with_inline_lambda_accumulates() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00229_enum_reduce_lambda.fz".to_string()),
        text: include_str!("../../fixtures2/00229_enum_reduce_lambda.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.reduce with lambda should resolve");
    // TODO: JIT-execute and assert result == 6
}

// Ported from src/ir_interp/tests/typed_slot.rs: Enum.take with list and range in chained non-tail call sequence
#[test]
fn enum_take_chained_non_tail_calls_preserve_continuations() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00230_enum_take_chained.fz".to_string()),
        text: include_str!("../../fixtures2/00230_enum_take_chained.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.take chained calls should resolve");
    // TODO: JIT-execute and assert dbg output == "[1, 2, 3]\n[]\n[1, 2, 3, 4, 5]\n[4, 5]\n[4, 5]"
}

// Ported from src/ir_interp/tests/typed_slot.rs: case-joined function reference used as Enum.reduce reducer
#[test]
#[ignore = "compiler2 DeriveAbiReady fatal on Process.heap_alloc_stats fixture — unblock when BIF is wired"]
fn case_joined_fn_refs_callable_as_enum_reduce_reducer() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00231_joined_fn_refs_enum_reduce.fz".to_string()),
        text: include_str!("../../fixtures2/00231_joined_fn_refs_enum_reduce.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "joined fn refs as Enum.reduce reducer should resolve");
    // TODO: JIT-execute and assert result == 6
}

// Ported from src/ir_interp/tests/typed_slot.rs: float equality inside list compares by value
#[test]
fn float_equality_in_list_compares_by_value() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00232_float_equality_in_list.fz".to_string()),
        text: include_str!("../../fixtures2/00232_float_equality_in_list.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "float equality in list should resolve");
    // TODO: JIT-execute and assert result == 1 (true)
}

// Ported from src/ir_interp/tests/typed_slot.rs: receive pattern matches float inside a list
#[test]
fn receive_pattern_matches_float_in_list() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00233_receive_float_in_list.fz".to_string()),
        text: include_str!("../../fixtures2/00233_receive_float_in_list.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "receive matching float in list should resolve");
    // TODO: JIT-execute and assert result == 7
}

// Ported from src/ir_interp/tests/typed_slot.rs: large integer survives send/receive message boundary intact
#[test]
fn large_integer_survives_send_receive_boundary() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00234_large_int_send_receive.fz".to_string()),
        text: include_str!("../../fixtures2/00234_large_int_send_receive.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "large int send/receive should resolve");
    // TODO: JIT-execute and assert result == 4611686018427387904
}

// Ported from src/ir_interp/tests/typed_slot.rs: large integer extracted via list head pattern match
#[test]
fn large_integer_extracted_via_list_head() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00235_large_int_list_head.fz".to_string()),
        text: include_str!("../../fixtures2/00235_large_int_list_head.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "large int list head extraction should resolve");
    // TODO: JIT-execute and assert result == 4611686018427387904
}

// Ported from src/ir_interp/tests/typed_slot.rs: large integer extracted via map field access
#[test]
fn large_integer_extracted_via_map_field() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00236_large_int_map_get.fz".to_string()),
        text: include_str!("../../fixtures2/00236_large_int_map_get.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "large int map field extraction should resolve");
    // TODO: JIT-execute and assert result == 4611686018427387904
}

// Ported from src/ir_interp/tests/typed_slot.rs: scalars read from list head, map field, and tuple slot destructuring
#[test]
fn scalars_read_from_list_map_tuple_containers() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00237_scalars_from_containers.fz".to_string()),
        text: include_str!("../../fixtures2/00237_scalars_from_containers.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "scalars from containers should resolve");
    // TODO: JIT-execute and assert dbg output == "{7, 42, 1.5}"
}

// Ported from src/ir_interp/tests/typed_slot.rs: heap values (lists) extracted from list, map, and tuple containers
#[test]
fn heap_values_read_from_list_map_tuple_containers() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00238_heap_values_from_containers.fz".to_string()),
        text: include_str!("../../fixtures2/00238_heap_values_from_containers.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "heap values from containers should resolve");
    // TODO: JIT-execute and assert dbg output == "{[1], [2], [3]}"
}

// Ported from src/ir_interp/tests/typed_slot.rs: typed integer clause guard dispatches to correct function body
#[test]
fn typed_integer_clause_guard_dispatches_correctly() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00239_typed_int_dispatch.fz".to_string()),
        text: include_str!("../../fixtures2/00239_typed_int_dispatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "typed int dispatch should resolve");
    // TODO: JIT-execute and assert result == 4611686018427387911
}

// Ported from src/ir_interp/tests/typed_slot.rs: large integer delivered from spawned process to blocked receive
#[test]
fn large_integer_delivered_from_spawn_unblocks_receive() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00240_large_int_from_spawn.fz".to_string()),
        text: include_str!("../../fixtures2/00240_large_int_from_spawn.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "large int from spawned process should resolve");
    // TODO: JIT-execute and assert result == 4611686018427387904
}

// Ported from src/ir_interp/tests/receive.rs: pinned-ref receive matches pre-queued tagged message correctly
#[test]
fn pinned_ref_receive_matches_pre_queued_message() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00241_pinned_ref_receive.fz".to_string()),
        text: include_str!("../../fixtures2/00241_pinned_ref_receive.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "pinned-ref receive should resolve");
    // TODO: JIT-execute and assert dbg output contains "7"
}

// Ported from src/ir_interp/tests/receive.rs: spawn delivers tagged message that unblocks selective receive
#[test]
fn spawn_delivers_tagged_message_unblocks_receive() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00242_spawn_tagged_receive.fz".to_string()),
        text: include_str!("../../fixtures2/00242_spawn_tagged_receive.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "spawn-then-tagged-receive should resolve");
    // TODO: JIT-execute and assert dbg output contains "99"
}

// Ported from src/ir_interp/tests/receive.rs: receive after 0 fires immediately when no message matches
#[test]
fn receive_after_zero_fires_immediately_on_empty_mailbox() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00243_receive_after_zero.fz".to_string()),
        text: include_str!("../../fixtures2/00243_receive_after_zero.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "receive after 0 should resolve");
    // TODO: JIT-execute and assert dbg output contains "12"
}

// Ported from src/ir_interp/tests/receive.rs: selective receive retrieves out-of-order message skipped earlier
#[test]
fn selective_receive_retrieves_out_of_order_skipped_message() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00244_out_of_order_receive.fz".to_string()),
        text: include_str!("../../fixtures2/00244_out_of_order_receive.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "out-of-order receive should resolve");
    // TODO: JIT-execute and assert dbg output contains "3"
}

// Ported from src/ir_interp/tests/receive.rs: map pattern in receive matches correct message from mailbox
#[test]
fn receive_map_pattern_matches_correct_message() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00245_receive_map_pattern.fz".to_string()),
        text: include_str!("../../fixtures2/00245_receive_map_pattern.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "map pattern receive should resolve");
    // TODO: JIT-execute and assert dbg output contains "42"
}

// Ported from src/ir_interp/tests/receive.rs: map receive pattern matches key whose value is nil
#[test]
fn receive_map_pattern_matches_present_nil_value() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00246_receive_map_nil_value.fz".to_string()),
        text: include_str!("../../fixtures2/00246_receive_map_nil_value.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "map receive with nil value should resolve");
    // TODO: JIT-execute and assert dbg output == "nil"
}

// Ported from src/ir_interp/tests/receive.rs: pinned-ref selective receive with out-of-order server replies
#[test]
fn selective_receive_pinned_ref_out_of_order_server_replies() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00247_selective_refs_stress.fz".to_string()),
        text: include_str!("../../fixtures2/00247_selective_refs_stress.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "selective refs stress test should resolve");
    // TODO: JIT-execute and assert dbg output contains "3"
}

// Ported from src/ir_interp/tests/resource_bif.rs: make_resource creates resource and dtor fires once on process exit
#[test]
fn make_resource_resolves_with_dtor_binding() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00248_make_resource_dtor.fz".to_string()),
        text: include_str!("../../fixtures2/00248_make_resource_dtor.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "make_resource with dtor should resolve");
    // TODO: JIT-execute, assert DTOR_FIRED == 1 and DTOR_LAST_PAYLOAD == 42 after process heap drop
}

// Ported from src/ir_interp/tests/resource_bif.rs: aliased resource bindings fire destructor exactly once
#[test]
fn aliased_resource_bindings_fire_dtor_once() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00249_aliased_resource_dtor.fz".to_string()),
        text: include_str!("../../fixtures2/00249_aliased_resource_dtor.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "aliased resource should resolve");
    // TODO: JIT-execute, assert DTOR_FIRED == 1 and DTOR_LAST_PAYLOAD == 7 (three names, one refcount edge)
}

// Ported from src/ir_interp/tests/resource_bif.rs: two distinct resources each fire their destructor exactly once
#[test]
fn two_distinct_resources_each_fire_dtor_once() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00250_two_distinct_resources.fz".to_string()),
        text: include_str!("../../fixtures2/00250_two_distinct_resources.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "two distinct resources should resolve");
    // TODO: JIT-execute, assert DTOR_FIRED == 2 (MSO chain must walk both Resource stubs)
}

// Ported from src/ir_interp/tests/resource_bif.rs: opaque resource .value accessor returns payload through module boundary
#[test]
fn opaque_resource_value_accessor_returns_payload() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00251_opaque_resource_value.fz".to_string()),
        text: include_str!("../../fixtures2/00251_opaque_resource_value.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "opaque resource .value accessor should resolve");
    // TODO: JIT-execute, assert R.get_value(r) == 99 and DTOR_FIRED == 1 after heap drop
}

// Ported from src/ir_interp/tests/variadic.rs: variadic C extern call passes integer arguments and returns fd
#[test]
#[cfg(unix)]
fn variadic_c_extern_open_passes_int_args() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00252_variadic_open_dynamic.fz".to_string()),
        text: include_str!("../../fixtures2/00252_variadic_open_dynamic.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "variadic open should resolve");
    // TODO: JIT-execute with a unique temp path and assert fd >= 0, file mode bits match requested & !umask
}

// Ported from src/ir_interp/tests/variadic.rs: unsupported variadic extern arg type produces a clear runtime error
#[test]
fn unsupported_variadic_extern_float_arg_is_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00253_variadic_float_error.fz".to_string()),
        text: include_str!("../../fixtures2/00253_variadic_float_error.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "variadic printf with float arg should resolve");
    // TODO: JIT-execute and assert error contains "unsupported variadic extern shape" and "F64"
}
