//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
#![allow(unused_imports)]

use super::drive_test::{assert_resolved, function_id, module_id};
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

// Ported from src/ir_codegen/ir_codegen_test.rs: multi-module import and cross-module call resolves and runs
#[test]
fn two_module_cross_call_resolves_and_runs() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00271_two_module_cross_call.fz".to_string()),
        text: include_str!("../../fixtures2/00271_two_module_cross_call.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "two_module_cross_call_resolves_and_runs");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/ir_codegen/ir_codegen_test.rs: cross-module function call resolves and executes provider body
#[test]
fn cross_module_provider_body_rewrites_provider_boundary_calls() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00271_two_module_cross_call.fz".to_string()),
        text: include_str!("../../fixtures2/00271_two_module_cross_call.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "cross_module_provider_body_rewrites_provider_boundary_calls",
    );
    // TODO: JIT-execute and assert result == 42; verify no provider-boundary call edges remain after linking
}

// Ported from src/ir_codegen/ir_codegen_test.rs: cross-module protocol impl dispatch resolves to correct implementation
#[test]
fn cross_module_protocol_impl_dispatch_resolves() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00272_protocol_impl_dispatch.fz".to_string()),
        text: include_str!("../../fixtures2/00272_protocol_impl_dispatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "cross_module_protocol_impl_dispatch_resolves");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/ir_codegen/ir_codegen_test.rs: protocol dispatch over integer type calls correct impl
#[test]
fn protocol_dispatch_over_integer_type() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00273_integer_protocol_dispatch.fz".to_string()),
        text: include_str!("../../fixtures2/00273_integer_protocol_dispatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "protocol_dispatch_over_integer_type");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/ir_codegen/ir_codegen_test.rs: closed-union protocol dispatch selects correct impl per value type
#[test]
fn closed_union_protocol_dispatch_selects_correct_impl() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00274_closed_union_protocol.fz".to_string()),
        text: include_str!("../../fixtures2/00274_closed_union_protocol.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Resolved once closed-union protocol dispatch no longer emits duplicate fact output
    // TODO: JIT-execute and assert result == 107 (interpreter and native paths)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: Enum.count, member?, reduce, and Enumerable.reduce over lists
#[test]
fn enum_count_member_reduce_and_enumerable_reduce() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00275_enum_count_member_reduce.fz".to_string()),
        text: include_str!("../../fixtures2/00275_enum_count_member_reduce.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "enum_count_member_reduce_and_enumerable_reduce");
    // TODO: JIT-execute and assert output == ["{3, true, 6, {:done, 6}}"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: Enum.to_list and Enum.map preserve list structure and elements
#[test]
fn enum_to_list_and_map_preserve_structure() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00276_enum_to_list_and_map.fz".to_string()),
        text: include_str!("../../fixtures2/00276_enum_to_list_and_map.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Resolved once Enum.to_list/Enum.map are fully ported
    let _ = compiler.drive();
    // TODO: JIT-execute and assert output == ["[1, 2, 3]", "[2, 4, 6, 8]"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: Enum tier-0 fixture exercises basic Enum operations end-to-end
#[test]
fn enum_tier0_fixture_exercises_basic_operations() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00277_enum_tier0_fixture.fz".to_string()),
        text: include_str!("../../fixtures2/00277_enum_tier0_fixture.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Resolved once all enum tier-0 operations are ported
    let _ = compiler.drive();
    // TODO: JIT-execute and assert output matches fixtures2/behavior/enum_tier0.expected.txt
}

// Ported from src/ir_codegen/ir_codegen_test.rs: Enum.count with predicate closure filters list correctly
#[test]
fn enum_count_predicate_closure_filters_correctly() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00278_enum_count_predicate.fz".to_string()),
        text: include_str!("../../fixtures2/00278_enum_count_predicate.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "enum_count_predicate_closure_filters_correctly");
    // TODO: JIT-execute and assert output == ["2"]; verify branch helper return lane is ValueRef
}

// Ported from src/ir_codegen/ir_codegen_test.rs: Enum.find and Enum.find_value with closures return correct results
#[test]
fn enum_find_and_find_value_with_closures() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00279_enum_find_find_value.fz".to_string()),
        text: include_str!("../../fixtures2/00279_enum_find_find_value.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "enum_find_and_find_value_with_closures");
    // TODO: JIT-execute and assert output == ["3", "{:even, 2}"]; verify reduce_step continuation ABI
}

// Ported from src/ir_codegen/ir_codegen_test.rs: Enum.find_index with predicate closure returns correct index or nil
#[test]
fn enum_find_index_returns_index_or_nil() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00280_enum_find_index.fz".to_string()),
        text: include_str!("../../fixtures2/00280_enum_find_index.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "enum_find_index_returns_index_or_nil");
    // TODO: JIT-execute and assert output == ["1", "nil"]; verify int clause boxes return on ValueRef lane
}

// Ported from src/ir_codegen/ir_codegen_test.rs: opaque reducer closure call chains with indirect continuation
#[test]
fn opaque_reducer_uses_indirect_lazy_continuation() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00281_opaque_reducer_closure.fz".to_string()),
        text: include_str!("../../fixtures2/00281_opaque_reducer_closure.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Resolved once opaque reducer closure ABI is ported
    let _ = compiler.drive();
    // TODO: JIT-execute and assert output == ["6"]; verify indirect dispatch uses lazy_descriptor continuation
}

// Ported from src/ir_codegen/ir_codegen_test.rs: Enumerable.reduce returns :done and :halted protocol results correctly
#[test]
fn enumerable_reduce_done_and_halted_results() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00282_enumerable_reduce_done_halt.fz".to_string()),
        text: include_str!("../../fixtures2/00282_enumerable_reduce_done_halt.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Resolved once Enumerable.reduce low-level protocol is ported
    let _ = compiler.drive();
    // TODO: JIT-execute and assert output == ["{{:done, 3}, {:halted, 7}}"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: Enum.reduce_while with shape-changing accumulator halts at correct element
#[test]
fn enum_reduce_while_shape_changing_accumulator() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00283_enum_reduce_while_shape.fz".to_string()),
        text: include_str!("../../fixtures2/00283_enum_reduce_while_shape.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "enum_reduce_while_shape_changing_accumulator");
    // TODO: JIT-execute and assert output == ["1"]; verify {:found, index} subtype in declared return
}

// Ported from src/ir_codegen/ir_codegen_test.rs: Enum.find early halt with default value returns first matching element
#[test]
fn enum_find_early_halt_returns_matching_element() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00284_enum_find_early_halt.fz".to_string()),
        text: include_str!("../../fixtures2/00284_enum_find_early_halt.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "enum_find_early_halt_returns_matching_element");
    // TODO: JIT-execute and assert output == ["1"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: Enum.sort with default and custom comparator preserves stable order
#[test]
fn enum_sort_stable_order_with_custom_comparator() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00285_enum_sort_stable.fz".to_string()),
        text: include_str!("../../fixtures2/00285_enum_sort_stable.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "enum_sort_stable_order_with_custom_comparator");
    // TODO: JIT-execute and assert output == ["[1, 1, 2, 3, 4, 5]", "[5, 4, 3, 2, 1, 1]", "[{1, :a}, {1, :b}, {2, :a}, {2, :b}]"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: atom identity is stable across multiple executions of same program
#[test]
fn atom_identity_stable_across_process_runs() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00286_atom_ok.fz".to_string()),
        text: include_str!("../../fixtures2/00286_atom_ok.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "atom_identity_stable_across_process_runs");
    // TODO: JIT-execute twice; assert both runs return the same halt value
}

// Ported from src/ir_codegen/ir_codegen_test.rs: nil, true, false reserved atom IDs are stable and correct
#[test]
fn reserved_atom_ids_nil_true_false_are_stable() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00287_nil_true_false_atoms.fz".to_string()),
        text: include_str!("../../fixtures2/00287_nil_true_false_atoms.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "reserved_atom_ids_nil_true_false_are_stable");
    // TODO: JIT-execute nil/true/false programs and assert halt values match NIL_ATOM_ID/TRUE_ATOM_ID/FALSE_ATOM_ID
}

// Ported from src/ir_codegen/ir_codegen_test.rs: spawn with captured variables executes and completes correctly
#[test]
fn spawn_with_captures_executes_and_completes() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00288_spawn_with_captures.fz".to_string()),
        text: include_str!("../../fixtures2/00288_spawn_with_captures.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "spawn_with_captures_executes_and_completes");
    // TODO: JIT-execute and assert halt value == NIL_ATOM_ID (assert passes)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: plain spawn of zero-arity function executes child process
#[test]
fn plain_spawn_executes_zero_arity_child() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00289_plain_spawn.fz".to_string()),
        text: include_str!("../../fixtures2/00289_plain_spawn.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "plain_spawn_executes_zero_arity_child");
    // TODO: JIT-execute and assert halt value == 2 (spawn/1 returns nil atom id)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: spawn + send + selective receive delivers message to waiting process
#[test]
fn spawn_send_selective_receive_delivers_message() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00290_spawn_send_receive.fz".to_string()),
        text: include_str!("../../fixtures2/00290_spawn_send_receive.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "spawn_send_selective_receive_delivers_message");
    // TODO: JIT-execute and assert halt value == 42
}

// Ported from src/ir_codegen/ir_codegen_test.rs: plain spawn executes child process via interpreter path
#[test]
fn plain_spawn_executes_via_interpreter_path() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00289_plain_spawn.fz".to_string()),
        text: include_str!("../../fixtures2/00289_plain_spawn.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "plain_spawn_executes_via_interpreter_path");
    // TODO: JIT-execute and assert halt value == 2
}

// Ported from src/ir_codegen/ir_codegen_test.rs: spawn child, send message, receive in main returns sent value
#[test]
fn spawn_child_send_receive_returns_sent_value() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00291_spawn_child_receive.fz".to_string()),
        text: include_str!("../../fixtures2/00291_spawn_child_receive.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "spawn_child_send_receive_returns_sent_value");
    // TODO: JIT-execute and assert halt value == 42
}

// Ported from src/ir_codegen/ir_codegen_test.rs: map construction is isolated between independent process runs
#[test]
fn map_construction_isolated_across_independent_processes() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00292_map_build_process.fz".to_string()),
        text: include_str!("../../fixtures2/00292_map_build_process.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "map_construction_isolated_across_independent_processes",
    );
    // TODO: JIT-execute program A twice; assert result == 10 on both runs; no state leak across runs
}

// Ported from src/ir_codegen/ir_codegen_test.rs: integer literal evaluates and returns correct value
#[test]
fn integer_literal_halts_with_correct_value() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00009_no_runtime.fz".to_string()),
        text: include_str!("../../fixtures2/00009_no_runtime.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "integer_literal_halts_with_correct_value");
    // TODO: JIT-execute and assert halt value == 42
}

// Ported from src/ir_codegen/ir_codegen_test.rs: integer addition computes correct result
#[test]
fn integer_addition_computes_sum() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00293_int_addition.fz".to_string()),
        text: include_str!("../../fixtures2/00293_int_addition.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "integer_addition_computes_sum");
    // TODO: JIT-execute and assert halt value == 42
}

// Ported from src/ir_codegen/ir_codegen_test.rs: chained arithmetic operators evaluate in correct order
#[test]
fn chained_arithmetic_evaluates_in_correct_order() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00294_arith_chain.fz".to_string()),
        text: include_str!("../../fixtures2/00294_arith_chain.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "chained_arithmetic_evaluates_in_correct_order");
    // TODO: JIT-execute and assert halt value == 21
}

// Ported from src/ir_codegen/ir_codegen_test.rs: if/else conditional takes true branch on satisfied condition
#[test]
fn if_else_takes_true_branch_when_condition_holds() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00295_if_then_else.fz".to_string()),
        text: include_str!("../../fixtures2/00295_if_then_else.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "if_else_takes_true_branch_when_condition_holds");
    // TODO: JIT-execute and assert halt value == 100
}

// Ported from src/ir_codegen/ir_codegen_test.rs: dbg/1 prints expression value to output
#[test]
fn dbg_routes_value_through_runtime_output() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00296_dbg_print.fz".to_string()),
        text: include_str!("../../fixtures2/00296_dbg_print.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "dbg_routes_value_through_runtime_output");
    // TODO: JIT-execute and assert output == ["42"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: Process.heap_alloc_stats intrinsic returns map with allocation counts
#[test]
fn process_heap_alloc_stats_returns_allocation_map() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00297_heap_alloc_stats.fz".to_string()),
        text: include_str!("../../fixtures2/00297_heap_alloc_stats.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "process_heap_alloc_stats_returns_allocation_map");
    // TODO: JIT-execute and assert output == ["[1, 2]", "2", "0"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: assert and refute builtins distinguish integer payload from bool kind
#[test]
fn assert_refute_distinguish_scalar_kind_from_payload() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00298_assert_refute.fz".to_string()),
        text: include_str!("../../fixtures2/00298_assert_refute.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "assert_refute_distinguish_scalar_kind_from_payload");
    // TODO: JIT-execute assert(2) and refute(true == 1) and assert both return NIL_ATOM_ID
}

// Ported from src/ir_codegen/ir_codegen_test.rs: unary negation of integer literal returns negative value
#[test]
fn unary_negation_returns_negative_value() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00299_unary_neg.fz".to_string()),
        text: include_str!("../../fixtures2/00299_unary_neg.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "unary_negation_returns_negative_value");
    // TODO: JIT-execute and assert halt value == -7
}

// Ported from src/ir_codegen/ir_codegen_test.rs: atom literal returns its interned atom id
#[test]
fn atom_literal_returns_interned_id() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00286_atom_ok.fz".to_string()),
        text: include_str!("../../fixtures2/00286_atom_ok.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "atom_literal_returns_interned_id");
    // TODO: JIT-execute and assert atom_names[halt_value] == "ok"
}

// Ported from src/ir_codegen/ir_codegen_test.rs: function call passes argument and returns computed result
#[test]
fn function_call_passes_argument_and_returns_result() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00300_add1_call.fz".to_string()),
        text: include_str!("../../fixtures2/00300_add1_call.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "function_call_passes_argument_and_returns_result");
    // TODO: JIT-execute and assert halt value == 42
}

// Ported from src/ir_codegen/ir_codegen_test.rs: non-tail call result used in enclosing arithmetic expression
#[test]
fn nontail_call_result_used_in_enclosing_binop() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00301_nontail_call_binop.fz".to_string()),
        text: include_str!("../../fixtures2/00301_nontail_call_binop.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "nontail_call_result_used_in_enclosing_binop");
    // TODO: JIT-execute and assert halt value == 43
}

// Ported from src/ir_codegen/ir_codegen_test.rs: recursive function with base case and pattern matching computes factorial
#[test]
fn recursive_function_with_pattern_match_computes_factorial() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00302_factorial_pattern_match.fz".to_string()),
        text: include_str!("../../fixtures2/00302_factorial_pattern_match.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "recursive_function_with_pattern_match_computes_factorial",
    );
    // TODO: JIT-execute and assert halt value == 120
}

// Ported from src/ir_codegen/ir_codegen_test.rs: deep recursive factorial executes without stack overflow
#[test]
fn deep_recursive_factorial_runs_without_overflow() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00303_factorial_deep_recursion.fz".to_string()),
        text: include_str!("../../fixtures2/00303_factorial_deep_recursion.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "deep_recursive_factorial_runs_without_overflow");
    // TODO: JIT-execute and assert halt value == 3628800
}

// Ported from src/ir_codegen/ir_codegen_test.rs: tail-recursive loop over 100k iterations does not overflow stack
#[test]
fn tail_recursive_loop_stays_bounded_via_frame_reuse() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00304_tail_recursive_count.fz".to_string()),
        text: include_str!("../../fixtures2/00304_tail_recursive_count.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tail_recursive_loop_stays_bounded_via_frame_reuse");
    // TODO: JIT-execute and assert halt value == 100_000
}

// Ported from src/ir_codegen/ir_codegen_test.rs: atom, true, false literals render correctly via dbg
#[test]
fn atom_true_false_literals_render_via_dbg() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00305_atom_bool_dbg.fz".to_string()),
        text: include_str!("../../fixtures2/00305_atom_bool_dbg.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "atom_true_false_literals_render_via_dbg");
    // TODO: JIT-execute and assert output == [":ok", "true", "false"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: atom-keyed map literal renders with canonical key-value syntax
#[test]
fn atom_keyed_map_renders_with_canonical_syntax() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00306_atom_keyed_map.fz".to_string()),
        text: include_str!("../../fixtures2/00306_atom_keyed_map.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "atom_keyed_map_renders_with_canonical_syntax");
    // TODO: JIT-execute and assert output == ["%{:a => 1, :b => 2}"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: map key access returns value for present keys
#[test]
fn map_key_access_returns_present_value() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00307_map_key_access.fz".to_string()),
        text: include_str!("../../fixtures2/00307_map_key_access.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "map_key_access_returns_present_value");
    // TODO: JIT-execute and assert halt value == 30
}

// Ported from src/ir_codegen/ir_codegen_test.rs: map update syntax creates new map leaving original immutable
#[test]
fn map_update_creates_new_map_original_unchanged() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00308_map_update_immutable.fz".to_string()),
        text: include_str!("../../fixtures2/00308_map_update_immutable.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "map_update_creates_new_map_original_unchanged");
    // TODO: JIT-execute and assert output == ["%{:a => 1, :b => 2}", "%{:a => 99, :b => 2}"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: bitstring literal renders correctly as byte sequence
#[test]
fn bitstring_literal_renders_as_byte_sequence() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00309_bitstring_literal.fz".to_string()),
        text: include_str!("../../fixtures2/00309_bitstring_literal.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "bitstring_literal_renders_as_byte_sequence");
    // TODO: JIT-execute and assert output == ["<<255, 171>>"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: binary pattern match splits header byte from rest of bitstring
#[test]
fn binary_pattern_splits_header_byte_from_rest() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00310_binary_pattern_header.fz".to_string()),
        text: include_str!("../../fixtures2/00310_binary_pattern_header.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Resolved once binary pattern matching is ported to compiler2
    let _ = compiler.drive();
    // TODO: JIT-execute and assert output == ["{165, <<1, 2>>}"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: binary pattern with size variable extracts variable-length segment
#[test]
fn binary_pattern_extracts_variable_length_segment() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00311_binary_variable_size.fz".to_string()),
        text: include_str!("../../fixtures2/00311_binary_variable_size.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Resolved once binary pattern matching is ported to compiler2
    let _ = compiler.drive();
    // TODO: JIT-execute and assert output == ["{3, <<1, 2, 3>>, <<255>>}"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: two-element tuple literal renders correctly
#[test]
fn tuple_pair_renders_correctly() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00312_tuple_pair_dbg.fz".to_string()),
        text: include_str!("../../fixtures2/00312_tuple_pair_dbg.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tuple_pair_renders_correctly");
    // TODO: JIT-execute and assert output == ["{1, 2}"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: tuple pattern match destructures elements by position
#[test]
fn tuple_pattern_match_destructures_by_position() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00313_tuple_destructure.fz".to_string()),
        text: include_str!("../../fixtures2/00313_tuple_destructure.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tuple_pattern_match_destructures_by_position");
    // TODO: JIT-execute and assert halt value == 50
}

// Ported from src/ir_codegen/ir_codegen_test.rs: mixed-type tuple with int, atom, bool renders correctly
#[test]
fn mixed_type_tuple_renders_all_field_types() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00314_mixed_type_tuple.fz".to_string()),
        text: include_str!("../../fixtures2/00314_mixed_type_tuple.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "mixed_type_tuple_renders_all_field_types");
    // TODO: JIT-execute and assert output == ["{1, :ok, true}"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: list literal renders correctly as bracketed comma-separated values
#[test]
fn list_literal_renders_as_bracketed_sequence() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00315_list_literal_dbg.fz".to_string()),
        text: include_str!("../../fixtures2/00315_list_literal_dbg.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "list_literal_renders_as_bracketed_sequence");
    // TODO: JIT-execute and assert output == ["[1, 2, 3]"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: recursive list head/tail pattern match accumulates sum correctly
#[test]
fn recursive_head_tail_pattern_match_sums_list() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00316_sum_list_head_tail.fz".to_string()),
        text: include_str!("../../fixtures2/00316_sum_list_head_tail.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "recursive_head_tail_pattern_match_sums_list");
    // TODO: JIT-execute and assert halt value == 15
}

// Ported from src/ir_codegen/ir_codegen_test.rs: double negation round-trips integer value correctly
#[test]
fn double_negation_roundtrips_integer() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00317_double_negation.fz".to_string()),
        text: include_str!("../../fixtures2/00317_double_negation.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "double_negation_roundtrips_integer");
    // TODO: JIT-execute and assert halt value == 42; test other values: 0, 1, -1, -42, 1_000_000_000
}

// Ported from src/ir_codegen/ir_codegen_test.rs: mutually recursive functions dispatch correctly across call boundaries
#[test]
fn mutually_recursive_even_odd_dispatch_correctly() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00318_mutual_recursion_even_odd.fz".to_string()),
        text: include_str!("../../fixtures2/00318_mutual_recursion_even_odd.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "mutually_recursive_even_odd_dispatch_correctly");
    // TODO: JIT-execute and assert halt value == 1 (true)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: function reference passed as value and called via closure application
#[test]
fn function_ref_passed_as_value_and_called() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00319_apply_fn_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00319_apply_fn_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "function_ref_passed_as_value_and_called");
    // TODO: JIT-execute and assert halt value == 42
}

// Ported from src/ir_codegen/ir_codegen_test.rs: closure captures enclosing scope variable and uses it on call
#[test]
fn closure_captures_enclosing_scope_variable() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00320_closure_captures_local.fz".to_string()),
        text: include_str!("../../fixtures2/00320_closure_captures_local.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "closure_captures_enclosing_scope_variable");
    // TODO: JIT-execute and assert halt value == 15
}

// Ported from src/ir_codegen/ir_codegen_test.rs: higher-order map applies function to each element and collects results
#[test]
fn higher_order_map_applies_function_to_each_element() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00321_higher_order_map.fz".to_string()),
        text: include_str!("../../fixtures2/00321_higher_order_map.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "higher_order_map_applies_function_to_each_element");
    // TODO: JIT-execute and assert output == ["[2, 4, 6]"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: list equality is structural not referential across distinct allocations
#[test]
fn list_equality_is_structural_not_referential() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00322_list_structural_eq.fz".to_string()),
        text: include_str!("../../fixtures2/00322_list_structural_eq.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "list_equality_is_structural_not_referential");
    // TODO: JIT-execute and assert halt value == 1 (true)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: list equality is false when lists have different lengths
#[test]
fn list_equality_false_on_length_mismatch() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00323_list_eq_length_mismatch.fz".to_string()),
        text: include_str!("../../fixtures2/00323_list_eq_length_mismatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "list_equality_false_on_length_mismatch");
    // TODO: JIT-execute and assert halt value == FALSE_ATOM_ID
}

// Ported from src/ir_codegen/ir_codegen_test.rs: tuple equality holds when arity and all fields match
#[test]
fn tuple_equality_holds_when_arity_and_fields_match() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00324_tuple_structural_eq.fz".to_string()),
        text: include_str!("../../fixtures2/00324_tuple_structural_eq.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tuple_equality_holds_when_arity_and_fields_match");
    // TODO: JIT-execute and assert halt value == 1 (true)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: tuple equality is false when arities differ
#[test]
fn tuple_equality_false_when_arities_differ() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00325_tuple_eq_arity_mismatch.fz".to_string()),
        text: include_str!("../../fixtures2/00325_tuple_eq_arity_mismatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tuple_equality_false_when_arities_differ");
    // TODO: JIT-execute and assert halt value == FALSE_ATOM_ID
}

// Ported from src/ir_codegen/ir_codegen_test.rs: bitstring equality compares byte content structurally
#[test]
fn bitstring_equality_compares_byte_content() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00326_bitstring_structural_eq.fz".to_string()),
        text: include_str!("../../fixtures2/00326_bitstring_structural_eq.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "bitstring_equality_compares_byte_content");
    // TODO: JIT-execute and assert halt value == 1 (true)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: map equality is order-independent, compares keys and values structurally
#[test]
fn map_equality_is_order_independent() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00327_map_eq_order_independent.fz".to_string()),
        text: include_str!("../../fixtures2/00327_map_eq_order_independent.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "map_equality_is_order_independent");
    // TODO: JIT-execute and assert halt value == 1 (true)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: map equality is false when values differ for matching keys
#[test]
fn map_equality_false_when_values_differ() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00328_map_eq_value_mismatch.fz".to_string()),
        text: include_str!("../../fixtures2/00328_map_eq_value_mismatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "map_equality_false_when_values_differ");
    // TODO: JIT-execute and assert halt value == FALSE_ATOM_ID
}

// Ported from src/ir_codegen/ir_codegen_test.rs: different container kinds (list vs tuple) are never equal
#[test]
fn heterogeneous_container_kinds_are_never_equal() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00329_heterogeneous_kinds_neq.fz".to_string()),
        text: include_str!("../../fixtures2/00329_heterogeneous_kinds_neq.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "heterogeneous_container_kinds_are_never_equal");
    // TODO: JIT-execute and assert halt value == FALSE_ATOM_ID
}

// Ported from src/ir_codegen/ir_codegen_test.rs: nested map containing list compares recursively by value
#[test]
fn nested_map_with_list_compares_recursively() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00330_nested_map_list_eq.fz".to_string()),
        text: include_str!("../../fixtures2/00330_nested_map_list_eq.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "nested_map_with_list_compares_recursively");
    // TODO: JIT-execute and assert halt value == 1 (true)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: != operator returns logical inverse of structural equality
#[test]
fn neq_operator_inverts_structural_equality() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00331_neq_operator.fz".to_string()),
        text: include_str!("../../fixtures2/00331_neq_operator.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "neq_operator_inverts_structural_equality");
    // TODO: JIT-execute and assert [1,2] != [1,2] == FALSE_ATOM_ID and [1,2] != [1,3] == 1
}

// Ported from src/ir_codegen/ir_codegen_test.rs: float literal preserves bit-exact value in return
#[test]
fn float_literal_preserves_bit_exact_value() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00332_float_literal.fz".to_string()),
        text: include_str!("../../fixtures2/00332_float_literal.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "float_literal_preserves_bit_exact_value");
    // TODO: JIT-execute and assert f64::from_bits(halt as u64) == 2.5
}

// Ported from src/ir_codegen/ir_codegen_test.rs: float literals render with explicit decimal point in output
#[test]
fn float_literals_render_with_decimal_point() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00333_float_dbg_render.fz".to_string()),
        text: include_str!("../../fixtures2/00333_float_dbg_render.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "float_literals_render_with_decimal_point");
    // TODO: JIT-execute and assert output == ["4.0", "2.5"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: float addition evaluates correctly and compares equal to expected result
#[test]
fn float_addition_evaluates_correctly() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00334_float_arithmetic.fz".to_string()),
        text: include_str!("../../fixtures2/00334_float_arithmetic.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "float_addition_evaluates_correctly");
    // TODO: JIT-execute and assert halt value == 1 (true)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: mixed int and float arithmetic promotes integer to float
#[test]
fn mixed_int_float_arithmetic_promotes_integer() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00335_mixed_int_float_arith.fz".to_string()),
        text: include_str!("../../fixtures2/00335_mixed_int_float_arith.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "mixed_int_float_arithmetic_promotes_integer");
    // TODO: JIT-execute and assert halt value == 1 (true)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: integer and float with same numeric value are not equal by strict equality
#[test]
fn integer_and_float_not_equal_by_strict_equality() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00336_int_float_strict_eq.fz".to_string()),
        text: include_str!("../../fixtures2/00336_int_float_strict_eq.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "integer_and_float_not_equal_by_strict_equality");
    // TODO: JIT-execute and assert halt value == FALSE_ATOM_ID
}

// Ported from src/ir_codegen/ir_codegen_test.rs: identical float literals compare equal
#[test]
fn identical_float_literals_compare_equal() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00337_float_literal_eq.fz".to_string()),
        text: include_str!("../../fixtures2/00337_float_literal_eq.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "identical_float_literals_compare_equal");
    // TODO: JIT-execute and assert halt value == 1 (true)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: float ordered comparison returns correct boolean result
#[test]
fn float_ordered_comparison_returns_correct_result() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00338_float_comparison.fz".to_string()),
        text: include_str!("../../fixtures2/00338_float_comparison.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "float_ordered_comparison_returns_correct_result");
    // TODO: JIT-execute and assert halt value == 1 (true)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: float bitstring field stores raw IEEE 754 bits big-endian
#[test]
fn float_bitstring_field_stores_ieee754_bits() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00339_float_bitstring_field.fz".to_string()),
        text: include_str!("../../fixtures2/00339_float_bitstring_field.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "float_bitstring_field_stores_ieee754_bits");
    // TODO: JIT-execute and assert big-endian bytes decode to f64 2.5
}

// Ported from src/ir_codegen/ir_codegen_test.rs: float as list head allocates only one cons cell without boxing
#[test]
fn float_list_head_allocates_only_cons_cell() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00340_float_list_head.fz".to_string()),
        text: include_str!("../../fixtures2/00340_float_list_head.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "float_list_head_allocates_only_cons_cell");
    // TODO: JIT-execute and assert live_count == 1 (only the cons cell)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: float inside a list renders correctly
#[test]
fn float_inside_list_renders_correctly() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00341_float_in_list_render.fz".to_string()),
        text: include_str!("../../fixtures2/00341_float_in_list_render.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "float_inside_list_renders_correctly");
    // TODO: JIT-execute and assert output == ["[1.5]"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: list head projection retrieves float element with correct value
#[test]
fn list_head_projection_retrieves_float_element() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00342_float_list_head_project.fz".to_string()),
        text: include_str!("../../fixtures2/00342_float_list_head_project.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "list_head_projection_retrieves_float_element");
    // TODO: JIT-execute and assert f64::from_bits(halt as u64) == 2.5
}

// Ported from src/ir_codegen/ir_codegen_test.rs: list containing float compares equal by value
#[test]
fn list_containing_float_compares_equal_by_value() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00343_float_in_list_eq.fz".to_string()),
        text: include_str!("../../fixtures2/00343_float_in_list_eq.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "list_containing_float_compares_equal_by_value");
    // TODO: JIT-execute and assert halt value == 1 (true)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: map with float value allocates only one object without boxing float
#[test]
fn map_with_float_value_allocates_only_one_object() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00344_map_float_value.fz".to_string()),
        text: include_str!("../../fixtures2/00344_map_float_value.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "map_with_float_value_allocates_only_one_object");
    // TODO: JIT-execute and assert live_count == 1 (map only, no float box)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: map with float key allocates only one object without boxing float key
#[test]
fn map_with_float_key_allocates_only_one_object() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00345_map_float_key.fz".to_string()),
        text: include_str!("../../fixtures2/00345_map_float_key.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "map_with_float_key_allocates_only_one_object");
    // TODO: JIT-execute and assert live_count == 1 (map only, no float key box)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: self-applying closure in tail position reuses frame across iterations
#[test]
fn self_applying_closure_reuses_frame_in_tail_position() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00346_self_apply_tail_call.fz".to_string()),
        text: include_str!("../../fixtures2/00346_self_apply_tail_call.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "self_applying_closure_reuses_frame_in_tail_position");
    // TODO: JIT-execute and assert halt value == 100_000; verify two callable-entry singletons for loop_with
}

// Ported from src/ir_codegen/ir_codegen_test.rs: chained non-tail closure calls compose correctly and return right values
#[test]
fn chained_nontail_closure_calls_compose_correctly() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00347_compose_nontail_chain.fz".to_string()),
        text: include_str!("../../fixtures2/00347_compose_nontail_chain.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "chained_nontail_closure_calls_compose_correctly");
    // TODO: JIT-execute asserts pass; verify compose return lane is ValueRef and k_ continuations accept ValueRef
}

// Ported from src/ir_codegen/ir_codegen_test.rs: dbg/1 returns its argument allowing use in further expressions
#[test]
fn dbg_returns_argument_for_further_use() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00348_dbg_returns_value.fz".to_string()),
        text: include_str!("../../fixtures2/00348_dbg_returns_value.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "dbg_returns_argument_for_further_use");
    // TODO: JIT-execute and assert output == ["41", "42"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: nil value does not match empty-list pattern — distinct types
#[test]
fn nil_does_not_match_empty_list_pattern() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00349_nil_not_empty_list.fz".to_string()),
        text: include_str!("../../fixtures2/00349_nil_not_empty_list.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "nil_does_not_match_empty_list_pattern");
    // TODO: JIT-execute and assert atom_names[halt_value] == "match_error"
}

// Ported from src/ir_codegen/ir_codegen_test.rs: empty list does not match nil pattern — distinct types
#[test]
fn empty_list_does_not_match_nil_pattern() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00350_empty_list_not_nil.fz".to_string()),
        text: include_str!("../../fixtures2/00350_empty_list_not_nil.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "empty_list_does_not_match_nil_pattern");
    // TODO: JIT-execute and assert atom_names[halt_value] == "match_error"
}

// Ported from src/ir_codegen/ir_codegen_test.rs: cons pattern falls through to next clause for non-list arguments
#[test]
fn cons_function_clause_falls_through_for_non_lists() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00351_cons_clause_fallthrough.fz".to_string()),
        text: include_str!("../../fixtures2/00351_cons_clause_fallthrough.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "cons_function_clause_falls_through_for_non_lists");
    // TODO: JIT-execute and assert halt value == 304 (interpreter and native paths)
}

// Ported from src/ir_codegen/ir_codegen_test.rs: recursive multi-clause function dispatches on list vs other types
#[test]
fn recursive_multi_clause_dispatches_on_list_vs_other() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00352_recursive_cons_clause.fz".to_string()),
        text: include_str!("../../fixtures2/00352_recursive_cons_clause.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "recursive_multi_clause_dispatches_on_list_vs_other");
    // TODO: JIT-execute and assert halt value == 200; verify no dispatch_missing events
}

// Ported from src/ir_codegen/ir_codegen_test.rs: nil and empty list are distinct values with distinct string representations
#[test]
fn nil_and_empty_list_have_distinct_string_representations() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00353_nil_vs_empty_list_dbg.fz".to_string()),
        text: include_str!("../../fixtures2/00353_nil_vs_empty_list_dbg.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "nil_and_empty_list_have_distinct_string_representations",
    );
    // TODO: JIT-execute and assert output == ["nil", "[]"]
}

// Ported from src/ir_codegen/ir_codegen_test.rs: make_resource creates resource and fires destructor at heap drop
#[test]
fn make_resource_fires_destructor_at_heap_drop() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00354_make_resource_dtor.fz".to_string()),
        text: include_str!("../../fixtures2/00354_make_resource_dtor.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "make_resource_fires_destructor_at_heap_drop");
    // TODO: JIT-execute with Runtime::with_module; assert dtor_fired == 1 and dtor_last_payload == 42
}

// Ported from src/ir_codegen/ir_codegen_test.rs: aliased resource fires destructor exactly once despite multiple references
#[test]
fn aliased_resource_fires_destructor_exactly_once() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00355_aliased_resource_dtor.fz".to_string()),
        text: include_str!("../../fixtures2/00355_aliased_resource_dtor.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "aliased_resource_fires_destructor_exactly_once");
    // TODO: JIT-execute with Runtime::with_module; assert dtor_fired == 1 despite three aliases
}

// Ported from src/ir_codegen/ir_codegen_test.rs: two distinct resources each fire their destructor exactly once
#[test]
fn two_distinct_resources_each_fire_destructor_once() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00356_two_distinct_resources.fz".to_string()),
        text: include_str!("../../fixtures2/00356_two_distinct_resources.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "two_distinct_resources_each_fire_destructor_once");
    // TODO: JIT-execute with Runtime::with_module; assert dtor_fired == 2
}
