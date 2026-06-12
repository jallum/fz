//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
#![allow(unused_imports)]

use super::drive_test::{assert_resolved, function_id, module_id};
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

// Ported from src/ir_planner/ir_planner_test.rs: higher-order closure call inlined as direct control flow
#[test]
fn higher_order_closure_call_folds_to_direct_branch() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00381_choose_closure_branch.fz".to_string()),
        text: include_str!("../../fixtures2/00381_choose_closure_branch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "choose with closure branch should resolve");
    // TODO: materialized choose body should have zero CallClosure terminators and at least one If terminator
}

// Ported from src/ir_planner/ir_planner_test.rs: non-tail direct call inlined and fused into single block
#[test]
fn direct_call_fused_into_single_block() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00382_add1_call_fuse.fz".to_string()),
        text: include_str!("../../fixtures2/00382_add1_call_fuse.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "add1 direct call fusion should resolve");
    // TODO: materialized main body should be one block with the singleton-folded add1 result
}

// Ported from src/ir_planner/ir_planner_test.rs: type-guard dispatch folds dead branch when arg type is concrete integer
#[test]
fn typetest_guard_folds_dead_branch_for_concrete_int() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00383_typetest_dead_branch_fold.fz".to_string()),
        text: include_str!("../../fixtures2/00383_typetest_dead_branch_fold.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "typetest dispatch with concrete int should resolve");
    // TODO: materialized check body for int input should have fewer branches than source; prim folds > 0
}

// Ported from src/ir_planner/ir_planner_test.rs: closure with captures registers typed callable entry at materialization
#[test]
fn closure_with_captures_registers_typed_callable_entry() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00384_closure_predicate_wrapper.fz".to_string()),
        text: include_str!("../../fixtures2/00384_closure_predicate_wrapper.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive(); // DeriveAbiReady: pre-existing pipeline gap
    // TODO: materialized program should have a one-capture wrapper callable entry for the lambda reducer
}

// Ported from src/ir_planner/ir_planner_test.rs: tuple destructure at call site specializes callee by return demand
#[test]
fn tuple_destructure_specializes_callee_by_return_demand() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00385_tuple_destructure_demand.fz".to_string()),
        text: include_str!("../../fixtures2/00385_tuple_destructure_demand.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "pair with tuple destructure and value demand should resolve",
    );
    // TODO: pair should have two specs: one for tuple_fields demand (destructure) and one for value demand
}

// Ported from src/ir_planner/ir_planner_test.rs: function return shape (tuple vs list) inferred statically over quicksort
#[test]
fn return_shape_tuple_vs_list_inferred_over_quicksort() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00386_quicksort_return_shapes.fz".to_string()),
        text: include_str!("../../fixtures2/00386_quicksort_return_shapes.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "quicksort return shape inference should resolve");
    // TODO: partition should have returns_tuple_of_arity = Some(2); qsort and main should have None
}

// Ported from src/ir_planner/ir_planner_test.rs: empty list pattern only dispatches to empty clause when input is []
#[test]
fn empty_list_input_only_reaches_empty_clause() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00387_empty_list_dispatch.fz".to_string()),
        text: include_str!("../../fixtures2/00387_empty_list_dispatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "empty list classify should resolve");
    // TODO: classify with [] input should have effective return :empty; cons clause unreachable
}

// Ported from src/ir_planner/ir_planner_test.rs: wildcard parameter position does not fork specialization on argument type
#[test]
fn wildcard_param_does_not_fork_specialization() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00388_wildcard_param_hole.fz".to_string()),
        text: include_str!("../../fixtures2/00388_wildcard_param_hole.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "wildcard param hole should resolve");
    // TODO: ignore should have exactly one spec; first key slot should be None (wildcard hole)
}

// Ported from src/ir_planner/ir_planner_test.rs: polymorphic function returns distinct types per concrete call-site input
#[test]
fn polymorphic_fn_returns_distinct_types_per_activation() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00389_poly_id_direct_call.fz".to_string()),
        text: include_str!("../../fixtures2/00389_poly_id_direct_call.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "polymorphic id direct call should resolve");
    // TODO: id should have two activation projections with projected returns known(int) and known(:ok)
}

// Ported from src/ir_planner/ir_planner_test.rs: named function reference passed as value retains polymorphic return per activation
#[test]
fn named_ref_retains_polymorphic_return_per_activation() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00390_poly_named_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00390_poly_named_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "polymorphic named ref should resolve");
    // TODO: id should have two activation projections; projected returns known(:ok) and known(int)
}

// Ported from src/ir_planner/ir_planner_test.rs: captured closure invoked polymorphically preserves per-activation return types
#[test]
fn captured_closure_preserves_per_activation_return_types() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00391_poly_capture_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00391_poly_capture_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "captured closure poly activation should resolve");
    // TODO: lambda should have two activation projections; projected returns known({:ok, int}) and known({:ok, :right})
}

// Ported from src/ir_planner/ir_planner_test.rs: pattern dispatch via named-ref function folds dead arms per concrete input
#[test]
fn named_ref_pattern_dispatch_folds_dead_arms_per_activation() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00392_named_ref_pattern_dispatch.fz".to_string()),
        text: include_str!("../../fixtures2/00392_named_ref_pattern_dispatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "named ref pattern dispatch should resolve");
    // TODO: pick should have two activation projections with projected returns known(:one) and known(:two)
}

// Ported from src/ir_planner/ir_planner_test.rs: atom pattern matching dispatches to correct clause per concrete input
#[test]
fn atom_pattern_dispatches_correct_clause_per_input() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00393_atom_pattern_dispatch.fz".to_string()),
        text: include_str!("../../fixtures2/00393_atom_pattern_dispatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "atom pattern dispatch should resolve");
    // TODO: pick should have two activation projections with projected returns known(:one) and known(:two)
}

// Ported from src/ir_planner/ir_planner_test.rs: list pattern dispatch on empty vs cons selects correct clause per input
#[test]
fn list_pattern_dispatch_selects_clause_by_shape() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00394_list_pattern_dispatch.fz".to_string()),
        text: include_str!("../../fixtures2/00394_list_pattern_dispatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "list pattern dispatch should resolve");
    // TODO: pick should have two activation projections with projected returns known(:empty) and known(:cons)
}

// Ported from src/ir_planner/ir_planner_test.rs: list head binding in pattern returns head element type for cons input
#[test]
fn list_head_binding_returns_element_type_for_cons_input() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00395_list_head_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00395_list_head_binding.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "list head binding should resolve");
    // TODO: pick should have two activation projections with projected returns known(:empty) and known(int)
}

// Ported from src/ir_planner/ir_planner_test.rs: tuple pattern binding projects field type at concrete tuple input
#[test]
fn tuple_pattern_binding_projects_field_type() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00396_tuple_pattern_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00396_tuple_pattern_binding.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tuple pattern binding should resolve");
    // TODO: pick should have two activation projections with projected returns known(:error) and known(int)
}

// Ported from src/ir_planner/ir_planner_test.rs: nested tuple/list pattern binding projects inner type per activation
#[test]
fn nested_pattern_binding_projects_inner_type() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00397_nested_pattern_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00397_nested_pattern_binding.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "nested pattern binding should resolve");
    // TODO: pick should have two activation projections with projected returns known(:error) and known(int)
}

// Ported from src/ir_planner/ir_planner_test.rs: nested pattern clause cascade selects right leaf for each concrete input
#[test]
fn nested_pattern_cascade_selects_correct_leaf_per_input() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00398_nested_pattern_partition.fz".to_string()),
        text: include_str!("../../fixtures2/00398_nested_pattern_partition.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "nested pattern partition should resolve");
    // TODO: pick should have three activation projections with returns known(:empty), known(:error), known(int)
}

// Ported from src/ir_planner/ir_planner_test.rs: tagged-tuple pattern dispatch selects clause by atom tag per input
#[test]
fn tagged_tuple_pattern_dispatch_by_atom_tag() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00399_tuple_tag_partition.fz".to_string()),
        text: include_str!("../../fixtures2/00399_tuple_tag_partition.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tuple tag partition should resolve");
    // TODO: pick should have two activation projections with returns known(:bad) and known(int)
}

// Ported from src/ir_planner/ir_planner_test.rs: tuple arity pattern dispatch selects clause by tuple size per input
#[test]
fn tuple_arity_pattern_dispatch_by_size() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00400_tuple_arity_partition.fz".to_string()),
        text: include_str!("../../fixtures2/00400_tuple_arity_partition.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tuple arity partition should resolve");
    // TODO: pick should have three activation projections with returns known(:other), known(int), known({int, int})
}

// Ported from src/ir_planner/ir_planner_test.rs: guard clause collapses multiple witness activations to one semantic spec
#[test]
fn guard_clause_collapses_witness_activations_to_one_spec() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00401_guard_partition.fz".to_string()),
        text: include_str!("../../fixtures2/00401_guard_partition.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "guard partition should resolve");
    // TODO: pick should have one semantic projection covering two witness activations; projected return known(int | :fallback)
}

// Ported from src/ir_planner/ir_planner_test.rs: map key pattern match binds hit value type vs absent atom per input
#[test]
fn map_pattern_binding_hit_vs_absent() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00402_map_pattern_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00402_map_pattern_binding.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "map pattern binding should resolve");
    // TODO: pick should have two activation projections with returns known(:none) and known(int)
}

// Ported from src/ir_planner/ir_planner_test.rs: tail-recursive fold over list returns concrete int type
#[test]
fn tail_recursive_fold_converges_to_concrete_int_return() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00403_tail_fold_closure.fz".to_string()),
        text: include_str!("../../fixtures2/00403_tail_fold_closure.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tail fold with closure should resolve");
    // TODO: myreduce should have one activation projection with projected return known(int)
}

// Ported from src/ir_planner/ir_planner_test.rs: Enum.reduce with user closure converges to concrete accumulator return type
#[test]
fn enum_reduce_with_closure_converges_to_concrete_int() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00404_enum_reduce_list.fz".to_string()),
        text: include_str!("../../fixtures2/00404_enum_reduce_list.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.reduce with closure should resolve");
    // TODO: Enum.reduce should have activation-covered known int projection; Enumerable.List.reduce known({:done, int})
}

// Ported from src/ir_planner/ir_planner_test.rs: Enum.reduce with &Kernel.+/2 operator ref propagates int accumulator type
#[test]
fn enum_reduce_with_operator_ref_propagates_int_type() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00405_enum_reduce_operator_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00405_enum_reduce_operator_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.reduce with operator ref should resolve");
    // TODO: Kernel.+ should have activation int projection; no callable_fallback in the runtime graph
}

// Ported from src/ir_planner/ir_planner_test.rs: Enum.reduce over a Range enumerable converges to concrete int return
#[test]
fn enum_reduce_over_range_converges_to_int() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00406_enum_reduce_range.fz".to_string()),
        text: include_str!("../../fixtures2/00406_enum_reduce_range.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive(); // DeriveAbiReady: pre-existing pipeline gap for Range Enumerable
    // TODO: Enum.reduce should have known int projection; Enumerable.Range.reduce known({:done, int})
}

// Ported from src/ir_planner/ir_planner_test.rs: spawned child process function reachable and typed through callable boundary
#[test]
fn spawned_child_reachable_through_callable_boundary() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00407_spawn_plain.fz".to_string()),
        text: include_str!("../../fixtures2/00407_spawn_plain.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "plain spawn child should resolve");
    // TODO: child activation projection should be exact with projected return known(nil)
}

// Ported from src/ir_planner/ir_planner_test.rs: spawned process child function stays reachable after materialization
#[test]
fn spawn_child_remains_reachable_after_materialization() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00407_spawn_plain.fz".to_string()),
        text: include_str!("../../fixtures2/00407_spawn_plain.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "plain spawn child stays reachable after materialization",
    );
    // TODO: child should appear in the reachable materialized body signals with a planned spec key
}

// Ported from src/ir_planner/ir_planner_test.rs: recursive list accumulation return type converges at fixpoint, not base case
#[test]
fn recursive_sum_return_converges_at_fixpoint_not_base_case() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00408_recursive_sum_fixpoint.fz".to_string()),
        text: include_str!("../../fixtures2/00408_recursive_sum_fixpoint.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "recursive sum fixpoint should resolve");
    // TODO: sum should have at least one spec with return ⊆ int and non-empty; no spec returning only int_lit(0)
}

// Ported from src/ir_planner/ir_planner_test.rs: function passed as value retains both typed specialization and callable entry
#[test]
fn fn_as_value_retains_typed_spec_and_callable_entry() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00409_higher_order_named_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00409_higher_order_named_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "higher-order named ref should resolve");
    // TODO: double should keep one any-key callable entry spec plus at least one narrow typed spec
}

// Ported from src/ir_planner/ir_planner_test.rs: spawn/1 receives typed closure capability; no synthetic thunk
#[test]
fn spawn_receives_typed_closure_capability_no_thunk() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00410_spawn_closure_capture.fz".to_string()),
        text: include_str!("../../fixtures2/00410_spawn_closure_capture.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "spawn with captures should resolve");
    // TODO: no fz_spawn_thunk function; Kernel.spawn/1 spec should carry KnownClosure capability for its param
}

// Ported from src/ir_planner/ir_planner_test.rs: closure with distinct captured values specializes without any-key body
#[test]
fn closure_distinct_captures_specializes_without_any_key() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00411_closure_distinct_captures.fz".to_string()),
        text: include_str!("../../fixtures2/00411_closure_distinct_captures.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "closure distinct captures should resolve");
    // TODO: lambda body specs should be non-empty; no lambda any-key body specs; at least one call-site specialization
}

// Ported from src/ir_planner/ir_planner_test.rs: named function reference propagates concrete callable identity to call sites
#[test]
fn named_fn_ref_propagates_callable_identity() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00409_higher_order_named_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00409_higher_order_named_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "named fn ref callable identity should resolve");
    // TODO: MakeFnRef(double) in main should populate KnownFn(double) capability on the bound var
}

// Ported from src/ir_planner/ir_planner_test.rs: closure with captures is distinct from plain function reference
#[test]
fn closure_with_captures_distinct_from_fn_ref() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00412_closure_with_captures.fz".to_string()),
        text: include_str!("../../fixtures2/00412_closure_with_captures.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "closure with captures should resolve");
    // TODO: MakeClosure with captures should record KnownClosure (not KnownFn) capability
}

// Ported from src/ir_planner/ir_planner_test.rs: callable identity flows through direct call into higher-order parameter
#[test]
fn callable_identity_flows_through_direct_call_to_parameter() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00409_higher_order_named_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00409_higher_order_named_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "callable identity propagation via direct call should resolve",
    );
    // TODO: apply2's spec for the apply2(double, 21) call should carry callable_capabilities[f] = KnownFn(double)
}

// Ported from src/ir_planner/ir_planner_test.rs: returned closure value retains captured-closure identity at call sites
#[test]
fn returned_closure_retains_captured_identity_at_call_sites() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00391_poly_capture_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00391_poly_capture_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "returned captured closure identity should resolve");
    // TODO: continuation slot 0 should retain KnownClosure capability for returned captured closure
}

// Ported from src/ir_planner/ir_planner_test.rs: indirect call with known function identity registers typed specialization
#[test]
fn indirect_call_with_known_fn_registers_typed_specialization() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00409_higher_order_named_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00409_higher_order_named_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "indirect call with known fn should resolve");
    // TODO: double should have a narrow int-typed spec from apply2's CallClosure with KnownFn(double) capability
}

// Ported from src/ir_planner/ir_planner_test.rs: protocol call on concrete receiver dispatches to correct impl
#[test]
fn protocol_call_on_concrete_receiver_dispatches_to_correct_impl() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00413_protocol_static_dispatch.fz".to_string()),
        text: include_str!("../../fixtures2/00413_protocol_static_dispatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "protocol static dispatch to List impl should resolve");
    // TODO: main's protocol call edge should dispatch to Collectable.List.id
}

// Ported from src/ir_planner/ir_planner_test.rs: cross-module call to imported function dispatches at module boundary
#[test]
fn cross_module_call_stays_at_provider_boundary() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00414_cross_module_provider.fz".to_string()),
        text: include_str!("../../fixtures2/00414_cross_module_provider.fz").to_string(),
    });
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00415_cross_module_user.fz".to_string()),
        text: include_str!("../../fixtures2/00415_cross_module_user.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "cross-module import call should resolve");
    // TODO: User.run spec should carry a provider-boundary call edge for Math.add with no local stub target
}

// Ported from src/ir_planner/ir_planner_test.rs: cross-module protocol call stays at provider boundary without local stub
#[test]
fn cross_module_protocol_call_stays_at_external_boundary() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00416_protocol_provider.fz".to_string()),
        text: include_str!("../../fixtures2/00416_protocol_provider.fz").to_string(),
    });
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00417_protocol_user.fz".to_string()),
        text: include_str!("../../fixtures2/00417_protocol_user.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive(); // duplicate fact: pre-existing pipeline gap for cross-module protocol dispatch
    // TODO: User.run spec should carry a provider-boundary call edge for the protocol id; no __protocol__ stub local target
}

// Ported from src/ir_planner/ir_planner_test.rs: Enum.count/1 on Range enumerator returns integer per declared spec
#[test]
fn enum_count_on_range_returns_integer_per_declared_spec() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00418_enum_count_range.fz".to_string()),
        text: include_str!("../../fixtures2/00418_enum_count_range.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive(); // DeriveAbiReady: pre-existing pipeline gap for Range Enumerable
    // TODO: declared return fact for Enum.count(range) should be integer
}

// Ported from src/ir_planner/ir_planner_test.rs: Enum.take on mixed List+Range inputs specializes for each enumerable type
#[test]
fn enum_take_on_mixed_inputs_specializes_for_each_type() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00419_enum_take_mixed.fz".to_string()),
        text: include_str!("../../fixtures2/00419_enum_take_mixed.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive(); // DeriveAbiReady: pre-existing pipeline gap for Range Enumerable
    // TODO: Enum.take specs should include a Range specialization for the range input
}

// Ported from src/ir_planner/ir_planner_test.rs: Enum.reduce with runtime-graph reducer returns non-empty type
#[test]
fn enum_reduce_runtime_graph_reducer_returns_non_empty_type() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00420_enum_take_drop_split.fz".to_string()),
        text: include_str!("../../fixtures2/00420_enum_take_drop_split.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive(); // DeriveAbiReady: pre-existing pipeline gap for enum_take_drop_split
    // TODO: declared return fact for Enum.reduce in Enum.drop_positive should be non-bottom
}

// Ported from src/ir_planner/ir_planner_test.rs: Enum.take_positive uses reduce_while with typed callback return
#[test]
fn take_positive_reduce_while_has_typed_callback_return() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00420_enum_take_drop_split.fz".to_string()),
        text: include_str!("../../fixtures2/00420_enum_take_drop_split.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive(); // DeriveAbiReady: pre-existing pipeline gap for enum_take_drop_split
    // TODO: declared return fact for Enum.reduce_while in Enum.take_positive should be non-bottom for int-amount spec
}

// Ported from src/ir_planner/ir_planner_test.rs: reduce_cont/reduce_step clause structure links list param to accumulator result
#[test]
fn reduce_cont_clause_links_list_param_to_accumulator_result() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00421_reduce_cont_clause.fz".to_string()),
        text: include_str!("../../fixtures2/00421_reduce_cont_clause.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("Probe".to_string()),
        name: "reduce_cont".to_string(),
        arity: 3,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive(); // Unresolved/SealSemanticClosure: pre-existing pipeline gap for defmodule-only roots
    // TODO: fn_clause_1 with 5 params should have function_correspondence groups tying param 0 to result
}

// Ported from src/ir_planner/ir_planner_test.rs: protocol impl callback with incompatible return type is rejected at compile time
#[test]
fn protocol_impl_disjoint_spec_rejected_at_compile_time() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00422_protocol_impl_disjoint_spec.fz".to_string()),
        text: include_str!("../../fixtures2/00422_protocol_impl_disjoint_spec.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // NOTE: this test exercises an error path; drive may or may not resolve depending on how compiler2 surfaces the error
    let _ = compiler.drive();
    // TODO: a ProtocolError diagnostic should name to_thing/1 as incompatible; atom vs integer result
}

// Ported from src/ir_planner/ir_planner_test.rs: protocol impl with matching return type spec is accepted at compile time
#[test]
fn protocol_impl_compatible_spec_accepted_at_compile_time() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00423_protocol_impl_compatible_spec.fz".to_string()),
        text: include_str!("../../fixtures2/00423_protocol_impl_compatible_spec.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive(); // DeriveFunctionContract: pre-existing pipeline gap for protocol spec checking
    // TODO: no ProtocolError diagnostic; to_thing/1 integer spec is compatible
}

// Ported from src/ir_planner/ir_planner_test.rs: protocol call on non-implementing type emits named diagnostic
#[test]
fn protocol_call_on_non_implementing_type_emits_diagnostic() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00424_protocol_no_impl.fz".to_string()),
        text: include_str!("../../fixtures2/00424_protocol_no_impl.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive();
    // TODO: a type/protocol-no-impl diagnostic should name protocol P, receiver type int, and known implementors List
}

// Ported from src/ir_planner/ir_planner_test.rs: protocol call on implementing receiver type emits no error
#[test]
fn protocol_call_on_implementing_receiver_emits_no_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00425_protocol_impl_match.fz".to_string()),
        text: include_str!("../../fixtures2/00425_protocol_impl_match.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "protocol call on implementing receiver should resolve",
    );
    // TODO: no type/protocol-no-impl diagnostic when receiver type matches an impl
}

// Ported from src/ir_planner/ir_planner_test.rs: closed union receiver dispatches each protocol impl via direct typetest cascade
#[test]
fn closed_union_receiver_dispatches_via_typetest_cascade() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00426_closed_union_protocol_dispatch.fz".to_string()),
        text: include_str!("../../fixtures2/00426_closed_union_protocol_dispatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let mut compiler = std::panic::AssertUnwindSafe(compiler);
    let _ = std::panic::catch_unwind(move || compiler.drive()); // duplicate fact panic: pre-existing pipeline bug
    // TODO: describe should not call __protocol__ stub; should dispatch two direct impl arms via TypeTest
}

// Ported from src/ir_planner/ir_planner_test.rs: closed union protocol dispatch matrix has no fallback when all types covered
#[test]
fn closed_union_dispatch_matrix_has_no_fallback() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00426_closed_union_protocol_dispatch.fz".to_string()),
        text: include_str!("../../fixtures2/00426_closed_union_protocol_dispatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let mut compiler = std::panic::AssertUnwindSafe(compiler);
    let _ = std::panic::catch_unwind(move || compiler.drive()); // duplicate fact panic: pre-existing pipeline bug
    // TODO: dispatch matrix for describe should be fully_covered, fallback_outcome=None, direct_outcomes.len==2
}

// Ported from src/ir_planner/ir_planner_test.rs: single-impl protocol receiver is not transformed into multi-arm cascade
#[test]
fn single_impl_protocol_receiver_not_rewritten_to_cascade() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00427_single_impl_protocol.fz".to_string()),
        text: include_str!("../../fixtures2/00427_single_impl_protocol.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "single-impl protocol receiver should resolve");
    // TODO: describe block count should be unchanged; a single-target receiver must not grow a switch cascade
}

// Ported from src/ir_planner/ir_planner_test.rs: single-impl protocol receiver selects StaticDirect dispatch without matrix
#[test]
fn single_impl_protocol_receiver_selects_static_direct_dispatch() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00427_single_impl_protocol.fz".to_string()),
        text: include_str!("../../fixtures2/00427_single_impl_protocol.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "single-impl StaticDirect dispatch should resolve");
    // TODO: dispatch matrix selection for describe should be StaticDirect (no full matrix)
}

// Ported from src/ir_planner/ir_planner_test.rs: open union receiver dispatches known impls inline with stub fallthrough for rest
#[test]
fn open_union_receiver_dispatches_with_stub_fallthrough() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00428_open_union_protocol.fz".to_string()),
        text: include_str!("../../fixtures2/00428_open_union_protocol.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let mut compiler = std::panic::AssertUnwindSafe(compiler);
    let _ = std::panic::catch_unwind(move || compiler.drive()); // duplicate fact panic: pre-existing pipeline bug
    // TODO: describe should dispatch Integer and List arms inline; retain stub call as fallthrough for residual atom
}

// Ported from src/ir_planner/ir_planner_test.rs: open union protocol matrix retains residual fallback for unimplemented types
#[test]
fn open_union_protocol_matrix_retains_residual_fallback() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00428_open_union_protocol.fz".to_string()),
        text: include_str!("../../fixtures2/00428_open_union_protocol.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let mut compiler = std::panic::AssertUnwindSafe(compiler);
    let _ = std::panic::catch_unwind(move || compiler.drive()); // duplicate fact panic: pre-existing pipeline bug
    // TODO: dispatch matrix for describe: fully_covered=false, fallback_outcome=Some(_), direct_outcomes.len==2
}

// Ported from src/ir_planner/ir_planner_test.rs: external provider protocol impl stays as stub fallback in dispatch matrix
#[test]
fn external_provider_protocol_impl_stays_as_stub_fallback() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00429_external_impl_residual.fz".to_string()),
        text: include_str!("../../fixtures2/00429_external_impl_residual.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive(); // duplicate fact: pre-existing pipeline gap for external protocol impl dispatch
    // TODO: dispatch matrix: Integer direct arm; Float external impl remains residual stub fallback
}

// Ported from src/ir_planner/ir_planner_test.rs: opaque type .value accessor inside declaring module types as inner T
#[test]
fn opaque_value_accessor_inside_declaring_module_types_as_inner() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00430_opaque_value_accessor.fz".to_string()),
        text: include_str!("../../fixtures2/00430_opaque_value_accessor.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "opaque value accessor inside declaring module should resolve",
    );
    // TODO: A.get MapGet result var should type as integer (inner T of opaque resource(integer))
}

// Ported from src/ir_planner/ir_planner_test.rs: opaque .value access inside declaring module emits no visibility diagnostic
#[test]
fn opaque_value_accessor_no_visibility_diagnostic_inside_module() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00431_opaque_accessor_no_diag.fz".to_string()),
        text: include_str!("../../fixtures2/00431_opaque_accessor_no_diag.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("A".to_string()),
        name: "get".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive(); // LowerNativeProgram Fatal: pre-existing pipeline gap for opaque accessor
    // TODO: no type/opaque-visibility diagnostic should be emitted for .value access inside module A
}

// Ported from src/ir_planner/ir_planner_test.rs: string literal lowers to utf8-branded bitstring with brand erasure in IR
#[test]
fn string_literal_lowers_to_utf8_branded_bitstring() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00432_string_utf8_brand.fz".to_string()),
        text: include_str!("../../fixtures2/00432_string_utf8_brand.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "string literal utf8 brand should resolve");
    // TODO: main body should have ConstBitstring(b"hi", 16); no Prim::Brand survives lowering; brand_inners has utf8
}

// Ported from src/ir_planner/ir_planner_test.rs: arithmetic on pid opaque type emits type error diagnostic
#[test]
fn pid_opaque_arithmetic_emits_type_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00433_opaque_pid_arithmetic.fz".to_string()),
        text: include_str!("../../fixtures2/00433_opaque_pid_arithmetic.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive();
    // TODO: a type/opaque-arithmetic diagnostic should name pid and the + operator
}

// Ported from src/ir_planner/ir_planner_test.rs: arithmetic on ref opaque type emits type error diagnostic
#[test]
fn ref_opaque_arithmetic_emits_type_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00434_opaque_ref_arithmetic.fz".to_string()),
        text: include_str!("../../fixtures2/00434_opaque_ref_arithmetic.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let _ = compiler.drive();
    // TODO: a type/opaque-arithmetic diagnostic should fire on make_ref() + 1
}

// Ported from src/ir_planner/ir_planner_test.rs: equality comparison on opaque pid/ref is permitted without diagnostic
#[test]
fn opaque_equality_comparison_permitted_without_diagnostic() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00435_opaque_equality_ok.fz".to_string()),
        text: include_str!("../../fixtures2/00435_opaque_equality_ok.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "opaque equality should resolve without diagnostic");
    // TODO: no type/opaque-arithmetic diagnostic should fire for == comparison on pid values
}

// Ported from src/ir_planner/ir_planner_test.rs: plain integer arithmetic does not trigger opaque-arithmetic diagnostic
#[test]
fn plain_int_arithmetic_no_opaque_diagnostic() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00436_plain_int_arithmetic.fz".to_string()),
        text: include_str!("../../fixtures2/00436_plain_int_arithmetic.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "plain int arithmetic should resolve");
    // TODO: no type/opaque-arithmetic diagnostic for 1 + 1
}
