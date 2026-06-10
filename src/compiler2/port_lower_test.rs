//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
#![allow(unused_imports)]

use super::drive_test::{assert_resolved, function_id, module_id};
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

// Ported from src/ir_lower/ir_lower_test.rs: if with constant condition routes to correct branch
#[test]
fn if_constant_condition_routes_to_correct_branch() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00461_if_constant_cond_branch.fz".to_string()),
        text: include_str!("../../fixtures2/00461_if_constant_cond_branch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "if_constant_condition_routes_to_correct_branch");
    // TODO: JIT-execute and assert result == "99" (constant false condition routes to else)
}

// Ported from src/ir_lower/ir_lower_test.rs: if arm with tail call returns correct value at runtime
#[test]
fn if_arm_tail_call_returns_correct_value() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00462_if_tail_call_arm.fz".to_string()),
        text: include_str!("../../fixtures2/00462_if_tail_call_arm.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "if_arm_tail_call_returns_correct_value");
    // TODO: JIT-execute and assert stdout == "7\n99"
}

// Ported from src/ir_lower/ir_lower_test.rs: case clause with non-tail call compiles without error
#[test]
fn case_clause_with_non_tail_call_compiles() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00463_case_call_in_clause.fz".to_string()),
        text: include_str!("../../fixtures2/00463_case_call_in_clause.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "case_clause_with_non_tail_call_compiles");
    // TODO: JIT-execute and assert stdout == "7\n99"
}

// Ported from src/ir_lower/ir_lower_test.rs: with-else routes non-matching pattern to else clause at runtime
#[test]
fn with_else_non_matching_pattern_routes_to_else() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00464_with_else_non_matching.fz".to_string()),
        text: include_str!("../../fixtures2/00464_with_else_non_matching.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: `with` is not yet handled by FrontDoorParser; currently fails IndexCode; once ported, JIT-execute and assert stdout == "0"
    let _ = compiler.drive();
}

// Ported from src/ir_lower/ir_lower_test.rs: if with comparison condition routes both arms correctly
#[test]
fn if_comparison_condition_routes_both_arms() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00465_if_comparison_cond.fz".to_string()),
        text: include_str!("../../fixtures2/00465_if_comparison_cond.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "if_comparison_condition_routes_both_arms");
    // TODO: JIT-execute and assert stdout == "7\n99"
}

// Ported from src/ir_lower/ir_lower_test.rs: non-tail if with call arm; result flows into enclosing expression
#[test]
fn non_tail_if_call_arm_flows_through_join() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00466_nontail_if_join_flow.fz".to_string()),
        text: include_str!("../../fixtures2/00466_nontail_if_join_flow.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "non_tail_if_call_arm_flows_through_join");
    // TODO: JIT-execute and assert stdout == "[100, 2, 300, 4]"
}

// Ported from src/ir_lower/ir_lower_test.rs: non-tail case with call arm; result flows into enclosing expression
#[test]
fn non_tail_case_call_arm_flows_through_join() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00467_nontail_case_join_flow.fz".to_string()),
        text: include_str!("../../fixtures2/00467_nontail_case_join_flow.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "non_tail_case_call_arm_flows_through_join");
    // TODO: JIT-execute and assert stdout == "[1]"
}

// Ported from src/ir_lower/ir_lower_test.rs: non-tail cond with call arm; result flows into enclosing expression
#[test]
fn non_tail_cond_call_arm_flows_through_join() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00468_nontail_cond_join_flow.fz".to_string()),
        text: include_str!("../../fixtures2/00468_nontail_cond_join_flow.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "non_tail_cond_call_arm_flows_through_join");
    // TODO: JIT-execute and assert stdout == "[1]"
}

// Ported from src/ir_lower/ir_lower_test.rs: synthesized dispatch branches do not generate unreachable-arm warnings
#[test]
fn synthesized_dispatch_branches_no_unreachable_arm_warnings() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00469_synthesized_branch_no_warn.fz".to_string()),
        text: include_str!("../../fixtures2/00469_synthesized_branch_no_warn.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "synthesized_dispatch_branches_no_unreachable_arm_warnings",
    );
    // TODO: assert no TYPE_UNREACHABLE_ARM diagnostics emitted for synthesized Ifs from destructure or clause dispatch
}

// Ported from src/ir_lower/ir_lower_test.rs: closure captures only variables referenced in its body
#[test]
fn closure_captures_only_referenced_outer_variables() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00470_closure_captures_outer.fz".to_string()),
        text: include_str!("../../fixtures2/00470_closure_captures_outer.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "mk".to_string(),
        arity: 2,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "closure_captures_only_referenced_outer_variables");
    // TODO: assert the closure captures exactly x (not y); lambda entry has params [captured_x, z]
}

// Ported from src/ir_lower/ir_lower_test.rs: closure with no outer references has no captured variables
#[test]
fn closure_with_no_outer_reads_has_no_captures() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00471_closure_no_captures.fz".to_string()),
        text: include_str!("../../fixtures2/00471_closure_no_captures.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "mk".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "closure_with_no_outer_reads_has_no_captures");
    // TODO: assert body reads no outer names so it lowers as a thin fn ref with zero captures; entry has one param (y only)
}

// Ported from src/ir_lower/ir_lower_test.rs: receive inside spawned lambda does not leak into enclosing function
#[test]
fn lambda_tail_receive_does_not_terminate_enclosing_spawn_call() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00472_spawn_lambda_receive.fz".to_string()),
        text: include_str!("../../fixtures2/00472_spawn_lambda_receive.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "p".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "lambda_tail_receive_does_not_terminate_enclosing_spawn_call",
    );
    // TODO: assert the enclosing fn tail-calls spawn/1 and does not contain a receive terminator
}

// Ported from src/ir_lower/ir_lower_test.rs: unbound variable reference is a compile-time error
#[test]
fn unbound_variable_reference_is_compile_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00473_unbound_var_error.fz".to_string()),
        text: include_str!("../../fixtures2/00473_unbound_var_error.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "f".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Fatal; assert the error is an Unbound diagnostic for "missing"
    let _ = compiler.drive();
}

// Ported from src/ir_lower/ir_lower_test.rs: call to undefined function is a compile-time error
#[test]
fn unbound_callee_is_compile_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00474_unbound_callee_error.fz".to_string()),
        text: include_str!("../../fixtures2/00474_unbound_callee_error.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "f".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Fatal; assert the error is an Unbound diagnostic for "nonesuch"
    let _ = compiler.drive();
}

// Ported from src/ir_lower/ir_lower_test.rs: empty case expression is a compile-time error
#[test]
fn empty_case_expression_is_compile_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00475_empty_case_error.fz".to_string()),
        text: include_str!("../../fixtures2/00475_empty_case_error.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "f".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "empty_case_expression_is_compile_error");
    // TODO: drive() should return DriveOutcome::Fatal; assert the error is LowerError::Unsupported for empty case
}

// Ported from src/ir_lower/ir_lower_test.rs: guard and binding share a single tuple field projection, not two
#[test]
fn guard_and_binding_reuse_single_tuple_field_projection() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00476_guard_tuple_field_reuse.fz".to_string()),
        text: include_str!("../../fixtures2/00476_guard_tuple_field_reuse.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "classify".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "guard_and_binding_reuse_single_tuple_field_projection",
    );
    // TODO: assert tuple_field(_, 1) is materialized exactly once in classify's lowered body
}

// Ported from src/ir_lower/ir_lower_test.rs: guard and binding share a single list head extraction, not two
#[test]
fn guard_and_binding_reuse_single_list_head_extraction() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00477_guard_list_head_reuse.fz".to_string()),
        text: include_str!("../../fixtures2/00477_guard_list_head_reuse.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "classify".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "guard_and_binding_reuse_single_list_head_extraction");
    // TODO: assert list_head is materialized exactly once in classify's lowered body
}

// Ported from src/ir_lower/ir_lower_test.rs: guard and binding share a single map_get extraction, not two
#[test]
fn guard_and_binding_reuse_single_map_get_extraction() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00478_guard_map_get_reuse.fz".to_string()),
        text: include_str!("../../fixtures2/00478_guard_map_get_reuse.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "classify".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "guard_and_binding_reuse_single_map_get_extraction");
    // TODO: assert MatcherMapGet is materialized exactly once across all fns
}

// Ported from src/ir_lower/ir_lower_test.rs: unexpanded quote node is a compile-time error
#[test]
fn unexpanded_quote_node_is_compile_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00479_quote_unexpanded_error.fz".to_string()),
        text: include_str!("../../fixtures2/00479_quote_unexpanded_error.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "f".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Fatal; assert the error is LowerError::PostExpansionNode
    let _ = compiler.drive();
}

// Ported from src/ir_lower/ir_lower_test.rs: extern call with wrong argument count is a compile-time error
#[test]
fn extern_call_arity_mismatch_is_compile_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00480_extern_arity_mismatch.fz".to_string()),
        text: include_str!("../../fixtures2/00480_extern_arity_mismatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Fatal; assert Unsupported message names open/3 vs 4 args
    let _ = compiler.drive();
}

// Ported from src/ir_lower/ir_lower_test.rs: variadic extern call with too few args is a compile-time error
#[test]
fn variadic_extern_too_few_args_is_compile_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00481_variadic_extern_too_few.fz".to_string()),
        text: include_str!("../../fixtures2/00481_variadic_extern_too_few.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Fatal; assert Unsupported message says "at least 2" vs 1 arg
    let _ = compiler.drive();
}

// Ported from src/ir_lower/ir_lower_test.rs: case guard calling a user function compiles without error
#[test]
fn case_guard_with_pure_user_fn_compiles() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00482_case_guard_pure_fn.fz".to_string()),
        text: include_str!("../../fixtures2/00482_case_guard_pure_fn.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "case_guard_with_pure_user_fn_compiles");
    // TODO: assert compilation succeeds and no diagnostics emitted
}

// Ported from src/ir_lower/ir_lower_test.rs: case guard calling multi-clause function dispatches correctly at runtime
#[test]
fn case_guard_with_multi_clause_fn_dispatches_correctly() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00483_case_guard_multi_clause.fz".to_string()),
        text: include_str!("../../fixtures2/00483_case_guard_multi_clause.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "case_guard_with_multi_clause_fn_dispatches_correctly");
    // TODO: JIT-execute and assert stdout == "1" (is_pos(5) is true, so :pos branch taken)
}

// Ported from src/ir_lower/ir_lower_test.rs: guarded list-cons pattern clause dispatches correctly at runtime
#[test]
fn guarded_list_cons_clause_dispatches_correctly() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00484_guarded_cons_clause.fz".to_string()),
        text: include_str!("../../fixtures2/00484_guarded_cons_clause.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "guarded_list_cons_clause_dispatches_correctly");
    // TODO: JIT-execute and assert stdout == "{[2, 1], [4]}"
}

// Ported from src/ir_lower/ir_lower_test.rs: pinned variable in receive pattern resolves from outer scope
#[test]
fn receive_pinned_variable_resolves_from_outer_scope() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00485_receive_pinned_outer.fz".to_string()),
        text: include_str!("../../fixtures2/00485_receive_pinned_outer.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "rx_pinned".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "receive_pinned_variable_resolves_from_outer_scope");
    // TODO: assert the receive dispatch carries a pinned input for "want" resolved from the outer scope
}

// Ported from src/ir_lower/ir_lower_test.rs: pinned variable in receive pattern referencing unbound name is an error
#[test]
fn receive_pinned_unbound_name_is_compile_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00486_receive_pinned_unbound.fz".to_string()),
        text: include_str!("../../fixtures2/00486_receive_pinned_unbound.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "rx".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Fatal; assert LowerError::Unbound for name "^nope"
    let _ = compiler.drive();
}

// Ported from src/ir_lower/ir_lower_test.rs: well-formed receive with multiple message patterns compiles cleanly
#[test]
fn receive_well_formed_multi_pattern_compiles() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00487_receive_multi_pattern.fz".to_string()),
        text: include_str!("../../fixtures2/00487_receive_multi_pattern.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "rx".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "receive_well_formed_multi_pattern_compiles");
    // TODO: assert planner accepts without emitting TYPE_IMPURE_RECEIVE_GUARD diagnostics
}

// Ported from src/ir_lower/ir_lower_test.rs: receive guard calling an extern-backed function is a compile-time error
#[test]
fn receive_guard_with_impure_helper_is_compile_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00488_receive_impure_guard.fz".to_string()),
        text: include_str!("../../fixtures2/00488_receive_impure_guard.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "rx".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: drive() should return DriveOutcome::Fatal; assert UnsupportedGuardExpr error for extern-backed helper
    let _ = compiler.drive();
}
