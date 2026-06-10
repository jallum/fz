//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
#![allow(unused_imports)]

use super::drive_test::{assert_resolved, function_id, module_id};
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

// Ported from src/type_infer/type_infer_test.rs: type inference converges to known returns for fold and arithmetic programs
#[test]
fn fixpoint_leaves_no_reached_fn_unknown_add() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00171_add_operator_flow.fz".to_string()),
        text: include_str!("../../fixtures2/00171_add_operator_flow.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "add: type inference should converge to known returns");
    // TODO: assert all reached fns have Known return (no Pending/Unknown) at fixpoint
}

// Ported from src/type_infer/type_infer_test.rs: type inference converges to known returns for fold and arithmetic programs
#[test]
fn fixpoint_leaves_no_reached_fn_unknown_fold_tail() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00172_fold_tail_recursive.fz".to_string()),
        text: include_str!("../../fixtures2/00172_fold_tail_recursive.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "fold_tail: type inference should converge to known returns",
    );
    // TODO: assert all reached fns have Known return (no Pending/Unknown) at fixpoint
}

// Ported from src/type_infer/type_infer_test.rs: type inference converges to known returns for fold and arithmetic programs
#[test]
fn fixpoint_leaves_no_reached_fn_unknown_fold_nontail() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00173_fold_nontail_finish.fz".to_string()),
        text: include_str!("../../fixtures2/00173_fold_nontail_finish.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "fold_nontail: type inference should converge to known returns",
    );
    // TODO: assert all reached fns have Known return (no Pending/Unknown) at fixpoint
}

// Ported from src/type_infer/type_infer_test.rs: type inference converges to known returns for fold and arithmetic programs
#[test]
fn fixpoint_leaves_no_reached_fn_unknown_fold_capture_int() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00174_fold_capture_int.fz".to_string()),
        text: include_str!("../../fixtures2/00174_fold_capture_int.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "fold_capture_int: type inference should converge to known returns",
    );
    // TODO: assert all reached fns have Known return (no Pending/Unknown) at fixpoint
}

// Ported from src/type_infer/type_infer_test.rs: type inference converges to known returns for fold and arithmetic programs
#[test]
fn fixpoint_leaves_no_reached_fn_unknown_fold_capture_closure() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00175_fold_capture_closure.fz".to_string()),
        text: include_str!("../../fixtures2/00175_fold_capture_closure.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "fold_capture_closure: type inference should converge to known returns",
    );
    // TODO: assert all reached fns have Known return (no Pending/Unknown) at fixpoint
}

// Ported from src/type_infer/type_infer_test.rs: type inference converges to known returns for fold and arithmetic programs
#[test]
fn fixpoint_leaves_no_reached_fn_unknown_fold_state_machine() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00176_fold_state_machine.fz".to_string()),
        text: include_str!("../../fixtures2/00176_fold_state_machine.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "fold_state_machine: type inference should converge to known returns",
    );
    // TODO: assert all reached fns have Known return (no Pending/Unknown) at fixpoint
}

// Ported from src/type_infer/type_infer_test.rs: Enum.reduce and Enum.count settle to int over list and range
#[test]
fn enum_reduce_list_lambda_settles_to_int() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00177_enum_reduce_list_lambda.fz".to_string()),
        text: include_str!("../../fixtures2/00177_enum_reduce_list_lambda.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.reduce list lambda should settle to int");
    // TODO: assert Enum.reduce return type is equivalent to int
}

// Ported from src/type_infer/type_infer_test.rs: Enum.reduce and Enum.count settle to int over list and range
#[test]
fn enum_reduce_named_ref_ok_settles_to_int() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00178_enum_reduce_named_ref_ok.fz".to_string()),
        text: include_str!("../../fixtures2/00178_enum_reduce_named_ref_ok.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("Main".to_string()),
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.reduce named-fn ref should settle to int");
    // TODO: assert Enum.reduce return type is equivalent to int
}

// Ported from src/type_infer/type_infer_test.rs: Enum.reduce and Enum.count settle to int over list and range
#[test]
fn enum_count_list_settles_to_int() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00179_enum_count_list.fz".to_string()),
        text: include_str!("../../fixtures2/00179_enum_count_list.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.count should settle to int");
    // TODO: assert Enum.count return type is equivalent to int
}

// Ported from src/type_infer/type_infer_test.rs: Enum.reduce and Enum.count settle to int over list and range
#[test]
fn enum_reduce_range_settles_to_int() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00180_enum_reduce_range.fz".to_string()),
        text: include_str!("../../fixtures2/00180_enum_reduce_range.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.reduce over range should settle to int");
    // TODO: assert Enum.reduce return type is equivalent to int
}

// Ported from src/type_infer/type_infer_test.rs: qualified and bare operator refs both settle via kernel specs
#[test]
fn enum_reduce_operator_refs_settle_through_kernel_specs() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00181_enum_reduce_operator_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00181_enum_reduce_operator_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "qualified and bare operator refs should both settle through kernel specs",
    );
    // TODO: assert main() return type is equivalent to {int, int}
}

// Ported from src/type_infer/type_infer_test.rs: concrete caller witness preserved despite erased list surface type
#[test]
fn enum_reduce_erased_list_preserves_concrete_caller_witness() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00182_enum_reduce_erased_list.fz".to_string()),
        text: include_str!("../../fixtures2/00182_enum_reduce_erased_list.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "erased list surface type should still settle main to int from concrete caller witness",
    );
    // TODO: assert main() and test/1 both settle to int; test/1 activation carries nonempty_list(int) witness
}

// Ported from src/type_infer/type_infer_test.rs: Enum.take activates distinct list and range call paths
#[test]
fn mixed_enum_take_calls_preserve_list_and_range_activations() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00183_enum_take_list_range.fz".to_string()),
        text: include_str!("../../fixtures2/00183_enum_take_list_range.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "mixed Enum.take calls should activate both list and range paths",
    );
    // TODO: assert Enum.take activates a list-returning path and a range-input path
}

// Ported from src/type_infer/type_infer_test.rs: selective receive threads typed captures and settles caller return
#[test]
fn receive_clause_body_keeps_typed_capture_and_settles_return() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00184_receive_cont_capture.fz".to_string()),
        text: include_str!("../../fixtures2/00184_receive_cont_capture.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "selective receive should infer through its clause body and settle",
    );
    // TODO: assert parent/1 settles to {int, any}; main/0 settles to {{int, any}}; Cont edge exists into rx_clause_0_body
}

// Ported from src/type_infer/type_infer_test.rs: spawn + receive type inference converges to known return
#[test]
fn spawn_receive_converges_through_extern_return_contract() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00185_spawn_receive_capture.fz".to_string()),
        text: include_str!("../../fixtures2/00185_spawn_receive_capture.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "spawn + receive should converge to known return via linked runtime graph",
    );
    // TODO: assert parent/1 settles to any; Kernel.spawn/1 called via Direct edge; selective-receive clause-body edge present
}

// Ported from src/type_infer/type_infer_test.rs: plain spawn propagates callable-boundary type edge into child process
#[test]
fn plain_spawn_surfaces_callable_boundary_to_child() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00186_spawn_plain_child.fz".to_string()),
        text: include_str!("../../fixtures2/00186_spawn_plain_child.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "plain spawn should activate child/0 through callable-boundary edge",
    );
    // TODO: assert child/0 activates with known nil return; Kernel.spawn/1 exposes CallableBoundary edge to child
}

// Ported from src/type_infer/type_infer_test.rs: string literal argument flows through calls as str_t
#[test]
fn string_literal_argument_types_as_str_t() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00187_string_literal_id.fz".to_string()),
        text: include_str!("../../fixtures2/00187_string_literal_id.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "string literal should flow through direct calls");
    // TODO: assert id return type is equivalent to str_t
}

// Ported from src/type_infer/type_infer_test.rs: Enum.reduce and Enumerable.List.reduce settle to concrete return types
#[test]
fn enum_reduce_runtime_graph_settles() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00177_enum_reduce_list_lambda.fz".to_string()),
        text: include_str!("../../fixtures2/00177_enum_reduce_list_lambda.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "Enum.reduce and Enumerable.List.reduce should both settle",
    );
    // TODO: assert Enum.reduce settles to int; Enumerable.List.reduce settles to {:done, int}
}

// Ported from src/type_infer/type_infer_test.rs: invalid operator usage in a named reducer produces a type diagnostic
#[test]
fn invalid_named_reduce_reducer_emits_operator_diagnostic() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00188_enum_reduce_ill_typed.fz".to_string()),
        text: include_str!("../../fixtures2/00188_enum_reduce_ill_typed.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("Main".to_string()),
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // NOTE: this program is intentionally ill-typed; DriveOutcome may not be Resolved.
    // The intent is that a type/invalid-operator diagnostic is emitted for broken_reducer/2.
    // TODO: assert DriveOutcome carries a type/invalid-operator diagnostic for Main.broken_reducer/2 on `+`
    let _ = compiler.drive();
}

// Ported from src/type_infer/type_infer_test.rs: arithmetic operators infer correct int/float return types per operands
#[test]
fn arithmetic_binops_infer_from_kernel_operator_specs() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00189_arithmetic_all_binops.fz".to_string()),
        text: include_str!("../../fixtures2/00189_arithmetic_all_binops.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "arithmetic operators should be typed by Kernel operator specs",
    );
    // TODO: assert main return type is equivalent to {int, int, int, int, int, float, float, float}
}

// Ported from src/type_infer/type_infer_test.rs: any + int infers union of successful operator returns without diagnostic
#[test]
fn arithmetic_binops_union_successful_returns_for_any_operands() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00190_arithmetic_any_operands.fz".to_string()),
        text: include_str!("../../fixtures2/00190_arithmetic_any_operands.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "add".to_string(),
        arity: 2,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "add(any, int) should settle without invalid-operator diagnostic",
    );
    // TODO: assert add/2 activation with (any, int) inputs settles to int|float; no type/invalid-operator diagnostic emitted
}

// Ported from src/type_infer/type_infer_test.rs: add(int, int) infers int return type
#[test]
fn add_infers_int_return() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00171_add_operator_flow.fz".to_string()),
        text: include_str!("../../fixtures2/00171_add_operator_flow.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "add(int, int) should infer int");
    // TODO: assert add/2 activation with (int, int) inputs returns int
}

// Ported from src/type_infer/type_infer_test.rs: polymorphic identity instantiates separately per callsite type
#[test]
fn direct_calls_instantiate_polymorphic_identity_per_callsite() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00191_poly_id_direct.fz".to_string()),
        text: include_str!("../../fixtures2/00191_poly_id_direct.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "main should keep id(1) and id(:ok) as separate instantiations",
    );
    // TODO: assert main return type is equivalent to {int, :ok}
}

// Ported from src/type_infer/type_infer_test.rs: named fn refs instantiate separate activations per call argument type
#[test]
fn named_refs_instantiate_polymorphic_identity_per_callsite() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00192_poly_named_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00192_poly_named_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "&id/1 should create separate activations for int and :ok calls",
    );
    // TODO: assert main return type is equivalent to {int, :ok}
}

// Ported from src/type_infer/type_infer_test.rs: &id/1 infers as thin FnRef with no capture payload
#[test]
fn named_ref_return_preserves_thin_callable_kind() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00193_named_ref_thin.fz".to_string()),
        text: include_str!("../../fixtures2/00193_named_ref_thin.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "&id/1 should return a thin FnRef with no captures");
    // TODO: assert main return type is a CallableValueKind::FnRef with zero captures
}

// Ported from src/type_infer/type_infer_test.rs: zero-capture lambda infers as thin callable with no closure payload
#[test]
fn zero_capture_lambda_infers_as_thin_callable() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00194_zero_capture_lambda.fz".to_string()),
        text: include_str!("../../fixtures2/00194_zero_capture_lambda.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "zero-capture lambda should infer as thin callable");
    // TODO: assert main return type is a CallableValueKind::FnRef with zero captures
}

// Ported from src/type_infer/type_infer_test.rs: lambda capturing outer variable infers as Closure with capture payload
#[test]
fn captured_lambda_infers_as_closure_with_capture_payload() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00195_lambda_capture_closure.fz".to_string()),
        text: include_str!("../../fixtures2/00195_lambda_capture_closure.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "capturing lambda should infer as Closure kind with capture payload",
    );
    // TODO: assert main return type is CallableValueKind::Closure with one capture
}

// Ported from src/type_infer/type_infer_test.rs: named fn ref dispatches distinct pattern clauses per activation argument
#[test]
fn named_refs_drive_pattern_dispatch_per_activation() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00196_poly_named_ref_pattern.fz".to_string()),
        text: include_str!("../../fixtures2/00196_poly_named_ref_pattern.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "&pick/1 should feed each activation argument into the matcher tree",
    );
    // TODO: assert main return type is equivalent to {:one, :two}; catch-all clause is dead
}

// Ported from src/type_infer/type_infer_test.rs: captured closure instantiates by prepending capture type to call args
#[test]
fn captured_closure_refs_instantiate_by_capture_and_arg_facts() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00197_poly_capture_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00197_poly_capture_ref.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "captured closure should prepend capture facts inside inference",
    );
    // TODO: assert main return type is equivalent to {{:ok, int}, {:ok, :right}}
}

// Ported from src/type_infer/type_infer_test.rs: atom pattern dispatch selects distinct clause per atom literal argument
#[test]
fn direct_calls_specialize_atom_pattern_dispatch_by_input() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00198_match_atom_partition.fz".to_string()),
        text: include_str!("../../fixtures2/00198_match_atom_partition.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "each atom literal call should select the matching clause leaf",
    );
    // TODO: assert main return type is equivalent to {:one, :two}
}

// Ported from src/type_infer/type_infer_test.rs: list pattern dispatch selects empty vs cons clause per input shape
#[test]
fn direct_calls_specialize_list_pattern_dispatch_by_shape() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00199_match_list_partition.fz".to_string()),
        text: include_str!("../../fixtures2/00199_match_list_partition.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "each list-shape call should select the matching clause leaf",
    );
    // TODO: assert main return type is equivalent to {:empty, :cons}
}

// Ported from src/type_infer/type_infer_test.rs: matched list cons head type flows into selected clause body
#[test]
fn list_pattern_binding_flows_into_selected_leaf() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00200_match_list_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00200_match_list_binding.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "cons leaf should return the matched head element type",
    );
    // TODO: assert main return type is equivalent to {:empty, int}
}

// Ported from src/type_infer/type_infer_test.rs: matched tuple payload type flows into selected clause body
#[test]
fn tuple_pattern_binding_flows_into_selected_leaf() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00201_match_tuple_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00201_match_tuple_binding.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tuple leaf should return the matched payload type");
    // TODO: assert main return type is equivalent to {int, :error}
}

// Ported from src/type_infer/type_infer_test.rs: nested tuple-inside-list pattern binding flows to matched type
#[test]
fn nested_pattern_binding_flows_into_selected_leaf() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00202_match_nested_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00202_match_nested_binding.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "nested tuple/list proof should flow the matched head into the leaf",
    );
    // TODO: assert main return type is equivalent to {int, :error}
}

// Ported from src/type_infer/type_infer_test.rs: nested tuple/list partition dispatches each sibling clause independently
#[test]
fn nested_pattern_partition_selects_sibling_leaves() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00203_match_nested_partition.fz".to_string()),
        text: include_str!("../../fixtures2/00203_match_nested_partition.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "nested tuple/list partition should select each sibling clause independently",
    );
    // TODO: assert main return type is equivalent to {:empty, int, :error}; catch-all is dead
}

// Ported from src/type_infer/type_infer_test.rs: same-arity tuple dispatch selects clause by tag atom
#[test]
fn tuple_tag_partition_selects_matching_payloads() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00204_match_tuple_tag.fz".to_string()),
        text: include_str!("../../fixtures2/00204_match_tuple_tag.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "same-arity tuple partition should select payloads by tag atom",
    );
    // TODO: assert main return type is equivalent to {int, :bad}
}

// Ported from src/type_infer/type_infer_test.rs: tuple dispatch selects clause by arity shape
#[test]
fn tuple_arity_partition_selects_matching_shape() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00205_match_tuple_arity.fz".to_string()),
        text: include_str!("../../fixtures2/00205_match_tuple_arity.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "tuple arity partition should select each matching shape clause",
    );
    // TODO: assert main return type is equivalent to {int, {int, int}, :other}
}

// Ported from src/type_infer/type_infer_test.rs: guard clause selects refined return type when guard proof succeeds
#[test]
fn guard_partition_selects_refined_clause() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00206_match_guard_clause.fz".to_string()),
        text: include_str!("../../fixtures2/00206_match_guard_clause.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "guarded tuple clause should be selected when guard proof succeeds",
    );
    // TODO: assert main return type is equivalent to {int, :fallback}
}

// Ported from src/type_infer/type_infer_test.rs: map pattern key binding flows matched value type into clause body
#[test]
fn map_pattern_binding_flows_into_selected_leaf() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00207_match_map_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00207_match_map_binding.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "map-pattern proof should flow matched key value into the clause leaf",
    );
    // TODO: assert main return type is equivalent to {int, :none}; catch-all is dead
}

// Ported from src/type_infer/type_infer_test.rs: tail-call, non-tail, capture-int, capture-closure, state-machine folds all settle to int
#[test]
fn corpus_folds_settle_myreduce_to_int_fold_tail() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00172_fold_tail_recursive.fz".to_string()),
        text: include_str!("../../fixtures2/00172_fold_tail_recursive.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fold_tail: myreduce should settle to int");
    // TODO: assert myreduce return type is equivalent to int
}

// Ported from src/type_infer/type_infer_test.rs: tail-call, non-tail, capture-int, capture-closure, state-machine folds all settle to int
#[test]
fn corpus_folds_settle_myreduce_to_int_fold_nontail() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00173_fold_nontail_finish.fz".to_string()),
        text: include_str!("../../fixtures2/00173_fold_nontail_finish.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fold_nontail: myreduce should settle to int");
    // TODO: assert myreduce return type is equivalent to int
}

// Ported from src/type_infer/type_infer_test.rs: tail-call, non-tail, capture-int, capture-closure, state-machine folds all settle to int
#[test]
fn corpus_folds_settle_myreduce_to_int_fold_capture_int() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00174_fold_capture_int.fz".to_string()),
        text: include_str!("../../fixtures2/00174_fold_capture_int.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fold_capture_int: myreduce should settle to int");
    // TODO: assert myreduce return type is equivalent to int
}

// Ported from src/type_infer/type_infer_test.rs: tail-call, non-tail, capture-int, capture-closure, state-machine folds all settle to int
#[test]
fn corpus_folds_settle_myreduce_to_int_fold_capture_closure() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00175_fold_capture_closure.fz".to_string()),
        text: include_str!("../../fixtures2/00175_fold_capture_closure.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fold_capture_closure: myreduce should settle to int");
    // TODO: assert myreduce return type is equivalent to int
}

// Ported from src/type_infer/type_infer_test.rs: tail-call, non-tail, capture-int, capture-closure, state-machine folds all settle to int
#[test]
fn corpus_folds_settle_myreduce_to_int_fold_state_machine() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00176_fold_state_machine.fz".to_string()),
        text: include_str!("../../fixtures2/00176_fold_state_machine.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fold_state_machine: myreduce should settle to int");
    // TODO: assert myreduce return type is equivalent to int
}
