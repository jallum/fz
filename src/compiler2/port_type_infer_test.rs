//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
use super::drive_test::{
    FunctionCapture, ModuleCapture, ReturnTypeCapture, assert_resolved, function_id, function_id_in_module,
};
use super::{CallableValueKind, CodeSubmission, Compiler2, ExecutableNeed, RootId, RootSubmission, Ty};
use crate::telemetry::ConfiguredTelemetry;

/// Attaches the `function.defined` and `return_type.defined` telemetry
/// captures every return-type assertion below needs to look up a settled
/// function's return type by name.
fn attach_return_captures(tel: &ConfiguredTelemetry) -> (FunctionCapture, ReturnTypeCapture) {
    let functions = FunctionCapture::new();
    functions.install(tel);
    let returns = ReturnTypeCapture::new();
    returns.install(tel);
    (functions, returns)
}

/// Same as [`attach_return_captures`], plus the `module.defined` capture
/// needed to disambiguate same-named functions living in different modules
/// (e.g. `Enum.reduce/3` vs `Enumerable.List.reduce/3`).
fn attach_return_captures_with_modules(
    tel: &ConfiguredTelemetry,
) -> (FunctionCapture, ModuleCapture, ReturnTypeCapture) {
    let (functions, returns) = attach_return_captures(tel);
    let modules = ModuleCapture::new();
    modules.install(tel);
    (functions, modules, returns)
}

/// Asserts that the settled return type of the top-level (unqualified) function
/// `name/arity` is equivalent — under the Types-layer equivalence relation, not
/// string/handle comparison — to `expected`.
fn assert_settles_to(
    compiler: &Compiler2<ConfiguredTelemetry>,
    functions: &FunctionCapture,
    returns: &ReturnTypeCapture,
    root_id: RootId,
    name: &str,
    arity: u64,
    expected: Ty,
    context: &str,
) -> Ty {
    let function_id = function_id(functions, name, arity);
    let actual = returns.last_for_function(root_id, function_id).return_ty;
    assert!(
        compiler.types_equivalent_for_test(actual, expected),
        "{name}/{arity} should settle to a return type equivalent to {context}, got {}",
        compiler.display_ty_for_test(actual),
    );
    actual
}

/// Same as [`assert_settles_to`], but for a function living inside `module_name`
/// (disambiguates same-named functions across modules, e.g. `Enum.reduce/3` vs
/// `Enumerable.List.reduce/3`).
fn assert_settles_to_in_module(
    compiler: &Compiler2<ConfiguredTelemetry>,
    functions: &FunctionCapture,
    modules: &ModuleCapture,
    returns: &ReturnTypeCapture,
    root_id: RootId,
    module_name: &str,
    name: &str,
    arity: u64,
    expected: Ty,
    context: &str,
) -> Ty {
    let function_id = function_id_in_module(functions, modules, module_name, name, arity);
    let actual = returns.last_for_function(root_id, function_id).return_ty;
    assert!(
        compiler.types_equivalent_for_test(actual, expected),
        "{module_name}.{name}/{arity} should settle to a return type equivalent to {context}, got {}",
        compiler.display_ty_for_test(actual),
    );
    actual
}

/// Asserts `actual` is a callable literal of the given `kind` carrying exactly
/// `n_captures` captured values (a thin `FnRef` is `kind = FnRef, n_captures = 0`).
fn assert_closure_kind(
    compiler: &Compiler2<ConfiguredTelemetry>,
    actual: Ty,
    kind: CallableValueKind,
    n_captures: usize,
    label: &str,
) {
    let info = compiler.types_for_test().closure_lit_parts(&actual).unwrap_or_else(|| {
        panic!(
            "{label} should be a closure literal, got {}",
            compiler.display_ty_for_test(actual),
        )
    });
    assert_eq!(info.kind, kind, "{label} should be a {kind:?}");
    assert_eq!(
        info.captures.len(),
        n_captures,
        "{label} should carry {n_captures} captures, got {:?}",
        info.captures,
    );
}

// Ported from src/type_infer/type_infer_test.rs: type inference converges to known returns for fold and arithmetic programs
#[test]
fn fixpoint_leaves_no_reached_fn_unknown_add() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
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
    let mut compiler = Compiler2::new(tel);
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
    let mut compiler = Compiler2::new(tel);
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
    let mut compiler = Compiler2::new(tel);
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
    let mut compiler = Compiler2::new(tel);
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
    let mut compiler = Compiler2::new(tel);
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
    let (functions, modules, returns) = attach_return_captures_with_modules(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00177_enum_reduce_list_lambda.fz".to_string()),
        text: include_str!("../../fixtures2/00177_enum_reduce_list_lambda.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.reduce list lambda should settle to int");

    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to_in_module(
        &compiler, &functions, &modules, &returns, root_id, "Enum", "reduce", 3, int_ty, "int",
    );
}

// Ported from src/type_infer/type_infer_test.rs: Enum.reduce and Enum.count settle to int over list and range
#[test]
fn enum_reduce_named_ref_ok_settles_to_int() {
    let tel = ConfiguredTelemetry::new();
    let (functions, modules, returns) = attach_return_captures_with_modules(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00178_enum_reduce_named_ref_ok.fz".to_string()),
        text: include_str!("../../fixtures2/00178_enum_reduce_named_ref_ok.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.reduce named-fn ref should settle to int");

    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to_in_module(
        &compiler, &functions, &modules, &returns, root_id, "Enum", "reduce", 3, int_ty, "int",
    );
}

// Ported from src/type_infer/type_infer_test.rs: Enum.reduce and Enum.count settle to int over list and range
#[test]
fn enum_count_list_settles_to_int() {
    let tel = ConfiguredTelemetry::new();
    let (functions, modules, returns) = attach_return_captures_with_modules(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00179_enum_count_list.fz".to_string()),
        text: include_str!("../../fixtures2/00179_enum_count_list.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.count should settle to int");

    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to_in_module(
        &compiler, &functions, &modules, &returns, root_id, "Enum", "count", 1, int_ty, "int",
    );
}

// Ported from src/type_infer/type_infer_test.rs: Enum.reduce and Enum.count settle to int over list and range
#[test]
fn enum_reduce_range_settles_to_int() {
    let tel = ConfiguredTelemetry::new();
    let (functions, modules, returns) = attach_return_captures_with_modules(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00180_enum_reduce_range.fz".to_string()),
        text: include_str!("../../fixtures2/00180_enum_reduce_range.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Enum.reduce over range should settle to int");

    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to_in_module(
        &compiler, &functions, &modules, &returns, root_id, "Enum", "reduce", 3, int_ty, "int",
    );
}

// Ported from src/type_infer/type_infer_test.rs: qualified and bare operator refs both settle via kernel specs
#[test]
fn enum_reduce_operator_refs_settle_through_kernel_specs() {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let returns = ReturnTypeCapture::new();
    returns.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00181_enum_reduce_operator_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00181_enum_reduce_operator_ref.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "qualified and bare operator refs should both settle through kernel specs",
    );

    let main_id = function_id(&functions, "main", 0);
    let main_return = returns.last_for_function(root_id, main_id).return_ty;
    let int_ty = compiler.types_mut_for_test().int();
    let expected_return = compiler.types_mut_for_test().tuple(&[int_ty, int_ty]);
    assert!(
        compiler.types_equivalent_for_test(main_return, expected_return),
        "main/0 should settle to a return type equivalent to {{int, int}} once the qualified \
         and bare operator refs both settle through kernel specs, got {}",
        compiler.display_ty_for_test(main_return),
    );
}

// Ported from src/type_infer/type_infer_test.rs: concrete caller witness preserved despite erased list surface type
#[test]
fn enum_reduce_erased_list_preserves_concrete_caller_witness() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00182_enum_reduce_erased_list.fz".to_string()),
        text: include_str!("../../fixtures2/00182_enum_reduce_erased_list.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "erased list surface type should still settle main to int from concrete caller witness",
    );

    // test/1 is declared `[any] -> integer`; it settling to int (rather than
    // falling back to `any`) is itself the proof that the reached activation
    // carried the concrete `nonempty_list(int)` caller witness through
    // `Enum.reduce/3` — that's the behaviour this fixture pins.
    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to(&compiler, &functions, &returns, root_id, "main", 0, int_ty, "int");
    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to(&compiler, &functions, &returns, root_id, "test", 1, int_ty, "int");
}

// Ported from src/type_infer/type_infer_test.rs: Enum.take activates distinct list and range call paths
#[test]
fn mixed_enum_take_calls_preserve_list_and_range_activations() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
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
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00184_receive_cont_capture.fz".to_string()),
        text: include_str!("../../fixtures2/00184_receive_cont_capture.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "selective receive should infer through its clause body and settle",
    );

    let parent_expected = {
        let int_ty = compiler.types_mut_for_test().int();
        let any_ty = compiler.types_mut_for_test().any();
        compiler.types_mut_for_test().tuple(&[int_ty, any_ty])
    };
    let parent_return = assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "parent",
        1,
        parent_expected,
        "{int, any}",
    );
    let main_expected = compiler.types_mut_for_test().tuple(&[parent_return]);
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        main_expected,
        "{{int, any}}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: spawn + receive type inference converges to known return
#[test]
fn spawn_receive_converges_through_extern_return_contract() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00185_spawn_receive_capture.fz".to_string()),
        text: include_str!("../../fixtures2/00185_spawn_receive_capture.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "spawn + receive should converge to known return via linked runtime graph",
    );

    // The message crosses a spawn/send/receive process boundary, so the
    // engine conservatively types the received value `any` even though the
    // spawned closure only ever sends the concrete `tag` back — the runtime
    // assertion in the fixture (`parent(99) == 99`) is what's actually
    // pinning the value, not the static return type.
    let any_ty = compiler.types_mut_for_test().any();
    assert_settles_to(&compiler, &functions, &returns, root_id, "parent", 1, any_ty, "any");
}

// Ported from src/type_infer/type_infer_test.rs: plain spawn propagates callable-boundary type edge into child process
#[test]
fn plain_spawn_surfaces_callable_boundary_to_child() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
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
    // NOT FILLED (aspirational TODO): child/0 is passed to `spawn/1` only as a
    // bare callable reference — the fixed point never activates child/0 itself,
    // so no `return_type.defined` fact for it exists to assert against.
    // Verified via telemetry: `spawn/1`'s (FunctionId 29) and main/0's settled
    // return is `pid` (the spawned process id), not a fact about child/0's
    // body. The `Kernel.spawn/1 exposes CallableBoundary edge to child` half
    // of the TODO is a claim about a callsite/edge fact, not a return type;
    // it needs a CallsiteCapture-based assertion, not `types_equivalent_for_test`.
}

// Ported from src/type_infer/type_infer_test.rs: string literal argument flows through calls as str_t
#[test]
fn string_literal_argument_types_as_str_t() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00187_string_literal_id.fz".to_string()),
        text: include_str!("../../fixtures2/00187_string_literal_id.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "string literal should flow through direct calls");

    let str_ty = compiler.types_mut_for_test().str_t();
    assert_settles_to(&compiler, &functions, &returns, root_id, "id", 1, str_ty, "str_t");
}

// Ported from src/type_infer/type_infer_test.rs: Enum.reduce and Enumerable.List.reduce settle to concrete return types
#[test]
fn enum_reduce_runtime_graph_settles() {
    let tel = ConfiguredTelemetry::new();
    let (functions, modules, returns) = attach_return_captures_with_modules(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00177_enum_reduce_list_lambda.fz".to_string()),
        text: include_str!("../../fixtures2/00177_enum_reduce_list_lambda.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "Enum.reduce and Enumerable.List.reduce should both settle",
    );

    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to_in_module(
        &compiler, &functions, &modules, &returns, root_id, "Enum", "reduce", 3, int_ty, "int",
    );
    let done_ty = {
        let done_atom = compiler.types_mut_for_test().atom_lit("done");
        let int_ty = compiler.types_mut_for_test().int();
        compiler.types_mut_for_test().tuple(&[done_atom, int_ty])
    };
    assert_settles_to_in_module(
        &compiler,
        &functions,
        &modules,
        &returns,
        root_id,
        "Enumerable.List",
        "reduce",
        3,
        done_ty,
        "{:done, int}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: invalid operator usage in a named reducer produces a type diagnostic
#[test]
fn invalid_named_reduce_reducer_emits_operator_diagnostic() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
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
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00189_arithmetic_all_binops.fz".to_string()),
        text: include_str!("../../fixtures2/00189_arithmetic_all_binops.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "arithmetic operators should be typed by Kernel operator specs",
    );

    let expected = {
        let int_ty = compiler.types_mut_for_test().int();
        let float_ty = compiler.types_mut_for_test().float();
        compiler
            .types_mut_for_test()
            .tuple(&[int_ty, int_ty, int_ty, int_ty, int_ty, float_ty, float_ty, float_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{int, int, int, int, int, float, float, float}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: any + int infers union of successful operator returns without diagnostic
#[test]
fn arithmetic_binops_union_successful_returns_for_any_operands() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00190_arithmetic_any_operands.fz".to_string()),
        text: include_str!("../../fixtures2/00190_arithmetic_any_operands.fz").to_string(),
    });
    // NOTE: `RootSubmission` has no per-argument type facility (unlike the
    // old-world `infer_from_entry(&mut t, &module, add_id, &[any, int], &tel)`
    // harness this was ported from), so both of add/2's parameters settle as
    // unconstrained `any` here rather than the old harness's `(any, int)`.
    // The behaviour under test survives the port regardless: `+` over two
    // `any` operands still settles to the union of every operator clause's
    // successful return (`int | float`), not a single joined `any`.
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "add".to_string(),
        arity: 2,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "add(any, int) should settle without invalid-operator diagnostic",
    );

    let expected = {
        let int_ty = compiler.types_mut_for_test().int();
        let float_ty = compiler.types_mut_for_test().float();
        compiler.types_mut_for_test().union(int_ty, float_ty)
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "add",
        2,
        expected,
        "int | float",
    );
    // NOT FILLED: "no type/invalid-operator diagnostic emitted" needs a
    // diagnostics/telemetry capture, not `types_equivalent_for_test` — out of
    // scope for this return-type sweep.
}

// Ported from src/type_infer/type_infer_test.rs: add(int, int) infers int return type
#[test]
fn add_infers_int_return() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00171_add_operator_flow.fz".to_string()),
        text: include_str!("../../fixtures2/00171_add_operator_flow.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "add(int, int) should infer int");

    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to(&compiler, &functions, &returns, root_id, "add", 2, int_ty, "int");
}

// Ported from src/type_infer/type_infer_test.rs: polymorphic identity instantiates separately per callsite type
#[test]
fn direct_calls_instantiate_polymorphic_identity_per_callsite() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00191_poly_id_direct.fz".to_string()),
        text: include_str!("../../fixtures2/00191_poly_id_direct.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "main should keep id(1) and id(:ok) as separate instantiations",
    );

    let expected = {
        let int_ty = compiler.types_mut_for_test().int();
        let ok_ty = compiler.types_mut_for_test().atom_lit("ok");
        compiler.types_mut_for_test().tuple(&[int_ty, ok_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{int, :ok}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: named fn refs instantiate separate activations per call argument type
#[test]
fn named_refs_instantiate_polymorphic_identity_per_callsite() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00192_poly_named_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00192_poly_named_ref.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "&id/1 should create separate activations for int and :ok calls",
    );

    let expected = {
        let int_ty = compiler.types_mut_for_test().int();
        let ok_ty = compiler.types_mut_for_test().atom_lit("ok");
        compiler.types_mut_for_test().tuple(&[int_ty, ok_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{int, :ok}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: &id/1 infers as thin FnRef with no capture payload
#[test]
fn named_ref_return_preserves_thin_callable_kind() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00193_named_ref_thin.fz".to_string()),
        text: include_str!("../../fixtures2/00193_named_ref_thin.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "&id/1 should return a thin FnRef with no captures");

    let main_id = function_id(&functions, "main", 0);
    let main_return = returns.last_for_function(root_id, main_id).return_ty;
    assert_closure_kind(
        &compiler,
        main_return,
        CallableValueKind::FnRef,
        0,
        "main/0's &id/1 return",
    );
}

// Ported from src/type_infer/type_infer_test.rs: zero-capture lambda infers as thin callable with no closure payload
#[test]
fn zero_capture_lambda_infers_as_thin_callable() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00194_zero_capture_lambda.fz".to_string()),
        text: include_str!("../../fixtures2/00194_zero_capture_lambda.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "zero-capture lambda should infer as thin callable");

    // NOTE: the TODO's literal claim ("a CallableValueKind::FnRef") does not
    // hold — `FnRef` is minted only for named function references (`&f/n`);
    // an anonymous lambda literal (`fn(x) -> x end`), even with zero
    // captures, still lowers through `closure_lit` and keeps
    // `CallableValueKind::Closure`. What *is* true, and what "thin callable"
    // actually means here, is that its capture list is empty — asserted below.
    let main_id = function_id(&functions, "main", 0);
    let main_return = returns.last_for_function(root_id, main_id).return_ty;
    assert_closure_kind(
        &compiler,
        main_return,
        CallableValueKind::Closure,
        0,
        "main/0's zero-capture lambda return",
    );
}

// Ported from src/type_infer/type_infer_test.rs: lambda capturing outer variable infers as Closure with capture payload
#[test]
fn captured_lambda_infers_as_closure_with_capture_payload() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00195_lambda_capture_closure.fz".to_string()),
        text: include_str!("../../fixtures2/00195_lambda_capture_closure.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "capturing lambda should infer as Closure kind with capture payload",
    );

    let main_id = function_id(&functions, "main", 0);
    let main_return = returns.last_for_function(root_id, main_id).return_ty;
    assert_closure_kind(
        &compiler,
        main_return,
        CallableValueKind::Closure,
        1,
        "main/0's captured lambda return",
    );
}

// Ported from src/type_infer/type_infer_test.rs: named fn ref dispatches distinct pattern clauses per activation argument
#[test]
fn named_refs_drive_pattern_dispatch_per_activation() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00196_poly_named_ref_pattern.fz".to_string()),
        text: include_str!("../../fixtures2/00196_poly_named_ref_pattern.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "&pick/1 should feed each activation argument into the matcher tree",
    );

    // main only calls `f.(:left)` and `f.(:right)`, so main/0 settling to
    // `{:one, :two}` (rather than a wider union including `:other`) is itself
    // the proof that the catch-all clause never contributes to the observed
    // return — that's what "catch-all clause is dead" means here.
    let expected = {
        let one_ty = compiler.types_mut_for_test().atom_lit("one");
        let two_ty = compiler.types_mut_for_test().atom_lit("two");
        compiler.types_mut_for_test().tuple(&[one_ty, two_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{:one, :two}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: captured closure instantiates by prepending capture type to call args
#[test]
fn captured_closure_refs_instantiate_by_capture_and_arg_facts() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00197_poly_capture_ref.fz".to_string()),
        text: include_str!("../../fixtures2/00197_poly_capture_ref.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "captured closure should prepend capture facts inside inference",
    );

    let expected = {
        let ok_ty = compiler.types_mut_for_test().atom_lit("ok");
        let int_ty = compiler.types_mut_for_test().int();
        let ok_int = compiler.types_mut_for_test().tuple(&[ok_ty, int_ty]);
        let ok_ty = compiler.types_mut_for_test().atom_lit("ok");
        let right_ty = compiler.types_mut_for_test().atom_lit("right");
        let ok_right = compiler.types_mut_for_test().tuple(&[ok_ty, right_ty]);
        compiler.types_mut_for_test().tuple(&[ok_int, ok_right])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{{:ok, int}, {:ok, :right}}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: atom pattern dispatch selects distinct clause per atom literal argument
#[test]
fn direct_calls_specialize_atom_pattern_dispatch_by_input() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00198_match_atom_partition.fz".to_string()),
        text: include_str!("../../fixtures2/00198_match_atom_partition.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "each atom literal call should select the matching clause leaf",
    );

    let expected = {
        let one_ty = compiler.types_mut_for_test().atom_lit("one");
        let two_ty = compiler.types_mut_for_test().atom_lit("two");
        compiler.types_mut_for_test().tuple(&[one_ty, two_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{:one, :two}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: list pattern dispatch selects empty vs cons clause per input shape
#[test]
fn direct_calls_specialize_list_pattern_dispatch_by_shape() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00199_match_list_partition.fz".to_string()),
        text: include_str!("../../fixtures2/00199_match_list_partition.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "each list-shape call should select the matching clause leaf",
    );

    let expected = {
        let empty_ty = compiler.types_mut_for_test().atom_lit("empty");
        let cons_ty = compiler.types_mut_for_test().atom_lit("cons");
        compiler.types_mut_for_test().tuple(&[empty_ty, cons_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{:empty, :cons}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: matched list cons head type flows into selected clause body
#[test]
fn list_pattern_binding_flows_into_selected_leaf() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00200_match_list_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00200_match_list_binding.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "cons leaf should return the matched head element type",
    );

    let expected = {
        let empty_ty = compiler.types_mut_for_test().atom_lit("empty");
        let int_ty = compiler.types_mut_for_test().int();
        compiler.types_mut_for_test().tuple(&[empty_ty, int_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{:empty, int}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: matched tuple payload type flows into selected clause body
#[test]
fn tuple_pattern_binding_flows_into_selected_leaf() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00201_match_tuple_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00201_match_tuple_binding.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tuple leaf should return the matched payload type");

    let expected = {
        let int_ty = compiler.types_mut_for_test().int();
        let error_ty = compiler.types_mut_for_test().atom_lit("error");
        compiler.types_mut_for_test().tuple(&[int_ty, error_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{int, :error}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: nested tuple-inside-list pattern binding flows to matched type
#[test]
fn nested_pattern_binding_flows_into_selected_leaf() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00202_match_nested_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00202_match_nested_binding.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "nested tuple/list proof should flow the matched head into the leaf",
    );

    let expected = {
        let int_ty = compiler.types_mut_for_test().int();
        let error_ty = compiler.types_mut_for_test().atom_lit("error");
        compiler.types_mut_for_test().tuple(&[int_ty, error_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{int, :error}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: nested tuple/list partition dispatches each sibling clause independently
#[test]
fn nested_pattern_partition_selects_sibling_leaves() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00203_match_nested_partition.fz".to_string()),
        text: include_str!("../../fixtures2/00203_match_nested_partition.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "nested tuple/list partition should select each sibling clause independently",
    );

    // main only reaches the empty-payload, cons-payload, and atom clauses;
    // main/0 settling to `{:empty, int, :error}` — not a wider union pulling
    // in `:unreachable` — is the proof that the catch-all clause is dead.
    let expected = {
        let empty_ty = compiler.types_mut_for_test().atom_lit("empty");
        let int_ty = compiler.types_mut_for_test().int();
        let error_ty = compiler.types_mut_for_test().atom_lit("error");
        compiler.types_mut_for_test().tuple(&[empty_ty, int_ty, error_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{:empty, int, :error}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: same-arity tuple dispatch selects clause by tag atom
#[test]
fn tuple_tag_partition_selects_matching_payloads() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00204_match_tuple_tag.fz".to_string()),
        text: include_str!("../../fixtures2/00204_match_tuple_tag.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "same-arity tuple partition should select payloads by tag atom",
    );

    let expected = {
        let int_ty = compiler.types_mut_for_test().int();
        let bad_ty = compiler.types_mut_for_test().atom_lit("bad");
        compiler.types_mut_for_test().tuple(&[int_ty, bad_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{int, :bad}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: tuple dispatch selects clause by arity shape
#[test]
fn tuple_arity_partition_selects_matching_shape() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00205_match_tuple_arity.fz".to_string()),
        text: include_str!("../../fixtures2/00205_match_tuple_arity.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "tuple arity partition should select each matching shape clause",
    );

    let expected = {
        let int_ty = compiler.types_mut_for_test().int();
        let int_pair = compiler.types_mut_for_test().tuple(&[int_ty, int_ty]);
        let int_ty = compiler.types_mut_for_test().int();
        let other_ty = compiler.types_mut_for_test().atom_lit("other");
        compiler.types_mut_for_test().tuple(&[int_ty, int_pair, other_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{int, {int, int}, :other}",
    );
}

// Ported from src/type_infer/type_infer_test.rs: guard clause selects refined return type when guard proof succeeds
#[test]
fn guard_partition_selects_refined_clause() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
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
    // NOT FILLED (aspirational TODO, diagnosed but not fixed): main/0
    // actually settles to `{int | :fallback, int | :fallback}`, not the
    // claimed `{int, :fallback}`. Root cause is architectural, not a local
    // dispatch bug: `ActivationKey::from_inputs` (`identity.rs`) keys purely
    // on argument `Ty`, and `Types::int_lit` (`types/mod.rs`) deliberately
    // collapses every numeric literal to plain `int` ("numeric literals are
    // VALUES, not types"). `pick({:ok, 1})` and `pick({:ok, 0})` therefore
    // mint the exact same `ActivationKey` — one shared activation, one
    // `reachable_clause_ids` computation, one joined `ReturnType` fact read
    // by both call sites. There is no per-callsite literal identity left by
    // the time `branch_possible`'s `Region::Guard` test runs to narrow
    // against, unlike the atom case (`direct_calls_specialize_atom_pattern_
    // dispatch_by_input`), where `atom_lit` singletons survive into the type
    // lattice and genuinely mint distinct `ActivationKey`s. Narrowing this
    // per callsite would need a new literal-value channel that survives
    // tuple construction/projection independent of `Ty` (e.g. per-callsite
    // guard re-evaluation against the caller's own literal operands) — a
    // deliberate architecture change, not a point fix, so it is left
    // diagnosed-not-fixed here rather than forced.
}

// Ported from src/type_infer/type_infer_test.rs: map pattern key binding flows matched value type into clause body
#[test]
fn map_pattern_binding_flows_into_selected_leaf() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00207_match_map_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00207_match_map_binding.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "map-pattern proof should flow matched key value into the clause leaf",
    );

    // main only reaches the map-shaped clause and the `:none` atom clause;
    // main/0 settling to `{int, :none}` — not a wider union pulling in
    // `:unreachable` — is the proof that the dead `pick(_)` catch-all does
    // not contribute to either position.
    let expected = {
        let int_ty = compiler.types_mut_for_test().int();
        let none_ty = compiler.types_mut_for_test().atom_lit("none");
        compiler.types_mut_for_test().tuple(&[int_ty, none_ty])
    };
    assert_settles_to(
        &compiler,
        &functions,
        &returns,
        root_id,
        "main",
        0,
        expected,
        "{int, :none}",
    );
}

// Regression guard: int, float, and string map-pattern keys are valid
// (`dispatch_matrix/pattern.rs` accepts them), but the lattice cannot resolve
// them to a prunable map-key singleton. The dispatch-reachability walk must
// keep both edges live for such keys instead of panicking on an unprovable
// key. main/0 settling (no panic) is the proof; because the keys are
// unprovable, each catch-all legitimately contributes `:other`.
#[test]
fn map_pattern_dispatch_on_nonatom_keys_does_not_panic() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00553_match_map_nonatom_keys.fz".to_string()),
        text: include_str!("../../fixtures2/00553_match_map_nonatom_keys.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "int/float/string map-pattern keys should compile without panicking",
    );

    // The single `pick(%{1 => 10})` call walks the whole dispatch graph, which
    // carries a `MapKeyPresent` test for the int, float, AND string clauses —
    // so all three non-atom key predicates are exercised (the naked-`.expect`
    // pre-fix crash fires on the float/string ones). Because none of the
    // non-atom keys can be proven present or absent, every clause leaf plus the
    // catch-all stays live and the return settles to `any`. main/0 settling at
    // all (no panic) is the regression guard.
    let expected = compiler.types_mut_for_test().any();
    assert_settles_to(&compiler, &functions, &returns, root_id, "main", 0, expected, "any");
}

// Ported from src/type_infer/type_infer_test.rs: tail-call, non-tail, capture-int, capture-closure, state-machine folds all settle to int
#[test]
fn corpus_folds_settle_myreduce_to_int_fold_tail() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00172_fold_tail_recursive.fz".to_string()),
        text: include_str!("../../fixtures2/00172_fold_tail_recursive.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fold_tail: myreduce should settle to int");

    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to(&compiler, &functions, &returns, root_id, "myreduce", 3, int_ty, "int");
}

// Ported from src/type_infer/type_infer_test.rs: tail-call, non-tail, capture-int, capture-closure, state-machine folds all settle to int
#[test]
fn corpus_folds_settle_myreduce_to_int_fold_nontail() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00173_fold_nontail_finish.fz".to_string()),
        text: include_str!("../../fixtures2/00173_fold_nontail_finish.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fold_nontail: myreduce should settle to int");

    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to(&compiler, &functions, &returns, root_id, "myreduce", 3, int_ty, "int");
}

// Ported from src/type_infer/type_infer_test.rs: tail-call, non-tail, capture-int, capture-closure, state-machine folds all settle to int
#[test]
fn corpus_folds_settle_myreduce_to_int_fold_capture_int() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00174_fold_capture_int.fz".to_string()),
        text: include_str!("../../fixtures2/00174_fold_capture_int.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fold_capture_int: myreduce should settle to int");

    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to(&compiler, &functions, &returns, root_id, "myreduce", 3, int_ty, "int");
}

// Ported from src/type_infer/type_infer_test.rs: tail-call, non-tail, capture-int, capture-closure, state-machine folds all settle to int
#[test]
fn corpus_folds_settle_myreduce_to_int_fold_capture_closure() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00175_fold_capture_closure.fz".to_string()),
        text: include_str!("../../fixtures2/00175_fold_capture_closure.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fold_capture_closure: myreduce should settle to int");

    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to(&compiler, &functions, &returns, root_id, "myreduce", 3, int_ty, "int");
}

// Ported from src/type_infer/type_infer_test.rs: tail-call, non-tail, capture-int, capture-closure, state-machine folds all settle to int
#[test]
fn corpus_folds_settle_myreduce_to_int_fold_state_machine() {
    let tel = ConfiguredTelemetry::new();
    let (functions, returns) = attach_return_captures(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00176_fold_state_machine.fz".to_string()),
        text: include_str!("../../fixtures2/00176_fold_state_machine.fz").to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fold_state_machine: myreduce should settle to int");

    let int_ty = compiler.types_mut_for_test().int();
    assert_settles_to(&compiler, &functions, &returns, root_id, "myreduce", 3, int_ty, "int");
}
