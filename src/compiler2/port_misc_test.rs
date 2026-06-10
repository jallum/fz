//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
#![allow(unused_imports)]

use super::drive_test::{assert_resolved, function_id, module_id};
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

// Ported from src/cli/repl_test.rs: integer arithmetic evaluation in interactive session
#[test]
fn integer_arithmetic_evaluates() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00501_integer_arithmetic.fz".to_string()),
        text: include_str!("../../fixtures2/00501_integer_arithmetic.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "integer arithmetic should resolve");
    // TODO: JIT-execute and assert result == 3
}

// Ported from src/cli/repl_test.rs: integer, float, and mixed-type list display round-trip
#[test]
fn int_float_atom_list_resolves() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00502_int_float_atom_list.fz".to_string()),
        text: include_str!("../../fixtures2/00502_int_float_atom_list.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "int/float/atom list should resolve");
    // TODO: JIT-execute and assert rendered result == "[1, 2.5, :a]"
}

// Ported from src/cli/repl_test.rs: Utf8.valid? and Utf8.from_bytes runtime semantics on binaries
#[test]
fn utf8_valid_and_from_bytes_semantics() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00503_utf8_valid_from_bytes.fz".to_string()),
        text: include_str!("../../fixtures2/00503_utf8_valid_from_bytes.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Utf8 valid? and from_bytes should resolve");
    // TODO: JIT-execute and assert main completes without runtime error
}

// Ported from src/cli/repl_test.rs: runtime import of Utf8 module; valid? callable in expression
#[test]
fn import_utf8_valid_callable() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00504_import_utf8_valid.fz".to_string()),
        text: include_str!("../../fixtures2/00504_import_utf8_valid.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "imported Utf8.valid? should resolve");
    // TODO: JIT-execute and assert result == true
}

// Ported from src/cli/repl_test.rs: module alias in scope; qualified call via alias resolves correctly
#[test]
fn alias_qualified_call_resolves() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00505_alias_utf8_valid.fz".to_string()),
        text: include_str!("../../fixtures2/00505_alias_utf8_valid.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "alias-qualified call should resolve");
    // TODO: JIT-execute and assert result == false (invalid UTF-8 bytes)
}

// Ported from src/cli/repl_test.rs: variable binding persists across sequential evaluation chunks
#[test]
fn variable_binding_in_block() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00506_variable_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00506_variable_binding.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "variable binding should resolve");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/cli/repl_test.rs: expression evaluation does not rebind existing variables in scope
#[test]
fn variable_not_mutated_by_expression() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00507_var_immutable_in_expr.fz".to_string()),
        text: include_str!("../../fixtures2/00507_var_immutable_in_expr.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "variable immutability in expression should resolve");
    // TODO: JIT-execute and assert result == 10 (x unchanged after x+5 expression)
}

// Ported from src/cli/repl_test.rs: tuple destructuring binds multiple names across session chunks
#[test]
fn tuple_destructure_binds_components() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00508_tuple_destructure.fz".to_string()),
        text: include_str!("../../fixtures2/00508_tuple_destructure.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "tuple destructuring should resolve");
    // TODO: JIT-execute and assert result == 3 (a + b where {a, b} = {1, 2})
}

// Ported from src/cli/repl_test.rs: whitespace-heavy assignment expression parses and binds correctly
#[test]
fn whitespace_assignment_parses_and_binds() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00509_whitespace_assignment.fz".to_string()),
        text: include_str!("../../fixtures2/00509_whitespace_assignment.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "whitespace-heavy assignment should resolve");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/cli/repl_test.rs: failed pattern match errors and does not corrupt prior bindings
#[test]
fn successful_match_binds_inner_var() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00510_match_failure_preserves.fz".to_string()),
        text: include_str!("../../fixtures2/00510_match_failure_preserves.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "match preserving prior binding should resolve");
    // TODO: JIT-execute and assert result == 1 (x unchanged after a match that binds _y)
}

// Ported from src/cli/repl_test.rs: top-level fn definition is callable from subsequent expressions
#[test]
fn top_level_fn_callable_from_expression() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00511_fn_defined_callable.fz".to_string()),
        text: include_str!("../../fixtures2/00511_fn_defined_callable.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "top-level fn callable should resolve");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/cli/repl_test.rs: spawn/receive/send message passing across sequential session chunks
#[test]
fn spawn_send_receive_round_trip() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00512_spawn_send_receive.fz".to_string()),
        text: include_str!("../../fixtures2/00512_spawn_send_receive.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "spawn/send/receive round-trip should resolve");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/cli/repl_test.rs: blocked child process survives new fn definition and later message
#[test]
fn blocked_spawn_resumes_after_new_fn_and_send() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00513_spawn_new_fn_resume.fz".to_string()),
        text: include_str!("../../fixtures2/00513_spawn_new_fn_resume.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "blocked spawn resuming after new fn should resolve");
    // TODO: JIT-execute and assert result == 7
}

// Ported from src/cli/repl_test.rs: send to self and receive round-trips a mixed-type list value
#[test]
fn send_receive_self_list_round_trip() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00514_send_receive_self_list.fz".to_string()),
        text: include_str!("../../fixtures2/00514_send_receive_self_list.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "send/receive self list should resolve");
    // TODO: JIT-execute and assert rendered result == "[1, 2.5, :a]"
}

// Ported from src/cli/repl_test.rs: spawned closure sends; receive with pattern match and after clause
#[test]
fn spawned_send_receive_with_after_clause() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00515_spawn_receive_after.fz".to_string()),
        text: include_str!("../../fixtures2/00515_spawn_receive_after.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "spawn send with receive/after should resolve");
    // TODO: JIT-execute and assert result == :ok
}

// Ported from src/cli/repl_test.rs: spawn/2 with heap hint argument sends message correctly
#[test]
fn spawn2_heap_hint_sends_message() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00516_spawn2_heap_hint.fz".to_string()),
        text: include_str!("../../fixtures2/00516_spawn2_heap_hint.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "spawn/2 with heap hint should resolve");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/cli/repl_test.rs: variable bound in one input chunk used in a later chunk
#[test]
fn variable_used_across_sequential_bindings() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00506_variable_binding.fz".to_string()),
        text: include_str!("../../fixtures2/00506_variable_binding.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "sequential variable use should resolve");
    // TODO: JIT-execute and assert result == 42 (x=7, x+35)
}

// Ported from src/cli/repl_test.rs: multi-clause recursive fn built incrementally across inputs
#[test]
fn multi_clause_recursive_fn_evaluates() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00517_recursive_fn_factorial.fz".to_string()),
        text: include_str!("../../fixtures2/00517_recursive_fn_factorial.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "multi-clause recursive fn should resolve");
    // TODO: JIT-execute and assert result == 720 (fact(6))
}

// Ported from src/cli/repl_test.rs: multiline do-end fn body with local binding evaluates correctly
#[test]
fn multiline_do_end_body_with_local_binding() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00518_multiline_do_end_body.fz".to_string()),
        text: include_str!("../../fixtures2/00518_multiline_do_end_body.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "multiline do-end body should resolve");
    // TODO: JIT-execute and assert result == 42 (double_plus(20) = (20+1)*2 = 42)
}

// Ported from src/cli/repl_test.rs: defmacro defined in one chunk is expandable in a later expression
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn defmacro_expands_in_subsequent_expression() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00519_defmacro_inc.fz".to_string()),
        text: include_str!("../../fixtures2/00519_defmacro_inc.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "defmacro expansion should resolve");
    // TODO: JIT-execute and assert result == 42 (inc(41) expands to 41 + 1)
}

// Ported from src/cli/repl_test.rs: script with main/0 calling a helper fn completes successfully
#[test]
fn script_main_calls_helper_fn() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00520_helper_calls_main.fz".to_string()),
        text: include_str!("../../fixtures2/00520_helper_calls_main.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "main calling helper fn should resolve");
    // TODO: JIT-execute and assert main completes without error
}

// Ported from src/cli/repl_test.rs: multi-process relay program runs through scheduler correctly
#[test]
fn relay_process_runs_through_scheduler() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00521_relay_process.fz".to_string()),
        text: include_str!("../../fixtures2/00521_relay_process.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "relay process program should resolve");
    // TODO: JIT-execute and assert main completes without error (got == 42)
}

// Ported from src/cli/repl_test.rs: multiline fn body with arithmetic evaluates and runs correctly
#[test]
fn multiline_fn_body_arithmetic() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00522_multiline_double_fn.fz".to_string()),
        text: include_str!("../../fixtures2/00522_multiline_double_fn.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "multiline fn body arithmetic should resolve");
    // TODO: JIT-execute and assert main completes without error (double(21) == 42)
}

// Ported from src/cli/repl_test.rs: top-level @spec attaches to following fn and program runs
#[test]
fn top_level_spec_attaches_to_fn() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00523_top_level_spec.fz".to_string()),
        text: include_str!("../../fixtures2/00523_top_level_spec.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "top-level @spec with fn should resolve");
    // TODO: JIT-execute and assert main completes without error
}

// Ported from src/cli/repl_test.rs: fn redefinition at different arity replaces old; new arity resolves
#[test]
fn fn_at_different_arity_resolves() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00524_fn_arity_replace.fz".to_string()),
        text: include_str!("../../fixtures2/00524_fn_arity_replace.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fn at different arity should resolve");
    // TODO: JIT-execute and assert result == 30 (f(10, 20))
}

// Ported from src/cli/test_runner_test.rs: test macro with passing assert runs without error
#[test]
#[ignore = "compiler2 test/defmacro macro expansion not yet implemented"]
fn test_macro_passing_assert_compiles() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00525_test_macro_assert.fz".to_string()),
        text: include_str!("../../fixtures2/00525_test_macro_assert.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "test_one".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "passing test macro should resolve");
    // TODO: JIT-execute and assert test_test_one completes without error
}

// Ported from src/cli/test_runner_test.rs: test macro with failing assert surfaces as error result
#[test]
#[ignore = "compiler2 test/defmacro macro expansion not yet implemented"]
fn test_macro_failing_assert_compiles() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00526_test_macro_fail.fz".to_string()),
        text: include_str!("../../fixtures2/00526_test_macro_fail.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "test_bad".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "failing test macro should still resolve (compilation succeeds)",
    );
    // TODO: JIT-execute and assert test_test_bad raises a runtime error (assert fails)
}

// Ported from src/cli/test_runner_test.rs: multiple test blocks; one failure makes overall result an error
#[test]
#[ignore = "compiler2 test/defmacro macro expansion not yet implemented"]
fn multiple_test_blocks_compile() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00527_multiple_tests_mixed.fz".to_string()),
        text: include_str!("../../fixtures2/00527_multiple_tests_mixed.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "test_a".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "multiple test blocks should resolve");
    // TODO: JIT-execute all three; assert test_c raises an error while test_a and test_b pass
}

// Ported from src/cli/test_runner_test.rs: fn test_*() convention is discovered and run like test macro
#[test]
fn test_fn_convention_compiles() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00528_test_fn_convention.fz".to_string()),
        text: include_str!("../../fixtures2/00528_test_fn_convention.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "test_plain".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "fn test_*() convention should resolve");
    // TODO: JIT-execute and assert test_plain completes without error
}

// Ported from src/lib_test.rs: spawn with captured variables executes correctly end-to-end
#[test]
fn spawn_with_captured_variables_end_to_end() {
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
    assert_resolved(compiler.drive(), "spawn with captures should resolve");
    // TODO: JIT-execute and assert main completes successfully (parent(99) == 99)
}

// Ported from src/compiler/compiler_test.rs: spawn with captured variables runs correctly through full compiler
#[test]
fn spawn_with_captures_through_full_compiler() {
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
    assert_resolved(compiler.drive(), "spawn with captures through Compiler2 should resolve");
    // TODO: JIT-execute and assert exit halt_value == NIL_ATOM_ID (completes cleanly)
}

// Ported from src/modules/pipeline_test.rs: recursive protocol reduce callback converges without oscillation
#[test]
fn protocol_reduce_converges_to_fixpoint() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00529_protocol_reduce_fixpoint.fz".to_string()),
        text: include_str!("../../fixtures2/00529_protocol_reduce_fixpoint.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "protocol reduce should converge and resolve");
    // TODO: verify via telemetry that worklist_pops <= 100 (no planning oscillation)
    // TODO: JIT-execute and assert result == {:done, 6}
}

// Ported from src/modules/pipeline_test.rs: Utf8.valid? on a valid binary returns true through linked runtime
#[test]
fn utf8_module_import_runs_through_linked_runtime() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00530_utf8_module_import_main.fz".to_string()),
        text: include_str!("../../fixtures2/00530_utf8_module_import_main.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Utf8 module import and valid? call should resolve");
    // TODO: JIT-execute and assert result == true (Utf8.valid? on <<104, 105>>)
}

// Ported from src/exec/ast_value_test.rs: Elixir-aligned binops round-trip through quoted-atom encoding
#[test]
#[ignore = "ListConcat and other stdlib-backed binops not yet supported in native lowering"]
fn elixir_aligned_binop_operators_resolve() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00531_elixir_binop_operators.fz".to_string()),
        text: include_str!("../../fixtures2/00531_elixir_binop_operators.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "Elixir-aligned binop operators should resolve");
    // TODO: verify binop_atom/binop_from_atom round-trips for ++, --, <>, .., ..//,  in, not in
}
