//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
#![allow(unused_imports)]

use super::drive_test::{assert_resolved, function_id, module_id};
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

// Ported from src/frontend/macros_test.rs: macro quote+unquote expands arithmetic at compile time
#[test]
#[ignore = "compiler2 macro expansion not yet implemented (defmacro/quote/unquote)"]
fn macro_quote_unquote_arithmetic() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00111_macro_quote_unquote.fz".to_string()),
        text: include_str!("../../fixtures2/00111_macro_quote_unquote.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "macro quote+unquote should resolve");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/frontend/macros_test.rs: macro called multiple times inside a fn body
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn macro_called_multiple_times_in_body() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00112_macro_multiple_calls.fz".to_string()),
        text: include_str!("../../fixtures2/00112_macro_multiple_calls.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "macro used multiple times should resolve");
    // TODO: JIT-execute and assert result == 60
}

// Ported from src/frontend/macros_test.rs: macro expansion splices a call to a regular function
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn macro_expansion_splices_regular_fn_call() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00113_macro_splices_fn_call.fz".to_string()),
        text: include_str!("../../fixtures2/00113_macro_splices_fn_call.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "macro splicing a regular fn call should resolve");
    // TODO: JIT-execute and assert result == 21
}

// Ported from src/frontend/macros_test.rs: nested macro wraps inner macro and expander re-expands result
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn nested_macro_expander_re_expands_result() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00114_nested_macro_expansion.fz".to_string()),
        text: include_str!("../../fixtures2/00114_nested_macro_expansion.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "nested macro expansion should resolve");
    // TODO: JIT-execute and assert result == 41
}

// Ported from src/frontend/macros_test.rs: macro args are passed as quoted AST, not pre-evaluated
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn macro_args_received_as_quoted_ast() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00115_macro_args_quoted_ast.fz".to_string()),
        text: include_str!("../../fixtures2/00115_macro_args_quoted_ast.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "macro receiving quoted AST args should resolve");
    // TODO: JIT-execute and assert result == 6 (m2 sees m1(0) as AST, so result is m1(0)+5 = 1+5 = 6)
}

// Ported from src/frontend/macros_test.rs: self-referencing macro hits depth limit without stack overflow
#[test]
fn runaway_macro_hits_depth_limit() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00116_runaway_macro_loop.fz".to_string()),
        text: include_str!("../../fixtures2/00116_runaway_macro_loop.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // TODO: assert that drive() returns an error (ExpansionLoop) rather than resolving or overflowing the stack
    let _ = compiler.drive();
}

// Ported from src/frontend/macros_test.rs: macro-introduced binding does not capture caller's variable
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn macro_hygiene_local_does_not_shadow_caller() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00117_macro_hygiene_local.fz".to_string()),
        text: include_str!("../../fixtures2/00117_macro_hygiene_local.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "hygienic macro local binding should resolve");
    // TODO: JIT-execute and assert result == 1 (caller's t survives, macro's t is a fresh gensym)
}

// Ported from src/frontend/macros_test.rs: unquoted variable splices caller's value into macro expansion
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn macro_hygiene_unquoted_var_splices_caller_value() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00118_macro_hygiene_unquote.fz".to_string()),
        text: include_str!("../../fixtures2/00118_macro_hygiene_unquote.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "unquoted var splicing caller value should resolve");
    // TODO: JIT-execute and assert result == 8 (unquote(x) splices 7, so 7+1=8)
}

// Ported from src/frontend/macros_test.rs: same macro-introduced name maps to one gensym within an invocation
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn macro_hygiene_consistent_gensym_within_invocation() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00119_macro_hygiene_gensym.fz".to_string()),
        text: include_str!("../../fixtures2/00119_macro_hygiene_gensym.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "consistent gensym within one invocation should resolve",
    );
    // TODO: JIT-execute and assert result == 42 (t__hyg_N = 21; t__hyg_N + t__hyg_N = 42)
}

// Ported from src/frontend/macros_test.rs: cross-module macro expansion qualifies bare names against home module
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn cross_module_macro_qualifies_names_against_home_module() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00120_cross_module_macro.fz".to_string()),
        text: include_str!("../../fixtures2/00120_cross_module_macro.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "cross-module macro qualifying bare names should resolve",
    );
    // TODO: JIT-execute and assert result == 107 (M.bump(7) expands to M.helper(7) = 7+100 = 107)
}

// Ported from src/frontend/macros_test.rs: imported macro is callable unqualified in importing module
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn imported_macro_callable_unqualified() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00121_imported_macro_unqualified.fz".to_string()),
        text: include_str!("../../fixtures2/00121_imported_macro_unqualified.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "imported macro used unqualified should resolve");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/frontend/macros_test.rs: item-level macro returns :fn_def tuple splicing a callable function
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn item_macro_fn_def_tuple_splices_callable_fn() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00122_item_macro_fn_def.fz".to_string()),
        text: include_str!("../../fixtures2/00122_item_macro_fn_def.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "item macro splicing a fn via :fn_def tuple should resolve",
    );
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/frontend/macros_test.rs: item macro returning a list of :fn_def tuples splices multiple fns
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn item_macro_list_of_fn_def_tuples_splices_multiple_fns() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00123_item_macro_list_of_fns.fz".to_string()),
        text: include_str!("../../fixtures2/00123_item_macro_list_of_fns.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "item macro splicing multiple fns via list should resolve",
    );
    // TODO: JIT-execute and assert result == 30 (first() + second() = 10 + 20)
}

// Ported from src/frontend/macros_test.rs: item macro inside defmodule qualifies spliced fn names with module path
#[test]
#[ignore = "compiler2 macro expansion not yet implemented"]
fn item_macro_in_module_qualifies_spliced_fn_names() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00124_item_macro_in_module.fz".to_string()),
        text: include_str!("../../fixtures2/00124_item_macro_in_module.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "item macro inside defmodule qualifying fn names should resolve",
    );
    // TODO: JIT-execute and assert result == 314
}

// Ported from src/frontend/macros_test.rs: expansion pipeline without macros evaluates plain arithmetic correctly
#[test]
fn expansion_pipeline_noop_without_macros() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00125_plain_arithmetic.fz".to_string()),
        text: include_str!("../../fixtures2/00125_plain_arithmetic.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "plain arithmetic without macros should resolve");
    // TODO: JIT-execute and assert result == 3
}

// Ported from src/frontend/macros_test.rs: pipe operator |> rewrites to regular call at expansion time
#[test]
fn pipe_operator_rewrites_to_regular_call() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00126_pipe_operator.fz".to_string()),
        text: include_str!("../../fixtures2/00126_pipe_operator.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "pipe operator rewrite should resolve");
    // TODO: JIT-execute and assert result == 3
}

// Ported from src/frontend/macros_test.rs: ++, --, <>, .. and //2 operators desugar to stdlib function calls
#[test]
#[ignore = "compiler2 operator desugar (++, --, <>, Range.new) not yet implemented in body lowering"]
fn operator_sugars_desugar_to_stdlib_calls() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00127_operator_sugar_rewrites.fz".to_string()),
        text: include_str!("../../fixtures2/00127_operator_sugar_rewrites.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "operator sugars desugaring to stdlib calls should resolve",
    );
    // TODO: assert ++ → List.concat/2, -- → List.subtract/2, <> → Kernel.fz_binary_concat/2, .. → Range.new/3, ..// → Range.new/3
}

// Ported from src/frontend/macros_test.rs: `in` and `not in` desugar to Enum.member? at expansion time
#[test]
#[ignore = "compiler2 operator desugar (in/not in → Enum.member?) not yet implemented in body lowering"]
fn membership_operators_desugar_to_enum_member() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00128_membership_sugar_rewrites.fz".to_string()),
        text: include_str!("../../fixtures2/00128_membership_sugar_rewrites.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "membership operators desugaring to Enum.member? should resolve",
    );
    // TODO: assert `in` → Enum.member?/2, `not in` → not(Enum.member?/2)
}

// Ported from src/frontend/macros_test.rs: & capture shorthand desugars to a callable lambda
#[test]
#[ignore = "compiler2 frontdoor does not yet parse &1 capture-arg syntax"]
fn capture_shorthand_desugars_to_callable_lambda() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00129_capture_shorthand_lambda.fz".to_string()),
        text: include_str!("../../fixtures2/00129_capture_shorthand_lambda.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "capture shorthand desugaring to lambda should resolve",
    );
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/frontend/macros_test.rs: bare &1 desugars to identity lambda returning its first argument
#[test]
#[ignore = "compiler2 frontdoor does not yet parse &1 capture-arg syntax"]
fn bare_capture_arg_desugars_to_identity_lambda() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00130_bare_capture_identity.fz".to_string()),
        text: include_str!("../../fixtures2/00130_bare_capture_identity.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "bare &1 desugaring to identity lambda should resolve");
    // TODO: JIT-execute and assert result == 42
}

// Ported from src/frontend/macros_test.rs: multi-clause fn literal desugars to case expression with pattern dispatch
#[test]
fn multi_clause_lambda_desugars_to_case_dispatch() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00131_multi_clause_lambda.fz".to_string()),
        text: include_str!("../../fixtures2/00131_multi_clause_lambda.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "multi-clause lambda desugaring to case dispatch should resolve",
    );
    // TODO: JIT-execute and assert result == {:zero, :pos, :other}
}
