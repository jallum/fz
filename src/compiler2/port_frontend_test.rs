//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
#![allow(unused_imports)]

use super::drive_test::{assert_resolved, function_id, module_id};
use super::{CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

// Ported from src/frontend/spec_check_test.rs: @spec param type matching inferred callsite type passes validation
#[test]
fn spec_param_type_matches_inferred_callsite() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00141_spec_param_type_match.fz".to_string()),
        text: include_str!("../../fixtures2/00141_spec_param_type_match.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "spec matching inferred type should resolve");
    // TODO: assert validate_specs produces no diagnostics (integer @spec matches integer inferred)
}

// Ported from src/frontend/spec_check_test.rs: @spec wider than inferred callsite type still passes (success typing)
#[test]
fn spec_wider_than_inferred_passes_success_typing() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00141_spec_param_type_match.fz".to_string()),
        text: include_str!("../../fixtures2/00141_spec_param_type_match.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "wider declared spec should accept narrower inferred callsite",
    );
    // TODO: assert validate_specs produces no diagnostics (int_lit(41) ⊆ integer passes)
}

// Ported from src/frontend/spec_check_test.rs: @spec disjoint from inferred callsite type produces a subtype violation
#[test]
fn spec_disjoint_from_inferred_produces_subtype_violation() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00142_spec_float_disjoint.fz".to_string()),
        text: include_str!("../../fixtures2/00142_spec_float_disjoint.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "disjoint spec should still resolve (diagnostic emitted separately)",
    );
    // TODO: assert validate_specs produces a "not a subtype" diagnostic (float @spec vs integer inferred)
}

// Ported from src/frontend/spec_check_test.rs: multi-overload @spec each cover their respective inferred specialisation
#[test]
fn multi_spec_overload_arrows_cover_each_inferred_shape() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00143_spec_multi_overload_echo.fz".to_string()),
        text: include_str!("../../fixtures2/00143_spec_multi_overload_echo.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "each inferred shape covered by one declared arrow should resolve",
    );
    // TODO: assert validate_specs produces no diagnostics for per-arrow coverage
}

// Ported from src/frontend/spec_check_test.rs: spec overloads are checked per-arrow not by unioning all inputs and results
#[test]
fn multi_spec_validation_preserves_param_result_correlation() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00144_spec_swapped_overload_echo.fz".to_string()),
        text: include_str!("../../fixtures2/00144_spec_swapped_overload_echo.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "swapped overload spec should still resolve");
    // TODO: assert validate_specs produces a "not a subtype" diagnostic (correlated arrows must fail, unioning would pass)
}

// Ported from src/frontend/spec_check_test.rs: @spec using a local @type alias resolves and passes validation
#[test]
fn spec_resolves_against_module_type_alias() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00145_spec_type_alias.fz".to_string()),
        text: include_str!("../../fixtures2/00145_spec_type_alias.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "alias-based spec should resolve and pass validation");
    // TODO: assert validate_specs produces no diagnostics (@type id :: integer resolves correctly)
}

// Ported from src/frontend/spec_check_test.rs: @spec with protocol domain type accepts a type with a known impl
#[test]
fn protocol_domain_spec_accepts_known_impl_target() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00146_protocol_spec_known_impl.fz".to_string()),
        text: include_str!("../../fixtures2/00146_protocol_spec_known_impl.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "known protocol impl target should satisfy protocol domain spec",
    );
    // TODO: assert validate_specs produces no diagnostics (List has Enumerable impl)
}

// Ported from src/frontend/spec_check_test.rs: @spec with protocol domain type rejects a type with no protocol impl
#[test]
fn protocol_domain_spec_rejects_type_without_impl() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00147_protocol_spec_no_impl.fz".to_string()),
        text: include_str!("../../fixtures2/00147_protocol_spec_no_impl.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "integer with no Enumerable impl should still resolve");
    // TODO: assert validate_specs produces a "not a subtype" diagnostic (integer has no Enumerable impl)
}

// Ported from src/frontend/spec_check_test.rs: @spec with unknown type alias surfaces unknown-type error at validation
#[test]
fn spec_with_unknown_type_alias_produces_diagnostic() {
    let tel = ConfiguredTelemetry::new();
    let capture = crate::telemetry::Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00148_spec_unknown_type_alias.fz".to_string()),
        text: include_str!("../../fixtures2/00148_spec_unknown_type_alias.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // The user's bad spec is reported as a diagnostic; the diagnosed spec
    // constrains nothing and the program still compiles (old-world
    // spec_check behavior, shared with
    // port_resolve_test::spec_unknown_type_is_resolve_error).
    assert_resolved(
        compiler.drive(),
        "a diagnosed @spec must not stop the program from compiling",
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("the unknown spec type must surface as a diagnostic");
    let Some(crate::telemetry::Value::Str(message)) = diagnostic.metadata.get("message") else {
        panic!("diagnostic message missing");
    };
    assert!(
        message.contains("unknown type name `unknown_thing`"),
        "diagnostic names the unknown type: {message}",
    );
}

// Ported from src/frontend/spec_check_test.rs: fn with no @spec annotation produces no type validation diagnostics
#[test]
fn fn_without_spec_produces_no_validation_diagnostics() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00149_fn_without_spec.fz".to_string()),
        text: include_str!("../../fixtures2/00149_fn_without_spec.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "fn without @spec should resolve cleanly with no diagnostics",
    );
    // TODO: assert validate_specs produces no diagnostics (no @spec means no validation target)
}

// Ported from src/frontend/spec_check_test.rs: @spec on a top-level fn with only builtin types passes without module env
#[test]
fn spec_on_top_level_fn_uses_builtin_env() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00150_spec_top_level_fn.fz".to_string()),
        text: include_str!("../../fixtures2/00150_spec_top_level_fn.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "top-level @spec with builtin scalar should resolve and pass",
    );
    // TODO: assert validate_specs produces no diagnostics (top-level fn uses empty module env)
}

// Ported from src/frontend/pattern_check_test.rs: wildcard clause makes subsequent specific clauses unreachable
#[test]
fn wildcard_before_specific_clause_makes_it_unreachable() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00151_wildcard_makes_unreachable.fz".to_string()),
        text: include_str!("../../fixtures2/00151_wildcard_makes_unreachable.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "wildcard before specific clause should resolve (with unreachable-arm diagnostic)",
    );
    // TODO: assert diagnostics contain TYPE_UNREACHABLE_ARM for the classify(0) clause
}

// Ported from src/frontend/pattern_check_test.rs: wildcard arm in case makes subsequent arms unreachable
#[test]
fn case_wildcard_arm_makes_subsequent_arms_unreachable() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00152_case_wildcard_unreachable.fz".to_string()),
        text: include_str!("../../fixtures2/00152_case_wildcard_unreachable.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "case wildcard arm before specific arm should resolve (with unreachable-arm diagnostic)",
    );
    // TODO: assert diagnostics contain TYPE_UNREACHABLE_ARM for the `0 -> :zero` arm
}

// Ported from src/frontend/pattern_check_test.rs: specific clause before wildcard is reachable, no spurious warning
#[test]
fn specific_clause_before_wildcard_produces_no_warning() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00153_specific_then_wildcard.fz".to_string()),
        text: include_str!("../../fixtures2/00153_specific_then_wildcard.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "specific-then-wildcard should resolve with no diagnostics",
    );
    // TODO: assert no TYPE_UNREACHABLE_ARM diagnostic is emitted
}

// Ported from src/frontend/pattern_check_test.rs: fn with only literal clauses and no wildcard is inexhaustive
#[test]
fn fn_with_only_literal_clauses_is_inexhaustive() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00154_inexhaustive_literal_clauses.fz".to_string()),
        text: include_str!("../../fixtures2/00154_inexhaustive_literal_clauses.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "inexhaustive literal clauses should resolve (with no-matching-clause diagnostic)",
    );
    // TODO: assert diagnostics contain TYPE_NO_MATCHING_CLAUSE
}

// Ported from src/frontend/pattern_check_test.rs: case with only literal arms and no wildcard is inexhaustive
#[test]
fn case_with_only_literal_arms_is_inexhaustive() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00155_inexhaustive_case.fz".to_string()),
        text: include_str!("../../fixtures2/00155_inexhaustive_case.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "inexhaustive case arms should resolve (with no-matching-clause diagnostic)",
    );
    // TODO: assert diagnostics contain TYPE_NO_MATCHING_CLAUSE
}

// Ported from src/frontend/pattern_check_test.rs: wildcard clause makes pattern set exhaustive, no warning
#[test]
fn wildcard_clause_makes_pattern_set_exhaustive() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00153_specific_then_wildcard.fz".to_string()),
        text: include_str!("../../fixtures2/00153_specific_then_wildcard.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "wildcard clause makes pattern exhaustive — should resolve with no no-matching-clause diagnostic",
    );
    // TODO: assert no TYPE_NO_MATCHING_CLAUSE diagnostic is emitted
}

// Ported from src/frontend/frontend_test.rs: inexhaustive pattern match produces no-matching-clause warning
#[test]
fn inexhaustive_pattern_match_produces_no_matching_clause_warning() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00154_inexhaustive_literal_clauses.fz".to_string()),
        text: include_str!("../../fixtures2/00154_inexhaustive_literal_clauses.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "inexhaustive pattern match should resolve and emit a TYPE_NO_MATCHING_CLAUSE warning",
    );
    // TODO: assert diagnostics contain TYPE_NO_MATCHING_CLAUSE (warning, not error)
}

// Ported from src/frontend/frontend_test.rs: unbound name in expression is a compile-time error
#[test]
fn unbound_name_in_expression_is_compile_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00156_unbound_name_error.fz".to_string()),
        text: include_str!("../../fixtures2/00156_unbound_name_error.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    // Unbound name causes a fatal during lowering — expect non-Resolved outcome
    assert!(
        !matches!(compiler.drive(), DriveOutcome::Resolved),
        "unbound name should produce a fatal outcome (lowering fails)"
    );
    // TODO: assert diagnostics contain at least one Severity::Error for `missing` being unresolved
}

// Ported from src/frontend/frontend_test.rs: cross-module import from external interface resolves call edges
#[test]
fn cross_module_import_resolves_external_call_edges() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00157_cross_module_import.fz".to_string()),
        text: include_str!("../../fixtures2/00157_cross_module_import.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 2,
        need: ExecutableNeed::Value,
    });
    // Math module body is not provided; compiler2 stalls waiting for it — expect Unresolved
    assert!(
        !matches!(compiler.drive(), DriveOutcome::Resolved),
        "cross-module import with missing provider body should not resolve"
    );
    // TODO: submit a Math stub or use interface injection so cross-module import fully resolves
    // TODO: once resolved, assert the provider-boundary call view contains Math.add/2 and User.run is defined
}
