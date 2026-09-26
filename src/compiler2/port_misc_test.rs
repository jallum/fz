//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
use super::drive_harness::assert_resolved;
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

// Ported from src/cli/test_runner_test.rs: fn test_*() convention is discovered and run like test macro
#[test]
fn test_fn_convention_compiles() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
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
    assert_resolved(compiler.drive(), "test_*() function convention should resolve");
    // TODO: JIT-execute and assert test_plain completes without error
}
