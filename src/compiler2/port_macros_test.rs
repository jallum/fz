//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
use super::drive_harness::assert_resolved;
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

// Ported from src/frontend/macros_test.rs: macro-introduced binding does not capture caller's variable
#[test]
fn macro_hygiene_local_does_not_shadow_caller() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
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
