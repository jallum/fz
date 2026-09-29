//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
use super::{CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, RootSubmission};
use crate::diag::codes;
use crate::telemetry::{Capture, ConfiguredTelemetry};

fn metadata_str<'a>(event: &'a crate::telemetry::capture::OwnedEvent, key: &str) -> &'a str {
    match event.metadata.get(key) {
        Some(crate::telemetry::Value::Str(value)) => value.as_ref(),
        None if key == "code" => event
            .diagnostic
            .as_ref()
            .map(|diagnostic| diagnostic.code.0)
            .unwrap_or_else(|| panic!("diagnostic missing for metadata key `{key}`")),
        None if key == "message" => event
            .diagnostic
            .as_ref()
            .map(|diagnostic| diagnostic.message.as_str())
            .unwrap_or_else(|| panic!("diagnostic missing for metadata key `{key}`")),
        other => panic!("metadata key `{key}` missing or not str: {other:?}"),
    }
}

fn assert_last_error(capture: &Capture, code: &str, message: &str) {
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a compiler diagnostic");
    assert_eq!(metadata_str(&diagnostic, "code"), code);
    assert_eq!(metadata_str(&diagnostic, "message"), message);
}

// Ported from src/frontend/resolve_test.rs: importing an undefined module is a compile-time error
#[test]
fn import_undefined_module_is_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00065_import_undefined_module.fz".to_string()),
        text: include_str!("../../fixtures2/00065_import_undefined_module.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Unresolved { .. }),
        "import of undefined module should stay unresolved until the missing provider exists",
    );
    assert_last_error(
        &capture,
        codes::RESOLVE_UNKNOWN_MODULE.0,
        "module `Missing` is not defined",
    );
}
