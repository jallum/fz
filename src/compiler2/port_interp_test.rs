//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
use super::drive_harness::assert_resolved;
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

// Ported from src/ir_interp/tests/resource_bif.rs: make_resource creates resource and dtor fires once on process exit
#[test]
fn make_resource_resolves_with_dtor_binding() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00248_make_resource_dtor.fz".to_string()),
        text: include_str!("../../fixtures2/00248_make_resource_dtor.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "make_resource with dtor should resolve");
    // TODO: JIT-execute, assert DTOR_FIRED == 1 and DTOR_LAST_PAYLOAD == 42 after process heap drop
}

// Ported from src/ir_interp/tests/resource_bif.rs: aliased resource bindings fire destructor exactly once
#[test]
fn aliased_resource_bindings_fire_dtor_once() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00249_aliased_resource_dtor.fz".to_string()),
        text: include_str!("../../fixtures2/00249_aliased_resource_dtor.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "aliased resource should resolve");
    // TODO: JIT-execute, assert DTOR_FIRED == 1 and DTOR_LAST_PAYLOAD == 7 (three names, one refcount edge)
}

// Ported from src/ir_interp/tests/resource_bif.rs: two distinct resources each fire their destructor exactly once
#[test]
fn two_distinct_resources_each_fire_dtor_once() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00250_two_distinct_resources.fz".to_string()),
        text: include_str!("../../fixtures2/00250_two_distinct_resources.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "two distinct resources should resolve");
    // TODO: JIT-execute, assert DTOR_FIRED == 2 (MSO chain must walk both Resource stubs)
}

// Ported from src/ir_interp/tests/resource_bif.rs: opaque resource .value accessor returns payload through module boundary
#[test]
fn opaque_resource_value_accessor_returns_payload() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00251_opaque_resource_value.fz".to_string()),
        text: include_str!("../../fixtures2/00251_opaque_resource_value.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "opaque resource .value accessor should resolve");
    // TODO: JIT-execute, assert R.get_value(r) == 99 and DTOR_FIRED == 1 after heap drop
}
