//! Ported tests from old-world — behaviour already captured; assertions filled in next pass.
use std::cell::RefCell;
use std::rc::Rc;

use super::drive_test::assert_resolved;
use super::{
    CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, InterfaceCallableKind, ModuleInterface,
    ModuleInterfaceCallable, RootSubmission, World,
};
use crate::diag::{Diagnostic, codes};
use crate::fz_ir::{DirectCallTarget, Term};
use crate::source::Span;
use crate::telemetry::handler::{Event, Handler};
use crate::telemetry::{Capture, ConfiguredTelemetry};

fn metadata_str<'a>(event: &'a crate::telemetry::capture::OwnedEvent, key: &str) -> &'a str {
    match event.metadata.get(key) {
        Some(crate::telemetry::Value::Str(value)) => value.as_ref(),
        other => panic!("metadata key `{key}` missing or not str: {other:?}"),
    }
}

/// Captures the primary span of the last `[fz, diag, error]` diagnostic seen.
/// `Capture` durably owns its events, which strips the opaque `Diagnostic`
/// payload (opaque values are not durable) -- so a span assertion needs a
/// handler that reads the `Diagnostic` synchronously, inside `handle`, the
/// way `telemetry::diag_render::DiagRenderer` does for rendering.
struct LastErrorSpan {
    span: Rc<RefCell<Option<Span>>>,
}

impl Handler for LastErrorSpan {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "diag", "error"] {
            return;
        }
        if let Some(diagnostic) = event
            .metadata
            .get("diagnostic")
            .and_then(|value| value.downcast_ref::<Diagnostic>())
        {
            *self.span.borrow_mut() = Some(diagnostic.primary.span);
        }
    }
}

fn assert_last_error(capture: &Capture, code: &str, message: &str) {
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a compiler diagnostic");
    assert_eq!(metadata_str(&diagnostic, "code"), code);
    assert_eq!(metadata_str(&diagnostic, "message"), message);
}

// Ported from src/frontend/resolve_test.rs: defmodule qualifies all fn names with the module path
#[test]
fn module_qualifies_fn_names() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00053_module_qualifies_fn.fz".to_string()),
        text: include_str!("../../fixtures2/00053_module_qualifies_fn.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "f".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "module qualifies fn names");
    // TODO: assert that the resolved function name is M.f (not bare f), and M.__info__/1 is also present
}

// Ported from src/frontend/resolve_test.rs: top-level fns outside defmodule retain their bare names
#[test]
fn top_level_fn_keeps_bare_name() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00054_top_level_bare_fn.fz".to_string()),
        text: include_str!("../../fixtures2/00054_top_level_bare_fn.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "helper".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "top-level fn retains bare name");
    // TODO: assert that the function is registered as "helper" (not "M.helper" or similar)
}

// Ported from src/frontend/resolve_test.rs: sibling function call inside module is qualified to full module path
#[test]
fn sibling_call_in_module_qualifies() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00055_sibling_call_qualifies.fz".to_string()),
        text: include_str!("../../fixtures2/00055_sibling_call_qualifies.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "use_helper".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "sibling call qualifies to M.helper");
    // TODO: assert that the call site in use_helper references M.helper (not bare helper)
}

// Ported from src/frontend/resolve_test.rs: qualified cross-module call resolves to the target module's fn
#[test]
fn cross_module_call_resolves() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00056_cross_module_call.fz".to_string()),
        text: include_str!("../../fixtures2/00056_cross_module_call.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("B".to_string()),
        name: "caller".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "cross-module call A.ping resolves");
    // TODO: assert the call site in B.caller resolves to A.ping
}

// Ported from src/frontend/resolve_test.rs: parameter shadowing a fn name is not rewritten to module path
#[test]
fn param_name_shadows_module_fn() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00057_param_shadows_fn_name.fz".to_string()),
        text: include_str!("../../fixtures2/00057_param_shadows_fn_name.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "shadow".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "param shadow not rewritten to module path");
    // TODO: assert body of M.shadow is Var("helper"), not Var("M.helper")
}

// Ported from src/frontend/resolve_test.rs: nested defmodule produces dotted module path for contained fns
#[test]
fn nested_module_produces_dotted_path() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00058_nested_module_dotted.fz".to_string()),
        text: include_str!("../../fixtures2/00058_nested_module_dotted.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("A.B".to_string()),
        name: "f".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "nested module A.B.f resolves");
    // TODO: assert fn names are [A.B.f, A.B.__info__, A.__info__]
}

// Ported from src/frontend/resolve_test.rs: caller outside nested module resolves dotted path correctly
#[test]
fn caller_outside_nested_module_resolves_dotted_path() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00059_nested_call_from_outside.fz".to_string()),
        text: include_str!("../../fixtures2/00059_nested_call_from_outside.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "main calling A.B.f resolves");
    // TODO: assert callee in main is A.B.f
}

// Ported from src/frontend/resolve_test.rs: alias expands short name to full module path at call sites
#[test]
fn alias_expands_to_full_module_path() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00060_alias_expands_module_path.fz".to_string()),
        text: include_str!("../../fixtures2/00060_alias_expands_module_path.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "caller".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "alias Path expands to Long.Path.f");
    // TODO: assert callee in User.caller is Long.Path.f
}

// Ported from src/frontend/resolve_test.rs: alias with `as:` renames a module to a custom short name
#[test]
fn alias_with_as_renames_module() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00061_alias_with_as_rename.fz".to_string()),
        text: include_str!("../../fixtures2/00061_alias_with_as_rename.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "caller".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "alias P (as: Long.Path) expands to Long.Path.f");
    // TODO: assert callee in User.caller is Long.Path.f
}

// Ported from src/frontend/resolve_test.rs: unfiltered import brings all exported names into scope
#[test]
fn import_unfiltered_pulls_all_names() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00062_import_unfiltered_all.fz".to_string()),
        text: include_str!("../../fixtures2/00062_import_unfiltered_all.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 2,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "import Math unfiltered resolves add");
    // TODO: assert callee in User.run is Math.add
}

// Ported from src/frontend/resolve_test.rs: import only: [] brings exactly the named exports into scope
#[test]
fn import_only_filters_to_named_exports() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00063_import_only_filter.fz".to_string()),
        text: include_str!("../../fixtures2/00063_import_only_filter.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "r1".to_string(),
        arity: 2,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "import only:[add:2] resolves r1 but not r2");
    // TODO: assert r1 callee is Math.add; assert r2 callee is bare mul (not resolved)
}

// Ported from src/frontend/resolve_test.rs: local fn definition shadows an imported name of the same arity
#[test]
fn local_fn_definition_shadows_imported_name() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00064_local_fn_shadows_import.fz".to_string()),
        text: include_str!("../../fixtures2/00064_local_fn_shadows_import.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "use_local".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "local add shadows imported Math.add");
    // TODO: assert callee in User.use_local is User.add (not Math.add)
}

// Ported from src/frontend/resolve_test.rs: importing an undefined module is a compile-time error
#[test]
fn import_undefined_module_is_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
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

// Ported from src/frontend/resolve_test.rs: aliasing an undefined module path is a compile-time error
#[test]
fn alias_undefined_module_is_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00066_alias_undefined_module.fz".to_string()),
        text: include_str!("../../fixtures2/00066_alias_undefined_module.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "alias of undefined module path produces an error");
    // TODO: assert drive emits RESOLVE_UNKNOWN_MODULE diagnostic for Missing.Path
}

// Ported from src/frontend/resolve_test.rs: importing a name at an arity not exported by the module errors
#[test]
fn import_wrong_arity_is_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00067_import_wrong_arity.fz".to_string()),
        text: include_str!("../../fixtures2/00067_import_wrong_arity.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "import of add/1 (exported as add/2) should fail once Math's interface settles",
    );
    assert_last_error(
        &capture,
        codes::RESOLVE_UNKNOWN_IMPORT.0,
        "module `Math` does not export `add/1`",
    );
}

// Ported from src/frontend/resolve_test.rs: import except: [] referencing a non-exported arity is an error
#[test]
fn import_except_wrong_arity_is_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00068_import_except_wrong_arity.fz".to_string()),
        text: include_str!("../../fixtures2/00068_import_except_wrong_arity.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 2,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "import except:[add:1] should fail once Math's interface settles",
    );
    assert_last_error(
        &capture,
        codes::RESOLVE_UNKNOWN_IMPORT.0,
        "module `Math` does not export `add/1`",
    );
}

// Ported from src/frontend/resolve_test.rs: import resolves against provider interface without source body
#[test]
fn import_from_external_interface_carries_provider_boundary_call_without_provider_body() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let math = world.reference_module("Math".to_string());
    let add = world.reference_function(math, "add".to_string(), 2);
    world.submit_module_interface(
        "Math".to_string(),
        ModuleInterface::new(vec![ModuleInterfaceCallable {
            function: add,
            reference: world.function_ref(add).clone(),
            kind: InterfaceCallableKind::PublicFunction,
            variadic: false,
        }]),
    );
    world.submit_code(
        Some("fixtures2/00069_import_from_external_interface.fz".to_string()),
        include_str!("../../fixtures2/00069_import_from_external_interface.fz").to_string(),
    );
    let root = world.submit_root(Some("User".to_string()), "run".to_string(), 2, ExecutableNeed::Value);
    // Native lowering is demand-only, so demand it explicitly before driving.
    world.demand(super::Job::LowerNativeProgram(root));
    assert_resolved(world.drive(), "interface-only provider call should settle");
    assert!(
        world.module_defined_revision(math).is_none(),
        "external interface imports should not require a provider module body",
    );
    assert!(
        world.module_interface_revision(math).is_some(),
        "external interface imports should publish the provider interface fact",
    );
    let program = world.native_program(root);
    let edges = program.module.external_call_edges();
    assert_eq!(
        edges.len(),
        1,
        "provider-boundary call should produce one derived import edge"
    );
    assert_eq!(edges[0].target.module.to_string(), "Math");
    assert_eq!(edges[0].target.name, "add");
    assert_eq!(edges[0].target.arity, 2);
    assert!(
        program.module.fns.iter().any(|function| {
            function.blocks.iter().any(|block| {
                matches!(
                    &block.terminator,
                    Term::Call {
                        callee: DirectCallTarget::ProviderBoundary(target),
                        ..
                    } | Term::TailCall {
                        callee: DirectCallTarget::ProviderBoundary(target),
                        ..
                    } if target.module.to_string() == "Math" && target.name == "add" && target.arity == 2
                )
            })
        }),
        "native program should carry provider-boundary call in the raw IR term"
    );
}

// Ported from src/frontend/resolve_test.rs: import from runtime stdlib resolves without explicit interface table entry
#[test]
fn import_from_runtime_stdlib_resolves() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00070_import_runtime_stdlib.fz".to_string()),
        text: include_str!("../../fixtures2/00070_import_runtime_stdlib.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "import from runtime Utf8 stdlib resolves");
    // TODO: assert callee is Utf8.valid?; Utf8 not in user-supplied module_interfaces
}

// Ported from src/frontend/resolve_test.rs: alias to runtime stdlib module resolves on demand at call sites
#[test]
fn alias_to_runtime_stdlib_resolves_on_demand() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00071_alias_runtime_stdlib.fz".to_string()),
        text: include_str!("../../fixtures2/00071_alias_runtime_stdlib.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "alias U -> Utf8 resolves call site on demand");
    // TODO: assert callee is Utf8.valid?; Utf8 in external_module_interfaces; Process is not
}

// Ported from src/frontend/resolve_test.rs: qualified call to runtime module namespace fetches that interface lazily
#[test]
fn qualified_runtime_call_fetches_interface_lazily() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00072_qualified_runtime_call.fz".to_string()),
        text: include_str!("../../fixtures2/00072_qualified_runtime_call.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "qualified Utf8.valid? call fetches interface lazily");
    // TODO: assert Utf8 in external_module_interfaces after drive
}

// Ported from src/frontend/resolve_test.rs: runtime module with protocol impl pulls in both module and protocol interfaces
#[test]
fn runtime_module_with_protocol_impl_loads_both_interfaces() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00073_runtime_protocol_impl.fz".to_string()),
        text: include_str!("../../fixtures2/00073_runtime_protocol_impl.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "Range.new pull loads both Range and Enumerable interfaces",
    );
    // TODO: assert Range and Enumerable are both in external_module_interfaces
}

// Ported from src/frontend/resolve_test.rs: importing a name not in a module's export list is an error
#[test]
fn import_non_exported_name_is_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00074_import_non_exported_name.fz".to_string()),
        text: include_str!("../../fixtures2/00074_import_non_exported_name.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "import of non-exported name hidden/0 should fail once Math's interface settles",
    );
    assert_last_error(
        &capture,
        codes::RESOLVE_UNKNOWN_IMPORT.0,
        "module `Math` does not export `hidden/0`",
    );
}

// Ported from src/frontend/resolve_test.rs: importing the same name from two modules is a conflict error
#[test]
fn conflicting_imports_produce_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00075_conflicting_imports.fz".to_string()),
        text: include_str!("../../fixtures2/00075_conflicting_imports.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "importing f from A and B produces a conflict error");
    // TODO: assert RESOLVE_CONFLICTING_IMPORT: "import f/0 from B conflicts with existing import from A"
}

// Ported from src/frontend/resolve_test.rs: importing the same name from the same module twice is idempotent
#[test]
fn duplicate_same_module_import_is_idempotent() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00076_duplicate_import_idempotent.fz".to_string()),
        text: include_str!("../../fixtures2/00076_duplicate_import_idempotent.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 2,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "duplicate import of Math.add/2 is idempotent");
    // TODO: assert callee in User.run is Math.add (no error for duplicate same-module import)
}

// Ported from src/frontend/resolve_test.rs: top-level import brings module names into scope for top-level fns
#[test]
fn top_level_import_resolves_top_level_fn_calls() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00077_top_level_import.fz".to_string()),
        text: include_str!("../../fixtures2/00077_top_level_import.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "top-level import Math resolves add in main");
    // TODO: assert callee in main is Math.add
}

// Ported from src/frontend/resolve_test.rs: top-level alias expands module shorthand in top-level fn calls
#[test]
fn top_level_alias_resolves_top_level_fn_calls() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00078_top_level_alias.fz".to_string()),
        text: include_str!("../../fixtures2/00078_top_level_alias.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "top-level alias I -> Outer.Inner expands in main");
    // TODO: assert callee in main is Outer.Inner.value
}

// Ported from src/frontend/resolve_test.rs: @type aliases in defmodule are parsed, attached, and type-resolved
#[test]
fn type_aliases_in_module_parse_and_resolve() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00079_type_aliases_in_module.fz".to_string()),
        text: include_str!("../../fixtures2/00079_type_aliases_in_module.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "one".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "@type id/pair/keyword attach and resolve in module M");
    // TODO: assert id == integer, pair == {integer,integer}, keyword(integer) == [{atom,integer}]
}

// Ported from src/frontend/resolve_test.rs: @type alias can reference runtime stdlib type aliases like keyword/1
#[test]
fn module_type_alias_can_use_stdlib_keyword() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00080_type_alias_uses_stdlib.fz".to_string()),
        text: include_str!("../../fixtures2/00080_type_alias_uses_stdlib.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "run".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "@type opts :: keyword(integer) resolves via stdlib");
    // TODO: assert opts alias resolves to [{atom, integer}]
}

// Ported from src/frontend/resolve_test.rs: defstruct with @type t populates typed field information for the struct
#[test]
fn struct_type_alias_populates_field_types() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00081_struct_type_alias_fields.fz".to_string()),
        text: include_str!("../../fixtures2/00081_struct_type_alias_fields.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("Range".to_string()),
        name: "__info__".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "@type t with all struct fields resolves the struct record shape",
    );
    // TODO: assert Range's resolved struct record shape has first/last/step all as integer.
}

// Ported from src/frontend/resolve_test.rs: @type t for a struct must cover all defstruct fields or is an error
#[test]
fn struct_type_alias_must_cover_all_fields() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00082_struct_type_alias_mismatch.fz".to_string()),
        text: include_str!("../../fixtures2/00082_struct_type_alias_mismatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("Range".to_string()),
        name: "__info__".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "@type t missing field step produces a type alias error",
    );
    // TODO: assert TypeAliasError with message containing "missing field `step`"
}

// Ported from src/frontend/resolve_test.rs: @spec can use stdlib type aliases without local @type definitions
#[test]
fn spec_can_use_stdlib_keyword_without_local_type() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00083_spec_uses_stdlib_alias.fz".to_string()),
        text: include_str!("../../fixtures2/00083_spec_uses_stdlib_alias.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "run".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "@spec run(keyword(integer)) resolves without local @type",
    );
    // TODO: assert spec param[0] resolves to [{atom, integer}]
}

// Ported from src/frontend/resolve_test.rs: @spec attribute is parsed and attached to the following fn definition
#[test]
fn spec_attribute_attaches_to_fn() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00084_spec_attaches_to_fn.fz".to_string()),
        text: include_str!("../../fixtures2/00084_spec_attaches_to_fn.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "add1".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "@spec add1(integer) :: integer attaches to M.add1");
    // TODO: assert spec name=="add1", param[0]==integer, result==integer
}

// Ported from src/frontend/resolve_test.rs: @spec with zero-parameter fn parses correctly
#[test]
fn spec_zero_arity_parses_correctly() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00085_spec_zero_arity.fz".to_string()),
        text: include_str!("../../fixtures2/00085_spec_zero_arity.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "one".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "@spec one() :: integer parses zero-arity correctly");
    // TODO: assert spec.param_body_tokens.len() == 0
}

// Ported from src/frontend/resolve_test.rs: @spec arity not matching fn arity is a parse-time error
#[test]
fn spec_arity_mismatch_is_parse_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00086_spec_arity_mismatch.fz".to_string()),
        text: include_str!("../../fixtures2/00086_spec_arity_mismatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "add1".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "@spec add1(integer,integer) should fail during function surface decoding",
    );
    assert_last_error(
        &capture,
        codes::PARSE_SPEC_ARITY_MISMATCH.0,
        "@spec arity 2 doesn't match function `add1/1`",
    );
}

// Ported from src/frontend/resolve_test.rs: @spec name not matching the following fn name is a parse-time error
#[test]
fn spec_name_mismatch_is_parse_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00087_spec_name_mismatch.fz".to_string()),
        text: include_str!("../../fixtures2/00087_spec_name_mismatch.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "add1".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "@spec other vs fn add1 should fail during function surface decoding",
    );
    assert_last_error(
        &capture,
        codes::PARSE_SPEC_NAME_MISMATCH.0,
        "@spec name `other` doesn't match function `add1`",
    );
}

// fz-go4.48: an @spec syntax typo (missing return type after `::`) is a
// USER-reachable mistake in the @spec sub-grammar -- quoted_function.rs is
// the sole validator of @spec token payloads, so this must surface as a
// PARSE_EXPECTED_TOKEN user diagnostic, not as
// INTERNAL_POST_RESOLUTION_LEFTOVER (which is what
// QuotedSourceError::new(..) routed it to before the reclassification).
#[test]
fn spec_missing_return_type_is_parse_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00554_spec_syntax_missing_return_type.fz".to_string()),
        text: include_str!("../../fixtures2/00554_spec_syntax_missing_return_type.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "add1".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "@spec add1(integer) :: with no result type should fail during function surface decoding",
    );
    assert_last_error(
        &capture,
        codes::PARSE_EXPECTED_TOKEN.0,
        "expected result type expression after `::` in @spec",
    );
}

// fz-go4.48: an unrecognized bitstring modifier atom (e.g. `<<1::bogus>>`) is
// a USER typo in the bitstring type-spec sub-grammar -- frontdoor.rs parses
// bitstring segments as generic exprs and never validates modifier names, so
// quoted_function.rs is the sole validator. Must surface as a
// parse/bitstring-bad-modifier user diagnostic, not as
// INTERNAL_POST_RESOLUTION_LEFTOVER.
#[test]
fn bitstring_bad_modifier_is_parse_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00555_bitstring_bad_modifier.fz".to_string()),
        text: include_str!("../../fixtures2/00555_bitstring_bad_modifier.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "<<1::bogus>> should fail during bit-spec modifier decoding",
    );
    assert_last_error(
        &capture,
        codes::PARSE_BITSTRING_BAD_MODIFIER.0,
        "unknown bitstring modifier: bogus",
    );
}

// fz-go4.49: a bitstring modifier that parses as a non-atom, non-call literal
// (e.g. a float, `<<1::3.14>>`) is also a USER typo, not an internal-compiler
// shape bug. frontdoor `parse_bitstring_literal` parses the `::` right-hand
// side as a fully generic expr, so a float literal reaches
// apply_bit_spec_modifier's final fallback (previously `QuotedSourceError::new`,
// routed to INTERNAL_POST_RESOLUTION_LEFTOVER) exactly like the unrecognized-
// atom case above. Confirmed the same fallback is also reachable via a list
// literal (`<<1::[1]>>`) and a bare 2-element tuple literal (`<<1::{2,3}>>`,
// which Elixir represents as a raw struct rather than a `{}` call node); the
// float case here is representative of all three.
#[test]
fn bitstring_float_modifier_is_parse_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00556_bitstring_float_modifier.fz".to_string()),
        text: include_str!("../../fixtures2/00556_bitstring_float_modifier.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "<<1::3.14>> should fail during bit-spec modifier decoding",
    );
    assert_last_error(
        &capture,
        codes::PARSE_BITSTRING_BAD_MODIFIER.0,
        "unsupported bitstring modifier value of kind ValueKind(14)",
    );
}

/// A USER coded quoted-source error must carry its source location end to
/// end, not `Span::DUMMY`: `QuotedSourceError` now threads a span from the
/// decode site (`quoted_function.rs`'s bit-spec modifier decode) through to
/// the `emit_surface_read_error` render site (`quoted_expander.rs`). `3.14`
/// is a bare literal in the quoted tree (frontdoor quotes literals without
/// their own span metadata), so the tightest span available is the
/// enclosing `1::3.14` bitstring field -- this asserts that span is real
/// (non-DUMMY) and brackets the `3.14` modifier, not merely non-DUMMY.
#[test]
fn bitstring_float_modifier_error_span_brackets_the_modifier() {
    let tel = ConfiguredTelemetry::new();
    let last_span = Rc::new(RefCell::new(None));
    tel.attach(
        &[],
        Box::new(LastErrorSpan {
            span: last_span.clone(),
        }),
    );
    let mut compiler = Compiler2::new(&tel);
    let source = include_str!("../../fixtures2/00556_bitstring_float_modifier.fz");
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00556_bitstring_float_modifier.fz".to_string()),
        text: source.to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "<<1::3.14>> should fail during bit-spec modifier decoding",
    );

    let span = last_span.borrow().expect("expected a captured diagnostic span");
    assert!(
        !span.is_dummy(),
        "user coded bit-spec modifier error must carry a real span, not DUMMY"
    );

    let modifier_start = source.find("3.14").expect("fixture contains `3.14`") as u32;
    let modifier_end = modifier_start + "3.14".len() as u32;
    assert!(
        span.start <= modifier_start && span.end >= modifier_end,
        "span [{}, {}) must bracket the `3.14` modifier at [{modifier_start}, {modifier_end})",
        span.start,
        span.end,
    );

    // Upper bound: the span must not widen past the `1::3.14` bitstring field.
    // Without this, a regression to a whole-function or whole-`<<>>` span would
    // still satisfy the containment check above. `3.14` is a bare literal
    // (no span meta of its own), so the enclosing `::` field is the tightest
    // bracket available and the span should equal exactly that field.
    let field_start = source.find("1::3.14").expect("fixture contains `1::3.14`") as u32;
    let field_end = field_start + "1::3.14".len() as u32;
    assert!(
        span.start >= field_start && span.end <= field_end,
        "span [{}, {}) must not extend beyond the `1::3.14` field at [{field_start}, {field_end})",
        span.start,
        span.end,
    );
}

// A `size(...)` modifier with a non-int, non-variable argument (`size(1.5)`)
// is the sole USER-reachable trigger of PARSE_BITSTRING_BAD_SIZE from
// `decode_bit_size`: frontdoor parses the `::` right-hand side as a generic
// expr, so `size(1.5)` reaches quoted_function.rs as a call node whose float
// argument is neither int nor variable. This asserts (a) the code is the
// user-facing bad-size code and (b) the span brackets the `size(1.5)` call
// construct TIGHTLY -- unlike a bare-literal modifier, a call-shaped modifier
// carries its own `__fz_span__`, so the error points at `size(1.5)` itself,
// not the wider enclosing bitstring field.
#[test]
fn bitstring_bad_size_error_span_brackets_the_size_modifier() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let last_span = Rc::new(RefCell::new(None));
    tel.attach(
        &[],
        Box::new(LastErrorSpan {
            span: last_span.clone(),
        }),
    );
    let mut compiler = Compiler2::new(&tel);
    let source = include_str!("../../fixtures2/00557_bitstring_bad_size.fz");
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00557_bitstring_bad_size.fz".to_string()),
        text: source.to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "<<1::size(1.5)>> should fail during bit-spec size decoding",
    );
    assert_last_error(
        &capture,
        codes::PARSE_BITSTRING_BAD_SIZE.0,
        "bitstring size expects int or variable, got ValueKind(14)",
    );

    let span = last_span.borrow().expect("expected a captured diagnostic span");
    assert!(
        !span.is_dummy(),
        "user coded bad-size error must carry a real span, not DUMMY"
    );

    // Lower bound: the span brackets the whole `size(1.5)` modifier.
    let modifier_start = source.find("size(1.5)").expect("fixture contains `size(1.5)`") as u32;
    let modifier_end = modifier_start + "size(1.5)".len() as u32;
    assert!(
        span.start <= modifier_start && span.end >= modifier_end,
        "span [{}, {}) must bracket the `size(1.5)` modifier at [{modifier_start}, {modifier_end})",
        span.start,
        span.end,
    );

    // Upper bound: the span must not widen past `size(1.5)` -- it must be the
    // tight call construct, not the enclosing `1::size(1.5)` field or the whole
    // `<<>>`. This is what makes threading node_span (rather than field_span)
    // through the size branch observable.
    assert!(
        span.start >= modifier_start && span.end <= modifier_end,
        "span [{}, {}) must equal the `size(1.5)` modifier at [{modifier_start}, {modifier_end}), not widen past it",
        span.start,
        span.end,
    );
}

/// A malformed `@type` in the SECOND submitted file must surface its
/// `RESOLVE_TYPE_ALIAS` diagnostic pointing at that second file, not at the
/// first. `token_payload::decode_token` used to stamp every decoded token
/// with a hardcoded `SourceId(0)` placeholder code id (only the byte
/// offsets were real); in a single-file compile file 0 IS the only file, so
/// the bug was invisible. Once a second file exists, an error whose tokens
/// were decoded from that second file must carry ITS code id, or the
/// diagnostic renders against the wrong source text entirely.
#[test]
fn malformed_type_alias_in_second_file_points_at_that_files_span() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let last_span = Rc::new(RefCell::new(None));
    tel.attach(
        &[],
        Box::new(LastErrorSpan {
            span: last_span.clone(),
        }),
    );
    let mut compiler = Compiler2::new(&tel);

    compiler.submit_code(CodeSubmission {
        name: Some("first.fz".to_string()),
        text: "fn main(), do: 1\n".to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "the first, well-formed file should resolve on its own",
    );

    // The second file arrives once a root is already active, so it is
    // auto-scoped (fz-f98.14.5) -- exercising exactly the multi-file shape
    // this bug hid behind: a real second `SourceId` whose decoded tokens
    // must carry their own code id, not file 0's.
    let second_source = "@type bad :: ,\n";
    let second_code = compiler.submit_code(CodeSubmission {
        name: Some("second.fz".to_string()),
        text: second_source.to_string(),
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "the malformed `@type` in the second file should fail to parse",
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("expected a compiler diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::RESOLVE_TYPE_ALIAS.0,
        "a malformed `@type` body should surface as RESOLVE_TYPE_ALIAS"
    );

    let span = last_span.borrow().expect("expected a captured diagnostic span");
    assert_eq!(
        span.code_id,
        crate::source::Id(second_code.as_u32()),
        "the diagnostic span must point at the SECOND file's source id, not file 0's"
    );

    let comma_offset = second_source.find(',').expect("fixture contains `,`") as u32;
    assert!(
        span.start <= comma_offset && span.end > comma_offset,
        "span [{}, {}) must bracket the malformed `,` at offset {comma_offset} inside the second file",
        span.start,
        span.end,
    );
}

// Ported from src/frontend/resolve_test.rs: @spec with no fn following it in the module is a parse-time error
#[test]
fn spec_without_following_fn_is_a_source_surface_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00088_spec_without_fn.fz".to_string()),
        text: include_str!("../../fixtures2/00088_spec_without_fn.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "lonely".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    // fz-rh2.17.5.6.4: the dangling @spec is rejected where it dangles,
    // instead of silently dropping and resurfacing later as a baffling
    // unknown-export diagnostic for the function it described.
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "a dangling @spec is a source-surface error",
    );
    assert_last_error(
        &capture,
        codes::PARSE_DANGLING_FUNCTION_ATTR.0,
        "`@spec` does not attach to any function definition: function attributes must be followed by their function's clauses",
    );
}

// Ported from src/frontend/resolve_test.rs: multiple @spec overloads on one fn are all attached in declaration order
#[test]
fn multiple_spec_overloads_attach_in_order() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00089_spec_multiple_overloads.fz".to_string()),
        text: include_str!("../../fixtures2/00089_spec_multiple_overloads.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "add1".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "two @spec overloads on add1 attach in declaration order",
    );
    // TODO: assert specs.len()==2, both named add1, param_body_tokens.len()==1 each
}

// Ported from src/frontend/resolve_test.rs: @spec referencing an unknown type name errors at resolve time
#[test]
fn spec_unknown_type_is_resolve_error() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00090_spec_unknown_type.fz".to_string()),
        text: include_str!("../../fixtures2/00090_spec_unknown_type.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "add1".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    // A spec that names an unknown type is the USER's error, reported as a
    // resolve diagnostic — never a fatal: the diagnosed spec constrains
    // nothing and the program still compiles.
    assert_resolved(compiler.drive(), "@spec with unknown_thing type errors at resolve time");
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("the unknown spec type must surface as a resolve diagnostic");
    assert!(
        metadata_str(&diagnostic, "message").contains("unknown type name `unknown_thing`"),
        "diagnostic names the unknown type: {}",
        metadata_str(&diagnostic, "message"),
    );
}

// Ported from src/frontend/resolve_test.rs: @spec type names resolve against local @type aliases in the module
#[test]
fn spec_resolves_against_local_type_aliases() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00091_spec_resolves_local_types.fz".to_string()),
        text: include_str!("../../fixtures2/00091_spec_resolves_local_types.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "lookup".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "@spec lookup(id)::id resolves id -> integer from @type",
    );
    // TODO: assert spec param[0]==integer, result==integer (via @type id :: integer)
}

// Ported from src/frontend/resolve_test.rs: top-level @type is attached as a program attribute alongside fns
#[test]
fn top_level_type_alias_is_program_attribute() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00092_type_alias_top_level.fz".to_string()),
        text: include_str!("../../fixtures2/00092_type_alias_top_level.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "top-level @type id is retained as a root program attr",
    );
    // TODO: assert program.attrs contains TypeAlias { name: "id" }
}

// Ported from src/frontend/resolve_test.rs: outer module's sibling call is not shadowed by inner module's same-named fn
#[test]
fn outer_sibling_call_not_shadowed_by_inner_fn() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00093_outer_sibling_not_shadowed.fz".to_string()),
        text: include_str!("../../fixtures2/00093_outer_sibling_not_shadowed.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("A".to_string()),
        name: "caller".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "A.caller resolves f to A.f not A.B.f");
    // TODO: assert A.f and A.B.f both exist; A.caller callee is A.f
}

// Ported from src/frontend/resolve_test.rs: defprotocol and defimpl register protocol, impl, and domain type facts
#[test]
fn protocol_registry_records_protocol_impl_and_domain_types() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00094_protocol_impl_registry.fz".to_string()),
        text: include_str!("../../fixtures2/00094_protocol_impl_registry.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("Consumer".to_string()),
        name: "use".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "defprotocol/defimpl register Enumerable protocol and List impl",
    );
    // TODO: assert protocol_registry has Enumerable; impl for List has reduce/3; Enumerable.t != any
}

// Ported from src/frontend/resolve_test.rs: protocol domain type Enumerable.t(integer) narrows to list(integer) subtype
#[test]
fn protocol_domain_type_refines_with_concrete_element() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00095_protocol_domain_refines.fz".to_string()),
        text: include_str!("../../fixtures2/00095_protocol_domain_refines.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("Consumer".to_string()),
        name: "use".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "Enumerable.t(integer) narrows to list(integer) subtype",
    );
    // TODO: assert list(integer) <: Enumerable.t(integer); list(atom) not <: Enumerable.t(integer)
}

// Ported from src/frontend/resolve_test.rs: defimpl that omits a declared protocol callback is a compile-time error
#[test]
fn protocol_impl_missing_callback_is_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00096_protocol_impl_missing_callback.fz".to_string()),
        text: include_str!("../../fixtures2/00096_protocol_impl_missing_callback.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("P".to_string()),
        name: "__info__".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "defimpl missing each/1 callback produces RESOLVE_PROTOCOL error",
    );
    // TODO: assert RESOLVE_PROTOCOL diagnostic: message contains "missing callback `each/1`"
}

// Ported from src/frontend/resolve_test.rs: two defimpl blocks for same protocol and type is a compile-time error
#[test]
fn duplicate_protocol_impls_are_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00097_protocol_duplicate_impl.fz".to_string()),
        text: include_str!("../../fixtures2/00097_protocol_duplicate_impl.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("P".to_string()),
        name: "__info__".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "two defimpl P for List produces RESOLVE_PROTOCOL error",
    );
    // TODO: assert RESOLVE_PROTOCOL: "already has an implementation"; secondaries[0] has "first implementation"
}

// Ported from src/frontend/resolve_test.rs: callback at wrong arity produces arity-mismatch error not missing-callback
#[test]
fn protocol_impl_wrong_arity_is_mismatch_not_missing() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00098_protocol_impl_wrong_arity.fz".to_string()),
        text: include_str!("../../fixtures2/00098_protocol_impl_wrong_arity.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("P".to_string()),
        name: "__info__".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "each/2 impl for each/1 protocol is arity mismatch not missing",
    );
    // TODO: assert RESOLVE_PROTOCOL: mentions "at arity 2" and "`each/1`"; not "missing callback"
}

// Ported from src/frontend/resolve_test.rs: protocol callback with multiple @spec overloads all survive validation
#[test]
fn protocol_callback_multiple_spec_overloads_pass_validation() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00099_protocol_overload_specs.fz".to_string()),
        text: include_str!("../../fixtures2/00099_protocol_overload_specs.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("P".to_string()),
        name: "__info__".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "protocol pick with 2 @spec overloads survives impl validation",
    );
    // TODO: assert callback.specs.len()==2; impl callback_specs[("pick",1)].len()==2
}

// Ported from src/frontend/resolve_test.rs: impl overload not matching any declared protocol spec is rejected
#[test]
fn protocol_impl_uncovered_overload_is_error() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00100_protocol_overload_uncovered.fz".to_string()),
        text: include_str!("../../fixtures2/00100_protocol_overload_uncovered.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: Some("P".to_string()),
        name: "__info__".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(
        compiler.drive(),
        "impl @spec pick(float) not in protocol spec set is rejected",
    );
    // TODO: assert RESOLVE_PROTOCOL: "callback `pick/1` parameter 1 is incompatible"
}
