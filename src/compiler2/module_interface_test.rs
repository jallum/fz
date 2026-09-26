use super::super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use super::*;
use crate::fz_ir::{DirectCallTarget, Term};
use crate::telemetry::ConfiguredTelemetry;

fn callable(id: u32, name: &str, arity: usize, kind: InterfaceCallableKind) -> ModuleInterfaceCallable {
    ModuleInterfaceCallable {
        function: FunctionId::from_fn_id(crate::fz_ir::FnId(id)),
        reference: FunctionRef {
            module: ModuleId::GLOBAL,
            denotation: std::sync::Arc::new(super::super::identity::FunctionDenotation {
                origin: super::super::identity::FunctionOrigin::Named {
                    module: None,
                    name: name.to_string(),
                },
                arity,
            }),
        },
        kind,
        variadic: false,
    }
}

#[test]
fn module_interface_queries_by_callable_kind() {
    let interface = ModuleInterface::new(vec![
        callable(1, "add", 2, InterfaceCallableKind::PublicFunction),
        callable(2, "defthing", 1, InterfaceCallableKind::Macro),
    ]);

    assert_eq!(
        interface.public_function_with_name_arity("add", 2),
        Some(FunctionId::from_fn_id(crate::fz_ir::FnId(1)))
    );
    assert_eq!(
        interface.macro_with_name_arity("defthing", 1),
        Some(FunctionId::from_fn_id(crate::fz_ir::FnId(2)))
    );
    assert_eq!(interface.public_function_with_name_arity("defthing", 1), None);
    assert_eq!(interface.macro_with_name_arity("add", 2), None);
}

#[test]
fn module_interface_filters_export_sets_by_kind_and_except() {
    let interface = ModuleInterface::new(vec![
        callable(1, "add", 2, InterfaceCallableKind::PublicFunction),
        callable(2, "sub", 2, InterfaceCallableKind::PublicFunction),
        callable(3, "defthing", 1, InterfaceCallableKind::Macro),
    ]);

    let ReadyOrPending::Ready(functions) = interface.exported_functions(Some(&[("sub".to_string(), 2)])) else {
        panic!("defined interfaces should return ready callable sets");
    };
    assert_eq!(functions.len(), 1);
    assert!(functions[0].matches_name_arity("add", 2));

    let ReadyOrPending::Ready(macros) = interface.exported_macros(None) else {
        panic!("defined interfaces should return ready callable sets");
    };
    assert_eq!(macros.len(), 1);
    assert!(macros[0].matches_name_arity("defthing", 1));
}

#[test]
fn module_interface_expectations_preserve_requested_kind() {
    let mut interface = ModuleInterface::default();
    interface.record_expectation(InterfaceExpectation {
        name: "add".to_string(),
        arity: 2,
        kind: InterfaceCallableKind::PublicFunction,
        requester: Some(InterfaceRequester {
            owner: SourceOwner::for_test(0),
            module: ModuleId::GLOBAL,
            span: Span::DUMMY,
        }),
    });
    interface.record_expectation(InterfaceExpectation {
        name: "add".to_string(),
        arity: 2,
        kind: InterfaceCallableKind::Macro,
        requester: Some(InterfaceRequester {
            owner: SourceOwner::for_test(0),
            module: ModuleId::GLOBAL,
            span: Span::DUMMY,
        }),
    });

    assert_eq!(interface.expectations().len(), 2);
    assert_ne!(interface.expectations()[0].kind, interface.expectations()[1].kind);
}

// Ported from src/frontend/resolve_test.rs: import resolves against provider interface without source body
#[test]
fn import_from_external_interface_carries_provider_boundary_call_without_provider_body() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    let math = compiler
        .world_mut()
        .reference_module(crate::modules::identity::ModuleName::parse_dotted("Math").unwrap());
    let add = compiler.world_mut().reference_function(math, "add".to_string(), 2);
    let reference = compiler.world().function_ref(add).clone();
    compiler.submit_module_interface(
        "Math".to_string(),
        ModuleInterface::new(vec![ModuleInterfaceCallable {
            function: add,
            reference,
            kind: InterfaceCallableKind::PublicFunction,
            variadic: false,
        }]),
    );
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/00069_import_from_external_interface.fz".to_string()),
        text: include_str!("../../fixtures/00069_import_from_external_interface.fz").to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: Some("User".to_string()),
        name: "run".to_string(),
        arity: 2,
        need: ExecutableNeed::Value,
    });
    let (_, native) = compiler
        .drive_root_to_dump_stage(root, super::super::dump::DumpStage::Native)
        .expect("interface-only provider call should settle");
    assert!(
        compiler.world().module_defined_revision(math).is_none(),
        "external interface imports should not require a provider module body",
    );
    assert!(
        compiler.world().module_interface_revision(math).is_some(),
        "external interface imports should publish the provider interface fact",
    );
    let program = native.expect("native dump stage must return its native product");
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
