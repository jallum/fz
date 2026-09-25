use super::*;

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
