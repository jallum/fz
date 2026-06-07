use super::{CodeState, FunctionDef, FunctionState, ModuleState, NamespaceSymbol, RootState, World};

#[test]
fn compiler2_identity_maps_promote_placeholders_and_preserve_reverse_lookup() {
    let mut world = World::new();
    let code_id = world
        .code_mut()
        .define(Some("math.fz".to_string()), "fn add(x, y), do: x + y\n".to_string());
    let namespace = world.namespaces().prelude_head();

    let math_ref = world.modules_mut().reference_named("Math");
    let math_def = math_ref;
    let math_revision = world.modules_mut().define(math_def, code_id, namespace);
    assert_eq!(
        math_ref, math_def,
        "module definition should fill the referenced placeholder"
    );
    assert_eq!(world.modules().name(math_def), Some("Math"));
    let module = world.modules().get(math_def).expect("defined module");
    assert_eq!(module.revision(), math_revision);
    match module.state() {
        ModuleState::Defined { codes, namespace } => {
            assert_eq!(codes, &vec![code_id]);
            assert_eq!(*namespace, world.namespaces().prelude_head());
        }
        other => panic!("module should promote from placeholder to defined, got {other:?}"),
    }

    let add_ref = world.functions_mut().reference(Some(math_def), "add", 2);
    let add_def = add_ref;
    let add_revision = world.functions_mut().define(
        add_def,
        FunctionDef::new(
            code_id,
            namespace,
            crate::ast::FnDef {
                name: "Math.add".to_string(),
                name_span: crate::compiler::source::Span::DUMMY,
                clauses: vec![crate::ast::FnClause {
                    params: vec![],
                    param_annotations: vec![],
                    guard: None,
                    body: crate::ast::Spanned::dummy(crate::ast::Expr::Int(42)),
                    span: crate::compiler::source::Span::DUMMY,
                }],
                is_macro: false,
                is_private: false,
                extern_abi: None,
                extern_params: vec![],
                extern_ret_tokens: crate::ast::TypeExprBody(vec![]),
                variadic: false,
                attrs: vec![],
                span: crate::compiler::source::Span::DUMMY,
            },
        ),
    );
    assert_eq!(
        add_ref, add_def,
        "function definition should fill the referenced placeholder"
    );
    let add_ref_data = world.functions().reference_for(add_def).expect("function ref");
    assert_eq!(add_ref_data.module, Some(math_def));
    assert_eq!(add_ref_data.name, "add");
    assert_eq!(add_ref_data.arity, 2);
    let function = world.functions().get(add_def).expect("defined function");
    assert_eq!(function.revision(), add_revision);
    match function.state() {
        FunctionState::Defined { def } => {
            assert_eq!(def.code(), code_id);
            assert_eq!(def.ast().name, "Math.add");
        }
        other => panic!("function should promote from placeholder to defined, got {other:?}"),
    }

    let code = world.code().get(code_id).expect("defined code");
    assert_eq!(code.state(), &CodeState::Pending);

    let repl_ref = world.roots_mut().reference_named("repl");
    let repl_def = world.roots_mut().define_named("repl");
    assert_eq!(
        repl_ref, repl_def,
        "root definition should fill the referenced placeholder"
    );
    assert_eq!(world.roots().name(repl_def), Some("repl"));
    assert_eq!(
        world.roots().get(repl_def).map(|root| root.state()),
        Some(&RootState::Defined),
        "root should promote from placeholder to defined"
    );

    let head = world
        .namespaces_mut()
        .bind(namespace, "add", NamespaceSymbol::Functions(vec![add_def]));
    assert_eq!(
        world.namespaces().lookup(head, "add"),
        Some(&NamespaceSymbol::Functions(vec![add_def])),
        "namespace lookup should preserve grouped function bindings"
    );
}
