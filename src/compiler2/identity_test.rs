use super::{
    CodeMap, CodeState, FunctionDef, FunctionMap, FunctionState, ModuleId, ModuleMap, ModuleState, NamespaceStore,
    NamespaceSymbol,
};

#[test]
fn compiler2_identity_maps_promote_placeholders_and_preserve_reverse_lookup() {
    let mut code = CodeMap::new();
    let namespaces = NamespaceStore::new();
    let mut modules = ModuleMap::new();
    let mut functions = FunctionMap::new();

    let code_id = code.define(Some("math.fz".to_string()), "fn add(x, y), do: x + y\n".to_string());
    let namespace = namespaces.prelude_head();

    let math_ref = modules.reference_named("Math");
    let math_def = math_ref;
    let math_revision = modules.define(math_def, code_id, namespace, Vec::new());
    assert_eq!(
        math_ref, math_def,
        "module definition should fill the referenced placeholder"
    );
    let same_math_revision = modules.define(math_def, code_id, namespace, Vec::new());
    assert_eq!(
        same_math_revision, math_revision,
        "replaying the same module definition should not bump the revision"
    );
    assert_eq!(modules.name(math_def), Some("Math"));
    let module = modules.get(math_def);
    assert_eq!(module.revision, math_revision);
    match &module.state {
        ModuleState::Defined { surface, .. } => {
            assert_eq!(surface.codes, vec![code_id]);
            assert_eq!(surface.namespace, namespaces.prelude_head());
        }
        other => panic!("module should promote from placeholder to defined, got {other:?}"),
    }

    let scoped_ref = modules.reference_named("Scoped");
    let indexed_revision = modules.index(
        scoped_ref,
        code_id,
        ModuleId::GLOBAL,
        "Scoped".to_string(),
        Vec::new(),
        Vec::new(),
    );
    let same_indexed_revision = modules.index(
        scoped_ref,
        code_id,
        ModuleId::GLOBAL,
        "Scoped".to_string(),
        Vec::new(),
        Vec::new(),
    );
    assert_eq!(
        same_indexed_revision, indexed_revision,
        "replaying the same module index should not bump the revision"
    );
    let scoped_revision = modules.scope(scoped_ref, namespace);
    let same_scoped_revision = modules.scope(scoped_ref, namespace);
    assert_eq!(
        same_scoped_revision, scoped_revision,
        "replaying the same module scope should not bump the revision"
    );

    let add_ref = functions.reference(math_def, "add", 2);
    let add_def = add_ref;
    let add_ast = crate::ast::FnDef {
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
    };
    let add_revision = functions.define(
        add_def,
        FunctionDef {
            code: code_id,
            namespace,
            ast: add_ast.clone(),
        },
    );
    let same_add_revision = functions.define(
        add_def,
        FunctionDef {
            code: code_id,
            namespace,
            ast: add_ast.clone(),
        },
    );
    assert_eq!(
        same_add_revision, add_revision,
        "replaying the same function definition should not bump the revision"
    );
    assert_eq!(
        add_ref, add_def,
        "function definition should fill the referenced placeholder"
    );
    let add_ref_data = functions.reference_for(add_def);
    assert_eq!(add_ref_data.module, math_def);
    assert_eq!(add_ref_data.name, "add");
    assert_eq!(add_ref_data.arity, 2);
    let generated = functions.reference_generated(
        add_def,
        math_def,
        crate::compiler::source::Span::new(crate::compiler::source::Id(code_id.as_u32()), 5, 19),
        1,
    );
    let same_generated = functions.reference_generated(
        add_def,
        math_def,
        crate::compiler::source::Span::new(crate::compiler::source::Id(code_id.as_u32()), 5, 19),
        1,
    );
    assert_eq!(
        generated, same_generated,
        "generated function identity should be stable per owner and source site"
    );
    let function = functions.get(add_def);
    assert_eq!(function.revision, add_revision);
    match &function.state {
        FunctionState::Defined { def } => {
            assert_eq!(def.code, code_id);
            assert_eq!(def.ast.name, "Math.add");
        }
        other => panic!("function should promote from placeholder to defined, got {other:?}"),
    }

    let code_slot = code.get(code_id);
    assert!(
        matches!(code_slot.state, CodeState::Pending),
        "new code should remain pending until indexing runs"
    );
    let indexed_code_revision = code.index(code_id, Vec::new());
    let same_indexed_code_revision = code.index(code_id, Vec::new());
    assert_eq!(
        same_indexed_code_revision, indexed_code_revision,
        "replaying the same code index should not bump the revision"
    );

    let mut namespaces = namespaces;
    let head = namespaces.bind(namespace, "add", NamespaceSymbol::Function(add_def));
    assert_eq!(
        namespaces.lookup(head, "add"),
        Some(&NamespaceSymbol::Function(add_def)),
        "namespace lookup should preserve grouped function bindings"
    );
}
