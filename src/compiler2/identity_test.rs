use super::quoted_surface::ScopeSurface;
use super::{
    CodeMap, CodeState, FunctionDef, FunctionMap, FunctionState, ModuleId, ModuleMap, ModuleState, NamespaceStore,
    NamespaceSymbol, QuotedCodeSource, QuotedSourceRoot, parse_quoted_program,
};
use crate::ast::{Expr, FnClause, Spanned, TypeExprBody};
use crate::function_surface::FunctionSurface;
use crate::telemetry::ConfiguredTelemetry;

fn quoted_source(source_name: &str, text: &str) -> QuotedSourceRoot {
    let tel = ConfiguredTelemetry::new();
    parse_quoted_program(source_name, text, &tel).expect("quoted parse should succeed")
}

fn function_surface(name: &str) -> FunctionSurface {
    FunctionSurface {
        name: name.to_string(),
        name_span: crate::compiler::source::Span::DUMMY,
        clauses: vec![FnClause {
            params: vec![],
            param_annotations: vec![],
            guard: None,
            body: Spanned::dummy(Expr::Int(42)),
            span: crate::compiler::source::Span::DUMMY,
        }],
        is_macro: false,
        extern_abi: None,
        extern_param_tokens: vec![],
        extern_ret_tokens: TypeExprBody(vec![]),
        extern_constraints: vec![],
        variadic: false,
        attrs: vec![],
        span: crate::compiler::source::Span::DUMMY,
    }
}

fn empty_scope_surface() -> ScopeSurface {
    ScopeSurface {
        attrs: Vec::new(),
        forms: Vec::new(),
    }
}

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
    let math_revision = modules.define(math_def, code_id, namespace, Vec::new(), 0);
    assert_eq!(
        math_ref, math_def,
        "module definition should fill the referenced placeholder"
    );
    let same_math_revision = modules.define(math_def, code_id, namespace, Vec::new(), math_revision);
    assert_eq!(
        same_math_revision, math_revision,
        "replaying the same module definition should not bump the revision"
    );
    assert_eq!(modules.name(math_def), Some("Math"));
    let module = modules.get(math_def);
    match &module.state {
        ModuleState::Defined { surface, .. } => {
            assert_eq!(surface.codes, vec![code_id]);
            assert_eq!(surface.namespace, namespaces.prelude_head());
        }
        other => panic!("module should promote from placeholder to defined, got {other:?}"),
    }

    let scoped_ref = modules.reference_named("Scoped");
    let scoped_source = quoted_source("scoped.fz", "defmodule Scoped do\nend\n");
    let indexed_revision = modules.index_body(
        scoped_ref,
        code_id,
        ModuleId::GLOBAL,
        "Scoped".to_string(),
        scoped_source.clone(),
        empty_scope_surface(),
        0,
    );
    let same_indexed_revision = modules.index_body(
        scoped_ref,
        code_id,
        ModuleId::GLOBAL,
        "Scoped".to_string(),
        scoped_source,
        empty_scope_surface(),
        indexed_revision,
    );
    assert_eq!(
        same_indexed_revision, indexed_revision,
        "replaying the same module index should not bump the revision"
    );
    let scoped_revision = modules.scope(scoped_ref, namespace, 0);
    let same_scoped_revision = modules.scope(scoped_ref, namespace, scoped_revision);
    assert_eq!(
        same_scoped_revision, scoped_revision,
        "replaying the same module scope should not bump the revision"
    );

    let add_ref = functions.reference(math_def, "add", 2);
    let add_def = add_ref;
    let add_ast = function_surface("Math.add");
    let add_source = quoted_source("math.fz", "fn add(x, y), do: 42\n");
    let add_revision = functions.define(
        add_def,
        FunctionDef {
            code: code_id,
            owner_module: math_def,
            namespace,
            capture_params: Vec::new(),
            source: add_source.clone(),
            surface: add_ast.clone(),
        },
        0,
    );
    let same_add_revision = functions.define(
        add_def,
        FunctionDef {
            code: code_id,
            owner_module: math_def,
            namespace,
            capture_params: Vec::new(),
            source: add_source,
            surface: add_ast.clone(),
        },
        add_revision,
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
    match &function.state {
        FunctionState::Defined { def } => {
            assert_eq!(def.code, code_id);
            assert_eq!(def.surface.name, "Math.add");
        }
        other => panic!("function should promote from placeholder to defined, got {other:?}"),
    }

    let code_slot = code.get(code_id);
    assert!(
        matches!(code_slot.state, CodeState::Pending),
        "new code should remain pending until indexing runs"
    );
    let code_source = quoted_source("math.fz", "fn add(x, y), do: x + y\n");
    let indexed_code_revision = code.index(
        code_id,
        QuotedCodeSource {
            quoted: code_source.clone(),
            surface: empty_scope_surface(),
        },
        0,
    );
    let same_indexed_code_revision = code.index(
        code_id,
        QuotedCodeSource {
            quoted: code_source,
            surface: empty_scope_surface(),
        },
        indexed_code_revision,
    );
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

#[test]
fn compiler2_code_index_revisions_ignore_quoted_heap_identity_when_semantics_match() {
    let mut code = CodeMap::new();
    let code_id = code.define(Some("math.fz".to_string()), "fn add(x, y), do: x + y\n".to_string());

    let first = quoted_source("math.fz", "fn add(x, y), do: x + y\n");
    let second = quoted_source("math.fz", "fn add(x, y), do: x + y\n");
    assert_ne!(
        first.key(),
        second.key(),
        "fresh quoted parses should prove this test is exercising cross-heap equality rather than root reuse",
    );

    let first_revision = code.index(
        code_id,
        QuotedCodeSource {
            quoted: first,
            surface: empty_scope_surface(),
        },
        0,
    );
    let second_revision = code.index(
        code_id,
        QuotedCodeSource {
            quoted: second,
            surface: empty_scope_surface(),
        },
        first_revision,
    );

    assert_eq!(
        second_revision, first_revision,
        "code indexing should key revisions on semantic quoted-source equality, not transport identity",
    );
}

#[test]
fn compiler2_function_definition_revisions_track_semantic_content_not_transport() {
    let mut functions = FunctionMap::new();
    let mut code = CodeMap::new();
    let namespaces = NamespaceStore::new();
    let code_id = code.define(Some("math.fz".to_string()), "fn add(x, y), do: 42\n".to_string());
    let namespace = namespaces.prelude_head();
    let function = functions.reference(ModuleId::GLOBAL, "add", 2);
    let def_ast = function_surface("add");
    let first = quoted_source("math.fz", "fn add(x, y), do: 42\n");
    let second = quoted_source("math.fz", "fn add(x, y), do: 42\n");
    let third = quoted_source("math.fz", "fn add(x, y), do: 43\n");
    assert_ne!(
        first.key(),
        second.key(),
        "fresh quoted parses should prove this test is exercising a replacement source root",
    );

    let first_revision = functions.define(
        function,
        FunctionDef {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            source: first,
            surface: def_ast.clone(),
        },
        0,
    );
    let second_revision = functions.define(
        function,
        FunctionDef {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            source: second,
            surface: def_ast.clone(),
        },
        first_revision,
    );
    let third_revision = functions.define(
        function,
        FunctionDef {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            source: third,
            surface: def_ast,
        },
        second_revision,
    );

    assert_eq!(
        second_revision, first_revision,
        "re-defining with semantically identical source must not bump the revision — transport identity is not content",
    );
    assert_eq!(
        third_revision,
        first_revision + 1,
        "a real body change (42 -> 43) must bump the function definition revision",
    );
}
