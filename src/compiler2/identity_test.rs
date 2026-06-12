use super::quoted_surface::ScopeSurface;
use super::{
    CodeMap, CodeState, FunctionMap, FunctionSource, FunctionState, Horizon, ModuleId, ModuleMap, ModuleState,
    NamespaceStore, NamespaceSymbol, QuotedCodeSource, QuotedSourceRoot, parse_quoted_program,
};
use crate::ast::{Expr, FnClause, Spanned, TypeExprBody};
use crate::function_surface::FunctionSurface;
use crate::telemetry::ConfiguredTelemetry;

fn quoted_source(source_name: &str, text: &str) -> QuotedSourceRoot {
    let tel = ConfiguredTelemetry::new();
    parse_quoted_program(source_name, text, &tel).expect("quoted parse should succeed")
}

fn function_surface_with_int(name: &str, value: i64) -> FunctionSurface {
    FunctionSurface {
        name: name.to_string(),
        name_span: crate::compiler::source::Span::DUMMY,
        clauses: vec![FnClause {
            params: vec![],
            param_annotations: vec![],
            guard: None,
            body: Spanned::dummy(Expr::Int(value)),
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

fn function_surface(name: &str) -> FunctionSurface {
    function_surface_with_int(name, 42)
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
    let math_changed = modules.define(
        math_def,
        code_id,
        namespace,
        crate::compiler2::ModuleInterface::default(),
    );
    assert_eq!(
        math_ref, math_def,
        "module definition should fill the referenced placeholder"
    );
    assert!(math_changed, "first module define should be a change");
    let same_math_changed = modules.define(
        math_def,
        code_id,
        namespace,
        crate::compiler2::ModuleInterface::default(),
    );
    assert!(
        !same_math_changed,
        "replaying the same module definition should not signal a change"
    );
    assert_eq!(modules.name(math_def), Some("Math"));
    let module = modules.get(math_def);
    match module {
        ModuleState::Defined { base, interface, .. } => {
            assert_eq!(*base, namespaces.prelude_head());
            assert!(interface.callables().is_empty());
        }
        other => panic!("module should promote from placeholder to defined, got {other:?}"),
    }

    let scoped_ref = modules.reference_named("Scoped");
    let scoped_source = quoted_source("scoped.fz", "defmodule Scoped do\nend\n");
    let indexed_changed = modules.index_body(
        scoped_ref,
        code_id,
        ModuleId::GLOBAL,
        "Scoped".to_string(),
        scoped_source.clone(),
        empty_scope_surface(),
    );
    let same_indexed_changed = modules.index_body(
        scoped_ref,
        code_id,
        ModuleId::GLOBAL,
        "Scoped".to_string(),
        scoped_source,
        empty_scope_surface(),
    );
    assert!(indexed_changed, "first module index_body should be a change");
    assert!(
        !same_indexed_changed,
        "replaying the same module index should not signal a change"
    );
    let scoped_changed = modules.scope(scoped_ref, namespace);
    let same_scoped_changed = modules.scope(scoped_ref, namespace);
    assert!(scoped_changed, "first module scope should be a change");
    assert!(
        !same_scoped_changed,
        "replaying the same module scope should not signal a change"
    );

    let add_ref = functions.reference(math_def, "add", 2);
    let add_def = add_ref;
    let add_ast = function_surface("Math.add");
    let add_source = quoted_source("math.fz", "fn add(x, y), do: 42\n");
    let add_changed = functions.define(
        add_def,
        FunctionSource {
            code: code_id,
            owner_module: math_def,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: add_source.clone(),
        },
        FunctionSource {
            code: code_id,
            owner_module: math_def,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: quoted_source("math.fz", "fn add(x, y), do: 42\n"),
        },
        add_ast.clone(),
    );
    let same_add_changed = functions.define(
        add_def,
        FunctionSource {
            code: code_id,
            owner_module: math_def,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: add_source,
        },
        FunctionSource {
            code: code_id,
            owner_module: math_def,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: quoted_source("math.fz", "fn add(x, y), do: 42\n"),
        },
        add_ast,
    );
    assert!(add_changed, "first function define should be a change");
    assert!(
        !same_add_changed,
        "replaying the same function definition should not signal a change"
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
    match function {
        FunctionState::Defined { source, surface, .. } => {
            assert_eq!(source.code, code_id);
            assert_eq!(surface.name, "Math.add");
        }
        other => panic!("function should promote from placeholder to defined, got {other:?}"),
    }

    assert!(
        matches!(code.get(code_id), CodeState::Pending),
        "new code should remain pending until indexing runs"
    );
    let code_source = quoted_source("math.fz", "fn add(x, y), do: x + y\n");
    let indexed_code_changed = code.index(
        code_id,
        QuotedCodeSource {
            quoted: code_source.clone(),
            surface: empty_scope_surface(),
        },
    );
    let same_indexed_code_changed = code.index(
        code_id,
        QuotedCodeSource {
            quoted: code_source,
            surface: empty_scope_surface(),
        },
    );
    assert!(indexed_code_changed, "first code index should be a change");
    assert!(
        !same_indexed_code_changed,
        "replaying the same code index should not signal a change"
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

    let first_changed = code.index(
        code_id,
        QuotedCodeSource {
            quoted: first,
            surface: empty_scope_surface(),
        },
    );
    let second_changed = code.index(
        code_id,
        QuotedCodeSource {
            quoted: second,
            surface: empty_scope_surface(),
        },
    );

    assert!(first_changed, "first index should be a change");
    assert!(
        !second_changed,
        "code indexing should key on semantic quoted-source equality, not transport identity",
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

    let first_changed = functions.define(
        function,
        FunctionSource {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: first,
        },
        FunctionSource {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: quoted_source("math.fz", "fn add(x, y), do: 42\n"),
        },
        def_ast.clone(),
    );
    let second_changed = functions.define(
        function,
        FunctionSource {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: second,
        },
        FunctionSource {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: quoted_source("math.fz", "fn add(x, y), do: 42\n"),
        },
        def_ast.clone(),
    );
    let third_changed = functions.define(
        function,
        FunctionSource {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: third,
        },
        FunctionSource {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: quoted_source("math.fz", "fn add(x, y), do: 43\n"),
        },
        def_ast,
    );

    assert!(first_changed, "first define should be a change");
    assert!(
        !second_changed,
        "re-defining with semantically identical source must not signal a change — transport identity is not content",
    );
    assert!(third_changed, "a real body change (42 -> 43) must signal a change",);
}

#[test]
fn compiler2_re_noting_a_defined_function_preserves_the_defined_state() {
    let mut functions = FunctionMap::new();
    let mut code = CodeMap::new();
    let namespaces = NamespaceStore::new();
    let code_id = code.define(Some("math.fz".to_string()), "fn add(), do: 42\n".to_string());
    let namespace = namespaces.prelude_head();
    let function = functions.reference(ModuleId::GLOBAL, "add", 0);
    let surface = function_surface("add");
    let first = quoted_source("math.fz", "fn add(), do: 42\n");
    let second = quoted_source("math.fz", "fn add(), do: 42\n");

    let defined_changed = functions.define(
        function,
        FunctionSource {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: first,
        },
        FunctionSource {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: quoted_source("math.fz", "fn add(), do: 42\n"),
        },
        surface.clone(),
    );
    assert!(defined_changed, "first define should be a change");

    let noted_changed = functions.note(
        function,
        FunctionSource {
            code: code_id,
            owner_module: ModuleId::GLOBAL,
            namespace,
            capture_params: Vec::new(),
            required_remote_macros: Vec::new(),
            variadic: false,
            source: second,
        },
    );
    assert!(
        !noted_changed,
        "re-noting semantically identical source must not manufacture a change"
    );
    match functions.get(function) {
        FunctionState::Defined {
            source, surface: kept, ..
        } => {
            assert_eq!(
                kept.name, surface.name,
                "the richer defined surface should stay in place"
            );
            assert!(
                source
                    .source
                    .semantically_eq(&quoted_source("math.fz", "fn add(), do: 42\n"), Horizon::Full),
                "the noted source should still refresh to the incoming source content"
            );
        }
        other => panic!("re-noting a defined function must preserve the defined state, got {other:?}"),
    }
}

#[test]
fn compiler2_define_function_updates_a_re_noted_surface_when_expansion_changes() {
    let mut functions = FunctionMap::new();
    let mut code = CodeMap::new();
    let namespaces = NamespaceStore::new();
    let code_id = code.define(Some("math.fz".to_string()), "fn add(), do: 42\n".to_string());
    let namespace = namespaces.prelude_head();
    let function = functions.reference(ModuleId::GLOBAL, "add", 0);
    let first = quoted_source("math.fz", "fn add(), do: 42\n");
    let second = quoted_source("math.fz", "fn add(), do: 43\n");

    assert!(
        functions.define(
            function,
            FunctionSource {
                code: code_id,
                owner_module: ModuleId::GLOBAL,
                namespace,
                capture_params: Vec::new(),
                required_remote_macros: Vec::new(),
                variadic: false,
                source: first.clone(),
            },
            FunctionSource {
                code: code_id,
                owner_module: ModuleId::GLOBAL,
                namespace,
                capture_params: Vec::new(),
                required_remote_macros: Vec::new(),
                variadic: false,
                source: first,
            },
            function_surface_with_int("add", 42),
        ),
        "first define should be a change",
    );

    assert!(
        functions.note(
            function,
            FunctionSource {
                code: code_id,
                owner_module: ModuleId::GLOBAL,
                namespace,
                capture_params: Vec::new(),
                required_remote_macros: Vec::new(),
                variadic: false,
                source: second.clone(),
            },
        ),
        "re-noting a changed raw source should invalidate the definition",
    );

    assert!(
        functions.define(
            function,
            FunctionSource {
                code: code_id,
                owner_module: ModuleId::GLOBAL,
                namespace,
                capture_params: Vec::new(),
                required_remote_macros: Vec::new(),
                variadic: false,
                source: second.clone(),
            },
            FunctionSource {
                code: code_id,
                owner_module: ModuleId::GLOBAL,
                namespace,
                capture_params: Vec::new(),
                required_remote_macros: Vec::new(),
                variadic: false,
                source: second,
            },
            function_surface_with_int("add", 43),
        ),
        "re-defining after a raw-source refresh must still notice the changed expanded definition",
    );

    match functions.get(function) {
        FunctionState::Defined { surface, .. } => {
            assert!(
                matches!(surface.clauses[0].body.node, Expr::Int(43)),
                "re-defining should replace the stale surface after a raw-source re-note"
            );
        }
        other => panic!("function should stay defined after redefine, got {other:?}"),
    }
}
