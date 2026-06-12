use super::quoted_surface::{
    ScopeForm, SurfaceSourceContext, read_compiler_fragment_surface, read_module_body_surface,
    read_protocol_impl_body_surface, read_scope_surface,
};
use super::{CodeMap, parse_quoted_program};
use crate::compiler2::CodeId;
use crate::compiler2::quoted_function::derive_function_surface;
use crate::telemetry::ConfiguredTelemetry;

#[test]
fn compiler2_quoted_surface_reads_alias_as_keyword_value() {
    let tel = ConfiguredTelemetry::new();
    let source = "alias Utf8, as: U\n";
    let mut code = CodeMap::new();
    let code_id = code.define(Some("alias_as.fz".to_string()), source.to_string());
    let root = parse_quoted_program("alias_as.fz", source, &tel).expect("quoted parse");
    let ctx = SurfaceSourceContext::new(code_id, source);

    let surface = read_scope_surface(&root, &ctx).expect("surface read");

    match &surface.forms[0] {
        ScopeForm::Alias(alias) => {
            assert_eq!(alias.path, vec!["Utf8"]);
            assert_eq!(alias.as_name, "U");
        }
        other => panic!("expected alias form, got {other:?}"),
    }
}

#[test]
fn compiler2_quoted_surface_groups_multiclause_functions_into_one_logical_form() {
    let tel = ConfiguredTelemetry::new();
    let source = "fn alpha(0), do: 0\nfn beta(x), do: x\nfn alpha(x), do: x\n";
    let mut code = CodeMap::new();
    let code_id = code.define(Some("surface.fz".to_string()), source.to_string());
    let root = parse_quoted_program("surface.fz", source, &tel).expect("quoted parse");
    let ctx = SurfaceSourceContext::new(code_id, source);

    let surface = read_scope_surface(&root, &ctx).expect("surface read");

    assert_eq!(
        surface.forms.len(),
        2,
        "quoted surface grouping should produce one logical form per function, not per clause",
    );
    match &surface.forms[0] {
        ScopeForm::MacroCall(form) => {
            assert_eq!(
                form.source
                    .cursor()
                    .list_items()
                    .expect("alpha grouped source items")
                    .len(),
                2,
                "source mode should still group multi-clause function macros into one quoted list",
            );
        }
        other => panic!("first grouped source form should be a macro call, got {other:?}"),
    }
    match &surface.forms[1] {
        ScopeForm::MacroCall(form) => {
            assert_eq!(
                form.source
                    .cursor()
                    .list_items()
                    .expect("beta grouped source items")
                    .len(),
                1,
                "single-clause source-mode defs should use the same grouped quoted list shape",
            );
        }
        other => panic!("second grouped source form should be a macro call, got {other:?}"),
    }

    let fragment_surface = read_compiler_fragment_surface(&root, &ctx).expect("fragment surface read");
    assert_eq!(
        fragment_surface.forms.len(),
        2,
        "compiler fragments should preserve the same logical grouping count",
    );
    match &fragment_surface.forms[0] {
        ScopeForm::Function(form) => {
            assert_eq!(form.name, "alpha");
            assert_eq!(form.arity, 1);
            assert_eq!(
                form.source
                    .cursor()
                    .list_items()
                    .expect("alpha grouped source items")
                    .len(),
                2,
                "multi-clause function source should be one grouped quoted list carrying both clauses",
            );
        }
        other => panic!("first grouped form should be alpha/1, got {other:?}"),
    }
    match &fragment_surface.forms[1] {
        ScopeForm::Function(form) => {
            assert_eq!(form.name, "beta");
            assert_eq!(form.arity, 1);
            assert_eq!(
                form.source
                    .cursor()
                    .list_items()
                    .expect("beta grouped source items")
                    .len(),
                1,
                "single-clause functions should still use the same grouped-source shape",
            );
        }
        other => panic!("second grouped form should be beta/1, got {other:?}"),
    }

    let surface_again = read_compiler_fragment_surface(&root, &ctx).expect("fragment surface reread");
    match (&fragment_surface.forms[0], &surface_again.forms[0]) {
        (ScopeForm::Function(first), ScopeForm::Function(second)) => {
            assert_eq!(
                first.source.key(),
                second.source.key(),
                "re-reading the same quoted source should reuse the same grouped function root",
            );
        }
        pair => panic!("expected alpha grouped function on reread, got {pair:?}"),
    }
}

#[test]
fn compiler2_quoted_surface_keeps_attached_function_attrs_inside_grouped_source() {
    let tel = ConfiguredTelemetry::new();
    let source = "@doc \"alpha\"\n@spec alpha(integer) :: integer\nfn alpha(x), do: x\n";
    let mut code = CodeMap::new();
    let code_id = code.define(Some("surface.fz".to_string()), source.to_string());
    let root = parse_quoted_program("surface.fz", source, &tel).expect("quoted parse");
    let ctx = SurfaceSourceContext::new(code_id, source);

    let surface = read_scope_surface(&root, &ctx).expect("surface read");

    match &surface.forms[0] {
        ScopeForm::MacroCall(form) => {
            let items = form.source.cursor().list_items().expect("grouped source items");
            assert_eq!(
                items.len(),
                3,
                "source mode should keep attrs attached to the grouped macro-call source"
            );
            assert_eq!(
                items[0]
                    .ast_node()
                    .expect("doc cursor")
                    .expect("doc node")
                    .head
                    .atom_name()
                    .expect("doc head"),
                "@doc"
            );
            assert_eq!(
                items[1]
                    .ast_node()
                    .expect("spec cursor")
                    .expect("spec node")
                    .head
                    .atom_name()
                    .expect("spec head"),
                "@spec"
            );
            assert_eq!(
                items[2]
                    .ast_node()
                    .expect("fn cursor")
                    .expect("fn node")
                    .head
                    .atom_name()
                    .expect("fn head"),
                "fn"
            );
        }
        other => panic!("expected grouped alpha macro call in source mode, got {other:?}"),
    }

    let fragment_surface = read_compiler_fragment_surface(&root, &ctx).expect("fragment surface read");
    match &fragment_surface.forms[0] {
        ScopeForm::Function(form) => {
            assert_eq!(form.name, "alpha");
            assert_eq!(form.arity, 1);
            let items = form
                .source
                .cursor()
                .list_items()
                .expect("grouped function source items");
            assert_eq!(
                items.len(),
                3,
                "grouped function source should carry attrs plus the clause"
            );
            assert_eq!(
                items[0]
                    .ast_node()
                    .expect("doc cursor")
                    .expect("doc node")
                    .head
                    .atom_name()
                    .expect("doc head"),
                "@doc"
            );
            assert_eq!(
                items[1]
                    .ast_node()
                    .expect("spec cursor")
                    .expect("spec node")
                    .head
                    .atom_name()
                    .expect("spec head"),
                "@spec"
            );
            assert_eq!(
                items[2]
                    .ast_node()
                    .expect("fn cursor")
                    .expect("fn node")
                    .head
                    .atom_name()
                    .expect("fn head"),
                "fn"
            );
        }
        other => panic!("expected grouped alpha function, got {other:?}"),
    }
}

#[test]
fn compiler2_quoted_surface_keeps_long_doc_payloads_inside_nested_module_function_groups() {
    let tel = ConfiguredTelemetry::new();
    let source = r#"
defmodule M do
  @doc "Removes the first matching left-side item for each item in the right list."
  @spec subtract([a], [a]) :: [a]
  fn subtract(left, []), do: left
  fn subtract(left, [item | rest]), do: subtract(delete_first(left, item), rest)
end
"#;
    let mut code = CodeMap::new();
    let code_id = code.define(Some("nested_long_doc.fz".to_string()), source.to_string());
    let root = parse_quoted_program("nested_long_doc.fz", source, &tel).expect("quoted parse");
    let ctx = SurfaceSourceContext::new(code_id, source);

    let outer = read_compiler_fragment_surface(&root, &ctx).expect("outer fragment surface");
    let ScopeForm::Module(module) = &outer.forms[0] else {
        panic!("expected defmodule fragment");
    };
    let body = read_module_body_surface(module, &ctx).expect("nested module body surface");
    let ScopeForm::MacroCall(function) = &body.forms[0] else {
        panic!("expected grouped function macro call inside nested module body");
    };

    derive_function_surface(&function.source, CodeId::ZERO, Some("nested_long_doc.fz"), source, &tel)
        .expect("nested grouped function source should still decode long procbin-backed @doc payloads");
}

#[test]
fn compiler2_quoted_surface_reads_protocol_impl_callbacks_through_grouped_source() {
    let tel = ConfiguredTelemetry::new();
    let source = "defimpl String.Chars, for: Box do\n  @doc \"box\"\n  fn to_string(%Box{value: 0}), do: \"zero\"\n  fn to_string(%Box{value: value}), do: value\nend\n";
    let mut code = CodeMap::new();
    let code_id = code.define(Some("surface.fz".to_string()), source.to_string());
    let root = parse_quoted_program("surface.fz", source, &tel).expect("quoted parse");
    let ctx = SurfaceSourceContext::new(code_id, source);

    let surface = read_scope_surface(&root, &ctx).expect("surface read");

    match &surface.forms[0] {
        ScopeForm::MacroCall(form) => {
            let protocol_impl_head = form
                .source
                .cursor()
                .ast_node()
                .expect("protocol impl cursor")
                .expect("protocol impl node")
                .head
                .atom_name()
                .expect("protocol impl head");
            assert_eq!(
                protocol_impl_head, "defimpl",
                "source mode should surface protocol impl definitions as macro calls",
            );
        }
        other => panic!("expected source-mode protocol impl macro call, got {other:?}"),
    }

    let fragment_surface = read_compiler_fragment_surface(&root, &ctx).expect("fragment surface read");
    match &fragment_surface.forms[0] {
        ScopeForm::ProtocolImpl(form) => {
            let body = read_protocol_impl_body_surface(form, &ctx).expect("protocol impl body surface");
            assert_eq!(
                body.forms.len(),
                1,
                "callback clauses should group to one logical function surface"
            );
            match &body.forms[0] {
                ScopeForm::Function(function) => {
                    assert_eq!(function.name, "to_string");
                    assert_eq!(function.arity, 1);
                    let items = function.source.cursor().list_items().expect("callback grouped items");
                    assert_eq!(
                        items.len(),
                        3,
                        "grouped callback source should carry attrs plus both clauses"
                    );
                }
                other => panic!("expected grouped callback function, got {other:?}"),
            }
        }
        other => panic!("expected compiler-fragment protocol impl form, got {other:?}"),
    }
}

#[test]
fn compiler2_quoted_surface_rejects_a_trailing_dangling_spec() {
    // A @spec that no function definition ever follows used to be silently
    // dropped at end-of-scope; the missing function then surfaced much later
    // as a confusing unknown-export diagnostic. It is a source-surface
    // error, and it is reported here, where the dangling attr is visible.
    let tel = ConfiguredTelemetry::new();
    let source = "fn alpha(x), do: x\n@spec beta(integer) :: integer\n";
    let mut code = CodeMap::new();
    let code_id = code.define(Some("dangling_tail.fz".to_string()), source.to_string());
    let root = parse_quoted_program("dangling_tail.fz", source, &tel).expect("quoted parse");
    let ctx = SurfaceSourceContext::new(code_id, source);

    let error = read_scope_surface(&root, &ctx).expect_err("a trailing @spec attaches to nothing");
    assert!(
        error.to_string().contains("@spec") && error.to_string().contains("does not attach"),
        "the rejection names the dangling attribute: {error}",
    );
}

#[test]
fn compiler2_quoted_surface_rejects_a_spec_followed_by_a_non_function_form() {
    let tel = ConfiguredTelemetry::new();
    let source = "@spec alpha(integer) :: integer\nalias Utf8, as: U\nfn alpha(x), do: x\n";
    let mut code = CodeMap::new();
    let code_id = code.define(Some("dangling_mid.fz".to_string()), source.to_string());
    let root = parse_quoted_program("dangling_mid.fz", source, &tel).expect("quoted parse");
    let ctx = SurfaceSourceContext::new(code_id, source);

    read_scope_surface(&root, &ctx).expect_err("an interposed non-function form orphans the pending @spec");
}

#[test]
fn compiler2_quoted_surface_attaches_stacked_doc_and_spec_through_scope_attrs() {
    // The happy paths stay happy: stacked @doc/@spec attach to the next
    // function group, and intervening NON-function attrs (@moduledoc) do
    // not orphan them.
    let tel = ConfiguredTelemetry::new();
    let source = concat!(
        "@doc \"adds one\"\n",
        "@moduledoc \"m\"\n",
        "@spec alpha(integer) :: integer\n",
        "fn alpha(x), do: x\n",
    );
    let mut code = CodeMap::new();
    let code_id = code.define(Some("stacked.fz".to_string()), source.to_string());
    let root = parse_quoted_program("stacked.fz", source, &tel).expect("quoted parse");
    let ctx = SurfaceSourceContext::new(code_id, source);

    let surface = read_scope_surface(&root, &ctx).expect("stacked attrs attach to the group");
    assert_eq!(
        surface.forms.len(),
        1,
        "one logical function form carries the attached attrs",
    );
}
