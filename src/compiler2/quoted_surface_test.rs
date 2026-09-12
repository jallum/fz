use super::quoted_surface::{
    ProtocolForm, ScopeForm, read_compiler_fragment_surface, read_module_body_surface, read_protocol_body_surface,
    read_protocol_impl_body_surface, read_scope_surface,
};
use super::{CodeMap, parse_quoted_program};
use crate::compiler2::quoted_function::derive_function_surface;
use crate::telemetry::ConfiguredTelemetry;

fn parse_code(code: &CodeMap, owner: super::SourceOwner, tel: &ConfiguredTelemetry) -> super::QuotedSourceRoot {
    parse_quoted_program(
        &code.source_map().borrow(),
        code.version(owner).expect("defined source version"),
        tel,
    )
    .expect("quoted parse")
}

#[test]
fn compiler2_quoted_surface_groups_def_and_derives_defp_privacy_and_bare_arity() {
    let tel = ConfiguredTelemetry::new();
    let source = concat!(
        "@doc \"identity\"\n",
        "@spec alpha(integer) :: integer\n",
        "def alpha(0), do: 0\n",
        "def alpha(x), do: x\n",
        "defp hidden(x), do: x\n",
        "def zero do\n  0\nend\n",
    );
    let mut code = CodeMap::new();
    let source_owner = code.define(Some("definition_surface.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);
    let source_map = code.source_map();
    let sources = source_map.borrow();

    let source_surface = read_scope_surface(&root, &sources).expect("source surface");
    assert_eq!(source_surface.forms.len(), 3, "alpha clauses should be one macro call");
    assert!(
        source_surface
            .forms
            .iter()
            .all(|form| matches!(form, ScopeForm::MacroCall(_)))
    );

    let fragment = read_compiler_fragment_surface(&root, &sources).expect("compiler fragment");
    let functions = fragment
        .forms
        .iter()
        .map(|form| match form {
            ScopeForm::Function(function) => function,
            other => panic!("expected function form, got {other:?}"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        functions
            .iter()
            .map(|function| (
                function.name.as_str(),
                function.arity,
                function.is_private,
                function.is_macro
            ))
            .collect::<Vec<_>>(),
        [
            ("alpha", 1, false, false),
            ("hidden", 1, true, false),
            ("zero", 0, false, false)
        ]
    );
    let alpha = derive_function_surface(&functions[0].source, &sources).expect("alpha surface");
    assert_eq!(alpha.clauses.len(), 2);
    assert_eq!(
        alpha.attrs.len(),
        2,
        "doc and spec attributes must remain attached to the grouped def surface"
    );
    assert!(
        derive_function_surface(&functions[2].source, &sources)
            .expect("bare zero-arity surface")
            .clauses[0]
            .params
            .is_empty()
    );
}

#[test]
fn compiler2_quoted_surface_rejects_mixed_def_and_defp_clauses() {
    let tel = ConfiguredTelemetry::new();
    let source = "def same(0), do: 0\ndefp same(x), do: x\n";
    let mut code = CodeMap::new();
    let source_owner = code.define(Some("mixed_visibility.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);
    let source_map = code.source_map();
    let sources = source_map.borrow();

    let error =
        read_scope_surface(&root, &sources).expect_err("one function group cannot mix public and private clauses");
    assert_eq!(
        error.user_code(),
        Some(crate::diag::codes::PARSE_MIXED_FUNCTION_VISIBILITY)
    );
    assert!(
        error.to_string().contains("mixes `def` and `defp`"),
        "diagnostic should name both conflicting heads: {error}"
    );
}

#[test]
fn compiler2_protocol_surface_rejects_a_bodyless_defp_fragment() {
    let tel = ConfiguredTelemetry::new();
    let source = "defprotocol Fold do\n  def reduce(value)\nend\n";
    let mut code = CodeMap::new();
    let source_owner = code.define(Some("protocol_private_callback.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);
    let source_map = code.source_map();
    let sources = source_map.borrow();
    let protocol = root.cursor().list_items().expect("top-level items")[0]
        .ast_node(&sources)
        .expect("protocol cursor")
        .expect("protocol node");
    let protocol_args = protocol.tail.list_items().expect("protocol args");
    let body_entry = protocol_args[1].list_items().expect("protocol keywords")[0]
        .tuple_items()
        .expect("do tuple");
    let callback = body_entry[1].list_items().expect("protocol body")[0]
        .ast_node(&sources)
        .expect("callback cursor")
        .expect("callback node");
    let callback_head = callback.tail.list_items().expect("callback args")[0].root();
    let builder = root.builder();
    let private_callback_args = builder.list(&[callback_head]).expect("private callback args");
    let private_callback = builder
        .tuple(&[builder.atom("defp"), callback.meta.root(), private_callback_args])
        .expect("private callback node");
    let private_body = builder.list(&[private_callback]).expect("private callback body");
    let private_keywords = builder
        .list(&[builder.keyword("do", private_body).expect("do keyword")])
        .expect("protocol keywords");
    let private_protocol_args = builder
        .list(&[protocol_args[0].root(), private_keywords])
        .expect("protocol args");
    let private_protocol = builder
        .tuple(&[builder.atom("defprotocol"), protocol.meta.root(), private_protocol_args])
        .expect("protocol node");
    let form = ProtocolForm {
        source: root.subroot(private_protocol),
        name: crate::modules::identity::ModuleName::parse_dotted("Fold").expect("module name"),
        span: crate::source::Span::DUMMY,
    };

    let error = read_protocol_body_surface(&form, &sources).expect_err("defp cannot become a protocol callback");
    assert_eq!(
        error.user_code(),
        Some(crate::diag::codes::PARSE_INVALID_FUNCTION_DEFINITION)
    );
    assert!(error.to_string().contains("must use `def`, got `defp`"), "{error}");
}

#[test]
fn compiler2_quoted_surface_uses_lexer_authority_for_local_definition_names() {
    let tel = ConfiguredTelemetry::new();
    let source = "def valid(value), do: value\n";
    let mut code = CodeMap::new();
    let source_owner = code.define(Some("generated_definition_names.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);
    let source_map = code.source_map();
    let sources = source_map.borrow();
    let definition = root.cursor().list_items().expect("items")[0]
        .ast_node(&sources)
        .expect("definition cursor")
        .expect("definition node");
    let definition_args = definition.tail.list_items().expect("definition args");
    let valid_head = definition_args[0]
        .ast_node(&sources)
        .expect("head cursor")
        .expect("head node");
    let builder = root.builder();

    for invalid_name in ["_", "Foo", "if"] {
        let invalid_head = builder
            .tuple(&[
                builder.atom(invalid_name),
                valid_head.meta.root(),
                valid_head.tail.root(),
            ])
            .expect("invalid head node");
        let invalid_args = builder
            .list(&[invalid_head, definition_args[1].root()])
            .expect("definition args");
        let invalid_definition = builder
            .tuple(&[definition.head.root(), definition.meta.root(), invalid_args])
            .expect("definition node");
        let invalid_root = root
            .interned_list_subroot(&[invalid_definition])
            .expect("definition root");

        let error = read_compiler_fragment_surface(&invalid_root, &sources)
            .expect_err("non-identifier source words cannot become local function names");
        assert_eq!(
            error.user_code(),
            Some(crate::diag::codes::PARSE_INVALID_FUNCTION_DEFINITION),
            "{invalid_name}: {error}"
        );
    }
}

#[test]
fn compiler2_quoted_surface_rejects_nested_when_definition_heads() {
    let tel = ConfiguredTelemetry::new();
    let source = "def valid(value) when value > 0, do: value\n";
    let mut code = CodeMap::new();
    let source_owner = code.define(Some("nested_definition_guard.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);
    let source_map = code.source_map();
    let sources = source_map.borrow();
    let definition = root.cursor().list_items().expect("items")[0]
        .ast_node(&sources)
        .expect("definition cursor")
        .expect("definition node");
    let definition_args = definition.tail.list_items().expect("definition args");
    let guard = definition_args[0]
        .ast_node(&sources)
        .expect("guard cursor")
        .expect("guard node");
    let guard_args = guard.tail.list_items().expect("guard args");
    let builder = root.builder();
    let nested_guard_args = builder
        .list(&[definition_args[0].root(), guard_args[1].root()])
        .expect("nested guard args");
    let nested_guard = builder
        .tuple(&[guard.head.root(), guard.meta.root(), nested_guard_args])
        .expect("nested guard");
    let nested_definition_args = builder
        .list(&[nested_guard, definition_args[1].root()])
        .expect("definition args");
    let nested_definition = builder
        .tuple(&[definition.head.root(), definition.meta.root(), nested_definition_args])
        .expect("definition node");
    let nested_root = root
        .interned_list_subroot(&[nested_definition])
        .expect("definition root");

    let error = read_compiler_fragment_surface(&nested_root, &sources)
        .expect_err("accepted function heads must not discard an inner guard");
    assert_eq!(
        error.user_code(),
        Some(crate::diag::codes::PARSE_INVALID_FUNCTION_DEFINITION)
    );
    assert!(error.to_string().contains("nested `when` guards"), "{error}");
}

#[test]
fn compiler2_quoted_surface_reads_alias_as_keyword_value() {
    let tel = ConfiguredTelemetry::new();
    let source = "alias Utf8, as: U\n";
    let mut code = CodeMap::new();
    let source_owner = code.define(Some("alias_as.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);

    let surface = read_scope_surface(&root, &code.source_map().borrow()).expect("surface read");

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
    let source_owner = code.define(Some("surface.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);

    let surface = read_scope_surface(&root, &code.source_map().borrow()).expect("surface read");

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

    let fragment_surface =
        read_compiler_fragment_surface(&root, &code.source_map().borrow()).expect("fragment surface read");
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

    let surface_again =
        read_compiler_fragment_surface(&root, &code.source_map().borrow()).expect("fragment surface reread");
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
    let source_owner = code.define(Some("surface.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);

    let surface = read_scope_surface(&root, &code.source_map().borrow()).expect("surface read");

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
                    .trusted_ast_node()
                    .expect("doc cursor")
                    .expect("doc node")
                    .head
                    .atom_name()
                    .expect("doc head"),
                "@doc"
            );
            assert_eq!(
                items[1]
                    .trusted_ast_node()
                    .expect("spec cursor")
                    .expect("spec node")
                    .head
                    .atom_name()
                    .expect("spec head"),
                "@spec"
            );
            assert_eq!(
                items[2]
                    .trusted_ast_node()
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

    let fragment_surface =
        read_compiler_fragment_surface(&root, &code.source_map().borrow()).expect("fragment surface read");
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
                    .trusted_ast_node()
                    .expect("doc cursor")
                    .expect("doc node")
                    .head
                    .atom_name()
                    .expect("doc head"),
                "@doc"
            );
            assert_eq!(
                items[1]
                    .trusted_ast_node()
                    .expect("spec cursor")
                    .expect("spec node")
                    .head
                    .atom_name()
                    .expect("spec head"),
                "@spec"
            );
            assert_eq!(
                items[2]
                    .trusted_ast_node()
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
    let source_owner = code.define(Some("nested_long_doc.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);

    let outer = read_compiler_fragment_surface(&root, &code.source_map().borrow()).expect("outer fragment surface");
    let ScopeForm::Module(module) = &outer.forms[0] else {
        panic!("expected defmodule fragment");
    };
    let body = read_module_body_surface(module, &code.source_map().borrow()).expect("nested module body surface");
    let ScopeForm::MacroCall(function) = &body.forms[0] else {
        panic!("expected grouped function macro call inside nested module body");
    };

    derive_function_surface(&function.source, &code.source_map().borrow())
        .expect("nested grouped function source should still decode long procbin-backed @doc payloads");
}

#[test]
fn compiler2_quoted_surface_reads_protocol_impl_callbacks_through_grouped_source() {
    let tel = ConfiguredTelemetry::new();
    let source = "defimpl String.Chars, for: Box do\n  @doc \"box\"\n  fn to_string(%Box{value: 0}), do: \"zero\"\n  fn to_string(%Box{value: value}), do: value\nend\n";
    let mut code = CodeMap::new();
    let source_owner = code.define(Some("surface.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);

    let surface = read_scope_surface(&root, &code.source_map().borrow()).expect("surface read");

    match &surface.forms[0] {
        ScopeForm::MacroCall(form) => {
            let protocol_impl_head = form
                .source
                .cursor()
                .trusted_ast_node()
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

    let fragment_surface =
        read_compiler_fragment_surface(&root, &code.source_map().borrow()).expect("fragment surface read");
    match &fragment_surface.forms[0] {
        ScopeForm::ProtocolImpl(form) => {
            let body =
                read_protocol_impl_body_surface(form, &code.source_map().borrow()).expect("protocol impl body surface");
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
    let source_owner = code.define(Some("dangling_tail.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);

    let error =
        read_scope_surface(&root, &code.source_map().borrow()).expect_err("a trailing @spec attaches to nothing");
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
    let source_owner = code.define(Some("dangling_mid.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);

    read_scope_surface(&root, &code.source_map().borrow())
        .expect_err("an interposed non-function form orphans the pending @spec");
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
    let source_owner = code.define(Some("stacked.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);

    let surface = read_scope_surface(&root, &code.source_map().borrow()).expect("stacked attrs attach to the group");
    assert_eq!(
        surface.forms.len(),
        1,
        "one logical function form carries the attached attrs",
    );
}

#[test]
fn compiler2_quoted_surface_carries_a_heredoc_moduledoc_whole() {
    // `@moduledoc` decodes on its own path (`parse_scope_attr`) rather than
    // the one `@doc` takes, so it gets its own pin: a heredoc reaching the
    // scope surface with its paragraphs intact.
    let tel = ConfiguredTelemetry::new();
    let source = "@moduledoc \"\"\"\nText handling.\n\nEverything here is bytes.\n\"\"\"\nfn a(), do: 1\n";
    let mut code = CodeMap::new();
    let source_owner = code.define(Some("mod_doc.fz".to_string()), source.to_string());
    let root = parse_code(&code, source_owner, &tel);

    let surface = read_scope_surface(&root, &code.source_map().borrow()).expect("surface read");

    match &surface.attrs[0] {
        crate::ast::Attribute::ModuleDoc(doc) => assert_eq!(
            doc, "Text handling.\n\nEverything here is bytes.\n",
            "a module doc should keep the blank line between its paragraphs"
        ),
        other => panic!("expected @moduledoc attr, got {other:?}"),
    }
}
