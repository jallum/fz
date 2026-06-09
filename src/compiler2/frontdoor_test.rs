use super::{QuotedSourceFingerprintPolicy, parse_quoted_program};
use crate::telemetry::ConfiguredTelemetry;

fn head_name(node: &super::QuotedAstNode) -> String {
    node.head.atom_name().expect("ast head atom")
}

#[test]
fn compiler2_frontdoor_parses_alias_import_and_require_as_quoted_calls() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "surface.fz",
        "alias Helpers.Tools, as: Tools\nrequire Helpers.Tools\nimport Helpers.Tools, only: [twice: 1]\n",
        &tel,
    )
    .expect("quoted parse");

    let items = root.cursor().list_items().expect("top-level items");
    assert_eq!(items.len(), 3);
    assert_eq!(
        head_name(&items[0].ast_node().expect("alias cursor").expect("alias node")),
        "alias"
    );
    assert_eq!(
        head_name(&items[1].ast_node().expect("require cursor").expect("require node")),
        "require"
    );
    let import = items[2].ast_node().expect("import cursor").expect("import node");
    assert_eq!(head_name(&import), "import");

    let import_args = import.tail.list_items().expect("import args");
    let only_kw = import_args[1].list_items().expect("import kw list");
    let only_entry = only_kw[0].tuple_items().expect("only tuple");
    assert_eq!(only_entry[0].atom_name().expect("only key"), "only");
    let filters = only_entry[1].list_items().expect("only filters");
    let pair = filters[0].tuple_items().expect("filter pair");
    assert_eq!(pair[0].atom_name().expect("filter name"), "twice");
    assert_eq!(pair[1].int_value().expect("filter arity"), 1);
}

#[test]
fn compiler2_frontdoor_threads_source_context_through_nested_modules() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "app.fz",
        "defmodule App do\n  require Helpers\n  defmodule Tools do\n    import Helpers, except: [twice: 1]\n  end\nend\n",
        &tel,
    )
    .expect("quoted parse");

    let top = root.cursor().list_items().expect("top-level items");
    let app = top[0].ast_node().expect("app cursor").expect("app defmodule node");
    assert_eq!(head_name(&app), "defmodule");

    let app_body = app.tail.list_items().expect("app args")[1]
        .list_items()
        .expect("app kw")[0]
        .tuple_items()
        .expect("app do tuple")[1]
        .list_items()
        .expect("app body items");
    let require = app_body[0].ast_node().expect("require cursor").expect("require node");
    let require_lexical = require
        .meta
        .map_value("__fz_lexical__")
        .expect("require lexical lookup")
        .expect("require lexical");
    assert_eq!(
        require_lexical
            .map_value("module")
            .expect("require module lookup")
            .expect("require module")
            .list_atom_names()
            .expect("require module atoms"),
        vec!["App".to_string()]
    );

    let tools = app_body[1]
        .ast_node()
        .expect("tools cursor")
        .expect("tools defmodule node");
    let tools_body = tools.tail.list_items().expect("tools args")[1]
        .list_items()
        .expect("tools kw")[0]
        .tuple_items()
        .expect("tools do tuple")[1]
        .list_items()
        .expect("tools body items");
    let import = tools_body[0]
        .ast_node()
        .expect("nested import cursor")
        .expect("nested import node");
    let import_lexical = import
        .meta
        .map_value("__fz_lexical__")
        .expect("nested import lexical lookup")
        .expect("nested import lexical");
    assert_eq!(
        import_lexical
            .map_value("module")
            .expect("nested import module lookup")
            .expect("nested import module")
            .list_atom_names()
            .expect("nested import module atoms"),
        vec!["App".to_string(), "Tools".to_string()]
    );
    assert_eq!(
        import
            .meta
            .map_value("__fz_span__")
            .expect("nested import span lookup")
            .expect("nested import span")
            .map_value("line")
            .expect("nested import line lookup")
            .expect("nested import line")
            .int_value()
            .expect("nested import line int"),
        4
    );
}

#[test]
fn compiler2_frontdoor_surface_root_is_real_quoted_source_not_old_ast() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "surface.fz",
        "require Helpers\nimport Helpers, except: [twice: 1]\ndefmodule App do\n  require Helpers\nend\n",
        &tel,
    )
    .expect("quoted parse");

    let semantic = root
        .fingerprint(QuotedSourceFingerprintPolicy::Semantic)
        .expect("semantic fingerprint");
    assert!(
        semantic.canonical.contains("atom:require")
            && semantic.canonical.contains("atom:import")
            && semantic.canonical.contains("atom:defmodule"),
        "front-door parse should produce one quoted source graph, not old AST authority"
    );
}

#[test]
fn compiler2_frontdoor_parses_function_and_macro_defs_with_quote_unquote() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program("macro_inc.fz", include_str!("../../fixtures/macro_inc/input.fz"), &tel)
        .expect("quoted parse");

    let items = root.cursor().list_items().expect("top-level items");
    assert_eq!(items.len(), 3);
    assert_eq!(
        head_name(&items[0].ast_node().expect("macro cursor").expect("macro node")),
        "defmacro"
    );
    assert_eq!(
        head_name(&items[1].ast_node().expect("macro cursor").expect("macro node")),
        "defmacro"
    );
    assert_eq!(
        head_name(&items[2].ast_node().expect("fn cursor").expect("fn node")),
        "fn"
    );

    let macro_node = items[0].ast_node().expect("macro cursor").expect("macro node");
    let macro_args = macro_node.tail.list_items().expect("macro args");
    let quote_node = macro_args[1].list_items().expect("macro kw")[0]
        .tuple_items()
        .expect("macro do tuple")[1]
        .ast_node()
        .expect("quote cursor")
        .expect("quote node");
    assert_eq!(head_name(&quote_node), "quote");
    let quote_body = quote_node.tail.list_items().expect("quote args")[0]
        .list_items()
        .expect("quote kw")[0]
        .tuple_items()
        .expect("quote do tuple")[1]
        .ast_node()
        .expect("quote body cursor")
        .expect("quote body node");
    assert_eq!(head_name(&quote_body), "+");
    let quote_args = quote_body.tail.list_items().expect("quote body args");
    assert_eq!(
        head_name(&quote_args[0].ast_node().expect("unquote cursor").expect("unquote node")),
        "unquote"
    );
}

#[test]
fn compiler2_frontdoor_parses_item_macro_calls_with_trailing_do() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program("test_surface.fz", "test(:name) do\n  42\nend\n", &tel).expect("quoted parse");

    let items = root.cursor().list_items().expect("top-level items");
    assert_eq!(items.len(), 1);
    let test_call = items[0].ast_node().expect("test cursor").expect("test call");
    assert_eq!(head_name(&test_call), "test");
    let args = test_call.tail.list_items().expect("test args");
    assert_eq!(args[0].atom_name().expect("test name atom"), "name");
    assert_eq!(
        args[1].list_items().expect("test kw")[0]
            .tuple_items()
            .expect("test do tuple")[0]
            .atom_name()
            .expect("test do key"),
        "do"
    );
}

#[test]
fn compiler2_frontdoor_parses_remote_calls_captures_and_headless_case_from_fixtures() {
    let tel = ConfiguredTelemetry::new();

    let cross = parse_quoted_program(
        "cross_module_macro.fz",
        include_str!("../../fixtures/cross_module_macro/input.fz"),
        &tel,
    )
    .expect("cross-module macro parse");
    let cross_semantic = cross
        .fingerprint(QuotedSourceFingerprintPolicy::Semantic)
        .expect("cross semantic");
    assert!(
        cross_semantic.canonical.contains("atom:defmodule")
            && cross_semantic.canonical.contains("atom:defmacro")
            && cross_semantic.canonical.contains("atom:import")
            && cross_semantic.canonical.contains("atom:.")
            && cross_semantic.canonical.contains("atom:__info__"),
        "cross-module macro fixture should parse remote calls and module source forms directly to quoted source"
    );

    let pipe_case = parse_quoted_program(
        "pipe_headless_case.fz",
        include_str!("../../fixtures/pipe_headless_case/input.fz"),
        &tel,
    )
    .expect("pipe/headless-case parse");
    let pipe_semantic = pipe_case
        .fingerprint(QuotedSourceFingerprintPolicy::Semantic)
        .expect("pipe semantic");
    assert!(
        pipe_semantic.canonical.contains("atom:|>")
            && pipe_semantic.canonical.contains("atom:case")
            && pipe_semantic.canonical.contains("atom:->"),
        "pipe/headless-case fixture should parse pipe and headless case directly to quoted source"
    );

    let fn_ref = parse_quoted_program(
        "fn_ref.fz",
        include_str!("../../fixtures/fn_ref_ampersand/input.fz"),
        &tel,
    )
    .expect("fn-ref parse");
    let fn_ref_semantic = fn_ref
        .fingerprint(QuotedSourceFingerprintPolicy::Semantic)
        .expect("fn-ref semantic");
    assert!(
        fn_ref_semantic.canonical.contains("atom:&")
            && fn_ref_semantic.canonical.contains("atom:/")
            && fn_ref_semantic.canonical.contains("atom:."),
        "function-reference fixture should parse captures and closure calls directly to quoted source"
    );
}

#[test]
fn compiler2_frontdoor_parses_attributes_protocols_impls_and_structs() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "surface.fz",
        "@moduledoc \"docs\"\n@type t :: integer\n@spec run(integer) :: integer\ndefstruct [name, age]\ndefprotocol Enumerable do\n  @doc \"reduce docs\"\n  fn reduce(xs, acc)\nend\ndefimpl Enumerable, for: List do\n  fn reduce(xs, acc), do: acc\nend\n",
        &tel,
    )
    .expect("quoted parse");

    let semantic = root
        .fingerprint(QuotedSourceFingerprintPolicy::Semantic)
        .expect("semantic fingerprint");
    assert!(
        semantic.canonical.contains("atom:@moduledoc")
            && semantic.canonical.contains("atom:@type")
            && semantic.canonical.contains("atom:@spec")
            && semantic.canonical.contains("atom:defstruct")
            && semantic.canonical.contains("atom:defprotocol")
            && semantic.canonical.contains("atom:defimpl"),
        "front door should parse attribute/protocol/source-declaration forms directly to quoted source"
    );
}

#[test]
fn compiler2_frontdoor_parses_maps_structs_bitstrings_and_patterns() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "shapes.fz",
        "fn shapes(x :: integer, ref) do\n  literal = %{2 => x, a: 1}\n  updated = %{literal | a: 2, b: 3}\n  point = %Point{x: x, y: 1}\n  bytes = <<104, 105>>\n  case x do\n    %{name: n} -> n\n    {:ok, s} when s == \"hi\" -> s\n    [h | _] -> h\n    ^ref -> ref\n    <<len, payload::binary-size(len), rest::binary>> -> len\n  end\nend\n",
        &tel,
    )
    .expect("quoted parse");

    let semantic = root
        .fingerprint(QuotedSourceFingerprintPolicy::Semantic)
        .expect("semantic fingerprint");
    assert!(
        semantic.canonical.contains("atom:::")
            && semantic.canonical.contains("atom:%{}")
            && semantic.canonical.contains("atom:%")
            && semantic.canonical.contains("atom:<<>>")
            && semantic.canonical.contains("atom:|")
            && semantic.canonical.contains("atom:^")
            && semantic.canonical.contains("atom:when")
            && semantic.canonical.contains("atom:binary")
            && semantic.canonical.contains("atom:size"),
        "front door should parse typed params, maps, structs, bitstrings, and pattern forms directly to quoted source"
    );
}
