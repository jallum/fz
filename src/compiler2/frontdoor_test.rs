use super::parse_quoted_program;
use super::source_test::assert_quoted_mentions;
use crate::compiler2::CodeId;
use crate::modules::runtime_library;
use crate::parser::lexer::Tok;
use crate::telemetry::ConfiguredTelemetry;

fn head_name(node: &super::QuotedAstNode) -> String {
    node.head.atom_name().expect("ast head atom")
}

fn map_value<'a>(
    entries: &'a [(super::QuotedSourceCursor, super::QuotedSourceCursor)],
    key: &str,
) -> &'a super::QuotedSourceCursor {
    entries
        .iter()
        .find(|(entry_key, _)| entry_key.atom_name().ok().as_deref() == Some(key))
        .map(|(_, value)| value)
        .unwrap_or_else(|| panic!("quoted map should contain `{key}`"))
}

fn token_kinds(cursor: &super::QuotedSourceCursor) -> Vec<Tok> {
    super::token_payload::decode_tokens(cursor)
        .expect("decode token payload")
        .into_iter()
        .map(|token| token.tok)
        .collect()
}

/// Digs out the `do:` body of the first top-level `fn`/`fnp`/`defmacro` item:
/// `{head_name, meta, [head, [{:do, body}]]}` -> `body`.
fn fn_do_body(root: &super::QuotedSourceRoot) -> super::QuotedSourceCursor {
    let items = root.cursor().list_items().expect("top-level items");
    let fn_node = items[0].ast_node().expect("fn cursor").expect("fn node");
    fn_node.tail.list_items().expect("fn args")[1]
        .list_items()
        .expect("fn kw list")[0]
        .tuple_items()
        .expect("do tuple")[1]
        .clone()
}

#[test]
fn compiler2_frontdoor_parses_alias_import_and_require_as_quoted_calls() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "surface.fz",
        "alias Helpers.Tools, as: Tools\nrequire Helpers.Tools\nimport Helpers.Tools, only: [twice: 1]\n",
        CodeId::ZERO,
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
    let source = "defmodule App do\n  require Helpers\n  defmodule Tools do\n    import Helpers, except: [twice: 1]\n  end\nend\n";
    let root = parse_quoted_program("app.fz", source, CodeId::ZERO, &tel).expect("quoted parse");

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
    // The span is a byte offset now; resolve it back to a line to assert the
    // nested import's position threaded through correctly (it sits on line 4).
    let start = import
        .meta
        .map_value("__fz_span__")
        .expect("nested import span lookup")
        .expect("nested import span")
        .map_value("start")
        .expect("nested import start lookup")
        .expect("nested import start")
        .int_value()
        .expect("nested import start int") as usize;
    let line = source[..start].bytes().filter(|&byte| byte == b'\n').count() + 1;
    assert_eq!(line, 4, "nested import span should point at line 4");
}

#[test]
fn compiler2_frontdoor_encodes_type_ascriptions_as_token_payloads() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "typed.fz",
        "fn pack(x :: integer), do: x :: list(integer)\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("quoted parse");

    let items = root.cursor().list_items().expect("top-level items");
    let function = items[0].ast_node().expect("function cursor").expect("function node");
    let function_args = function.tail.list_items().expect("function args");
    let head = function_args[0]
        .ast_node()
        .expect("function head cursor")
        .expect("function head node");
    let head_args = head.tail.list_items().expect("head args");
    let annotated_param = head_args[0]
        .ast_node()
        .expect("annotated param cursor")
        .expect("annotated param node");
    assert_eq!(head_name(&annotated_param), "::");
    let param_parts = annotated_param.tail.list_items().expect("annotated param parts");
    assert_eq!(
        token_kinds(&param_parts[1]),
        vec![Tok::Ident("integer".to_string())],
        "parameter annotation rhs should stay as a token payload",
    );

    let body_kw = function_args[1].list_items().expect("function kw list");
    let body_expr = body_kw[0].tuple_items().expect("do keyword tuple")[1]
        .ast_node()
        .expect("body ascription cursor")
        .expect("body ascription node");
    assert_eq!(head_name(&body_expr), "::");
    let body_parts = body_expr.tail.list_items().expect("body ascription parts");
    assert_eq!(
        token_kinds(&body_parts[1]),
        vec![
            Tok::Ident("list".to_string()),
            Tok::LParen,
            Tok::Ident("integer".to_string()),
            Tok::RParen,
        ],
        "expression ascription rhs should stay as a token payload",
    );
}

#[test]
fn compiler2_frontdoor_surface_root_is_real_quoted_source_not_old_ast() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "surface.fz",
        "require Helpers\nimport Helpers, except: [twice: 1]\ndefmodule App do\n  require Helpers\nend\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("quoted parse");

    // Front-door parse should produce one quoted source graph, not old AST
    // authority.
    assert_quoted_mentions(&root, &["require", "import", "defmodule"]);
}

#[test]
fn compiler2_frontdoor_parses_function_and_macro_defs_with_quote_unquote() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "macro_inc.fz",
        include_str!("../../fixtures2/behavior/macro_inc.fz"),
        CodeId::ZERO,
        &tel,
    )
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
fn compiler2_frontdoor_parses_guarded_one_line_function_clauses() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "guarded_clause.fz",
        "fn positive(n), do: n > 0\nfn wanted(n) when positive(n), do: n\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("quoted parse");

    let items = root.cursor().list_items().expect("top-level items");
    assert_eq!(items.len(), 2);
    let wanted = items[1].ast_node().expect("wanted cursor").expect("wanted node");
    assert_eq!(head_name(&wanted), "fn");
    let head = wanted.tail.list_items().expect("wanted args")[0]
        .ast_node()
        .expect("wanted head cursor")
        .expect("wanted head node");
    assert_eq!(
        head_name(&head),
        "when",
        "guarded one-line defs should keep the guard on the function head instead of letting `, do:` bleed into the guard expression",
    );
}

#[test]
fn compiler2_frontdoor_paren_call_keyword_args_plus_trailing_do_appends_second_keyword_list() {
    // Elixir never merges a trailing `do:` into a preceding keyword-list
    // argument, even when that argument came from paren-call keyword sugar:
    // `echo(label: :work) do 42 end` is `echo([label: :work], [do: 42])`,
    // arity 2 -- not `echo([label: :work, do: 42])`, arity 1. `attach_trailing_do`
    // always appends a fresh `[do: ...]` argument for a parenthesized call; it
    // never rewrites an existing argument in place.
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "keyword_paren_do.fz",
        "echo(label: :work) do\n  42\nend\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("quoted parse");

    let items = root.cursor().list_items().expect("top-level items");
    assert_eq!(items.len(), 1);
    let call = items[0].ast_node().expect("call cursor").expect("call node");
    assert_eq!(head_name(&call), "echo");
    let args = call.tail.list_items().expect("call args");
    assert_eq!(
        args.len(),
        2,
        "the preceding keyword-list arg and the trailing do-block are two separate arguments, not merged"
    );
    let first_kw = args[0].list_items().expect("first kw list");
    assert_eq!(
        first_kw[0].tuple_items().expect("label tuple")[0]
            .atom_name()
            .expect("label key"),
        "label"
    );
    let second_kw = args[1].list_items().expect("second kw list");
    assert_eq!(
        second_kw[0].tuple_items().expect("do tuple")[0]
            .atom_name()
            .expect("do key"),
        "do"
    );
}

#[test]
fn compiler2_frontdoor_parses_item_macro_calls_with_trailing_do() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program("test_surface.fz", "test(:name) do\n  42\nend\n", CodeId::ZERO, &tel)
        .expect("quoted parse");

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
        include_str!("../../fixtures2/behavior/cross_module_macro.fz"),
        CodeId::ZERO,
        &tel,
    )
    .expect("cross-module macro parse");
    // Cross-module macro fixture should parse remote calls and module source
    // forms directly to quoted source.
    assert_quoted_mentions(&cross, &["defmodule", "defmacro", "import", ".", "__info__"]);

    let pipe_case = parse_quoted_program(
        "pipe_headless_case.fz",
        include_str!("../../fixtures2/behavior/pipe_headless_case.fz"),
        CodeId::ZERO,
        &tel,
    )
    .expect("pipe/headless-case parse");
    // Pipe/headless-case fixture should parse pipe and headless case directly
    // to quoted source.
    assert_quoted_mentions(&pipe_case, &["|>", "case", "->"]);

    let fn_ref = parse_quoted_program(
        "fn_ref.fz",
        include_str!("../../fixtures2/behavior/fn_ref_ampersand.fz"),
        CodeId::ZERO,
        &tel,
    )
    .expect("fn-ref parse");
    // Function-reference fixture should parse captures and closure calls
    // directly to quoted source.
    assert_quoted_mentions(&fn_ref, &["&", "/", "."]);

    let lambda_sugars = parse_quoted_program(
        "lambda_sugars.fz",
        include_str!("../../fixtures2/behavior/lambda_sugars.fz"),
        CodeId::ZERO,
        &tel,
    )
    .expect("lambda sugar parse");
    // Capture placeholders and capture expressions should enter quoted source
    // as compiler2-owned AST, not as old frontend nodes.
    assert_quoted_mentions(&lambda_sugars, &["&", "+", "fn", "when", "->"]);
}

#[test]
fn compiler2_frontdoor_parses_multiline_call_args_and_newline_pipe() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "multiline-call.fz",
        "fn main() do\n  finish(loop(\n    [1, 2, 3],\n    {:cont, 0},\n    fn (entry, inner) -> {:cont, entry + inner} end\n  ))\n  |> dbg()\nend\n",
        CodeId::ZERO, &tel,
    )
    .expect("multiline call args and newline pipe parse");
    assert_quoted_mentions(&root, &["finish", "loop", "|>", "dbg"]);
}

#[test]
fn compiler2_frontdoor_parses_assignment_rhs_after_newline() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "assignment-newline.fz",
        "fn main() do\n  x =\n    41\n  x + 1\nend\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("assignment rhs after newline parse");
    assert_quoted_mentions(&root, &["fn", "=", "+"]);
}

// The four cases below pin the grammar-owned eol/eoe model: newline
// continuation falls out of which token follows a run of physical
// newlines (infix-only tokens swallow it at tokenize time; the parser
// never peeks past a newline to decide). No test-only lexer/parser hooks
// are used — each asserts the real parse tree `parse_quoted_program`
// produces.

#[test]
fn compiler2_frontdoor_continues_expr_across_newline_after_operator() {
    // A binary operator at the END of a line (`+` here) continues onto the
    // next line: this must parse as the single call `1 + 2`, not as two
    // statements `1` followed by a dangling `+ 2`.
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "operator-trailing-newline.fz",
        "fn main() do\n  1 +\n    2\nend\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("trailing operator newline parse");
    let body = fn_do_body(&root).ast_node().expect("body cursor").expect("body node");
    assert_eq!(head_name(&body), "+", "newline after `+` must continue the expression");
    let args = body.tail.list_items().expect("+ args");
    assert_eq!(args.len(), 2);
    assert_eq!(args[0].int_value().expect("lhs"), 1);
    assert_eq!(args[1].int_value().expect("rhs"), 2);
}

#[test]
fn compiler2_frontdoor_continues_expr_across_newline_after_dot() {
    // `.` at the end of a line continues onto the next: `cfg.\n  value`
    // must parse as the single remote-access node `cfg.value`, not error
    // out looking for a field name and hit a newline instead.
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "dot-trailing-newline.fz",
        "fn main() do\n  cfg.\n    value\nend\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("trailing dot newline parse");
    let body = fn_do_body(&root).ast_node().expect("body cursor").expect("body node");
    assert_eq!(
        head_name(&body),
        ".",
        "newline after `.` must continue the remote access"
    );
    let tail = body.tail.list_items().expect(". tail");
    assert_eq!(tail.len(), 2);
    let target = tail[0].ast_node().expect("target cursor").expect("target node");
    assert_eq!(head_name(&target), "cfg");
    assert_eq!(tail[1].atom_name().expect("field atom"), "value");
}

#[test]
fn compiler2_frontdoor_separates_statements_at_a_bare_newline() {
    // Two expressions on separate lines with no continuing operator are
    // two statements (`eoe`-separated), not one: the block wraps them as
    // `__block__` with two independent children.
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "block-separation.fz",
        "fn main() do\n  a\n  b\nend\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("block separation parse");
    let body = fn_do_body(&root).ast_node().expect("body cursor").expect("body node");
    assert_eq!(head_name(&body), "__block__");
    let stmts = body.tail.list_items().expect("block items");
    assert_eq!(stmts.len(), 2);
    assert_eq!(
        head_name(&stmts[0].ast_node().expect("first cursor").expect("first node")),
        "a"
    );
    assert_eq!(
        head_name(&stmts[1].ast_node().expect("second cursor").expect("second node")),
        "b"
    );
}

#[test]
fn compiler2_frontdoor_leading_operator_starts_a_new_expression() {
    // The tricky disambiguation the old lookahead heuristic got wrong: a
    // `-` that LEADS a fresh line is a unary prefix starting a NEW
    // statement, never a continuation of the previous one. `a\n-b` is two
    // statements — `a`, then the unary call `-(b)` — not the single binary
    // expression `a - b`.
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "leading-operator-new-statement.fz",
        "fn main() do\n  a\n  -b\nend\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("leading operator new-statement parse");
    let body = fn_do_body(&root).ast_node().expect("body cursor").expect("body node");
    assert_eq!(
        head_name(&body),
        "__block__",
        "a bare newline before a leading `-` must not fuse the two statements into one binary expression"
    );
    let stmts = body.tail.list_items().expect("block items");
    assert_eq!(stmts.len(), 2);
    assert_eq!(
        head_name(&stmts[0].ast_node().expect("first cursor").expect("first node")),
        "a"
    );
    let second = stmts[1].ast_node().expect("second cursor").expect("second node");
    assert_eq!(head_name(&second), "-", "leading `-` parses as the unary operator");
    let unary_args = second.tail.list_items().expect("unary - args");
    assert_eq!(
        unary_args.len(),
        1,
        "unary `-` takes exactly one argument, not `a` and `b`"
    );
    assert_eq!(
        head_name(&unary_args[0].ast_node().expect("operand cursor").expect("operand node")),
        "b"
    );
}

#[test]
fn compiler2_frontdoor_leading_struct_literal_starts_a_new_expression() {
    // `%` is fz's OTHER dual prefix/infix token (like `-`): prefix it opens
    // a `%Foo{...}` struct literal, infix it is modulo. A `%` that LEADS a
    // fresh line is the struct-literal prefix starting a NEW statement, not
    // a modulo continuation of the previous line. `a\n%Foo{x: 1}` must parse
    // as two statements — `a`, then the struct `%Foo{x: 1}` — not the infix
    // `a % Foo` with a dangling `{x: 1}`.
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "leading-struct-new-statement.fz",
        "fn main() do\n  a\n  %Foo{x: 1}\nend\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("leading struct-literal new-statement parse");
    let body = fn_do_body(&root).ast_node().expect("body cursor").expect("body node");
    assert_eq!(
        head_name(&body),
        "__block__",
        "a bare newline before a leading `%` must not fuse the two statements into infix modulo"
    );
    let stmts = body.tail.list_items().expect("block items");
    assert_eq!(stmts.len(), 2);
    assert_eq!(
        head_name(&stmts[0].ast_node().expect("first cursor").expect("first node")),
        "a"
    );
    let second = stmts[1].ast_node().expect("second cursor").expect("second node");
    assert_eq!(
        head_name(&second),
        "%",
        "leading `%` parses as the struct-literal prefix"
    );
    let struct_args = second.tail.list_items().expect("% args");
    assert_eq!(
        struct_args.len(),
        2,
        "struct node is `%(alias, map)`, not infix `%(a, Foo)`"
    );
    let alias = struct_args[0].ast_node().expect("alias cursor").expect("alias node");
    assert_eq!(head_name(&alias), "__aliases__");
    assert_eq!(
        alias.tail.list_items().expect("alias segments")[0]
            .atom_name()
            .expect("alias segment atom"),
        "Foo"
    );
    assert_eq!(
        head_name(&struct_args[1].ast_node().expect("map cursor").expect("map node")),
        "%{}"
    );
}

#[test]
fn compiler2_frontdoor_parses_keyword_list_macro_heads() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "macro-heads.fz",
        "defmacro test(name_atom, [do: body]) do\n  {:fn, %{}, [{name_atom, %{}, []}, [{:do, body}]]}\nend\n\ndefmacro switching_macro(list, a, do: block) do\n  block\nend\n",
        CodeId::ZERO, &tel,
    )
    .expect("keyword list macro heads parse");
    assert_quoted_mentions(&root, &["defmacro", "test", "switching_macro", "do"]);
}

#[test]
fn compiler2_frontdoor_parses_with_expressions() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "with.fz",
        "fn main(v) do\n  with {:ok, x} <- v do x else :err -> 0 end\nend\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("quoted with parse");

    // Front door should quote `with` directly, including match bindings and
    // ordinary else clauses, instead of relying on the old parser AST.
    assert_quoted_mentions(&root, &["with", "<-", "else", "->"]);
}

#[test]
fn compiler2_frontdoor_parses_cond_and_remote_operator_capture_refs() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "cond_capture.fz",
        "fn main() do\n  cond do\n    false -> &Kernel.+/2\n    true -> &+/2\n  end\nend\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("quoted parse");

    // Front door should quote cond arms and both remote and bare operator
    // capture refs directly.
    assert_quoted_mentions(&root, &["cond", "&", "/", "+", "Kernel"]);
}

#[test]
fn compiler2_frontdoor_parses_attributes_protocols_impls_and_structs() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "surface.fz",
        "@moduledoc \"docs\"\n@type t :: integer\n@spec run(integer) :: integer\ndefstruct [name, age]\ndefprotocol Enumerable do\n  @doc \"reduce docs\"\n  fn reduce(xs, acc)\nend\ndefimpl Enumerable, for: List do\n  fn reduce(xs, acc), do: acc\nend\n",
        CodeId::ZERO, &tel,
    )
    .expect("quoted parse");

    // Front door should parse attribute/protocol/source-declaration forms
    // directly to quoted source.
    assert_quoted_mentions(
        &root,
        &["@moduledoc", "@type", "@spec", "defstruct", "defprotocol", "defimpl"],
    );
}

#[test]
fn compiler2_frontdoor_parses_maps_structs_bitstrings_and_patterns() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "shapes.fz",
        "fn shapes(x :: integer, ref) do\n  literal = %{2 => x, a: 1}\n  updated = %{literal | a: 2, b: 3}\n  point = %Point{x: x, y: 1}\n  bytes = <<104, 105>>\n  case x do\n    %{name: n} -> n\n    {:ok, s} when s == \"hi\" -> s\n    [h | _] -> h\n    ^ref -> ref\n    <<len, payload::binary-size(len), rest::binary>> -> len\n  end\nend\n",
        CodeId::ZERO, &tel,
    )
    .expect("quoted parse");

    // Front door should parse typed params, maps, structs, bitstrings, and
    // pattern forms directly to quoted source.
    assert_quoted_mentions(&root, &["::", "%{}", "%", "<<>>", "|", "^", "when", "binary", "size"]);
}

#[test]
fn compiler2_frontdoor_quotes_postfix_bracket_access_as_access_get() {
    let tel = ConfiguredTelemetry::new();
    let root =
        parse_quoted_program("map_access.fz", "fn main(), do: m[:a]\n", CodeId::ZERO, &tel).expect("quoted parse");

    let items = root.cursor().list_items().expect("top-level items");
    let main = items[0].ast_node().expect("main cursor").expect("main node");
    let body = main.tail.list_items().expect("main args")[1]
        .list_items()
        .expect("main kw")[0]
        .tuple_items()
        .expect("main do tuple")[1]
        .ast_node()
        .expect("body cursor")
        .expect("body node");
    let callee = body.head.ast_node().expect("callee cursor").expect("callee node");

    assert_eq!(
        head_name(&callee),
        ".",
        "postfix bracket access should quote through an Access.get remote callee, like Elixir",
    );
    let callee_tail = callee.tail.list_items().expect("callee tail");
    let access = callee_tail[0].ast_node().expect("access cursor").expect("access alias");
    assert_eq!(head_name(&access), "__aliases__");
    assert_eq!(
        access.tail.list_atom_names().expect("access segments"),
        vec!["Access".to_string()]
    );
    assert_eq!(callee_tail[1].atom_name().expect("callee field"), "get");
    let args = body.tail.list_items().expect("access args");
    assert_eq!(args.len(), 2);
    assert_eq!(
        head_name(&args[0].ast_node().expect("base cursor").expect("base var")),
        "m"
    );
    assert_eq!(args[1].atom_name().expect("map key"), "a");
}

#[test]
fn compiler2_frontdoor_parses_runtime_bootstrap_sources_directly() {
    let tel = ConfiguredTelemetry::new();

    let prelude = parse_quoted_program(
        "runtime:runtime.fz",
        runtime_library::prelude_source(),
        CodeId::ZERO,
        &tel,
    )
    .expect("runtime prelude quoted parse");
    // Runtime prelude should quote operator import filters directly.
    assert_quoted_mentions(&prelude, &["import", "+", "dbg"]);

    for (name, source) in runtime_library::module_sources() {
        let root = parse_quoted_program(format!("runtime:{name}.fz"), source, CodeId::ZERO, &tel)
            .unwrap_or_else(|error| panic!("runtime module `{name}` should quote directly: {error}"));
        let module = root.cursor().list_items().expect("runtime module top-level items")[0]
            .ast_node()
            .expect("runtime module cursor")
            .expect("runtime module node");
        let head = head_name(&module);
        assert!(
            head == "defmodule" || head == "defprotocol",
            "runtime module `{name}` should still be ordinary module/protocol source"
        );
    }

    parse_quoted_program(
        "receive_selective_refs.fz",
        include_str!("../../fixtures2/behavior/receive_selective_refs.fz"),
        CodeId::ZERO,
        &tel,
    )
    .expect("receive selective refs quoted parse");
}

#[test]
fn compiler2_frontdoor_quotes_bootstrap_control_and_ffi_forms() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "bootstrap_surface.fz",
        "extern \"C\" fn libc::open(path :: cstring, flags :: integer, ...) :: integer\nfn run(pred) do\n  if pred.(1) do\n    receive do\n      {:ok, value} -> (fn (x) -> x end).(value)\n    after\n      500 -> nil\n    end\n  else\n    nil\n  end\nend\n",
        CodeId::ZERO, &tel,
    )
    .expect("quoted parse");
    // Bootstrap-shaped surface should quote extern/control/lambda forms
    // directly.
    assert_quoted_mentions(&root, &["extern", "if", "receive", "fn"]);

    let items = root.cursor().list_items().expect("top-level items");
    assert_eq!(items.len(), 2);

    let extern_node = items[0].ast_node().expect("extern cursor").expect("extern node");
    assert_eq!(head_name(&extern_node), "extern");
    let extern_args = extern_node.tail.list_items().expect("extern args");
    assert_eq!(extern_args[0].utf8_binary_text().expect("extern abi text"), "C");
    let extern_options = extern_args[1].map_entries().expect("extern options");
    assert_eq!(
        extern_options
            .iter()
            .find(|(key, _)| key.atom_name().ok().as_deref() == Some("name"))
            .expect("extern name entry")
            .1
            .utf8_binary_text()
            .expect("extern name text"),
        "libc::open"
    );
    assert_eq!(
        extern_options
            .iter()
            .find(|(key, _)| key.atom_name().ok().as_deref() == Some("variadic"))
            .expect("extern variadic entry")
            .1
            .atom_name()
            .expect("extern variadic atom"),
        "true"
    );

    let run_node = items[1].ast_node().expect("run cursor").expect("run node");
    let run_args = run_node.tail.list_items().expect("run args");
    let if_node = run_args[1].list_items().expect("run kw")[0]
        .tuple_items()
        .expect("run do tuple")[1]
        .ast_node()
        .expect("if cursor")
        .expect("if node");
    assert_eq!(head_name(&if_node), "if");

    let if_args = if_node.tail.list_items().expect("if args");
    let cond_call = if_args[0].ast_node().expect("if cond cursor").expect("if cond node");
    let cond_head = cond_call
        .head
        .ast_node()
        .expect("closure-call head cursor")
        .expect("closure-call head");
    assert_eq!(head_name(&cond_head), ".");
    let if_kw = if_args[1].list_items().expect("if kw list");
    let do_branch = if_kw[0].tuple_items().expect("if do tuple")[1]
        .ast_node()
        .expect("receive cursor")
        .expect("receive node");
    assert_eq!(head_name(&do_branch), "receive");

    let receive_args = do_branch.tail.list_items().expect("receive args");
    let receive_kw = receive_args[0].list_items().expect("receive kw");
    let do_clauses = receive_kw[0].tuple_items().expect("receive do tuple")[1]
        .list_items()
        .expect("receive clauses");
    let clause = do_clauses[0]
        .ast_node()
        .expect("receive clause cursor")
        .expect("receive clause");
    assert_eq!(head_name(&clause), "->");
    let lambda_call = clause.tail.list_items().expect("receive clause args")[1]
        .ast_node()
        .expect("lambda call cursor")
        .expect("lambda call");
    let lambda_dot = lambda_call
        .head
        .ast_node()
        .expect("lambda callee cursor")
        .expect("lambda callee");
    assert_eq!(head_name(&lambda_dot), ".");
    let lambda = lambda_dot.tail.list_items().expect("lambda dot args")[0]
        .ast_node()
        .expect("lambda root cursor")
        .expect("lambda root");
    assert_eq!(head_name(&lambda), "fn");
}

#[test]
fn compiler2_frontdoor_preserves_extern_symbol_calls_distinct_from_ascription() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "extern_call.fz",
        "fn main(), do: libc::open(path, flags, mode :: integer)\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("quoted parse");

    let items = root.cursor().list_items().expect("top-level items");
    assert_eq!(items.len(), 1);

    let main_node = items[0].ast_node().expect("main cursor").expect("main node");
    let main_args = main_node.tail.list_items().expect("main args");
    let body = main_args[1].list_items().expect("main kw")[0]
        .tuple_items()
        .expect("main do tuple")[1]
        .ast_node()
        .expect("call cursor")
        .expect("call node");
    assert_eq!(head_name(&body), "libc::open");

    let call_args = body.tail.list_items().expect("call args");
    assert_eq!(call_args.len(), 3);
    let typed_arg = call_args[2]
        .ast_node()
        .expect("typed arg cursor")
        .expect("typed arg node");
    assert_eq!(
        head_name(&typed_arg),
        "::",
        "call-arg ascription should survive while the extern symbol itself stays a direct call head",
    );
}

#[test]
fn compiler2_frontdoor_parses_operator_headed_function_defs() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "operator_head.fz",
        "fn left + right, do: left + right\n",
        CodeId::ZERO,
        &tel,
    )
    .expect("quoted parse");
    // Operator-headed function definitions should quote directly.
    assert_quoted_mentions(&root, &["fn", "+"]);
}

#[test]
fn compiler2_frontdoor_parses_complex_extern_signatures() {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(
        "extern_surface.fz",
        "extern \"C\" fn fz_spawn(() -> any) :: pid\nextern \"C\" fn fz_make_resource(t, (t) -> nil) :: resource(t) when t: integer | cpointer\n",
        CodeId::ZERO, &tel,
    )
    .expect("quoted parse");
    let items = root.cursor().list_items().expect("top-level externs");
    assert_eq!(items.len(), 2);

    let first = items[0].ast_node().expect("first extern cursor").expect("first extern");
    let first_args = first.tail.list_items().expect("first extern args");
    let first_options = first_args[1].map_entries().expect("first extern options");
    let first_params = map_value(&first_options, "params").list_items().expect("first params");
    assert_eq!(
        token_kinds(&first_params[0]),
        vec![Tok::LParen, Tok::RParen, Tok::Arrow, Tok::Ident("any".to_string())],
        "extern parameter signatures should be quoted as token payloads"
    );

    let second = items[1]
        .ast_node()
        .expect("second extern cursor")
        .expect("second extern");
    let second_args = second.tail.list_items().expect("second extern args");
    let second_options = second_args[1].map_entries().expect("second extern options");
    assert_eq!(
        token_kinds(map_value(&second_options, "return")),
        vec![
            Tok::Ident("resource".to_string()),
            Tok::LParen,
            Tok::Ident("t".to_string()),
            Tok::RParen,
        ],
        "extern return signatures should be quoted as token payloads"
    );
    let constraints = map_value(&second_options, "when")
        .list_items()
        .expect("second constraints");
    let constraint = constraints[0].tuple_items().expect("constraint keyword");
    assert_eq!(constraint[0].atom_name().expect("constraint name"), "t");
    assert_eq!(
        token_kinds(&constraint[1]),
        vec![
            Tok::Ident("integer".to_string()),
            Tok::Bar,
            Tok::Ident("cpointer".to_string()),
        ],
        "extern constraints should be quoted as token payloads"
    );
}
