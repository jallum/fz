use crate::ast::{Attribute, BitSize, BitType, Expr, Pattern, WithBinding};
use crate::parser::lexer::Tok;
use crate::telemetry::ConfiguredTelemetry;

use super::quoted_function::derive_function_surface;
use super::{CodeId, QuotedSourceRoot, parse_quoted_program};

fn grouped_function_root(source_name: &str, text: &str) -> QuotedSourceRoot {
    let tel = ConfiguredTelemetry::new();
    let root = parse_quoted_program(source_name, text, CodeId::ZERO, &tel).expect("quoted parse");
    let items = root.cursor().list_items().expect("top-level items");
    let item_roots = items.into_iter().map(|item| item.root()).collect::<Vec<_>>();
    root.interned_list_subroot(&item_roots)
        .expect("grouped function root should intern")
}

#[test]
fn compiler2_quoted_function_surface_derives_specs_and_bit_specs_without_old_parser() {
    let source = r#"
@spec pack(integer) :: binary
fn pack(x :: integer), do: <<x::integer-size(16), rest::binary-size(len)-unit(8)>>
"#;
    let root = grouped_function_root("pack.fz", source);
    let surface = derive_function_surface(&root).expect("derive function surface");

    let Attribute::Spec(spec) = &surface.attrs[0] else {
        panic!("expected @spec attr");
    };
    assert_eq!(spec.name, "pack");
    assert_eq!(spec.param_body_tokens.len(), 1);
    assert!(
        matches!(spec.param_body_tokens[0].0.as_slice(), [token] if matches!(token.tok, Tok::Ident(ref name) if name == "integer"))
    );
    assert!(
        matches!(spec.result_body_tokens.0.as_slice(), [token] if matches!(token.tok, Tok::Ident(ref name) if name == "binary"))
    );

    let annotation = surface.clauses[0].param_annotations[0]
        .as_ref()
        .expect("parameter annotation should decode");
    assert!(
        matches!(annotation.0.as_slice(), [token] if matches!(token.tok, Tok::Ident(ref name) if name == "integer"))
    );

    let Expr::Bitstring(fields) = &surface.clauses[0].body.node else {
        panic!("expected bitstring body");
    };
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].spec.ty, BitType::Integer);
    assert!(matches!(fields[0].spec.size, Some(BitSize::Literal(16))));
    assert_eq!(fields[1].spec.ty, BitType::Binary);
    assert!(matches!(fields[1].spec.size, Some(BitSize::Var(ref name)) if name == "len"));
    assert_eq!(fields[1].spec.unit, Some(8));
}

#[test]
fn compiler2_quoted_function_surface_derives_operator_specs_from_quoted_source() {
    let source = r#"
@spec integer + integer :: integer
fn left + right, do: left + right
"#;
    let root = grouped_function_root("plus.fz", source);
    let surface = derive_function_surface(&root).expect("derive function surface");

    assert_eq!(surface.name, "+");
    let Attribute::Spec(spec) = &surface.attrs[0] else {
        panic!("expected @spec attr");
    };
    assert_eq!(spec.name, "+");
    assert_eq!(spec.param_body_tokens.len(), 2);
    assert!(spec.param_body_tokens.iter().all(
        |body| matches!(body.0.as_slice(), [token] if matches!(token.tok, Tok::Ident(ref name) if name == "integer"))
    ));
    assert!(
        matches!(spec.result_body_tokens.0.as_slice(), [token] if matches!(token.tok, Tok::Ident(ref name) if name == "integer"))
    );
}

#[test]
fn compiler2_quoted_function_surface_derives_typed_operator_clause_annotations() {
    let source = r#"
fn left :: integer + right :: float, do: left + right
"#;
    let root = grouped_function_root("typed_plus.fz", source);
    let surface = derive_function_surface(&root).expect("derive function surface");

    assert_eq!(surface.name, "+");
    let left = surface.clauses[0].param_annotations[0]
        .as_ref()
        .expect("lhs annotation should decode");
    let right = surface.clauses[0].param_annotations[1]
        .as_ref()
        .expect("rhs annotation should decode");
    assert!(matches!(left.0.as_slice(), [token] if matches!(token.tok, Tok::Ident(ref name) if name == "integer")));
    assert!(matches!(right.0.as_slice(), [token] if matches!(token.tok, Tok::Ident(ref name) if name == "float")));
}

#[test]
fn compiler2_quoted_function_surface_derives_with_from_quoted_source() {
    let source = r#"
fn pick(v) do
  with {:ok, x} <- v do x else :err -> 0 end
end
"#;
    let root = grouped_function_root("with.fz", source);
    let surface = derive_function_surface(&root).expect("derive function surface");

    let Expr::With(bindings, body, else_clauses) = &surface.clauses[0].body.node else {
        panic!("expected with body");
    };
    assert_eq!(bindings.len(), 1);
    let WithBinding::Match(pattern, expr) = &bindings[0] else {
        panic!("expected match binding");
    };
    assert!(matches!(&pattern.node, Pattern::Tuple(parts) if parts.len() == 2));
    assert!(matches!(&expr.node, Expr::Var(name) if name == "v"));
    assert!(matches!(&body.node, Expr::Var(name) if name == "x"));
    assert_eq!(else_clauses.len(), 1);
}

#[test]
fn compiler2_quoted_function_surface_decodes_struct_literals_before_percent_operator() {
    let source = r#"
fn new(first, last, step), do: %Range{first: first, last: last, step: step}
"#;
    let root = grouped_function_root("range.fz", source);
    let surface = derive_function_surface(&root).expect("derive function surface");

    let Expr::Struct { module, fields } = &surface.clauses[0].body.node else {
        panic!("expected %Range{{}} to decode as a struct literal");
    };
    assert_eq!(module.dotted(), "Range");
    assert_eq!(
        fields.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>(),
        ["first", "last", "step"]
    );
}

/// A macro's quoted fragment gets rematerialized into a caller's heap by
/// `world::run_macro_on_source` -- byte offsets intact -- and decoded there
/// with no external code id at all (`derive_function_surface` takes only the
/// source root). A decoded token's span must still name the file it was
/// actually lexed from: the code id is embedded in the token tuple at encode
/// time, so it travels with the token instead of being reattached from the
/// decode call site. This test lexes a fragment under one real submitted
/// `CodeId` and asserts the decoded token span keeps that id -- there is no
/// decode-time code id that could override it.
#[test]
fn a_decoded_token_span_carries_its_own_files_baked_code_id() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = super::Compiler2::new(&tel);
    let file_code = compiler.submit_code(super::CodeSubmission {
        name: Some("macro_file.fz".to_string()),
        text: String::new(),
    });

    let source = "fn tmpl(), do: x :: integer\n";
    let root = parse_quoted_program("macro_file.fz", source, file_code, &tel).expect("quoted parse");
    let items = root.cursor().list_items().expect("top-level items");
    let item_roots = items.into_iter().map(|item| item.root()).collect::<Vec<_>>();
    let grouped = root
        .interned_list_subroot(&item_roots)
        .expect("grouped function root should intern");

    let surface = derive_function_surface(&grouped).expect("derive function surface");

    let Expr::Ascribe(_, type_expr) = &surface.clauses[0].body.node else {
        panic!("expected an ascribed body expression");
    };
    let token = type_expr
        .0
        .first()
        .expect("type expr body should carry at least one token");
    assert_eq!(
        token.span.code_id,
        crate::source::Id(file_code.as_u32()),
        "a decoded token must carry the code id of the file it was actually lexed from"
    );
}

/// The AST-node sibling of the token test above: `span_from_meta` used to
/// build a decoded `Expr`/`Pattern` span from a caller-supplied `code_id`
/// plus the node's own `start`/`length` -- the same external-reattachment
/// hazard the token fix closed, just one layer up. A macro's quoted fragment
/// is rematerialized into a caller's heap with its `__fz_span__` meta
/// untouched, and decoding it used to mislabel which file the *expression*
/// span (not just its inner type-expr tokens) named. Every `__fz_span__` now
/// bakes its own originating code id at emit time, so `span_from_meta` reads
/// it back from the node -- and `derive_function_surface` no longer even takes
/// a code id, so there is nothing external left to override it. This test
/// lexes a fragment under one real submitted `CodeId` and asserts the decoded
/// expression span keeps that id.
#[test]
fn a_decoded_ast_node_meta_span_carries_its_own_files_baked_code_id() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = super::Compiler2::new(&tel);
    let file_code = compiler.submit_code(super::CodeSubmission {
        name: Some("macro_file.fz".to_string()),
        text: String::new(),
    });

    let source = "fn tmpl(), do: x :: integer\n";
    let root = parse_quoted_program("macro_file.fz", source, file_code, &tel).expect("quoted parse");
    let items = root.cursor().list_items().expect("top-level items");
    let item_roots = items.into_iter().map(|item| item.root()).collect::<Vec<_>>();
    let grouped = root
        .interned_list_subroot(&item_roots)
        .expect("grouped function root should intern");

    let surface = derive_function_surface(&grouped).expect("derive function surface");

    let body_span = surface.clauses[0].body.span;
    assert_eq!(
        body_span.code_id,
        crate::source::Id(file_code.as_u32()),
        "a decoded expression's own __fz_span__ must carry the code id of the file it was actually parsed from"
    );
}
