use crate::ast::{Attribute, BitSize, BitType, Expr, Pattern, WithBinding};
use crate::parser::lexer::Tok;
use crate::telemetry::ConfiguredTelemetry;

use super::quoted_function::derive_function_surface;
use super::{QuotedSourceHeap, QuotedSourceMetadata, QuotedSourceRoot, parse_quoted_program};

fn grouped_function_root(source_name: &str, text: &str) -> (QuotedSourceRoot, crate::source::SourceMap) {
    let tel = ConfiguredTelemetry::new();
    let mut sources = crate::source::SourceMap::default();
    let version = sources.add_code(Some(source_name), text);
    let root = parse_quoted_program(&sources, version, &tel).expect("quoted parse");
    let items = root.cursor().list_items().expect("top-level items");
    let item_roots = items.into_iter().map(|item| item.root()).collect::<Vec<_>>();
    let grouped = root
        .interned_list_subroot(&item_roots)
        .expect("grouped function root should intern");
    (grouped, sources)
}

#[test]
fn projected_module_identity_survives_call_and_function_reference_decoding() {
    use super::{QuotedSourceHeap, QuotedSourceMetadata};
    use crate::modules::identity::{ModuleDenotation, ModuleName};
    let heap = std::rc::Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let mut sources = crate::source::SourceMap::new();
    let version = sources.add_code(Some("projected-module.fz"), "A.B.C");
    let span = crate::source::Span::new(version, 0, 5);
    let module = ModuleDenotation::ProtocolImpl {
        protocol: ModuleName::parse_dotted("A").unwrap(),
        target: ModuleName::parse_dotted("B.C").unwrap(),
    };
    let empty = QuotedSourceMetadata::default();
    let meta = QuotedSourceMetadata {
        module: Some(module.clone()),
        span: Some(span),
        ..Default::default()
    };
    // Even a non-alias display head/tail is inert once the module is resolved.
    let alias = builder
        .ast_node(builder.int(99), &meta, builder.atom("display"))
        .unwrap();
    let target = builder.call(".", &empty, &[alias, builder.atom("val")]).unwrap();
    let call = builder.call_callee(target, &empty, &[builder.int(1)]).unwrap();
    let quotient = builder.call("/", &empty, &[target, builder.int(1)]).unwrap();
    let reference = builder.call("&", &empty, &[quotient]).unwrap();
    let body = builder.call("{}", &empty, &[call, reference]).unwrap();
    let head = builder.call("probe", &empty, &[]).unwrap();
    let keyword = builder.list(&[builder.keyword("do", body).unwrap()]).unwrap();
    let function = builder.call("fn", &empty, &[head, keyword]).unwrap();
    let source = builder.root(builder.list(&[function]).unwrap()).unwrap();
    assert!(
        derive_function_surface(&source, &crate::source::SourceMap::new()).is_err(),
        "a resolved module identity cannot bypass validation of its exact source version"
    );
    let decoded = derive_function_surface(&source, &sources).unwrap();
    let Expr::Tuple(items) = &decoded.clauses[0].body.node else {
        panic!("tuple body")
    };
    let Expr::Call(target, _) = &items[0].node else {
        panic!("qualified call")
    };
    let Expr::Index(module_expr, _) = &target.node else {
        panic!("qualified target")
    };
    assert_eq!(
        module_expr.span, span,
        "typed module decoding retains exact node provenance"
    );
    let call = crate::ast::CallableName::for_call(&target.node, 1).unwrap();
    assert_eq!(call.module, Some(module.clone()));
    assert_eq!(call.name, "val");
    let Expr::FnRef { name, arity } = &items[1].node else {
        panic!("explicit function reference")
    };
    assert_eq!(name.module, Some(module));
    assert_eq!(name.name, "val");
    assert_eq!(*arity, 1);
}

#[test]
fn source_lambda_occurrences_survive_cloning_and_decode_retries() {
    let (root, sources) = grouped_function_root(
        "lambda_occurrences.fz",
        "fn choose(0), do: {fn () -> fn () -> 1 end end, fn () -> 2 end}\nfn choose(1), do: fn () -> 3 end\n",
    );
    fn occurrences(surface: &crate::function_surface::FunctionSurface) -> [crate::ast::LambdaOccurrence; 4] {
        let Expr::Tuple(items) = &surface.clauses[0].body.node else {
            panic!("tuple body")
        };
        let Expr::Lambda {
            occurrence: outer,
            clauses,
        } = &items[0].node
        else {
            panic!("outer lambda")
        };
        let Expr::Lambda { occurrence: inner, .. } = &clauses[0].body.node else {
            panic!("nested lambda")
        };
        let Expr::Lambda {
            occurrence: sibling, ..
        } = &items[1].node
        else {
            panic!("sibling lambda")
        };
        let Expr::Lambda {
            occurrence: next_clause,
            ..
        } = &surface.clauses[1].body.node
        else {
            panic!("next clause lambda")
        };
        [*outer, *inner, *sibling, *next_clause]
    }
    let decoded = derive_function_surface(&root, &sources).expect("decode source");
    let first = occurrences(&decoded);
    assert_eq!(
        first.iter().copied().collect::<std::collections::HashSet<_>>().len(),
        4,
        "nested lambdas, siblings, and grouped clauses are distinct source occurrences"
    );
    let cloned = decoded.clone();
    assert_ne!(decoded.clauses.as_ptr(), cloned.clauses.as_ptr());
    assert_eq!(first, occurrences(&cloned), "lowering clones retain source identity");
    assert_eq!(
        first,
        occurrences(&derive_function_surface(&root, &sources).expect("retry decode")),
        "retrying unchanged source does not mint new occurrences"
    );
}

#[test]
fn compiler2_quoted_function_surface_derives_specs_and_bit_specs_without_old_parser() {
    let source = r#"
@spec pack(integer) :: binary
fn pack(x :: integer), do: <<x::integer-size(16), rest::binary-size(len)-unit(8)>>
"#;
    let (root, sources) = grouped_function_root("pack.fz", source);
    let surface = derive_function_surface(&root, &sources).expect("derive function surface");

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
fn compiler2_unsuffixed_binary_expression_field_owns_a_binary_spec() {
    let (root, sources) = grouped_function_root("binary_field.fz", "fn pack(x), do: <<\"x\", x>>\n");
    let surface = derive_function_surface(&root, &sources).expect("derive function surface");

    let Expr::Bitstring(fields) = &surface.clauses[0].body.node else {
        panic!("expected bitstring body");
    };
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].spec.ty, BitType::Binary);
    assert!(fields[0].spec.size.is_none());
    assert_eq!(fields[1].spec.ty, BitType::Integer);
}

#[test]
fn compiler2_quoted_function_surface_derives_operator_specs_from_quoted_source() {
    let source = r#"
@spec integer + integer :: integer
fn left + right, do: left + right
"#;
    let (root, sources) = grouped_function_root("plus.fz", source);
    let surface = derive_function_surface(&root, &sources).expect("derive function surface");

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
    let (root, sources) = grouped_function_root("typed_plus.fz", source);
    let surface = derive_function_surface(&root, &sources).expect("derive function surface");

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
    let (root, sources) = grouped_function_root("with.fz", source);
    let surface = derive_function_surface(&root, &sources).expect("derive function surface");

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
    let (root, sources) = grouped_function_root("range.fz", source);
    let surface = derive_function_surface(&root, &sources).expect("derive function surface");

    let Expr::Struct { module, fields } = &surface.clauses[0].body.node else {
        panic!("expected %Range{{}} to decode as a struct literal");
    };
    assert_eq!(module.to_string(), "Range");
    assert_eq!(
        fields.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>(),
        ["first", "last", "step"]
    );
}

#[test]
fn source_less_ast_child_stays_source_less_under_a_spanned_parent() {
    let mut sources = crate::source::SourceMap::default();
    let version = sources.add_code(Some("generated-child.fz"), "fn main(), do: generated\n");
    let heap = std::rc::Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let parent_meta = QuotedSourceMetadata {
        span: Some(crate::source::Span::new(version, 0, 24)),
        ..QuotedSourceMetadata::default()
    };
    let generated_meta = QuotedSourceMetadata {
        span: Some(crate::source::Span::DUMMY),
        ..QuotedSourceMetadata::default()
    };
    let head = builder.call("main", &parent_meta, &[]).expect("function head");
    let body = builder
        .variable("generated", &generated_meta)
        .expect("source-less generated variable");
    let do_entry = builder.keyword("do", body).expect("do entry");
    let options = builder.list(&[do_entry]).expect("function options");
    let function = builder
        .call("fn", &parent_meta, &[head, options])
        .expect("function form");
    let items = builder.list(&[function]).expect("function list");
    let root = builder.root(items).expect("quoted function root");

    let surface = derive_function_surface(&root, &sources).expect("generated child decodes");
    assert!(
        surface.clauses[0].body.span.is_dummy(),
        "missing child provenance must not be reconstructed from its parent"
    );
}

/// A macro's quoted fragment gets rematerialized into a caller's heap by
/// `world::run_macro_on_source` -- byte offsets intact -- and decoded there
/// against the World's authoritative `SourceMap`. The token tuple carries its
/// exact immutable version rather than accepting provenance from the decode
/// site. This test lexes a fragment under one real submitted `SourceVersion`
/// and asserts the decoded token span keeps that version -- there is no
/// decode-time source identity that could override it.
#[test]
fn a_decoded_token_span_retains_its_exact_source_version() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = super::Compiler2::new(tel);
    let source = "fn tmpl(), do: x :: integer\n";
    let owner = compiler.submit_code(super::CodeSubmission {
        name: Some("macro_file.fz".to_string()),
        text: source.to_string(),
    });
    let version = compiler
        .world()
        .source_version(owner)
        .expect("submitted source version");

    let source_map = compiler.world().source_map();
    let root = parse_quoted_program(&source_map.borrow(), version, compiler.telemetry()).expect("quoted parse");
    let items = root.cursor().list_items().expect("top-level items");
    let item_roots = items.into_iter().map(|item| item.root()).collect::<Vec<_>>();
    let grouped = root
        .interned_list_subroot(&item_roots)
        .expect("grouped function root should intern");

    let surface = derive_function_surface(&grouped, &source_map.borrow()).expect("derive function surface");

    let Expr::Ascribe(_, type_expr) = &surface.clauses[0].body.node else {
        panic!("expected an ascribed body expression");
    };
    let token = type_expr
        .0
        .first()
        .expect("type expr body should carry at least one token");
    assert_eq!(
        token.span.source_version, version,
        "a decoded token must retain the immutable source version it was lexed from"
    );
}

/// AST-node metadata carries the same exact immutable version as token
/// payloads. The decoder reads that version from the node itself; no lexical
/// publisher or caller can reattach the node to a different source.
#[test]
fn a_decoded_ast_node_meta_span_retains_its_exact_source_version() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = super::Compiler2::new(tel);
    let source = "fn tmpl(), do: x :: integer\n";
    let owner = compiler.submit_code(super::CodeSubmission {
        name: Some("macro_file.fz".to_string()),
        text: source.to_string(),
    });
    let version = compiler
        .world()
        .source_version(owner)
        .expect("submitted source version");

    let source_map = compiler.world().source_map();
    let root = parse_quoted_program(&source_map.borrow(), version, compiler.telemetry()).expect("quoted parse");
    let items = root.cursor().list_items().expect("top-level items");
    let item_roots = items.into_iter().map(|item| item.root()).collect::<Vec<_>>();
    let grouped = root
        .interned_list_subroot(&item_roots)
        .expect("grouped function root should intern");

    let surface = derive_function_surface(&grouped, &source_map.borrow()).expect("derive function surface");

    let body_span = surface.clauses[0].body.span;
    assert_eq!(
        body_span.source_version, version,
        "a decoded expression must retain the immutable source version it was parsed from"
    );
}

#[test]
fn compiler2_quoted_function_surface_carries_a_heredoc_doc_whole() {
    // A one-line `@doc` was all the attribute had ever been handed, because
    // `"""` lexed as three quote characters rather than a delimiter. The
    // attribute already took a string token, so a heredoc that lexes to one
    // needs nothing further from it -- this pins that, text and all, so the
    // library can carry Elixir-shaped docs instead of one-line labels.
    let source = "@doc \"\"\"\nAdds one.\n\n## Examples\n\n    bump(1) == 2\n\"\"\"\nfn bump(n), do: n + 1\n";
    let (root, sources) = grouped_function_root("bump.fz", source);
    let surface = derive_function_surface(&root, &sources).expect("derive function surface");

    let Attribute::Doc(doc) = &surface.attrs[0] else {
        panic!("expected @doc attr, got {:?}", surface.attrs[0]);
    };
    assert_eq!(
        doc, "Adds one.\n\n## Examples\n\n    bump(1) == 2\n",
        "the doc should arrive with its blank lines and its example's indentation intact"
    );
}
