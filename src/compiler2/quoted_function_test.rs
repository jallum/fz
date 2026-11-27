use crate::ast::{Attribute, BinOp, BitSize, BitType, Expr, Pattern, PatternBitSize, Var, WithBinding};
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
fn a_module_atom_is_an_exact_target_for_calls_and_function_references() {
    use super::{QuotedSourceHeap, QuotedSourceMetadata};
    use crate::modules::identity::ModuleName;
    let heap = std::rc::Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let module = ModuleName::parse_dotted("A.B.C").unwrap();
    let empty = QuotedSourceMetadata::default();
    let atom = builder.atom(&module.atom_name());
    let target = builder.call(".", &empty, &[atom, builder.atom("val")]).unwrap();
    let call = builder.call_callee(target, &empty, &[builder.int(1)]).unwrap();
    let no_parens = QuotedSourceMetadata {
        no_parens: true,
        ..QuotedSourceMetadata::default()
    };
    let named = builder.call_callee(target, &no_parens, &[]).unwrap();
    let quotient = builder.call("/", &empty, &[named, builder.int(1)]).unwrap();
    let reference = builder.call("&", &empty, &[quotient]).unwrap();
    let body = builder.call("{}", &empty, &[call, reference]).unwrap();
    let head = builder.call("probe", &empty, &[]).unwrap();
    let keyword = builder.list(&[builder.keyword("do", body).unwrap()]).unwrap();
    let function = builder.call("def", &empty, &[head, keyword]).unwrap();
    let source = builder.root(builder.list(&[function]).unwrap()).unwrap();
    let decoded = derive_function_surface(&source, &crate::source::SourceMap::new()).unwrap();
    let Expr::Tuple(items) = &decoded.clauses[0].body.node else {
        panic!("tuple body")
    };
    let Expr::Call(target, _) = &items[0].node else {
        panic!("qualified call")
    };
    let crate::ast::Callee::Name(call) = crate::ast::Callee::for_call(&target.node, 1).unwrap() else {
        panic!("a qualified source call names its callee")
    };
    assert_eq!(call.module, Some(crate::ast::ModuleTarget::Exact(module.clone())));
    assert_eq!(call.name, "val");
    let Expr::FnRef { name, arity } = &items[1].node else {
        panic!("explicit function reference")
    };
    assert_eq!(name.module, Some(crate::ast::ModuleTarget::Exact(module)));
    assert_eq!(name.name, "val");
    assert_eq!(*arity, 1);
}

#[test]
fn source_lambda_occurrences_survive_cloning_and_decode_retries() {
    let (root, sources) = grouped_function_root(
        "lambda_occurrences.fz",
        "def choose(0), do: {fn () -> fn () -> 1 end end, fn () -> 2 end}\ndef choose(1), do: fn () -> 3 end\n",
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
        first.iter().copied().collect::<crate::fast_hash::HashSet<_>>().len(),
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
def pack(x :: integer), do: <<x::integer-size(16), rest::binary-size(len)-unit(8)>>
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
    assert!(matches!(fields[1].spec.size, Some(BitSize::Var(ref name)) if name.name == "len"));
    assert_eq!(fields[1].spec.unit, Some(8));
}

#[test]
fn compiler2_bitstring_size_written_as_an_expression_decodes_to_that_expression() {
    let (root, sources) = grouped_function_root(
        "size_expression.fz",
        "def read(<<n, body::binary-size(n * 2 - 1)>>), do: body\n",
    );
    let surface = derive_function_surface(&root, &sources).expect("derive function surface");

    let Pattern::Bitstring(fields) = &surface.clauses[0].params[0].node else {
        panic!("expected bitstring parameter");
    };
    assert!(matches!(
        fields[1].spec.size,
        Some(PatternBitSize::Expr(ref size)) if matches!(size.node, Expr::BinOp(BinOp::Sub, _, _))
    ));
}

#[test]
fn compiler2_unsuffixed_binary_expression_field_owns_a_binary_spec() {
    let (root, sources) = grouped_function_root("binary_field.fz", "def pack(x), do: <<\"x\", x>>\n");
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
def left + right, do: left + right
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
fn compiler2_quoted_function_surface_derives_a_unary_operator_spec_from_quoted_source() {
    let source = r#"
@spec +(integer) :: integer
def +(x :: integer), do: x
"#;
    let (root, sources) = grouped_function_root("unary_plus.fz", source);
    let surface = derive_function_surface(&root, &sources).expect("derive function surface");

    assert_eq!(surface.name, "+");
    let Attribute::Spec(spec) = &surface.attrs[0] else {
        panic!("expected @spec attr");
    };
    assert_eq!(spec.name, "+");
    assert_eq!(
        spec.param_body_tokens.len(),
        1,
        "a unary operator spec declares one parameter"
    );
}

#[test]
fn compiler2_quoted_function_surface_derives_typed_operator_clause_annotations() {
    let source = r#"
def (left :: integer) + (right :: float), do: left + right
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
def pick(v) do
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
    assert!(matches!(&expr.node, Expr::Var(name) if name.name == "v"));
    assert!(matches!(&body.node, Expr::Var(name) if name.name == "x"));
    assert_eq!(else_clauses.len(), 1);
}

#[test]
fn compiler2_quoted_function_surface_decodes_struct_literals_before_percent_operator() {
    let source = r#"
def new(first, last, step), do: %Range{first: first, last: last, step: step}
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
    let version = sources.add_code(Some("generated-child.fz"), "def main(), do: generated\n");
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
        .variable(&Var::user("generated"), &generated_meta)
        .expect("source-less generated variable");
    let do_entry = builder.keyword("do", body).expect("do entry");
    let options = builder.list(&[do_entry]).expect("function options");
    let function = builder
        .call("def", &parent_meta, &[head, options])
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
    let source = "def tmpl(), do: x :: integer\n";
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
    let source = "def tmpl(), do: x :: integer\n";
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

// ----- `<>` and `++` in patterns -----------------------------------------

fn surface_of(text: &str) -> crate::function_surface::FunctionSurface {
    let (root, sources) = grouped_function_root("concat_pattern.fz", text);
    derive_function_surface(&root, &sources).expect("derive function surface")
}

fn refusal_of(text: &str) -> (crate::compiler2::QuotedSourceError, String) {
    let (root, sources) = grouped_function_root("concat_pattern.fz", text);
    let error = derive_function_surface(&root, &sources).expect_err("the pattern is refused");
    let covered = error
        .span()
        .map(|span| sources.code(span.source_version).bytes[span.start as usize..span.end as usize].to_string())
        .unwrap_or_default();
    (error, covered)
}

/// A pattern rendered as text, spans left out, so two spellings can be
/// compared for being the same pattern.
fn shape(pattern: &Pattern) -> String {
    match pattern {
        Pattern::Wildcard => "_".to_string(),
        Pattern::Var(var) => var.name.clone(),
        Pattern::Pinned(var) => format!("^{}", var.name),
        Pattern::Both(left, right) => format!("{} = {}", shape(&left.node), shape(&right.node)),
        Pattern::Int(value) => value.to_string(),
        Pattern::Binary(bytes) => format!("{:?}", String::from_utf8_lossy(bytes)),
        Pattern::List(items, tail) => {
            let items = items
                .iter()
                .map(|item| shape(&item.node))
                .collect::<Vec<_>>()
                .join(", ");
            match tail {
                Some(tail) => format!("[{items} | {}]", shape(&tail.node)),
                None => format!("[{items}]"),
            }
        }
        Pattern::Bitstring(fields) => {
            let fields = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}::{:?}/{:?}",
                        shape(&field.value.node),
                        field.spec.ty,
                        field.spec.size
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("<<{fields}>>")
        }
        other => format!("{other:?}"),
    }
}

fn head_shape(text: &str) -> String {
    shape(&surface_of(text).clauses[0].params[0].node)
}

fn case_shape(clause_pattern: &str) -> String {
    let surface = surface_of(&format!(
        "def f(s) do\n  case s do\n    {clause_pattern} -> 1\n  end\nend\n"
    ));
    let Expr::Case(_, clauses) = &surface.clauses[0].body.node else {
        panic!("expected a case body");
    };
    shape(&clauses[0].pattern.node)
}

#[test]
fn a_prefix_in_a_function_head_is_the_bitstring_it_stands_for() {
    assert_eq!(
        head_shape("def f(\"--\" <> r), do: r\n"),
        head_shape("def f(<<\"--\", r::binary>>), do: r\n"),
    );
}

#[test]
fn a_prefix_in_a_case_clause_is_the_bitstring_it_stands_for() {
    assert_eq!(case_shape("\"--\" <> r"), case_shape("<<\"--\", r::binary>>"));
}

#[test]
fn a_prefix_in_a_match_is_the_bitstring_it_stands_for() {
    let surface = surface_of("def f(s) do\n  \"--\" <> r = s\n  r\nend\n");
    let Expr::Block(exprs) = &surface.clauses[0].body.node else {
        panic!("expected a block body");
    };
    let Expr::Match(pattern, _) = &exprs[0].node else {
        panic!("expected a match");
    };
    assert_eq!(
        shape(&pattern.node),
        head_shape("def f(<<\"--\", r::binary>>), do: r\n")
    );
}

#[test]
fn a_chain_of_prefixes_flattens_into_one_bitstring() {
    let flat = "<<\"a\", \"b\", r::binary>>";
    assert_eq!(case_shape("\"a\" <> \"b\" <> r"), case_shape(flat));
    assert_eq!(case_shape("\"a\" <> (\"b\" <> r)"), case_shape(flat));
    assert_eq!(
        head_shape("def f(\"a\" <> \"b\" <> r), do: r\n"),
        head_shape(&format!("def f({flat}), do: r\n"))
    );
}

#[test]
fn an_empty_prefix_binds_the_whole_subject() {
    assert_eq!(case_shape("\"\" <> r"), case_shape("<<\"\", r::binary>>"));
}

#[test]
fn a_literal_alone_after_the_operator_matches_only_that_literal() {
    assert_eq!(case_shape("\"--\" <> \"\""), case_shape("<<\"--\", \"\">>"));
}

#[test]
fn a_bitstring_after_the_operator_continues_the_same_bitstring() {
    assert_eq!(
        case_shape("\"--\" <> <<c, r::binary>>"),
        case_shape("<<\"--\", c, r::binary>>")
    );
}

#[test]
fn a_pinned_prefix_is_sized_by_its_pinned_value() {
    let pinned = case_shape("^p <> r");
    assert_eq!(pinned, case_shape("<<^p::binary, r::binary>>"));
    assert!(
        pinned.contains("ByteSizeOf"),
        "the pinned segment names the value whose byte size it takes: {pinned}"
    );
}

#[test]
fn a_literal_list_before_plus_plus_is_the_list_pattern_it_stands_for() {
    assert_eq!(case_shape("[1, 2] ++ r"), case_shape("[1, 2 | r]"));
    assert_eq!(case_shape("[1] ++ [2] ++ r"), case_shape("[1, 2 | r]"));
    assert_eq!(case_shape("[a] ++ r"), case_shape("[a | r]"));
    assert_eq!(case_shape("[1] ++ [2]"), case_shape("[1, 2]"));
    assert_eq!(case_shape("[] ++ r"), case_shape("r"));
    assert_eq!(
        head_shape("def f([1, 2] ++ r), do: r\n"),
        head_shape("def f([1, 2 | r]), do: r\n")
    );
}

#[test]
fn a_user_written_kernel_concat_call_is_not_the_operator() {
    let (error, covered) = refusal_of("def f(s) do\n  case s do\n    Kernel.<>(\"a\", r) -> r\n  end\nend\n");
    assert_eq!(
        error.user_code(),
        Some(crate::diag::codes::PARSE_CONCAT_PATTERN_OPERAND),
        "{error}"
    );
    assert!(covered.contains("Kernel.<>"), "span covers the call: {covered:?}");
}

#[test]
fn a_user_written_kernel_list_concat_call_is_not_the_operator() {
    let (error, _) = refusal_of("def f(s) do\n  case s do\n    Kernel.++([1], r) -> r\n  end\nend\n");
    assert_eq!(
        error.user_code(),
        Some(crate::diag::codes::PARSE_CONCAT_PATTERN_OPERAND),
        "{error}"
    );
}

fn assert_refused(pattern: &str, message: &str, covered: &str) {
    let (error, text) = refusal_of(&format!("def f(s) do\n  case s do\n    {pattern} -> 1\n  end\nend\n"));
    assert_eq!(
        error.user_code(),
        Some(crate::diag::codes::PARSE_CONCAT_PATTERN_OPERAND),
        "{pattern}: {error}"
    );
    assert_eq!(error.to_string(), message, "{pattern}");
    assert_eq!(text, covered, "{pattern}: span");
}

#[test]
fn a_variable_before_the_binary_operator_is_refused_where_it_stands() {
    assert_refused(
        "a <> r",
        "cannot perform prefix match because the left operand of <> has unknown size. The left operand of <> inside a match should either be a literal binary or an existing variable with the pin operator (such as ^some_var). Got: a",
        "a",
    );
}

#[test]
fn an_underscore_before_the_binary_operator_is_refused_where_it_stands() {
    assert_refused(
        "_ <> r",
        "cannot perform prefix match because the left operand of <> has unknown size. The left operand of <> inside a match should either be a literal binary or an existing variable with the pin operator (such as ^some_var). Got: _",
        "_",
    );
}

#[test]
fn a_variable_inside_a_chain_is_refused_where_it_stands() {
    assert_refused(
        "\"a\" <> b <> r",
        "cannot perform prefix match because the left operand of <> has unknown size. The left operand of <> inside a match should either be a literal binary or an existing variable with the pin operator (such as ^some_var). Got: b",
        "b",
    );
}

#[test]
fn a_number_operand_of_the_binary_operator_is_refused() {
    assert_refused("1 <> r", "expected binary argument in <> operator but got: 1", "1 <> r");
}

#[test]
fn an_atom_operand_of_the_binary_operator_is_refused() {
    assert_refused(
        "\"a\" <> :b",
        "expected binary argument in <> operator but got: :b",
        "\"a\" <> :b",
    );
}

#[test]
fn a_list_operand_of_the_binary_operator_is_refused() {
    assert_refused(
        "[1] <> r",
        "expected binary argument in <> operator but got: [1]",
        "[1] <> r",
    );
}

#[test]
fn a_tuple_operand_of_the_binary_operator_is_refused_where_it_stands() {
    assert_refused(
        "{1} <> r",
        "a bitstring only accepts binaries, numbers, and variables inside a match, got: {1}",
        "{1}",
    );
}

#[test]
fn a_variable_before_plus_plus_is_refused_where_it_stands() {
    assert_refused(
        "a ++ r",
        "invalid argument for ++ operator inside a match, expected a literal proper list, got: a",
        "a",
    );
}

#[test]
fn a_binary_before_plus_plus_is_refused() {
    assert_refused(
        "\"a\" ++ r",
        "invalid argument for ++ operator inside a match, expected a literal proper list, got: \"a\"",
        "\"a\" ++ r",
    );
}

#[test]
fn an_improper_list_before_plus_plus_is_refused() {
    assert_refused(
        "[1 | t] ++ r",
        "invalid argument for ++ operator inside a match, expected a literal proper list, got: [1 | t]",
        "[1 | t] ++ r",
    );
}

#[test]
fn a_variable_inside_a_plus_plus_chain_is_refused_where_it_stands() {
    assert_refused(
        "[1] ++ a ++ r",
        "invalid argument for ++ operator inside a match, expected a literal proper list, got: a",
        "a",
    );
}

/// A function head the way the expander leaves it after rewriting the one
/// operator in its first parameter: the stamped call instead of the bare
/// operator.
fn stamped_head_shape(text: &str) -> String {
    use super::source_sugar::rewrite_source_sugar;
    let (root, sources) = grouped_function_root("stamped_concat.fz", text);
    let def = root.cursor().list_items().expect("items").remove(0);
    let def_node = def.ast_node(&sources).expect("def").expect("def node");
    let def_args = def_node.tail.list_items().expect("def args");
    let head_node = def_args[0].ast_node(&sources).expect("head").expect("head node");
    let operator = head_node.tail.list_items().expect("head args").remove(0);
    let operator_node = operator.ast_node(&sources).expect("operator").expect("operator node");
    let rewritten = rewrite_source_sugar(
        &root,
        operator.root(),
        &operator_node,
        &sources,
        super::quoted_expander::ExpansionContext::Match,
    )
    .expect("rewrite")
    .expect("the operator is source sugar");
    let builder = root.builder();
    let head = builder
        .tuple(&[
            head_node.head.root(),
            head_node.meta.root(),
            builder.list(&[rewritten]).expect("args"),
        ])
        .expect("head");
    let def = builder
        .tuple(&[
            def_node.head.root(),
            def_node.meta.root(),
            builder.list(&[head, def_args[1].root()]).expect("def args"),
        ])
        .expect("def");
    let grouped = root.interned_list_subroot(&[def]).expect("grouped");
    shape(&derive_function_surface(&grouped, &sources).expect("derive").clauses[0].params[0].node)
}

#[test]
fn the_expanders_stamped_call_is_the_operator_it_was_made_from() {
    for (stamped, bare) in [
        ("def f(\"--\" <> r), do: r\n", "def f(<<\"--\", r::binary>>), do: r\n"),
        (
            "def f(\"a\" <> \"b\" <> r), do: r\n",
            "def f(<<\"a\", \"b\", r::binary>>), do: r\n",
        ),
        ("def f(^p <> r), do: r\n", "def f(<<^p::binary, r::binary>>), do: r\n"),
        ("def f([1, 2] ++ r), do: r\n", "def f([1, 2 | r]), do: r\n"),
        ("def f([1] ++ [2] ++ r), do: r\n", "def f([1, 2 | r]), do: r\n"),
    ] {
        assert_eq!(stamped_head_shape(stamped), head_shape(bare), "{stamped}");
    }
}

/// Intent: `=` in a pattern keeps both sides as patterns, in source order,
/// whichever side is the variable.
#[test]
fn an_equals_in_a_head_pattern_decodes_both_sides_as_patterns() {
    assert_eq!(head_shape("def f(m = [h | _]), do: m\n"), "m = [h | _]");
    assert_eq!(head_shape("def f([h | _] = m), do: m\n"), "[h | _] = m");
    assert_eq!(
        head_shape("def f([h | _] = [_, x | _] = l), do: l\n"),
        "[h | _] = [_, x | _] = l"
    );
}

#[test]
fn an_equals_in_a_case_pattern_decodes_both_sides_as_patterns() {
    assert_eq!(case_shape("[h | _] = [_ | t]"), "[h | _] = [_ | t]");
}

/// The body and rescue clauses of a `try` whose rescue section is
/// `rescue_clauses`, decoded the way a function body is.
fn try_of(rescue_clauses: &str) -> (Expr, Vec<crate::ast::RescueClause>) {
    let surface = surface_of(&format!(
        "def f() do\n  try do\n    1\n  rescue\n{rescue_clauses}\n  end\nend\n"
    ));
    let Expr::Try { body, rescue, .. } = &surface.clauses[0].body.node else {
        panic!("expected a try, got {:?}", surface.clauses[0].body.node);
    };
    (body.node.clone(), rescue.clone())
}

fn rescue_shape(clause: &crate::ast::RescueClause) -> (Option<String>, Vec<String>) {
    (
        clause.binding.as_ref().map(|binding| binding.node.name.clone()),
        clause
            .exceptions
            .iter()
            .map(|exception| exception.node.atom_name())
            .collect(),
    )
}

#[test]
fn the_five_rescue_head_shapes_decode_to_a_binding_and_an_exception_list() {
    let (body, rescue) = try_of(
        "    e -> 1\n    ArgumentError -> 2\n    [ArgumentError, RuntimeError] -> 3\n    e in ArgumentError -> 4\n    e in [ArgumentError, RuntimeError] -> 5",
    );
    assert!(matches!(body, Expr::Int(1)), "{body:?}");
    let shapes = rescue.iter().map(rescue_shape).collect::<Vec<_>>();
    let name = |alias: &str| format!("Elixir.{alias}");
    assert_eq!(
        shapes,
        vec![
            (Some("e".to_string()), vec![]),
            (None, vec![name("ArgumentError")]),
            (None, vec![name("ArgumentError"), name("RuntimeError")]),
            (Some("e".to_string()), vec![name("ArgumentError")]),
            (Some("e".to_string()), vec![name("ArgumentError"), name("RuntimeError")]),
        ]
    );
}

#[test]
fn a_wildcard_rescue_head_binds_nothing_and_catches_everything() {
    let (_, rescue) = try_of("    _ -> 1");
    assert_eq!(
        rescue.iter().map(rescue_shape).collect::<Vec<_>>(),
        vec![(None, vec![])]
    );
}

fn try_refusal(source: &str) -> (Option<crate::diag::codes::DiagCode>, String) {
    let (error, _) = refusal_of(source);
    (error.user_code(), error.to_string())
}

#[test]
fn a_rescue_head_outside_the_five_shapes_is_refused_with_elixirs_words() {
    assert_eq!(
        try_refusal("def f() do\n  try do\n    1\n  rescue\n    %{} -> 2\n  end\nend\n"),
        (
            Some(crate::diag::codes::PARSE_INVALID_TRY),
            "invalid \"rescue\" clause. The clause should match on an alias, a variable or be in the \"var in [alias]\" format. Got: %{}".to_string()
        )
    );
    assert_eq!(
        try_refusal("def f() do\n  try do\n    1\n  rescue\n    e in 1 -> 2\n  end\nend\n"),
        (
            Some(crate::diag::codes::PARSE_INVALID_TRY),
            "invalid \"rescue\" clause. The clause should match on an alias, a variable or be in the \"var in [alias]\" format. Got: e in 1".to_string()
        )
    );
}

#[test]
fn a_try_with_only_a_do_block_is_refused_with_elixirs_words() {
    assert_eq!(
        try_refusal("def f() do\n  try do\n    1\n  end\nend\n"),
        (
            Some(crate::diag::codes::PARSE_INVALID_TRY),
            "missing :catch/:rescue/:after option in \"try\"".to_string()
        )
    );
}

#[test]
fn a_try_section_given_twice_is_refused_with_elixirs_words() {
    assert_eq!(
        try_refusal("def f() do\n  try do\n    1\n  rescue\n    e -> 2\n  rescue\n    e -> 3\n  end\nend\n"),
        (
            Some(crate::diag::codes::PARSE_INVALID_TRY),
            "duplicate \"rescue\" clauses given for \"try\"".to_string()
        )
    );
}

#[test]
fn a_rescue_section_that_is_not_clauses_is_refused_with_elixirs_words() {
    assert_eq!(
        try_refusal("def f() do\n  try do\n    1\n  rescue\n    2\n  end\nend\n"),
        (
            Some(crate::diag::codes::PARSE_INVALID_TRY),
            "invalid \"rescue\" block in \"try\", it expects \"pattern -> expr\" clauses".to_string()
        )
    );
}

#[test]
fn a_catch_clause_with_one_head_is_a_throw_clause_and_with_two_names_its_kind() {
    let surface = surface_of(
        "def f() do\n  try do\n    1\n  catch\n    v -> v\n    :exit, r -> r\n    k, v when k == :error -> v\n    w when w > 1 -> w\n  end\nend\n",
    );
    let Expr::Try { catch, .. } = &surface.clauses[0].body.node else {
        panic!("expected a try, got {:?}", surface.clauses[0].body.node);
    };
    assert_eq!(catch.len(), 4);
    let kinds = catch.iter().map(|clause| &clause.kind.node).collect::<Vec<_>>();
    assert!(
        matches!(kinds[0], Pattern::Atom(kind) if kind == "throw"),
        "one head means a throw: {kinds:?}"
    );
    assert!(matches!(kinds[1], Pattern::Atom(kind) if kind == "exit"), "{kinds:?}");
    assert!(matches!(kinds[2], Pattern::Var(_)), "{kinds:?}");
    let guarded = catch.iter().map(|clause| clause.guard.is_some()).collect::<Vec<_>>();
    assert_eq!(guarded, [false, false, true, true], "a guard belongs to its clause");
}

#[test]
fn a_catch_clause_of_three_heads_is_refused_with_elixirs_words() {
    for source in [
        "def f() do\n  try do\n    1\n  catch\n    a, b, c -> 2\n  end\nend\n",
        "def f() do\n  try do\n    1\n  catch\n    a, b, c when true -> 2\n  end\nend\n",
        "def f() do\n  try do\n    1\n  catch\n    -> 2\n  end\nend\n",
    ] {
        assert_eq!(
            try_refusal(source),
            (
                Some(crate::diag::codes::PARSE_INVALID_TRY),
                "expected one or two args for :catch clauses (->) in \"try\"".to_string()
            ),
            "{source}"
        );
    }
}

#[test]
fn a_catch_section_that_is_not_clauses_is_refused_with_elixirs_words() {
    for source in [
        "def f() do\n  try do\n    1\n  catch\n    :x\n  end\nend\n",
        "def f() do\n  try do\n    1\n  catch\n  end\nend\n",
    ] {
        assert_eq!(
            try_refusal(source),
            (
                Some(crate::diag::codes::PARSE_INVALID_TRY),
                "expected -> clauses for :catch in \"try\"".to_string()
            ),
            "{source}"
        );
    }
}

#[test]
fn an_else_section_that_is_not_clauses_is_refused_with_elixirs_words() {
    assert_eq!(
        try_refusal("def f() do\n  try do\n    1\n  rescue\n    e -> 2\n  else\n    3\n  end\nend\n"),
        (
            Some(crate::diag::codes::PARSE_INVALID_TRY),
            "expected -> clauses for :else in \"try\"".to_string()
        )
    );
}

#[test]
fn an_after_or_else_section_given_twice_is_refused_with_elixirs_words() {
    for (section, clauses) in [("after", "1"), ("else", "v -> v")] {
        let source = format!(
            "def f() do\n  try do\n    1\n  {section}\n    {clauses}\n  {section}\n    {clauses}\n  end\nend\n"
        );
        assert_eq!(
            try_refusal(&source),
            (
                Some(crate::diag::codes::PARSE_INVALID_TRY),
                format!("duplicate \"{section}\" clauses given for \"try\"")
            ),
            "{section}"
        );
    }
}

#[test]
fn rescue_else_and_after_decode_beside_the_body_in_any_section_order() {
    let surface = surface_of(
        "def f() do\n  try do\n    1\n  after\n    4\n  else\n    1 -> 2\n    n -> n\n  rescue\n    e -> 3\n  end\nend\n",
    );
    let Expr::Try {
        body,
        rescue,
        else_clauses,
        after,
        ..
    } = &surface.clauses[0].body.node
    else {
        panic!("expected a try, got {:?}", surface.clauses[0].body.node);
    };
    assert!(matches!(body.node, Expr::Int(1)), "{body:?}");
    assert_eq!(rescue.len(), 1);
    assert_eq!(else_clauses.len(), 2);
    assert!(matches!(after.as_deref().map(|after| &after.node), Some(Expr::Int(4))));
}

fn decoded_var(
    build: impl FnOnce(&super::QuotedSourceBuilder) -> fz_runtime::any_value::AnyValueRef,
) -> Result<Var, super::QuotedSourceError> {
    let heap = std::rc::Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let root = builder.root(build(&builder)).expect("root");
    let expr =
        super::quoted_function::decode_standalone_expr(&root.cursor(), None, &crate::source::SourceMap::default())?;
    match expr.node {
        Expr::Var(var) => Ok(var),
        other => panic!("expected a variable, got {other:?}"),
    }
}

#[test]
fn every_variable_identity_survives_writing_and_reading_back() {
    use crate::ast::{AtomName, VarContext, VarCounter};
    let identities = [
        VarContext::user(),
        VarContext {
            context: Some(AtomName::from("Elixir.Main")),
            counter: None,
        },
        VarContext {
            context: Some(AtomName::from("Elixir.Gen")),
            counter: Some(VarCounter::Module {
                module: AtomName::from("Elixir.Main"),
                n: -3,
            }),
        },
        VarContext {
            context: Some(AtomName::from("Elixir.Gen")),
            counter: Some(VarCounter::Integer(41)),
        },
        VarContext::minted("fz_source_sugar", 2),
    ];
    for context in identities {
        let var = Var {
            name: "x".to_string(),
            context,
        };
        let read = decoded_var(|builder| builder.variable(&var, &QuotedSourceMetadata::default()).expect("write"))
            .expect("read back");
        assert_eq!(read, var, "a variable reads back as the variable written");
    }
}

#[test]
fn a_variable_built_by_hand_reads_as_elixir_names_it() {
    use crate::ast::{AtomName, VarContext, VarCounter};
    let read = decoded_var(|b| {
        let counter = b.tuple(&[b.atom("Elixir.Main"), b.int(7)]).unwrap();
        let meta = b.list(&[b.tuple(&[b.atom("counter"), counter]).unwrap()]).unwrap();
        b.tuple(&[b.atom("x"), meta, b.atom("Elixir.Gen")]).unwrap()
    })
    .expect("decodes");
    assert_eq!(
        read.context,
        VarContext {
            context: Some(AtomName::from("Elixir.Gen")),
            counter: Some(VarCounter::Module {
                module: AtomName::from("Elixir.Main"),
                n: 7
            }),
        },
        "`{{:x, [counter: {{Main, 7}}], Gen}}` is Gen's x, claimed by Main's seventh expansion"
    );
    let user = decoded_var(|b| b.tuple(&[b.atom("x"), b.list(&[]).unwrap(), b.nil()]).unwrap()).expect("decodes");
    assert!(
        user.context.is_user(),
        "`{{:x, [], nil}}` is the variable the user writes"
    );
}

#[test]
fn a_counter_that_is_neither_an_integer_nor_a_module_pair_is_refused() {
    let error = decoded_var(|b| {
        let meta = b
            .list(&[b.tuple(&[b.atom("counter"), b.atom("bad")]).unwrap()])
            .unwrap();
        b.tuple(&[b.atom("x"), meta, b.atom("Elixir.Gen")]).unwrap()
    })
    .unwrap_err();
    assert!(error.to_string().contains("a variable's counter must be"), "{error}");
}

#[test]
fn a_receive_with_only_an_after_clause_decodes_to_no_message_clauses_and_an_after() {
    let surface = surface_of("def f() do\n  receive do\n  after 20 -> :ok\n  end\nend\n");
    let Expr::Receive { clauses, after } = &surface.clauses[0].body.node else {
        panic!("expected a receive");
    };
    assert!(clauses.is_empty(), "no message clause was written");
    assert!(after.is_some(), "the after clause is kept");
}

#[test]
fn a_macros_caller_and_a_handlers_stacktrace_read_the_enclosing_scope_whatever_quote_wrote_them() {
    use crate::ast::{AtomName, VarContext};
    for name in [crate::ast::CALLER, crate::ast::STACKTRACE] {
        let written = Var {
            name: name.to_string(),
            context: VarContext {
                context: Some(AtomName::from("Elixir.Record")),
                counter: None,
            },
        };
        let read = decoded_var(|builder| {
            builder
                .variable(&written, &QuotedSourceMetadata::default())
                .expect("write")
        })
        .expect("read back");
        assert_eq!(read, Var::user(name), "{name} is no quote's hygienic variable");
    }
}
