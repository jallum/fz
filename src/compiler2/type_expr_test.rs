//! The in-house type-expr parser is purely syntactic: it captures structure
//! and leaves every name unclassified, so an unknown name is not an error
//! here (resolution decides) and no `ModuleTypeEnv` is consulted. These tests
//! pin that intent against the worked examples the rework is built around.

use super::type_expr::{MapTypePair, NominalKind, TypeDefBody, TypeExpr, parse_type_def_body, parse_type_expr};
use crate::parser::lexer::{Lexer, Token};
use crate::source::Span;
use crate::telemetry::ConfiguredTelemetry;

fn lex(src: &str) -> Vec<Token> {
    let mut sources = crate::source::SourceMap::default();
    let version = sources.add_code(Some("<test>"), src);
    Lexer::with_source_version_and_name(src, version, "<test>")
        .tokenize(&ConfiguredTelemetry::new())
        .expect("type-expr fragment lexes")
}

/// The parse's structure, with every span blanked: the structural tests
/// below compare trees, and a span is pinned by its own test.
fn parse(src: &str) -> TypeExpr {
    unspanned(parse_type_expr(&lex(src)).expect("type-expr parses"))
}

fn parse_body(src: &str) -> Result<TypeDefBody, super::type_expr::TypeExprError> {
    parse_type_def_body(&lex(src)).map(|body| TypeDefBody {
        kind: body.kind,
        inner: unspanned(body.inner),
    })
}

fn unspanned(expr: TypeExpr) -> TypeExpr {
    let each = |exprs: Vec<TypeExpr>| exprs.into_iter().map(unspanned).collect();
    match expr {
        TypeExpr::Name { path, args, .. } => TypeExpr::Name {
            path,
            args: each(args),
            span: Span::DUMMY,
        },
        TypeExpr::List(inner) => TypeExpr::List(Box::new(unspanned(*inner))),
        TypeExpr::Tuple(elems) => TypeExpr::Tuple(each(elems)),
        TypeExpr::Union(elems) => TypeExpr::Union(each(elems)),
        TypeExpr::Arrow { params, result } => TypeExpr::Arrow {
            params: each(params),
            result: Box::new(unspanned(*result)),
        },
        TypeExpr::StructRecord { module, fields, .. } => TypeExpr::StructRecord {
            module,
            span: Span::DUMMY,
            fields: fields.into_iter().map(|(field, ty)| (field, unspanned(ty))).collect(),
        },
        TypeExpr::Map(pairs) => TypeExpr::Map(
            pairs
                .into_iter()
                .map(|pair| MapTypePair {
                    key: unspanned(pair.key),
                    optional: pair.optional,
                    value: unspanned(pair.value),
                })
                .collect(),
        ),
        leaf => leaf,
    }
}

fn name(path: &[&str], args: Vec<TypeExpr>) -> TypeExpr {
    TypeExpr::Name {
        path: path.iter().map(|segment| segment.to_string()).collect(),
        args,
        span: Span::DUMMY,
    }
}

/// The text a span covers in `src`.
fn written(src: &str, span: Span) -> &str {
    &src[span.start as usize..span.end as usize]
}

/// A name is reported under itself, so its span is the whole dotted path and
/// nothing around it: not its type arguments, not the type it sits in.
#[test]
fn a_name_spans_its_whole_path_and_nothing_more() {
    let src = "[{:ok, Geo.Pt.t(integer)}]";
    let TypeExpr::List(tuple) = parse_type_expr(&lex(src)).expect("type-expr parses") else {
        panic!("a list type");
    };
    let TypeExpr::Tuple(elems) = *tuple else {
        panic!("a tuple type");
    };
    let TypeExpr::Name { span, args, .. } = &elems[1] else {
        panic!("a name");
    };
    assert_eq!(written(src, *span), "Geo.Pt.t");
    let TypeExpr::Name { span, .. } = &args[0] else {
        panic!("a name argument");
    };
    assert_eq!(written(src, *span), "integer");
}

/// A struct record is reported under the whole record, as a struct literal
/// and a struct pattern are.
#[test]
fn a_struct_record_spans_the_whole_record() {
    let src = "[%Geo.Pt{x: integer}]";
    let TypeExpr::List(record) = parse_type_expr(&lex(src)).expect("type-expr parses") else {
        panic!("a list type");
    };
    let TypeExpr::StructRecord { span, .. } = *record else {
        panic!("a struct record");
    };
    assert_eq!(written(src, span), "%Geo.Pt{x: integer}");
}

#[test]
fn a_builtin_and_a_user_name_are_indistinguishable_until_resolution() {
    // The whole point: the parser does not know `integer` is special. Both a
    // builtin and a one-letter alias/variable are the same Name shape; only
    // resolution (against the captured namespace) tells them apart.
    assert_eq!(parse("integer"), name(&["integer"], vec![]));
    assert_eq!(parse("t"), name(&["t"], vec![]));
}

#[test]
fn an_unknown_name_parses_rather_than_erroring() {
    // The old-world parser rejected names absent from its env. In-house the
    // parser never resolves, so a name it has never heard of is still just a
    // Name — an unresolved-frontier question for later, not a parse failure.
    assert_eq!(parse("Frobnicate.whatsit"), name(&["Frobnicate", "whatsit"], vec![]),);
}

#[test]
fn a_qualified_name_keeps_its_path_and_argument() {
    // `SomeModule.t(float)`: dotted identity plus a one-arg application, with
    // the argument itself an unresolved Name.
    assert_eq!(
        parse("SomeModule.t(float)"),
        name(&["SomeModule", "t"], vec![name(&["float"], vec![])]),
    );
}

#[test]
fn an_arrow_over_a_tuple_parses_structurally() {
    // The higher-order reducer surface `(a, b -> {a, b})`.
    assert_eq!(
        parse("(a, b -> {a, b})"),
        TypeExpr::Arrow {
            params: vec![name(&["a"], vec![]), name(&["b"], vec![])],
            result: Box::new(TypeExpr::Tuple(vec![name(&["a"], vec![]), name(&["b"], vec![])])),
        },
    );
}

#[test]
fn a_union_of_tagged_tuples_parses() {
    // The control-tuple result `{:cont, b} | {:halt, b}`.
    assert_eq!(
        parse("{:cont, b} | {:halt, b}"),
        TypeExpr::Union(vec![
            TypeExpr::Tuple(vec![TypeExpr::AtomLit("cont".to_string()), name(&["b"], vec![])]),
            TypeExpr::Tuple(vec![TypeExpr::AtomLit("halt".to_string()), name(&["b"], vec![])]),
        ]),
    );
}

#[test]
fn lists_distinguish_element_from_empty() {
    assert_eq!(parse("[integer]"), TypeExpr::List(Box::new(name(&["integer"], vec![]))));
    assert_eq!(parse("[]"), TypeExpr::EmptyList);
}

#[test]
fn literals_and_wildcard_are_syntactic() {
    assert_eq!(parse("_"), TypeExpr::Wildcard);
    assert_eq!(parse("42"), TypeExpr::IntLit(42));
    assert_eq!(parse(":ok"), TypeExpr::AtomLit("ok".to_string()));
    assert_eq!(parse("nil"), TypeExpr::Nil);
    assert_eq!(parse("true"), TypeExpr::Bool);
}

#[test]
fn a_struct_record_keeps_module_and_field_types() {
    assert_eq!(
        parse("%Range{first: integer, last: integer}"),
        TypeExpr::StructRecord {
            module: vec!["Range".to_string()],
            span: Span::DUMMY,
            fields: vec![
                ("first".to_string(), name(&["integer"], vec![])),
                ("last".to_string(), name(&["integer"], vec![])),
            ],
        },
    );
}

#[test]
fn a_map_parses_its_key_value_pairs() {
    // `%{k => v}`: parity with `[T]` for lists — the structural map type.
    assert_eq!(
        parse("%{ok => integer}"),
        TypeExpr::Map(vec![pair(name(&["ok"], vec![]), name(&["integer"], vec![]))]),
    );
}

fn pair(key: TypeExpr, value: TypeExpr) -> MapTypePair {
    MapTypePair {
        key,
        optional: false,
        value,
    }
}

#[test]
fn a_map_key_wrapped_in_optional_is_an_optional_entry() {
    // Elixir's typespec reference: `optional(k) => v` may be absent.
    assert_eq!(
        parse("%{optional(:array_start) => integer}"),
        TypeExpr::Map(vec![MapTypePair {
            key: TypeExpr::AtomLit("array_start".to_string()),
            optional: true,
            value: name(&["integer"], vec![]),
        }]),
    );
}

#[test]
fn a_map_key_wrapped_in_required_is_the_same_entry_as_the_bare_key() {
    assert_eq!(parse("%{required(:x) => integer}"), parse("%{:x => integer}"));
}

#[test]
fn a_parenthesized_union_is_a_map_key() {
    // `%{(binary() | atom()) => v}`: the key is one type, written with parentheses.
    assert_eq!(
        parse("%{(binary() | atom()) => integer}"),
        TypeExpr::Map(vec![pair(
            TypeExpr::Union(vec![name(&["binary"], vec![]), name(&["atom"], vec![])]),
            name(&["integer"], vec![]),
        )]),
    );
}

#[test]
fn optional_names_a_type_everywhere_but_the_wrapper_position_of_a_map_key() {
    // `optional` followed by no `(` in key position is an ordinary type name.
    assert_eq!(
        parse("%{optional => integer}"),
        TypeExpr::Map(vec![pair(name(&["optional"], vec![]), name(&["integer"], vec![]))]),
    );
}

#[test]
fn a_map_key_shorthand_matches_the_struct_record_field_shorthand() {
    // `key: T` is atom-shorthand for `:key => T`, mirroring both the
    // struct-record field shorthand and the value-level map literal's
    // `key: value` form.
    assert_eq!(
        parse("%{ok: integer, err: atom}"),
        TypeExpr::Map(vec![
            pair(TypeExpr::AtomLit("ok".to_string()), name(&["integer"], vec![])),
            pair(TypeExpr::AtomLit("err".to_string()), name(&["atom"], vec![])),
        ]),
    );
}

#[test]
fn a_map_key_can_be_any_type_expression_via_fat_arrow() {
    // `1 => atom`: the canonical `=>` form accepts a key that is not a bare
    // atom/ident, unlike the `:`-shorthand.
    assert_eq!(
        parse("%{1 => atom}"),
        TypeExpr::Map(vec![pair(TypeExpr::IntLit(1), name(&["atom"], vec![]))]),
    );
}

#[test]
fn an_empty_map_parses_with_no_pairs() {
    assert_eq!(parse("%{}"), TypeExpr::Map(vec![]));
}

#[test]
fn a_refines_body_strips_the_nominal_prefix() {
    // `@type B :: refines integer` — the brand worked example. The inner is a
    // plain unresolved Name; the resolver mints the brand over it.
    assert_eq!(
        parse_body("refines integer"),
        Ok(TypeDefBody {
            kind: NominalKind::Refines,
            inner: name(&["integer"], vec![]),
        }),
    );
}

#[test]
fn an_opaque_body_over_resource_does_not_special_case_resource() {
    // `@type t :: opaque resource(integer)` — `resource` is just another Name
    // to the parser; resolution knows it is the resource constructor.
    assert_eq!(
        parse_body("opaque resource(integer)"),
        Ok(TypeDefBody {
            kind: NominalKind::Opaque,
            inner: name(&["resource"], vec![name(&["integer"], vec![])]),
        }),
    );
}

#[test]
fn a_plain_body_has_no_nominal_prefix() {
    assert_eq!(
        parse_body("t"),
        Ok(TypeDefBody {
            kind: NominalKind::Plain,
            inner: name(&["t"], vec![]),
        }),
    );
}

#[test]
fn a_nominal_body_without_an_inner_type_is_an_error() {
    assert!(parse_type_def_body(&lex("refines")).is_err());
}

#[test]
fn a_zero_arity_function_type_has_no_parameters() {
    assert_eq!(
        parse("(-> any)"),
        TypeExpr::Arrow {
            params: vec![],
            result: Box::new(name(&["any"], vec![]))
        },
    );
}

#[test]
fn an_arrow_after_the_parentheses_is_refused_with_the_elixir_spelling() {
    // Elixir has one function-type spelling, with the arrow inside the
    // parentheses; the arrow after them is not Elixir and is refused.
    for written in ["(a, b) -> {a, b}", "(integer) -> integer", "() -> any"] {
        let error = parse_type_expr(&lex(written)).expect_err(written);
        assert!(error.msg.contains("`(A, B -> R)`"), "{written}: {}", error.msg);
    }
}

#[test]
fn an_elixir_function_type_nests_inside_a_list_and_as_a_result() {
    // `compose([(any -> any)], (any, c -> d)) :: (any, c -> d)` in one piece.
    let reducer = parse("(any, c -> d)");
    assert_eq!(parse("[(any -> any)]"), TypeExpr::List(Box::new(parse("(any -> any)"))),);
    assert_eq!(
        parse("(any, c -> d) | nil"),
        TypeExpr::Union(vec![reducer, TypeExpr::Nil]),
    );
}

#[test]
fn an_elixir_function_type_must_close_its_parenthesis() {
    let error = parse_type_expr(&lex("(a -> b")).expect_err("an unclosed function type is refused");
    assert!(error.msg.contains("`)` closing the function type"), "{}", error.msg);
}

#[test]
fn a_multi_element_paren_without_an_arrow_is_an_error() {
    // `(a, b)` is ambiguous with a tuple; the grammar demands `{a, b}` or an
    // arrow. This is a grammar rule, not a naming decision.
    assert!(parse_type_expr(&lex("(a, b)")).is_err());
}

#[test]
fn trailing_tokens_are_rejected() {
    assert!(parse_type_expr(&lex("integer integer")).is_err());
}
