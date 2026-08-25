//! The in-house type-expr parser is purely syntactic: it captures structure
//! and leaves every name unclassified, so an unknown name is not an error
//! here (resolution decides) and no `ModuleTypeEnv` is consulted. These tests
//! pin that intent against the worked examples the rework is built around.

use super::type_expr::{NominalKind, TypeDefBody, TypeExpr, parse_type_def_body, parse_type_expr};
use crate::parser::lexer::{Lexer, Token};
use crate::telemetry::ConfiguredTelemetry;

fn lex(src: &str) -> Vec<Token> {
    Lexer::with_source_name(src, "<test>")
        .tokenize(&ConfiguredTelemetry::new())
        .expect("type-expr fragment lexes")
}

fn parse(src: &str) -> TypeExpr {
    parse_type_expr(&lex(src)).expect("type-expr parses")
}

fn name(path: &[&str], args: Vec<TypeExpr>) -> TypeExpr {
    TypeExpr::Name {
        path: path.iter().map(|segment| segment.to_string()).collect(),
        args,
    }
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
    // The higher-order reducer surface `(a, b) -> {a, b}`.
    assert_eq!(
        parse("(a, b) -> {a, b}"),
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
        TypeExpr::Map(vec![(name(&["ok"], vec![]), name(&["integer"], vec![]))]),
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
            (TypeExpr::AtomLit("ok".to_string()), name(&["integer"], vec![])),
            (TypeExpr::AtomLit("err".to_string()), name(&["atom"], vec![])),
        ]),
    );
}

#[test]
fn a_map_key_can_be_any_type_expression_via_fat_arrow() {
    // `1 => atom`: the canonical `=>` form accepts a key that is not a bare
    // atom/ident, unlike the `:`-shorthand.
    assert_eq!(
        parse("%{1 => atom}"),
        TypeExpr::Map(vec![(TypeExpr::IntLit(1), name(&["atom"], vec![]))]),
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
        parse_type_def_body(&lex("refines integer")),
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
        parse_type_def_body(&lex("opaque resource(integer)")),
        Ok(TypeDefBody {
            kind: NominalKind::Opaque,
            inner: name(&["resource"], vec![name(&["integer"], vec![])]),
        }),
    );
}

#[test]
fn a_plain_body_has_no_nominal_prefix() {
    assert_eq!(
        parse_type_def_body(&lex("t")),
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
fn a_multi_element_paren_without_an_arrow_is_an_error() {
    // `(a, b)` is ambiguous with a tuple; the grammar demands `{a, b}` or an
    // arrow. This is a grammar rule, not a naming decision.
    assert!(parse_type_expr(&lex("(a, b)")).is_err());
}

#[test]
fn trailing_tokens_are_rejected() {
    assert!(parse_type_expr(&lex("integer integer")).is_err());
}
