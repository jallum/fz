use super::*;

use std::collections::HashMap;
use std::slice::from_ref;

use crate::ast::{Attribute, SpecDecl, TypeAliasDecl, TypeExprBody};
use crate::diag::Span;
use crate::parser::lexer::Lexer;
use crate::specs::{
    ResolvedSpec, ResolvedSpecSet, StructuralCorrespondenceGroup, StructuralOccurrence, StructuralPathStep,
    spec_set_correspondence_groups,
};
use crate::types::{DefaultTypes, Ty, TypeVarId, Types};

fn parse_one<T: Types<Ty = Ty>>(t: &mut T, src: &str) -> Result<T::Ty, TypeExprError> {
    parse_one_with(t, src, &ModuleTypeEnv::new())
}

fn parse_one_with<T: Types<Ty = Ty>>(t: &mut T, src: &str, env: &ModuleTypeEnv) -> Result<T::Ty, TypeExprError> {
    let toks = Lexer::new(src).tokenize().expect("lex");
    let (ty, consumed) = parse_type_expr(t, &toks, env)?;
    // Allow trailing Eof.
    let trailing = toks.len() - consumed;
    if trailing > 1 || (trailing == 1 && !matches!(toks[consumed].tok, Tok::Eof)) {
        return Err(TypeExprError {
            msg: format!("trailing {} token(s) after type expression", trailing),
            span: toks[consumed].span,
        });
    }
    Ok(ty)
}

fn spec_correspondence_groups(spec: &ResolvedSpec) -> Vec<StructuralCorrespondenceGroup> {
    spec_set_correspondence_groups(&ResolvedSpecSet {
        arrows: vec![spec.clone()],
    })
}

#[test]
fn scalar_names_parse_to_corresponding_descrs() {
    let mut ct = crate::types::new();
    let nil = ct.nil();
    let bool_ = ct.bool();
    let int = ct.int();
    let float = ct.float();
    let binary = ct.str_t();
    let atom = ct.atom();
    let any = ct.any();
    let cases: &[(&str, &Ty)] = &[
        ("nil", &nil),
        ("bool", &bool_),
        ("integer", &int),
        ("float", &float),
        ("binary", &binary),
        ("atom", &atom),
        ("any", &any),
        ("_", &any),
    ];
    for (src, expected) in cases {
        let actual = parse_one(&mut ct, src).unwrap();
        assert!(ct.is_equivalent(&actual, expected), "src={}", src);
    }
}

#[test]
fn runtime_builtin_names_parse_without_env_aliases() {
    let mut ct = crate::types::new();

    let utf8 = parse_one(&mut ct, "utf8").unwrap();
    assert_eq!(ct.brand_singleton(&utf8).as_deref(), Some("utf8"));

    let pid = parse_one(&mut ct, "pid").unwrap();
    assert_eq!(ct.opaque_singleton(&pid).as_deref(), Some("pid"));

    let ref_ = parse_one(&mut ct, "ref").unwrap();
    assert_eq!(ct.opaque_singleton(&ref_).as_deref(), Some("ref"));
}

#[test]
fn atom_literal_parses_to_singleton() {
    let mut ct = crate::types::new();
    let ok = ct.atom_lit("ok");
    let err = ct.atom_lit("error");
    let a = parse_one(&mut ct, ":ok").unwrap();
    let b = parse_one(&mut ct, ":error").unwrap();
    assert!(ct.is_equivalent(&a, &ok));
    assert!(ct.is_equivalent(&b, &err));
}

#[test]
fn int_literal_parses_to_singleton() {
    let mut ct = crate::types::new();
    let i42 = ct.int_lit(42);
    let i0 = ct.int_lit(0);
    let a = parse_one(&mut ct, "42").unwrap();
    let b = parse_one(&mut ct, "0").unwrap();
    assert!(ct.is_equivalent(&a, &i42));
    assert!(ct.is_equivalent(&b, &i0));
}

#[test]
fn float_literal_parses_to_singleton() {
    let mut ct = crate::types::new();
    let expected = ct.float_lit(2.5);
    let actual = parse_one(&mut ct, "2.5").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn list_of_integer() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let expected = ct.list(int);
    let actual = parse_one(&mut ct, "[integer]").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn empty_list_is_nil() {
    let mut ct = crate::types::new();
    let nil = ct.nil();
    let actual = parse_one(&mut ct, "[]").unwrap();
    assert!(ct.is_equivalent(&actual, &nil));
}

#[test]
fn tuple_two_elements() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let atom = ct.atom();
    let expected = ct.tuple(&[int, atom]);
    let actual = parse_one(&mut ct, "{integer, atom}").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn tuple_three_elements_with_literal() {
    let mut ct = crate::types::new();
    let ok = ct.atom_lit("ok");
    let int = ct.int();
    let expected = ct.tuple(&[ok, int.clone(), int]);
    let actual = parse_one(&mut ct, "{:ok, integer, integer}").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn empty_tuple() {
    let mut ct = crate::types::new();
    let expected = ct.tuple(&[]);
    let actual = parse_one(&mut ct, "{}").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn arrow_zero_arg() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let expected = ct.arrow(&[], int);
    let actual = parse_one(&mut ct, "() -> integer").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn arrow_one_arg() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let arg = int.clone();
    let expected = ct.arrow(from_ref(&arg), int);
    let actual = parse_one(&mut ct, "(integer) -> integer").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn arrow_two_args() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let float = ct.float();
    let bin = ct.str_t();
    let expected = ct.arrow(&[int, float], bin);
    let actual = parse_one(&mut ct, "(integer, float) -> binary").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn paren_grouping_one_element() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let actual = parse_one(&mut ct, "(integer)").unwrap();
    assert!(ct.is_equivalent(&actual, &int));
}

#[test]
fn paren_grouping_with_union() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let float = ct.float();
    let expected = ct.union(int, float);
    let actual = parse_one(&mut ct, "(integer | float)").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn paren_multi_without_arrow_errors() {
    let mut ct = crate::types::new();
    let r = parse_one(&mut ct, "(integer, float)");
    assert!(r.is_err(), "multi-element paren without `->` must error; got ok",);
}

#[test]
fn union_two_axes() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let float = ct.float();
    let expected = ct.union(int, float);
    let actual = parse_one(&mut ct, "integer | float").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn union_three_axes_is_left_associative_but_equivalent() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let float = ct.float();
    let nil = ct.nil();
    let u = ct.union(int, float);
    let expected = ct.union(u, nil);
    let actual = parse_one(&mut ct, "integer | float | nil").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn union_with_atom_literals() {
    let mut ct = crate::types::new();
    let ok = ct.atom_lit("ok");
    let err = ct.atom_lit("error");
    let expected = ct.union(ok, err);
    let actual = parse_one(&mut ct, ":ok | :error").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn list_of_union() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let float = ct.float();
    let u = ct.union(int, float);
    let expected = ct.list(u);
    let actual = parse_one(&mut ct, "[integer | float]").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn nested_tuple_inside_list() {
    let mut ct = crate::types::new();
    let ok = ct.atom_lit("ok");
    let int = ct.int();
    let tup = ct.tuple(&[ok, int]);
    let expected = ct.list(tup);
    let actual = parse_one(&mut ct, "[{:ok, integer}]").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn arrow_taking_arrow_argument() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let arg = int.clone();
    let f = ct.arrow(from_ref(&arg), int.clone());
    let l = ct.list(int);
    let expected = ct.arrow(&[f, l.clone()], l);
    let actual = parse_one(&mut ct, "((integer) -> integer, [integer]) -> [integer]").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn named_ref_resolves_via_env() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let mut env = ModuleTypeEnv::new();
    env.insert("id".to_string(), int.clone());
    let actual = parse_one_with(&mut ct, "id", &env).unwrap();
    assert!(ct.is_equivalent(&actual, &int));
}

#[test]
fn named_ref_used_in_arrow_via_env() {
    let mut ct = crate::types::new();
    let int = ct.int();
    let mut env = ModuleTypeEnv::new();
    env.insert("id".to_string(), int.clone());
    let arg = int.clone();
    let expected = ct.arrow(from_ref(&arg), int);
    let actual = parse_one_with(&mut ct, "(id) -> id", &env).unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn unknown_name_with_empty_env_errors() {
    let mut ct = crate::types::new();
    let r = parse_one(&mut ct, "nonesuch");
    assert!(r.is_err());
    let e = r.unwrap_err();
    assert!(e.msg.contains("unknown type name"), "msg = {}", e.msg);
}

#[test]
fn builtin_name_takes_precedence_over_alias() {
    // A user-defined alias must NOT shadow a builtin scalar name.
    let mut ct = crate::types::new();
    let float = ct.float();
    let int = ct.int();
    let mut env = ModuleTypeEnv::new();
    env.insert("integer".to_string(), float);
    let actual = parse_one_with(&mut ct, "integer", &env).unwrap();
    assert!(
        ct.is_equivalent(&actual, &int),
        "builtin `integer` must resolve to int regardless of env shadow"
    );
}

#[test]
fn malformed_unclosed_list_errors() {
    let mut ct = crate::types::new();
    assert!(parse_one(&mut ct, "[integer").is_err());
}

#[test]
fn malformed_unclosed_tuple_errors() {
    let mut ct = crate::types::new();
    assert!(parse_one(&mut ct, "{integer, atom").is_err());
}

#[test]
fn malformed_unclosed_paren_errors() {
    let mut ct = crate::types::new();
    assert!(parse_one(&mut ct, "(integer").is_err());
}

#[test]
fn trailing_tokens_error() {
    let mut ct = crate::types::new();
    let r = parse_one(&mut ct, "integer foo");
    assert!(r.is_err(), "trailing tokens must be rejected");
}

#[test]
fn primary_position_rejects_bar() {
    // `| integer` is malformed — `|` is a binary operator.
    let mut ct = crate::types::new();
    assert!(parse_one(&mut ct, "| integer").is_err());
}

#[test]
fn struct_record_type_parses_field_types() {
    let toks = Lexer::new("%Range{first: integer, last: integer, step: integer}")
        .tokenize()
        .expect("lex");
    let env = ModuleTypeEnv::new();
    let mut ct = crate::types::new();
    let (record, ty, consumed) = parse_struct_record_type(&mut ct, &toks, &env).unwrap();
    assert_eq!(record.module.dotted(), "Range");
    assert_eq!(
        record
            .fields
            .iter()
            .map(|field| field.name.as_str())
            .collect::<Vec<_>>(),
        vec!["first", "last", "step"]
    );
    let int = ct.int();
    assert!(record.fields.iter().all(|field| ct.is_equivalent(&field.ty, &int)));
    assert_eq!(ct.opaque_singleton(&ty).as_deref(), Some("impl-target::Range"));
    assert_eq!(toks.len() - consumed, 1, "only trailing Eof remains");
}

// ----- fz-ul4.31.3: build_module_type_env -----

fn type_alias_attr(name: &str, body_src: &str) -> Attribute {
    type_alias_attr_with_params(name, &[], body_src)
}

fn type_alias_attr_with_params(name: &str, params: &[&str], body_src: &str) -> Attribute {
    let toks = Lexer::new(body_src).tokenize().expect("lex body");
    // Drop trailing Eof to match parser behavior.
    let body_tokens: Vec<_> = toks.into_iter().filter(|t| !matches!(t.tok, Tok::Eof)).collect();
    Attribute::TypeAlias(TypeAliasDecl {
        name: name.to_string(),
        name_span: Span::DUMMY,
        params: params.iter().map(|param| param.to_string()).collect(),
        body_tokens: TypeExprBody(body_tokens),
        span: Span::DUMMY,
    })
}

fn build_module_type_env_for_test(
    t: &mut DefaultTypes,
    attrs: &[Attribute],
    module_path: &str,
) -> Result<(ModuleTypeEnv, OpaqueInnerTypes, BrandInnerTypes), TypeExprError> {
    build_module_type_env_for_with_base(t, attrs, module_path, &ModuleTypeEnv::new())
}

#[test]
fn build_env_resolves_simple_alias() {
    let attrs = vec![type_alias_attr("id", "integer")];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let int = ct.int();
    assert!(ct.is_equivalent(env.get("id").unwrap(), &int));
}

#[test]
fn build_env_records_struct_field_types_from_type_alias() {
    let attrs = vec![type_alias_attr(
        "t",
        "%Range{first: integer, last: integer, step: integer}",
    )];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let alias_ty = env.get("t").expect("t alias");
    assert_eq!(ct.opaque_singleton(alias_ty).as_deref(), Some("impl-target::Range"));
    let record = env.struct_record("t").expect("struct record");
    assert_eq!(record.module.dotted(), "Range");
    let int = ct.int();
    assert!(record.fields.iter().all(|field| ct.is_equivalent(&field.ty, &int)));
}

#[test]
fn build_env_resolves_alias_of_alias_in_either_order() {
    // Declare in forward order: a refs b, b is plain.
    let attrs = vec![type_alias_attr("a", "b"), type_alias_attr("b", "integer")];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let int = ct.int();
    assert!(ct.is_equivalent(env.get("a").unwrap(), &int));
    assert!(ct.is_equivalent(env.get("b").unwrap(), &int));
}

#[test]
fn build_env_resolves_composite_alias() {
    // pair := {id, id}; id := integer.
    let attrs = vec![type_alias_attr("pair", "{id, id}"), type_alias_attr("id", "integer")];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let int = ct.int();
    let expected = ct.tuple(&[int.clone(), int]);
    assert!(ct.is_equivalent(env.get("pair").unwrap(), &expected));
}

#[test]
fn build_env_detects_simple_cycle() {
    let attrs = vec![type_alias_attr("a", "b"), type_alias_attr("b", "a")];
    let mut ct = crate::types::new();
    let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
    assert!(err.msg.contains("cycle"), "expected cycle diag, got: {}", err.msg);
}

#[test]
fn build_env_detects_three_way_cycle() {
    let attrs = vec![
        type_alias_attr("a", "b"),
        type_alias_attr("b", "c"),
        type_alias_attr("c", "a"),
    ];
    let mut ct = crate::types::new();
    let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
    assert!(err.msg.contains("cycle"), "expected cycle diag, got: {}", err.msg);
}

#[test]
fn build_env_rejects_unknown_reference() {
    let attrs = vec![type_alias_attr("foo", "nonesuch")];
    let mut ct = crate::types::new();
    let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
    assert!(
        err.msg.contains("unknown type name"),
        "expected unknown-name diag, got: {}",
        err.msg
    );
}

#[test]
fn build_env_rejects_duplicate_alias() {
    let attrs = vec![type_alias_attr("id", "integer"), type_alias_attr("id", "float")];
    let mut ct = crate::types::new();
    let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
    assert!(
        err.msg.contains("duplicate"),
        "expected duplicate diag, got: {}",
        err.msg
    );
}

#[test]
fn build_env_ignores_non_type_alias_attributes() {
    let attrs = vec![
        Attribute::ModuleDoc("hello".to_string()),
        type_alias_attr("id", "integer"),
        Attribute::Doc("a doc".to_string()),
    ];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    assert_eq!(env.len(), 1);
    let int = ct.int();
    assert!(ct.is_equivalent(env.get("id").unwrap(), &int));
}

#[test]
fn build_env_empty_for_module_without_aliases() {
    let attrs: Vec<Attribute> = vec![];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    assert!(env.is_empty());
}

#[test]
fn build_env_resolves_arrow_using_alias() {
    let attrs = vec![type_alias_attr("id", "integer"), type_alias_attr("idfn", "(id) -> id")];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let int = ct.int();
    let arg = int.clone();
    let expected = ct.arrow(from_ref(&arg), int);
    assert!(ct.is_equivalent(env.get("idfn").unwrap(), &expected));
}

#[test]
fn build_env_parameterized_alias_substitutes_args() {
    let attrs = vec![type_alias_attr_with_params("pair", &["a", "b"], "{a, b}")];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let actual = parse_one_with(&mut ct, "pair(integer, atom)", &env).unwrap();
    let int = ct.int();
    let atom = ct.atom();
    let expected = ct.tuple(&[int, atom]);
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn build_env_allows_same_alias_name_with_different_arities() {
    let attrs = vec![
        type_alias_attr("keyword", "[{atom, any}]"),
        type_alias_attr_with_params("keyword", &["t"], "[{atom, t}]"),
    ];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();

    let mono = env.get("keyword").expect("keyword/0");
    let atom = ct.atom();
    let any = ct.any();
    let any_pair = ct.tuple(&[atom.clone(), any]);
    let expected_mono = ct.list(any_pair);
    assert!(ct.is_equivalent(mono, &expected_mono));
    let mono_call = parse_one_with(&mut ct, "keyword()", &env).unwrap();
    assert!(ct.is_equivalent(&mono_call, &expected_mono));

    let applied = parse_one_with(&mut ct, "keyword(integer)", &env).unwrap();
    let int = ct.int();
    let int_pair = ct.tuple(&[atom, int]);
    let expected_applied = ct.list(int_pair);
    assert!(ct.is_equivalent(&applied, &expected_applied));
}

#[test]
fn build_env_parameterized_aliases_compose() {
    let attrs = vec![
        type_alias_attr_with_params("result", &["ok", "err"], "{:ok, ok} | {:error, err}"),
        type_alias_attr_with_params("api_result", &["t"], "result(t, utf8)"),
    ];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let actual = parse_one_with(&mut ct, "api_result(integer)", &env).unwrap();
    let ok = ct.atom_lit("ok");
    let int = ct.int();
    let ok_tuple = ct.tuple(&[ok, int]);
    let error = ct.atom_lit("error");
    let utf8 = ct.brand_of("utf8");
    let error_tuple = ct.tuple(&[error, utf8]);
    let expected = ct.union(ok_tuple, error_tuple);
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn parameterized_alias_application_checks_arity() {
    let attrs = vec![type_alias_attr_with_params("pair", &["a", "b"], "{a, b}")];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let err = parse_one_with(&mut ct, "pair(integer)", &env).unwrap_err();
    assert!(
        err.msg.contains("unknown type alias `pair/1`"),
        "expected arity error, got: {}",
        err.msg
    );
}

#[test]
fn parameterized_alias_cycle_is_rejected() {
    let attrs = vec![type_alias_attr_with_params("loop", &["t"], "loop(t)")];
    let mut ct = crate::types::new();
    let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
    assert!(err.msg.contains("cycle"), "expected cycle error, got: {}", err.msg);
}

#[test]
fn consumed_count_reports_correct_position() {
    // Parser returns how many tokens it consumed, so callers can
    // continue parsing whatever follows (e.g., the `::` separator
    // in `@spec name(T) :: R`).
    let toks = Lexer::new("integer foo").tokenize().unwrap();
    let env = ModuleTypeEnv::new();
    let mut ct = crate::types::new();
    let int = ct.int();
    let (ty, consumed) = parse_type_expr(&mut ct, &toks, &env).unwrap();
    assert!(ct.is_equivalent(&ty, &int));
    assert_eq!(consumed, 1, "consumed only the `integer` token");
}

// ---- opaque aliases ----

#[test]
fn build_env_opaque_alias_creates_nominal_type() {
    let attrs = vec![type_alias_attr("pid", "opaque integer")];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let pid = env.get("pid").unwrap();
    let expected = ct.opaque_of("pid");
    assert!(
        ct.is_equivalent(pid, &expected),
        "opaque alias should resolve to nominal opaque Ty: got {}",
        ct.display(pid),
    );
}

#[test]
fn build_env_opaque_alias_is_disjoint_from_underlying() {
    let attrs = vec![type_alias_attr("pid", "opaque integer")];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let pid = env.get("pid").unwrap();
    let int = ct.int();
    assert!(!ct.is_subtype(pid, &int), "pid should NOT be a subtype of integer");
    assert!(!ct.is_subtype(&int, pid), "integer should NOT be a subtype of pid");
}

// ---- resource(T) (fz-swt.6) ----

#[test]
fn resource_integer_parses_to_builtin_opaque_tag() {
    // `resource(T)` preserves the payload type now that constrained
    // polymorphic specs can return `resource(t)`.
    let mut ct = crate::types::new();
    let d = parse_one(&mut ct, "resource(integer)").unwrap();
    let payload = ct
        .resource_payload_type(&d)
        .expect("resource payload should be present");
    let int = ct.int();
    assert!(ct.is_equivalent(&payload, &int));
}

#[test]
fn resource_inner_type_is_validated() {
    let mut ct = crate::types::new();
    let r = parse_one(&mut ct, "resource(nonesuch)");
    assert!(r.is_err(), "unknown inner type must error");
}

#[test]
fn constrained_polymorphic_spec_resolves_vars_and_bounds() {
    let toks = |src: &str| Lexer::new(src).tokenize().expect("lex");
    let mut ct = crate::types::new();
    let spec = SpecDecl {
        name: "make_resource".to_string(),
        param_body_tokens: vec![TypeExprBody(toks("t")), TypeExprBody(toks("(t) -> nil"))],
        result_body_tokens: TypeExprBody(toks("resource(t)")),
        constraints: vec![("t".to_string(), TypeExprBody(toks("integer | cpointer")))],
    };
    let resolved = resolve_spec_decl(&mut ct, &spec, &ModuleTypeEnv::new()).unwrap();
    assert_eq!(resolved.constraints.len(), 1);
    assert!(ct.has_vars(&resolved.params[0]));
    assert!(ct.has_vars(&resolved.result));
}

#[test]
fn resolved_spec_retains_structural_shape_for_container_parametricity() {
    let toks = |src: &str| Lexer::new(src).tokenize().expect("lex");
    let mut ct = crate::types::new();
    let mut env = ModuleTypeEnv::new();
    env.insert("Enumerable.t".to_string(), ct.any());
    env.insert_param_alias(
        "Enumerable.t".to_string(),
        ParameterizedTypeAlias {
            params: vec!["a".to_string()],
            body_tokens: TypeExprBody(toks("a")),
            span: Span::DUMMY,
        },
    );
    let spec = SpecDecl {
        name: "drop".to_string(),
        param_body_tokens: vec![TypeExprBody(toks("Enumerable.t(a)")), TypeExprBody(toks("integer"))],
        result_body_tokens: TypeExprBody(toks("[a]")),
        constraints: vec![],
    };

    let resolved = resolve_spec_decl(&mut ct, &spec, &env).unwrap();
    assert_eq!(
        resolved.param_shapes,
        vec![
            ResolvedTypeShape::Named {
                name: "Enumerable.t".to_string(),
                args: vec![ResolvedTypeShape::Var(TypeVarId(0))],
            },
            ResolvedTypeShape::Integer,
        ]
    );
    assert_eq!(
        resolved.result_shape,
        ResolvedTypeShape::List(Box::new(ResolvedTypeShape::Var(TypeVarId(0))))
    );
}

#[test]
fn resolved_spec_retains_structural_shape_for_higher_order_parametricity() {
    let toks = |src: &str| Lexer::new(src).tokenize().expect("lex");
    let mut ct = crate::types::new();
    let mut env = ModuleTypeEnv::new();
    env.insert("Enumerable.t".to_string(), ct.any());
    env.insert_param_alias(
        "Enumerable.t".to_string(),
        ParameterizedTypeAlias {
            params: vec!["a".to_string()],
            body_tokens: TypeExprBody(toks("a")),
            span: Span::DUMMY,
        },
    );
    let spec = SpecDecl {
        name: "reduce".to_string(),
        param_body_tokens: vec![
            TypeExprBody(toks("Enumerable.t(a)")),
            TypeExprBody(toks("b")),
            TypeExprBody(toks("(a, b) -> b")),
        ],
        result_body_tokens: TypeExprBody(toks("b")),
        constraints: vec![],
    };

    let resolved = resolve_spec_decl(&mut ct, &spec, &env).unwrap();
    assert_eq!(
        resolved.param_shapes,
        vec![
            ResolvedTypeShape::Named {
                name: "Enumerable.t".to_string(),
                args: vec![ResolvedTypeShape::Var(TypeVarId(0))],
            },
            ResolvedTypeShape::Var(TypeVarId(1)),
            ResolvedTypeShape::Arrow {
                params: vec![
                    ResolvedTypeShape::Var(TypeVarId(0)),
                    ResolvedTypeShape::Var(TypeVarId(1)),
                ],
                result: Box::new(ResolvedTypeShape::Var(TypeVarId(1))),
            },
        ]
    );
    assert_eq!(resolved.result_shape, ResolvedTypeShape::Var(TypeVarId(1)));
}

#[test]
fn resolved_spec_reports_reduce_invariant_slot_correspondence() {
    let mut ct = crate::types::new();
    let entry_var = ct.type_var(TypeVarId(0));
    let acc_var = ct.type_var(TypeVarId(1));
    let enumerable_param = ct.list(entry_var.clone());
    let reducer_param = ct.arrow(&[entry_var, acc_var.clone()], acc_var.clone());
    let spec = ResolvedSpec {
        params: vec![enumerable_param, acc_var.clone(), reducer_param],
        param_shapes: vec![
            ResolvedTypeShape::List(Box::new(ResolvedTypeShape::Var(TypeVarId(0)))),
            ResolvedTypeShape::Var(TypeVarId(1)),
            ResolvedTypeShape::Arrow {
                params: vec![
                    ResolvedTypeShape::Var(TypeVarId(0)),
                    ResolvedTypeShape::Var(TypeVarId(1)),
                ],
                result: Box::new(ResolvedTypeShape::Var(TypeVarId(1))),
            },
        ],
        result: acc_var,
        result_shape: ResolvedTypeShape::Var(TypeVarId(1)),
        constraints: HashMap::new(),
    };

    let groups = spec_correspondence_groups(&spec);
    assert_eq!(groups.len(), 2);
    assert_eq!(
        groups.iter().find(|group| group.var == TypeVarId(1)),
        Some(&StructuralCorrespondenceGroup {
            var: TypeVarId(1),
            occurrences: vec![
                StructuralOccurrence::Param {
                    param_index: 1,
                    path: vec![],
                },
                StructuralOccurrence::Result { path: vec![] },
                StructuralOccurrence::CallbackArg {
                    param_index: 2,
                    arg_index: 1,
                    path: vec![],
                },
                StructuralOccurrence::CallbackResult {
                    param_index: 2,
                    path: vec![],
                },
            ],
        })
    );
}

#[test]
fn resolved_spec_reports_structural_container_correspondence() {
    let toks = |src: &str| Lexer::new(src).tokenize().expect("lex");
    let mut ct = crate::types::new();
    let mut env = ModuleTypeEnv::new();
    env.insert("Enumerable.t".to_string(), ct.any());
    env.insert_param_alias(
        "Enumerable.t".to_string(),
        ParameterizedTypeAlias {
            params: vec!["a".to_string()],
            body_tokens: TypeExprBody(toks("a")),
            span: Span::DUMMY,
        },
    );
    let spec = SpecDecl {
        name: "drop".to_string(),
        param_body_tokens: vec![TypeExprBody(toks("Enumerable.t(a)")), TypeExprBody(toks("integer"))],
        result_body_tokens: TypeExprBody(toks("[a]")),
        constraints: vec![],
    };

    let resolved = resolve_spec_decl(&mut ct, &spec, &env).unwrap();
    assert_eq!(
        spec_correspondence_groups(&resolved),
        vec![StructuralCorrespondenceGroup {
            var: TypeVarId(0),
            occurrences: vec![
                StructuralOccurrence::Param {
                    param_index: 0,
                    path: vec![StructuralPathStep::NamedArg(0)],
                },
                StructuralOccurrence::Result {
                    path: vec![StructuralPathStep::ListElem],
                },
            ],
        }]
    );
}

#[test]
fn resolved_spec_reports_reduce_while_invariant_slot_correspondence() {
    let mut ct = crate::types::new();
    let entry_var = ct.type_var(TypeVarId(0));
    let acc_var = ct.type_var(TypeVarId(1));
    let cont = ct.atom_lit("cont");
    let halt = ct.atom_lit("halt");
    let reducer_ret = {
        let cont_tuple = ct.tuple(&[cont, acc_var.clone()]);
        let halt_tuple = ct.tuple(&[halt, acc_var.clone()]);
        ct.union(cont_tuple, halt_tuple)
    };
    let spec = ResolvedSpec {
        params: vec![
            ct.list(entry_var.clone()),
            acc_var.clone(),
            ct.arrow(&[entry_var, acc_var.clone()], reducer_ret),
        ],
        param_shapes: vec![
            ResolvedTypeShape::List(Box::new(ResolvedTypeShape::Var(TypeVarId(0)))),
            ResolvedTypeShape::Var(TypeVarId(1)),
            ResolvedTypeShape::Arrow {
                params: vec![
                    ResolvedTypeShape::Var(TypeVarId(0)),
                    ResolvedTypeShape::Var(TypeVarId(1)),
                ],
                result: Box::new(ResolvedTypeShape::Union(vec![
                    ResolvedTypeShape::Tuple(vec![
                        ResolvedTypeShape::AtomLit("cont".to_string()),
                        ResolvedTypeShape::Var(TypeVarId(1)),
                    ]),
                    ResolvedTypeShape::Tuple(vec![
                        ResolvedTypeShape::AtomLit("halt".to_string()),
                        ResolvedTypeShape::Var(TypeVarId(1)),
                    ]),
                ])),
            },
        ],
        result: acc_var,
        result_shape: ResolvedTypeShape::Var(TypeVarId(1)),
        constraints: HashMap::new(),
    };

    let groups = spec_correspondence_groups(&spec);
    assert_eq!(groups.len(), 2);
    assert_eq!(
        groups.iter().find(|group| group.var == TypeVarId(1)),
        Some(&StructuralCorrespondenceGroup {
            var: TypeVarId(1),
            occurrences: vec![
                StructuralOccurrence::Param {
                    param_index: 1,
                    path: vec![],
                },
                StructuralOccurrence::Result { path: vec![] },
                StructuralOccurrence::CallbackArg {
                    param_index: 2,
                    arg_index: 1,
                    path: vec![],
                },
                StructuralOccurrence::CallbackResult {
                    param_index: 2,
                    path: vec![StructuralPathStep::UnionMember(0), StructuralPathStep::TupleElem(1)],
                },
                StructuralOccurrence::CallbackResult {
                    param_index: 2,
                    path: vec![StructuralPathStep::UnionMember(1), StructuralPathStep::TupleElem(1)],
                },
            ],
        })
    );
}

#[test]
fn build_env_opaque_resource_alias_qualifies_with_module() {
    // The design example: `@type t :: opaque resource(integer)`.
    // Built under module "File", the alias should carry the
    // qualified tag `"File::t"`.
    let attrs = vec![type_alias_attr("t", "opaque resource(integer)")];
    let mut ct = crate::types::new();
    let (env, _o, _b) = build_module_type_env_for_test(&mut ct, &attrs, "File").unwrap();
    let ct = crate::types::new();
    let t = env.get("t").expect("alias resolved");
    assert_eq!(ct.opaque_singleton(t).as_deref(), Some("File::t"));
}

#[test]
fn build_env_opaque_alias_unqualified_at_top_level() {
    // Top-level (no enclosing module) preserves the historical
    // unqualified tag — these opaques have no owner.
    let attrs = vec![type_alias_attr("pid", "opaque integer")];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let ct = crate::types::new();
    let pid = env.get("pid").unwrap();
    assert_eq!(ct.opaque_singleton(pid).as_deref(), Some("pid"));
}

#[test]
fn build_env_opaque_alias_rejects_bad_body() {
    // `opaque <body>` parses the body; an unknown name surfaces.
    let attrs = vec![type_alias_attr("t", "opaque nonesuch")];
    let mut ct = crate::types::new();
    let err = build_module_type_env_for_test(&mut ct, &attrs, "M").unwrap_err();
    assert!(
        err.msg.contains("unknown type name"),
        "expected unknown-name diag from opaque body, got: {}",
        err.msg,
    );
}

#[test]
fn build_env_two_opaque_aliases_are_distinct() {
    let attrs = vec![
        type_alias_attr("pid", "opaque integer"),
        type_alias_attr("timestamp", "opaque integer"),
    ];
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let pid = env.get("pid").unwrap();
    let ts = env.get("timestamp").unwrap();
    let inter = ct.intersect(pid.clone(), ts.clone());
    assert!(
        ct.is_empty(&inter),
        "distinct opaques should be disjoint: pid ∩ timestamp = {}",
        ct.display(&inter),
    );
}

// ---- refines / brand aliases (fz-axu.3 K2) ----

#[test]
fn build_env_refines_alias_creates_brand_descr() {
    let attrs = vec![type_alias_attr("utf8", "refines binary")];
    let mut ct = crate::types::new();
    let (env, _o, brand_inners) = build_module_type_env_for_test(&mut ct, &attrs, "").unwrap();
    let utf8 = env.get("utf8").unwrap();
    assert_eq!(
        ct.brand_singleton(utf8).as_deref(),
        Some("utf8"),
        "alias resolves to brand-of(name): got {}",
        ct.display(utf8),
    );
    let inner = brand_inners.get("utf8").expect("brand_inners records the inner type");
    let str_t = ct.str_t();
    assert!(
        ct.is_equivalent(inner, &str_t),
        "inner of `refines binary` is binary (str_t): got {}",
        ct.display(inner),
    );
}

#[test]
fn build_env_refines_alias_qualifies_with_module() {
    let attrs = vec![type_alias_attr("email", "refines binary")];
    let mut ct = crate::types::new();
    let (env, _o, brand_inners) = build_module_type_env_for_test(&mut ct, &attrs, "Email").unwrap();
    let ct = crate::types::new();
    let email = env.get("email").unwrap();
    assert_eq!(ct.brand_singleton(email).as_deref(), Some("Email::email"));
    assert!(brand_inners.contains_key("Email::email"));
}

#[test]
fn build_env_refines_alias_rejects_empty_body() {
    let attrs = vec![type_alias_attr("bad", "refines")];
    let mut ct = crate::types::new();
    let err = build_module_type_env_for_test(&mut ct, &attrs, "M").unwrap_err();
    assert!(
        err.msg.contains("requires an inner type"),
        "expected diag about missing inner; got: {}",
        err.msg,
    );
}

#[test]
fn build_env_refines_alias_rejects_bad_inner() {
    let attrs = vec![type_alias_attr("bad", "refines nonesuch")];
    let mut ct = crate::types::new();
    let err = build_module_type_env_for_test(&mut ct, &attrs, "M").unwrap_err();
    assert!(
        err.msg.contains("unknown type name"),
        "expected unknown-name diag from refines body; got: {}",
        err.msg,
    );
}

#[test]
fn refines_distinct_from_opaque_with_same_name() {
    // Across two modules: M declares brand B = refines integer; N
    // declares opaque B = opaque integer. Their types come from
    // different axes, so they are lattice-disjoint.
    let m_attrs = vec![type_alias_attr("B", "refines integer")];
    let n_attrs = vec![type_alias_attr("B", "opaque integer")];
    let mut ct = crate::types::new();
    let (m_env, _, _) = build_module_type_env_for_test(&mut ct, &m_attrs, "M").unwrap();
    let (n_env, _, _) = build_module_type_env_for_test(&mut ct, &n_attrs, "N").unwrap();
    let b_brand = m_env.get("B").unwrap();
    let b_opaque = n_env.get("B").unwrap();
    let inter = ct.intersect(b_brand.clone(), b_opaque.clone());
    assert!(
        ct.is_empty(&inter),
        "brand and opaque axes are disjoint: {} ∩ {}",
        ct.display(b_brand),
        ct.display(b_opaque),
    );
}
