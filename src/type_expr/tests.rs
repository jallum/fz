use super::*;

use crate::lexer::Lexer;
use crate::types::{ConcreteTypes, Ty, Types};

fn parse_one<T: Types<Ty = Ty>>(t: &mut T, src: &str) -> Result<T::Ty, TypeExprError> {
    parse_one_with(t, src, &ModuleTypeEnv::new())
}

fn parse_one_with<T: Types<Ty = Ty>>(
    t: &mut T,
    src: &str,
    env: &ModuleTypeEnv,
) -> Result<T::Ty, TypeExprError> {
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

#[test]
fn scalar_names_parse_to_corresponding_descrs() {
    let mut ct = ConcreteTypes;
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
fn atom_literal_parses_to_singleton() {
    let mut ct = ConcreteTypes;
    let ok = ct.atom_lit("ok");
    let err = ct.atom_lit("error");
    let a = parse_one(&mut ct, ":ok").unwrap();
    let b = parse_one(&mut ct, ":error").unwrap();
    assert!(ct.is_equivalent(&a, &ok));
    assert!(ct.is_equivalent(&b, &err));
}

#[test]
fn int_literal_parses_to_singleton() {
    let mut ct = ConcreteTypes;
    let i42 = ct.int_lit(42);
    let i0 = ct.int_lit(0);
    let a = parse_one(&mut ct, "42").unwrap();
    let b = parse_one(&mut ct, "0").unwrap();
    assert!(ct.is_equivalent(&a, &i42));
    assert!(ct.is_equivalent(&b, &i0));
}

#[test]
fn float_literal_parses_to_singleton() {
    let mut ct = ConcreteTypes;
    let expected = ct.float_lit(2.5);
    let actual = parse_one(&mut ct, "2.5").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn list_of_integer() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let expected = ct.list(int);
    let actual = parse_one(&mut ct, "[integer]").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn empty_list_is_nil() {
    let mut ct = ConcreteTypes;
    let nil = ct.nil();
    let actual = parse_one(&mut ct, "[]").unwrap();
    assert!(ct.is_equivalent(&actual, &nil));
}

#[test]
fn tuple_two_elements() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let atom = ct.atom();
    let expected = ct.tuple(&[int, atom]);
    let actual = parse_one(&mut ct, "{integer, atom}").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn tuple_three_elements_with_literal() {
    let mut ct = ConcreteTypes;
    let ok = ct.atom_lit("ok");
    let int = ct.int();
    let expected = ct.tuple(&[ok, int.clone(), int]);
    let actual = parse_one(&mut ct, "{:ok, integer, integer}").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn empty_tuple() {
    let mut ct = ConcreteTypes;
    let expected = ct.tuple(&[]);
    let actual = parse_one(&mut ct, "{}").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn arrow_zero_arg() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let expected = ct.arrow(&[], int);
    let actual = parse_one(&mut ct, "() -> integer").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn arrow_one_arg() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let arg = int.clone();
    let expected = ct.arrow(std::slice::from_ref(&arg), int);
    let actual = parse_one(&mut ct, "(integer) -> integer").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn arrow_two_args() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let float = ct.float();
    let bin = ct.str_t();
    let expected = ct.arrow(&[int, float], bin);
    let actual = parse_one(&mut ct, "(integer, float) -> binary").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn paren_grouping_one_element() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let actual = parse_one(&mut ct, "(integer)").unwrap();
    assert!(ct.is_equivalent(&actual, &int));
}

#[test]
fn paren_grouping_with_union() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let float = ct.float();
    let expected = ct.union(int, float);
    let actual = parse_one(&mut ct, "(integer | float)").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn paren_multi_without_arrow_errors() {
    let mut ct = ConcreteTypes;
    let r = parse_one(&mut ct, "(integer, float)");
    assert!(
        r.is_err(),
        "multi-element paren without `->` must error; got ok",
    );
}

#[test]
fn union_two_axes() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let float = ct.float();
    let expected = ct.union(int, float);
    let actual = parse_one(&mut ct, "integer | float").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn union_three_axes_is_left_associative_but_equivalent() {
    let mut ct = ConcreteTypes;
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
    let mut ct = ConcreteTypes;
    let ok = ct.atom_lit("ok");
    let err = ct.atom_lit("error");
    let expected = ct.union(ok, err);
    let actual = parse_one(&mut ct, ":ok | :error").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn list_of_union() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let float = ct.float();
    let u = ct.union(int, float);
    let expected = ct.list(u);
    let actual = parse_one(&mut ct, "[integer | float]").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn nested_tuple_inside_list() {
    let mut ct = ConcreteTypes;
    let ok = ct.atom_lit("ok");
    let int = ct.int();
    let tup = ct.tuple(&[ok, int]);
    let expected = ct.list(tup);
    let actual = parse_one(&mut ct, "[{:ok, integer}]").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn arrow_taking_arrow_argument() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let arg = int.clone();
    let f = ct.arrow(std::slice::from_ref(&arg), int.clone());
    let l = ct.list(int);
    let expected = ct.arrow(&[f, l.clone()], l);
    let actual = parse_one(&mut ct, "((integer) -> integer, [integer]) -> [integer]").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn named_ref_resolves_via_env() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let mut env = ModuleTypeEnv::new();
    env.insert("id".to_string(), int.clone());
    let actual = parse_one_with(&mut ct, "id", &env).unwrap();
    assert!(ct.is_equivalent(&actual, &int));
}

#[test]
fn named_ref_used_in_arrow_via_env() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let mut env = ModuleTypeEnv::new();
    env.insert("id".to_string(), int.clone());
    let arg = int.clone();
    let expected = ct.arrow(std::slice::from_ref(&arg), int);
    let actual = parse_one_with(&mut ct, "(id) -> id", &env).unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn unknown_name_with_empty_env_errors() {
    let mut ct = ConcreteTypes;
    let r = parse_one(&mut ct, "nonesuch");
    assert!(r.is_err());
    let e = r.unwrap_err();
    assert!(e.msg.contains("unknown type name"), "msg = {}", e.msg);
}

#[test]
fn builtin_name_takes_precedence_over_alias() {
    // A user-defined alias must NOT shadow a builtin scalar name.
    let mut ct = ConcreteTypes;
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
    let mut ct = ConcreteTypes;
    assert!(parse_one(&mut ct, "[integer").is_err());
}

#[test]
fn malformed_unclosed_tuple_errors() {
    let mut ct = ConcreteTypes;
    assert!(parse_one(&mut ct, "{integer, atom").is_err());
}

#[test]
fn malformed_unclosed_paren_errors() {
    let mut ct = ConcreteTypes;
    assert!(parse_one(&mut ct, "(integer").is_err());
}

#[test]
fn trailing_tokens_error() {
    let mut ct = ConcreteTypes;
    let r = parse_one(&mut ct, "integer foo");
    assert!(r.is_err(), "trailing tokens must be rejected");
}

#[test]
fn primary_position_rejects_bar() {
    // `| integer` is malformed — `|` is a binary operator.
    let mut ct = ConcreteTypes;
    assert!(parse_one(&mut ct, "| integer").is_err());
}

// ----- fz-ul4.31.3: build_module_type_env -----

fn type_alias_attr(name: &str, body_src: &str) -> crate::ast::Attribute {
    use crate::ast::{Attribute, TypeAliasDecl};
    use crate::diag::Span;
    let toks = Lexer::new(body_src).tokenize().expect("lex body");
    // Drop trailing Eof to match parser behavior.
    let body_tokens: Vec<_> = toks
        .into_iter()
        .filter(|t| !matches!(t.tok, Tok::Eof))
        .collect();
    Attribute::TypeAlias(TypeAliasDecl {
        name: name.to_string(),
        name_span: Span::DUMMY,
        body_tokens: crate::ast::TypeExprBody(body_tokens),
        span: Span::DUMMY,
    })
}

#[test]
fn build_env_resolves_simple_alias() {
    let attrs = vec![type_alias_attr("id", "integer")];
    let mut ct = crate::types::ConcreteTypes;
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let int = ct.int();
    assert!(ct.is_equivalent(env.get("id").unwrap(), &int));
}

#[test]
fn build_env_resolves_alias_of_alias_in_either_order() {
    // Declare in forward order: a refs b, b is plain.
    let attrs = vec![type_alias_attr("a", "b"), type_alias_attr("b", "integer")];
    let mut ct = crate::types::ConcreteTypes;
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let int = ct.int();
    assert!(ct.is_equivalent(env.get("a").unwrap(), &int));
    assert!(ct.is_equivalent(env.get("b").unwrap(), &int));
}

#[test]
fn build_env_resolves_composite_alias() {
    // pair := {id, id}; id := integer.
    let attrs = vec![
        type_alias_attr("pair", "{id, id}"),
        type_alias_attr("id", "integer"),
    ];
    let mut ct = crate::types::ConcreteTypes;
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let int = ct.int();
    let expected = ct.tuple(&[int.clone(), int]);
    assert!(ct.is_equivalent(env.get("pair").unwrap(), &expected));
}

#[test]
fn build_env_detects_simple_cycle() {
    let attrs = vec![type_alias_attr("a", "b"), type_alias_attr("b", "a")];
    let mut ct = crate::types::ConcreteTypes;
    let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
    assert!(
        err.msg.contains("cycle"),
        "expected cycle diag, got: {}",
        err.msg
    );
}

#[test]
fn build_env_detects_three_way_cycle() {
    let attrs = vec![
        type_alias_attr("a", "b"),
        type_alias_attr("b", "c"),
        type_alias_attr("c", "a"),
    ];
    let mut ct = crate::types::ConcreteTypes;
    let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
    assert!(
        err.msg.contains("cycle"),
        "expected cycle diag, got: {}",
        err.msg
    );
}

#[test]
fn build_env_rejects_unknown_reference() {
    let attrs = vec![type_alias_attr("foo", "nonesuch")];
    let mut ct = crate::types::ConcreteTypes;
    let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
    assert!(
        err.msg.contains("unknown type name"),
        "expected unknown-name diag, got: {}",
        err.msg
    );
}

#[test]
fn build_env_rejects_duplicate_alias() {
    let attrs = vec![
        type_alias_attr("id", "integer"),
        type_alias_attr("id", "float"),
    ];
    let mut ct = crate::types::ConcreteTypes;
    let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
    assert!(
        err.msg.contains("duplicate"),
        "expected duplicate diag, got: {}",
        err.msg
    );
}

#[test]
fn build_env_ignores_non_type_alias_attributes() {
    use crate::ast::Attribute;
    let attrs = vec![
        Attribute::ModuleDoc("hello".to_string()),
        type_alias_attr("id", "integer"),
        Attribute::Doc("a doc".to_string()),
    ];
    let mut ct = crate::types::ConcreteTypes;
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    assert_eq!(env.len(), 1);
    let int = ct.int();
    assert!(ct.is_equivalent(env.get("id").unwrap(), &int));
}

#[test]
fn build_env_empty_for_module_without_aliases() {
    let attrs: Vec<crate::ast::Attribute> = vec![];
    let mut ct = crate::types::ConcreteTypes;
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    assert!(env.is_empty());
}

#[test]
fn build_env_resolves_arrow_using_alias() {
    let attrs = vec![
        type_alias_attr("id", "integer"),
        type_alias_attr("idfn", "(id) -> id"),
    ];
    let mut ct = crate::types::ConcreteTypes;
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let int = ct.int();
    let arg = int.clone();
    let expected = ct.arrow(std::slice::from_ref(&arg), int);
    assert!(ct.is_equivalent(env.get("idfn").unwrap(), &expected));
}

#[test]
fn consumed_count_reports_correct_position() {
    // Parser returns how many tokens it consumed, so callers can
    // continue parsing whatever follows (e.g., the `::` separator
    // in `@spec name(T) :: R`).
    let toks = Lexer::new("integer foo").tokenize().unwrap();
    let env = ModuleTypeEnv::new();
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let (ty, consumed) = parse_type_expr(&mut ct, &toks, &env).unwrap();
    assert!(ct.is_equivalent(&ty, &int));
    assert_eq!(consumed, 1, "consumed only the `integer` token");
}

// ---- vector(T) ----

#[test]
fn vector_integer_parses() {
    let mut ct = ConcreteTypes;
    let expected = ct.vec(crate::types::VectorElem::Integer);
    let actual = parse_one(&mut ct, "vector(integer)").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn vector_float_parses() {
    let mut ct = ConcreteTypes;
    let expected = ct.vec(crate::types::VectorElem::Float);
    let actual = parse_one(&mut ct, "vector(float)").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn vector_u8_parses() {
    let mut ct = ConcreteTypes;
    let expected = ct.vec(crate::types::VectorElem::U8);
    let actual = parse_one(&mut ct, "vector(u8)").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn vector_bit_parses() {
    let mut ct = ConcreteTypes;
    let expected = ct.vec(crate::types::VectorElem::Bit);
    let actual = parse_one(&mut ct, "vector(bit)").unwrap();
    assert!(ct.is_equivalent(&actual, &expected));
}

#[test]
fn vector_unknown_elem_type_errors() {
    let mut ct = ConcreteTypes;
    let r = parse_one(&mut ct, "vector(atom)");
    assert!(r.is_err(), "vector(atom) should error");
}

// ---- opaque aliases ----

#[test]
fn build_env_opaque_alias_creates_nominal_type() {
    let attrs = vec![type_alias_attr("pid", "opaque integer")];
    let mut ct = crate::types::ConcreteTypes;
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
    let mut ct = crate::types::ConcreteTypes;
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let pid = env.get("pid").unwrap();
    let int = ct.int();
    assert!(
        !ct.is_subtype(pid, &int),
        "pid should NOT be a subtype of integer"
    );
    assert!(
        !ct.is_subtype(&int, pid),
        "integer should NOT be a subtype of pid"
    );
}

// ---- resource(T) (fz-swt.6) ----

#[test]
fn resource_integer_parses_to_builtin_opaque_tag() {
    // `resource(T)` is a parametric opaque ctor. The result has the
    // unqualified built-in tag `"resource"`; visibility for user
    // aliases (`@type t :: opaque resource(integer)`) comes from
    // the *outer* opaque alias, not from this tag.
    let mut ct = ConcreteTypes;
    let d = parse_one(&mut ct, "resource(integer)").unwrap();
    assert_eq!(ct.opaque_singleton(&d).as_deref(), Some("resource"));
}

#[test]
fn resource_inner_type_is_validated() {
    let mut ct = ConcreteTypes;
    let r = parse_one(&mut ct, "resource(nonesuch)");
    assert!(r.is_err(), "unknown inner type must error");
}

#[test]
fn build_env_opaque_resource_alias_qualifies_with_module() {
    // The design example: `@type t :: opaque resource(integer)`.
    // Built under module "File", the alias should carry the
    // qualified tag `"File::t"`.
    let attrs = vec![type_alias_attr("t", "opaque resource(integer)")];
    let mut ct = crate::types::ConcreteTypes;
    let (env, _o, _b) = build_module_type_env_for(&mut ct, &attrs, "File").unwrap();
    let ct = crate::types::ConcreteTypes;
    let t = env.get("t").expect("alias resolved");
    assert_eq!(ct.opaque_singleton(t).as_deref(), Some("File::t"));
}

#[test]
fn build_env_opaque_alias_unqualified_at_top_level() {
    // Top-level (no enclosing module) preserves the legacy
    // unqualified tag — these opaques have no owner.
    let attrs = vec![type_alias_attr("pid", "opaque integer")];
    let mut ct = crate::types::ConcreteTypes;
    let env = build_module_type_env(&mut ct, &attrs).unwrap();
    let ct = crate::types::ConcreteTypes;
    let pid = env.get("pid").unwrap();
    assert_eq!(ct.opaque_singleton(pid).as_deref(), Some("pid"));
}

#[test]
fn build_env_opaque_alias_rejects_bad_body() {
    // `opaque <body>` parses the body; an unknown name surfaces.
    let attrs = vec![type_alias_attr("t", "opaque nonesuch")];
    let mut ct = crate::types::ConcreteTypes;
    let err = build_module_type_env_for(&mut ct, &attrs, "M").unwrap_err();
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
    let mut ct = crate::types::ConcreteTypes;
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
    let mut ct = crate::types::ConcreteTypes;
    let (env, _o, brand_inners) = build_module_type_env_for(&mut ct, &attrs, "").unwrap();
    let utf8 = env.get("utf8").unwrap();
    assert_eq!(
        ct.brand_singleton(utf8).as_deref(),
        Some("utf8"),
        "alias resolves to brand-of(name): got {}",
        ct.display(utf8),
    );
    let inner = brand_inners
        .get("utf8")
        .expect("brand_inners records the inner type");
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
    let mut ct = crate::types::ConcreteTypes;
    let (env, _o, brand_inners) = build_module_type_env_for(&mut ct, &attrs, "Email").unwrap();
    let ct = crate::types::ConcreteTypes;
    let email = env.get("email").unwrap();
    assert_eq!(ct.brand_singleton(email).as_deref(), Some("Email::email"));
    assert!(brand_inners.contains_key("Email::email"));
}

#[test]
fn build_env_refines_alias_rejects_empty_body() {
    let attrs = vec![type_alias_attr("bad", "refines")];
    let mut ct = crate::types::ConcreteTypes;
    let err = build_module_type_env_for(&mut ct, &attrs, "M").unwrap_err();
    assert!(
        err.msg.contains("requires an inner type"),
        "expected diag about missing inner; got: {}",
        err.msg,
    );
}

#[test]
fn build_env_refines_alias_rejects_bad_inner() {
    let attrs = vec![type_alias_attr("bad", "refines nonesuch")];
    let mut ct = crate::types::ConcreteTypes;
    let err = build_module_type_env_for(&mut ct, &attrs, "M").unwrap_err();
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
    let mut ct = crate::types::ConcreteTypes;
    let (m_env, _, _) = build_module_type_env_for(&mut ct, &m_attrs, "M").unwrap();
    let (n_env, _, _) = build_module_type_env_for(&mut ct, &n_attrs, "N").unwrap();
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
