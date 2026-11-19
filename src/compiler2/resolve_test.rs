//! Resolver-layer tests for the builtin type-constructor registry: each
//! nullary scalar must resolve to the exact same `Ty` a hand-built call to
//! the corresponding `Types` method produces, and a nullary name applied
//! with arguments must fail with the registry's uniform arity error.

use super::type_expr::TypeExprError;
use super::types::MapKey;
use super::{Namespace, Ty, Types, World};
use crate::ast::{SpecDecl, TypeExprBody};
use crate::parser::lexer::{Lexer, Tok};
use crate::telemetry::ConfiguredTelemetry;

fn resolve(tel: &ConfiguredTelemetry, world: &mut World, src: &str) -> Result<Ty, TypeExprError> {
    let mut sources = crate::source::SourceMap::default();
    let version = sources.add_code(Some("<test>"), src);
    let tokens = Lexer::with_source_version_and_name(src, version, "<test>")
        .tokenize(tel)
        .expect("fragment lexes");
    world.resolve_type_expr_body(Namespace::default(), &TypeExprBody(tokens))
}

type ScalarBuilder = fn(&mut Types) -> Ty;

#[test]
fn nullary_scalars_resolve_to_the_same_ty_as_the_direct_types_call() {
    let tel = ConfiguredTelemetry::new();

    let cases: &[(&str, ScalarBuilder)] = &[
        ("nil", |t| t.nil()),
        ("boolean", |t| t.bool()),
        ("integer", |t| t.int()),
        ("float", |t| t.float()),
        ("c_pointer", |t| t.c_pointer()),
        ("binary", |t| t.str_t()),
        ("atom", |t| t.atom()),
        ("any", |t| t.any()),
        ("term", |t| t.any()),
        ("dynamic", |t| t.any()),
        ("never", |t| t.none()),
        ("utf8", |t| {
            let inner = t.str_t();
            t.mint_brand(inner, "utf8")
        }),
        ("pid", |t| t.pid()),
        ("ref", |t| t.reference()),
        ("map", |t| t.map_top()),
    ];

    for (name, expect_ty) in cases {
        let mut world = World::new();
        let resolved = resolve(&tel, &mut world, name).expect("nullary builtin resolves");

        let mut expect = Types::new();
        let expected = expect_ty(&mut expect);

        // Compare through display rather than raw ids: each `World`/`Types`
        // owns its own interner, so this is a format-agnostic structural
        // check that the registry mints the same type as the direct call —
        // the same technique `compiler2_resolve_spec_...` in world_test.rs
        // uses.
        assert_eq!(
            world.types_mut().display(&resolved),
            expect.display(&expected),
            "`{name}` should resolve to the same Ty the direct Types call produces",
        );
    }
}

#[test]
fn builtin_opaque_source_names_resolve_to_closed_builtin_identities() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    for (name, builtin) in [
        ("pid", super::types::BuiltinOpaque::Pid),
        ("ref", super::types::BuiltinOpaque::Ref),
        ("c_pointer", super::types::BuiltinOpaque::CPointer),
    ] {
        let resolved = resolve(&tel, &mut world, name).expect("builtin opaque resolves");
        assert_eq!(world.types_mut().builtin_opaque_singleton(&resolved), Some(builtin));
        assert_eq!(world.types_mut().opaque_singleton(&resolved), None);
    }
}

#[test]
fn a_nullary_builtin_applied_with_arguments_reports_the_uniform_arity_error() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let error = resolve(&tel, &mut world, "integer(nil)")
        .expect_err("a nullary builtin applied with an argument should fail to resolve");

    assert_eq!(error.msg, "expected 0 type argument(s), got 1 `integer`");
}

/// Elixir's typespecs know only `dynamic()`; the gradual `dynamic(T)` of its
/// type checker is not a typespec, and Elixir refuses it as an undefined type.
#[test]
fn dynamic_takes_no_type_argument() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let error = resolve(&tel, &mut world, "dynamic(integer)")
        .expect_err("dynamic applied with an argument should fail to resolve");

    assert_eq!(error.msg, "expected 0 type argument(s), got 1 `dynamic`");
}

#[test]
fn compact_c_pointer_spelling_is_not_a_builtin_alias() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let error = resolve(&tel, &mut world, "cpointer")
        .expect_err("the legacy spelling should fail rather than silently alias c_pointer");

    assert_eq!(error.msg, "unknown type name `cpointer`");
}

/// `[T]` (structural), `list(T)`, and bare `list` (defaulting the element to
/// `any`) are three syntaxes that must resolve to the identical target `Ty` —
/// the concordance this registry entry exists to prove.
#[test]
fn list_bracket_and_named_forms_resolve_to_the_same_ty() {
    let tel = ConfiguredTelemetry::new();

    let mut world = World::new();
    let bracket = resolve(&tel, &mut world, "[integer]").expect("[T] resolves");
    let named = resolve(&tel, &mut world, "list(integer)").expect("list(T) resolves");
    assert_eq!(
        world.types_mut().display(&bracket),
        world.types_mut().display(&named),
        "`[integer]` and `list(integer)` should resolve to the same Ty"
    );

    let mut world = World::new();
    let bracket_any = resolve(&tel, &mut world, "[any]").expect("[any] resolves");
    let bare = resolve(&tel, &mut world, "list").expect("bare list resolves");
    assert_eq!(
        world.types_mut().display(&bracket_any),
        world.types_mut().display(&bare),
        "`[any]` and bare `list` should resolve to the same Ty"
    );
}

/// `[]` in type position is the empty-LIST type (Elixir typespec parity:
/// `[]` denotes the empty list, `nil` denotes the atom). It must resolve to
/// `Types::empty_list()`, not `Types::nil()` — a different axis (list vs.
/// atom) with a different runtime `ValueKind` tag (LIST vs. ATOM).
#[test]
fn empty_list_brackets_resolve_to_the_empty_list_type_not_nil() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let resolved = resolve(&tel, &mut world, "[]").expect("`[]` resolves");

    let mut expect = Types::new();
    let expected = expect.empty_list();

    assert_eq!(
        world.types_mut().display(&resolved),
        expect.display(&expected),
        "`[]` in type position should resolve to `Types::empty_list()`",
    );

    let mut nil_world = World::new();
    let nil_ty = nil_world.types_mut().nil();
    assert_ne!(
        world.types_mut().display(&resolved),
        nil_world.types_mut().display(&nil_ty),
        "`[]` (empty-list type) must be distinct from `nil` (the atom)",
    );
}

/// `resource(T)` resolves exactly as it did before the registry migration:
/// a payload type wrapped by `Types::resource`.
#[test]
fn resource_with_one_argument_resolves_as_before() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let resolved = resolve(&tel, &mut world, "resource(integer)").expect("resource(T) resolves");

    let mut expect = Types::new();
    let inner = expect.int();
    let expected = expect.resource(inner);

    assert_eq!(
        world.types_mut().display(&resolved),
        expect.display(&expected),
        "`resource(integer)` should resolve to `Types::resource(integer)`"
    );
}

/// Before this migration, `resource(A, B)` silently dropped `B` (the
/// `NameClass::Resource` arm took only `arg_tys.into_iter().next()`). The
/// registry's uniform arity check now diagnoses the extra argument instead
/// of truncating it — the one intended behavior change in this fold.
#[test]
fn resource_with_two_arguments_now_errors_instead_of_silently_dropping_the_second() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let error = resolve(&tel, &mut world, "resource(integer, boolean)")
        .expect_err("resource with two type arguments should now fail to resolve");

    assert_eq!(error.msg, "expected 0 to 1 type argument(s), got 2 `resource`");
}

/// Bare `resource` (no type arguments) resolved before this migration too —
/// the old `NameClass::Resource` arm had the identical `unwrap_or_else(any)`
/// fallback as `list` — so it keeps resolving, defaulting the payload to
/// `any`, under `Arity::Range(0, 1)`.
#[test]
fn bare_resource_resolves_with_an_any_payload() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let resolved = resolve(&tel, &mut world, "resource").expect("bare resource resolves");

    let mut expect = Types::new();
    let any = expect.any();
    let expected = expect.resource(any);

    assert_eq!(
        world.types_mut().display(&resolved),
        expect.display(&expected),
        "bare `resource` should resolve to `Types::resource(any)`"
    );
}

#[test]
fn a_structural_map_type_resolves_to_the_same_ty_as_a_hand_built_exact_map() {
    // `%{ok: integer, err: atom}` — parity with `[T]` for lists: the
    // structural map form must land on the exact same `Ty` as constructing
    // the map directly through `Types::map`.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let resolved = resolve(&tel, &mut world, "%{ok: integer, err: atom}").expect("structural map resolves");

    let mut expect = Types::new();
    let ok_ty = expect.int();
    let err_ty = expect.atom();
    let expected = expect.map(&[
        (MapKey::Atom("ok".to_string()), ok_ty),
        (MapKey::Atom("err".to_string()), err_ty),
    ]);

    assert_eq!(
        world.types_mut().display(&resolved),
        expect.display(&expected),
        "`%{{ok: integer, err: atom}}` should resolve to the same Ty as a hand-built `types.map`",
    );
}

#[test]
fn an_int_keyed_map_type_resolves_using_the_literal_int_key() {
    // `%{1 => atom}` — an int key, read straight off the syntactic literal
    // (the lattice keeps no numeric singletons, so this cannot round-trip
    // through a resolved `Ty`).
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let resolved = resolve(&tel, &mut world, "%{1 => atom}").expect("int-keyed map resolves");

    let mut expect = Types::new();
    let value_ty = expect.atom();
    let expected = expect.map(&[(MapKey::Int(1), value_ty)]);

    assert_eq!(
        world.types_mut().display(&resolved),
        expect.display(&expected),
        "`%{{1 => atom}}` should resolve to the same Ty as a hand-built `types.map` keyed by `MapKey::Int(1)`",
    );
}

#[test]
fn a_non_literal_map_key_is_a_clean_resolution_error() {
    // `%{integer => atom}` — a homogeneous/parametric key the exact-map
    // `Ty` cannot represent. This must fail cleanly rather than silently
    // widen to `map_top`; a real homogeneous-map axis is a separate,
    // unauthorized question.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let error =
        resolve(&tel, &mut world, "%{integer => atom}").expect_err("a non-literal map key should fail to resolve");

    assert!(
        error.msg.contains("literal atom or int"),
        "expected a literal-key diagnostic, got: {}",
        error.msg
    );
}

#[test]
fn an_empty_map_type_resolves_to_the_exact_empty_map() {
    // `%{}` — chosen to denote the exact empty-map type (parity with how
    // `%{}` denotes the empty map value), not the unconstrained `map_top`.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let resolved = resolve(&tel, &mut world, "%{}").expect("empty map resolves");

    let mut expect = Types::new();
    let expected = expect.map(&[]);

    assert_eq!(
        world.types_mut().display(&resolved),
        expect.display(&expected),
        "`%{{}}` should resolve to the exact empty-map Ty, not `map_top`",
    );
}

/// `map` applied with a type argument must fail the same uniform arity
/// check every other nullary builtin does — the named `map` constructor is
/// nullary-only; a homogeneous `map(k, v)` is a separate, unauthorized
/// question.
#[test]
fn map_with_a_type_argument_reports_the_uniform_arity_error() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let error =
        resolve(&tel, &mut world, "map(integer)").expect_err("nullary `map` applied with an argument should fail");

    assert_eq!(error.msg, "expected 0 type argument(s), got 1 `map`");
}

/// `tuple` is the named counterpart to the structural `{T, U}`: the top of
/// the tuple axis, every tuple of every arity.
#[test]
fn bare_tuple_resolves_to_the_tuple_top() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let ty = resolve(&tel, &mut world, "tuple").expect("`tuple` is a builtin constructor name");

    let t = world.types_mut();
    let expected = t.tuple_top();
    assert_eq!(ty, expected);
    let pair = {
        let int = t.int();
        t.tuple(&[int, int])
    };
    assert!(t.is_subtype(&pair, &ty), "`{{T, U}}` is a tuple");
}

/// `fun` is the top of the function axis, every function of every arity, and
/// `function` is the same type, as in Elixir's typespecs.
#[test]
fn fun_and_function_resolve_to_the_function_top() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let fun = resolve(&tel, &mut world, "fun").expect("`fun` is a builtin constructor name");
    let function = resolve(&tel, &mut world, "function").expect("`function` is a builtin constructor name");

    let t = world.types_mut();
    assert_eq!(fun, t.fun_top());
    assert_eq!(function, fun, "`function` is `fun`");
    let unary = {
        let any = t.any();
        t.arrow(&[any], any)
    };
    let binary = {
        let any = t.any();
        t.arrow(&[any, any], any)
    };
    assert!(t.is_subtype(&unary, &fun), "a one-argument function is a function");
    assert!(t.is_subtype(&binary, &fun), "a two-argument function is a function");
}

/// An arrow is the only spelling of a function's signature; `fun` takes no
/// arguments, as `tuple` does.
#[test]
fn applied_fun_reports_the_uniform_arity_error() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let error = resolve(&tel, &mut world, "fun(any)").expect_err("nullary `fun` applied should fail");

    assert_eq!(error.msg, "expected 0 type argument(s), got 1 `fun`");
}

/// `{T, U}` is the only fixed-arity spelling; `tuple` takes no arguments, as `map` does.
#[test]
fn applied_tuple_reports_the_uniform_arity_error() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();

    let error = resolve(&tel, &mut world, "tuple(integer, atom)").expect_err("nullary `tuple` applied should fail");

    assert_eq!(error.msg, "expected 0 type argument(s), got 2 `tuple`");
}

/// A spec body as the front door hands it over: its tokens, without the
/// lexer's end-of-input marker.
fn body(tel: &ConfiguredTelemetry, src: &str) -> TypeExprBody {
    let mut sources = crate::source::SourceMap::default();
    let version = sources.add_code(Some("<test>"), src);
    let mut tokens = Lexer::with_source_version_and_name(src, version, "<test>")
        .tokenize(tel)
        .expect("fragment lexes");
    tokens.retain(|token| !matches!(token.tok, Tok::Eof));
    TypeExprBody(tokens)
}

fn spec_when(tel: &ConfiguredTelemetry, params: &[&str], result: &str, constraints: &[(&str, &str)]) -> SpecDecl {
    SpecDecl {
        name: "f".to_string(),
        param_body_tokens: params.iter().map(|param| body(tel, param)).collect(),
        result_body_tokens: body(tel, result),
        constraints: constraints
            .iter()
            .map(|(var, bound)| (var.to_string(), body(tel, bound)))
            .collect(),
    }
}

/// Elixir's `when a: var` says `a` is a type variable with no bound; only the
/// real bound beside it constrains anything.
#[test]
fn a_var_bound_leaves_its_variable_unconstrained() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let spec = spec_when(&tel, &["a", "b"], "a | b", &[("a", "var"), ("b", "integer")]);

    let resolved = world.resolve_spec(Namespace::default(), &spec).expect("spec resolves");

    let integer = world.types_mut().int();
    let bounds: Vec<Ty> = resolved.constraints.values().copied().collect();
    assert_eq!(bounds, [integer], "only `b: integer` bounds its variable");
}

/// `var` names no type, but its variable still has to be one the spec uses:
/// a misspelled name is reported as it is for any other bound.
#[test]
fn a_var_bound_on_an_unknown_variable_is_refused() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let spec = spec_when(&tel, &["a"], "a", &[("zzz", "var")]);

    let error = world
        .resolve_spec(Namespace::default(), &spec)
        .expect_err("an unused variable's bound is refused");

    assert_eq!(error.msg, "constraint references unknown type variable `zzz`");
}
