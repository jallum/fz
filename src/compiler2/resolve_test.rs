//! Resolver-layer tests for the builtin type-constructor registry: each
//! nullary scalar must resolve to the exact same `Ty` a hand-built call to
//! the corresponding `Types` method produces, and a nullary name applied
//! with arguments must fail with the registry's uniform arity error.

use super::type_expr::TypeExprError;
use super::{Namespace, Ty, Types, World};
use crate::ast::TypeExprBody;
use crate::parser::lexer::Lexer;
use crate::telemetry::ConfiguredTelemetry;

fn resolve(tel: &ConfiguredTelemetry, world: &mut World, src: &str) -> Result<Ty, TypeExprError> {
    let tokens = Lexer::with_source_name(src, "<test>")
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
        ("bool", |t| t.bool()),
        ("integer", |t| t.int()),
        ("float", |t| t.float()),
        ("cpointer", |t| t.cpointer()),
        ("binary", |t| t.str_t()),
        ("atom", |t| t.atom()),
        ("any", |t| t.any()),
        ("never", |t| t.none()),
        ("utf8", |t| {
            let inner = t.str_t();
            t.mint_brand(inner, "utf8")
        }),
        ("pid", |t| t.opaque_of("pid")),
        ("ref", |t| t.opaque_of("ref")),
    ];

    for (name, expect_ty) in cases {
        let mut world = World::new(&tel);
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
fn a_nullary_builtin_applied_with_arguments_reports_the_uniform_arity_error() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);

    let error = resolve(&tel, &mut world, "integer(nil)")
        .expect_err("a nullary builtin applied with an argument should fail to resolve");

    assert_eq!(error.msg, "expected 0 type argument(s), got 1 `integer`");
}
