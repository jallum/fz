use super::{DriveOutcome, Job, ModuleId, Namespace, TypeName, TypeVarId, Types, World};
use crate::ast::Attribute;
use crate::specs::ResolvedTypeShape;
use crate::telemetry::ConfiguredTelemetry;

#[test]
#[should_panic(expected = "modules should be scoped before definition")]
fn compiler2_world_define_module_panics_for_unscoped_module() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let module = world.reference_module("Unscoped");

    let _ = world.define_module(module, Namespace::default(), Vec::new());
}

#[test]
#[should_panic(expected = "module exports should only be read from defined modules")]
fn compiler2_world_module_exports_panics_for_unscoped_module() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let module = world.reference_module("Unscoped");

    let _ = world.module_exports(module);
}

#[test]
#[should_panic(expected = "modules should be indexed before scoping")]
fn compiler2_world_scope_module_panics_for_unindexed_module() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let module = world.reference_module("Unindexed");

    let _ = world.scope_module(module, Namespace::default());
}

#[test]
fn compiler2_resolve_spec_resolves_types_shapes_and_constraints_against_the_captured_namespace() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let code = world.submit_code(
        Some("spec.fz".to_string()),
        concat!(
            "@type tkf_elem :: integer\n",
            "@type tkf_box(a) :: [a]\n",
            "@spec tkf_f(tkf_box(float), tkf_elem) :: x when x: tkf_box(tkf_elem)\n",
            "fn tkf_f(p, q), do: q\n",
        )
        .to_string(),
    );
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "indexing should resolve"
    );
    assert!(world.demand(Job::ScopeCode(code)), "scoping should be demandable");
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "scoping should resolve"
    );

    // resolve_spec reads each referenced type from the TypeDefined store, so pull
    // them first — the production order the contract seam will follow.
    let elem = TypeName {
        module: ModuleId::GLOBAL,
        name: "tkf_elem".to_string(),
        arity: 0,
    };
    let boxed = TypeName {
        module: ModuleId::GLOBAL,
        name: "tkf_box".to_string(),
        arity: 1,
    };
    assert!(world.demand(Job::DeriveTypeDef(elem)));
    assert!(world.demand(Job::DeriveTypeDef(boxed)));
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "the referenced types should resolve"
    );

    let function = world.reference_function(ModuleId::GLOBAL, "tkf_f", 2);
    assert!(
        world.demand(Job::DefineFunction(function)),
        "legacy function materialization should be demandable when a caller actually needs it",
    );
    assert!(
        world.function_source(function).is_some(),
        "scoping should note the grouped quoted function source before define",
    );
    let outcome = world.drive();
    assert!(
        matches!(outcome, DriveOutcome::Resolved),
        "demanding the function should derive its legacy compatibility shape on demand",
    );
    let def = world.function_definition(function);
    let spec = def
        .legacy_ast
        .attrs
        .iter()
        .find_map(|attr| match attr {
            Attribute::Spec(spec) => Some(spec.clone()),
            _ => None,
        })
        .expect("tkf_f declares an @spec");
    let resolved = world
        .resolve_spec(def.namespace, &spec)
        .expect("the spec resolves against the function's captured namespace");

    // Expected hard types, rendered through the same interner for a format-
    // agnostic comparison.
    let mut expect = Types::new();
    let float = expect.float();
    let list_float = expect.list(float);
    let int = expect.int();
    let list_int = expect.list(int);
    let var0 = expect.type_var(TypeVarId(0));

    assert_eq!(resolved.params.len(), 2, "two declared parameters");
    assert_eq!(
        world.types_mut().display(&resolved.params[0]),
        expect.display(&list_float),
        "tkf_box(float) instantiates the box template to a list of float",
    );
    assert_eq!(
        world.types_mut().display(&resolved.params[1]),
        expect.display(&int),
        "tkf_elem resolves to its integer inner",
    );
    assert_eq!(
        world.types_mut().display(&resolved.result),
        expect.display(&var0),
        "the result is the free variable `x`, bound to id 0 on first sight",
    );

    // Shapes carry the same variable numbering and keep declared names nominal.
    assert_eq!(
        resolved.param_shapes,
        vec![
            ResolvedTypeShape::Named {
                name: "tkf_box".to_string(),
                args: vec![ResolvedTypeShape::Float],
            },
            ResolvedTypeShape::Named {
                name: "tkf_elem".to_string(),
                args: Vec::new(),
            },
        ],
    );
    assert_eq!(resolved.result_shape, ResolvedTypeShape::Var(TypeVarId(0)));

    // The `when x: tkf_box(tkf_elem)` bound resolves to list(integer), keyed by
    // the very variable the result names.
    assert_eq!(resolved.constraints.len(), 1, "one when-clause bound");
    let bound = resolved
        .constraints
        .get(&TypeVarId(0))
        .copied()
        .expect("x is constrained");
    assert_eq!(
        world.types_mut().display(&bound),
        expect.display(&list_int),
        "tkf_box(tkf_elem) instantiates to a list of integer",
    );
}
