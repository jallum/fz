use super::facts::FactUse;
use super::{DriveOutcome, FactKey, Job, ModuleId, ModuleInterface, Namespace, TypeName, TypeVarId, Types, World};
use crate::ast::Attribute;
use crate::compiler2::drive::JobEffects;
use crate::specs::ResolvedTypeShape;
use crate::telemetry::ConfiguredTelemetry;

#[test]
#[should_panic(expected = "modules should be scoped before definition")]
fn compiler2_world_define_module_panics_for_unscoped_module() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let module = world.reference_module("Unscoped");

    let _ = world.define_module(module, Namespace::default(), ModuleInterface::default());
}

#[test]
#[should_panic(expected = "module interface should only be read when it exists")]
fn compiler2_world_module_interface_panics_for_unscoped_module() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let module = world.reference_module("Unscoped");

    let _ = world.module_interface(module);
}

#[test]
fn compiler2_world_submitted_module_interface_is_available_without_module_definition() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let module = world.submit_module_interface("IfaceOnly".to_string(), ModuleInterface::default());

    assert_eq!(world.module_interface(module), ModuleInterface::default());
    assert!(world.module_defined_revision(module).is_none());
    assert!(world.module_interface_revision(module).is_none());
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "publishing an interface-only module should settle without body definition",
    );
    assert!(world.module_interface_revision(module).is_some());
}

#[test]
#[should_panic(expected = "modules should be indexed before scoping")]
fn compiler2_world_scope_module_panics_for_unindexed_module() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let module = world.reference_module("Unindexed");

    world.scope_module(module, Namespace::default());
}

#[test]
fn compiler2_resolve_spec_resolves_types_shapes_and_constraints_against_the_captured_namespace() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let code = world.submit_code(
        Some("spec.fz".to_string()),
        include_str!("../../fixtures2/00049_resolve_spec.fz").to_string(),
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
        "defined function materialization should be demandable when a caller actually needs it",
    );
    assert!(
        world.function_source(function).is_some(),
        "scoping should note the grouped quoted function source before define",
    );
    let outcome = world.drive();
    assert!(
        matches!(outcome, DriveOutcome::Resolved),
        "demanding the function should derive its function surface on demand",
    );
    let (source, surface) = world.function_definition(function);
    let spec = surface
        .attrs
        .iter()
        .find_map(|attr| match attr {
            Attribute::Spec(spec) => Some(spec.clone()),
            _ => None,
        })
        .expect("tkf_f declares an @spec");
    let resolved = world
        .resolve_spec(source.namespace, &spec)
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

#[test]
fn compiler2_define_function_stages_expanded_source_before_definition() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let code = world.submit_code(Some("staged_source.fz".to_string()), "fn main(), do: 42\n".to_string());
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "indexing should resolve"
    );
    assert!(world.demand(Job::ScopeCode(code)), "scoping should be demandable");
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "scoping should resolve"
    );

    let main = world.reference_function(ModuleId::GLOBAL, "main", 0);
    let raw = world
        .function_source(main)
        .expect("scoping should note raw function source");
    assert!(
        world.fact_revision(FactKey::ExpandedFunctionSource(main)).is_none(),
        "scoping alone should not yet stage expanded function source",
    );

    assert!(
        world.demand(Job::DefineFunction(main)),
        "DefineFunction should be demandable"
    );
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "demanding the function should stage expanded source and then define it",
    );

    let expanded = world
        .expanded_function_source(main)
        .expect("DefineFunction should first materialize staged expanded source");
    assert_eq!(
        raw.source.key(),
        expanded.source.key(),
        "before raw publication flips over, staged expanded source should preserve the same quoted root",
    );
    assert!(
        world.function_defined_revision(main).is_some(),
        "the function should end the drive in the defined state",
    );
}

#[test]
fn compiler2_activation_inputs_are_distinct_from_the_canonical_activation_key() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = world.submit_root(None, "main".to_string(), 0, super::ExecutableNeed::Value);
    let function = world.reference_function(ModuleId::GLOBAL, "loop", 1);
    assert!(world.define_recursive(function, true));
    assert!(world.define_dispatch_mask(function, vec![false]));

    // A recursive fn's non-dispatch slot collapses to its convergence class
    // in the KEY (list(int) -> list(any)), while the body-input EVIDENCE
    // keeps the precise type. (Numeric literals no longer exist to widen;
    // the list collapse is the surviving canonicalization.)
    let int = world.types_mut().int();
    let raw_input = world.types_mut().list(int);
    let key = world.activation_key(root, function, &[raw_input]);
    let canonical_input = key.input[0];

    world.complete_job(
        Job::SeedRoot(root),
        JobEffects {
            activation_input_contributions: vec![(key.clone(), vec![raw_input])],
            ..JobEffects::default()
        },
    );

    let observed_inputs = world
        .activation_inputs(&key)
        .expect("publishing activation inputs should materialize a separate body-evidence fact");
    assert_eq!(
        observed_inputs,
        vec![raw_input],
        "activation body evidence should preserve the published caller input",
    );
    assert!(
        !world.types().is_equivalent(&canonical_input, &observed_inputs[0]),
        "recursive key convergence should not overwrite the separate activation-input evidence",
    );
}

#[test]
fn compiler2_activation_inputs_retract_one_publishers_stale_contribution() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = world.submit_root(None, "main".to_string(), 0, super::ExecutableNeed::Value);
    let function = world.reference_function(ModuleId::GLOBAL, "loop", 1);
    assert!(world.define_recursive(function, false));
    assert!(world.define_dispatch_mask(function, vec![true]));

    let input_a = world.types_mut().atom_lit("a");
    let input_b = world.types_mut().atom_lit("b");
    let key = world.activation_key(root, function, &[input_a]);

    world.complete_job(
        Job::SeedRoot(root),
        JobEffects {
            activation_input_contributions: vec![(key.clone(), vec![input_a])],
            ..JobEffects::default()
        },
    );
    world.complete_job(
        Job::AnalyzeActivation(key.clone()),
        JobEffects {
            activation_input_contributions: vec![(key.clone(), vec![input_b])],
            ..JobEffects::default()
        },
    );

    let step = world.complete_job(Job::SeedRoot(root), JobEffects::default());
    assert!(
        step.changed.iter().any(|change| {
            change.key == FactKey::ActivationInputs(key.clone())
                && change.old_revision.is_some()
                && change.new_revision.is_some()
                && change.new_revision > change.old_revision
        }),
        "retracting one publisher should republish the still-present activation-input fact when the joined body evidence changes",
    );
    assert_eq!(
        world.activation_inputs(&key),
        Some(vec![input_b]),
        "the surviving publisher's input should remain as the body evidence after the stale contribution retracts",
    );
}

#[test]
fn compiler2_waiting_job_keeps_activation_input_contributions() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = world.submit_root(None, "main".to_string(), 0, super::ExecutableNeed::Value);
    let function = world.reference_function(ModuleId::GLOBAL, "loop", 1);
    assert!(world.define_recursive(function, false));
    assert!(world.define_dispatch_mask(function, vec![true]));

    let input = world.types_mut().int_lit(1);
    let key = world.activation_key(root, function, &[input]);

    world.complete_job(
        Job::SeedRoot(root),
        JobEffects {
            activation_input_contributions: vec![(key.clone(), vec![input])],
            ..JobEffects::default()
        },
    );
    assert!(world.activation_inputs(&key).is_some());

    // A blocked re-run of the same publisher lists no contributions. Pausing
    // must not withdraw the standing body evidence.
    world.complete_job(
        Job::SeedRoot(root),
        JobEffects {
            waits: vec![FactUse::current(FactKey::FunctionDefined(function))],
            ..JobEffects::default()
        },
    );
    assert_eq!(
        world.activation_inputs(&key),
        Some(vec![input]),
        "a waiting completion must not withdraw the publisher's standing contributions",
    );
}
