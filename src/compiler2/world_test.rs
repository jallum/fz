use super::facts::FactUse;
use super::keying::DispatchDemand;
use super::{DriveOutcome, FactKey, Job, ModuleId, ModuleInterface, Namespace, TypeName, Types, World};
use crate::ast::Attribute;
use crate::compiler2::drive::JobEffects;
use crate::telemetry::{Capture, ConfiguredTelemetry, Event, Value};

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
    // Scope stashes the raw source eagerly; the body fact is noted only when the
    // demand above is driven (fz-f98.14.5), so read the stash before drive.
    assert!(
        world.pending_function_source(function).is_some(),
        "scoping should stash the grouped quoted function source before define",
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
    // fz-hwn.27.14 + .27.13: `resolve_spec` addresses the whole spec scope at
    // the binder, so the spec's result variable `x` is the RESULT-SLOT ADDRESS
    // r0 — not an encounter ordinal — and now renders legibly as `r0` rather
    // than a bare `αN`.
    let expect_r0 = expect.result_alpha();
    assert_eq!(
        world.types_mut().display(&resolved.result),
        expect.display(&expect_r0),
        "the result is the result-slot address r0 (the spec's `x`), rendered legibly",
    );
    let r0 = world.types_mut().result_alpha();
    assert_eq!(
        resolved.result, r0,
        "the spec result is addressed to r0 by construction"
    );

    // The `when x: tkf_box(tkf_elem)` bound resolves to list(integer), keyed by
    // the variable the result names — re-keyed onto its address r0 through the
    // resolver's name→address env.
    assert_eq!(resolved.constraints.len(), 1, "one when-clause bound");
    let r0_id = world.types_mut().result_alpha_id();
    let bound = resolved
        .constraints
        .get(&r0_id)
        .copied()
        .expect("x is constrained, keyed by its address r0");
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
    // Raw source lives in the eager stash until demand (fz-f98.14.5); clone it so
    // it survives the later define drive.
    let raw = world
        .pending_function_source(main)
        .expect("scoping should stash raw function source")
        .clone();
    assert!(
        world.fact_revision(&FactKey::ExpandedFunctionSource(main)).is_none(),
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
    assert!(world.define_dispatch_mask(function, vec![DispatchDemand::Ignore]));

    // A recursive fn's non-dispatch slot collapses to its convergence class
    // in the KEY (list(int) -> list(any)), while the body-input EVIDENCE
    // keeps the precise type. (Numeric literals no longer exist to widen;
    // the list collapse is the surviving canonicalization.)
    let int = world.types_mut().int();
    let raw_input = world.types_mut().list(int);
    let key = world.activation_key(root, function, &[raw_input]);
    let canonical_input = key.inputs(world.types())[0];

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
fn compiler2_recursive_activation_key_ignores_accumulator_list_shape() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = world.submit_root(None, "main".to_string(), 0, super::ExecutableNeed::Value);
    let function = world.reference_function(ModuleId::GLOBAL, "partition", 4);
    assert!(world.define_recursive(function, true));
    assert!(world.define_dispatch_mask(
        function,
        vec![
            DispatchDemand::Whole,
            DispatchDemand::ListShape(Box::new(DispatchDemand::Whole)),
            DispatchDemand::Ignore,
            DispatchDemand::Ignore,
        ],
    ));

    let int = world.types_mut().int();
    let list_int = world.types_mut().list(int);
    let empty = world.types_mut().empty_list();
    let non_empty = world.types_mut().non_empty_list(int);

    let initial = world.activation_key(root, function, &[int, non_empty, empty, empty]);
    let lo_accumulated = world.activation_key(root, function, &[int, list_int, non_empty, empty]);
    let hi_accumulated = world.activation_key(root, function, &[int, list_int, empty, non_empty]);

    assert_eq!(
        initial, lo_accumulated,
        "ignored accumulator list shape must not split recursive activation keys",
    );
    assert_eq!(
        initial, hi_accumulated,
        "ignored accumulator list shape must not split recursive activation keys",
    );
}

#[test]
fn compiler2_recursive_activation_key_ignores_tuple_accumulator_list_shape() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = world.submit_root(None, "main".to_string(), 0, super::ExecutableNeed::Value);
    let function = world.reference_function(ModuleId::GLOBAL, "split_while_cont", 3);
    assert!(world.define_recursive(function, true));
    assert!(world.define_dispatch_mask(
        function,
        vec![
            DispatchDemand::ListShape(Box::new(DispatchDemand::Ignore)),
            DispatchDemand::Ignore,
            DispatchDemand::Ignore,
        ],
    ));

    let int = world.types_mut().int();
    let list_int = world.types_mut().list(int);
    let empty = world.types_mut().empty_list();
    let non_empty = world.types_mut().non_empty_list(int);
    let initial_acc = world.types_mut().tuple(&[empty, empty]);
    let left_accumulated = world.types_mut().tuple(&[non_empty, empty]);
    let right_accumulated = world.types_mut().tuple(&[empty, non_empty]);
    let callable_a = {
        let result = world.types_mut().atom_lit("cont");
        world.types_mut().arrow(&[int], result)
    };
    let callable_b = {
        let result = world.types_mut().atom_lit("halt");
        world.types_mut().arrow(&[int], result)
    };

    let initial = world.activation_key(root, function, &[list_int, initial_acc, callable_a]);
    let left = world.activation_key(root, function, &[list_int, left_accumulated, callable_a]);
    let right = world.activation_key(root, function, &[list_int, right_accumulated, callable_b]);

    assert_eq!(
        initial, left,
        "ignored tuple accumulator list shape must not split recursive activation keys",
    );
    assert_eq!(
        initial, right,
        "ignored callable surface details must not split recursive activation keys",
    );
}

#[test]
fn compiler2_activation_input_join_is_quiet_for_equivalent_list_evidence() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = world.submit_root(None, "main".to_string(), 0, super::ExecutableNeed::Value);
    let function = world.reference_function(ModuleId::GLOBAL, "subtract", 1);
    assert!(world.define_recursive(function, false));
    assert!(world.define_dispatch_mask(function, vec![DispatchDemand::Whole]));

    let int = world.types_mut().int();
    let list_int = world.types_mut().list(int);
    let non_empty_int = world.types_mut().non_empty_list(int);
    let equivalent_list = world.types_mut().union(list_int, non_empty_int);
    assert!(
        world.types().is_equivalent(&list_int, &equivalent_list),
        "test setup should model telemetry's equivalent list evidence, got {} vs {}",
        world.types_mut().display(&list_int),
        world.types_mut().display(&equivalent_list),
    );

    let key = world.activation_key(root, function, &[list_int]);
    world.complete_job(
        Job::SeedRoot(root),
        JobEffects {
            activation_input_contributions: vec![(key.clone(), vec![list_int]), (key.clone(), vec![equivalent_list])],
            ..JobEffects::default()
        },
    );

    assert_eq!(
        world.activation_inputs(&key),
        Some(vec![list_int]),
        "one publisher should keep the first representative instead of manufacturing list | list evidence",
    );
    let revision = world
        .fact_revision(&FactKey::ActivationInputs(key.clone()))
        .expect("activation-input fact should exist after the first contribution");

    let step = world.complete_job(
        Job::AnalyzeActivation(key.clone()),
        JobEffects {
            activation_input_contributions: vec![(key.clone(), vec![equivalent_list])],
            ..JobEffects::default()
        },
    );
    assert_eq!(
        world.fact_revision(&FactKey::ActivationInputs(key.clone())),
        Some(revision),
        "an equivalent contribution from another publisher should not advance the activation-input revision",
    );
    assert!(
        step.changed
            .iter()
            .all(|change| change.key != FactKey::ActivationInputs(key.clone())),
        "equivalent activation-input evidence should not requeue semantic work",
    );
}

#[test]
fn compiler2_activation_analysis_preserves_prior_input_frontier() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = world.submit_root(None, "main".to_string(), 0, super::ExecutableNeed::Value);
    let caller = world.reference_function(ModuleId::GLOBAL, "caller", 1);
    let callee = world.reference_function(ModuleId::GLOBAL, "callee", 1);
    assert!(world.define_recursive(caller, true));
    assert!(world.define_dispatch_mask(caller, vec![DispatchDemand::Whole]));
    assert!(world.define_recursive(callee, true));
    assert!(world.define_dispatch_mask(callee, vec![DispatchDemand::Whole]));

    let int = world.types_mut().int();
    let caller_key = world.activation_key(root, caller, &[int]);
    let callee_key = world.activation_key(root, callee, &[int]);

    world.complete_job(
        Job::AnalyzeActivation(caller_key.clone()),
        JobEffects {
            activation_input_contributions: vec![(callee_key.clone(), vec![int])],
            ..JobEffects::default()
        },
    );
    let revision = world
        .fact_revision(&FactKey::ActivationInputs(callee_key.clone()))
        .expect("callee input evidence should be published");

    let step = world.complete_job(
        Job::AnalyzeActivation(caller_key),
        JobEffects {
            activation_input_contributions: vec![],
            ..JobEffects::default()
        },
    );

    assert_eq!(
        world.activation_inputs(&callee_key),
        Some(vec![int]),
        "semantic analysis should not retract prior activation-input evidence when a callsite temporarily disappears",
    );
    assert_eq!(
        world.fact_revision(&FactKey::ActivationInputs(callee_key.clone())),
        Some(revision),
        "preserving the semantic frontier should avoid a withdrawal revision",
    );
    assert!(
        step.changed
            .iter()
            .all(|change| change.key != FactKey::ActivationInputs(callee_key.clone())),
        "preserving the semantic frontier should not requeue activation analysis",
    );
}

#[test]
fn compiler2_recursive_list_shape_key_accepts_joined_list_family_evidence() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = world.submit_root(None, "main".to_string(), 0, super::ExecutableNeed::Value);
    let function = world.reference_function(ModuleId::GLOBAL, "delete_first", 2);
    assert!(world.define_recursive(function, true));
    assert!(world.define_dispatch_mask(
        function,
        vec![
            DispatchDemand::ListShape(Box::new(DispatchDemand::Whole)),
            DispatchDemand::Ignore,
        ],
    ));

    let int = world.types_mut().int();
    let list_int = world.types_mut().list(int);
    let non_empty_int = world.types_mut().non_empty_list(int);
    let joined_list_family = world.types_mut().union(list_int, non_empty_int);

    let direct = world.activation_key(root, function, &[list_int, int]);
    let joined = world.activation_key(root, function, &[joined_list_family, int]);
    assert_eq!(
        direct, joined,
        "recursive list-shape keys should not split when upstream evidence is an equivalent joined list family",
    );
}

#[test]
fn compiler2_activation_inputs_retract_one_publishers_stale_contribution() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = world.submit_root(None, "main".to_string(), 0, super::ExecutableNeed::Value);
    let function = world.reference_function(ModuleId::GLOBAL, "loop", 1);
    assert!(world.define_recursive(function, false));
    assert!(world.define_dispatch_mask(function, vec![DispatchDemand::Whole]));

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
    assert!(world.define_dispatch_mask(function, vec![DispatchDemand::Whole]));

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

/// The bare drive's demand-on-stall pass: a waiter blocked on a fact whose
/// mapped producer has never run must not stall — the wait is the demand, the
/// fact->producer map expands it, and the drive completes.
#[test]
fn compiler2_drive_demands_the_blocked_facts_producer_on_stall() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler2", "drive", "demand_on_stall"], capture.handler());
    let demanded_facts: std::rc::Rc<std::cell::RefCell<Vec<Vec<FactKey>>>> =
        std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    let demanded_facts_sink = std::rc::Rc::clone(&demanded_facts);
    tel.attach(
        &["fz", "compiler2", "drive", "demand_on_stall"],
        Box::new(move |event: &Event<'_, '_, '_>| {
            let Some(facts) = event
                .metadata
                .get("demanded_facts")
                .and_then(Value::downcast_ref::<Vec<FactKey>>)
            else {
                return;
            };
            demanded_facts_sink.borrow_mut().push(facts.clone());
        }),
    );
    let mut world = World::new(&tel);
    let root = world.submit_root(None, "main".to_string(), 0, super::ExecutableNeed::Value);
    // Take the submit-root ignition out of the agenda: this test isolates the
    // stall pass, so nothing may be ready when the drive starts.
    assert_eq!(world.work_graph.pop(), Some(Job::SeedRoot(root)));
    world.submit_code(Some("stall.fz".to_string()), "fn echoval(a), do: a\n".to_string());
    let function = world.reference_function(ModuleId::GLOBAL, "echoval", 1);
    // Settle echoval/1's own facts up front (outside the isolated stall pass
    // below): the activation frontier now demands full analysis for every
    // discovered activation, so `key_a`'s later `AnalyzeActivation` needs a
    // real, fully-lowered callee to conclude against.
    world.demand(Job::DefineFunction(function));
    world.demand(Job::LowerFunction(function));
    world.demand(Job::PlanEntryDispatch(function));
    world.demand(Job::DeriveRecursive(function));
    world.demand(Job::DeriveDispatchMask(function));
    assert_eq!(
        world.drive(),
        DriveOutcome::Resolved,
        "echoval/1's own facts should settle before the isolated stall-pass setup",
    );
    let input_a = world.types_mut().atom_lit("a");
    let input_b = world.types_mut().atom_lit("b");
    let key_a = world.activation_key(root, function, &[input_a]);
    let key_b = world.activation_key(root, function, &[input_b]);

    // A real waiter blocks on a fact no enqueued or concluded job produces.
    world.complete_job(
        Job::SeedActivation(key_b.clone()),
        JobEffects {
            waits: vec![FactUse::settled(FactKey::Activation(key_a.clone()))],
            ..JobEffects::default()
        },
    );
    assert_eq!(world.work_graph.pending_jobs(), 0);

    assert_eq!(
        world.drive(),
        DriveOutcome::Resolved,
        "the stall pass should demand the blocked fact's mapped producer and complete the drive",
    );
    assert!(
        world.has_fact(&FactKey::Activation(key_a.clone())),
        "the demanded producer should have run and published the blocked fact",
    );
    assert!(
        world.has_fact(&FactKey::Activation(key_b)),
        "the woken waiter should have concluded once its wait settled",
    );
    assert!(
        !capture
            .find(&["fz", "compiler2", "drive", "demand_on_stall"])
            .is_empty(),
        "the drive should report that the demand-on-stall pass fired",
    );
    assert!(
        demanded_facts
            .borrow()
            .iter()
            .any(|facts| facts.contains(&FactKey::Activation(key_a.clone()))),
        "demand_on_stall should name the blocked fact it poked a producer for",
    );
}

/// A blocked fact with no fact->producer arm is the genuine stall: the drive
/// must report it unresolved, never spin the demand-on-stall pass on it.
#[test]
fn compiler2_drive_reports_unmapped_blocked_facts_as_unresolved() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let function = world.reference_function(ModuleId::GLOBAL, "main", 0);
    world.complete_job(
        Job::DeriveRecursive(function),
        JobEffects {
            waits: vec![FactUse::current(FactKey::GuardDispatch(function))],
            ..JobEffects::default()
        },
    );

    let DriveOutcome::Unresolved { waits } = world.drive() else {
        panic!("a blocked fact with no mapped producer must surface as the genuine stall");
    };
    assert!(
        waits
            .iter()
            .any(|wait| *wait.fact.fact() == FactKey::GuardDispatch(function)),
        "the unresolved report should carry the unmapped blocked fact: {waits:?}",
    );
}
