use super::*;
use crate::compiler2::drive::ExecutionContext;
use crate::compiler2::{DriveOutcome, ExecutableNeed};
use crate::telemetry::ConfiguredTelemetry;

fn aligned_world() -> (World, ActivationKey, CallSiteId) {
    let mut world = World::new();
    world.submit_code(
        Some("inherited-key-coordinate.fz".into()),
        "def aligned(:left, :right), do: :ok\n\
         def aligned({x}, {y}), do: aligned(x, y)\n\
         def aligned(_x, _y), do: :crossed\n\
         def main(), do: aligned({:left}, {:right})\n"
            .into(),
    );
    world.submit_root(None, "main".into(), 0, ExecutableNeed::Value);
    assert!(matches!(
        ExecutionContext::new(&mut world, &ConfiguredTelemetry::new()).drive(),
        DriveOutcome::Resolved
    ));
    let function = world.reference_function(ModuleId::GLOBAL, "aligned", 2);
    let caller = world
        .activation_keys()
        .into_iter()
        .find(|key| key.function == function)
        .unwrap();
    let callsite = *world
        .return_skeleton(function)
        .unwrap()
        .invocations
        .iter()
        .find(|(_, invocation)| invocation.callee.named() == Some(function))
        .unwrap()
        .0;
    assert!(
        world
            .return_unknowns(function)
            .unwrap()
            .callsite(callsite)
            .unwrap()
            .destinations
            .iter()
            .all(KeyShape::is_settled),
        "the projection-only cycle does not independently own a growing position"
    );
    (world, caller, callsite)
}

#[test]
fn a_projection_cycle_keeps_the_callers_existing_unknown_coordinates() {
    let (mut world, mut caller, callsite) = aligned_world();
    let left = world.types_mut().atom_lit("left");
    let right = world.types_mut().atom_lit("right");
    let alpha0 = world.types_mut().param_alpha(0);
    let alpha1 = world.types_mut().param_alpha(1);
    caller = ActivationKey::from_inputs(caller.root, caller.function, &[alpha0, alpha1], world.types_mut());
    let inputs = [ActivationInput::new(left), ActivationInput::new(right)];
    let keyed = key_inputs_for_call(
        &mut world,
        &caller,
        callsite,
        caller.function,
        0,
        &inputs,
        &mut Vec::new(),
    );
    assert_eq!(
        keyed.iter().map(ActivationInput::ty).collect::<Vec<_>>(),
        [alpha0, alpha1],
        "peeling a value already owned by a symbolic input must not mint a concrete depth activation"
    );
    assert_eq!(
        inputs.iter().map(ActivationInput::ty).collect::<Vec<_>>(),
        [left, right],
        "the precise row remains evidence even when its key uses coordinates"
    );
}

#[test]
fn a_direct_concrete_projection_cycle_keeps_its_specialization() {
    let (mut world, mut caller, callsite) = aligned_world();
    let left = world.types_mut().atom_lit("left");
    let right = world.types_mut().atom_lit("right");
    let left_tuple = world.types_mut().tuple(&[left]);
    let right_tuple = world.types_mut().tuple(&[right]);
    caller = ActivationKey::from_inputs(
        caller.root,
        caller.function,
        &[left_tuple, right_tuple],
        world.types_mut(),
    );
    let inputs = [ActivationInput::new(left), ActivationInput::new(right)];
    let keyed = key_inputs_for_call(
        &mut world,
        &caller,
        callsite,
        caller.function,
        0,
        &inputs,
        &mut Vec::new(),
    );
    assert_eq!(keyed, inputs);
}

#[test]
fn source_binding_preserves_settled_fields_beside_inherited_coordinates() {
    use crate::compiler2::return_skeleton::Skeleton;
    use crate::compiler2::semantic::ProjectStep;

    let mut types = Types::new();
    let int = types.int();
    let alpha = types.param_alpha(0);
    let pair = types.tuple(&[int, alpha]);
    let first = Skeleton::project(Skeleton::Input(0), ProjectStep::TupleField(0));
    let second = Skeleton::project(Skeleton::Input(0), ProjectStep::TupleField(1));
    assert_eq!(KeyShape::bind_inputs(&mut types, &first, &[pair]), KeyShape::Settled);
    assert_eq!(KeyShape::bind_inputs(&mut types, &second, &[pair]), KeyShape::Unknown);
    let argument = Skeleton::Tuple(vec![first, second]);
    assert_eq!(
        KeyShape::bind_inputs(&mut types, &argument, &[pair]),
        KeyShape::Tuple(vec![KeyShape::Settled, KeyShape::Unknown])
    );
}

#[test]
fn a_callable_binder_does_not_become_an_unknown_value_coordinate() {
    use crate::compiler2::return_skeleton::Skeleton;

    let mut types = Types::new();
    let alpha = types.param_alpha(0);
    let identity = types.arrow(&[alpha], alpha);
    assert_eq!(
        KeyShape::bind_inputs(&mut types, &Skeleton::Input(0), &[identity]),
        KeyShape::Settled
    );
    let tuple = types.tuple(&[identity, alpha]);
    assert_eq!(
        KeyShape::bind_inputs(&mut types, &Skeleton::Input(0), &[tuple]),
        KeyShape::Tuple(vec![KeyShape::Settled, KeyShape::Unknown])
    );
}

#[test]
fn list_projections_keep_the_inherited_element_coordinate() {
    use crate::compiler2::return_skeleton::Skeleton;
    use crate::compiler2::semantic::ProjectStep;

    let mut types = Types::new();
    let alpha = types.param_alpha(0);
    let list = types.list(alpha);
    let head = Skeleton::project(Skeleton::Input(0), ProjectStep::ListElement);
    let tail = Skeleton::project(Skeleton::Input(0), ProjectStep::ListTail);
    assert_eq!(KeyShape::bind_inputs(&mut types, &head, &[list]), KeyShape::Unknown);
    assert_eq!(
        KeyShape::bind_inputs(&mut types, &tail, &[list]),
        KeyShape::List(Box::new(KeyShape::Unknown))
    );
}

#[test]
fn independent_ground_first_calls_keep_distinct_return_specializations() {
    let mut world = World::new();
    world.submit_code(
        Some("independent-first-coordinates.fz".into()),
        "def first(x, _y), do: x\ndef main(), do: {first(1, :unused), first(1.0, :unused)}\n".into(),
    );
    world.submit_root(None, "main".into(), 0, ExecutableNeed::Value);
    assert!(matches!(
        ExecutionContext::new(&mut world, &ConfiguredTelemetry::new()).drive(),
        DriveOutcome::Resolved
    ));
    let first = world.reference_function(ModuleId::GLOBAL, "first", 2);
    let int = world.types_mut().int();
    let float = world.types_mut().float();
    let activations = world
        .activation_keys()
        .into_iter()
        .filter(|key| key.function == first)
        .filter(|key| world.has_fact(&FactKey::Activation(key.clone())))
        .collect::<Vec<_>>();
    assert_eq!(
        activations
            .iter()
            .map(|key| key.signature.inputs[0])
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([int, float])
    );
    for activation in activations {
        assert_eq!(
            world.activation_return(&activation),
            Some(activation.signature.inputs[0])
        );
    }
}

#[test]
fn inherited_projection_coordinates_also_own_the_return_component_edge() {
    let (mut world, mut caller, callsite) = aligned_world();
    let alpha0 = world.types_mut().param_alpha(0);
    let alpha1 = world.types_mut().param_alpha(1);
    caller = ActivationKey::from_inputs(caller.root, caller.function, &[alpha0, alpha1], world.types_mut());
    let left = world.types_mut().atom_lit("left");
    let right = world.types_mut().atom_lit("right");
    let left_tuple = world.types_mut().tuple(&[left]);
    let right_tuple = world.types_mut().tuple(&[right]);
    let tel = ConfiguredTelemetry::new();
    let evaluation = evaluate_activation(
        &mut world,
        &tel,
        &caller,
        &ActivationInputAlternatives::from_row(vec![left_tuple, right_tuple]),
    )
    .unwrap();
    assert_eq!(
        evaluation.rows[0].calls[0].targets[0].key, caller,
        "the source projection must retain its caller's admitted symbolic coordinate"
    );
    let effects = commit_activation_evaluation(&mut world, &tel, evaluation);
    world.complete_job(Job::AnalyzeActivation(caller.clone()), effects);
    let component = world
        .return_membership(&caller)
        .into_component()
        .expect("a call that carries an inherited unknown has the same shared return ownership as its key");
    assert_eq!(component.members, [caller.clone()]);
    assert_eq!(component.unknowns.slots(), [(caller.clone(), 0), (caller.clone(), 1)]);
    let reads = world.return_membership(&caller).reads(&world);
    assert!(reads.contains(&FactKey::CallSiteTargets(CallSiteKey {
        activation: caller.clone(),
        callsite
    })));
    assert!(reads.contains(&FactKey::ReturnSkeleton(caller.function)));
    assert!(reads.contains(&FactKey::ReturnUnknowns(caller.function)));
}

#[test]
fn inherited_projection_membership_is_symmetric_across_the_shape_peel() {
    let (mut world, mut caller, _) = aligned_world();
    let alpha0 = world.types_mut().param_alpha(0);
    let alpha1 = world.types_mut().param_alpha(1);
    let tuple0 = world.types_mut().tuple(&[alpha0]);
    let tuple1 = world.types_mut().tuple(&[alpha1]);
    caller = ActivationKey::from_inputs(caller.root, caller.function, &[tuple0, tuple1], world.types_mut());
    let left = world.types_mut().atom_lit("left");
    let right = world.types_mut().atom_lit("right");
    let left_tuple = world.types_mut().tuple(&[left]);
    let right_tuple = world.types_mut().tuple(&[right]);
    let tel = ConfiguredTelemetry::new();
    let evaluation = evaluate_activation(
        &mut world,
        &tel,
        &caller,
        &ActivationInputAlternatives::from_row(vec![left_tuple, right_tuple]),
    )
    .unwrap();
    let callee = evaluation.rows[0].calls[0].targets[0].key.clone();
    assert_ne!(caller, callee, "one structural peel changes the addressed shape once");
    assert_eq!(callee.signature.inputs.as_ref(), [alpha0, alpha1]);
    let effects = commit_activation_evaluation(&mut world, &tel, evaluation);
    world.complete_job(Job::AnalyzeActivation(caller.clone()), effects);
    let from_caller = world
        .return_membership(&caller)
        .into_component()
        .expect("outgoing inherited edge");
    let from_callee = world
        .return_membership(&callee)
        .into_component()
        .expect("incoming inherited edge");
    assert_eq!(from_caller, from_callee);
    assert_eq!(
        from_caller.members.into_iter().collect::<BTreeSet<_>>(),
        BTreeSet::from([caller, callee])
    );
}

#[test]
fn a_captured_call_keeps_the_positional_input_from_its_own_source_row() {
    use std::cell::Cell;
    use std::rc::Rc;

    let tel = ConfiguredTelemetry::new();
    let walks = Rc::new(Cell::new(0));
    let counts = walks.clone();
    tel.attach_raw_event2::<ActivationKey, ActivationInputAlternatives, _>(
        &["fz", "compiler2", "inference_work", "activation_walk"],
        move |_, _, _, _, _| {
            counts.set(counts.get() + 1);
            assert!(
                counts.get() <= 80,
                "the two finite capture rows must settle without unbounded refinement"
            );
        },
    );
    let mut world = World::new();
    world.submit_code(
        Some("capture-source-row-binding.fz".into()),
        concat!(
            "def same(:a, :a), do: :ok\n",
            "def same(:b, :b), do: :ok\n",
            "def same(_x, _y), do: :crossed\n",
            "def invoke(capture, argument) do\n",
            " f = fn (value) -> same(capture, value) end\n",
            " f.(argument)\nend\n",
            "def main(), do: invoke(:a, :a)\n",
        )
        .into(),
    );
    let root = world.submit_root(None, "main".into(), 0, ExecutableNeed::Value);
    assert!(matches!(
        ExecutionContext::new(&mut world, &tel).drive(),
        DriveOutcome::Resolved
    ));
    let invoke = world.reference_function(ModuleId::GLOBAL, "invoke", 2);
    let alpha0 = world.types_mut().param_alpha(0);
    let alpha1 = world.types_mut().param_alpha(1);
    let caller = ActivationKey::from_inputs(root, invoke, &[alpha0, alpha1], world.types_mut());
    let a = world.types_mut().atom_lit("a");
    let b = world.types_mut().atom_lit("b");
    // Supply two admitted rows to one shared caller through its normal seed
    // fact. The paper edges are closure[a](a) and closure[b](b), never either
    // captured value paired with the argument from the other source row.
    let mut seed = super::super::root::seed_activation(&caller).unwrap();
    seed.activation_input_contributions = [a, b]
        .into_iter()
        .map(|ty| (caller.clone(), vec![ActivationInput::new(ty), ActivationInput::new(ty)]))
        .collect();
    world.complete_job(Job::SeedActivation(caller.clone()), seed);
    world.demand(Job::AnalyzeActivation(caller.clone()));
    assert!(matches!(
        ExecutionContext::new(&mut world, &tel).drive(),
        DriveOutcome::Resolved
    ));
    let ok = world.types_mut().atom_lit("ok");
    let actual = world.activation_return(&caller);
    let actual_display = actual.map(|ty| world.types().display(&ty));
    assert_eq!(
        actual,
        Some(ok),
        "binding the source family must preserve which row supplied each closure's capture and argument; actual {actual_display:?}"
    );
}
