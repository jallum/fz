use std::collections::{HashMap, HashSet};

use super::World;
use super::identity::{ActivationKey, RootId};
use super::semantic::{
    ActivationInputAlternatives, ActivationInputMap, CallSiteSummary, CallTargetSummary, CallableDemand, RuntimeDemand,
    SelectedCallee, ShapeDemand,
};
use crate::compiler2::Job;

/// A consumer states a tuple demand field by field, and two consumers of
/// one tuple rarely read the same fields. `TupleFields` is a prefix: a body
/// that reads only field 0 says one field, a body that reads field 1 says
/// two. Joining those is padding the shorter one with `ignore`, not
/// throwing both away -- a value nobody read cannot be evidence about a
/// value somebody did, and the callable obligation on field 0 has to
/// survive the arrival of a sibling.
#[test]
fn joining_tuple_field_demands_of_different_length_keeps_every_field() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let callable = RuntimeDemand::callable(CallableDemand::resolved(vec![int], world.types_mut()));
    let first_field_only = RuntimeDemand::tuple_fields(vec![callable.clone()]);
    let second_field_only = RuntimeDemand::tuple_fields(vec![RuntimeDemand::ignore(), RuntimeDemand::whole()]);

    let joined = first_field_only.join(&second_field_only);

    let ShapeDemand::TupleFields(fields) = &joined.shape else {
        panic!("two field demands join to a field demand, not {:?}", joined.shape);
    };
    assert_eq!(fields.len(), 2, "the join spans every field either side named");
    assert_eq!(
        fields[0], callable,
        "the callable obligation on a field only one side read still stands"
    );
    assert_eq!(fields[1], RuntimeDemand::whole());
    assert_eq!(
        second_field_only.join(&first_field_only),
        joined,
        "the join does not depend on which consumer is seen first"
    );
}

/// A provider boundary is somebody else's code: it publishes a call surface,
/// not a compiler2 executable, so nothing downstream can emit a direct edge
/// to it or ground a return against its executable fact. The activation field
/// is not the test -- a summary carrying one anyway must still be refused,
/// because the callee kind is what decides who owns the body.
#[test]
fn a_provider_boundary_is_never_the_one_owned_target() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "impl", 1);
    let activation = ActivationKey::from_inputs(RootId::for_test(0), function, &[int], world.types_mut());
    let target = |callee| CallTargetSummary {
        callee,
        surface_inputs: vec![int],
        activation: Some(activation.clone()),
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let summary = |callee| CallSiteSummary {
        targets: vec![target(callee)],
        return_ty: None,
    };

    assert!(
        summary(SelectedCallee::ProviderBoundary(function))
            .single_owned_target()
            .is_none(),
        "a provider boundary owns no executable to call directly",
    );
    assert_eq!(
        summary(SelectedCallee::Function(function))
            .single_owned_target()
            .map(|(_, activation)| activation.clone()),
        Some(activation),
        "a compiler-owned callee with one activation is the target",
    );
}

fn membership_key(world: &mut World) -> ActivationKey {
    let int = world.types_mut().int();
    let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "owner", 1);
    ActivationKey::from_inputs(RootId::for_test(0), function, &[int], world.types_mut())
}

/// A publisher that contributed a concrete row and later concludes naming
/// no rows for that key has not retracted anything: `ActivationInputs` is
/// cumulative evidence, and a publisher's silence within a drive is not
/// knowledge that the row stopped being true.
#[test]
fn a_later_silent_conclusion_leaves_the_joined_evidence_and_frontier_standing() {
    let mut world = World::new();
    let key = membership_key(&mut world);
    let none = world.types_mut().none();
    let int = world.types_mut().int();
    let walk = Job::AnalyzeActivation(key.clone());
    let solve = Job::SolveReturnComponent(key.clone());
    let mut map = ActivationInputMap::new();

    map.conclude_preserving_frontier(
        world.types_mut(),
        walk,
        HashSet::new(),
        HashMap::from([(key.clone(), ActivationInputAlternatives::from_row(vec![none, none]))]),
    );

    map.conclude_preserving_frontier(
        world.types_mut(),
        solve.clone(),
        HashSet::new(),
        HashMap::from([(key.clone(), ActivationInputAlternatives::from_row(vec![int, int]))]),
    );
    let rows_now = |map: &ActivationInputMap<Job>, key: &ActivationKey| {
        map.get(key)
            .map(|alternatives| alternatives.rows().iter().map(|row| row.tys()).collect::<Vec<_>>())
    };
    assert_eq!(
        rows_now(&map, &key),
        Some(vec![vec![int, int]]),
        "the concrete row dominates the none row, so the joined antichain keeps only it",
    );

    let silent =
        map.conclude_preserving_frontier(world.types_mut(), solve, HashSet::from([key.clone()]), HashMap::new());

    assert_eq!(
        rows_now(&map, &key),
        Some(vec![vec![int, int]]),
        "a later conclusion naming no rows must not retract the publisher's standing row",
    );
    assert_eq!(
        silent.output_keys,
        HashSet::from([key]),
        "the publisher's frontier keeps the key it once named",
    );
    assert!(
        silent.changed_keys.is_empty(),
        "an unchanged frontier reports no movement"
    );
}

/// The sibling arm's contrast: `conclude_exact` is for evidence whose
/// silence about a key genuinely is a retraction, so a later conclusion
/// naming no rows withdraws what stood.
#[test]
fn conclude_exact_withdraws_a_key_the_publisher_stops_naming() {
    let mut world = World::new();
    let key = membership_key(&mut world);
    let int = world.types_mut().int();
    let publisher = Job::AnalyzeActivation(key.clone());
    let mut map = ActivationInputMap::new();

    let seeded = map.conclude_exact(
        world.types_mut(),
        publisher.clone(),
        HashSet::new(),
        HashMap::from([(key.clone(), ActivationInputAlternatives::from_row(vec![int]))]),
    );
    assert_eq!(map.get(&key), Some(&ActivationInputAlternatives::from_row(vec![int])));

    let withdrawn = map.conclude_exact(world.types_mut(), publisher, seeded.output_keys, HashMap::new());

    assert!(
        map.get(&key).is_none(),
        "an exact conclusion naming no rows withdraws the row the publisher stops naming",
    );
    assert_eq!(
        withdrawn.changed_keys,
        HashSet::from([key]),
        "the withdrawal is reported as movement"
    );
}

/// Two publishers each stand behind their own row for one key. When one of
/// them concludes exactly and names the key no more, only its row goes; the
/// other publisher's correlation is untouched.
#[test]
fn an_exact_withdrawal_retracts_only_the_withdrawing_publishers_rows() {
    let mut world = World::new();
    let key = membership_key(&mut world);
    let seen_a = world.types_mut().atom_lit("a");
    let seen_b = world.types_mut().atom_lit("b");
    let first = Job::AnalyzeActivation(key.clone());
    let second = Job::SolveReturnComponent(key.clone());
    let mut map = ActivationInputMap::new();

    let first_frontier = map.conclude_exact(
        world.types_mut(),
        first.clone(),
        HashSet::new(),
        HashMap::from([(key.clone(), ActivationInputAlternatives::from_row(vec![seen_a]))]),
    );
    map.conclude_exact(
        world.types_mut(),
        second,
        HashSet::new(),
        HashMap::from([(key.clone(), ActivationInputAlternatives::from_row(vec![seen_b]))]),
    );
    let rows_now = |map: &ActivationInputMap<Job>| {
        map.get(&key)
            .map(|alternatives| alternatives.rows().iter().map(|row| row.tys()).collect::<Vec<_>>())
    };
    assert_eq!(
        rows_now(&map),
        Some(vec![vec![seen_a], vec![seen_b]]),
        "two publishers' distinct rows coexist as alternatives",
    );

    let withdrawn = map.conclude_exact(world.types_mut(), first, first_frontier.output_keys, HashMap::new());

    assert_eq!(
        rows_now(&map),
        Some(vec![vec![seen_b]]),
        "withdrawing one publisher retracts exactly its row",
    );
    assert_eq!(
        withdrawn.changed_keys,
        HashSet::from([key.clone()]),
        "the narrowed join is reported as movement",
    );
}

/// A solo publisher's own frontier survives a pass that names nothing: the
/// key it once contributed stays in its output set and the standing row is
/// untouched.
#[test]
fn preserving_frontier_conclusion_keeps_a_solo_publishers_row_when_it_later_names_nothing() {
    let mut world = World::new();
    let key = membership_key(&mut world);
    let input = world.types_mut().atom_lit("seen");
    let publisher = Job::AnalyzeActivation(key.clone());
    let mut map = ActivationInputMap::new();

    let first = map.conclude_preserving_frontier(
        world.types_mut(),
        publisher.clone(),
        HashSet::new(),
        HashMap::from([(key.clone(), ActivationInputAlternatives::from_row(vec![input]))]),
    );
    assert_eq!(first.output_keys, HashSet::from([key.clone()]));
    assert_eq!(map.get(&key), Some(&ActivationInputAlternatives::from_row(vec![input])));

    let silent = map.conclude_preserving_frontier(
        world.types_mut(),
        publisher,
        HashSet::from([key.clone()]),
        HashMap::new(),
    );

    assert_eq!(
        silent.output_keys,
        HashSet::from([key.clone()]),
        "a pass that names nothing must not retract the publisher's prior edge"
    );
    assert!(
        silent.changed_keys.is_empty(),
        "preserving an unchanged frontier should not mark the activation input dirty"
    );
    assert_eq!(map.get(&key), Some(&ActivationInputAlternatives::from_row(vec![input])));
}

/// The joined aggregate must not depend on `HashMap`'s native iteration
/// order: the fold that builds it is pinned to a deterministic,
/// publisher-identity-derived key, not to insertion order.
#[test]
fn contribution_key_waves_allocate_identically_across_reverse_insertion() {
    let run = |reverse: bool| {
        let mut world = World::new();
        let root = RootId::for_test(92);
        let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "contribution_order", 1);
        let int = world.types_mut().int();
        let float = world.types_mut().float();
        let atom_a = world.types_mut().atom_lit("a");
        let atom_b = world.types_mut().atom_lit("b");
        let list = world.types_mut().list(int);
        let non_empty = world.types_mut().non_empty_list(int);
        let list_key = ActivationKey::from_inputs(root, function, &[list], world.types_mut());
        let non_empty_key = ActivationKey::from_inputs(root, function, &[non_empty], world.types_mut());
        let mut map = ActivationInputMap::new();
        let publisher_a = Job::SeedRoot(root);
        let publisher_b = Job::AnalyzeActivation(list_key.clone());
        let first = HashMap::from([
            (list_key.clone(), ActivationInputAlternatives::from_row(vec![int])),
            (
                non_empty_key.clone(),
                ActivationInputAlternatives::from_row(vec![float]),
            ),
        ]);
        map.conclude_preserving_frontier(world.types_mut(), publisher_a, HashSet::new(), first);
        let second = if reverse {
            [
                (
                    non_empty_key.clone(),
                    ActivationInputAlternatives::from_row(vec![atom_b]),
                ),
                (list_key.clone(), ActivationInputAlternatives::from_row(vec![atom_a])),
            ]
            .into_iter()
            .collect()
        } else {
            HashMap::from([
                (list_key.clone(), ActivationInputAlternatives::from_row(vec![atom_a])),
                (
                    non_empty_key.clone(),
                    ActivationInputAlternatives::from_row(vec![atom_b]),
                ),
            ])
        };
        map.conclude_preserving_frontier(
            world.types_mut(),
            publisher_b,
            HashSet::from([list_key.clone(), non_empty_key.clone()]),
            second,
        );
        (
            map.get(&list_key).expect("list contribution").rows()[0].inputs()[0].ty(),
            map.get(&non_empty_key).expect("non-empty contribution").rows()[0].inputs()[0].ty(),
            world.types().identity_inventory(),
        )
    };

    assert_eq!(run(false), run(true));
}
