use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

use super::*;
use crate::compiler2::drive::ExecutionContext;
use crate::compiler2::{DriveOutcome, ExecutableNeed};
use crate::telemetry::ConfiguredTelemetry;

/// Drives one fixture to a resolved root, the way every door does, while
/// recording every `ActivationKey` a `ReturnType` was ever defined for.
/// The structural-rule tests below read that set instead of reconstructing
/// a key by hand: a recursive function's key is a convergence class over
/// its own input rows (`World::canonical_activation_key_with_callable_surfaces`),
/// not the literal argument type any one call site observed, and the
/// telemetry the production pipeline already emits at every `ReturnType`
/// revision names the actual key it settled on.
fn drive_fixture(tel: &ConfiguredTelemetry, name: &str, source: &str) -> (World, Rc<RefCell<HashSet<ActivationKey>>>) {
    let seen: Rc<RefCell<HashSet<ActivationKey>>> = Rc::new(RefCell::new(HashSet::new()));
    let sink = Rc::clone(&seen);
    tel.attach_raw_event2::<World, ActivationKey, _>(
        &["fz", "compiler2", "return_type", "defined"],
        move |_, _, _, _, activation| {
            sink.borrow_mut().insert(activation.clone());
        },
    );

    let mut world = World::new();
    world.submit_code(Some(name.to_string()), source.to_string());
    world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert!(
        matches!(ExecutionContext::new(&mut world, tel).drive(), DriveOutcome::Resolved),
        "{name} should drive its main/0 root to a resolved product",
    );
    (world, seen)
}

/// The one `ActivationKey` a recursive function's own calls collapsed to.
/// A widened recursive function shares exactly one activation across every
/// specialization its own calls address (`RETURN_LADDERS` in `drive_test.rs`
/// pins this for these same fixtures); more than one match here means that
/// premise broke.
fn sole_activation(seen: &HashSet<ActivationKey>, function: FunctionId, label: &str) -> ActivationKey {
    let matches: Vec<&ActivationKey> = seen.iter().filter(|key| key.function == function).collect();
    assert_eq!(
        matches.len(),
        1,
        "{label} should collapse to exactly one shared activation across its recursive calls, found {matches:?}",
    );
    matches[0].clone()
}

/// Every `ActivationKey` a function's calls addressed. `alias_cycle_with_entry`
/// carries no `RETURN_LADDERS` row (it settles under the widening ceiling
/// without ever collapsing rows into one convergence class), so `cont/2` is
/// reached once from `enter/1` with an empty accumulator and once more, in
/// steady state, from `step/2` with a growing one -- two distinct concrete
/// keys, neither a specialization of the other.
fn activations(seen: &HashSet<ActivationKey>, function: FunctionId) -> Vec<ActivationKey> {
    seen.iter().filter(|key| key.function == function).cloned().collect()
}

/// Re-runs the pure walk over a settled activation to read the
/// `ReturnExpression` it produced, the same value `evaluate_activation`
/// handed `commit_activation_evaluation` during the real drive.
fn expression_for(world: &mut World, tel: &ConfiguredTelemetry, activation: &ActivationKey) -> ReturnExpression {
    let alternatives = world
        .activation_input_alternatives(activation)
        .expect("a key seen in a return_type.defined event must have settled input evidence")
        .clone();
    evaluate_activation(world, tel, activation, &alternatives)
        .expect("re-evaluating an already-settled activation must not refuse")
        .expression
}

#[test]
fn nest_1_addresses_its_own_recursive_call_by_key() {
    let tel = ConfiguredTelemetry::new();
    let (mut world, seen) = drive_fixture(
        &tel,
        "self_guarded_nest.fz",
        include_str!("../../../fixtures2/behavior/self_guarded_nest.fz"),
    );

    let nest = world.reference_function(ModuleId::GLOBAL, "nest", 1);
    let activation = sole_activation(&seen.borrow(), nest, "nest/1");
    let expression = expression_for(&mut world, &tel, &activation);

    let ReturnExpression::Union(members) = &expression else {
        panic!("nest/1's two clauses should join into a Union: {expression:?}");
    };
    assert_eq!(members.len(), 2, "nest/1 has exactly two clauses: {members:?}");
    assert!(
        matches!(members[0], ReturnExpression::Published(_)),
        "nest(0) -> 0 publishes a plain type with no call involved: {:?}",
        members[0],
    );
    let ReturnExpression::NonEmptyList(element) = &members[1] else {
        panic!(
            "nest(n) -> [nest(n - 1)] builds a flat literal, provably non-empty on its own: {:?}",
            members[1],
        );
    };
    let ReturnExpression::Local(key) = element.as_ref() else {
        panic!("the list's one element must address nest's own activation: {element:?}");
    };
    assert_eq!(key.function, nest, "the recursive call resolves straight back to nest");
}

#[test]
fn f_1_keeps_its_own_recursive_call_apart_from_an_unrelated_one() {
    let tel = ConfiguredTelemetry::new();
    let (mut world, seen) = drive_fixture(
        &tel,
        "false_embedding.fz",
        include_str!("../../../fixtures2/behavior/false_embedding.fz"),
    );

    let f = world.reference_function(ModuleId::GLOBAL, "f", 1);
    let leaf = world.reference_function(ModuleId::GLOBAL, "leaf", 1);
    let activation = sole_activation(&seen.borrow(), f, "f/1");
    let expression = expression_for(&mut world, &tel, &activation);

    let ReturnExpression::Union(members) = &expression else {
        panic!("f/1's three clauses should join into a Union: {expression:?}");
    };
    assert_eq!(members.len(), 3, "f/1 has exactly three clauses: {members:?}");
    assert!(
        matches!(members[0], ReturnExpression::Published(_)),
        "f(0) -> 0 publishes a plain type with no call involved: {:?}",
        members[0],
    );
    let ReturnExpression::Tuple(fields) = &members[1] else {
        panic!("f(1) -> {{:ok, leaf(1)}} builds a tuple: {:?}", members[1]);
    };
    assert_eq!(fields.len(), 2, "the tuple has two fields: {fields:?}");
    assert!(
        matches!(fields[0], ReturnExpression::Published(_)),
        ":ok is a literal atom, no call involved: {:?}",
        fields[0],
    );
    let ReturnExpression::Local(leaf_key) = &fields[1] else {
        panic!("leaf(1) must address leaf's own activation, not f's: {:?}", fields[1]);
    };
    assert_eq!(
        leaf_key.function, leaf,
        "the embedded call addresses leaf, the callee it actually names"
    );
    let ReturnExpression::Local(f_key) = &members[2] else {
        panic!("f(n) -> f(n - 1) tail-calls f directly: {:?}", members[2]);
    };
    assert_eq!(f_key.function, f, "the self call addresses f's own activation");
}

#[test]
fn even_1_addresses_its_mutual_partner_by_key() {
    let tel = ConfiguredTelemetry::new();
    let (mut world, seen) = drive_fixture(
        &tel,
        "mutual_tuple_states.fz",
        include_str!("../../../fixtures2/behavior/mutual_tuple_states.fz"),
    );

    let even = world.reference_function(ModuleId::GLOBAL, "even", 1);
    let odd = world.reference_function(ModuleId::GLOBAL, "odd", 1);
    let activation = sole_activation(&seen.borrow(), even, "even/1");
    let expression = expression_for(&mut world, &tel, &activation);

    let ReturnExpression::Union(members) = &expression else {
        panic!("even/1's two clauses should join into a Union: {expression:?}");
    };
    assert_eq!(members.len(), 2, "even/1 has exactly two clauses: {members:?}");
    let ReturnExpression::Tuple(even_fields) = &members[0] else {
        panic!("even([]) -> {{:even, 0}} builds a tuple: {:?}", members[0]);
    };
    assert_eq!(even_fields.len(), 2, "the tuple has two fields: {even_fields:?}");
    assert!(
        matches!(even_fields[0], ReturnExpression::Published(_)),
        ":even is a literal atom, no call involved: {:?}",
        even_fields[0],
    );
    assert!(
        matches!(even_fields[1], ReturnExpression::Published(_)),
        "0 is a literal int, no call involved: {:?}",
        even_fields[1],
    );
    let ReturnExpression::Tuple(e_fields) = &members[1] else {
        panic!("even([_ | t]) -> {{:e, odd(t)}} builds a tuple: {:?}", members[1]);
    };
    assert_eq!(e_fields.len(), 2, "the tuple has two fields: {e_fields:?}");
    assert!(
        matches!(e_fields[0], ReturnExpression::Published(_)),
        ":e is a literal atom, no call involved: {:?}",
        e_fields[0],
    );
    let ReturnExpression::Local(odd_key) = &e_fields[1] else {
        panic!("odd(t) must address odd's own activation: {:?}", e_fields[1]);
    };
    assert_eq!(
        odd_key.function, odd,
        "the mutual call addresses odd, its actual callee"
    );
}

#[test]
fn cont_2_tail_calls_its_sibling_directly() {
    let tel = ConfiguredTelemetry::new();
    let (mut world, seen) = drive_fixture(
        &tel,
        "alias_cycle_with_entry.fz",
        include_str!("../../../fixtures2/behavior/alias_cycle_with_entry.fz"),
    );

    let cont = world.reference_function(ModuleId::GLOBAL, "cont", 2);
    let step = world.reference_function(ModuleId::GLOBAL, "step", 2);
    let keys = activations(&seen.borrow(), cont);
    assert_eq!(
        keys.len(),
        2,
        "cont/2 is entered once from enter/1, where the accumulator's type still admits both \
         clauses, and once more, in steady state, from step/2, where dispatch has already \
         proven the empty-list clause unreachable -- alias_cycle_with_entry carries no \
         RETURN_LADDERS row, so neither call ever collapses into the other's key: {keys:?}",
    );

    let expressions: Vec<ReturnExpression> = keys
        .iter()
        .map(|activation| expression_for(&mut world, &tel, activation))
        .collect();

    let unions: Vec<&ReturnExpression> = expressions
        .iter()
        .filter(|expression| matches!(expression, ReturnExpression::Union(_)))
        .collect();
    assert_eq!(
        unions.len(),
        1,
        "exactly one of the two keys still has both clauses reachable: {expressions:?}",
    );
    let ReturnExpression::Union(members) = unions[0] else {
        unreachable!("filtered to Union above");
    };
    assert_eq!(members.len(), 2, "cont/2 has exactly two clauses: {members:?}");
    let ReturnExpression::Tuple(fields) = &members[0] else {
        panic!("cont([], acc) -> {{:done, acc}} builds a tuple: {:?}", members[0]);
    };
    assert_eq!(fields.len(), 2, "the tuple has two fields: {fields:?}");
    assert!(
        matches!(fields[0], ReturnExpression::Published(_)),
        ":done is a literal atom, no call involved: {:?}",
        fields[0],
    );
    assert!(
        matches!(fields[1], ReturnExpression::Published(_)),
        "acc is a delivered parameter here, not a call result: {:?}",
        fields[1],
    );
    let ReturnExpression::Local(step_key) = &members[1] else {
        panic!(
            "cont([h | t], acc) -> step(t, {{:cont, [h | acc]}}) tail-calls step directly, \
             so the whole clause addresses step, not a tuple around it: {:?}",
            members[1]
        );
    };
    assert_eq!(
        step_key.function, step,
        "the tail call addresses step, its actual callee"
    );

    // The steady-state key's own row has already proven the empty-list
    // clause unreachable, so its join never wraps a single contribution in
    // a `Union` of one -- it collapses straight to that one clause's own
    // expression, the same `Local` the general key carries as its second
    // member.
    let bare: Vec<&ReturnExpression> = expressions
        .iter()
        .filter(|expression| !matches!(expression, ReturnExpression::Union(_)))
        .collect();
    assert_eq!(bare.len(), 1, "the other key's one reachable clause: {expressions:?}");
    let ReturnExpression::Local(step_key) = bare[0] else {
        panic!(
            "with only cont([h | t], acc) reachable, the whole activation addresses step \
             directly: {:?}",
            bare[0]
        );
    };
    assert_eq!(
        step_key.function, step,
        "the tail call addresses step, its actual callee"
    );
}

#[test]
fn a_map_update_on_a_still_open_recursive_call_settles_with_a_published_companion() {
    let tel = ConfiguredTelemetry::new();
    let (mut world, seen) = drive_fixture(
        &tel,
        "map_update_on_a_local.fz",
        r#"
def f(0), do: %{count: 0}
def f(n), do: %{f(n - 1) | count: n}
def main() do
  dbg(f(2))
end
"#,
    );

    let f = world.reference_function(ModuleId::GLOBAL, "f", 1);
    let activation = sole_activation(&seen.borrow(), f, "f/1");
    let expression = expression_for(&mut world, &tel, &activation);

    // A map update has no structural rule of its own -- its result is a
    // refinement of the base's real `Ty`, not a fold over the base's
    // companion -- so f(n)'s update clause publishes outright even though
    // its base is f's own still-open recursive call, the same way it always
    // has, rather than needing that `Local` closed first.
    let ReturnExpression::Union(members) = &expression else {
        panic!("f/1's two clauses should join into a Union: {expression:?}");
    };
    assert_eq!(members.len(), 2, "f/1 has exactly two clauses: {members:?}");
    assert!(
        matches!(members[1], ReturnExpression::Published(_)),
        "the map update clause publishes outright, independent of its still-open base: {:?}",
        members[1],
    );
}
