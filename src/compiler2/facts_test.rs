use std::collections::HashSet;

use super::{FactTable, FactValue, Types};

type TestFacts = FactTable<u32, &'static str>;

#[test]
fn compiler2_fact_table_input_join_is_order_independent() {
    let mut forward = TestFacts::new();
    let mut reverse = TestFacts::new();
    let mut forward_types = Types::new();
    let mut reverse_types = Types::new();
    let fact = "activation";

    let forward_int = forward_types.int();
    let forward_empty = forward_types.empty_list();
    let forward_non_empty = forward_types.non_empty_list(forward_int);
    let forward_empty_inputs = FactValue::inputs(&mut forward_types, vec![forward_empty]);
    let forward_non_empty_inputs = FactValue::inputs(&mut forward_types, vec![forward_non_empty]);

    let reverse_int = reverse_types.int();
    let reverse_empty = reverse_types.empty_list();
    let reverse_non_empty = reverse_types.non_empty_list(reverse_int);
    let reverse_empty_inputs = FactValue::inputs(&mut reverse_types, vec![reverse_empty]);
    let reverse_non_empty_inputs = FactValue::inputs(&mut reverse_types, vec![reverse_non_empty]);

    let _ = forward.replace_contributions(
        &mut forward_types,
        &1_u32,
        &HashSet::new(),
        vec![(fact, forward_empty_inputs)],
    );
    let _ = forward.replace_contributions(
        &mut forward_types,
        &2_u32,
        &HashSet::new(),
        vec![(fact, forward_non_empty_inputs)],
    );

    let _ = reverse.replace_contributions(
        &mut reverse_types,
        &2_u32,
        &HashSet::new(),
        vec![(fact, reverse_non_empty_inputs)],
    );
    let _ = reverse.replace_contributions(
        &mut reverse_types,
        &1_u32,
        &HashSet::new(),
        vec![(fact, reverse_empty_inputs)],
    );

    let forward_list = forward_types.list(forward_int);
    let forward_expected = FactValue::inputs(&mut forward_types, vec![forward_list]);
    let reverse_list = reverse_types.list(reverse_int);
    let reverse_expected = FactValue::inputs(&mut reverse_types, vec![reverse_list]);
    assert_eq!(
        forward.slot(&fact).and_then(|slot| slot.value()),
        Some(&forward_expected),
        "joining empty and non-empty list observations should converge to the same aggregate regardless of arrival order",
    );
    assert_eq!(
        reverse.slot(&fact).and_then(|slot| slot.value()),
        Some(&reverse_expected),
        "reversing the contribution order should not change the joined aggregate value",
    );
    assert_eq!(
        forward.revision(&fact),
        reverse.revision(&fact),
        "equivalent join histories should settle to the same slot revision shape",
    );
}

#[test]
fn compiler2_fact_table_revision_bumps_only_when_joined_value_changes() {
    let mut facts = TestFacts::new();
    let mut types = Types::new();
    let fact = "activation";

    let int = types.int();
    let empty = types.empty_list();
    let non_empty = types.non_empty_list(int);
    let empty_inputs = FactValue::inputs(&mut types, vec![empty]);
    let non_empty_inputs = FactValue::inputs(&mut types, vec![non_empty]);

    let first = facts.replace_contributions(&mut types, &1_u32, &HashSet::new(), vec![(fact, empty_inputs)]);
    assert_eq!(
        first.changed[0].new_revision,
        Some(1),
        "publishing the first aggregate value should mint slot revision 1",
    );

    let second = facts.replace_contributions(
        &mut types,
        &2_u32,
        &HashSet::new(),
        vec![(fact, non_empty_inputs.clone())],
    );
    assert_eq!(
        second.changed[0].old_revision,
        Some(1),
        "widening the aggregate should observe the prior slot revision",
    );
    assert_eq!(
        second.changed[0].new_revision,
        Some(2),
        "a changed joined value should bump the slot revision exactly once",
    );

    let stable = facts.replace_contributions(
        &mut types,
        &2_u32,
        &HashSet::from([fact]),
        vec![(fact, non_empty_inputs)],
    );
    assert!(
        stable.changed.is_empty(),
        "rewriting an equal contribution should leave the joined value and slot revision untouched",
    );
    assert_eq!(
        facts.revision(&fact),
        Some(2),
        "slot revisions should track aggregate changes, not contribution rewrites or payload hash values",
    );
}
