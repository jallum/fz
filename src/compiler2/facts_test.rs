use std::collections::HashSet;

use super::FactTable;

type TestFacts = FactTable<u32, &'static str>;

// The table stores the revision the authority job published, verbatim — it
// does not mint its own counter. Propagation (a FactChange) happens exactly
// when the stored revision moves.
#[test]
fn compiler2_fact_table_propagates_only_when_the_published_revision_moves() {
    let mut facts = TestFacts::new();
    let fact = "module-defined";

    let first = facts.replace_outputs(&1_u32, &HashSet::new(), vec![(fact, 7)]);
    assert_eq!(
        first.changed[0].new_revision,
        Some(7),
        "the table should store the published revision verbatim"
    );
    assert_eq!(facts.revision(&fact), Some(7));

    let stable = facts.replace_outputs(&1_u32, &HashSet::from([fact]), vec![(fact, 7)]);
    assert!(
        stable.changed.is_empty(),
        "republishing the same revision should not propagate"
    );

    let moved = facts.replace_outputs(&1_u32, &HashSet::from([fact]), vec![(fact, 8)]);
    assert_eq!(moved.changed[0].old_revision, Some(7));
    assert_eq!(
        moved.changed[0].new_revision,
        Some(8),
        "a moved revision should propagate with both endpoints visible"
    );
}

// A job that stops publishing a key drops its entry: when the last publisher
// retracts, the fact reads as absent, and a later re-publication propagates
// again even at the old revision.
#[test]
fn compiler2_fact_table_retracts_facts_when_their_last_publisher_stops() {
    let mut facts = TestFacts::new();
    let fact = "function-defined";

    facts.replace_outputs(&1_u32, &HashSet::new(), vec![(fact, 3)]);
    let retracted = facts.replace_outputs(&1_u32, &HashSet::from([fact]), vec![]);
    assert_eq!(retracted.changed[0].old_revision, Some(3));
    assert_eq!(
        retracted.changed[0].new_revision, None,
        "a fact whose last publisher stops publishing it should be retracted"
    );
    assert_eq!(facts.revision(&fact), None);

    let reasserted = facts.replace_outputs(&2_u32, &HashSet::new(), vec![(fact, 3)]);
    assert_eq!(
        reasserted.changed[0].new_revision,
        Some(3),
        "re-publication after retraction should propagate even at the old revision"
    );
}

// Demand facts (Activation, Executable) are published by every demander. The
// fact stays present while any demander remains, and one demander leaving does
// not disturb subscribers as long as the settled revision holds still.
#[test]
fn compiler2_fact_table_keeps_demand_facts_alive_until_the_last_demander_leaves() {
    let mut facts = TestFacts::new();
    let fact = "activation";

    facts.replace_outputs(&1_u32, &HashSet::new(), vec![(fact, 1)]);
    let second = facts.replace_outputs(&2_u32, &HashSet::new(), vec![(fact, 1)]);
    assert!(
        second.changed.is_empty(),
        "a second demander at the same revision should not propagate"
    );

    let first_leaves = facts.replace_outputs(&1_u32, &HashSet::from([fact]), vec![]);
    assert!(
        first_leaves.changed.is_empty(),
        "one demander leaving should not disturb the fact while another remains"
    );
    assert_eq!(facts.revision(&fact), Some(1));

    let last_leaves = facts.replace_outputs(&2_u32, &HashSet::from([fact]), vec![]);
    assert_eq!(
        last_leaves.changed[0].new_revision, None,
        "the last demander leaving should retract the fact"
    );
    assert_eq!(facts.revision(&fact), None);
}

#[test]
#[should_panic(expected = "duplicate fact output")]
fn compiler2_fact_table_rejects_duplicate_outputs_in_one_publication() {
    let mut facts = TestFacts::new();
    let fact = "activation";
    facts.replace_outputs(&1_u32, &HashSet::new(), vec![(fact, 1), (fact, 2)]);
}
