use std::collections::HashSet;

use super::FactTable;

type TestFacts = FactTable<u32, &'static str>;

// The table owns the revision counter. First publication sets it to 1.
// Re-publication with changed=true increments it. Re-publication with
// changed=false leaves it untouched. Propagation (a FactChange) fires
// exactly when the stored revision moves.
#[test]
fn compiler2_fact_table_propagates_only_when_content_changes() {
    let mut facts = TestFacts::new();
    let fact = "module-defined";

    let first = facts.replace_outputs(&1_u32, &HashSet::new(), vec![(fact, true)]);
    assert_eq!(
        first.changed[0].new_revision,
        Some(1),
        "first publication should set revision to 1"
    );
    assert_eq!(facts.revision(&fact), Some(1));

    let stable = facts.replace_outputs(&1_u32, &HashSet::from([fact]), vec![(fact, false)]);
    assert!(
        stable.changed.is_empty(),
        "republishing with changed=false should not propagate"
    );
    assert_eq!(facts.revision(&fact), Some(1));

    let moved = facts.replace_outputs(&1_u32, &HashSet::from([fact]), vec![(fact, true)]);
    assert_eq!(moved.changed[0].old_revision, Some(1));
    assert_eq!(
        moved.changed[0].new_revision,
        Some(2),
        "republishing with changed=true should increment the table counter"
    );
    assert_eq!(facts.revision(&fact), Some(2));
}

// A job that stops publishing a key retracts it when it was the last publisher.
// After retraction, the counter resets: the next publisher starts at 1 again.
#[test]
fn compiler2_fact_table_retracts_facts_when_their_last_publisher_stops() {
    let mut facts = TestFacts::new();
    let fact = "function-defined";

    facts.replace_outputs(&1_u32, &HashSet::new(), vec![(fact, true)]);
    assert_eq!(facts.revision(&fact), Some(1));

    let retracted = facts.replace_outputs(&1_u32, &HashSet::from([fact]), vec![]);
    assert_eq!(retracted.changed[0].old_revision, Some(1));
    assert_eq!(
        retracted.changed[0].new_revision, None,
        "a fact whose last publisher stops publishing it should be retracted"
    );
    assert_eq!(facts.revision(&fact), None);

    let reasserted = facts.replace_outputs(&2_u32, &HashSet::new(), vec![(fact, false)]);
    assert_eq!(
        reasserted.changed[0].new_revision,
        Some(1),
        "re-publication after retraction starts a fresh counter at 1"
    );
}

// Demand facts (Activation, Executable) carry changed=false because their
// content is fully determined by the key itself. The fact stays present while
// any publisher remains. One publisher leaving does not disturb subscribers as
// long as another still holds the claim.
#[test]
fn compiler2_fact_table_keeps_demand_facts_alive_until_the_last_demander_leaves() {
    let mut facts = TestFacts::new();
    let fact = "activation";

    let first = facts.replace_outputs(&1_u32, &HashSet::new(), vec![(fact, false)]);
    assert_eq!(
        first.changed[0].new_revision,
        Some(1),
        "first demander's appearance should propagate at revision 1"
    );

    let second = facts.replace_outputs(&2_u32, &HashSet::new(), vec![(fact, false)]);
    assert!(
        second.changed.is_empty(),
        "a second demander with changed=false should not propagate"
    );
    assert_eq!(facts.revision(&fact), Some(1));

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
    facts.replace_outputs(&1_u32, &HashSet::new(), vec![(fact, false), (fact, true)]);
}
