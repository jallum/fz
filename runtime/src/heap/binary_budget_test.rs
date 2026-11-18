use super::*;

const MIB: usize = 1024 * 1024;

#[test]
fn a_heap_that_made_no_binaries_waits_for_the_minimum_budget() {
    let mut budget = BinaryBudget::new();
    assert_eq!(budget.budget(), MIN_BINARY_BUDGET);
    assert_eq!(MIN_BINARY_BUDGET, 256 * 1024);

    budget.record_made(MIN_BINARY_BUDGET - 1);
    assert!(!budget.is_due(), "one byte short of the budget");
    budget.record_made(1);
    assert!(budget.is_due(), "the budget is reached, not exceeded");
}

#[test]
fn a_collection_restarts_the_young_count_and_sizes_the_budget_by_what_survived() {
    let mut budget = BinaryBudget::new();
    budget.record_made(3 * MIB);

    budget.after_collection(Generation::Major, 2 * MIB);

    assert_eq!(budget.young_binary_bytes(), 0);
    assert_eq!(budget.held_binary_bytes(), 2 * MIB);
    assert_eq!(
        budget.budget(),
        2 * MIB,
        "a heap holding N binary bytes collects after N more"
    );
    assert!(!budget.is_due());
}

#[test]
fn the_budget_never_falls_below_the_minimum_however_little_survives() {
    let mut budget = BinaryBudget::new();
    budget.record_made(MIB);

    budget.after_collection(Generation::Major, 1024);

    assert_eq!(budget.held_binary_bytes(), 1024);
    assert_eq!(budget.budget(), MIN_BINARY_BUDGET);
}

#[test]
fn a_minor_collection_adds_its_survivors_to_the_held_bytes() {
    let mut budget = BinaryBudget::new();
    budget.after_collection(Generation::Minor, MIB);
    budget.after_collection(Generation::Minor, MIB);

    assert_eq!(budget.held_binary_bytes(), 2 * MIB);
    assert_eq!(budget.budget(), 2 * MIB);
}

#[test]
fn a_major_collection_replaces_the_held_bytes_with_its_survivors() {
    let mut budget = BinaryBudget::new();
    budget.after_collection(Generation::Minor, 4 * MIB);
    budget.after_collection(Generation::Minor, MIB);

    budget.after_collection(Generation::Major, MIB / 2);

    assert_eq!(
        budget.held_binary_bytes(),
        MIB / 2,
        "the major saw every BinRef, so what died since is no longer held"
    );
}
