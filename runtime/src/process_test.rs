use super::{Process, YIELD_REASON_REDUCTIONS};
use std::cell::RefCell;
use std::rc::Rc;

#[test]
fn aligned_closure_storage_is_taggable() {
    for _ in 0..128 {
        let mut buf = super::AlignedClosureStorage::zeroed();
        assert_eq!(buf.as_ptr() as u64 & crate::any_value::TAG_MASK, 0);
    }
}

#[test]
fn reduction_budget_resets_and_spends() {
    let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
    let mut process = Process::new(schemas);
    process.reductions_per_quantum = 3;
    process.reset_reduction_budget();

    assert_eq!(process.reductions_remaining, 3);
    process.finish_yield_report(-1, YIELD_REASON_REDUCTIONS);
    assert_eq!(process.reductions_remaining, -1);
    assert_eq!(process.reductions_executed, 4);
    assert_eq!(process.reduction_yields, 1);
    assert_eq!(process.yield_reasons & YIELD_REASON_REDUCTIONS, YIELD_REASON_REDUCTIONS);
}

#[test]
fn finish_yield_report_charges_only_reduction_exhaustion() {
    let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
    let mut process = Process::new(schemas);
    process.reductions_per_quantum = 10;
    process.reset_reduction_budget();

    process.finish_yield_report(3, YIELD_REASON_REDUCTIONS);

    assert_eq!(process.reductions_remaining, 3);
    assert_eq!(process.reductions_executed, 7);
    assert_eq!(process.reduction_yields, 1);
    assert_eq!(process.yield_reasons, YIELD_REASON_REDUCTIONS);
}

#[test]
fn reset_reduction_budget_clears_yield_reasons() {
    let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
    let mut process = Process::new(schemas);
    process.reductions_per_quantum = 5;
    process.reductions_remaining = 0;
    process.yield_reasons = YIELD_REASON_REDUCTIONS;

    process.reset_reduction_budget();

    assert_eq!(process.reductions_remaining, 5);
    assert_eq!(process.yield_reasons, 0);
}
