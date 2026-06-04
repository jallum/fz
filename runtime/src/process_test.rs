use super::{Process, YIELD_REASON_ALLOCATION_PRESSURE, YIELD_REASON_REDUCTIONS};
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
    assert_eq!(process.allocation_pressure_yields, 0);
    assert_eq!(process.yield_reasons & YIELD_REASON_REDUCTIONS, YIELD_REASON_REDUCTIONS);
}

#[test]
fn allocation_pressure_banks_only_genuine_reductions() {
    let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
    let mut process = Process::new(schemas);
    process.reductions_per_quantum = 4000;
    process.reset_reduction_budget();

    // Real work: back edges spent the budget down to 3950 (50 burned).
    process.reductions_remaining = 3950;

    // Allocation crosses the watermark mid-quantum and force-expires the
    // budget. The 50 genuinely-burned reductions are banked now, while
    // `reductions_remaining` is still truthful; the budget is then zeroed
    // to trip the next back edge.
    process.expire_budget(YIELD_REASON_ALLOCATION_PRESSURE);
    assert_eq!(process.reductions_remaining, 0);
    assert_eq!(process.reductions_executed, 50);

    // A second crossing in the same quantum must not double-count.
    process.expire_budget(YIELD_REASON_ALLOCATION_PRESSURE);
    assert_eq!(process.reductions_executed, 50);

    // The back edge that observes the zeroed budget yields, reporting a
    // slightly-negative remaining (its own cost). finish_yield_report
    // banks only that post-expiry work — NOT a re-credited full quantum.
    process.finish_yield_report(-1, YIELD_REASON_REDUCTIONS);
    assert_eq!(process.reductions_executed, 51);
    assert_eq!(process.allocation_pressure_yields, 1);
    assert_eq!(process.reduction_yields, 0);
}

#[test]
fn reset_reduction_budget_clears_yield_reasons() {
    let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
    let mut process = Process::new(schemas);
    process.reductions_per_quantum = 5;
    process.reductions_remaining = 0;
    process.yield_reasons = YIELD_REASON_ALLOCATION_PRESSURE | YIELD_REASON_REDUCTIONS;

    process.reset_reduction_budget();

    assert_eq!(process.reductions_remaining, 5);
    assert_eq!(process.yield_reasons, 0);
}

#[test]
fn allocation_pressure_yields_are_counted_by_cause() {
    let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
    let mut process = Process::new(schemas);

    process.finish_yield_report(9, YIELD_REASON_REDUCTIONS | YIELD_REASON_ALLOCATION_PRESSURE);

    assert_eq!(process.reduction_yields, 0);
    assert_eq!(process.allocation_pressure_yields, 1);
    assert_eq!(
        process.yield_reasons & YIELD_REASON_ALLOCATION_PRESSURE,
        YIELD_REASON_ALLOCATION_PRESSURE
    );
}
