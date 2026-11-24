//! A guard's `in` over a literal list or an integer range is dispatch-pure.
//!
//! Fixture 01779 uses it in function heads, case arms and a receive clause.

use super::drive_harness::Drive;

/// Dispatch evaluates a guard itself, so a membership test only plans when the
/// guard expands to comparisons and bounds. Every guard in the fixture must
/// plan, or the drive stops at the first one that does not.
#[test]
fn a_guard_membership_test_over_a_literal_list_or_range_plans() {
    Drive::fixture(1779).settle();
}
