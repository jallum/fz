//! A type-test guard and a typed parameter are one dispatch row.
//!
//! Fixture 00651 spells the same clause both ways. These tests read the
//! entry plans and the settled return types the fixture produces.

use super::drive_harness::{Drive, EntryDispatchCapture, Settled, latest_entry_dispatch};
use super::{FunctionId, Ty};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardExpr};
use crate::dispatch_matrix::{DispatchNode, Region};
use std::rc::Rc;

const FIXTURE: u32 = 651;

struct Planned {
    settled: Settled,
    plans: EntryDispatchCapture,
}

fn planned() -> Planned {
    let drive = Drive::fixture(FIXTURE);
    let plans = EntryDispatchCapture::new();
    plans.install(drive.telemetry());
    Planned {
        settled: drive.settle(),
        plans,
    }
}

impl Planned {
    fn plan(&self, name: &str, arity: u64) -> Rc<PatternDispatchPlan<Ty>> {
        latest_entry_dispatch(&self.plans, self.settled.function(name, arity))
    }

    fn function(&self, name: &str, arity: u64) -> FunctionId {
        self.settled.function(name, arity)
    }
}

fn type_question_count(plan: &PatternDispatchPlan<Ty>) -> usize {
    plan.graph
        .nodes
        .iter()
        .filter(|node| {
            matches!(
                node,
                DispatchNode::Test {
                    predicate,
                    ..
                } if matches!(predicate.region, Region::Type(_))
            )
        })
        .count()
}

fn assert_same_row(planned: &Planned, typed: (&str, u64), spelled: &[(&str, u64)]) {
    let expected = planned.plan(typed.0, typed.1);
    assert!(expected.guards.is_empty(), "{} asks only type questions", typed.0);
    for (name, arity) in spelled {
        let plan = planned.plan(name, *arity);
        assert_eq!(
            plan.graph, expected.graph,
            "{name}/{arity} asks exactly what {}/{} asks",
            typed.0, typed.1
        );
        assert!(plan.guards.is_empty(), "{name}/{arity} keeps no guard");
    }
}

#[test]
fn every_spelling_of_an_integer_test_builds_the_row_the_typed_parameter_builds() {
    assert_same_row(
        &planned(),
        ("typed", 1),
        &[("guarded", 1), ("user_guarded", 1), ("qualified", 1), ("doubled", 1)],
    );
}

#[test]
fn a_helper_over_two_parameters_and_an_and_chain_build_the_row_two_typed_parameters_build() {
    assert_same_row(&planned(), ("pair_typed", 2), &[("pair_guarded", 2), ("pair_anded", 2)]);
}

#[test]
fn is_boolean_and_is_nil_build_the_row_their_typed_parameter_builds() {
    let planned = planned();
    assert_same_row(&planned, ("boolean_typed", 1), &[("boolean_guarded", 1)]);
    assert_same_row(&planned, ("nil_typed", 1), &[("nil_guarded", 1)]);
}

#[test]
fn a_conjunct_that_is_not_a_type_test_stays_the_guard() {
    let plan = planned().plan("partial", 1);

    assert_eq!(type_question_count(&plan), 1, "is_map(m) is a type question");
    assert_eq!(plan.guards.len(), 1, "map_size(m) == 0 is the whole guard");
    assert!(
        matches!(plan.guards[0], PatternGuardExpr::Binary { .. }),
        "the guard left is the comparison, not the type test: {:?}",
        plan.guards[0]
    );
}

#[test]
fn guards_that_are_not_an_and_chain_of_type_tests_stay_guards() {
    let planned = planned();
    for name in ["either", "negated", "projected"] {
        let plan = planned.plan(name, 1);
        assert_eq!(plan.guards.len(), 1, "{name} keeps its guard whole");
        assert_eq!(type_question_count(&plan), 0, "{name} lifts no type question");
    }
}

#[test]
fn a_type_test_guard_narrows_the_body_as_a_typed_parameter_does() {
    let planned = planned();
    let typed = planned.function("narrow_typed", 1);
    let guarded = planned.function("narrow_guarded", 1);
    let settled = &planned.settled;
    let return_of = |function| {
        settled
            .return_types()
            .last_for_function(settled.root(), function)
            .return_ty
    };
    let (typed_ty, guarded_ty) = (return_of(typed), return_of(guarded));

    assert!(
        settled.compiler().types_equivalent_for_test(typed_ty, guarded_ty),
        "narrow_typed returns {}, narrow_guarded returns {}",
        settled.compiler().display_ty_for_test(typed_ty),
        settled.compiler().display_ty_for_test(guarded_ty),
    );
}
