use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

use super::super::drive_harness::Drive;
use super::super::pull::{ProductKey, ProductRequestId, ProductScope, PullOutcome};
use super::super::{CodeSubmission, Compiler2, ExecutableNeed, FunctionId, RootSubmission, World};
use super::ReachKey;
use crate::telemetry::ConfiguredTelemetry;

/// The nodes reachable from `from` by at least one edge, found by walking
/// `successors` directly. This is the question a reach product answers
/// without walking, so it is the oracle the products are checked against.
fn walked_reach(world: &World, from: &ReachKey) -> HashSet<ReachKey> {
    let mut reached = HashSet::new();
    let mut frontier = from.successors(world);
    while let Some(node) = frontier.pop() {
        if reached.insert(node.clone()) {
            frontier.extend(node.successors(world));
        }
    }
    reached
}

fn static_reach(compiler: &Compiler2<ConfiguredTelemetry>, function: FunctionId) -> Rc<super::ReachSet> {
    compiler
        .retained_reach_products(ProductScope::Program)
        .into_iter()
        .find_map(|(key, set)| (key == ReachKey::Static(function)).then_some(set))
        .unwrap_or_else(|| panic!("{function:?} should have a settled static reach"))
}

fn is_recursive(compiler: &Compiler2<ConfiguredTelemetry>, function: FunctionId) -> bool {
    compiler
        .world()
        .body_keying(function)
        .unwrap_or_else(|| panic!("body keying for {function:?}"))
        .recursive
}

/// A function's static callees can grow after its reach settled: redefining
/// `b` so it calls `a` back closes a cycle through functions whose own
/// bodies did not change. Their reach must reopen and `Recursive` must turn
/// true, rather than keep the answer that was true before the new edge.
#[test]
fn a_callee_that_grows_an_edge_reopens_the_reach_above_it_and_closes_a_cycle() {
    let mut settled = Drive::fixture(611).settle();
    let a = settled.function("a", 2);
    let b = settled.function("b", 2);
    assert!(
        !is_recursive(settled.compiler(), a),
        "a chain that reaches no cycle is not recursive"
    );
    let before = static_reach(settled.compiler(), a);
    assert!(
        before.contains(&ReachKey::Static(b)) && !before.contains(&ReachKey::Static(a)),
        "a reaches b and nothing that leads back to a: {before:?}"
    );

    settled.compiler_mut().submit_code(CodeSubmission {
        name: Some("fixtures/00612_static_reach_edge_added_later_after.fz".to_string()),
        text: include_str!("../../fixtures/00612_static_reach_edge_added_later_after.fz").to_string(),
    });
    let outcome = settled.compiler_mut().drive();
    assert!(matches!(outcome, super::super::DriveOutcome::Resolved), "{outcome:?}");

    assert!(
        is_recursive(settled.compiler(), a) && is_recursive(settled.compiler(), b),
        "b now calls a, so each reaches itself through the other"
    );
    let after = static_reach(settled.compiler(), a);
    assert!(
        after.contains(&ReachKey::Static(a)) && after.contains(&ReachKey::Static(b)),
        "the reach above the changed callee was recomputed: {after:?}"
    );
    assert_eq!(
        after,
        static_reach(settled.compiler(), b),
        "mutually reachable functions share one reach"
    );
}

/// A closure created outside a recursion and threaded back through it leaves
/// the static call graph acyclic, so only the executable edges see the cycle.
/// Following every call target finds it; following direct calls alone does
/// not, since the way back runs through a closure call. Each settled reach is
/// also exactly what walking its successors finds.
#[test]
fn a_closure_threaded_through_a_recursion_is_a_cycle_only_when_closure_calls_are_followed() {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/closure_threaded_recursion.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/closure_threaded_recursion.fz").to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_backend_work_starts(root)
        .expect("the fixture should settle its backend product");

    let reaches = compiler.retained_reach_products(ProductScope::Root(root));
    for (key, set) in &reaches {
        assert_eq!(
            **set,
            walked_reach(compiler.world(), key),
            "{key:?} must hold exactly the nodes its successors lead to"
        );
    }
    let on_a_cycle = |arm: fn(&ReachKey) -> bool| {
        reaches
            .iter()
            .filter(|(key, _)| arm(key))
            .filter(|(key, set)| set.contains(key))
            .count()
    };
    assert_eq!(
        on_a_cycle(|key| matches!(key, ReachKey::Direct(_))),
        0,
        "no chain of direct calls leads back to where it started"
    );
    assert!(
        on_a_cycle(|key| matches!(key, ReachKey::All(_))) > 0,
        "the closure call carries the recursion back to its start"
    );
}

/// Each function's static reach settles once and is read by one evaluation
/// per edge it waits on, so the work a compile spends on static reach grows
/// with the call graph's edges and not with edges times the functions that
/// can reach them.
#[test]
fn static_reach_work_on_enum_take_drop_split_is_proportional_to_edges() {
    let drive = Drive::fixture(420);
    let evaluations = Rc::new(RefCell::new(Vec::<ReachKey>::new()));
    let observed = Rc::clone(&evaluations);
    drive
        .telemetry()
        .attach_raw_event3::<ProductKey, ProductRequestId, PullOutcome, _>(
            &["fz", "compiler2", "pull", "product", "evaluated"],
            move |_, _, _, key, _, _| {
                if let ProductKey::Reach(reach @ ReachKey::Static(_)) = key {
                    observed.borrow_mut().push(reach.clone());
                }
            },
        );
    let settled = drive.settle();

    let reaches = settled.compiler().retained_reach_products(ProductScope::Program);
    let functions = reaches.len();
    let edges: usize = reaches
        .iter()
        .map(|(key, _)| key.successors(settled.world()).len())
        .sum();
    let evaluations = evaluations.borrow().len();
    assert_eq!((functions, edges, evaluations), (105, 148, 206));
    assert!(
        evaluations <= functions + edges,
        "each function evaluates once to discover its callees and once more for each callee it waits on"
    );
}
