use crate::fast_hash::HashSet;
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use super::super::drive::{FactKey, Job};
use super::super::drive_harness::Drive;
use super::super::world::JobCompletion;
use super::super::{CodeSubmission, Compiler2, ExecutableKey, ExecutableNeed, FunctionId, RootSubmission, World};
use super::{CallChain, ReachSet, executable_successors};
use crate::telemetry::ConfiguredTelemetry;

/// The nodes reachable from `from` by at least one edge, found by walking
/// `executable_successors` directly. This is the question a reach fact
/// answers by walking the edge facts, so the plain walk is the oracle the
/// facts are checked against.
fn walked_reach(world: &World, from: &ExecutableKey, chain: CallChain) -> ReachSet {
    let mut reached = HashSet::default();
    let mut frontier = executable_successors(world, from, chain);
    while let Some(node) = frontier.pop() {
        if reached.insert(node.clone()) {
            frontier.extend(executable_successors(world, &node, chain));
        }
    }
    reached
}

fn static_reach(compiler: &Compiler2<ConfiguredTelemetry>, function: FunctionId) -> Rc<BTreeSet<FunctionId>> {
    Rc::clone(
        compiler
            .world()
            .static_reach(function)
            .unwrap_or_else(|| panic!("{function:?} should have a settled static reach")),
    )
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
        before.contains(&b) && !before.contains(&a),
        "a reaches b and nothing that leads back to a: {before:?}"
    );

    settled.compiler_mut().submit_code(CodeSubmission {
        name: Some("fixtures/00612_static_reach_edge_added_later_after.fz".to_string()),
        text: include_str!("../../fixtures/00612_static_reach_edge_added_later_after.fz").to_string(),
    });
    let outcome = settled.compiler_mut().drive();
    assert!(matches!(outcome, fz_engine::DriveOutcome::Resolved), "{outcome:?}");

    assert!(
        is_recursive(settled.compiler(), a) && is_recursive(settled.compiler(), b),
        "b now calls a, so each reaches itself through the other"
    );
    let after = static_reach(settled.compiler(), a);
    assert!(
        after.contains(&a) && after.contains(&b),
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
        name: Some("fixtures/01434_closure_threaded_recursion.fz".to_string()),
        text: include_str!("../../fixtures/01434_closure_threaded_recursion.fz").to_string(),
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

    let reaches = compiler
        .world()
        .executable_reach_entries()
        .into_iter()
        .filter(|((executable, _), _)| executable.activation.root == root)
        .collect::<Vec<_>>();
    for ((executable, chain), set) in &reaches {
        assert_eq!(
            **set,
            walked_reach(compiler.world(), executable, *chain),
            "{chain:?} reach of {executable:?} must hold exactly the nodes its successors lead to"
        );
    }
    let on_a_cycle = |wanted: CallChain| {
        reaches
            .iter()
            .filter(|((_, chain), _)| *chain == wanted)
            .filter(|((executable, _), set)| set.contains(executable))
            .count()
    };
    assert_eq!(
        on_a_cycle(CallChain::Direct),
        0,
        "no chain of direct calls leads back to where it started"
    );
    assert!(
        on_a_cycle(CallChain::All) > 0,
        "the closure call carries the recursion back to its start"
    );
}

/// A reach fact is one job that walks the edge facts of everything it
/// reaches and reads each of them, so a change to any edge in the cone
/// reopens it. No reach fact reads another: the cone is walked, never
/// assembled from other cones.
#[test]
fn a_reach_job_reads_the_edge_of_every_node_it_reaches_and_no_other_reach() {
    let settled = Drive::fixture(420).settle();
    let world = settled.world();
    let entries = world.static_reach_entries();
    assert!(!entries.is_empty());
    for (function, reach) in &entries {
        let reads = world
            .job_reads(&Job::DeriveStaticReach(*function))
            .into_iter()
            .map(|usage| usage.fact().clone())
            .collect::<HashSet<_>>();
        for node in reach.iter().chain([function]) {
            assert!(
                reads.contains(&FactKey::StaticCallees(*node)),
                "the reach of {function:?} must read the edges of {node:?}"
            );
        }
        assert!(
            reads
                .iter()
                .all(|fact| !matches!(fact, FactKey::StaticReach(_) | FactKey::ExecutableReach(..))),
            "the reach of {function:?} reads another reach: {reads:?}"
        );
    }
}

/// The executable arms read the same way: the settled `ExecutableFacts` of
/// every executable the chain reaches, and no other reach.
#[test]
fn an_executable_reach_job_reads_the_facts_of_every_executable_it_reaches_and_no_other_reach() {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/01434_closure_threaded_recursion.fz".to_string()),
        text: include_str!("../../fixtures/01434_closure_threaded_recursion.fz").to_string(),
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
    let world = compiler.world();
    let entries = world.executable_reach_entries();
    assert!(!entries.is_empty());
    for ((executable, chain), reach) in &entries {
        let reads = world
            .job_reads(&Job::DeriveExecutableReach(executable.clone(), *chain))
            .into_iter()
            .map(|usage| usage.fact().clone())
            .collect::<HashSet<_>>();
        for node in reach.iter().chain([executable]) {
            assert!(
                reads.contains(&FactKey::ExecutableFacts(node.clone())),
                "the {chain:?} reach of {executable:?} must read the facts of {node:?}"
            );
        }
        assert!(
            reads
                .iter()
                .all(|fact| !matches!(fact, FactKey::StaticReach(_) | FactKey::ExecutableReach(..))),
            "the {chain:?} reach of {executable:?} reads another reach"
        );
    }
}

/// A static reach exists for each function whose recursion is asked, and no
/// reach is assembled for the functions only reached through those. Each
/// answer came with the recursion verdict it served.
#[test]
fn static_reach_on_enum_take_drop_split_covers_the_call_graph() {
    let settled = Drive::fixture(420).settle();
    let entries = settled.world().static_reach_entries();
    for (function, _) in &entries {
        assert!(
            settled.world().body_keying(*function).is_some(),
            "{function:?} has a static reach no recursion verdict asked for"
        );
    }
    let functions = entries.len();
    let edges: usize = entries
        .iter()
        .map(|(function, _)| settled.world().static_callees(*function).len())
        .sum();
    // (68, 112) -> (56, 99): `Enum.to_list/1` builds a range's list itself, so listing a range no longer reaches the reduce-and-reverse path.
    assert_eq!((functions, edges), (56, 99));
}

/// A reach job runs once to meet its cone and once more per callee whose
/// edges it had to wait for, so its runs are bounded by the size of the cone
/// it ends up holding.
#[test]
fn a_static_reach_job_runs_at_most_once_per_function_of_its_cone() {
    let drive = Drive::fixture(420);
    let runs = Rc::new(RefCell::new(Vec::<FunctionId>::new()));
    let observed = Rc::clone(&runs);
    drive.telemetry().attach_raw_event2::<World, JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, _world, completion| {
            if let Job::DeriveStaticReach(function) = &completion.job {
                observed.borrow_mut().push(*function);
            }
        },
    );
    let settled = drive.settle();
    let runs = runs.borrow();
    for (function, reach) in settled.world().static_reach_entries() {
        let own = runs.iter().filter(|run| **run == function).count();
        assert!(
            own <= 1 + reach.len(),
            "{function:?} ran {own} times for a cone of {}",
            reach.len()
        );
    }
}
