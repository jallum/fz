use std::collections::BTreeMap;

use super::*;
use crate::compiler2::drive_harness::{Drive, Settled};
use crate::fz_ir::FnId;

fn function(number: u32) -> FunctionId {
    FunctionId::from_fn_id(FnId(number))
}

fn fields(index: u32, demand: DispatchDemand) -> DispatchDemand {
    DispatchDemand::TupleFields(BTreeMap::from([(index, demand)]))
}

fn node(local: DispatchDemand, forwards: Vec<ForwardEdge>) -> DemandNode {
    DemandNode {
        local: vec![local],
        uses: vec![DispatchDemand::Ignore],
        local_result: vec![DispatchDemand::Ignore],
        forwards,
    }
}

fn edge(callee: FunctionId, path: Vec<DemandPathStep>, descent: Vec<DemandPathStep>) -> ForwardEdge {
    ForwardEdge {
        slot: 0,
        path,
        descent,
        callee,
        callee_slot: 0,
    }
}

fn solve(graph: &BTreeMap<FunctionId, DemandNode>, root: FunctionId) -> DispatchDemand {
    solve_forwarded_demand(graph, root, DemandNode::dispatch_and_uses, lifted_demand)
        .into_iter()
        .next()
        .expect("one slot")
}

/// A projection forwarded to a callee that asks about the whole value asks
/// about that position of the caller's input, and a callee that asks nothing
/// asks nothing.
#[test]
fn a_forwarded_projection_lifts_what_the_callee_asks_to_the_position() {
    let projection = edge(function(1), vec![DemandPathStep::TupleField(1)], vec![]);
    assert_eq!(
        lifted_demand(&projection, &DispatchDemand::Whole),
        fields(1, DispatchDemand::Whole)
    );
    assert_eq!(
        lifted_demand(&projection, &DispatchDemand::Ignore),
        DispatchDemand::Ignore
    );
}

/// Only an input passed on as it is carries the callee's return back to the
/// caller's own; a position handed on, or held in a construction, names a
/// value the caller's return is not built from.
#[test]
fn a_return_comes_back_only_through_an_input_passed_on_whole() {
    let whole_slot = edge(function(1), vec![], vec![]);
    let projection = edge(function(1), vec![DemandPathStep::TupleField(0)], vec![]);
    let held = edge(function(1), vec![], vec![DemandPathStep::ListHead]);
    assert_eq!(
        returned_through_edge(&whole_slot, &DispatchDemand::Whole),
        DispatchDemand::Whole
    );
    assert_eq!(
        returned_through_edge(&projection, &DispatchDemand::Whole),
        DispatchDemand::Ignore
    );
    assert_eq!(
        returned_through_edge(&held, &DispatchDemand::Whole),
        DispatchDemand::Ignore
    );
}

/// `go({_, rest})` calling `go(rest)` would deepen its own demand on every
/// pass; the solve widens that edge to the whole slot and stops.
#[test]
fn a_projection_that_feeds_itself_asks_about_the_whole_slot() {
    let go = function(1);
    let graph = BTreeMap::from([(
        go,
        node(
            DispatchDemand::Whole,
            vec![edge(go, vec![DemandPathStep::TupleField(1)], vec![])],
        ),
    )]);
    assert_eq!(solve(&graph, go), DispatchDemand::Whole);
}

/// The same holds when the cycle runs through another function.
#[test]
fn a_projection_around_a_cycle_asks_about_the_whole_slot() {
    let (ping, pong) = (function(1), function(2));
    let graph = BTreeMap::from([
        (ping, node(DispatchDemand::Whole, vec![edge(pong, vec![], vec![])])),
        (
            pong,
            node(
                DispatchDemand::Ignore,
                vec![edge(ping, vec![DemandPathStep::TupleField(0)], vec![])],
            ),
        ),
    ]);
    assert_eq!(solve(&graph, pong), DispatchDemand::Whole);
}

/// A recursion over a list's tail keeps the list's shape: the lift does not
/// deepen, so the demand stays as precise as the callee's.
#[test]
fn a_recursion_down_a_list_keeps_its_demand() {
    let walk = function(1);
    let shape = DispatchDemand::ListShape(Box::new(DispatchDemand::Class));
    let graph = BTreeMap::from([(
        walk,
        node(shape.clone(), vec![edge(walk, vec![DemandPathStep::ListTail], vec![])]),
    )]);
    assert_eq!(solve(&graph, walk), shape);
}

/// A projection forwarded to a callee that is not part of a cycle is lifted
/// once, at full precision.
#[test]
fn a_projection_forwarded_off_a_cycle_keeps_its_depth() {
    let (caller, callee) = (function(1), function(2));
    let graph = BTreeMap::from([
        (
            caller,
            node(
                DispatchDemand::Ignore,
                vec![edge(callee, vec![DemandPathStep::TupleField(1)], vec![])],
            ),
        ),
        (callee, node(DispatchDemand::Whole, vec![])),
    ]);
    assert_eq!(solve(&graph, caller), fields(1, DispatchDemand::Whole));
}

fn cycle_supplied(settled: &Settled, name: &str, arity: u64) -> u64 {
    let function = settled.function(name, arity);
    settled
        .world()
        .body_keying(function)
        .unwrap_or_else(|| panic!("body keying for {name}/{arity}"))
        .cycle_supplied
}

#[test]
fn a_self_recursion_that_wraps_its_accumulator_is_a_cycle_of_one_that_supplies_it() {
    let settled = Drive::fixture(1344).settle();

    assert_eq!(
        cycle_supplied(&settled, "mix", 2) & 0b10,
        0b10,
        "mix wraps its accumulator in a new tuple on every call, so the recursion supplies slot 1"
    );
}

#[test]
fn two_functions_that_call_each_other_supply_the_accumulator_at_both() {
    let settled = Drive::fixture(1350).settle();

    for (name, arity) in [("cont", 3), ("step", 3)] {
        let supplied = cycle_supplied(&settled, name, arity);
        assert_eq!(
            supplied & 0b10,
            0b10,
            "{name} is handed the accumulator by the cycle: the closure's result comes round, whether or not a direct self call exists"
        );
        assert_eq!(
            supplied & 0b100,
            0,
            "{name}'s reducer is handed on unchanged by every call of the cycle, so the cycle does not supply it"
        );
    }
}

#[test]
fn a_recursion_that_swaps_its_accumulators_supplies_neither() {
    let settled = Drive::fixture(1352).settle();

    assert_eq!(
        cycle_supplied(&settled, "go", 3) & 0b110,
        0,
        "go hands each accumulator the value the other held, which builds nothing"
    );
}

#[test]
fn a_function_outside_any_cycle_supplies_nothing() {
    let settled = Drive::fixture(1348).settle();

    assert_eq!(cycle_supplied(&settled, "push", 2), 0);
}
