use std::collections::BTreeMap;

use super::*;
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
