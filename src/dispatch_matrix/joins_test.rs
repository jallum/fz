use super::*;
use crate::compiler2::Ty;
use crate::dispatch_matrix::{
    ComparisonValue, DispatchEdge, DispatchGraphBuilder, DispatchNode, EdgeEvidence, GroundValue, OutcomeId,
    PlanInputs, Region, RegionPredicate, Subject, SubjectId, SubjectSource,
};
use std::collections::BTreeMap;

/// What an arrival knows: a value per name.
#[derive(Clone, Debug, PartialEq)]
struct Known(BTreeMap<&'static str, u32>);

impl ArrivalState for Known {
    fn meet(arrivals: Vec<Self>) -> Self {
        let mut arrivals = arrivals.into_iter();
        let mut met = arrivals.next().expect("a reached join has an arrival");
        for other in arrivals {
            met.0.retain(|name, value| other.0.get(name) == Some(value));
        }
        met
    }
}

fn known(entries: &[(&'static str, u32)]) -> Known {
    Known(entries.iter().copied().collect())
}

/// `fail` (0) and `out` (1) are each reached by two edges: `fail` from `low`
/// and `mid`, `out` from `low` and `root`. `low` (2), `mid` (3) and `root` (4)
/// are reached once.
fn graph_with_two_joins() -> (crate::dispatch_matrix::DispatchGraph<Ty>, [GraphNodeId; 5]) {
    let subjects = vec![Subject {
        id: SubjectId(0),
        source: SubjectSource::Input { ordinal: 0 },
    }];
    let inputs = PlanInputs {
        count: 1,
        pinned: &[],
        guard_leaves: &[],
        literal_blind: &|_| false,
    };
    let mut builder = DispatchGraphBuilder::<Ty>::typed(subjects, inputs);
    let fail = builder.add_node(DispatchNode::Fail);
    let out = builder.add_node(DispatchNode::Outcome {
        outcome: OutcomeId(0),
        evidence: EdgeEvidence::empty(),
    });
    let mut test = |on_match, on_miss| {
        builder.add_node(DispatchNode::Test {
            predicate: RegionPredicate::new(SubjectId(0), Region::Equal(ComparisonValue::Const(GroundValue::Nil))),
            on_match: DispatchEdge::new(on_match),
            on_miss: DispatchEdge::new(on_miss),
        })
    };
    let low = test(out, fail);
    let mid = test(low, fail);
    let root = test(mid, out);
    let graph = builder.build(root).expect("ids ascend toward the root");
    (graph, [fail, out, low, mid, root])
}

#[test]
fn an_edge_to_a_node_with_one_edge_in_is_emitted_where_it_stands() {
    let (graph, [_, _, low, ..]) = graph_with_two_joins();
    let mut joins = DispatchJoins::<u32, Known>::default();

    assert_eq!(
        joins.arrive(&graph, low, &known(&[]), || unreachable!("a non-join gets no block")),
        None
    );
    assert!(joins.next().is_none());
}

#[test]
fn every_arrival_at_a_join_jumps_to_the_one_block_made_for_it() {
    let (graph, [fail, ..]) = graph_with_two_joins();
    let mut joins = DispatchJoins::<u32, Known>::default();
    let mut made = 0;

    let first = joins.arrive(&graph, fail, &known(&[]), || {
        made += 1;
        7
    });
    let second = joins.arrive(&graph, fail, &known(&[]), || {
        made += 1;
        8
    });

    assert_eq!((first, second, made), (Some(7), Some(7), 1));
}

#[test]
fn a_join_keeps_only_what_every_arrival_holds() {
    let (graph, [fail, ..]) = graph_with_two_joins();
    let mut joins = DispatchJoins::<u32, Known>::default();
    joins.arrive(&graph, fail, &known(&[("a", 1), ("b", 2), ("c", 3)]), || 0);
    joins.arrive(&graph, fail, &known(&[("a", 1), ("b", 9)]), || 0);

    let ready = joins.next().expect("fail was reached");

    assert_eq!(
        ready.state,
        known(&[("a", 1)]),
        "b differs and c is missing from one arrival"
    );
}

#[test]
fn a_join_one_arrival_reached_keeps_that_arrival_whole() {
    let (graph, [fail, ..]) = graph_with_two_joins();
    let mut joins = DispatchJoins::<u32, Known>::default();
    joins.arrive(&graph, fail, &known(&[("a", 1), ("b", 2)]), || 0);

    assert_eq!(joins.next().expect("reached").state, known(&[("a", 1), ("b", 2)]));
}

#[test]
fn joins_are_ready_from_the_largest_id_down() {
    let (graph, [fail, out, ..]) = graph_with_two_joins();
    let mut joins = DispatchJoins::<u32, Known>::default();
    joins.arrive(&graph, fail, &known(&[]), || 0);
    joins.arrive(&graph, out, &known(&[]), || 1);

    let order: Vec<_> = std::iter::from_fn(|| joins.next().map(|ready| ready.node)).collect();

    assert_eq!(
        order,
        vec![out, fail],
        "a join is emitted after every node that can lead to it"
    );
}
