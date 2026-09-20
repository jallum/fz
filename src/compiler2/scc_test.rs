//! Tests for the generic Tarjan walker in `scc.rs`.

use std::collections::HashMap;

use super::scc::strongly_connected_components;

fn graph(edges: &[(u32, u32)]) -> HashMap<u32, Vec<u32>> {
    let mut graph: HashMap<u32, Vec<u32>> = HashMap::new();
    for &(from, to) in edges {
        graph.entry(from).or_default().push(to);
        graph.entry(to).or_default();
    }
    graph
}

fn sorted_components(mut components: Vec<Vec<u32>>) -> Vec<Vec<u32>> {
    for component in &mut components {
        component.sort_unstable();
    }
    components.sort_by_key(|component| component[0]);
    components
}

/// A DAG (no cycle at all) decomposes into one singleton component per node:
/// the walker must not invent a component out of ordinary forward edges.
#[test]
fn acyclic_graph_is_all_singletons() {
    let graph = graph(&[(1, 2), (2, 3)]);
    let components = strongly_connected_components([1, 2, 3], |node| graph[node].clone());
    let components = sorted_components(components);
    assert_eq!(components, vec![vec![1], vec![2], vec![3]]);
}

/// A node with an edge to itself is its own strongly connected component:
/// the self edge is what promotes it from an ordinary singleton to a real
/// component, exactly the `value_call_self_cycle` witness's shape.
#[test]
fn self_edge_is_its_own_component() {
    let graph = graph(&[(1, 1)]);
    let components = strongly_connected_components([1], |node| graph[node].clone());
    assert_eq!(components, vec![vec![1]]);
}

/// Two nodes that reach each other form one two-member component, whichever
/// one is offered as the root -- the `Enum.reverse([1])` witness's shape
/// (`List.reduce_cont` <-> `List.reduce_step`), and canonical under member
/// permutation.
#[test]
fn mutual_pair_is_one_component_from_either_root() {
    let graph = graph(&[(1, 2), (2, 1)]);
    for root in [1, 2] {
        let components = strongly_connected_components([root], |node| graph[node].clone());
        let components = sorted_components(components);
        assert_eq!(components, vec![vec![1, 2]], "root {root} disagreed on membership");
    }
}

/// Rooting the walk at a single node visits only what that node can reach --
/// a downstream node past the cycle, with no path back in, never joins the
/// component, and never even appears (the walker only reports what it
/// visited). This is the shape Discovery needs: "retaining exactly the
/// vertices that reach the seed" starts from a forward walk and keeps only
/// the completed component containing the seed.
#[test]
fn rooted_walk_does_not_pull_in_unreachable_downstream_nodes() {
    let graph = graph(&[(1, 2), (2, 1), (2, 3)]);
    let components = strongly_connected_components([1], |node| graph[node].clone());
    let components = sorted_components(components);
    assert_eq!(components, vec![vec![1, 2], vec![3]]);
    let all_members: Vec<u32> = components.iter().flatten().copied().collect();
    assert!(
        all_members.contains(&3),
        "node 3 is reachable from the root and must still be visited"
    );
}

/// A three-node cycle plus an entry node that calls into it but is not
/// itself mutually reachable: the entry stays its own singleton and the
/// cycle is one three-member component, matching "the entry specialization
/// reaches but is NOT a member" from the `Enum.reverse([1])` witness.
#[test]
fn entry_outside_the_cycle_stays_a_singleton() {
    let graph = graph(&[(0, 1), (1, 2), (2, 3), (3, 1)]);
    let components = strongly_connected_components([0], |node| graph[node].clone());
    let components = sorted_components(components);
    assert_eq!(components, vec![vec![0], vec![1, 2, 3]]);
}

/// Passing every node as a root computes the full decomposition, matching
/// how `jobs::native` and `types::regular` use the walker today: an
/// unreachable-from-any-single-root component still surfaces.
#[test]
fn every_node_as_root_finds_every_component() {
    let graph = graph(&[(1, 2), (2, 1), (3, 4), (4, 3)]);
    let components = strongly_connected_components([1, 2, 3, 4], |node| graph[node].clone());
    let components = sorted_components(components);
    assert_eq!(components, vec![vec![1, 2], vec![3, 4]]);
}
