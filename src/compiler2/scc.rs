//! One generic strongly-connected-components walker.
//!
//! Tarjan's algorithm, parameterized over any node id and a neighbor
//! callback. Passing every node in the graph as a root computes the whole
//! graph's decomposition (`jobs::native`'s back-edge annotation over `FnId`,
//! `types::regular`'s equation-forest partition over local body indices).
//! Passing a single root computes only the component reachable from it,
//! which is the shape a rooted membership query needs
//! (`jobs::semantic`'s return-component discovery over `ActivationKey`).
//! One walk serves both shapes: the outer loop over roots is what decides
//! whether the walk is a full decomposition or a single rooted probe.
//!
//! Two other DFS-shaped walks in this crate are NOT folded onto this one:
//! `pull::PendingStrongComponent` overrides one node's edges with
//! not-yet-committed dependencies and threads its own per-call telemetry
//! counters through the drain arbiter's hot path -- a different contract,
//! not just a different node type. `types::emptiness::Memo` is a
//! coinductive memoized evaluator whose "edges" are discovered as a side
//! effect of computing an answer, not listed by a pure neighbor function --
//! it has no static graph for this walker's `neighbors` callback to name.

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// Every strongly connected component reachable from `roots`, each as its
/// own member list. A root with no path back to itself yields its own
/// singleton component -- a component "exists" as a graph fact regardless of
/// size; callers that only care about self-edges or multi-node cycles decide
/// that distinction from the member list plus (if they need it) their own
/// self-edge check, not from anything this walker filters out.
pub(crate) fn strongly_connected_components<N, I>(
    roots: impl IntoIterator<Item = N>,
    mut neighbors: impl FnMut(&N) -> I,
) -> Vec<Vec<N>>
where
    N: Clone + Eq + Hash,
    I: IntoIterator<Item = N>,
{
    let mut walk = Walk {
        next_index: 0,
        index: HashMap::new(),
        lowlink: HashMap::new(),
        stack: Vec::new(),
        on_stack: HashSet::new(),
        components: Vec::new(),
    };
    for root in roots {
        if !walk.index.contains_key(&root) {
            visit(root, &mut walk, &mut neighbors);
        }
    }
    walk.components
}

struct Walk<N> {
    next_index: usize,
    index: HashMap<N, usize>,
    lowlink: HashMap<N, usize>,
    stack: Vec<N>,
    on_stack: HashSet<N>,
    components: Vec<Vec<N>>,
}

fn visit<N, I>(node: N, walk: &mut Walk<N>, neighbors: &mut impl FnMut(&N) -> I)
where
    N: Clone + Eq + Hash,
    I: IntoIterator<Item = N>,
{
    let index = walk.next_index;
    walk.next_index += 1;
    walk.index.insert(node.clone(), index);
    walk.lowlink.insert(node.clone(), index);
    walk.stack.push(node.clone());
    walk.on_stack.insert(node.clone());

    for neighbor in neighbors(&node) {
        if !walk.index.contains_key(&neighbor) {
            visit(neighbor.clone(), walk, neighbors);
            let neighbor_lowlink = walk.lowlink[&neighbor];
            let node_lowlink = walk.lowlink.get_mut(&node).expect("visited node has a lowlink");
            *node_lowlink = (*node_lowlink).min(neighbor_lowlink);
        } else if walk.on_stack.contains(&neighbor) {
            let neighbor_index = walk.index[&neighbor];
            let node_lowlink = walk.lowlink.get_mut(&node).expect("visited node has a lowlink");
            *node_lowlink = (*node_lowlink).min(neighbor_index);
        }
    }

    if walk.lowlink[&node] == walk.index[&node] {
        let mut component = Vec::new();
        loop {
            let member = walk.stack.pop().expect("a component root stays on the stack");
            walk.on_stack.remove(&member);
            let complete = member == node;
            component.push(member);
            if complete {
                break;
            }
        }
        walk.components.push(component);
    }
}
