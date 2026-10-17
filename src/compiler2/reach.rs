//! What a node reaches, answered once and shared.
//!
//! Two questions ask "which nodes can I get to by following one or more
//! edges?": is a function recursive (it reaches itself over its static
//! callees), and is a call on a cycle (the callee reaches back to the caller
//! over settled call-site targets). A `ReachKey` names one node under one
//! kind of edge, and its product holds every node reachable from it.
//!
//! A node's reach is the union, over its successors, of the successor itself
//! and the successor's own reach. Each reach is therefore built from its
//! successors' reaches rather than by walking, and nodes that reach each other
//! settle together as one recursive group, all holding the same set.

use std::collections::HashSet;
use std::rc::Rc;

use super::drive::FactKey;
use super::executable_facts::TransportOrigin;
use super::facts::FactUse;
use super::identity::{ExecutableKey, ExecutableNeed, FunctionId};
use super::pull::{ProductKey, ProductReadContext, ProductValue, PullOutcome, PullWait, RecursiveProductRead};
use super::semantic::SemanticOrd;
use super::world::World;

/// A node together with the edges that define its reach. Every successor of
/// a key is a key of the same kind, so a node is never asked about under
/// edges it does not have.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ReachKey {
    /// A function over its `StaticCallees`.
    Static(FunctionId),
    /// An executable over its settled call-site targets, skipping call sites
    /// whose return arrives through a closure call: the edges of a direct
    /// call chain.
    Direct(ExecutableKey),
    /// An executable over every settled call-site target, closure calls
    /// included.
    All(ExecutableKey),
}

/// The nodes reachable from a key by at least one edge, as keys of the same
/// kind.
pub(crate) type ReachSet = HashSet<ReachKey>;

impl ReachKey {
    /// A function's reach depends on call edges alone, so one answer serves
    /// every root. An executable's reach lives in the root its key carries.
    pub(crate) fn is_program_scoped(&self) -> bool {
        matches!(self, Self::Static(_))
    }

    /// The fact that must be settled before this node's edges can be read.
    fn edges_fact(&self) -> FactKey {
        match self {
            Self::Static(function) => FactKey::StaticCallees(*function),
            Self::Direct(executable) | Self::All(executable) => FactKey::ExecutableFacts(executable.clone()),
        }
    }

    /// The nodes one edge away. Requires `edges_fact` to be settled.
    fn successors(&self, world: &World) -> Vec<ReachKey> {
        match self {
            Self::Static(function) => {
                let mut callees = world.static_callees(*function).to_vec();
                callees.sort();
                callees.dedup();
                callees.into_iter().map(Self::Static).collect()
            }
            Self::Direct(executable) => executable_successors(world, executable, true, Self::Direct),
            Self::All(executable) => executable_successors(world, executable, false, Self::All),
        }
    }
}

/// The call-site targets of a settled executable, each wrapped as the same
/// kind of node as the asker. A direct chain skips call sites whose return
/// arrives through a closure call.
fn executable_successors(
    world: &World,
    executable: &ExecutableKey,
    direct_only: bool,
    node: fn(ExecutableKey) -> ReachKey,
) -> Vec<ReachKey> {
    let facts = world.executable_facts(executable).expect("settled executable facts");
    let mut successors = HashSet::new();
    for (callsite, summary) in facts.callsites() {
        if direct_only
            && matches!(
                facts.callsite_return_origin(*callsite),
                Some(TransportOrigin::ClosureCallReturn { .. })
            )
        {
            continue;
        }
        let need = facts
            .callsite_needs()
            .get(callsite)
            .copied()
            .unwrap_or(ExecutableNeed::Value);
        for target in &summary.targets {
            if let Some(activation) = &target.activation {
                successors.insert(node(ExecutableKey {
                    activation: activation.clone(),
                    need,
                }));
            }
        }
    }
    let mut successors = successors.into_iter().collect::<Vec<_>>();
    successors.sort_by(|left, right| left.semantic_cmp(right, world.types()));
    successors
}

impl SemanticOrd<super::types::Types> for ReachKey {
    fn semantic_cmp(&self, other: &Self, types: &super::types::Types) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Static(left), Self::Static(right)) => left.cmp(right),
            (Self::Direct(left), Self::Direct(right)) | (Self::All(left), Self::All(right)) => {
                left.semantic_cmp(right, types)
            }
            _ => self.rank().cmp(&other.rank()),
        }
    }
}

impl ReachKey {
    fn rank(&self) -> u8 {
        match self {
            Self::Static(_) => 0,
            Self::Direct(_) => 1,
            Self::All(_) => 2,
        }
    }
}

pub(crate) fn produce_reach_product(
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    world: &World,
    from: &ReachKey,
) -> PullOutcome {
    let edges = FactUse::settled(from.edges_fact());
    if !context.read_fact(world, edges.clone()) {
        return PullOutcome::wait_on_fact(edges);
    }
    let types = world.types();
    let current = ProductKey::Reach(from.clone());
    let successors = from.successors(world);
    let mut reach: ReachSet = successors.iter().cloned().collect();
    let mut waits = Vec::new();
    let mut recursive_group: Option<Vec<ProductKey>> = None;
    for successor in successors {
        let key = ProductKey::Reach(successor);
        match context.read_recursive_product(tel, key.clone(), &current, types) {
            RecursiveProductRead::Ready(ProductValue::Reach(successor_reach)) => {
                reach.extend(successor_reach.iter().cloned());
            }
            RecursiveProductRead::Ready(other) => panic!("reach product produced unexpected value {other:?}"),
            RecursiveProductRead::Waiting => waits.push(PullWait::Product(key)),
            RecursiveProductRead::Group(members) => {
                if let Some(previous) = &recursive_group {
                    assert!(
                        previous.iter().all(|member| members.contains(member)),
                        "recording another read cannot shrink a recursive group"
                    );
                }
                recursive_group = Some(members);
            }
        }
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let Some(members) = recursive_group else {
        return PullOutcome::Produced(ProductValue::Reach(Rc::new(reach)));
    };

    // Members reach each other, so each holds the one set: every member's own
    // successors, plus whatever the group reaches beyond itself. A member's
    // edges are settled facts, because it recorded reading them before it
    // joined the group.
    let mut group_reach = reach;
    for member in &members {
        let ProductKey::Reach(member) = member else {
            panic!("a reach group holds only reach members, found {member:?}")
        };
        group_reach.extend(member.successors(world));
    }
    let mut external_waits = Vec::new();
    for (key, value) in context.recorded_recursive_group_inputs(&current, &members, types) {
        match (&key, value) {
            (ProductKey::Reach(_), Some(ProductValue::Reach(beyond))) => group_reach.extend(beyond.iter().cloned()),
            (ProductKey::Reach(_), None) => external_waits.push(PullWait::Product(key)),
            (_, value) => panic!("a reach group recorded unexpected input {key:?}: {value:?}"),
        }
    }
    if !external_waits.is_empty() {
        return PullOutcome::Waiting(external_waits);
    }
    let shared = Rc::new(group_reach);
    let values = members
        .iter()
        .map(|_| ProductValue::Reach(Rc::clone(&shared)))
        .collect();
    PullOutcome::Produced(context.stage_recursive_group(&current, &members, values))
}

#[cfg(test)]
#[path = "reach_test.rs"]
mod tests;
