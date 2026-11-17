//! What a node reaches, answered once and shared.
//!
//! Two questions ask "which nodes can I get to by following one or more
//! edges?": is a function recursive (it reaches itself over its static
//! callees), and is a call on a cycle (the callee reaches back to the caller
//! over settled call-site targets). Each answer is a World fact
//! (`FactKey::StaticReach`, `FactKey::ExecutableReach`) whose job walks the
//! edge facts of everything the node reaches and reads every one of them, so
//! a change to any edge in the cone reopens the answer. A reach never reads
//! another reach.

use crate::fast_hash::HashSet;

use super::executable_facts::TransportOrigin;
use super::identity::{ExecutableKey, ExecutableNeed};
use super::world::World;
use fz_engine::SemanticOrd;

/// Which call-site targets are the edges of an executable's reach.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CallChain {
    /// Every settled call-site target except call sites whose return arrives
    /// through a closure call: the edges of a direct call chain.
    Direct,
    /// Every settled call-site target, closure calls included.
    All,
}

/// The executables reachable from an executable by at least one edge.
pub(crate) type ReachSet = HashSet<ExecutableKey>;

/// The call-site targets of a settled executable, along `chain`, in semantic
/// order. Requires the executable's facts to be present.
pub(crate) fn executable_successors(world: &World, executable: &ExecutableKey, chain: CallChain) -> Vec<ExecutableKey> {
    let facts = world.executable_facts(executable).expect("settled executable facts");
    let mut successors = HashSet::default();
    for (callsite, summary) in facts.callsites() {
        if chain == CallChain::Direct
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
                successors.insert(ExecutableKey {
                    activation: activation.clone(),
                    need,
                });
            }
        }
    }
    let mut successors = successors.into_iter().collect::<Vec<_>>();
    successors.sort_by(|left, right| left.semantic_cmp(right, world.types()));
    successors
}

#[cfg(test)]
#[path = "reach_test.rs"]
mod tests;
