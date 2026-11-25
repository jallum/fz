//! The meeting points of a dispatch graph during emission.
//!
//! A dispatch graph shares nodes: several edges lead to one node, and the node
//! is the same decision however it was reached. An emitter that follows each
//! edge to its target would emit a shared node once per edge, and the nodes
//! below it once per copy. Emitters instead stop at a join, record what the
//! arrival knows, and emit the join once after every arrival has been seen.
//!
//! Graph ids ascend from the leaves to the root, so a node is reached only
//! from nodes with larger ids. Emitting pending joins from the largest id down
//! therefore emits each join after all of its arrivals.

use super::{DispatchGraph, GraphNodeId, OutcomeId};
use std::collections::BTreeMap;

/// How a decision ends: with no outcome, or with the one it selected. The
/// emitter that owns the decision's consequences emits it.
#[derive(Clone, Copy)]
pub(crate) enum DispatchLeaf {
    Fail,
    Outcome(OutcomeId),
}

/// What an emitter knows on arriving at a join, and what the join may keep.
pub(crate) trait ArrivalState: Sized {
    /// The state of a join reached by `arrivals`: only what every arrival
    /// holds. A join one arrival reached keeps that arrival whole.
    fn meet(arrivals: Vec<Self>) -> Self;
}

/// A join reached and not yet emitted: its block, the state of every arrival.
struct Reached<Block, State> {
    block: Block,
    arrivals: Vec<State>,
}

/// A join whose arrivals have all been seen, ready to emit.
pub(crate) struct ReadyJoin<Block, State> {
    pub(crate) node: GraphNodeId,
    pub(crate) block: Block,
    pub(crate) state: State,
}

/// The joins one emission has reached and not yet emitted.
pub(crate) struct DispatchJoins<Block, State> {
    reached: BTreeMap<GraphNodeId, Reached<Block, State>>,
}

impl<Block, State> Default for DispatchJoins<Block, State> {
    fn default() -> Self {
        Self {
            reached: BTreeMap::new(),
        }
    }
}

impl<Block: Copy, State: ArrivalState + Clone> DispatchJoins<Block, State> {
    /// An edge to `target` arrives holding `state`. When `target` is a join,
    /// records the arrival and answers the block the emitter jumps to, made by
    /// `new_block` on the first arrival. When it is not, answers `None` and
    /// the emitter emits the target where it stands.
    pub(crate) fn arrive<TypeHandle>(
        &mut self,
        graph: &DispatchGraph<TypeHandle>,
        target: GraphNodeId,
        state: &State,
        new_block: impl FnOnce() -> Block,
    ) -> Option<Block> {
        if !graph.is_join(target) {
            return None;
        }
        let reached = self.reached.entry(target).or_insert_with(|| Reached {
            block: new_block(),
            arrivals: Vec::new(),
        });
        reached.arrivals.push(state.clone());
        Some(reached.block)
    }

    /// The reached join with the largest id, with the meet of its arrivals.
    pub(crate) fn next(&mut self) -> Option<ReadyJoin<Block, State>> {
        let (node, Reached { block, arrivals }) = self.reached.pop_last()?;
        Some(ReadyJoin {
            node,
            block,
            state: State::meet(arrivals),
        })
    }
}

#[cfg(test)]
#[path = "joins_test.rs"]
mod joins_test;
