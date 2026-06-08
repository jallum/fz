//! Compiler2's artifact-side program projection.
//!
//! A materialized program is the closed backend handoff for one root. It owns
//! the current entry executable, the root revision it came from, and one
//! materialized executable body per reachable `ExecutableKey`.

use std::collections::HashMap;

use super::body::{CallSiteId, LoweredBody};
use super::identity::{ExecutableKey, ExecutableNeed, RootId};
use super::semantic::SelectedCallee;
use super::types::Ty;

#[derive(Debug, Clone, PartialEq)]
pub struct MaterializedProgram {
    pub semantic_revision: u64,
    pub entry: ExecutableKey,
    pub executables: HashMap<ExecutableKey, MaterializedExecutable>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MaterializedExecutable {
    pub return_ty: Ty,
    pub body: LoweredBody,
    pub call_edges: HashMap<CallSiteId, MaterializedCallEdge>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaterializedCallEdge {
    pub callee: SelectedCallee,
    pub input_types: Vec<Ty>,
    pub need: ExecutableNeed,
    pub return_ty: Ty,
}

#[derive(Debug, Clone)]
pub struct MaterializedProgramSlot {
    pub(crate) state: MaterializedProgramState,
    pub(crate) revision: u64,
}

#[derive(Debug, Clone)]
pub enum MaterializedProgramState {
    Placeholder,
    Defined(MaterializedProgram),
}

#[derive(Debug, Default)]
pub struct MaterializedProgramMap {
    slots: Vec<MaterializedProgramSlot>,
}

impl MaterializedProgramMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, root: RootId, program: MaterializedProgram) -> u64 {
        self.ensure(root);
        let slot = &mut self.slots[root.as_u32() as usize];
        let next = MaterializedProgramState::Defined(program);
        if !slot.state.same_state(&next) {
            slot.state = next;
            slot.revision += 1;
        }
        slot.revision
    }

    pub fn get(&self, root: RootId) -> Option<&MaterializedProgram> {
        match &self.slots.get(root.as_u32() as usize)?.state {
            MaterializedProgramState::Placeholder => None,
            MaterializedProgramState::Defined(program) => Some(program),
        }
    }

    fn ensure(&mut self, root: RootId) {
        let needed = root.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || MaterializedProgramSlot {
                state: MaterializedProgramState::Placeholder,
                revision: 0,
            });
        }
    }
}

impl MaterializedProgramState {
    fn same_state(&self, other: &Self) -> bool {
        match (self, other) {
            (MaterializedProgramState::Placeholder, MaterializedProgramState::Placeholder) => true,
            (MaterializedProgramState::Defined(left), MaterializedProgramState::Defined(right)) => left == right,
            _ => false,
        }
    }
}
