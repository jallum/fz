//! Compiler2's reusable dispatch facts.
//!
//! These slots hold compiler-owned `dispatch_matrix::pattern` artifacts keyed
//! by function id. They are facts, not work queues: identity lives in the
//! owning map, and each slot only tracks lifecycle state plus revision.

use crate::dispatch_matrix::pattern::PatternGuardDispatch;

use super::identity::FunctionId;

#[derive(Debug, Clone)]
pub(crate) struct GuardDispatchSlot {
    pub(crate) state: GuardDispatchState,
    pub(crate) revision: u64,
}

#[derive(Debug, Clone)]
pub(crate) enum GuardDispatchState {
    Placeholder,
    Reified(PatternGuardDispatch),
}

#[derive(Debug, Default)]
pub(crate) struct GuardDispatchMap {
    slots: Vec<GuardDispatchSlot>,
}

impl GuardDispatchMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn define(&mut self, id: FunctionId, dispatch: PatternGuardDispatch) -> u64 {
        self.ensure(id);
        let slot = &mut self.slots[id.as_u32() as usize];
        let next = GuardDispatchState::Reified(dispatch);
        if !slot.state.same_state(&next) {
            slot.state = next;
            slot.revision += 1;
        }
        slot.revision
    }

    fn ensure(&mut self, id: FunctionId) {
        let needed = id.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || GuardDispatchSlot {
                state: GuardDispatchState::Placeholder,
                revision: 0,
            });
        }
    }
}

impl GuardDispatchState {
    fn same_state(&self, other: &Self) -> bool {
        match (self, other) {
            (GuardDispatchState::Placeholder, GuardDispatchState::Placeholder) => true,
            (GuardDispatchState::Reified(left), GuardDispatchState::Reified(right)) => left == right,
            _ => false,
        }
    }
}
