//! Compiler2's reusable dispatch facts.
//!
//! These slots hold compiler-owned `dispatch_matrix::pattern` artifacts keyed
//! by function id. They are facts, not work queues: identity lives in the
//! owning map, and each slot only tracks lifecycle state plus revision.

use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch};

use super::identity::FunctionId;
use super::types::Ty;

#[derive(Debug, Clone)]
enum DispatchState<T> {
    Placeholder,
    Defined(T),
}

#[derive(Debug)]
pub(crate) struct FunctionDispatchMap<T> {
    slots: Vec<DispatchState<T>>,
}

pub(crate) type GuardDispatchMap = FunctionDispatchMap<PatternGuardDispatch<Ty>>;
pub(crate) type EntryDispatchMap = FunctionDispatchMap<PatternDispatchPlan<Ty>>;

impl<T> FunctionDispatchMap<T>
where
    T: Clone + PartialEq,
{
    pub(crate) fn new() -> Self {
        Self { slots: Vec::new() }
    }

    pub(crate) fn define(&mut self, id: FunctionId, value: T, current_revision: u64) -> u64 {
        self.ensure(id);
        let slot = &mut self.slots[id.as_u32() as usize];
        let next = DispatchState::Defined(value);
        let changed = !slot.same_state(&next);
        *slot = next;
        if changed {
            current_revision + 1
        } else {
            current_revision
        }
    }

    pub(crate) fn get(&self, id: FunctionId) -> Option<&T> {
        match self.slots.get(id.as_u32() as usize)? {
            DispatchState::Placeholder => None,
            DispatchState::Defined(value) => Some(value),
        }
    }

    fn ensure(&mut self, id: FunctionId) {
        let needed = id.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || DispatchState::Placeholder);
        }
    }
}

impl<T> Default for FunctionDispatchMap<T> {
    fn default() -> Self {
        Self { slots: Vec::new() }
    }
}

impl<T: PartialEq> DispatchState<T> {
    fn same_state(&self, other: &Self) -> bool {
        match (self, other) {
            (DispatchState::Placeholder, DispatchState::Placeholder) => true,
            (DispatchState::Defined(left), DispatchState::Defined(right)) => left == right,
            _ => false,
        }
    }
}
