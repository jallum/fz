//! Compiler2's reusable dispatch facts.
//!
//! These slots hold compiler-owned `dispatch_matrix::pattern` artifacts keyed
//! by function id. They are facts, not work queues: identity lives in the
//! owning map, and each slot only tracks lifecycle state plus revision.
//! SourcePatternResolver supplies the shared producer with World-owned struct
//! identity and the caller's guard-helper resolution.

use crate::ast::{CallableName, ModuleTarget};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch, PatternResolver, SourcePatternError};
use crate::source::Span;

use super::identity::{FunctionId, ModuleId};
use super::namespace::Namespace;
use super::types::Ty;
use super::world::World;

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

    pub(crate) fn define(&mut self, id: FunctionId, value: T) -> bool {
        self.ensure(id);
        let slot = &mut self.slots[id.as_u32() as usize];
        let next = DispatchState::Defined(value);
        let changed = !slot.same_state(&next);
        *slot = next;
        changed
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

pub(crate) struct SourcePatternResolver<'a, F> {
    pub(crate) world: &'a mut World,
    pub(crate) namespace: Namespace,
    pub(crate) owner: ModuleId,
    pub(crate) guard: F,
}

impl<F> PatternResolver<Ty> for SourcePatternResolver<'_, F>
where
    F: FnMut(&mut World, &CallableName, usize) -> Result<Option<PatternGuardDispatch<Ty>>, SourcePatternError>,
{
    fn struct_type(&mut self, module: &ModuleTarget, _span: Span) -> Result<Ty, SourcePatternError> {
        let module_id = self
            .world
            .resolve_module_target(self.owner, self.namespace, module)
            .ok_or_else(|| SourcePatternError::UnresolvedStruct(module.clone()))?;
        Ok(self.world.struct_value_ty(module_id, &[], &[]))
    }

    fn guard_call(
        &mut self,
        name: &CallableName,
        arity: usize,
    ) -> Result<Option<PatternGuardDispatch<Ty>>, SourcePatternError> {
        (self.guard)(self.world, name, arity)
    }
}
