//! Stable facts used to canonicalize activation keys.

use std::collections::BTreeMap;

use super::identity::FunctionId;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum DispatchDemand {
    #[default]
    Ignore,
    Whole,
    TupleFields(BTreeMap<u32, DispatchDemand>),
    ListShape(Box<DispatchDemand>),
}

impl DispatchDemand {
    pub(crate) fn join_assign(&mut self, other: DispatchDemand) {
        match (self, other) {
            (Self::Whole, _) | (_, Self::Ignore) => {}
            (slot @ Self::Ignore, next) => *slot = next,
            (slot, Self::Whole) => *slot = Self::Whole,
            (Self::ListShape(current), Self::ListShape(next)) => current.join_assign(*next),
            (Self::TupleFields(current), Self::TupleFields(next)) => {
                for (field, demand) in next {
                    current.entry(field).or_default().join_assign(demand);
                }
            }
            (slot, _) => *slot = Self::Whole,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct FunctionFactMap<T> {
    slots: Vec<Option<T>>,
}

/// The body-shape keying fact `Job::DeriveRecursive` publishes under
/// `FactKey::Recursive`: both answers live in one value so a consumer can
/// never observe one without the other.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BodyKeying {
    /// Reaches itself through the static call graph: its activation keys
    /// convergence-collapse so the ascent settles (fz-y6w).
    pub(crate) recursive: bool,
    /// Calls through a callable, constructs a lambda, or is a capture-holding
    /// lambda: closure brands are meaning to this body, so its keys stay
    /// precise. A body with neither treats brands as freight (fz-6gb).
    pub(crate) consumes_callable_identity: bool,
}

pub(crate) type BodyKeyingMap = FunctionFactMap<BodyKeying>;
pub(crate) type DispatchMaskMap = FunctionFactMap<Vec<DispatchDemand>>;

impl<T> FunctionFactMap<T>
where
    T: Clone + PartialEq,
{
    pub(crate) fn new() -> Self {
        Self { slots: Vec::new() }
    }

    pub(crate) fn define(&mut self, function: FunctionId, value: T) -> bool {
        self.ensure(function);
        let slot = &mut self.slots[function.as_u32() as usize];
        let changed = slot.as_ref() != Some(&value);
        *slot = Some(value);
        changed
    }

    pub(crate) fn get(&self, function: FunctionId) -> Option<&T> {
        self.slots.get(function.as_u32() as usize)?.as_ref()
    }

    fn ensure(&mut self, function: FunctionId) {
        let needed = function.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || None);
        }
    }
}

impl<T> Default for FunctionFactMap<T> {
    fn default() -> Self {
        Self { slots: Vec::new() }
    }
}
