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

pub(crate) type RecursiveMap = FunctionFactMap<bool>;
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
