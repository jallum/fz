//! Stable facts used to canonicalize activation keys.

use super::identity::FunctionId;

#[derive(Debug, Clone)]
pub(crate) struct FunctionFactMap<T> {
    slots: Vec<Option<T>>,
}

pub(crate) type RecursiveMap = FunctionFactMap<bool>;
pub(crate) type DispatchMaskMap = FunctionFactMap<Vec<bool>>;

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
