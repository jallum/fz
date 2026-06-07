//! Stable facts used to canonicalize activation keys.

use super::identity::FunctionId;

#[derive(Debug, Clone)]
pub(crate) struct FunctionFactSlot<T> {
    value: Option<T>,
    revision: u64,
}

#[derive(Debug, Clone)]
pub(crate) struct FunctionFactMap<T> {
    slots: Vec<FunctionFactSlot<T>>,
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

    pub(crate) fn define(&mut self, function: FunctionId, value: T) -> u64 {
        self.ensure(function);
        let slot = &mut self.slots[function.as_u32() as usize];
        if slot.value.as_ref() != Some(&value) {
            slot.value = Some(value);
            slot.revision += 1;
        }
        slot.revision
    }

    pub(crate) fn get(&self, function: FunctionId) -> Option<&T> {
        self.slots
            .get(function.as_u32() as usize)
            .and_then(|slot| slot.value.as_ref())
    }

    fn ensure(&mut self, function: FunctionId) {
        let needed = function.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || FunctionFactSlot {
                value: None,
                revision: 0,
            });
        }
    }
}

impl<T> Default for FunctionFactMap<T> {
    fn default() -> Self {
        Self { slots: Vec::new() }
    }
}
