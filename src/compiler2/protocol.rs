//! Compiler2 protocol callback and implementation facts.
//!
//! Protocol callbacks are function-like namespaced identities without lowered
//! bodies. Protocol implementations map those callbacks onto ordinary
//! functions owned by a source module. Semantic analysis consumes these facts
//! directly when a rooted call reaches a protocol callback.

use std::collections::HashMap;

use super::identity::{FunctionId, ModuleId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ProtocolCallback {
    pub(crate) protocol: ModuleId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ProtocolCallbackImpl {
    pub(crate) function: FunctionId,
    pub(crate) owner_module: ModuleId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ProtocolImplKey {
    pub(crate) protocol: ModuleId,
    pub(crate) target: ModuleId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProtocolImpl {
    pub(crate) callbacks: HashMap<(String, usize), ProtocolCallbackImpl>,
}

#[derive(Debug, Clone)]
struct Revisioned<T> {
    value: T,
    revision: u64,
}

#[derive(Debug, Default)]
pub(crate) struct ProtocolCallbackMap {
    slots: HashMap<FunctionId, Revisioned<ProtocolCallback>>,
}

#[derive(Debug, Default)]
pub(crate) struct ProtocolImplMap {
    slots: HashMap<ProtocolImplKey, Revisioned<ProtocolImpl>>,
}

impl ProtocolCallbackMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn define(&mut self, function: FunctionId, callback: ProtocolCallback) -> u64 {
        match self.slots.get_mut(&function) {
            Some(slot) => {
                if slot.value != callback {
                    slot.value = callback;
                    slot.revision += 1;
                }
                slot.revision
            }
            None => {
                self.slots.insert(
                    function,
                    Revisioned {
                        value: callback,
                        revision: 1,
                    },
                );
                1
            }
        }
    }

    pub(crate) fn get(&self, function: FunctionId) -> Option<ProtocolCallback> {
        self.slots.get(&function).map(|slot| slot.value)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&FunctionId, ProtocolCallback)> {
        self.slots.iter().map(|(function, slot)| (function, slot.value))
    }
}

impl ProtocolImplMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn define(&mut self, key: ProtocolImplKey, protocol_impl: ProtocolImpl) -> u64 {
        match self.slots.get_mut(&key) {
            Some(slot) => {
                if slot.value != protocol_impl {
                    slot.value = protocol_impl;
                    slot.revision += 1;
                }
                slot.revision
            }
            None => {
                self.slots.insert(
                    key,
                    Revisioned {
                        value: protocol_impl,
                        revision: 1,
                    },
                );
                1
            }
        }
    }

    pub(crate) fn impl_for(&self, key: &ProtocolImplKey) -> Option<&ProtocolImpl> {
        self.slots.get(key).map(|slot| &slot.value)
    }

    pub(crate) fn impls_for_protocol(
        &self,
        protocol: ModuleId,
    ) -> impl Iterator<Item = (&ProtocolImplKey, &ProtocolImpl)> {
        self.slots
            .iter()
            .filter_map(move |(key, slot)| (key.protocol == protocol).then_some((key, &slot.value)))
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&ProtocolImplKey, &ProtocolImpl)> {
        self.slots.iter().map(|(key, slot)| (key, &slot.value))
    }
}
