//! Compiler2 protocol callback and implementation facts.
//!
//! Protocol callbacks are function-like namespaced identities without lowered
//! bodies. Protocol implementations map those callbacks onto ordinary
//! functions owned by a source module. Compiler2 publishes both the raw impl
//! registry and a co-defined protocol-dispatch artifact so type legality and
//! impl selection stay separate in the fact graph.

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProtocolDispatchArm {
    pub(crate) target: ModuleId,
    pub(crate) callbacks: HashMap<(String, usize), ProtocolCallbackImpl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProtocolDispatch {
    pub(crate) arms: Vec<ProtocolDispatchArm>,
}

#[derive(Debug, Default)]
pub(crate) struct ProtocolCallbackMap {
    slots: HashMap<FunctionId, ProtocolCallback>,
}

#[derive(Debug, Default)]
pub(crate) struct ProtocolImplMap {
    slots: HashMap<ProtocolImplKey, ProtocolImpl>,
}

#[derive(Debug, Default)]
pub(crate) struct ProtocolDispatchMap {
    slots: HashMap<ModuleId, ProtocolDispatch>,
}

impl ProtocolCallbackMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn define(&mut self, function: FunctionId, callback: ProtocolCallback) {
        self.slots.insert(function, callback);
    }

    pub(crate) fn get(&self, function: FunctionId) -> Option<ProtocolCallback> {
        self.slots.get(&function).copied()
    }
}

impl ProtocolImplMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn define(&mut self, key: ProtocolImplKey, protocol_impl: ProtocolImpl) {
        self.slots.insert(key, protocol_impl);
    }

    pub(crate) fn impl_for(&self, key: &ProtocolImplKey) -> Option<&ProtocolImpl> {
        self.slots.get(key)
    }

    pub(crate) fn impls_for_protocol(
        &self,
        protocol: ModuleId,
    ) -> impl Iterator<Item = (&ProtocolImplKey, &ProtocolImpl)> {
        self.slots
            .iter()
            .filter_map(move |(key, value)| (key.protocol == protocol).then_some((key, value)))
    }
}

impl ProtocolDispatchMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn define(&mut self, protocol: ModuleId, dispatch: ProtocolDispatch, current_revision: u64) -> u64 {
        let changed = self.slots.get(&protocol) != Some(&dispatch);
        self.slots.insert(protocol, dispatch);
        if changed {
            current_revision + 1
        } else {
            current_revision
        }
    }

    pub(crate) fn get(&self, protocol: ModuleId) -> Option<&ProtocolDispatch> {
        self.slots.get(&protocol)
    }
}
