//! Compiler2 protocol callback and implementation facts.
//!
//! Protocol callbacks are function-like namespaced identities without lowered
//! bodies. Protocol implementations map those callbacks — keyed by the
//! callback's interned `FunctionId`, the same identity callsites resolve to —
//! onto ordinary functions owned by a source module. Compiler2 publishes both the raw impl
//! registry and a co-defined protocol-dispatch artifact so type legality and
//! impl selection stay separate in the fact graph.

use std::collections::HashMap;

use super::identity::{FunctionId, ModuleId};

pub(crate) fn protocol_domain_tag(protocol: impl std::fmt::Display) -> String {
    format!("protocol::{}.t", protocol)
}

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
    pub(crate) callbacks: HashMap<FunctionId, ProtocolCallbackImpl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProtocolDispatchArm {
    pub(crate) target: ModuleId,
    pub(crate) callbacks: HashMap<FunctionId, ProtocolCallbackImpl>,
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

/// The closed implementation relation, discovered at scope time as resolved
/// module ids: for one `(protocol, target)` it names the modules whose source
/// declares the `defimpl`. The semantic tier reads this to demand a provider's
/// definition when a concrete receiver flows to a protocol position — without
/// it, an impl that lives in a module the program never otherwise reaches is
/// invisible to dispatch.
#[derive(Debug, Default)]
pub(crate) struct ProtocolImplProviderMap {
    slots: HashMap<ProtocolImplKey, Vec<ModuleId>>,
}

impl ProtocolImplProviderMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Records `provider` as a source of the `(protocol, target)` impl. Returns
    /// whether the provider set grew, so the caller can bump the fact revision.
    pub(crate) fn register(&mut self, key: ProtocolImplKey, provider: ModuleId) -> bool {
        let providers = self.slots.entry(key).or_default();
        if providers.contains(&provider) {
            return false;
        }
        providers.push(provider);
        true
    }

    /// Every `(target, provider)` recorded for a protocol.
    pub(crate) fn providers_for_protocol(&self, protocol: ModuleId) -> Vec<(ModuleId, ModuleId)> {
        let mut out = Vec::new();
        for (key, providers) in &self.slots {
            if key.protocol != protocol {
                continue;
            }
            for provider in providers {
                out.push((key.target, *provider));
            }
        }
        out.sort_by_key(|(target, provider)| (target.as_u32(), provider.as_u32()));
        out
    }
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

    pub(crate) fn define(&mut self, protocol: ModuleId, dispatch: ProtocolDispatch) -> bool {
        let changed = self.slots.get(&protocol) != Some(&dispatch);
        self.slots.insert(protocol, dispatch);
        changed
    }

    pub(crate) fn get(&self, protocol: ModuleId) -> Option<&ProtocolDispatch> {
        self.slots.get(&protocol)
    }
}
