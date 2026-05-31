//! Protocol registry facts.
//!
//! Protocols are represented as typed resolver facts, not as lowered
//! functions. Later dispatch and type-checking stages consume this registry
//! directly so they do not need to rediscover protocol shape from flattened
//! names.

use crate::diag::Span;
use crate::modules::identity::{ExportKey, ModuleName};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ProtocolRegistry {
    /// `ModuleName` derives `Serialize` as a struct (`{ segments: [...] }`),
    /// which serde_json rejects as a map key, so this map serializes as a
    /// sequence of `(key, value)` entries.
    #[serde(with = "protocols_as_seq")]
    pub protocols: BTreeMap<ModuleName, ProtocolDecl>,
    /// `ProtocolImplKey` is a struct, which serde_json rejects as a map key,
    /// so this map serializes as a sequence of `(key, value)` entries.
    #[serde(with = "impls_as_seq")]
    pub impls: BTreeMap<ProtocolImplKey, ProtocolImplFact>,
}

/// (De)serialize `BTreeMap<ModuleName, ProtocolDecl>` as a
/// `Vec<(ModuleName, ProtocolDecl)>` so the struct key survives serde_json
/// (which forbids non-string object keys).
mod protocols_as_seq {
    use super::{ModuleName, ProtocolDecl};
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::BTreeMap;

    pub fn serialize<S: Serializer>(
        map: &BTreeMap<ModuleName, ProtocolDecl>,
        s: S,
    ) -> Result<S::Ok, S::Error> {
        map.iter().collect::<Vec<_>>().serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        d: D,
    ) -> Result<BTreeMap<ModuleName, ProtocolDecl>, D::Error> {
        Ok(Vec::<(ModuleName, ProtocolDecl)>::deserialize(d)?
            .into_iter()
            .collect())
    }
}

/// (De)serialize `BTreeMap<ProtocolImplKey, ProtocolImplFact>` as a
/// `Vec<(ProtocolImplKey, ProtocolImplFact)>` so the struct key survives
/// serde_json (which forbids non-string object keys).
mod impls_as_seq {
    use super::{ProtocolImplFact, ProtocolImplKey};
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::BTreeMap;

    pub fn serialize<S: Serializer>(
        map: &BTreeMap<ProtocolImplKey, ProtocolImplFact>,
        s: S,
    ) -> Result<S::Ok, S::Error> {
        map.iter().collect::<Vec<_>>().serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        d: D,
    ) -> Result<BTreeMap<ProtocolImplKey, ProtocolImplFact>, D::Error> {
        Ok(Vec::<(ProtocolImplKey, ProtocolImplFact)>::deserialize(d)?
            .into_iter()
            .collect())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterfaceProtocol {
    pub name: ModuleName,
    pub callbacks: Vec<InterfaceProtocolCallback>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct InterfaceProtocolCallback {
    pub name: String,
    pub arity: usize,
    #[serde(default)]
    pub specs: Vec<crate::modules::interface::InterfaceSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterfaceProtocolImpl {
    pub protocol: ModuleName,
    pub target: ImplTarget,
    pub callbacks: Vec<ExportKey>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolDecl {
    pub callbacks: Vec<ProtocolCallbackFact>,
    pub span: Span,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolCallbackFact {
    pub name: String,
    pub arity: usize,
    #[serde(default)]
    // Dispatch/type checking consumes callback specs in the next protocol tickets.
    pub specs: Vec<crate::ast::SpecDecl>,
    #[allow(dead_code)] // Kept for callback-specific diagnostics as validation grows.
    pub span: Span,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolImplFact {
    pub protocol: ModuleName,
    pub target: ImplTarget,
    /// Tuple `(String, usize)` keys are not valid serde_json object keys, so
    /// these two maps serialize as sequences of `(key, value)` entries.
    #[serde(with = "callbacks_as_seq")]
    pub callbacks: BTreeMap<(String, usize), ExportKey>,
    /// Declared `@spec` of each impl callback that carries one, keyed by
    /// `(name, arity)`. Empty for interface-sourced impls (the interface does
    /// not carry impl callback specs) and for callbacks declared without a
    /// spec. Consumed by callback-spec compatibility checking.
    #[serde(with = "callback_specs_as_seq")]
    pub callback_specs: BTreeMap<(String, usize), Vec<crate::ast::SpecDecl>>,
    pub span: Span,
}

/// (De)serialize the tuple-keyed `callbacks` map as a sequence of entries.
mod callbacks_as_seq {
    use crate::modules::identity::ExportKey;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::BTreeMap;

    pub fn serialize<S: Serializer>(
        map: &BTreeMap<(String, usize), ExportKey>,
        s: S,
    ) -> Result<S::Ok, S::Error> {
        map.iter().collect::<Vec<_>>().serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        d: D,
    ) -> Result<BTreeMap<(String, usize), ExportKey>, D::Error> {
        Ok(Vec::<((String, usize), ExportKey)>::deserialize(d)?
            .into_iter()
            .collect())
    }
}

/// (De)serialize the tuple-keyed `callback_specs` map as a sequence of entries.
mod callback_specs_as_seq {
    use crate::ast::SpecDecl;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::BTreeMap;

    pub fn serialize<S: Serializer>(
        map: &BTreeMap<(String, usize), Vec<SpecDecl>>,
        s: S,
    ) -> Result<S::Ok, S::Error> {
        map.iter().collect::<Vec<_>>().serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        d: D,
    ) -> Result<BTreeMap<(String, usize), Vec<SpecDecl>>, D::Error> {
        Ok(Vec::<((String, usize), Vec<SpecDecl>)>::deserialize(d)?
            .into_iter()
            .collect())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ProtocolImplKey {
    pub protocol: ModuleName,
    pub target: ImplTarget,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ImplTarget {
    Module(ModuleName),
}

impl ImplTarget {
    pub fn module(module: ModuleName) -> Self {
        Self::Module(module)
    }

    pub fn display_name(&self) -> String {
        match self {
            Self::Module(module) => module.to_string(),
        }
    }
}

impl fmt::Display for ImplTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.display_name())
    }
}

impl ProtocolRegistry {
    pub fn extend_interfaces(
        &mut self,
        interfaces: &std::collections::BTreeMap<
            ModuleName,
            crate::modules::interface::ModuleInterface,
        >,
    ) {
        for interface in interfaces.values() {
            for protocol in &interface.protocols {
                self.protocols
                    .entry(protocol.name.clone())
                    .or_insert_with(|| ProtocolDecl {
                        callbacks: protocol
                            .callbacks
                            .iter()
                            .map(|callback| ProtocolCallbackFact {
                                name: callback.name.clone(),
                                arity: callback.arity,
                                specs: Vec::new(),
                                span: Span::DUMMY,
                            })
                            .collect(),
                        span: Span::DUMMY,
                    });
            }
            for protocol_impl in &interface.protocol_impls {
                let callbacks = protocol_impl
                    .callbacks
                    .iter()
                    .map(|callback| ((callback.name.clone(), callback.arity), callback.clone()))
                    .collect();
                let key = ProtocolImplKey {
                    protocol: protocol_impl.protocol.clone(),
                    target: protocol_impl.target.clone(),
                };
                self.impls.entry(key).or_insert_with(|| ProtocolImplFact {
                    protocol: protocol_impl.protocol.clone(),
                    target: protocol_impl.target.clone(),
                    callbacks,
                    callback_specs: BTreeMap::new(),
                    span: Span::DUMMY,
                });
            }
        }
    }
}

pub fn protocol_domain_tag(protocol: &ModuleName) -> String {
    format!("protocol::{}.t", protocol)
}

/// Reserved type variable standing for a protocol domain's element parameter
/// (the `a` in `Enumerable.t(a)`). The domain *template* carries this variable
/// in every element-parametric target position; applying `t(arg)` instantiates
/// it with `arg`. The id is `u32::MAX` so it never collides with the `0,1,2,…`
/// variables minted for user-written type names.
pub const PROTOCOL_ELEM_VAR: crate::types::TypeVarId = crate::types::TypeVarId(u32::MAX);

pub fn impl_target_type<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    target: &ImplTarget,
) -> crate::types::Ty {
    let any = t.any();
    impl_target_type_with_element(t, target, any)
}

/// The type of an impl target, with `element` threaded into element-parametric
/// targets. `List` becomes `list(element)`; scalar and map targets are not
/// parametric in a single element type, so `element` does not refine them.
/// `impl_target_type` is the `element = any` case.
pub fn impl_target_type_with_element<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    target: &ImplTarget,
    element: crate::types::Ty,
) -> crate::types::Ty {
    match target {
        ImplTarget::Module(module) => match module.last_segment() {
            "List" => t.list(element),
            "Integer" => t.int(),
            "Float" => t.float(),
            "Atom" => t.atom(),
            "Binary" => t.str_t(),
            "Map" => t.map_top(),
            other => struct_impl_target_type(t, other),
        },
    }
}

pub fn struct_impl_target_type<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module_last_segment: &str,
) -> crate::types::Ty {
    t.opaque_of(&format!("impl-target::{}", module_last_segment))
}
