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

#[derive(Debug, Clone, Default)]
pub struct ProtocolRegistry {
    pub protocols: BTreeMap<ModuleName, ProtocolDecl>,
    pub impls: BTreeMap<ProtocolImplKey, ProtocolImplFact>,
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
    pub spec: Option<crate::modules::interface::InterfaceSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterfaceProtocolImpl {
    pub protocol: ModuleName,
    pub target: ImplTarget,
    pub callbacks: Vec<ExportKey>,
}

#[derive(Debug, Clone)]
pub struct ProtocolDecl {
    pub callbacks: Vec<ProtocolCallbackFact>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ProtocolCallbackFact {
    pub name: String,
    pub arity: usize,
    #[allow(dead_code)]
    // Dispatch/type checking consumes callback specs in the next protocol tickets.
    pub spec: Option<crate::ast::SpecDecl>,
    #[allow(dead_code)] // Kept for callback-specific diagnostics as validation grows.
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ProtocolImplFact {
    pub protocol: ModuleName,
    pub target: ImplTarget,
    pub callbacks: BTreeMap<(String, usize), ExportKey>,
    /// Declared `@spec` of each impl callback that carries one, keyed by
    /// `(name, arity)`. Empty for interface-sourced impls (the interface does
    /// not carry impl callback specs) and for callbacks declared without a
    /// spec. Consumed by callback-spec compatibility checking.
    pub callback_specs: BTreeMap<(String, usize), crate::ast::SpecDecl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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
                                spec: None,
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
            other => t.opaque_of(&format!("impl-target::{}", other)),
        },
    }
}
