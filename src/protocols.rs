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

pub fn protocol_domain_tag(protocol: &ModuleName) -> String {
    format!("protocol::{}.t", protocol)
}
