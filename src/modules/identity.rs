//! Canonical module and export identities.
//!
//! The frontend still renders many names as dotted strings because the
//! existing IR and dumps are string-shaped. These types are the semantic
//! boundary: module paths and exported functions are assembled from parsed
//! segments, not recovered by repeatedly splitting display text.

pub use fz_runtime::module_name::{ModuleDenotation, ModuleName};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Mfa {
    pub module: ModuleName,
    pub name: String,
    pub arity: usize,
}

impl Mfa {
    pub fn new(module: ModuleName, name: impl Into<String>, arity: usize) -> Self {
        Self {
            module,
            name: name.into(),
            arity,
        }
    }
}

impl fmt::Display for Mfa {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}/{}", self.module, self.name, self.arity)
    }
}

#[cfg(test)]
#[path = "identity_test.rs"]
mod identity_test;
