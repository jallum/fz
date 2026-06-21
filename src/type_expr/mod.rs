//! Shared contract and nominal-name helpers retained outside compiler2.
//!
//! Compiler2 owns the active type-expression parser and resolver in
//! `compiler2/type_expr.rs` and `compiler2/resolve.rs`. This module only keeps
//! the cross-module data shape still shared by backend artifacts plus the opaque
//! tag helpers used by both type kernels.

use std::collections::HashMap;

use crate::types::TypeVarId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedSpecDecl<TypeHandle> {
    pub params: Vec<TypeHandle>,
    pub result: TypeHandle,
    pub constraints: HashMap<TypeVarId, TypeHandle>,
}

/// Build the module-qualified opaque tag stored on an opaque type token.
///
/// When `module_path` is empty, the result is just `alias`; top-level and
/// runtime-prelude opaques have no module owner. Otherwise the tag is
/// `"Mod.Path::alias"`.
#[cfg(test)]
pub fn qualify_opaque_name(module_path: &str, alias: &str) -> String {
    if module_path.is_empty() {
        alias.to_string()
    } else {
        format!("{}::{}", module_path, alias)
    }
}

/// Extract the declaring module path from a qualified opaque tag.
///
/// Returns `None` for unqualified built-in opaques such as `"resource"`.
pub fn opaque_owner_module(qualified: &str) -> Option<&str> {
    qualified.find("::").map(|i| &qualified[..i])
}
