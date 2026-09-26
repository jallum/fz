//! Shared contract data shape retained outside compiler2.
//!
//! Compiler2 owns the active type-expression parser and resolver in
//! `compiler2/type_expr.rs` and `compiler2/resolve.rs`. This module only keeps
//! the cross-module data shape still shared by backend artifacts.

use std::collections::HashMap;

use crate::types::TypeVarId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedSpecDecl<TypeHandle> {
    pub params: Vec<TypeHandle>,
    pub result: TypeHandle,
    pub constraints: HashMap<TypeVarId, TypeHandle>,
}
