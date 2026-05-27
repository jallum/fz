//! fz-ul4.31.1 — Type-expression parser.
//!
//! Parses a fragment of fz type syntax into a seam `Ty`. Used (in later .31
//! children) by `@spec` and `@type` attribute bodies. Standalone and
//! pure: takes a token slice + a `ModuleTypeEnv` (name → Ty) for
//! named-reference resolution; produces a `Ty` and the count of
//! tokens consumed.
//!
//! ## Grammar
//!
//! ```text
//! type_expr  = union
//! union      = primary ('|' primary)*
//! primary    = list | tuple | paren_or_arrow | atom_form
//! list       = '[' type_expr ']'
//! tuple      = '{' (type_expr (',' type_expr)*)? '}'
//! paren_or_arrow = '(' (type_expr (',' type_expr)*)? ')' ('->' type_expr)?
//! atom_form  = SCALAR_NAME | RUNTIME_NAME | ':' ATOM | INT_LITERAL | FLOAT_LITERAL | '_' | NAMED_REF
//!
//! SCALAR_NAME ∈ { nil, bool, integer, float, binary, atom, any }
//! RUNTIME_NAME ∈ { pid, ref, utf8 }
//! NAMED_REF   = identifier resolved against the module's type env
//! ```
//!
//! `'|'` binds looser than primary forms; `'(A, B) -> R'` is one
//! primary (the arrow itself). `[T]` is a list of T (not a postfix
//! operator). `{T, U}` is a tuple. `:foo` is the singleton atom.
//! Bare `42` and `2.5` are singleton literals.

use std::collections::HashMap;

use crate::diag::Span;
use crate::lexer::{Tok, Token};
use crate::types::Types;

/// Module-level type environment: name → declared type. Populated by
/// `@type name :: <expr>` declarations in .31.3.
pub type ModuleTypeEnv = HashMap<String, crate::types::Ty>;

#[derive(Debug, Clone)]
pub struct TypeExprError {
    pub msg: String,
    pub span: Span,
}

impl std::fmt::Display for TypeExprError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "type-expr error: {}", self.msg)
    }
}

/// fz-ul4.31.4 — Resolved form of a `SpecDecl` after type-expression
/// lookup. Produced by `resolve_spec_decl` given a `ModuleTypeEnv`.
#[derive(Debug, Clone)]
pub struct ResolvedSpec {
    pub params: Vec<crate::types::Ty>,
    pub result: crate::types::Ty,
    pub constraints: HashMap<crate::types::TypeVarId, crate::types::Ty>,
}

/// fz-swt.8 — Inner-type map for opaque aliases declared in one
/// module. Keyed by the qualified opaque tag (matches the tag stored
/// on the qualified opaque type name); value is the parsed body following
/// the `opaque` keyword — i.e., the inner type `T` for
/// `@type t :: opaque T` (or `opaque resource(T)`, etc.).
///
/// The planner consumes this map at `Prim::MapGet(handle, :value)` sites
/// to type `handle.value` as `T` instead of falling back to the generic
/// map-lookup result. Visibility gating already lives in
/// `crate::ir_planner::check_opaque_visibility`; the inner-type map is the
/// payload the gate guards.
pub type OpaqueInnerTypes = HashMap<String, crate::types::Ty>;

/// fz-axu.3 (K2) — Inner-type map for `refines` brand aliases
/// declared in one module. Keyed by the qualified brand tag (matches
/// the qualified brand type name); value is the parsed body
/// following the `refines` keyword — i.e., the inner type `T` for
/// `@type B :: refines T`.
///
/// Distinct from `OpaqueInnerTypes` because the K4 is_subtype rule
/// treats brands as a proper subset of their inner, whereas opaques
/// are nominally disjoint from theirs. K2 only collects the map;
/// downstream tickets (K3 mint, K4 lattice rule, K5 erasure) read it.
pub type BrandInnerTypes = HashMap<String, crate::types::Ty>;

pub const BUILTIN_UTF8: &str = "utf8";
pub const BUILTIN_PID: &str = "pid";
pub const BUILTIN_REF: &str = "ref";

pub fn builtin_type_env<T>(t: &mut T) -> ModuleTypeEnv
where
    T: Types<Ty = crate::types::Ty>,
{
    HashMap::from([
        (BUILTIN_UTF8.to_string(), t.brand_of(BUILTIN_UTF8)),
        (BUILTIN_PID.to_string(), t.opaque_of(BUILTIN_PID)),
        (BUILTIN_REF.to_string(), t.opaque_of(BUILTIN_REF)),
    ])
}

pub fn builtin_opaque_inners<T>(t: &mut T) -> OpaqueInnerTypes
where
    T: Types<Ty = crate::types::Ty>,
{
    HashMap::from([
        (BUILTIN_PID.to_string(), t.int()),
        (BUILTIN_REF.to_string(), t.cpointer()),
    ])
}

pub fn builtin_brand_inners<T>(t: &mut T) -> BrandInnerTypes
where
    T: Types<Ty = crate::types::Ty>,
{
    HashMap::from([(BUILTIN_UTF8.to_string(), t.str_t())])
}

mod env;
mod parser;

pub use parser::parse_type_expr;

pub fn resolve_spec_decl<T>(
    t: &mut T,
    decl: &crate::ast::SpecDecl,
    env: &ModuleTypeEnv,
) -> Result<ResolvedSpec, TypeExprError>
where
    T: Types<Ty = crate::types::Ty>,
{
    self::env::resolve_spec_decl(t, decl, env)
}

#[cfg(test)]
pub fn build_module_type_env<T>(
    t: &mut T,
    attrs: &[crate::ast::Attribute],
) -> Result<ModuleTypeEnv, TypeExprError>
where
    T: Types<Ty = crate::types::Ty>,
{
    self::env::build_module_type_env(t, attrs)
}

pub fn build_module_type_env_for<T>(
    t: &mut T,
    attrs: &[crate::ast::Attribute],
    module_path: &str,
) -> Result<(ModuleTypeEnv, OpaqueInnerTypes, BrandInnerTypes), TypeExprError>
where
    T: Types<Ty = crate::types::Ty>,
{
    self::env::build_module_type_env_for(t, attrs, module_path)
}

#[cfg(test)]
pub fn qualify_opaque_name(module_path: &str, alias: &str) -> String {
    self::env::qualify_opaque_name(module_path, alias)
}

pub fn opaque_owner_module(qualified: &str) -> Option<&str> {
    self::env::opaque_owner_module(qualified)
}

#[cfg(test)]
mod tests;
