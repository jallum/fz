//! fz-ul4.31.1 — Type-expression parser.
//!
//! Parses a fragment of fz type syntax into a seam `Ty`. Used (in later .31
//! children) by `@spec` and `@type` attribute bodies. Standalone and
//! pure: takes a token slice + a `ModuleTypeEnv` for named-reference
//! resolution; produces a `Ty` and the count of tokens consumed.
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
//! atom_form  = SCALAR_NAME | RUNTIME_NAME | ':' ATOM | INT_LITERAL | FLOAT_LITERAL | '_' | NAMED_REF | NAMED_REF '(' type_expr* ')'
//!
//! SCALAR_NAME ∈ { nil, bool, integer, float, binary, atom, any }
//! RUNTIME_NAME ∈ { pid, ref, utf8 }
//! NAMED_REF   = identifier resolved against the module's type env;
//!               `name(args...)` applies a parameterized alias
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

/// Module-level type environment. Monomorphic aliases resolve directly to
/// `Ty`; parameterized aliases keep their body tokens until an application
/// supplies actual type arguments.
#[derive(Debug, Clone)]
pub struct ParameterizedTypeAlias {
    pub params: Vec<String>,
    pub body_tokens: crate::ast::TypeExprBody,
    pub span: crate::diag::Span,
}

#[derive(Debug, Clone)]
enum TypeAlias {
    Resolved(crate::types::Ty),
    Parameterized(ParameterizedTypeAlias),
    /// A protocol domain template carrying `PROTOCOL_ELEM_VAR` in its
    /// element-parametric positions. Applying `Protocol.t(arg)` instantiates
    /// that variable with `arg`, refining `list(_)` targets to `list(arg)`.
    ProtocolDomain(crate::types::Ty),
}

#[derive(Debug, Clone, Default)]
pub struct ModuleTypeEnv {
    aliases: HashMap<(String, usize), TypeAlias>,
}

impl ModuleTypeEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&self, name: &str) -> Option<&crate::types::Ty> {
        match self.aliases.get(&(name.to_string(), 0)) {
            Some(TypeAlias::Resolved(ty)) => Some(ty),
            _ => None,
        }
    }

    pub fn insert(&mut self, name: String, ty: crate::types::Ty) -> Option<crate::types::Ty> {
        match self.aliases.insert((name, 0), TypeAlias::Resolved(ty)) {
            Some(TypeAlias::Resolved(prev)) => Some(prev),
            _ => None,
        }
    }

    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.aliases.len()
    }

    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        self.aliases.is_empty()
    }

    pub fn extend_env(&mut self, other: ModuleTypeEnv) {
        self.aliases.extend(other.aliases);
    }

    pub fn insert_param_alias(
        &mut self,
        name: String,
        alias: ParameterizedTypeAlias,
    ) -> Option<ParameterizedTypeAlias> {
        match self
            .aliases
            .insert((name, alias.params.len()), TypeAlias::Parameterized(alias))
        {
            Some(TypeAlias::Parameterized(prev)) => Some(prev),
            _ => None,
        }
    }

    fn get_alias(&self, name: &str, arity: usize) -> Option<&TypeAlias> {
        self.aliases.get(&(name.to_string(), arity))
    }

    /// Register a protocol domain template under `name` at arity 1. Applying
    /// `name(arg)` instantiates `PROTOCOL_ELEM_VAR` in the template with `arg`.
    pub fn insert_protocol_domain(&mut self, name: String, template: crate::types::Ty) {
        self.aliases
            .insert((name, 1), TypeAlias::ProtocolDomain(template));
    }

    pub fn param_aliases(
        &self,
    ) -> impl Iterator<Item = (&(String, usize), &ParameterizedTypeAlias)> {
        self.aliases.iter().filter_map(|(key, alias)| match alias {
            TypeAlias::Parameterized(alias) => Some((key, alias)),
            TypeAlias::Resolved(_) | TypeAlias::ProtocolDomain(_) => None,
        })
    }
}

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
    let mut env = ModuleTypeEnv::new();
    env.insert(BUILTIN_UTF8.to_string(), t.brand_of(BUILTIN_UTF8));
    env.insert(BUILTIN_PID.to_string(), t.opaque_of(BUILTIN_PID));
    env.insert(BUILTIN_REF.to_string(), t.opaque_of(BUILTIN_REF));
    env
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

/// Best-effort per-position spec resolution: each param and the result resolve
/// independently, yielding `None` for any body that does not resolve (rather
/// than failing the whole spec). Free type variables are shared across
/// positions. See `env::resolve_spec_decl_positions`.
pub fn resolve_spec_decl_positions<T>(
    t: &mut T,
    decl: &crate::ast::SpecDecl,
    env: &ModuleTypeEnv,
) -> (Vec<Option<crate::types::Ty>>, Option<crate::types::Ty>)
where
    T: Types<Ty = crate::types::Ty>,
{
    self::env::resolve_spec_decl_positions(t, decl, env)
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

pub fn build_module_type_env_for_with_base<T>(
    t: &mut T,
    attrs: &[crate::ast::Attribute],
    module_path: &str,
    base_env: &ModuleTypeEnv,
) -> Result<(ModuleTypeEnv, OpaqueInnerTypes, BrandInnerTypes), TypeExprError>
where
    T: Types<Ty = crate::types::Ty>,
{
    self::env::build_module_type_env_for_with_base(t, attrs, module_path, base_env)
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
