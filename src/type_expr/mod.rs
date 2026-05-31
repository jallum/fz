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

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::diag::Span;
use crate::modules::identity::ModuleName;
use crate::parser::lexer::{Tok, Token};
use crate::types::{
    ClosureTypes, SchemeInstantiation, SchemeMatch, Types, instantiate_scheme_match,
};

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

#[derive(Debug, Clone)]
pub struct StructFieldType {
    pub name: String,
    pub ty: crate::types::Ty,
}

#[derive(Debug, Clone)]
pub struct StructRecordType {
    pub module: ModuleName,
    pub span: crate::diag::Span,
    pub fields: Vec<StructFieldType>,
}

#[derive(Debug, Clone, Default)]
pub struct ModuleTypeEnv {
    aliases: HashMap<(String, usize), TypeAlias>,
    struct_records: HashMap<String, StructRecordType>,
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

    pub fn insert_struct_record(&mut self, alias: String, record: StructRecordType) {
        self.struct_records.insert(alias, record);
    }

    #[cfg(test)]
    pub fn struct_record(&self, alias: &str) -> Option<&StructRecordType> {
        self.struct_records.get(alias)
    }

    pub fn struct_records(&self) -> impl Iterator<Item = (&String, &StructRecordType)> {
        self.struct_records.iter()
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
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ResolvedSpec {
    pub params: Vec<crate::types::Ty>,
    #[serde(default)]
    pub param_shapes: Vec<ResolvedTypeShape>,
    pub result: crate::types::Ty,
    #[serde(default)]
    pub result_shape: ResolvedTypeShape,
    /// `TypeVarId` is a `u32` newtype, which serde_json renders as a number —
    /// not a valid object key — so this map serializes as a sequence of
    /// `(TypeVarId, Ty)` entries.
    #[serde(with = "constraints_as_seq")]
    pub constraints: HashMap<crate::types::TypeVarId, crate::types::Ty>,
}

#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct ResolvedSpecSet {
    pub arrows: Vec<ResolvedSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedSpecMatch {
    pub params: Vec<crate::types::Ty>,
    pub result: crate::types::Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HigherOrderInvariantGroup {
    pub var: crate::types::TypeVarId,
    pub occurrences: Vec<InvariantOccurrence>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct StructuralCorrespondenceGroup {
    pub var: crate::types::TypeVarId,
    pub occurrences: Vec<StructuralOccurrence>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize, Default)]
pub struct ResolvedStructFieldShape {
    pub name: String,
    pub ty: ResolvedTypeShape,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize, Default)]
pub enum ResolvedTypeShape {
    #[default]
    Any,
    Never,
    Nil,
    Bool,
    Integer,
    Float,
    CPointer,
    Binary,
    Atom,
    Utf8,
    Pid,
    Ref,
    Var(crate::types::TypeVarId),
    AtomLit(String),
    IntLit(i64),
    FloatLit(u64),
    Named {
        name: String,
        args: Vec<ResolvedTypeShape>,
    },
    Resource(Box<ResolvedTypeShape>),
    List(Box<ResolvedTypeShape>),
    Tuple(Vec<ResolvedTypeShape>),
    Arrow {
        params: Vec<ResolvedTypeShape>,
        result: Box<ResolvedTypeShape>,
    },
    Union(Vec<ResolvedTypeShape>),
    StructRecord {
        module: ModuleName,
        fields: Vec<ResolvedStructFieldShape>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum InvariantOccurrence {
    Param(usize),
    Result,
    CallbackArg {
        param_index: usize,
        arg_index: usize,
    },
    CallbackResult {
        param_index: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub enum StructuralPathStep {
    NamedArg(usize),
    ResourceInner,
    ListElem,
    TupleElem(usize),
    ArrowParam(usize),
    ArrowResult,
    UnionMember(usize),
    StructField(String),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub enum StructuralOccurrence {
    Param {
        param_index: usize,
        path: Vec<StructuralPathStep>,
    },
    Result {
        path: Vec<StructuralPathStep>,
    },
    CallbackArg {
        param_index: usize,
        arg_index: usize,
        path: Vec<StructuralPathStep>,
    },
    CallbackResult {
        param_index: usize,
        path: Vec<StructuralPathStep>,
    },
}

impl ResolvedSpecSet {
    pub fn matching_arrows<T>(
        &self,
        t: &mut T,
        arg_tys: &[crate::types::Ty],
    ) -> Vec<ResolvedSpecMatch>
    where
        T: ClosureTypes<Ty = crate::types::Ty>,
    {
        self.arrows
            .iter()
            .filter_map(|spec| instantiate_matching_arrow(t, spec, arg_tys))
            .collect()
    }

    pub fn unique_matching_params<T>(
        &self,
        t: &mut T,
        arg_tys: &[crate::types::Ty],
    ) -> Option<Vec<crate::types::Ty>>
    where
        T: ClosureTypes<Ty = crate::types::Ty>,
    {
        match self.matching_arrows(t, arg_tys).as_slice() {
            [matched] => Some(matched.params.clone()),
            _ => None,
        }
    }

    #[allow(dead_code)]
    pub fn matching_result<T>(
        &self,
        t: &mut T,
        arg_tys: &[crate::types::Ty],
    ) -> Option<crate::types::Ty>
    where
        T: ClosureTypes<Ty = crate::types::Ty>,
    {
        let mut result = None;
        for matched in self.matching_arrows(t, arg_tys) {
            result = Some(match result {
                Some(prev) => t.union(prev, matched.result),
                None => matched.result,
            });
        }
        result
    }
}

impl ResolvedSpec {
    pub fn structural_correspondence_groups(&self) -> Vec<StructuralCorrespondenceGroup> {
        fn walk_shape(
            shape: &ResolvedTypeShape,
            path: &mut Vec<StructuralPathStep>,
            emit: &mut impl FnMut(crate::types::TypeVarId, Vec<StructuralPathStep>),
        ) {
            match shape {
                ResolvedTypeShape::Var(var) => emit(*var, path.clone()),
                ResolvedTypeShape::Named { args, .. } => {
                    for (idx, arg) in args.iter().enumerate() {
                        path.push(StructuralPathStep::NamedArg(idx));
                        walk_shape(arg, path, emit);
                        path.pop();
                    }
                }
                ResolvedTypeShape::Resource(inner) => {
                    path.push(StructuralPathStep::ResourceInner);
                    walk_shape(inner, path, emit);
                    path.pop();
                }
                ResolvedTypeShape::List(inner) => {
                    path.push(StructuralPathStep::ListElem);
                    walk_shape(inner, path, emit);
                    path.pop();
                }
                ResolvedTypeShape::Tuple(elems) | ResolvedTypeShape::Union(elems) => {
                    for (idx, elem) in elems.iter().enumerate() {
                        path.push(match shape {
                            ResolvedTypeShape::Tuple(_) => StructuralPathStep::TupleElem(idx),
                            ResolvedTypeShape::Union(_) => StructuralPathStep::UnionMember(idx),
                            _ => unreachable!(),
                        });
                        walk_shape(elem, path, emit);
                        path.pop();
                    }
                }
                ResolvedTypeShape::Arrow { params, result } => {
                    for (idx, param) in params.iter().enumerate() {
                        path.push(StructuralPathStep::ArrowParam(idx));
                        walk_shape(param, path, emit);
                        path.pop();
                    }
                    path.push(StructuralPathStep::ArrowResult);
                    walk_shape(result, path, emit);
                    path.pop();
                }
                ResolvedTypeShape::StructRecord { fields, .. } => {
                    for field in fields {
                        path.push(StructuralPathStep::StructField(field.name.clone()));
                        walk_shape(&field.ty, path, emit);
                        path.pop();
                    }
                }
                ResolvedTypeShape::Any
                | ResolvedTypeShape::Never
                | ResolvedTypeShape::Nil
                | ResolvedTypeShape::Bool
                | ResolvedTypeShape::Integer
                | ResolvedTypeShape::Float
                | ResolvedTypeShape::CPointer
                | ResolvedTypeShape::Binary
                | ResolvedTypeShape::Atom
                | ResolvedTypeShape::Utf8
                | ResolvedTypeShape::Pid
                | ResolvedTypeShape::Ref
                | ResolvedTypeShape::AtomLit(_)
                | ResolvedTypeShape::IntLit(_)
                | ResolvedTypeShape::FloatLit(_) => {}
            }
        }

        let mut groups: BTreeMap<crate::types::TypeVarId, BTreeSet<StructuralOccurrence>> =
            BTreeMap::new();
        let mut path = Vec::new();

        for (param_index, shape) in self.param_shapes.iter().enumerate() {
            match shape {
                ResolvedTypeShape::Arrow { params, result } => {
                    for (arg_index, arg) in params.iter().enumerate() {
                        walk_shape(arg, &mut path, &mut |var, shape_path| {
                            groups.entry(var).or_default().insert(
                                StructuralOccurrence::CallbackArg {
                                    param_index,
                                    arg_index,
                                    path: shape_path,
                                },
                            );
                        });
                    }
                    walk_shape(result, &mut path, &mut |var, shape_path| {
                        groups.entry(var).or_default().insert(
                            StructuralOccurrence::CallbackResult {
                                param_index,
                                path: shape_path,
                            },
                        );
                    });
                }
                _ => walk_shape(shape, &mut path, &mut |var, shape_path| {
                    groups
                        .entry(var)
                        .or_default()
                        .insert(StructuralOccurrence::Param {
                            param_index,
                            path: shape_path,
                        });
                }),
            }
        }

        walk_shape(&self.result_shape, &mut path, &mut |var, shape_path| {
            groups
                .entry(var)
                .or_default()
                .insert(StructuralOccurrence::Result { path: shape_path });
        });

        groups
            .into_iter()
            .filter_map(|(var, occurrences)| {
                (occurrences.len() > 1).then_some(StructuralCorrespondenceGroup {
                    var,
                    occurrences: occurrences.into_iter().collect(),
                })
            })
            .collect()
    }

    pub fn higher_order_invariant_groups<T>(&self, t: &mut T) -> Vec<HigherOrderInvariantGroup>
    where
        T: ClosureTypes<Ty = crate::types::Ty>,
    {
        let _ = t;
        self.structural_correspondence_groups()
            .into_iter()
            .filter_map(|group| {
                let projected = group
                    .occurrences
                    .iter()
                    .filter_map(|occ| match occ {
                        StructuralOccurrence::Param { param_index, path } if path.is_empty() => {
                            Some(InvariantOccurrence::Param(*param_index))
                        }
                        StructuralOccurrence::Result { path } if path.is_empty() => {
                            Some(InvariantOccurrence::Result)
                        }
                        StructuralOccurrence::CallbackArg {
                            param_index,
                            arg_index,
                            path,
                        } if path.is_empty() => Some(InvariantOccurrence::CallbackArg {
                            param_index: *param_index,
                            arg_index: *arg_index,
                        }),
                        StructuralOccurrence::CallbackResult { param_index, path }
                            if path.is_empty() =>
                        {
                            Some(InvariantOccurrence::CallbackResult {
                                param_index: *param_index,
                            })
                        }
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                let has_callback_result = projected
                    .iter()
                    .any(|occ| matches!(occ, InvariantOccurrence::CallbackResult { .. }));
                let has_outer = projected
                    .iter()
                    .any(|occ| matches!(occ, InvariantOccurrence::Param(_) | InvariantOccurrence::Result));
                (has_callback_result && has_outer).then_some(HigherOrderInvariantGroup {
                    var: group.var,
                    occurrences: projected,
                })
            })
            .collect()
    }
}

fn instantiate_matching_arrow<T>(
    t: &mut T,
    spec: &ResolvedSpec,
    arg_tys: &[crate::types::Ty],
) -> Option<ResolvedSpecMatch>
where
    T: ClosureTypes<Ty = crate::types::Ty>,
{
    match instantiate_scheme_match(t, &spec.params, &spec.result, &spec.constraints, arg_tys) {
        SchemeInstantiation::Known(SchemeMatch { params, result }) => {
            Some(ResolvedSpecMatch { params, result })
        }
        SchemeInstantiation::Underconstrained(_) | SchemeInstantiation::Invalid => None,
    }
}

/// (De)serialize `HashMap<TypeVarId, Ty>` as a `Vec<(TypeVarId, Ty)>` so the
/// numeric key survives serde_json (which forbids non-string object keys).
mod constraints_as_seq {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::HashMap;

    type Constraints = HashMap<crate::types::TypeVarId, crate::types::Ty>;

    pub fn serialize<S: Serializer>(map: &Constraints, s: S) -> Result<S::Ok, S::Error> {
        map.iter().collect::<Vec<_>>().serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Constraints, D::Error> {
        Ok(
            Vec::<(crate::types::TypeVarId, crate::types::Ty)>::deserialize(d)?
                .into_iter()
                .collect(),
        )
    }
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
#[cfg(test)]
pub use parser::parse_struct_record_type;

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

pub fn resolve_spec_decls<'a, T>(
    t: &mut T,
    decls: impl IntoIterator<Item = &'a crate::ast::SpecDecl>,
    env: &ModuleTypeEnv,
) -> Result<ResolvedSpecSet, TypeExprError>
where
    T: Types<Ty = crate::types::Ty>,
{
    let mut arrows = Vec::new();
    for decl in decls {
        arrows.push(resolve_spec_decl(t, decl, env)?);
    }
    Ok(ResolvedSpecSet { arrows })
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
