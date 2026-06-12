//! Compiler2's in-house type-name resolver.
//!
//! Resolution is the second half of the in-house naming subsystem: the
//! [`super::type_expr`] parser turns syntax into a resolution-free [`TypeExpr`],
//! and this module turns that tree into a hard compiler2 [`Ty`] by classifying
//! each name *against the namespace captured where the declaration appeared* —
//! a builtin scalar, a declared type (read from the `TypeDefined` store), or a
//! free type variable. No `ModuleTypeEnv`, no re-lexing, no whole-program
//! assumption.
//!
//! The single interner rule is absolute: every type is minted through
//! [`World::types_mut`], the one compiler2 [`Types`](super::types::Types). There
//! is no throwaway interner and no legacy re-projection on this path.
//!
//! Two products: [`World::resolve_type_def`] resolves a `@type` body to a
//! [`TypeDef`] (for `DeriveTypeDef` to publish), and [`World::resolve_spec`]
//! resolves an `@spec` to a [`ResolvedSpec`] — hard types plus their structural
//! shapes — for the contract and dispatch seams to consume.

use std::collections::HashMap;

use crate::ast::{SpecDecl, TypeExprBody};
use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::modules::identity::ModuleName;
use crate::specs::{ResolvedStructFieldShape, ResolvedTypeShape};
use crate::type_expr::ResolvedSpecDecl;

use super::identity::{NotedTypeDecl, TypeName};
use super::namespace::Namespace;
use super::type_expr::{NominalKind, TypeExpr, TypeExprError, parse_type_expr};
use super::typedef::TypeDef;
use super::types::{Ty, TypeVarId};
use super::world::World;

/// An `@spec` resolved against its captured namespace: hard compiler2 types in
/// argument/result position, the parallel structural [`ResolvedTypeShape`]s
/// (variable-numbering shared with the types), and the `when`-clause bounds.
///
/// The shapes carry the same `TypeVarId`s as the types because both come from
/// one traversal threading a single variable map, so a `t` in argument position
/// and the `t` named in `when t: Bound` are the very same variable.
// Consumed by the contract/dispatch/extern cut-over (fz-rh2.12.4); landed one
// inch ahead and exercised by this inch's resolver tests.
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub(crate) struct ResolvedSpec {
    pub(crate) params: Vec<Ty>,
    pub(crate) param_shapes: Vec<ResolvedTypeShape>,
    pub(crate) result: Ty,
    pub(crate) result_shape: ResolvedTypeShape,
    pub(crate) constraints: HashMap<TypeVarId, Ty>,
}

/// How a name in type position classifies once measured against the namespace.
enum NameClass {
    /// The `list(T)` / `list()` builtin list constructor — Elixir-equivalent to
    /// `[T]` / `[any]`, producing the very same type and shape as the brackets.
    List,
    /// The `resource(T)` parametric opaque constructor.
    Resource,
    /// A builtin scalar — minted directly, never namespace-resolved.
    Builtin(Builtin),
    /// A declared type, read from the `TypeDefined` store at this identity.
    Named(TypeName),
    /// A free type variable, bound to this id for the rest of the declaration.
    Var(TypeVarId),
    /// A name that is neither builtin, declared, nor a single-letter variable.
    Unknown,
}

#[derive(Clone, Copy)]
enum Builtin {
    Nil,
    Bool,
    Integer,
    Float,
    CPointer,
    Binary,
    Atom,
    Any,
    Never,
    Utf8,
    Pid,
    Ref,
}

impl World<'_> {
    /// Resolves a noted `@type` declaration to its [`TypeDef`]. Formal
    /// parameters take variable ids `0..params.len()` in declaration order, so a
    /// parametric body resolves to a template a use site instantiates by
    /// substitution. A `refines` nominal brands the inner type under the type's
    /// qualified tag; an `opaque` declaration validates its body but publishes a
    /// pure nominal tag.
    pub(crate) fn resolve_type_def(&mut self, name: &TypeName, decl: &NotedTypeDecl) -> Result<TypeDef, TypeExprError> {
        let mut vars: HashMap<String, TypeVarId> = HashMap::new();
        let params: Vec<TypeVarId> = decl
            .params
            .iter()
            .enumerate()
            .map(|(index, param)| {
                let id = TypeVarId(index as u32);
                vars.insert(param.clone(), id);
                id
            })
            .collect();
        let inner = self.resolve_ty(decl.namespace, &decl.body.inner, &mut vars)?;
        let ty = match decl.body.kind {
            NominalKind::Plain => inner,
            NominalKind::Refines => {
                let tag = self.qualified_type_tag(name);
                self.types_mut().mint_brand(inner, &tag)
            }
            NominalKind::Opaque => {
                let tag = self.qualified_type_tag(name);
                self.types_mut().opaque_of(&tag)
            }
        };
        Ok(TypeDef { ty, params })
    }

    /// Resolves an `@spec` to hard types and parallel shapes against the
    /// namespace captured where the spec appears. Free type variables are
    /// allocated first-seen and shared across every position and the
    /// `when`-clause bounds.
    // Consumed by the contract/dispatch/extern cut-over (fz-rh2.12.4); landed one
    // inch ahead and exercised by this inch's resolver tests.
    #[allow(dead_code)]
    pub(crate) fn resolve_spec(
        &mut self,
        namespace: Namespace,
        spec: &SpecDecl,
    ) -> Result<ResolvedSpec, TypeExprError> {
        let mut vars: HashMap<String, TypeVarId> = HashMap::new();
        let mut params = Vec::with_capacity(spec.param_body_tokens.len());
        let mut param_shapes = Vec::with_capacity(spec.param_body_tokens.len());
        for body in &spec.param_body_tokens {
            let expr = parse_type_expr(&body.0)?;
            let (ty, shape) = self.resolve_pair(namespace, &expr, &mut vars)?;
            params.push(ty);
            param_shapes.push(shape);
        }
        let result_expr = parse_type_expr(&spec.result_body_tokens.0)?;
        let (result, result_shape) = self.resolve_pair(namespace, &result_expr, &mut vars)?;
        let mut constraints = HashMap::new();
        for (var_name, body) in &spec.constraints {
            let Some(&id) = vars.get(var_name) else {
                return Err(TypeExprError {
                    msg: format!("constraint references unknown type variable `{}`", var_name),
                    span: body.0.first().map(|token| token.span).unwrap_or(Span::DUMMY),
                });
            };
            let expr = parse_type_expr(&body.0)?;
            let bound = self.resolve_ty(namespace, &expr, &mut vars)?;
            constraints.insert(id, bound);
        }
        Ok(ResolvedSpec {
            params,
            param_shapes,
            result,
            result_shape,
            constraints,
        })
    }

    /// Resolves a source `TypeExprBody` directly against a captured namespace.
    /// Consumers that own one type-position (parameter annotations, extern wire
    /// hints after semantic resolution) use this instead of rebuilding a
    /// module-wide environment.
    pub(crate) fn resolve_type_expr_body(
        &mut self,
        namespace: Namespace,
        body: &TypeExprBody,
    ) -> Result<Ty, TypeExprError> {
        let expr = parse_type_expr(&body.0)?;
        let mut vars: HashMap<String, TypeVarId> = HashMap::new();
        self.resolve_ty(namespace, &expr, &mut vars)
    }

    /// Resolves one spec to the shared downstream contract shape:
    /// params/result/constraints over hard compiler2 `Ty`.
    pub(crate) fn resolve_spec_decl(
        &mut self,
        namespace: Namespace,
        spec: &SpecDecl,
    ) -> Result<ResolvedSpecDecl<Ty>, TypeExprError> {
        let resolved = self.resolve_spec(namespace, spec)?;
        Ok(ResolvedSpecDecl {
            params: resolved.params,
            result: resolved.result,
            constraints: resolved.constraints,
        })
    }

    fn resolve_ty(
        &mut self,
        namespace: Namespace,
        expr: &TypeExpr,
        vars: &mut HashMap<String, TypeVarId>,
    ) -> Result<Ty, TypeExprError> {
        Ok(self.resolve_pair(namespace, expr, vars)?.0)
    }

    /// The one traversal. Produces the hard type and its structural shape
    /// together so their variable numbering can never drift apart.
    fn resolve_pair(
        &mut self,
        namespace: Namespace,
        expr: &TypeExpr,
        vars: &mut HashMap<String, TypeVarId>,
    ) -> Result<(Ty, ResolvedTypeShape), TypeExprError> {
        match expr {
            TypeExpr::Name { path, args } => self.resolve_name(namespace, path, args, vars),
            TypeExpr::List(inner) => {
                let (elem, elem_shape) = self.resolve_pair(namespace, inner, vars)?;
                Ok((
                    self.types_mut().list(elem),
                    ResolvedTypeShape::List(Box::new(elem_shape)),
                ))
            }
            TypeExpr::EmptyList => Ok((self.types_mut().nil(), ResolvedTypeShape::Nil)),
            TypeExpr::Tuple(elems) => {
                let (tys, shapes) = self.resolve_each(namespace, elems, vars)?;
                Ok((self.types_mut().tuple(&tys), ResolvedTypeShape::Tuple(shapes)))
            }
            TypeExpr::Arrow { params, result } => {
                let (param_tys, param_shapes) = self.resolve_each(namespace, params, vars)?;
                let (result_ty, result_shape) = self.resolve_pair(namespace, result, vars)?;
                Ok((
                    self.types_mut().arrow(&param_tys, result_ty),
                    ResolvedTypeShape::Arrow {
                        params: param_shapes,
                        result: Box::new(result_shape),
                    },
                ))
            }
            TypeExpr::Union(elems) => {
                let (tys, shapes) = self.resolve_each(namespace, elems, vars)?;
                let mut tys = tys.into_iter();
                let mut acc = tys.next().expect("a parsed union has at least two members");
                for ty in tys {
                    acc = self.types_mut().union(acc, ty);
                }
                Ok((acc, ResolvedTypeShape::Union(shapes)))
            }
            TypeExpr::StructRecord { module, fields } => {
                let module_name = ModuleName::from_segments(module.clone());
                let module_id = self
                    .lookup_module_path(namespace, &module_name.dotted())
                    .unwrap_or_else(|| self.reference_module(module_name.dotted()));
                let field_order = self.module_struct_fields(module_id).map(|fields| fields.to_vec());
                let any = self.types_mut().any();
                let mut by_name = HashMap::new();
                let mut field_shapes = Vec::with_capacity(fields.len());
                for (name, field) in fields {
                    let (field_ty, field_shape) = self.resolve_pair(namespace, field, vars)?;
                    by_name.insert(name.clone(), field_ty);
                    field_shapes.push(ResolvedStructFieldShape {
                        name: name.clone(),
                        ty: field_shape,
                    });
                }
                let ordered_names =
                    field_order.unwrap_or_else(|| fields.iter().map(|(name, _)| name.clone()).collect());
                let ordered_fields = ordered_names
                    .iter()
                    .map(|name| by_name.get(name).copied().unwrap_or(any))
                    .collect::<Vec<_>>();
                let ty = self.struct_value_ty(&module_name.dotted(), &ordered_names, &ordered_fields);
                Ok((
                    ty,
                    ResolvedTypeShape::StructRecord {
                        module: module_name,
                        fields: field_shapes,
                    },
                ))
            }
            TypeExpr::AtomLit(name) => Ok((
                self.types_mut().atom_lit(name),
                ResolvedTypeShape::AtomLit(name.clone()),
            )),
            // The lattice cannot express a numeric singleton (Elixir's
            // descr draws the same line): a literal in type position means
            // its kind, and says so once.
            TypeExpr::IntLit(value) => {
                self.warn_numeric_literal_type(&value.to_string());
                Ok((self.types_mut().int(), ResolvedTypeShape::IntLit(*value)))
            }
            TypeExpr::FloatLit(bits) => {
                self.warn_numeric_literal_type(&f64::from_bits(*bits).to_string());
                Ok((self.types_mut().float(), ResolvedTypeShape::FloatLit(*bits)))
            }
            TypeExpr::Wildcard => Ok((self.types_mut().any(), ResolvedTypeShape::Any)),
            TypeExpr::Nil => Ok((self.types_mut().nil(), ResolvedTypeShape::Nil)),
            TypeExpr::Bool => Ok((self.types_mut().bool(), ResolvedTypeShape::Bool)),
        }
    }

    fn resolve_each(
        &mut self,
        namespace: Namespace,
        exprs: &[TypeExpr],
        vars: &mut HashMap<String, TypeVarId>,
    ) -> Result<(Vec<Ty>, Vec<ResolvedTypeShape>), TypeExprError> {
        let mut tys = Vec::with_capacity(exprs.len());
        let mut shapes = Vec::with_capacity(exprs.len());
        for expr in exprs {
            let (ty, shape) = self.resolve_pair(namespace, expr, vars)?;
            tys.push(ty);
            shapes.push(shape);
        }
        Ok((tys, shapes))
    }

    fn resolve_name(
        &mut self,
        namespace: Namespace,
        path: &[String],
        args: &[TypeExpr],
        vars: &mut HashMap<String, TypeVarId>,
    ) -> Result<(Ty, ResolvedTypeShape), TypeExprError> {
        let (arg_tys, arg_shapes) = self.resolve_each(namespace, args, vars)?;
        match self.classify_name(namespace, path, args.len(), vars) {
            NameClass::List => {
                if args.len() > 1 {
                    return Err(self.name_error(path, "list takes at most one type argument"));
                }
                let inner_ty = arg_tys.into_iter().next().unwrap_or_else(|| self.types_mut().any());
                let inner_shape = arg_shapes.into_iter().next().unwrap_or(ResolvedTypeShape::Any);
                Ok((
                    self.types_mut().list(inner_ty),
                    ResolvedTypeShape::List(Box::new(inner_shape)),
                ))
            }
            NameClass::Resource => {
                let inner_ty = arg_tys.into_iter().next().unwrap_or_else(|| self.types_mut().any());
                let inner_shape = arg_shapes.into_iter().next().unwrap_or(ResolvedTypeShape::Any);
                Ok((
                    self.types_mut().resource(inner_ty),
                    ResolvedTypeShape::Resource(Box::new(inner_shape)),
                ))
            }
            NameClass::Builtin(builtin) => {
                if !args.is_empty() {
                    return Err(self.name_error(path, "a builtin type takes no type arguments"));
                }
                Ok((self.builtin_ty(builtin), builtin_shape(builtin)))
            }
            NameClass::Named(type_name) => {
                let Some(def) = self.type_def(&type_name).cloned() else {
                    return Err(self.name_error(path, "type is referenced before it is resolved"));
                };
                let ty = def.instantiate(self.types_mut(), &arg_tys);
                Ok((
                    ty,
                    ResolvedTypeShape::Named {
                        name: path.join("."),
                        args: arg_shapes,
                    },
                ))
            }
            NameClass::Var(id) => {
                if !args.is_empty() {
                    return Err(self.name_error(path, "a type variable takes no type arguments"));
                }
                Ok((self.types_mut().type_var(id), ResolvedTypeShape::Var(id)))
            }
            NameClass::Unknown => Err(self.name_error(path, "unknown type name")),
        }
    }

    fn classify_name(
        &mut self,
        namespace: Namespace,
        path: &[String],
        arity: usize,
        vars: &mut HashMap<String, TypeVarId>,
    ) -> NameClass {
        if let [name] = path {
            if name == "list" {
                return NameClass::List;
            }
            if name == "resource" {
                return NameClass::Resource;
            }
            if let Some(builtin) = builtin_from_name(name) {
                return NameClass::Builtin(builtin);
            }
            if let Some(&id) = vars.get(name) {
                return NameClass::Var(id);
            }
        }
        if let Some(type_name) = self.reference_type(namespace, path, arity) {
            return NameClass::Named(type_name);
        }
        if let [name] = path
            && name.chars().count() == 1
        {
            let next = TypeVarId(vars.len() as u32);
            let id = *vars.entry(name.clone()).or_insert(next);
            return NameClass::Var(id);
        }
        NameClass::Unknown
    }

    fn warn_numeric_literal_type(&mut self, literal: &str) {
        self.emit_warning_once(Diagnostic::warning(
            codes::TYPE_NUMERIC_LITERAL_WIDENED,
            format!(
                "`{literal}` is not a type; a numeric literal in type position means its kind — use a pattern or a guard to filter values"
            ),
            Span::DUMMY,
        ));
    }

    fn builtin_ty(&mut self, builtin: Builtin) -> Ty {
        let types = self.types_mut();
        match builtin {
            Builtin::Nil => types.nil(),
            Builtin::Bool => types.bool(),
            Builtin::Integer => types.int(),
            Builtin::Float => types.float(),
            Builtin::CPointer => types.cpointer(),
            Builtin::Binary => types.str_t(),
            Builtin::Atom => types.atom(),
            Builtin::Any => types.any(),
            Builtin::Never => types.none(),
            Builtin::Utf8 => {
                let inner = types.str_t();
                types.mint_brand(inner, "utf8")
            }
            Builtin::Pid => types.opaque_of("pid"),
            Builtin::Ref => types.opaque_of("ref"),
        }
    }

    fn name_error(&self, path: &[String], msg: &str) -> TypeExprError {
        TypeExprError {
            msg: format!("{} `{}`", msg, path.join(".")),
            span: Span::DUMMY,
        }
    }
}

fn builtin_from_name(name: &str) -> Option<Builtin> {
    Some(match name {
        "nil" => Builtin::Nil,
        "bool" => Builtin::Bool,
        "integer" => Builtin::Integer,
        "float" => Builtin::Float,
        "cpointer" => Builtin::CPointer,
        "binary" => Builtin::Binary,
        "atom" => Builtin::Atom,
        "any" => Builtin::Any,
        "never" => Builtin::Never,
        "utf8" => Builtin::Utf8,
        "pid" => Builtin::Pid,
        "ref" => Builtin::Ref,
        _ => return None,
    })
}

fn builtin_shape(builtin: Builtin) -> ResolvedTypeShape {
    match builtin {
        Builtin::Nil => ResolvedTypeShape::Nil,
        Builtin::Bool => ResolvedTypeShape::Bool,
        Builtin::Integer => ResolvedTypeShape::Integer,
        Builtin::Float => ResolvedTypeShape::Float,
        Builtin::CPointer => ResolvedTypeShape::CPointer,
        Builtin::Binary => ResolvedTypeShape::Binary,
        Builtin::Atom => ResolvedTypeShape::Atom,
        Builtin::Any => ResolvedTypeShape::Any,
        Builtin::Never => ResolvedTypeShape::Never,
        Builtin::Utf8 => ResolvedTypeShape::Utf8,
        Builtin::Pid => ResolvedTypeShape::Pid,
        Builtin::Ref => ResolvedTypeShape::Ref,
    }
}
