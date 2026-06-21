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
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::modules::identity::ModuleName;
use crate::source::Span;
use crate::type_expr::ResolvedSpecDecl;

use super::identity::{NotedTypeDecl, TypeName};
use super::namespace::Namespace;
use super::type_expr::{NominalKind, TypeExpr, TypeExprError, parse_type_expr};
use super::typedef::TypeDef;
use super::types::{Ty, TypeVarId};
use super::world::World;

/// An `@spec` resolved against its captured namespace: hard compiler2 types in
/// argument/result position plus the `when`-clause bounds.
#[derive(Debug, Clone)]
pub(crate) struct ResolvedSpec {
    pub(crate) params: Vec<Ty>,
    pub(crate) result: Ty,
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

    /// Resolves an `@spec` to hard types against the namespace captured where
    /// the spec appears. Free type variables are allocated first-seen and
    /// shared across every position and the `when`-clause bounds.
    pub(crate) fn resolve_spec(
        &mut self,
        namespace: Namespace,
        spec: &SpecDecl,
    ) -> Result<ResolvedSpec, TypeExprError> {
        let mut vars: HashMap<String, TypeVarId> = HashMap::new();
        let mut params = Vec::with_capacity(spec.param_body_tokens.len());
        for body in &spec.param_body_tokens {
            let expr = parse_type_expr(&body.0)?;
            let ty = self.resolve_ty(namespace, &expr, &mut vars)?;
            params.push(ty);
        }
        let result_expr = parse_type_expr(&spec.result_body_tokens.0)?;
        let result = self.resolve_ty(namespace, &result_expr, &mut vars)?;
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
        // fz-hwn.27.14 — address the whole spec scope at the binder. The
        // resolver's first-occurrence ids are raw material; a variable's
        // canonical identity is its STRUCTURAL ADDRESS (param i -> a{i}, result
        // -> r0, nested by path), assigned here in one whole-scope pass so two
        // alpha-equivalent specs intern byte-identical. Names and bounds re-key
        // through the env, never escaping un-addressed (addressing > encounter).
        let (arrow, env) = self.types_mut().address_arrow_with_env(&params, result);
        let params = self.types_mut().arrow_params(&arrow);
        let result = self
            .types_mut()
            .arrow_result(&arrow)
            .expect("an addressed spec arrow has a result slot");
        let mut sigma: HashMap<TypeVarId, Ty> = HashMap::with_capacity(env.len());
        for (&original, &address) in &env {
            let addressed_var = self.types_mut().type_var(address);
            sigma.insert(original, addressed_var);
        }
        let mut addressed_constraints = HashMap::with_capacity(constraints.len());
        for (var, bound) in constraints {
            let address = env.get(&var).copied().unwrap_or(var);
            let bound = self.types_mut().instantiate(&bound, &sigma);
            addressed_constraints.insert(address, bound);
        }
        Ok(ResolvedSpec {
            params,
            result,
            constraints: addressed_constraints,
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
        match expr {
            TypeExpr::Name { path, args } => self.resolve_name(namespace, path, args, vars),
            TypeExpr::List(inner) => {
                let elem = self.resolve_ty(namespace, inner, vars)?;
                Ok(self.types_mut().list(elem))
            }
            TypeExpr::EmptyList => Ok(self.types_mut().nil()),
            TypeExpr::Tuple(elems) => {
                let tys = self.resolve_each(namespace, elems, vars)?;
                Ok(self.types_mut().tuple(&tys))
            }
            TypeExpr::Arrow { params, result } => {
                let param_tys = self.resolve_each(namespace, params, vars)?;
                let result_ty = self.resolve_ty(namespace, result, vars)?;
                Ok(self.types_mut().arrow(&param_tys, result_ty))
            }
            TypeExpr::Union(elems) => {
                let tys = self.resolve_each(namespace, elems, vars)?;
                let mut tys = tys.into_iter();
                let mut acc = tys.next().expect("a parsed union has at least two members");
                for ty in tys {
                    acc = self.types_mut().union(acc, ty);
                }
                Ok(acc)
            }
            TypeExpr::StructRecord { module, fields } => {
                let module_name = ModuleName::from_segments(module.clone());
                let module_id = self
                    .lookup_module_path(namespace, &module_name.dotted())
                    .unwrap_or_else(|| self.reference_module(module_name.dotted()));
                let field_order = self.module_struct_fields(module_id).map(|fields| fields.to_vec());
                let any = self.types_mut().any();
                let mut by_name = HashMap::new();
                for (name, field) in fields {
                    let field_ty = self.resolve_ty(namespace, field, vars)?;
                    by_name.insert(name.clone(), field_ty);
                }
                let ordered_names =
                    field_order.unwrap_or_else(|| fields.iter().map(|(name, _)| name.clone()).collect());
                let ordered_fields = ordered_names
                    .iter()
                    .map(|name| by_name.get(name).copied().unwrap_or(any))
                    .collect::<Vec<_>>();
                Ok(self.struct_value_ty(&module_name.dotted(), &ordered_names, &ordered_fields))
            }
            TypeExpr::AtomLit(name) => Ok(self.types_mut().atom_lit(name)),
            // The lattice cannot express a numeric singleton (Elixir's
            // descr draws the same line): a literal in type position means
            // its kind, and says so once.
            TypeExpr::IntLit(value) => {
                self.warn_numeric_literal_type(&value.to_string());
                Ok(self.types_mut().int())
            }
            TypeExpr::FloatLit(bits) => {
                self.warn_numeric_literal_type(&f64::from_bits(*bits).to_string());
                Ok(self.types_mut().float())
            }
            TypeExpr::Wildcard => Ok(self.types_mut().any()),
            TypeExpr::Nil => Ok(self.types_mut().nil()),
            TypeExpr::Bool => Ok(self.types_mut().bool()),
        }
    }

    fn resolve_each(
        &mut self,
        namespace: Namespace,
        exprs: &[TypeExpr],
        vars: &mut HashMap<String, TypeVarId>,
    ) -> Result<Vec<Ty>, TypeExprError> {
        let mut tys = Vec::with_capacity(exprs.len());
        for expr in exprs {
            tys.push(self.resolve_ty(namespace, expr, vars)?);
        }
        Ok(tys)
    }

    fn resolve_name(
        &mut self,
        namespace: Namespace,
        path: &[String],
        args: &[TypeExpr],
        vars: &mut HashMap<String, TypeVarId>,
    ) -> Result<Ty, TypeExprError> {
        let arg_tys = self.resolve_each(namespace, args, vars)?;
        match self.classify_name(namespace, path, args.len(), vars) {
            NameClass::List => {
                if args.len() > 1 {
                    return Err(self.name_error(path, "list takes at most one type argument"));
                }
                let inner_ty = arg_tys.into_iter().next().unwrap_or_else(|| self.types_mut().any());
                Ok(self.types_mut().list(inner_ty))
            }
            NameClass::Resource => {
                let inner_ty = arg_tys.into_iter().next().unwrap_or_else(|| self.types_mut().any());
                Ok(self.types_mut().resource(inner_ty))
            }
            NameClass::Builtin(builtin) => {
                if !args.is_empty() {
                    return Err(self.name_error(path, "a builtin type takes no type arguments"));
                }
                Ok(self.builtin_ty(builtin))
            }
            NameClass::Named(type_name) => {
                let Some(def) = self.type_def(&type_name).cloned() else {
                    return Err(self.name_error(path, "type is referenced before it is resolved"));
                };
                Ok(def.instantiate(self.types_mut(), &arg_tys))
            }
            NameClass::Var(id) => {
                if !args.is_empty() {
                    return Err(self.name_error(path, "a type variable takes no type arguments"));
                }
                Ok(self.types_mut().type_var(id))
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
