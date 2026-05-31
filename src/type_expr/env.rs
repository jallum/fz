use super::*;

/// fz-ul4.31.4 — Lower a `SpecDecl`'s body tokens into concrete types
/// against the module's type env. Surfaces unknown-name errors from
/// `parse_type_expr` directly. Caller is responsible for arity / name
/// validation against the target fn (the parser already enforces this
/// at parse time).
pub fn resolve_spec_decl<T>(
    t: &mut T,
    decl: &crate::ast::SpecDecl,
    env: &ModuleTypeEnv,
) -> Result<ResolvedSpec, TypeExprError>
where
    T: Types<Ty = crate::types::Ty>,
{
    let mut vars: HashMap<String, crate::types::TypeVarId> = HashMap::new();
    let mut params = Vec::with_capacity(decl.param_body_tokens.len());
    let mut param_shapes = Vec::with_capacity(decl.param_body_tokens.len());
    for body in &decl.param_body_tokens {
        let (ty, _consumed) = super::parser::parse_type_expr_with_vars(t, &body.0, env, &mut vars)?;
        let (shape, _consumed) = super::parser::parse_type_shape_with_vars(&body.0, env, &mut vars)?;
        params.push(ty);
        param_shapes.push(shape);
    }
    let (result, _consumed) =
        super::parser::parse_type_expr_with_vars(t, &decl.result_body_tokens.0, env, &mut vars)?;
    let (result_shape, _consumed) =
        super::parser::parse_type_shape_with_vars(&decl.result_body_tokens.0, env, &mut vars)?;
    let mut constraints = HashMap::new();
    for (name, body) in &decl.constraints {
        let Some(id) = vars.get(name).copied() else {
            return Err(TypeExprError {
                msg: format!("constraint references unknown type variable `{}`", name),
                span: body
                    .0
                    .first()
                    .map(|tok| tok.span)
                    .unwrap_or(crate::diag::Span::DUMMY),
            });
        };
        let (bound, _consumed) = parse_type_expr(t, &body.0, env)?;
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

/// Best-effort per-position resolution of a spec's bodies: a body that fails to
/// resolve yields `None` for that position instead of failing the whole spec.
/// Free type variables are shared across positions, matching `resolve_spec_decl`.
/// Used by protocol callback-spec compatibility checking, where a domain-applied
/// position (`t(a)`) may not resolve yet while the result and other params still
/// can.
pub fn resolve_spec_decl_positions<T>(
    t: &mut T,
    decl: &crate::ast::SpecDecl,
    env: &ModuleTypeEnv,
) -> (Vec<Option<crate::types::Ty>>, Option<crate::types::Ty>)
where
    T: Types<Ty = crate::types::Ty>,
{
    let mut vars: HashMap<String, crate::types::TypeVarId> = HashMap::new();
    let params = decl
        .param_body_tokens
        .iter()
        .map(|body| {
            super::parser::parse_type_expr_with_vars(t, &body.0, env, &mut vars)
                .ok()
                .map(|(ty, _consumed)| ty)
        })
        .collect();
    let result =
        super::parser::parse_type_expr_with_vars(t, &decl.result_body_tokens.0, env, &mut vars)
            .ok()
            .map(|(ty, _consumed)| ty);
    (params, result)
}

/// fz-ul4.31.3 — Build a `ModuleTypeEnv` from a module's `@type`
/// attributes. Resolves each alias body via `parse_type_expr`, threading
/// a partial env that grows as aliases are resolved. Forward references
/// inside the same module are supported (the resolver does a fixed-point
/// pass); cycles are detected and reported.
///
/// `attrs` is expected to be a `ModuleDef.attrs` (or `Program`-level
/// equivalent). Non-TypeAlias attributes are ignored. Duplicate alias
/// names within `attrs` are an error.
///
/// Equivalent to `build_module_type_env_for_with_base(attrs, "", empty)` —
/// used when the module path is not available (top-level, unit tests).
/// Opaque names declared via the empty path are unqualified, which means
/// they have no module owner for visibility purposes (see fz-swt.6).
#[cfg(test)]
pub fn build_module_type_env<T>(
    t: &mut T,
    attrs: &[crate::ast::Attribute],
) -> Result<ModuleTypeEnv, TypeExprError>
where
    T: Types<Ty = crate::types::Ty>,
{
    build_module_type_env_for_with_base(t, attrs, "", &ModuleTypeEnv::new())
        .map(|(env, _o, _b)| env)
}

/// fz-swt.6 — like `build_module_type_env`, but threads the enclosing
/// module's qualified path so opaque-type declarations record their
/// declaring module. The opaque tag in the resulting type is
/// `format!("{module_path}::{alias}")` when `module_path` is non-empty,
/// and just `alias` otherwise.
///
/// Visibility gating consults the opaque singleton query /
/// `crate::ir_planner::check_opaque_visibility` to compare the declaring
/// module against the using module.
pub fn build_module_type_env_for_with_base<T>(
    t: &mut T,
    attrs: &[crate::ast::Attribute],
    module_path: &str,
    base_env: &ModuleTypeEnv,
) -> Result<(ModuleTypeEnv, OpaqueInnerTypes, BrandInnerTypes), TypeExprError>
where
    T: Types<Ty = crate::types::Ty>,
{
    use crate::ast::Attribute;
    let mut pending: HashMap<String, &crate::ast::TypeAliasDecl> = HashMap::new();
    let mut order: Vec<String> = Vec::new();
    let mut seen: HashMap<(String, usize), crate::diag::Span> = HashMap::new();
    let mut param_aliases = Vec::new();
    for a in attrs {
        if let Attribute::TypeAlias(decl) = a {
            let key = (decl.name.clone(), decl.params.len());
            if seen.insert(key.clone(), decl.name_span).is_some() {
                return Err(TypeExprError {
                    msg: format!(
                        "duplicate @type alias `{}/{}`",
                        decl.name,
                        decl.params.len()
                    ),
                    span: decl.name_span,
                });
            }
            validate_type_alias_params(decl)?;
            if decl.params.is_empty() {
                order.push(decl.name.clone());
                pending.insert(decl.name.clone(), decl);
            } else {
                param_aliases.push(decl);
            }
        }
    }
    if pending.is_empty() && param_aliases.is_empty() {
        return Ok((
            base_env.clone(),
            OpaqueInnerTypes::new(),
            BrandInnerTypes::new(),
        ));
    }
    let mut env: ModuleTypeEnv = base_env.clone();
    let mut resolved: std::collections::HashSet<String> = std::collections::HashSet::new();
    for decl in param_aliases {
        env.insert_param_alias(
            decl.name.clone(),
            ParameterizedTypeAlias {
                params: decl.params.clone(),
                body_tokens: decl.body_tokens.clone(),
                span: decl.span,
            },
        );
    }
    // fz-swt.8 — Side map: qualified opaque tag → inner T parsed from
    // the body following `opaque`. Populated alongside `env` so the
    // planner's `.value` lowering can look up T without re-parsing.
    let mut opaque_inners: OpaqueInnerTypes = OpaqueInnerTypes::new();
    // fz-axu.3 (K2) — parallel side map: qualified brand tag → inner T
    // parsed from the body following `refines`. Consumed by K4's
    // is_subtype rule and K5 erasure.
    let mut brand_inners: BrandInnerTypes = BrandInnerTypes::new();
    // Fixed-point resolve: keep walking until no progress.
    loop {
        let mut progressed = false;
        for name in &order {
            if resolved.contains(name) {
                continue;
            }
            let decl = pending[name];
            // `@type Foo :: opaque T` — purely nominal; create an opaque
            // type keyed by the (module-qualified) alias name. The
            // underlying type T is not stored in the type (opaque types
            // are nominal, not structural), but we still parse it to
            // validate the body and to allow forms like `resource(T)`.
            let is_opaque = decl
                .body_tokens
                .0
                .first()
                .map(|t| matches!(&t.tok, Tok::Ident(n) if n == "opaque"))
                .unwrap_or(false);
            // fz-axu.3 (K2) — `@type B :: refines T` declares a brand on
            // top of an existing structural type T. Mirrors the opaque
            // branch below but populates `brand_inners` instead.
            let is_refines = decl
                .body_tokens
                .0
                .first()
                .map(|t| matches!(&t.tok, Tok::Ident(n) if n == "refines"))
                .unwrap_or(false);
            let is_struct_record = decl
                .body_tokens
                .0
                .first()
                .map(|t| matches!(t.tok, Tok::Percent))
                .unwrap_or(false);
            if is_struct_record {
                match super::parser::parse_struct_record_type(t, &decl.body_tokens.0, &env) {
                    Ok((record, ty, consumed)) if consumed == decl.body_tokens.0.len() => {
                        env.insert(name.clone(), ty);
                        env.insert_struct_record(name.clone(), record);
                        resolved.insert(name.clone());
                        progressed = true;
                        continue;
                    }
                    Ok((_record, _ty, _consumed)) => {
                        return Err(TypeExprError {
                            msg: format!(
                                "unexpected trailing tokens in struct record type alias `{}`",
                                name
                            ),
                            span: decl.span,
                        });
                    }
                    Err(_) => {
                        continue;
                    }
                }
            }
            if is_refines {
                let body_after_refines = &decl.body_tokens.0[1..];
                if body_after_refines.is_empty() {
                    return Err(TypeExprError {
                        msg: format!("`@type {} :: refines T` requires an inner type T", name),
                        span: decl.span,
                    });
                }
                let inner = match parse_type_expr(t, body_after_refines, &env) {
                    Ok((ty, _)) => ty,
                    Err(_) => {
                        // Body isn't resolvable yet (forward ref); retry.
                        continue;
                    }
                };
                let qualified = qualify_opaque_name(module_path, name);
                let brand_ty = t.brand_of(&qualified);
                env.insert(name.clone(), brand_ty);
                resolved.insert(name.clone());
                brand_inners.insert(qualified, inner);
                progressed = true;
                continue;
            }
            if is_opaque {
                // Parse the body after `opaque` and record T in the
                // side map so the `.value` accessor (fz-swt.8) can
                // type the access as T. Failure to parse defers (like
                // the non-opaque branch) so forward references inside
                // `opaque ...` still resolve.
                //
                // Special case: `opaque resource(T)` is the standard
                // shape for refcounted resources (fz-swt). The body
                // would otherwise resolve to the unqualified built-in
                // opaque `Descr::opaque_of("resource")` — which
                // discards T. We peel the `resource(...)` layer here
                // so `opaque_inners` records the user's actual T (the
                // payload's type), not the resource wrapper itself.
                let body_after_opaque = &decl.body_tokens.0[1..];
                let inner = if body_after_opaque.is_empty() {
                    // `opaque` with no body — no inner type to record.
                    None
                } else if starts_with_resource_constructor(body_after_opaque) {
                    // Reparse just the `(T)` payload — `parse_resource`
                    // throws T away and returns the wrapper tag.
                    match parse_resource_payload_type(t, body_after_opaque, &env) {
                        Ok(ty) => Some(ty),
                        Err(_) => continue,
                    }
                } else {
                    match parse_type_expr(t, body_after_opaque, &env) {
                        Ok((ty, _)) => Some(ty),
                        Err(_) => {
                            // Body isn't valid yet (likely a forward
                            // reference); try again in the next fixed-
                            // point iteration. The post-loop unresolved-
                            // handler will surface the real error if it
                            // never resolves.
                            continue;
                        }
                    }
                };
                let qualified = qualify_opaque_name(module_path, name);
                let opaque_ty = t.opaque_of(&qualified);
                env.insert(name.clone(), opaque_ty);
                resolved.insert(name.clone());
                if let Some(ty) = inner {
                    opaque_inners.insert(qualified, ty);
                }
                progressed = true;
                continue;
            }
            match parse_type_expr(t, &decl.body_tokens.0, &env) {
                Ok((ty, _consumed)) => {
                    env.insert(name.clone(), ty);
                    resolved.insert(name.clone());
                    progressed = true;
                }
                Err(_) => {
                    // Body references a name not yet in env. Try again
                    // next iteration after other aliases resolve.
                }
            }
        }
        if !progressed {
            break;
        }
    }
    // Anything still pending is a cycle or references an unknown name.
    // Re-parse one unresolved body to surface the underlying error.
    if resolved.len() < pending.len() {
        for name in &order {
            if resolved.contains(name) {
                continue;
            }
            let decl = pending[name];
            // Distinguish cycle from unknown-name by checking whether
            // the body references another unresolved alias.
            let body_refs = referenced_user_type_names(&decl.body_tokens.0);
            let mut cycle_partner: Option<&str> = None;
            for r in &body_refs {
                if pending.contains_key(r) && !resolved.contains(r) {
                    cycle_partner = Some(r.as_str());
                    break;
                }
            }
            if let Some(partner) = cycle_partner {
                return Err(TypeExprError {
                    msg: format!(
                        "type-alias cycle: `{}` and `{}` depend on each other",
                        name, partner
                    ),
                    span: decl.span,
                });
            }
            // No cycle partner — surface the original parse error.
            match parse_type_expr(t, &decl.body_tokens.0, &env) {
                Ok(_) => unreachable!("env did not grow; this should not parse OK"),
                Err(e) => return Err(e),
            }
        }
    }
    validate_param_aliases(t, &env)?;
    Ok((env, opaque_inners, brand_inners))
}

fn validate_type_alias_params(decl: &crate::ast::TypeAliasDecl) -> Result<(), TypeExprError> {
    let mut seen = std::collections::HashSet::new();
    for param in &decl.params {
        if is_reserved_type_name(param) {
            return Err(TypeExprError {
                msg: format!("type parameter `{}` uses a reserved type name", param),
                span: decl.span,
            });
        }
        if !seen.insert(param) {
            return Err(TypeExprError {
                msg: format!("duplicate type parameter `{}`", param),
                span: decl.span,
            });
        }
    }
    Ok(())
}

fn validate_param_aliases<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &ModuleTypeEnv,
) -> Result<(), TypeExprError> {
    for ((name, arity), alias) in env.param_aliases() {
        let mut local = env.clone();
        for (idx, param) in alias.params.iter().enumerate() {
            local.insert(
                param.clone(),
                t.type_var(crate::types::TypeVarId(idx as u32)),
            );
        }
        let stack = vec![(name.clone(), *arity)];
        let (.., consumed) = super::parser::parse_type_expr_with_stack(
            t,
            &alias.body_tokens.0,
            &local,
            None,
            stack,
        )?;
        if consumed != alias.body_tokens.0.len() {
            return Err(TypeExprError {
                msg: "unexpected trailing tokens in parameterized type alias body".to_string(),
                span: alias
                    .body_tokens
                    .0
                    .get(consumed)
                    .map(|tok| tok.span)
                    .unwrap_or(alias.span),
            });
        }
    }
    Ok(())
}

/// fz-swt.6 — build the module-qualified opaque tag stored on a
/// the opaque type token. When `module_path` is empty, the result is
/// just `alias` (top-level / runtime-prelude opaques have no module
/// owner). Otherwise the tag has the form `"Mod.Path::alias"`. The `::`
/// separator is chosen so it can't collide with module-path `.`
/// segments or with parametric forms like `resource<integer>`.
pub fn qualify_opaque_name(module_path: &str, alias: &str) -> String {
    if module_path.is_empty() {
        alias.to_string()
    } else {
        format!("{}::{}", module_path, alias)
    }
}

/// fz-swt.8 — recognise the literal `resource(...)` body shape so we
/// can extract the payload type T rather than the wrapper opaque tag.
/// Pure tokenwise match; semantic resolution still goes through
/// `parse_resource_payload_type` below.
fn starts_with_resource_constructor(toks: &[crate::parser::lexer::Token]) -> bool {
    use crate::parser::lexer::Tok;
    matches!(toks.first().map(|t| &t.tok), Some(Tok::Ident(n)) if n == "resource")
        && matches!(toks.get(1).map(|t| &t.tok), Some(Tok::LParen))
        && toks
            .last()
            .map(|t| matches!(&t.tok, Tok::RParen))
            .unwrap_or(false)
}

/// fz-swt.8 — parse the `(T)` payload from a `resource(T)` body.
/// Returns T directly, *not* the wrapper opaque tag. Used to populate
/// the per-program `opaque_inners` side map so the planner's `.value`
/// accessor sees the user's intended payload type rather than the
/// unqualified built-in `"resource"` opaque.
fn parse_resource_payload_type<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    toks: &[crate::parser::lexer::Token],
    env: &ModuleTypeEnv,
) -> Result<T::Ty, TypeExprError> {
    // Drop the leading `resource (` and the trailing `)`. Caller has
    // already verified the shape via `starts_with_resource_constructor`, so the
    // slice arithmetic is safe.
    debug_assert!(starts_with_resource_constructor(toks));
    let inner_toks = &toks[2..toks.len() - 1];
    let (ty, consumed) = parse_type_expr(t, inner_toks, env)?;
    if consumed != inner_toks.len() {
        return Err(TypeExprError {
            msg: "unexpected trailing tokens in resource(T)".to_string(),
            span: inner_toks
                .get(consumed)
                .map(|tok| tok.span)
                .unwrap_or(crate::diag::Span::DUMMY),
        });
    }
    Ok(ty)
}

/// fz-swt.6 — invert `qualify_opaque_name`: extract the declaring
/// module path from a qualified opaque tag. Returns `None` for
/// unqualified built-in opaques (`"resource"`) — they have no owner
/// and are visible from every module.
pub fn opaque_owner_module(qualified: &str) -> Option<&str> {
    qualified.find("::").map(|i| &qualified[..i])
}

/// Scan `tokens` and return the user-visible names referenced (any
/// Ident / Upper that isn't a built-in scalar). Used by
/// `build_module_type_env` to detect cycles vs unknown-name errors.
fn referenced_user_type_names(tokens: &[crate::parser::lexer::Token]) -> Vec<String> {
    use crate::parser::lexer::Tok;
    tokens
        .iter()
        .filter_map(|t| match &t.tok {
            Tok::Ident(n) | Tok::Upper(n) if !is_reserved_type_name(n) => Some(n.clone()),
            _ => None,
        })
        .collect()
}

fn is_reserved_type_name(name: &str) -> bool {
    matches!(
        name,
        "nil"
            | "bool"
            | "integer"
            | "float"
            | "binary"
            | "cpointer"
            | "atom"
            | "any"
            | "never"
            | "opaque"
            | "refines"
            | "resource"
            | super::BUILTIN_UTF8
            | super::BUILTIN_PID
            | super::BUILTIN_REF
    )
}
