//! fz-ul4.31.1 — Type-expression parser.
//!
//! Parses a fragment of fz type syntax into a `Descr` from the
//! set-theoretic lattice in `crate::types`. Used (in later .31
//! children) by `@spec` and `@type` attribute bodies. Standalone and
//! pure: takes a token slice + a `ModuleTypeEnv` (name → Descr) for
//! named-reference resolution; produces a `Descr` and the count of
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
//! atom_form  = SCALAR_NAME | ':' ATOM | INT_LITERAL | FLOAT_LITERAL | '_' | NAMED_REF
//!
//! SCALAR_NAME ∈ { nil, bool, integer, float, binary, atom, any }
//! NAMED_REF   = identifier resolved against the module's type env
//! ```
//!
//! `'|'` binds looser than primary forms; `'(A, B) -> R'` is one
//! primary (the arrow itself). `[T]` is a list of T (not a postfix
//! operator). `{T, U}` is a tuple. `:foo` is the singleton atom.
//! Bare `42` and `2.5` are singleton literals.

#![allow(dead_code)] // fz-ul4.31.4 wires this into the parser; tests
// exercise the API directly until then.

use std::collections::HashMap;

use crate::diag::Span;
use crate::lexer::{Tok, Token};
use crate::types_seam::Types;

/// Module-level type environment: name → declared Descr. Populated by
/// `@type name :: <expr>` declarations in .31.3.
pub type ModuleTypeEnv = HashMap<String, crate::types_seam::Ty>;

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
    pub params: Vec<crate::types_seam::Ty>,
    pub result: crate::types_seam::Ty,
}

/// fz-ul4.31.4 — Lower a `SpecDecl`'s body tokens into concrete Descrs
/// against the module's type env. Surfaces unknown-name errors from
/// `parse_type_expr` directly. Caller is responsible for arity / name
/// validation against the target fn (the parser already enforces this
/// at parse time).
pub fn resolve_spec_decl<T: Types>(
    t: &mut T,
    decl: &crate::ast::SpecDecl,
    env: &ModuleTypeEnv,
) -> Result<ResolvedSpec, TypeExprError> {
    let mut params = Vec::with_capacity(decl.param_body_tokens.len());
    for body in &decl.param_body_tokens {
        let (ty, _consumed) = parse_type_expr(t, &body.0, env)?;
        // ResolvedSpec stores concrete Ty (Program-attached, non-
        // generic); bridge T::Ty → Ty via Descr.
        params.push(crate::types_seam::Ty::from_descr(t.to_descr(&ty)));
    }
    let (result, _consumed) = parse_type_expr(t, &decl.result_body_tokens.0, env)?;
    let result = crate::types_seam::Ty::from_descr(t.to_descr(&result));
    Ok(ResolvedSpec { params, result })
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
/// Equivalent to `build_module_type_env_for(attrs, "")` — used when the
/// module path is not available (top-level, runtime prelude, unit tests).
/// Opaque names declared via the empty path are unqualified, which means
/// they have no module owner for visibility purposes (see fz-swt.6).
pub fn build_module_type_env<T: Types>(
    t: &mut T,
    attrs: &[crate::ast::Attribute],
) -> Result<ModuleTypeEnv, TypeExprError> {
    build_module_type_env_for(t, attrs, "").map(|(env, _o, _b)| env)
}

/// fz-swt.8 — Inner-type map for opaque aliases declared in one
/// module. Keyed by the qualified opaque tag (matches the tag stored
/// on `Descr::opaque_of(...)`); value is the parsed body following
/// the `opaque` keyword — i.e., the inner type `T` for
/// `@type t :: opaque T` (or `opaque resource(T)`, etc.).
///
/// The typer consumes this map at `Prim::MapGet(handle, :value)` sites
/// to type `handle.value` as `T` instead of falling back to the generic
/// map-lookup result. Visibility gating already lives in
/// `crate::typer::check_opaque_visibility`; the inner-type map is the
/// payload the gate guards.
pub type OpaqueInnerTypes = HashMap<String, crate::types_seam::Ty>;

/// fz-axu.3 (K2) — Inner-type map for `refines` brand aliases
/// declared in one module. Keyed by the qualified brand tag (matches
/// the tag stored on `Descr::brand_of(...)`); value is the parsed body
/// following the `refines` keyword — i.e., the inner type `T` for
/// `@type B :: refines T`.
///
/// Distinct from `OpaqueInnerTypes` because the K4 is_subtype rule
/// treats brands as a proper subset of their inner, whereas opaques
/// are nominally disjoint from theirs. K2 only collects the map;
/// downstream tickets (K3 mint, K4 lattice rule, K5 erasure) read it.
pub type BrandInnerTypes = HashMap<String, crate::types_seam::Ty>;

/// fz-swt.6 — like `build_module_type_env`, but threads the enclosing
/// module's qualified path so opaque-type declarations record their
/// declaring module. The opaque tag in the resulting `Descr` is
/// `format!("{module_path}::{alias}")` when `module_path` is non-empty,
/// and just `alias` otherwise.
///
/// Visibility gating consults `Descr::opaque_singleton()` /
/// `crate::typer::check_opaque_visibility` to compare the declaring
/// module against the using module.
pub fn build_module_type_env_for<T: Types>(
    t: &mut T,
    attrs: &[crate::ast::Attribute],
    module_path: &str,
) -> Result<(ModuleTypeEnv, OpaqueInnerTypes, BrandInnerTypes), TypeExprError> {
    use crate::ast::Attribute;
    // Collect aliases keyed by name; reject duplicates.
    let mut pending: HashMap<String, &crate::ast::TypeAliasDecl> = HashMap::new();
    let mut order: Vec<String> = Vec::new();
    for a in attrs {
        if let Attribute::TypeAlias(decl) = a {
            if pending.contains_key(&decl.name) {
                return Err(TypeExprError {
                    msg: format!("duplicate @type alias `{}`", decl.name),
                    span: decl.name_span,
                });
            }
            order.push(decl.name.clone());
            pending.insert(decl.name.clone(), decl);
        }
    }
    if pending.is_empty() {
        return Ok((
            ModuleTypeEnv::new(),
            OpaqueInnerTypes::new(),
            BrandInnerTypes::new(),
        ));
    }
    let mut env: ModuleTypeEnv = ModuleTypeEnv::new();
    // fz-swt.8 — Side map: qualified opaque tag → inner T parsed from
    // the body following `opaque`. Populated alongside `env` so the
    // typer's `.value` lowering can look up T without re-parsing.
    let mut opaque_inners: OpaqueInnerTypes = OpaqueInnerTypes::new();
    // fz-axu.3 (K2) — parallel side map: qualified brand tag → inner T
    // parsed from the body following `refines`. Consumed by K4's
    // is_subtype rule and K5 erasure.
    let mut brand_inners: BrandInnerTypes = BrandInnerTypes::new();
    // Fixed-point resolve: keep walking until no progress.
    loop {
        let mut progressed = false;
        for name in &order {
            if env.contains_key(name) {
                continue;
            }
            let decl = pending[name];
            // `@type Foo :: opaque T` — purely nominal; create an opaque
            // Descr keyed by the (module-qualified) alias name. The
            // underlying type T is not stored in the Descr (opaque types
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
                env.insert(
                    name.clone(),
                    crate::types_seam::Ty::from_descr(t.to_descr(&brand_ty)),
                );
                brand_inners.insert(
                    qualified,
                    crate::types_seam::Ty::from_descr(t.to_descr(&inner)),
                );
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
                } else if is_resource_ctor_body(body_after_opaque) {
                    // Reparse just the `(T)` payload — `parse_resource`
                    // throws T away and returns the wrapper tag.
                    match parse_resource_inner(t, body_after_opaque, &env) {
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
                env.insert(
                    name.clone(),
                    crate::types_seam::Ty::from_descr(t.to_descr(&opaque_ty)),
                );
                if let Some(ty) = inner {
                    opaque_inners.insert(
                        qualified,
                        crate::types_seam::Ty::from_descr(t.to_descr(&ty)),
                    );
                }
                progressed = true;
                continue;
            }
            match parse_type_expr(t, &decl.body_tokens.0, &env) {
                Ok((ty, _consumed)) => {
                    env.insert(
                        name.clone(),
                        crate::types_seam::Ty::from_descr(t.to_descr(&ty)),
                    );
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
    if env.len() < pending.len() {
        for name in &order {
            if env.contains_key(name) {
                continue;
            }
            let decl = pending[name];
            // Distinguish cycle from unknown-name by checking whether
            // the body references another unresolved alias.
            let body_refs = referenced_names(&decl.body_tokens.0);
            let mut cycle_partner: Option<&str> = None;
            for r in &body_refs {
                if pending.contains_key(r) && !env.contains_key(r) {
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
    Ok((env, opaque_inners, brand_inners))
}

/// fz-swt.6 — build the module-qualified opaque tag stored on a
/// `Descr::opaque_of(...)`. When `module_path` is empty, the result is
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
/// `parse_resource_inner` below.
fn is_resource_ctor_body(toks: &[crate::lexer::Token]) -> bool {
    use crate::lexer::Tok;
    matches!(toks.first().map(|t| &t.tok), Some(Tok::Ident(n)) if n == "resource")
        && matches!(toks.get(1).map(|t| &t.tok), Some(Tok::LParen))
        && toks
            .last()
            .map(|t| matches!(&t.tok, Tok::RParen))
            .unwrap_or(false)
}

/// fz-swt.8 — parse the `(T)` payload from a `resource(T)` body.
/// Returns T directly, *not* the wrapper opaque tag. Used to populate
/// the per-program `opaque_inners` side map so the typer's `.value`
/// accessor sees the user's intended payload type rather than the
/// unqualified built-in `"resource"` opaque.
fn parse_resource_inner<T: crate::types_seam::Types>(
    t: &mut T,
    toks: &[crate::lexer::Token],
    env: &ModuleTypeEnv,
) -> Result<T::Ty, TypeExprError> {
    // Drop the leading `resource (` and the trailing `)`. Caller has
    // already verified the shape via `is_resource_ctor_body`, so the
    // slice arithmetic is safe.
    debug_assert!(is_resource_ctor_body(toks));
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
fn referenced_names(tokens: &[crate::lexer::Token]) -> Vec<String> {
    use crate::lexer::Tok;
    tokens
        .iter()
        .filter_map(|t| match &t.tok {
            Tok::Ident(n) | Tok::Upper(n) => match n.as_str() {
                "nil" | "bool" | "integer" | "float" | "binary" | "atom" | "any" | "never"
                | "opaque" | "refines" | "vector" | "u8" | "bit" | "resource" => None,
                _ => Some(n.clone()),
            },
            _ => None,
        })
        .collect()
}

/// Parse one type expression from `tokens` starting at index 0.
/// Returns the lowered `Descr` and the number of tokens consumed.
///
/// `env` resolves named references (e.g. `id` → declared alias).
/// Names not in `env` and not one of the built-in scalars produce an
/// unknown-name error.
pub fn parse_type_expr<T: crate::types_seam::Types>(
    t: &mut T,
    tokens: &[Token],
    env: &ModuleTypeEnv,
) -> Result<(T::Ty, usize), TypeExprError> {
    let mut p = TypeExprParser {
        t,
        tokens,
        pos: 0,
        env,
    };
    let ty = p.parse_union()?;
    Ok((ty, p.pos))
}

struct TypeExprParser<'a, T: crate::types_seam::Types> {
    t: &'a mut T,
    tokens: &'a [Token],
    pos: usize,
    env: &'a ModuleTypeEnv,
}

impl<'a, T: crate::types_seam::Types> TypeExprParser<'a, T> {
    fn peek(&self) -> &Tok {
        self.tokens
            .get(self.pos)
            .map(|t| &t.tok)
            .unwrap_or(&Tok::Eof)
    }

    fn peek_span(&self) -> Span {
        self.tokens
            .get(self.pos)
            .or_else(|| self.tokens.last())
            .map(|t| t.span)
            .unwrap_or(Span::DUMMY)
    }

    fn bump(&mut self) {
        self.pos += 1;
    }

    fn err(&self, msg: impl Into<String>) -> TypeExprError {
        TypeExprError {
            msg: msg.into(),
            span: self.peek_span(),
        }
    }

    fn expect(&mut self, want: &Tok, ctx: &str) -> Result<(), TypeExprError> {
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(want) {
            self.bump();
            Ok(())
        } else {
            Err(self.err(format!("expected {}, got {}", ctx, self.peek())))
        }
    }

    fn parse_union(&mut self) -> Result<T::Ty, TypeExprError> {
        let mut acc = self.parse_primary()?;
        while matches!(self.peek(), Tok::Bar) {
            self.bump();
            let rhs = self.parse_primary()?;
            acc = self.t.union(acc, rhs);
        }
        Ok(acc)
    }

    fn parse_primary(&mut self) -> Result<T::Ty, TypeExprError> {
        match self.peek().clone() {
            Tok::LBrack => self.parse_list(),
            Tok::LBrace => self.parse_tuple(),
            Tok::LParen => self.parse_paren_or_arrow(),
            Tok::Underscore => {
                self.bump();
                Ok(self.t.any())
            }
            Tok::Atom(name) => {
                self.bump();
                Ok(self.t.atom_lit(&name))
            }
            Tok::Int(n) => {
                self.bump();
                Ok(self.t.int_lit(n))
            }
            Tok::Float(f) => {
                self.bump();
                Ok(self.t.float_lit(f))
            }
            Tok::Nil => {
                self.bump();
                Ok(self.t.nil())
            }
            Tok::True => {
                self.bump();
                // bool singleton: bool intersected with literal `true` —
                // fz's basic-bits model has no per-literal bool; the
                // closest user-facing meaning is "the bool type".
                Ok(self.t.bool())
            }
            Tok::False => {
                self.bump();
                Ok(self.t.bool())
            }
            Tok::Ident(name) => {
                self.bump();
                if name == "vector" {
                    self.parse_vector()
                } else if name == "resource" {
                    self.parse_resource()
                } else {
                    self.lookup_named(&name)
                }
            }
            Tok::Upper(name) => {
                self.bump();
                self.lookup_named(&name)
            }
            other => Err(self.err(format!("expected a type expression, got {}", other))),
        }
    }

    fn parse_vector(&mut self) -> Result<T::Ty, TypeExprError> {
        // `vector` already consumed. Parse `(elem_type)`.
        self.expect(&Tok::LParen, "`(` after `vector`")?;
        let elem_name = match self.peek().clone() {
            Tok::Ident(n) => {
                self.bump();
                n
            }
            other => {
                return Err(self.err(format!("expected element type in vector(T), got {}", other)));
            }
        };
        self.expect(&Tok::RParen, "`)` after vector element type")?;
        match elem_name.as_str() {
            "integer" => Ok(self.t.vec_i64()),
            "float" => Ok(self.t.vec_f64()),
            "u8" => Ok(self.t.vec_u8()),
            "bit" => Ok(self.t.vec_bit()),
            other => Err(self.err(format!(
                "unknown vector element type `{}`; expected integer, float, u8, or bit",
                other
            ))),
        }
    }

    /// fz-swt.6 — `resource(T)` is a parametric opaque ctor: the
    /// "wrapped host value" type from the refcounted-resources epic
    /// (fz-swt). The element type `T` is parsed and validated, but the
    /// returned `Descr` is a built-in unqualified opaque tag
    /// (`"resource"`) — visible from every module on its own. The
    /// per-module visibility gate comes from the *outer* `opaque`
    /// alias that wraps it (e.g. `@type t :: opaque resource(integer)`):
    /// the alias's qualified opaque tag (`"Mod::t"`) is what enforces
    /// module ownership.
    ///
    /// Storing `T` structurally in the Descr is left to fz-swt.8 (the
    /// `.value` accessor) — at this layer the parameter exists only to
    /// validate the type-expr and to document intent.
    fn parse_resource(&mut self) -> Result<T::Ty, TypeExprError> {
        // `resource` already consumed. Parse `(T)`.
        self.expect(&Tok::LParen, "`(` after `resource`")?;
        let _inner = self.parse_union()?;
        self.expect(&Tok::RParen, "`)` after resource element type")?;
        Ok(self.t.opaque_of("resource"))
    }

    fn parse_list(&mut self) -> Result<T::Ty, TypeExprError> {
        self.expect(&Tok::LBrack, "`[`")?;
        // Empty list type `[]` — the empty list singleton (nil).
        if matches!(self.peek(), Tok::RBrack) {
            self.bump();
            return Ok(self.t.nil());
        }
        let elem = self.parse_union()?;
        self.expect(&Tok::RBrack, "`]`")?;
        Ok(self.t.list(elem))
    }

    fn parse_tuple(&mut self) -> Result<T::Ty, TypeExprError> {
        self.expect(&Tok::LBrace, "`{`")?;
        let mut elems: Vec<T::Ty> = Vec::new();
        if !matches!(self.peek(), Tok::RBrace) {
            elems.push(self.parse_union()?);
            while matches!(self.peek(), Tok::Comma) {
                self.bump();
                elems.push(self.parse_union()?);
            }
        }
        self.expect(&Tok::RBrace, "`}`")?;
        Ok(self.t.tuple(&elems))
    }

    fn parse_paren_or_arrow(&mut self) -> Result<T::Ty, TypeExprError> {
        self.expect(&Tok::LParen, "`(`")?;
        let mut elems: Vec<T::Ty> = Vec::new();
        if !matches!(self.peek(), Tok::RParen) {
            elems.push(self.parse_union()?);
            while matches!(self.peek(), Tok::Comma) {
                self.bump();
                elems.push(self.parse_union()?);
            }
        }
        self.expect(&Tok::RParen, "`)`")?;
        if matches!(self.peek(), Tok::Arrow) {
            self.bump();
            let ret = self.parse_union()?;
            return Ok(self.t.arrow(&elems, ret));
        }
        // No arrow: parenthesized grouping. Only legal with exactly one
        // inner type — otherwise it's a tuple-shaped paren which we
        // reject (fz uses `{...}` for tuple types).
        if elems.len() == 1 {
            Ok(elems.into_iter().next().unwrap())
        } else {
            Err(self.err(
                "parenthesized type with multiple elements must be \
                 followed by `->` (use `{T, U}` for tuple types)",
            ))
        }
    }

    fn lookup_named(&mut self, name: &str) -> Result<T::Ty, TypeExprError> {
        // Built-in scalar names take precedence over env aliases — a
        // user can't redefine `integer` to mean something else.
        match name {
            "nil" => Ok(self.t.nil()),
            "bool" => Ok(self.t.bool()),
            "integer" => Ok(self.t.int()),
            "float" => Ok(self.t.float()),
            "binary" => Ok(self.t.str_t()),
            "atom" => Ok(self.t.atom()),
            "any" => Ok(self.t.any()),
            "never" => Ok(self.t.none()),
            _ => match self.env.get(name) {
                // ModuleTypeEnv stores concrete Ty (Program is non-
                // generic); bridge through Descr to the parser's T::Ty.
                Some(ty) => Ok(self.t.from_descr(ty.descr())),
                None => Err(TypeExprError {
                    msg: format!("unknown type name `{}`", name),
                    span: self.peek_span(),
                }),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::types_seam::{ConcreteTypes, Ty, Types};

    fn parse_one<T: Types>(t: &mut T, src: &str) -> Result<T::Ty, TypeExprError> {
        parse_one_with(t, src, &ModuleTypeEnv::new())
    }

    fn parse_one_with<T: Types>(
        t: &mut T,
        src: &str,
        env: &ModuleTypeEnv,
    ) -> Result<T::Ty, TypeExprError> {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let (ty, consumed) = parse_type_expr(t, &toks, env)?;
        // Allow trailing Eof.
        let trailing = toks.len() - consumed;
        if trailing > 1 || (trailing == 1 && !matches!(toks[consumed].tok, Tok::Eof)) {
            return Err(TypeExprError {
                msg: format!("trailing {} token(s) after type expression", trailing),
                span: toks[consumed].span,
            });
        }
        Ok(ty)
    }

    #[test]
    fn scalar_names_parse_to_corresponding_descrs() {
        let mut ct = ConcreteTypes;
        let nil = ct.nil();
        let bool_ = ct.bool();
        let int = ct.int();
        let float = ct.float();
        let binary = ct.str_t();
        let atom = ct.atom();
        let any = ct.any();
        let cases: &[(&str, &Ty)] = &[
            ("nil", &nil),
            ("bool", &bool_),
            ("integer", &int),
            ("float", &float),
            ("binary", &binary),
            ("atom", &atom),
            ("any", &any),
            ("_", &any),
        ];
        for (src, expected) in cases {
            let actual = parse_one(&mut ct, src).unwrap();
            assert!(ct.is_equivalent(&actual, expected), "src={}", src);
        }
    }

    #[test]
    fn atom_literal_parses_to_singleton() {
        let mut ct = ConcreteTypes;
        let ok = ct.atom_lit("ok");
        let err = ct.atom_lit("error");
        let a = parse_one(&mut ct, ":ok").unwrap();
        let b = parse_one(&mut ct, ":error").unwrap();
        assert!(ct.is_equivalent(&a, &ok));
        assert!(ct.is_equivalent(&b, &err));
    }

    #[test]
    fn int_literal_parses_to_singleton() {
        let mut ct = ConcreteTypes;
        let i42 = ct.int_lit(42);
        let i0 = ct.int_lit(0);
        let a = parse_one(&mut ct, "42").unwrap();
        let b = parse_one(&mut ct, "0").unwrap();
        assert!(ct.is_equivalent(&a, &i42));
        assert!(ct.is_equivalent(&b, &i0));
    }

    #[test]
    fn float_literal_parses_to_singleton() {
        let mut ct = ConcreteTypes;
        let expected = ct.float_lit(2.5);
        let actual = parse_one(&mut ct, "2.5").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn list_of_integer() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let expected = ct.list(int);
        let actual = parse_one(&mut ct, "[integer]").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn empty_list_is_nil() {
        let mut ct = ConcreteTypes;
        let nil = ct.nil();
        let actual = parse_one(&mut ct, "[]").unwrap();
        assert!(ct.is_equivalent(&actual, &nil));
    }

    #[test]
    fn tuple_two_elements() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let atom = ct.atom();
        let expected = ct.tuple(&[int, atom]);
        let actual = parse_one(&mut ct, "{integer, atom}").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn tuple_three_elements_with_literal() {
        let mut ct = ConcreteTypes;
        let ok = ct.atom_lit("ok");
        let int = ct.int();
        let expected = ct.tuple(&[ok, int.clone(), int]);
        let actual = parse_one(&mut ct, "{:ok, integer, integer}").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn empty_tuple() {
        let mut ct = ConcreteTypes;
        let expected = ct.tuple(&[]);
        let actual = parse_one(&mut ct, "{}").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn arrow_zero_arg() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let expected = ct.arrow(&[], int);
        let actual = parse_one(&mut ct, "() -> integer").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn arrow_one_arg() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let expected = ct.arrow(&[int.clone()], int);
        let actual = parse_one(&mut ct, "(integer) -> integer").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn arrow_two_args() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let float = ct.float();
        let bin = ct.str_t();
        let expected = ct.arrow(&[int, float], bin);
        let actual = parse_one(&mut ct, "(integer, float) -> binary").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn paren_grouping_one_element() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let actual = parse_one(&mut ct, "(integer)").unwrap();
        assert!(ct.is_equivalent(&actual, &int));
    }

    #[test]
    fn paren_grouping_with_union() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let float = ct.float();
        let expected = ct.union(int, float);
        let actual = parse_one(&mut ct, "(integer | float)").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn paren_multi_without_arrow_errors() {
        let mut ct = ConcreteTypes;
        let r = parse_one(&mut ct, "(integer, float)");
        assert!(
            r.is_err(),
            "multi-element paren without `->` must error; got ok",
        );
    }

    #[test]
    fn union_two_axes() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let float = ct.float();
        let expected = ct.union(int, float);
        let actual = parse_one(&mut ct, "integer | float").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn union_three_axes_is_left_associative_but_equivalent() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let float = ct.float();
        let nil = ct.nil();
        let u = ct.union(int, float);
        let expected = ct.union(u, nil);
        let actual = parse_one(&mut ct, "integer | float | nil").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn union_with_atom_literals() {
        let mut ct = ConcreteTypes;
        let ok = ct.atom_lit("ok");
        let err = ct.atom_lit("error");
        let expected = ct.union(ok, err);
        let actual = parse_one(&mut ct, ":ok | :error").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn list_of_union() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let float = ct.float();
        let u = ct.union(int, float);
        let expected = ct.list(u);
        let actual = parse_one(&mut ct, "[integer | float]").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn nested_tuple_inside_list() {
        let mut ct = ConcreteTypes;
        let ok = ct.atom_lit("ok");
        let int = ct.int();
        let tup = ct.tuple(&[ok, int]);
        let expected = ct.list(tup);
        let actual = parse_one(&mut ct, "[{:ok, integer}]").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn arrow_taking_arrow_argument() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let f = ct.arrow(&[int.clone()], int.clone());
        let l = ct.list(int);
        let expected = ct.arrow(&[f, l.clone()], l);
        let actual = parse_one(&mut ct, "((integer) -> integer, [integer]) -> [integer]").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn named_ref_resolves_via_env() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let mut env = ModuleTypeEnv::new();
        env.insert("id".to_string(), int.clone());
        let actual = parse_one_with(&mut ct, "id", &env).unwrap();
        assert!(ct.is_equivalent(&actual, &int));
    }

    #[test]
    fn named_ref_used_in_arrow_via_env() {
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let mut env = ModuleTypeEnv::new();
        env.insert("id".to_string(), int.clone());
        let expected = ct.arrow(&[int.clone()], int);
        let actual = parse_one_with(&mut ct, "(id) -> id", &env).unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn unknown_name_with_empty_env_errors() {
        let mut ct = ConcreteTypes;
        let r = parse_one(&mut ct, "nonesuch");
        assert!(r.is_err());
        let e = r.unwrap_err();
        assert!(e.msg.contains("unknown type name"), "msg = {}", e.msg);
    }

    #[test]
    fn builtin_name_takes_precedence_over_alias() {
        // A user-defined alias must NOT shadow a builtin scalar name.
        let mut ct = ConcreteTypes;
        let float = ct.float();
        let int = ct.int();
        let mut env = ModuleTypeEnv::new();
        env.insert("integer".to_string(), float);
        let actual = parse_one_with(&mut ct, "integer", &env).unwrap();
        assert!(
            ct.is_equivalent(&actual, &int),
            "builtin `integer` must resolve to int regardless of env shadow"
        );
    }

    #[test]
    fn malformed_unclosed_list_errors() {
        let mut ct = ConcreteTypes;
        assert!(parse_one(&mut ct, "[integer").is_err());
    }

    #[test]
    fn malformed_unclosed_tuple_errors() {
        let mut ct = ConcreteTypes;
        assert!(parse_one(&mut ct, "{integer, atom").is_err());
    }

    #[test]
    fn malformed_unclosed_paren_errors() {
        let mut ct = ConcreteTypes;
        assert!(parse_one(&mut ct, "(integer").is_err());
    }

    #[test]
    fn trailing_tokens_error() {
        let mut ct = ConcreteTypes;
        let r = parse_one(&mut ct, "integer foo");
        assert!(r.is_err(), "trailing tokens must be rejected");
    }

    #[test]
    fn primary_position_rejects_bar() {
        // `| integer` is malformed — `|` is a binary operator.
        let mut ct = ConcreteTypes;
        assert!(parse_one(&mut ct, "| integer").is_err());
    }

    // ----- fz-ul4.31.3: build_module_type_env -----

    fn type_alias_attr(name: &str, body_src: &str) -> crate::ast::Attribute {
        use crate::ast::{Attribute, TypeAliasDecl};
        use crate::diag::Span;
        let toks = Lexer::new(body_src).tokenize().expect("lex body");
        // Drop trailing Eof to match parser behavior.
        let body_tokens: Vec<_> = toks
            .into_iter()
            .filter(|t| !matches!(t.tok, Tok::Eof))
            .collect();
        Attribute::TypeAlias(TypeAliasDecl {
            name: name.to_string(),
            name_span: Span::DUMMY,
            body_tokens: crate::ast::TypeExprBody(body_tokens),
            span: Span::DUMMY,
        })
    }

    #[test]
    fn build_env_resolves_simple_alias() {
        let attrs = vec![type_alias_attr("id", "integer")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let env = build_module_type_env(&mut ct, &attrs).unwrap();
        let int = ct.int();
        assert!(ct.is_equivalent(env.get("id").unwrap(), &int));
    }

    #[test]
    fn build_env_resolves_alias_of_alias_in_either_order() {
        // Declare in forward order: a refs b, b is plain.
        let attrs = vec![type_alias_attr("a", "b"), type_alias_attr("b", "integer")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let env = build_module_type_env(&mut ct, &attrs).unwrap();
        let int = ct.int();
        assert!(ct.is_equivalent(env.get("a").unwrap(), &int));
        assert!(ct.is_equivalent(env.get("b").unwrap(), &int));
    }

    #[test]
    fn build_env_resolves_composite_alias() {
        // pair := {id, id}; id := integer.
        let attrs = vec![
            type_alias_attr("pair", "{id, id}"),
            type_alias_attr("id", "integer"),
        ];
        let mut ct = crate::types_seam::ConcreteTypes;
        let env = build_module_type_env(&mut ct, &attrs).unwrap();
        let int = ct.int();
        let expected = ct.tuple(&[int.clone(), int]);
        assert!(ct.is_equivalent(env.get("pair").unwrap(), &expected));
    }

    #[test]
    fn build_env_detects_simple_cycle() {
        let attrs = vec![type_alias_attr("a", "b"), type_alias_attr("b", "a")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
        assert!(
            err.msg.contains("cycle"),
            "expected cycle diag, got: {}",
            err.msg
        );
    }

    #[test]
    fn build_env_detects_three_way_cycle() {
        let attrs = vec![
            type_alias_attr("a", "b"),
            type_alias_attr("b", "c"),
            type_alias_attr("c", "a"),
        ];
        let mut ct = crate::types_seam::ConcreteTypes;
        let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
        assert!(
            err.msg.contains("cycle"),
            "expected cycle diag, got: {}",
            err.msg
        );
    }

    #[test]
    fn build_env_rejects_unknown_reference() {
        let attrs = vec![type_alias_attr("foo", "nonesuch")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
        assert!(
            err.msg.contains("unknown type name"),
            "expected unknown-name diag, got: {}",
            err.msg
        );
    }

    #[test]
    fn build_env_rejects_duplicate_alias() {
        let attrs = vec![
            type_alias_attr("id", "integer"),
            type_alias_attr("id", "float"),
        ];
        let mut ct = crate::types_seam::ConcreteTypes;
        let err = build_module_type_env(&mut ct, &attrs).unwrap_err();
        assert!(
            err.msg.contains("duplicate"),
            "expected duplicate diag, got: {}",
            err.msg
        );
    }

    #[test]
    fn build_env_ignores_non_type_alias_attributes() {
        use crate::ast::Attribute;
        let attrs = vec![
            Attribute::ModuleDoc("hello".to_string()),
            type_alias_attr("id", "integer"),
            Attribute::Doc("a doc".to_string()),
        ];
        let mut ct = crate::types_seam::ConcreteTypes;
        let env = build_module_type_env(&mut ct, &attrs).unwrap();
        assert_eq!(env.len(), 1);
        let int = ct.int();
        assert!(ct.is_equivalent(env.get("id").unwrap(), &int));
    }

    #[test]
    fn build_env_empty_for_module_without_aliases() {
        let attrs: Vec<crate::ast::Attribute> = vec![];
        let mut ct = crate::types_seam::ConcreteTypes;
        let env = build_module_type_env(&mut ct, &attrs).unwrap();
        assert!(env.is_empty());
    }

    #[test]
    fn build_env_resolves_arrow_using_alias() {
        let attrs = vec![
            type_alias_attr("id", "integer"),
            type_alias_attr("idfn", "(id) -> id"),
        ];
        let mut ct = crate::types_seam::ConcreteTypes;
        let env = build_module_type_env(&mut ct, &attrs).unwrap();
        let int = ct.int();
        let expected = ct.arrow(&[int.clone()], int);
        assert!(ct.is_equivalent(env.get("idfn").unwrap(), &expected));
    }

    #[test]
    fn consumed_count_reports_correct_position() {
        // Parser returns how many tokens it consumed, so callers can
        // continue parsing whatever follows (e.g., the `::` separator
        // in `@spec name(T) :: R`).
        let toks = Lexer::new("integer foo").tokenize().unwrap();
        let env = ModuleTypeEnv::new();
        let mut ct = ConcreteTypes;
        let int = ct.int();
        let (ty, consumed) = parse_type_expr(&mut ct, &toks, &env).unwrap();
        assert!(ct.is_equivalent(&ty, &int));
        assert_eq!(consumed, 1, "consumed only the `integer` token");
    }

    // ---- vector(T) ----

    #[test]
    fn vector_integer_parses() {
        let mut ct = ConcreteTypes;
        let expected = ct.vec_i64();
        let actual = parse_one(&mut ct, "vector(integer)").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn vector_float_parses() {
        let mut ct = ConcreteTypes;
        let expected = ct.vec_f64();
        let actual = parse_one(&mut ct, "vector(float)").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn vector_u8_parses() {
        let mut ct = ConcreteTypes;
        let expected = ct.vec_u8();
        let actual = parse_one(&mut ct, "vector(u8)").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn vector_bit_parses() {
        let mut ct = ConcreteTypes;
        let expected = ct.vec_bit();
        let actual = parse_one(&mut ct, "vector(bit)").unwrap();
        assert!(ct.is_equivalent(&actual, &expected));
    }

    #[test]
    fn vector_unknown_elem_type_errors() {
        let mut ct = ConcreteTypes;
        let r = parse_one(&mut ct, "vector(atom)");
        assert!(r.is_err(), "vector(atom) should error");
    }

    // ---- opaque aliases ----

    #[test]
    fn build_env_opaque_alias_creates_nominal_type() {
        let attrs = vec![type_alias_attr("pid", "opaque integer")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let env = build_module_type_env(&mut ct, &attrs).unwrap();
        let pid = env.get("pid").unwrap();
        let expected = ct.opaque_of("pid");
        assert!(
            ct.is_equivalent(pid, &expected),
            "opaque alias should resolve to nominal opaque Ty: got {}",
            ct.display(pid),
        );
    }

    #[test]
    fn build_env_opaque_alias_is_disjoint_from_underlying() {
        let attrs = vec![type_alias_attr("pid", "opaque integer")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let env = build_module_type_env(&mut ct, &attrs).unwrap();
        let pid = env.get("pid").unwrap();
        let int = ct.int();
        assert!(
            !ct.is_subtype(pid, &int),
            "pid should NOT be a subtype of integer"
        );
        assert!(
            !ct.is_subtype(&int, pid),
            "integer should NOT be a subtype of pid"
        );
    }

    // ---- resource(T) (fz-swt.6) ----

    #[test]
    fn resource_integer_parses_to_builtin_opaque_tag() {
        // `resource(T)` is a parametric opaque ctor. The result has the
        // unqualified built-in tag `"resource"`; visibility for user
        // aliases (`@type t :: opaque resource(integer)`) comes from
        // the *outer* opaque alias, not from this tag.
        let mut ct = ConcreteTypes;
        let d = parse_one(&mut ct, "resource(integer)").unwrap();
        assert_eq!(ct.opaque_singleton(&d).as_deref(), Some("resource"));
    }

    #[test]
    fn resource_inner_type_is_validated() {
        let mut ct = ConcreteTypes;
        let r = parse_one(&mut ct, "resource(nonesuch)");
        assert!(r.is_err(), "unknown inner type must error");
    }

    #[test]
    fn build_env_opaque_resource_alias_qualifies_with_module() {
        // The design example: `@type t :: opaque resource(integer)`.
        // Built under module "File", the alias should carry the
        // qualified tag `"File::t"`.
        let attrs = vec![type_alias_attr("t", "opaque resource(integer)")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let (env, _o, _b) = build_module_type_env_for(&mut ct, &attrs, "File").unwrap();
        let ct = crate::types_seam::ConcreteTypes;
        let t = env.get("t").expect("alias resolved");
        assert_eq!(ct.opaque_singleton(t).as_deref(), Some("File::t"));
    }

    #[test]
    fn build_env_opaque_alias_unqualified_at_top_level() {
        // Top-level (no enclosing module) preserves the legacy
        // unqualified tag — these opaques have no owner.
        let attrs = vec![type_alias_attr("pid", "opaque integer")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let env = build_module_type_env(&mut ct, &attrs).unwrap();
        let ct = crate::types_seam::ConcreteTypes;
        let pid = env.get("pid").unwrap();
        assert_eq!(ct.opaque_singleton(pid).as_deref(), Some("pid"));
    }

    #[test]
    fn build_env_opaque_alias_rejects_bad_body() {
        // `opaque <body>` parses the body; an unknown name surfaces.
        let attrs = vec![type_alias_attr("t", "opaque nonesuch")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let err = build_module_type_env_for(&mut ct, &attrs, "M").unwrap_err();
        assert!(
            err.msg.contains("unknown type name"),
            "expected unknown-name diag from opaque body, got: {}",
            err.msg,
        );
    }

    #[test]
    fn build_env_two_opaque_aliases_are_distinct() {
        let attrs = vec![
            type_alias_attr("pid", "opaque integer"),
            type_alias_attr("timestamp", "opaque integer"),
        ];
        let mut ct = crate::types_seam::ConcreteTypes;
        let env = build_module_type_env(&mut ct, &attrs).unwrap();
        let pid = env.get("pid").unwrap();
        let ts = env.get("timestamp").unwrap();
        let inter = ct.intersect(pid.clone(), ts.clone());
        assert!(
            ct.is_empty(&inter),
            "distinct opaques should be disjoint: pid ∩ timestamp = {}",
            ct.display(&inter),
        );
    }

    // ---- refines / brand aliases (fz-axu.3 K2) ----

    #[test]
    fn build_env_refines_alias_creates_brand_descr() {
        let attrs = vec![type_alias_attr("utf8", "refines binary")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let (env, _o, brand_inners) = build_module_type_env_for(&mut ct, &attrs, "").unwrap();
        let utf8 = env.get("utf8").unwrap();
        assert_eq!(
            ct.brand_singleton(utf8).as_deref(),
            Some("utf8"),
            "alias resolves to brand-of(name): got {}",
            ct.display(utf8),
        );
        let inner = brand_inners
            .get("utf8")
            .expect("brand_inners records the inner type");
        let str_t = ct.str_t();
        assert!(
            ct.is_equivalent(inner, &str_t),
            "inner of `refines binary` is binary (str_t): got {}",
            ct.display(inner),
        );
    }

    #[test]
    fn build_env_refines_alias_qualifies_with_module() {
        let attrs = vec![type_alias_attr("email", "refines binary")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let (env, _o, brand_inners) = build_module_type_env_for(&mut ct, &attrs, "Email").unwrap();
        let ct = crate::types_seam::ConcreteTypes;
        let email = env.get("email").unwrap();
        assert_eq!(ct.brand_singleton(email).as_deref(), Some("Email::email"));
        assert!(brand_inners.contains_key("Email::email"));
    }

    #[test]
    fn build_env_refines_alias_rejects_empty_body() {
        let attrs = vec![type_alias_attr("bad", "refines")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let err = build_module_type_env_for(&mut ct, &attrs, "M").unwrap_err();
        assert!(
            err.msg.contains("requires an inner type"),
            "expected diag about missing inner; got: {}",
            err.msg,
        );
    }

    #[test]
    fn build_env_refines_alias_rejects_bad_inner() {
        let attrs = vec![type_alias_attr("bad", "refines nonesuch")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let err = build_module_type_env_for(&mut ct, &attrs, "M").unwrap_err();
        assert!(
            err.msg.contains("unknown type name"),
            "expected unknown-name diag from refines body; got: {}",
            err.msg,
        );
    }

    #[test]
    fn refines_distinct_from_opaque_with_same_name() {
        // Across two modules: M declares brand B = refines integer; N
        // declares opaque B = opaque integer. Their Descrs come from
        // different axes, so they are lattice-disjoint.
        let m_attrs = vec![type_alias_attr("B", "refines integer")];
        let n_attrs = vec![type_alias_attr("B", "opaque integer")];
        let mut ct = crate::types_seam::ConcreteTypes;
        let (m_env, _, _) = build_module_type_env_for(&mut ct, &m_attrs, "M").unwrap();
        let (n_env, _, _) = build_module_type_env_for(&mut ct, &n_attrs, "N").unwrap();
        let b_brand = m_env.get("B").unwrap();
        let b_opaque = n_env.get("B").unwrap();
        let inter = ct.intersect(b_brand.clone(), b_opaque.clone());
        assert!(
            ct.is_empty(&inter),
            "brand and opaque axes are disjoint: {} ∩ {}",
            ct.display(b_brand),
            ct.display(b_opaque),
        );
    }
}
