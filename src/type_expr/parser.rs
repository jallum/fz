use super::*;
use crate::frontend::protocols::PROTOCOL_ELEM_VAR;
use crate::types::TypeVarId;
use std::mem::discriminant;

/// Parse one type expression from `tokens` starting at index 0.
/// Returns the lowered type and the number of tokens consumed.
///
/// `env` resolves named references (e.g. `id` → declared alias).
/// Names not in `env` and not one of the built-in scalars produce an
/// unknown-name error.
pub fn parse_type_expr<T: Types<Ty = Ty>>(
    t: &mut T,
    tokens: &[Token],
    env: &ModuleTypeEnv,
) -> Result<(T::Ty, usize), TypeExprError> {
    parse_type_expr_with_stack(t, tokens, env, None, Vec::new())
}

pub fn parse_struct_record_type<T: Types<Ty = Ty>>(
    t: &mut T,
    tokens: &[Token],
    env: &ModuleTypeEnv,
) -> Result<(StructRecordType, Ty, usize), TypeExprError> {
    let mut p = TypeExprParser {
        t,
        tokens,
        pos: 0,
        env,
        vars: None,
        alias_stack: Vec::new(),
    };
    p.parse_struct_record()
}

pub(super) fn parse_type_expr_with_stack<T: Types<Ty = Ty>>(
    t: &mut T,
    tokens: &[Token],
    env: &ModuleTypeEnv,
    vars: Option<&mut HashMap<String, TypeVarId>>,
    alias_stack: Vec<(String, usize)>,
) -> Result<(T::Ty, usize), TypeExprError> {
    let mut p = TypeExprParser {
        t,
        tokens,
        pos: 0,
        env,
        vars,
        alias_stack,
    };
    let ty = p.parse_union()?;
    Ok((ty, p.pos))
}

pub fn parse_type_expr_with_vars<T: Types<Ty = Ty>>(
    t: &mut T,
    tokens: &[Token],
    env: &ModuleTypeEnv,
    vars: &mut HashMap<String, TypeVarId>,
) -> Result<(T::Ty, usize), TypeExprError> {
    parse_type_expr_with_stack(t, tokens, env, Some(vars), Vec::new())
}

pub fn parse_type_shape_with_vars(
    tokens: &[Token],
    env: &ModuleTypeEnv,
    vars: &mut HashMap<String, TypeVarId>,
) -> Result<(ResolvedTypeShape, usize), TypeExprError> {
    let mut p = TypeShapeParser {
        tokens,
        pos: 0,
        env,
        vars,
    };
    let shape = p.parse_union()?;
    Ok((shape, p.pos))
}

pub fn struct_record_nominal_ty<T: Types<Ty = Ty>>(t: &mut T, module: &ModuleName) -> T::Ty {
    t.opaque_of(&format!("impl-target::{}", module.last_segment()))
}

struct TypeExprParser<'a, T: Types<Ty = Ty>> {
    t: &'a mut T,
    tokens: &'a [Token],
    pos: usize,
    env: &'a ModuleTypeEnv,
    vars: Option<&'a mut HashMap<String, TypeVarId>>,
    alias_stack: Vec<(String, usize)>,
}

struct TypeShapeParser<'a> {
    tokens: &'a [Token],
    pos: usize,
    env: &'a ModuleTypeEnv,
    vars: &'a mut HashMap<String, TypeVarId>,
}

impl<'a, T: Types<Ty = Ty>> TypeExprParser<'a, T> {
    fn peek(&self) -> &Tok {
        self.tokens.get(self.pos).map(|t| &t.tok).unwrap_or(&Tok::Eof)
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
        if discriminant(self.peek()) == discriminant(want) {
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
            Tok::LParen => self.parse_parenthesized_type_or_arrow_type(),
            Tok::Percent => {
                let (_record, ty, _consumed) = self.parse_struct_record()?;
                Ok(ty)
            }
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
                if name == "resource" {
                    self.parse_resource()
                } else if matches!(self.peek(), Tok::LParen) {
                    self.parse_alias_application(name)
                } else {
                    self.parse_named_type(name)
                }
            }
            Tok::Upper(name) => {
                self.bump();
                if matches!(self.peek(), Tok::LParen) {
                    self.parse_alias_application(name)
                } else {
                    self.parse_named_type(name)
                }
            }
            other => Err(self.err(format!("expected a type expression, got {}", other))),
        }
    }

    fn parse_struct_record(&mut self) -> Result<(StructRecordType, T::Ty, usize), TypeExprError> {
        let span = self.peek_span();
        self.expect(&Tok::Percent, "`%` before struct record type")?;
        let module = self.parse_module_name("struct record type module")?;
        self.expect(&Tok::LBrace, "`{` after struct record type module")?;
        let mut fields = Vec::new();
        if !matches!(self.peek(), Tok::RBrace) {
            loop {
                let field = self.parse_record_field_name()?;
                let ty = self.parse_union()?;
                fields.push(StructFieldType { name: field, ty });
                if !matches!(self.peek(), Tok::Comma) {
                    break;
                }
                self.bump();
            }
        }
        self.expect(&Tok::RBrace, "`}` after struct record fields")?;
        let ty = struct_record_nominal_ty(self.t, &module);
        Ok((StructRecordType { module, span, fields }, ty, self.pos))
    }

    fn parse_record_field_name(&mut self) -> Result<String, TypeExprError> {
        match self.peek().clone() {
            Tok::KwKey(name) => {
                self.bump();
                Ok(name)
            }
            Tok::Atom(name) | Tok::Ident(name) => {
                self.bump();
                self.expect(&Tok::Colon, "`:` after struct record field name")?;
                Ok(name)
            }
            other => Err(self.err(format!("expected struct record field name, got {}", other))),
        }
    }

    fn parse_module_name(&mut self, ctx: &str) -> Result<ModuleName, TypeExprError> {
        let mut segments = match self.peek().clone() {
            Tok::Upper(name) => {
                self.bump();
                vec![name]
            }
            other => return Err(self.err(format!("expected {}, got {}", ctx, other))),
        };
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.peek().clone() {
                Tok::Upper(segment) => {
                    self.bump();
                    segments.push(segment);
                }
                other => {
                    return Err(self.err(format!("expected module segment after `.`, got {}", other)));
                }
            }
        }
        Ok(ModuleName::from_segments(segments))
    }

    fn parse_named_type(&mut self, mut name: String) -> Result<T::Ty, TypeExprError> {
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.peek().clone() {
                Tok::Ident(segment) | Tok::Upper(segment) => {
                    self.bump();
                    name.push('.');
                    name.push_str(&segment);
                }
                other => {
                    return Err(self.err(format!("expected type-name segment after `.`, got {}", other)));
                }
            }
        }
        let ty = self.lookup_named(&name)?;
        if matches!(self.peek(), Tok::LParen) {
            self.bump();
            let mut args = Vec::new();
            if !matches!(self.peek(), Tok::RParen) {
                args.push(self.parse_union()?);
                while matches!(self.peek(), Tok::Comma) {
                    self.bump();
                    args.push(self.parse_union()?);
                }
            }
            self.expect(&Tok::RParen, "`)` after type arguments")?;
            // A protocol domain `Protocol.t(elem)` refines its element-parametric
            // targets with `elem`. The element is the first argument; the domain
            // is single-parameter, so any extra arguments do not refine further.
            // A `elem` that still mentions a free type variable (e.g. the `a` in
            // a protocol's own `t(a)` callback declaration) carries no concrete
            // refinement — `list(a)` for unconstrained `a` is `list(any)` — so
            // the bare domain is used and dispatch is left unperturbed.
            if let (Some(TypeAlias::ProtocolDomain(template)), Some(elem)) =
                (self.env.get_alias(&name, args.len()).cloned(), args.first())
                && !self.t.has_vars(elem)
            {
                let sigma = HashMap::from([(PROTOCOL_ELEM_VAR, elem.clone())]);
                return Ok(self.t.instantiate(&template, &sigma));
            }
        }
        Ok(ty)
    }

    /// fz-swt.6 — `resource(T)` is a parametric opaque ctor: the
    /// "wrapped host value" type from the refcounted-resources epic
    /// (fz-swt). The element type `T` is parsed and validated, but the
    /// returned type is a built-in unqualified opaque tag
    /// (`"resource"`) — visible from every module on its own. The
    /// per-module visibility gate comes from the *outer* `opaque`
    /// alias that wraps it (e.g. `@type t :: opaque resource(integer)`):
    /// the alias's qualified opaque tag (`"Mod::t"`) is what enforces
    /// module ownership.
    ///
    /// Storing `T` structurally in the concrete representation is left to fz-swt.8 (the
    /// `.value` accessor) — at this layer the parameter exists only to
    /// validate the type-expr and to document intent.
    fn parse_resource(&mut self) -> Result<T::Ty, TypeExprError> {
        // `resource` already consumed. Parse `(T)`.
        self.expect(&Tok::LParen, "`(` after `resource`")?;
        let inner = self.parse_union()?;
        self.expect(&Tok::RParen, "`)` after resource element type")?;
        Ok(self.t.resource(inner))
    }

    fn parse_alias_application(&mut self, name: String) -> Result<T::Ty, TypeExprError> {
        self.expect(&Tok::LParen, "`(` after type alias name")?;
        let mut args = Vec::new();
        if !matches!(self.peek(), Tok::RParen) {
            loop {
                args.push(self.parse_union()?);
                if !matches!(self.peek(), Tok::Comma) {
                    break;
                }
                self.bump();
            }
        }
        self.expect(&Tok::RParen, "`)` after type alias arguments")?;

        let arity = args.len();
        let Some(alias) = self.env.get_alias(&name, arity).cloned() else {
            return Err(self.err(format!("unknown type alias `{}/{}`", name, arity)));
        };
        let alias = match alias {
            TypeAlias::Resolved(ty) => return Ok(ty),
            TypeAlias::ProtocolDomain(template) => {
                let elem = args.first().cloned().unwrap_or_else(|| self.t.any());
                // A concrete element refines; an element mentioning a free
                // variable carries no refinement, so `PROTOCOL_ELEM_VAR` falls
                // back to `any` (the bare domain).
                let elem = if self.t.has_vars(&elem) { self.t.any() } else { elem };
                let sigma = HashMap::from([(PROTOCOL_ELEM_VAR, elem)]);
                return Ok(self.t.instantiate(&template, &sigma));
            }
            TypeAlias::Parameterized(alias) => alias,
        };
        let key = (name, arity);
        if self.alias_stack.contains(&key) {
            return Err(TypeExprError {
                msg: format!("type-alias cycle involving `{}/{}`", key.0, key.1),
                span: alias.span,
            });
        }

        let mut env = self.env.clone();
        for (param, arg) in alias.params.iter().zip(args) {
            env.insert(param.clone(), arg);
        }
        let mut stack = self.alias_stack.clone();
        stack.push(key);
        let (ty, consumed) = parse_type_expr_with_stack(self.t, &alias.body_tokens.0, &env, None, stack)?;
        if consumed != alias.body_tokens.0.len() {
            return Err(TypeExprError {
                msg: "unexpected trailing tokens in type alias body".to_string(),
                span: alias
                    .body_tokens
                    .0
                    .get(consumed)
                    .map(|tok| tok.span)
                    .unwrap_or(alias.span),
            });
        }
        Ok(ty)
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

    fn parse_parenthesized_type_or_arrow_type(&mut self) -> Result<T::Ty, TypeExprError> {
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
            "cpointer" => Ok(self.t.cpointer()),
            "binary" => Ok(self.t.str_t()),
            "atom" => Ok(self.t.atom()),
            "any" => Ok(self.t.any()),
            "never" => Ok(self.t.none()),
            super::BUILTIN_UTF8 => Ok(self.t.brand_of(super::BUILTIN_UTF8)),
            super::BUILTIN_PID => Ok(self.t.opaque_of(super::BUILTIN_PID)),
            super::BUILTIN_REF => Ok(self.t.opaque_of(super::BUILTIN_REF)),
            _ => match self.env.get(name) {
                Some(ty) => Ok(ty.clone()),
                None => {
                    if let Some(vars) = self.vars.as_deref_mut()
                        && name.len() == 1
                    {
                        let next = TypeVarId(vars.len() as u32);
                        let id = *vars.entry(name.to_string()).or_insert(next);
                        Ok(self.t.type_var(id))
                    } else {
                        Err(TypeExprError {
                            msg: format!("unknown type name `{}`", name),
                            span: self.peek_span(),
                        })
                    }
                }
            },
        }
    }
}

impl TypeShapeParser<'_> {
    fn peek(&self) -> &Tok {
        self.tokens.get(self.pos).map(|t| &t.tok).unwrap_or(&Tok::Eof)
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
        if discriminant(self.peek()) == discriminant(want) {
            self.bump();
            Ok(())
        } else {
            Err(self.err(format!("expected {}, got {}", ctx, self.peek())))
        }
    }

    fn parse_union(&mut self) -> Result<ResolvedTypeShape, TypeExprError> {
        let mut elems = vec![self.parse_primary()?];
        while matches!(self.peek(), Tok::Bar) {
            self.bump();
            elems.push(self.parse_primary()?);
        }
        match elems.as_slice() {
            [single] => Ok(single.clone()),
            _ => Ok(ResolvedTypeShape::Union(elems)),
        }
    }

    fn parse_primary(&mut self) -> Result<ResolvedTypeShape, TypeExprError> {
        match self.peek().clone() {
            Tok::LBrack => self.parse_list(),
            Tok::LBrace => self.parse_tuple(),
            Tok::LParen => self.parse_parenthesized_type_or_arrow_type(),
            Tok::Percent => self.parse_struct_record(),
            Tok::Underscore => {
                self.bump();
                Ok(ResolvedTypeShape::Any)
            }
            Tok::Atom(name) => {
                self.bump();
                Ok(ResolvedTypeShape::AtomLit(name))
            }
            Tok::Int(n) => {
                self.bump();
                Ok(ResolvedTypeShape::IntLit(n))
            }
            Tok::Float(f) => {
                self.bump();
                Ok(ResolvedTypeShape::FloatLit(f.to_bits()))
            }
            Tok::Nil => {
                self.bump();
                Ok(ResolvedTypeShape::Nil)
            }
            Tok::True | Tok::False => {
                self.bump();
                Ok(ResolvedTypeShape::Bool)
            }
            Tok::Ident(name) => {
                self.bump();
                if name == "resource" {
                    self.parse_resource()
                } else if matches!(self.peek(), Tok::LParen) {
                    self.parse_alias_application(name)
                } else {
                    self.parse_named_type(name)
                }
            }
            Tok::Upper(name) => {
                self.bump();
                if matches!(self.peek(), Tok::LParen) {
                    self.parse_alias_application(name)
                } else {
                    self.parse_named_type(name)
                }
            }
            other => Err(self.err(format!("expected a type expression, got {}", other))),
        }
    }

    fn parse_struct_record(&mut self) -> Result<ResolvedTypeShape, TypeExprError> {
        self.expect(&Tok::Percent, "`%` before struct record type")?;
        let module = self.parse_module_name("struct record type module")?;
        self.expect(&Tok::LBrace, "`{` after struct record type module")?;
        let mut fields = Vec::new();
        if !matches!(self.peek(), Tok::RBrace) {
            loop {
                let name = self.parse_record_field_name()?;
                self.expect(&Tok::Colon, "`:` after struct field name")?;
                let ty = self.parse_union()?;
                fields.push(ResolvedStructFieldShape { name, ty });
                if !matches!(self.peek(), Tok::Comma) {
                    break;
                }
                self.bump();
            }
        }
        self.expect(&Tok::RBrace, "`}` after struct record fields")?;
        Ok(ResolvedTypeShape::StructRecord { module, fields })
    }

    fn parse_record_field_name(&mut self) -> Result<String, TypeExprError> {
        match self.peek().clone() {
            Tok::Atom(name) | Tok::Ident(name) => {
                self.bump();
                Ok(name)
            }
            other => Err(self.err(format!("expected field name in struct record type, got {}", other))),
        }
    }

    fn parse_module_name(&mut self, ctx: &str) -> Result<ModuleName, TypeExprError> {
        let mut segments = match self.peek().clone() {
            Tok::Upper(name) => {
                self.bump();
                vec![name]
            }
            other => return Err(self.err(format!("expected {}, got {}", ctx, other))),
        };
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.peek().clone() {
                Tok::Upper(segment) => {
                    self.bump();
                    segments.push(segment);
                }
                other => {
                    return Err(self.err(format!("expected module segment after `.`, got {}", other)));
                }
            }
        }
        Ok(ModuleName::from_segments(segments))
    }

    fn parse_named_type(&mut self, mut name: String) -> Result<ResolvedTypeShape, TypeExprError> {
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.peek().clone() {
                Tok::Ident(segment) | Tok::Upper(segment) => {
                    self.bump();
                    name.push('.');
                    name.push_str(&segment);
                }
                other => {
                    return Err(self.err(format!("expected type-name segment after `.`, got {}", other)));
                }
            }
        }
        let shape = self.lookup_named(&name)?;
        if matches!(self.peek(), Tok::LParen) {
            self.bump();
            let mut args = Vec::new();
            if !matches!(self.peek(), Tok::RParen) {
                args.push(self.parse_union()?);
                while matches!(self.peek(), Tok::Comma) {
                    self.bump();
                    args.push(self.parse_union()?);
                }
            }
            self.expect(&Tok::RParen, "`)` after type arguments")?;
            let arity = args.len();
            if self.env.get_alias(&name, arity).is_none() {
                return Err(self.err(format!("unknown type alias `{}/{}`", name, arity)));
            }
            return Ok(ResolvedTypeShape::Named { name, args });
        }
        Ok(shape)
    }

    fn parse_resource(&mut self) -> Result<ResolvedTypeShape, TypeExprError> {
        self.expect(&Tok::LParen, "`(` after `resource`")?;
        let inner = self.parse_union()?;
        self.expect(&Tok::RParen, "`)` after resource element type")?;
        Ok(ResolvedTypeShape::Resource(Box::new(inner)))
    }

    fn parse_alias_application(&mut self, mut name: String) -> Result<ResolvedTypeShape, TypeExprError> {
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.peek().clone() {
                Tok::Ident(segment) | Tok::Upper(segment) => {
                    self.bump();
                    name.push('.');
                    name.push_str(&segment);
                }
                other => {
                    return Err(self.err(format!("expected type-name segment after `.`, got {}", other)));
                }
            }
        }
        self.expect(&Tok::LParen, "`(` after type alias name")?;
        let mut args = Vec::new();
        if !matches!(self.peek(), Tok::RParen) {
            loop {
                args.push(self.parse_union()?);
                if !matches!(self.peek(), Tok::Comma) {
                    break;
                }
                self.bump();
            }
        }
        self.expect(&Tok::RParen, "`)` after type alias arguments")?;

        let arity = args.len();
        if self.env.get_alias(&name, arity).is_none() {
            return Err(self.err(format!("unknown type alias `{}/{}`", name, arity)));
        }
        Ok(ResolvedTypeShape::Named { name, args })
    }

    fn parse_list(&mut self) -> Result<ResolvedTypeShape, TypeExprError> {
        self.expect(&Tok::LBrack, "`[`")?;
        if matches!(self.peek(), Tok::RBrack) {
            self.bump();
            return Ok(ResolvedTypeShape::Nil);
        }
        let elem = self.parse_union()?;
        self.expect(&Tok::RBrack, "`]`")?;
        Ok(ResolvedTypeShape::List(Box::new(elem)))
    }

    fn parse_tuple(&mut self) -> Result<ResolvedTypeShape, TypeExprError> {
        self.expect(&Tok::LBrace, "`{`")?;
        let mut elems = Vec::new();
        if !matches!(self.peek(), Tok::RBrace) {
            elems.push(self.parse_union()?);
            while matches!(self.peek(), Tok::Comma) {
                self.bump();
                elems.push(self.parse_union()?);
            }
        }
        self.expect(&Tok::RBrace, "`}`")?;
        Ok(ResolvedTypeShape::Tuple(elems))
    }

    fn parse_parenthesized_type_or_arrow_type(&mut self) -> Result<ResolvedTypeShape, TypeExprError> {
        self.expect(&Tok::LParen, "`(`")?;
        let mut elems = Vec::new();
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
            return Ok(ResolvedTypeShape::Arrow {
                params: elems,
                result: Box::new(ret),
            });
        }
        if elems.len() == 1 {
            Ok(elems.into_iter().next().unwrap())
        } else {
            Err(self.err(
                "parenthesized type with multiple elements must be followed by `->` (use `{T, U}` for tuple types)",
            ))
        }
    }

    fn lookup_named(&mut self, name: &str) -> Result<ResolvedTypeShape, TypeExprError> {
        match name {
            "nil" => Ok(ResolvedTypeShape::Nil),
            "bool" => Ok(ResolvedTypeShape::Bool),
            "integer" => Ok(ResolvedTypeShape::Integer),
            "float" => Ok(ResolvedTypeShape::Float),
            "cpointer" => Ok(ResolvedTypeShape::CPointer),
            "binary" => Ok(ResolvedTypeShape::Binary),
            "atom" => Ok(ResolvedTypeShape::Atom),
            "any" => Ok(ResolvedTypeShape::Any),
            "never" => Ok(ResolvedTypeShape::Never),
            super::BUILTIN_UTF8 => Ok(ResolvedTypeShape::Utf8),
            super::BUILTIN_PID => Ok(ResolvedTypeShape::Pid),
            super::BUILTIN_REF => Ok(ResolvedTypeShape::Ref),
            _ => match self.env.get(name) {
                Some(_) => Ok(ResolvedTypeShape::Named {
                    name: name.to_string(),
                    args: Vec::new(),
                }),
                None if name.len() == 1 => {
                    let next = TypeVarId(self.vars.len() as u32);
                    let id = *self.vars.entry(name.to_string()).or_insert(next);
                    Ok(ResolvedTypeShape::Var(id))
                }
                None => Err(TypeExprError {
                    msg: format!("unknown type name `{}`", name),
                    span: self.peek_span(),
                }),
            },
        }
    }
}
