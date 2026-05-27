use super::*;

/// Parse one type expression from `tokens` starting at index 0.
/// Returns the lowered type and the number of tokens consumed.
///
/// `env` resolves named references (e.g. `id` → declared alias).
/// Names not in `env` and not one of the built-in scalars produce an
/// unknown-name error.
pub fn parse_type_expr<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    tokens: &[Token],
    env: &ModuleTypeEnv,
) -> Result<(T::Ty, usize), TypeExprError> {
    parse_type_expr_with_stack(t, tokens, env, None, Vec::new())
}

pub(super) fn parse_type_expr_with_stack<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    tokens: &[Token],
    env: &ModuleTypeEnv,
    vars: Option<&mut std::collections::HashMap<String, crate::types::TypeVarId>>,
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

pub fn parse_type_expr_with_vars<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    tokens: &[Token],
    env: &ModuleTypeEnv,
    vars: &mut std::collections::HashMap<String, crate::types::TypeVarId>,
) -> Result<(T::Ty, usize), TypeExprError> {
    parse_type_expr_with_stack(t, tokens, env, Some(vars), Vec::new())
}

struct TypeExprParser<'a, T: crate::types::Types<Ty = crate::types::Ty>> {
    t: &'a mut T,
    tokens: &'a [Token],
    pos: usize,
    env: &'a ModuleTypeEnv,
    vars: Option<&'a mut std::collections::HashMap<String, crate::types::TypeVarId>>,
    alias_stack: Vec<(String, usize)>,
}

impl<'a, T: crate::types::Types<Ty = crate::types::Ty>> TypeExprParser<'a, T> {
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
            Tok::LParen => self.parse_parenthesized_type_or_arrow_type(),
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
                    self.lookup_named(&name)
                }
            }
            Tok::Upper(name) => {
                self.bump();
                if matches!(self.peek(), Tok::LParen) {
                    self.parse_alias_application(name)
                } else {
                    self.lookup_named(&name)
                }
            }
            other => Err(self.err(format!("expected a type expression, got {}", other))),
        }
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
        let Some(alias) = self.env.get_param_alias(&name, arity).cloned() else {
            if arity == 0 {
                return self.lookup_named(&name);
            }
            return Err(self.err(format!("unknown type alias `{}/{}`", name, arity)));
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
        let (ty, consumed) =
            parse_type_expr_with_stack(self.t, &alias.body_tokens.0, &env, None, stack)?;
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
                        let next = crate::types::TypeVarId(vars.len() as u32);
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
