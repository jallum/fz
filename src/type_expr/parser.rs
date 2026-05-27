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
    let mut p = TypeExprParser {
        t,
        tokens,
        pos: 0,
        env,
        vars: None,
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
    let mut p = TypeExprParser {
        t,
        tokens,
        pos: 0,
        env,
        vars: Some(vars),
    };
    let ty = p.parse_union()?;
    Ok((ty, p.pos))
}

struct TypeExprParser<'a, T: crate::types::Types<Ty = crate::types::Ty>> {
    t: &'a mut T,
    tokens: &'a [Token],
    pos: usize,
    env: &'a ModuleTypeEnv,
    vars: Option<&'a mut std::collections::HashMap<String, crate::types::TypeVarId>>,
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
                } else {
                    self.parse_named_type(name)
                }
            }
            Tok::Upper(name) => {
                self.bump();
                self.parse_named_type(name)
            }
            other => Err(self.err(format!("expected a type expression, got {}", other))),
        }
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
                    return Err(self.err(format!(
                        "expected type-name segment after `.`, got {}",
                        other
                    )));
                }
            }
        }
        let ty = self.lookup_named(&name)?;
        if matches!(self.peek(), Tok::LParen) {
            self.bump();
            if !matches!(self.peek(), Tok::RParen) {
                let _ = self.parse_union()?;
                while matches!(self.peek(), Tok::Comma) {
                    self.bump();
                    let _ = self.parse_union()?;
                }
            }
            self.expect(&Tok::RParen, "`)` after type arguments")?;
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
