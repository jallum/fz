//! Compiler2-owned syntactic type-expression parse.
//!
//! A type expression — an `@spec` argument or result, an `@type` body, a
//! parameter annotation, an extern signature — is parsed from its
//! `TypeExprBody` tokens into a purely *syntactic* tree. Names stay bare
//! [`TypeExpr::Name`]: the parser never decides whether a name is a builtin
//! scalar, a declared alias, or a free type variable, and it consults no
//! environment. That classification is a *resolution* question, answered
//! against the namespace captured where the declaration appears (see
//! `fz-rh2.12.1`/`.3`), not a parse-time one.
//!
//! This is the in-house replacement for the old-world `crate::type_expr`
//! parser, which welds a `ModuleTypeEnv` into the grammar — name-vs-var and
//! arity are decided mid-parse there. That coupling is exactly the
//! whole-program assumption the incremental compiler rejects, so the grammar
//! comes in-house clean and resolution-free.
//!
//! `parse_type_def_body` is consumed by scoping (fz-rh2.12.1); the reference
//! walk (fz-rh2.12.12) and resolver (fz-rh2.12.3) consume the rest.

use crate::compiler::source::Span;
use crate::parser::lexer::{Tok, Token};

/// A syntactic type expression. Every user name — scalar, alias, or
/// variable — is a [`TypeExpr::Name`] until resolution classifies it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeExpr {
    /// A name in type position: `integer`, `t`, `SomeModule.t`, `t(float)`.
    /// `path` holds the dotted segments; `args` the optional `(...)`
    /// application. Builtins, aliases, and free variables all arrive here.
    Name { path: Vec<String>, args: Vec<TypeExpr> },
    /// `[T]`.
    List(Box<TypeExpr>),
    /// `[]` — the empty-list type.
    EmptyList,
    /// `{T, U, …}`.
    Tuple(Vec<TypeExpr>),
    /// `(A, B) -> R`.
    Arrow {
        params: Vec<TypeExpr>,
        result: Box<TypeExpr>,
    },
    /// `A | B | …`.
    Union(Vec<TypeExpr>),
    /// `%Mod{field: T, …}`.
    StructRecord {
        module: Vec<String>,
        fields: Vec<(String, TypeExpr)>,
    },
    /// `:ok`.
    AtomLit(String),
    /// `42`.
    IntLit(i64),
    /// `2.5`, stored as its bit pattern to match the lattice's float key.
    FloatLit(u64),
    /// `_`.
    Wildcard,
    /// `nil`.
    Nil,
    /// `true` / `false` in type position (both denote the bool type).
    Bool,
}

/// How an `@type` declaration wraps its inner type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NominalKind {
    /// `@type t :: <type>` — a transparent alias.
    Plain,
    /// `@type B :: refines T` — a brand over the structural inner `T`.
    Refines,
    /// `@type T :: opaque U` — a nominal opaque declaration with body `U`.
    Opaque,
}

/// The parsed body of an `@type` declaration: a nominal kind over an inner
/// type expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDefBody {
    pub kind: NominalKind,
    pub inner: TypeExpr,
}

/// A failure to parse a type expression, carrying the offending span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeExprError {
    pub msg: String,
    pub span: Span,
}

/// Parses a complete type expression, requiring every token be consumed (a
/// trailing `Eof` is allowed).
pub fn parse_type_expr(tokens: &[Token]) -> Result<TypeExpr, TypeExprError> {
    let mut parser = TypeExprParser { tokens, pos: 0 };
    let expr = parser.parse_union()?;
    parser.expect_end()?;
    Ok(expr)
}

/// Parses the body of an `@type` declaration: an optional `refines` / `opaque`
/// nominal prefix over an inner type expression.
pub fn parse_type_def_body(tokens: &[Token]) -> Result<TypeDefBody, TypeExprError> {
    let (kind, rest) = match tokens.first().map(|token| &token.tok) {
        Some(Tok::Ident(word)) if word == "refines" => (NominalKind::Refines, &tokens[1..]),
        Some(Tok::Ident(word)) if word == "opaque" => (NominalKind::Opaque, &tokens[1..]),
        _ => (NominalKind::Plain, tokens),
    };
    if matches!(kind, NominalKind::Refines | NominalKind::Opaque) && is_empty_body(rest) {
        let span = tokens.first().map(|token| token.span).unwrap_or(Span::DUMMY);
        return Err(TypeExprError {
            msg: "a nominal `@type` body requires an inner type".to_string(),
            span,
        });
    }
    let inner = parse_type_expr(rest)?;
    Ok(TypeDefBody { kind, inner })
}

fn is_empty_body(tokens: &[Token]) -> bool {
    tokens.iter().all(|token| matches!(token.tok, Tok::Eof))
}

struct TypeExprParser<'a> {
    tokens: &'a [Token],
    pos: usize,
}

impl<'a> TypeExprParser<'a> {
    fn peek(&self) -> &Tok {
        self.tokens.get(self.pos).map(|token| &token.tok).unwrap_or(&Tok::Eof)
    }

    fn peek_span(&self) -> Span {
        self.tokens
            .get(self.pos)
            .or_else(|| self.tokens.last())
            .map(|token| token.span)
            .unwrap_or(Span::DUMMY)
    }

    fn bump(&mut self) {
        self.pos += 1;
    }

    fn at_end(&self) -> bool {
        matches!(self.peek(), Tok::Eof)
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

    fn expect_end(&mut self) -> Result<(), TypeExprError> {
        if self.at_end() {
            Ok(())
        } else {
            Err(self.err(format!("unexpected trailing token {}", self.peek())))
        }
    }

    fn parse_union(&mut self) -> Result<TypeExpr, TypeExprError> {
        let mut elems = vec![self.parse_primary()?];
        while matches!(self.peek(), Tok::Bar) {
            self.bump();
            elems.push(self.parse_primary()?);
        }
        if elems.len() == 1 {
            Ok(elems.pop().unwrap())
        } else {
            Ok(TypeExpr::Union(elems))
        }
    }

    fn parse_primary(&mut self) -> Result<TypeExpr, TypeExprError> {
        match self.peek().clone() {
            Tok::LBrack => self.parse_list(),
            Tok::LBrace => self.parse_tuple(),
            Tok::LParen => self.parse_paren_or_arrow(),
            Tok::Percent => self.parse_struct_record(),
            Tok::Underscore => {
                self.bump();
                Ok(TypeExpr::Wildcard)
            }
            Tok::Atom(name) => {
                self.bump();
                Ok(TypeExpr::AtomLit(name))
            }
            Tok::Int(n) => {
                self.bump();
                Ok(TypeExpr::IntLit(n))
            }
            Tok::Float(f) => {
                self.bump();
                Ok(TypeExpr::FloatLit(f.to_bits()))
            }
            Tok::Nil => {
                self.bump();
                Ok(TypeExpr::Nil)
            }
            Tok::True | Tok::False => {
                self.bump();
                Ok(TypeExpr::Bool)
            }
            Tok::Ident(name) | Tok::Upper(name) => {
                self.bump();
                self.parse_name(name)
            }
            other => Err(self.err(format!("expected a type expression, got {}", other))),
        }
    }

    /// Parses a (possibly dotted) name with an optional type-argument
    /// application: `t`, `t(float)`, `SomeModule.t`, `SomeModule.t(float)`. No
    /// classification or arity check — that is resolution's job.
    fn parse_name(&mut self, first: String) -> Result<TypeExpr, TypeExprError> {
        let mut path = vec![first];
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.peek().clone() {
                Tok::Ident(segment) | Tok::Upper(segment) => {
                    self.bump();
                    path.push(segment);
                }
                other => return Err(self.err(format!("expected a name segment after `.`, got {}", other))),
            }
        }
        let args = if matches!(self.peek(), Tok::LParen) {
            self.parse_args()?
        } else {
            Vec::new()
        };
        Ok(TypeExpr::Name { path, args })
    }

    fn parse_args(&mut self) -> Result<Vec<TypeExpr>, TypeExprError> {
        self.expect(&Tok::LParen, "`(`")?;
        let mut args = Vec::new();
        if !matches!(self.peek(), Tok::RParen) {
            args.push(self.parse_union()?);
            while matches!(self.peek(), Tok::Comma) {
                self.bump();
                args.push(self.parse_union()?);
            }
        }
        self.expect(&Tok::RParen, "`)` after type arguments")?;
        Ok(args)
    }

    fn parse_list(&mut self) -> Result<TypeExpr, TypeExprError> {
        self.expect(&Tok::LBrack, "`[`")?;
        if matches!(self.peek(), Tok::RBrack) {
            self.bump();
            return Ok(TypeExpr::EmptyList);
        }
        let elem = self.parse_union()?;
        self.expect(&Tok::RBrack, "`]`")?;
        Ok(TypeExpr::List(Box::new(elem)))
    }

    fn parse_tuple(&mut self) -> Result<TypeExpr, TypeExprError> {
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
        Ok(TypeExpr::Tuple(elems))
    }

    fn parse_paren_or_arrow(&mut self) -> Result<TypeExpr, TypeExprError> {
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
            let result = self.parse_union()?;
            return Ok(TypeExpr::Arrow {
                params: elems,
                result: Box::new(result),
            });
        }
        if elems.len() == 1 {
            Ok(elems.pop().unwrap())
        } else {
            Err(self
                .err("a parenthesized type with multiple elements must be followed by `->` (use `{T, U}` for a tuple)"))
        }
    }

    fn parse_struct_record(&mut self) -> Result<TypeExpr, TypeExprError> {
        self.expect(&Tok::Percent, "`%`")?;
        let module = self.parse_module_path()?;
        self.expect(&Tok::LBrace, "`{` after struct-record module")?;
        let mut fields = Vec::new();
        if !matches!(self.peek(), Tok::RBrace) {
            loop {
                let name = self.parse_field_name()?;
                let ty = self.parse_union()?;
                fields.push((name, ty));
                if !matches!(self.peek(), Tok::Comma) {
                    break;
                }
                self.bump();
            }
        }
        self.expect(&Tok::RBrace, "`}` after struct-record fields")?;
        Ok(TypeExpr::StructRecord { module, fields })
    }

    fn parse_module_path(&mut self) -> Result<Vec<String>, TypeExprError> {
        let mut segments = match self.peek().clone() {
            Tok::Upper(name) => {
                self.bump();
                vec![name]
            }
            other => return Err(self.err(format!("expected a module name, got {}", other))),
        };
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.peek().clone() {
                Tok::Upper(segment) => {
                    self.bump();
                    segments.push(segment);
                }
                other => return Err(self.err(format!("expected a module segment after `.`, got {}", other))),
            }
        }
        Ok(segments)
    }

    /// A struct-record field name. The `name:` shorthand lexes as a single
    /// `KwKey` that carries its own colon; a bare atom or ident keeps the
    /// colon as a separate token.
    fn parse_field_name(&mut self) -> Result<String, TypeExprError> {
        match self.peek().clone() {
            Tok::KwKey(name) => {
                self.bump();
                Ok(name)
            }
            Tok::Atom(name) | Tok::Ident(name) => {
                self.bump();
                self.expect(&Tok::Colon, "`:` after struct field name")?;
                Ok(name)
            }
            other => Err(self.err(format!("expected a struct field name, got {}", other))),
        }
    }
}
