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
use crate::types::Descr;

/// Module-level type environment: name → declared Descr. Populated by
/// `@type name :: <expr>` declarations in .31.3.
pub type ModuleTypeEnv = HashMap<String, Descr>;

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
    pub params: Vec<Descr>,
    pub result: Descr,
}

/// fz-ul4.31.4 — Lower a `SpecDecl`'s body tokens into concrete Descrs
/// against the module's type env. Surfaces unknown-name errors from
/// `parse_type_expr` directly. Caller is responsible for arity / name
/// validation against the target fn (the parser already enforces this
/// at parse time).
pub fn resolve_spec_decl(
    decl: &crate::ast::SpecDecl,
    env: &ModuleTypeEnv,
) -> Result<ResolvedSpec, TypeExprError> {
    let mut params = Vec::with_capacity(decl.param_body_tokens.len());
    for body in &decl.param_body_tokens {
        let (d, _consumed) = parse_type_expr(body, env)?;
        params.push(d);
    }
    let (result, _consumed) = parse_type_expr(&decl.result_body_tokens, env)?;
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
pub fn build_module_type_env(
    attrs: &[crate::ast::Attribute],
) -> Result<ModuleTypeEnv, TypeExprError> {
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
        return Ok(ModuleTypeEnv::new());
    }
    let mut env: ModuleTypeEnv = ModuleTypeEnv::new();
    // Fixed-point resolve: keep walking until no progress.
    loop {
        let mut progressed = false;
        for name in &order {
            if env.contains_key(name) {
                continue;
            }
            let decl = pending[name];
            match parse_type_expr(&decl.body_tokens, &env) {
                Ok((d, _consumed)) => {
                    env.insert(name.clone(), d);
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
            let body_refs = referenced_names(&decl.body_tokens);
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
            match parse_type_expr(&decl.body_tokens, &env) {
                Ok(_) => unreachable!("env did not grow; this should not parse OK"),
                Err(e) => return Err(e),
            }
        }
    }
    Ok(env)
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
                "nil" | "bool" | "integer" | "float" | "binary" | "atom" | "any" => None,
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
pub fn parse_type_expr(
    tokens: &[Token],
    env: &ModuleTypeEnv,
) -> Result<(Descr, usize), TypeExprError> {
    let mut p = TypeExprParser {
        tokens,
        pos: 0,
        env,
    };
    let d = p.parse_union()?;
    Ok((d, p.pos))
}

struct TypeExprParser<'a> {
    tokens: &'a [Token],
    pos: usize,
    env: &'a ModuleTypeEnv,
}

impl<'a> TypeExprParser<'a> {
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

    fn parse_union(&mut self) -> Result<Descr, TypeExprError> {
        let mut acc = self.parse_primary()?;
        while matches!(self.peek(), Tok::Bar) {
            self.bump();
            let rhs = self.parse_primary()?;
            acc = acc.union(&rhs);
        }
        Ok(acc)
    }

    fn parse_primary(&mut self) -> Result<Descr, TypeExprError> {
        match self.peek().clone() {
            Tok::LBrack => self.parse_list(),
            Tok::LBrace => self.parse_tuple(),
            Tok::LParen => self.parse_paren_or_arrow(),
            Tok::Underscore => {
                self.bump();
                Ok(Descr::any())
            }
            Tok::Atom(name) => {
                self.bump();
                Ok(Descr::atom_lit(name))
            }
            Tok::Int(n) => {
                self.bump();
                Ok(Descr::int_lit(n))
            }
            Tok::Float(f) => {
                self.bump();
                Ok(Descr::float_lit(f))
            }
            Tok::Nil => {
                self.bump();
                Ok(Descr::nil())
            }
            Tok::True => {
                self.bump();
                // bool singleton: bool intersected with literal `true` —
                // fz's basic-bits model has no per-literal bool; the
                // closest user-facing meaning is "the bool type".
                Ok(Descr::bool_t())
            }
            Tok::False => {
                self.bump();
                Ok(Descr::bool_t())
            }
            Tok::Ident(name) => {
                self.bump();
                self.lookup_named(&name)
            }
            Tok::Upper(name) => {
                self.bump();
                self.lookup_named(&name)
            }
            other => Err(self.err(format!("expected a type expression, got {}", other))),
        }
    }

    fn parse_list(&mut self) -> Result<Descr, TypeExprError> {
        self.expect(&Tok::LBrack, "`[`")?;
        // Empty list type `[]` — the empty list singleton (nil).
        if matches!(self.peek(), Tok::RBrack) {
            self.bump();
            return Ok(Descr::nil());
        }
        let elem = self.parse_union()?;
        self.expect(&Tok::RBrack, "`]`")?;
        Ok(Descr::list_of(elem))
    }

    fn parse_tuple(&mut self) -> Result<Descr, TypeExprError> {
        self.expect(&Tok::LBrace, "`{`")?;
        let mut elems: Vec<Descr> = Vec::new();
        if !matches!(self.peek(), Tok::RBrace) {
            elems.push(self.parse_union()?);
            while matches!(self.peek(), Tok::Comma) {
                self.bump();
                elems.push(self.parse_union()?);
            }
        }
        self.expect(&Tok::RBrace, "`}`")?;
        Ok(Descr::tuple_of(elems))
    }

    fn parse_paren_or_arrow(&mut self) -> Result<Descr, TypeExprError> {
        self.expect(&Tok::LParen, "`(`")?;
        let mut elems: Vec<Descr> = Vec::new();
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
            return Ok(Descr::arrow(elems, ret));
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

    fn lookup_named(&self, name: &str) -> Result<Descr, TypeExprError> {
        // Built-in scalar names take precedence over env aliases — a
        // user can't redefine `integer` to mean something else.
        match name {
            "nil" => Ok(Descr::nil()),
            "bool" => Ok(Descr::bool_t()),
            "integer" => Ok(Descr::int()),
            "float" => Ok(Descr::float()),
            "binary" => Ok(Descr::str_t()),
            "atom" => Ok(Descr::atom_top()),
            "any" => Ok(Descr::any()),
            _ => match self.env.get(name) {
                Some(d) => Ok(d.clone()),
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

    fn parse_one(src: &str) -> Result<Descr, TypeExprError> {
        parse_one_with(src, &ModuleTypeEnv::new())
    }

    fn parse_one_with(src: &str, env: &ModuleTypeEnv) -> Result<Descr, TypeExprError> {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let (d, consumed) = parse_type_expr(&toks, env)?;
        // Allow trailing Eof.
        let trailing = toks.len() - consumed;
        if trailing > 1 || (trailing == 1 && !matches!(toks[consumed].tok, Tok::Eof)) {
            return Err(TypeExprError {
                msg: format!("trailing {} token(s) after type expression", trailing),
                span: toks[consumed].span,
            });
        }
        Ok(d)
    }

    #[test]
    fn scalar_names_parse_to_corresponding_descrs() {
        assert!(parse_one("nil").unwrap().is_equiv(&Descr::nil()));
        assert!(parse_one("bool").unwrap().is_equiv(&Descr::bool_t()));
        assert!(parse_one("integer").unwrap().is_equiv(&Descr::int()));
        assert!(parse_one("float").unwrap().is_equiv(&Descr::float()));
        assert!(parse_one("binary").unwrap().is_equiv(&Descr::str_t()));
        assert!(parse_one("atom").unwrap().is_equiv(&Descr::atom_top()));
        assert!(parse_one("any").unwrap().is_equiv(&Descr::any()));
        assert!(parse_one("_").unwrap().is_equiv(&Descr::any()));
    }

    #[test]
    fn atom_literal_parses_to_singleton() {
        assert!(parse_one(":ok").unwrap().is_equiv(&Descr::atom_lit("ok")));
        assert!(
            parse_one(":error")
                .unwrap()
                .is_equiv(&Descr::atom_lit("error"))
        );
    }

    #[test]
    fn int_literal_parses_to_singleton() {
        assert!(parse_one("42").unwrap().is_equiv(&Descr::int_lit(42)));
        assert!(parse_one("0").unwrap().is_equiv(&Descr::int_lit(0)));
    }

    #[test]
    fn float_literal_parses_to_singleton() {
        let d = parse_one("2.5").unwrap();
        assert!(d.is_equiv(&Descr::float_lit(2.5)));
    }

    #[test]
    fn list_of_integer() {
        let d = parse_one("[integer]").unwrap();
        assert!(d.is_equiv(&Descr::list_of(Descr::int())));
    }

    #[test]
    fn empty_list_is_nil() {
        let d = parse_one("[]").unwrap();
        assert!(d.is_equiv(&Descr::nil()));
    }

    #[test]
    fn tuple_two_elements() {
        let d = parse_one("{integer, atom}").unwrap();
        assert!(d.is_equiv(&Descr::tuple_of([Descr::int(), Descr::atom_top()])));
    }

    #[test]
    fn tuple_three_elements_with_literal() {
        let d = parse_one("{:ok, integer, integer}").unwrap();
        let expected = Descr::tuple_of([Descr::atom_lit("ok"), Descr::int(), Descr::int()]);
        assert!(d.is_equiv(&expected));
    }

    #[test]
    fn empty_tuple() {
        let d = parse_one("{}").unwrap();
        assert!(d.is_equiv(&Descr::tuple_of(Vec::<Descr>::new())));
    }

    #[test]
    fn arrow_zero_arg() {
        let d = parse_one("() -> integer").unwrap();
        assert!(d.is_equiv(&Descr::arrow(Vec::<Descr>::new(), Descr::int())));
    }

    #[test]
    fn arrow_one_arg() {
        let d = parse_one("(integer) -> integer").unwrap();
        assert!(d.is_equiv(&Descr::arrow([Descr::int()], Descr::int())));
    }

    #[test]
    fn arrow_two_args() {
        let d = parse_one("(integer, float) -> binary").unwrap();
        assert!(d.is_equiv(&Descr::arrow(
            [Descr::int(), Descr::float()],
            Descr::str_t(),
        )));
    }

    #[test]
    fn paren_grouping_one_element() {
        let d = parse_one("(integer)").unwrap();
        assert!(d.is_equiv(&Descr::int()));
    }

    #[test]
    fn paren_grouping_with_union() {
        let d = parse_one("(integer | float)").unwrap();
        assert!(d.is_equiv(&Descr::int().union(&Descr::float())));
    }

    #[test]
    fn paren_multi_without_arrow_errors() {
        let r = parse_one("(integer, float)");
        assert!(
            r.is_err(),
            "multi-element paren without `->` must error; got {:?}",
            r
        );
    }

    #[test]
    fn union_two_axes() {
        let d = parse_one("integer | float").unwrap();
        assert!(d.is_equiv(&Descr::int().union(&Descr::float())));
    }

    #[test]
    fn union_three_axes_is_left_associative_but_equivalent() {
        let d = parse_one("integer | float | nil").unwrap();
        let expected = Descr::int().union(&Descr::float()).union(&Descr::nil());
        assert!(d.is_equiv(&expected));
    }

    #[test]
    fn union_with_atom_literals() {
        let d = parse_one(":ok | :error").unwrap();
        assert!(d.is_equiv(&Descr::atom_lit("ok").union(&Descr::atom_lit("error"))));
    }

    #[test]
    fn list_of_union() {
        let d = parse_one("[integer | float]").unwrap();
        assert!(d.is_equiv(&Descr::list_of(Descr::int().union(&Descr::float()))));
    }

    #[test]
    fn nested_tuple_inside_list() {
        let d = parse_one("[{:ok, integer}]").unwrap();
        let expected = Descr::list_of(Descr::tuple_of([Descr::atom_lit("ok"), Descr::int()]));
        assert!(d.is_equiv(&expected));
    }

    #[test]
    fn arrow_taking_arrow_argument() {
        let d = parse_one("((integer) -> integer, [integer]) -> [integer]").unwrap();
        let f = Descr::arrow([Descr::int()], Descr::int());
        let l = Descr::list_of(Descr::int());
        let expected = Descr::arrow([f, l.clone()], l);
        assert!(d.is_equiv(&expected));
    }

    #[test]
    fn named_ref_resolves_via_env() {
        let mut env = ModuleTypeEnv::new();
        env.insert("id".to_string(), Descr::int());
        let d = parse_one_with("id", &env).unwrap();
        assert!(d.is_equiv(&Descr::int()));
    }

    #[test]
    fn named_ref_used_in_arrow_via_env() {
        let mut env = ModuleTypeEnv::new();
        env.insert("id".to_string(), Descr::int());
        let d = parse_one_with("(id) -> id", &env).unwrap();
        assert!(d.is_equiv(&Descr::arrow([Descr::int()], Descr::int())));
    }

    #[test]
    fn unknown_name_with_empty_env_errors() {
        let r = parse_one("nonesuch");
        assert!(r.is_err());
        let e = r.unwrap_err();
        assert!(e.msg.contains("unknown type name"), "msg = {}", e.msg);
    }

    #[test]
    fn builtin_name_takes_precedence_over_alias() {
        // A user-defined alias must NOT shadow a builtin scalar name.
        let mut env = ModuleTypeEnv::new();
        env.insert("integer".to_string(), Descr::float());
        let d = parse_one_with("integer", &env).unwrap();
        assert!(
            d.is_equiv(&Descr::int()),
            "builtin `integer` must resolve to int regardless of env shadow"
        );
    }

    #[test]
    fn malformed_unclosed_list_errors() {
        assert!(parse_one("[integer").is_err());
    }

    #[test]
    fn malformed_unclosed_tuple_errors() {
        assert!(parse_one("{integer, atom").is_err());
    }

    #[test]
    fn malformed_unclosed_paren_errors() {
        assert!(parse_one("(integer").is_err());
    }

    #[test]
    fn trailing_tokens_error() {
        let r = parse_one("integer foo");
        assert!(r.is_err(), "trailing tokens must be rejected; got {:?}", r);
    }

    #[test]
    fn primary_position_rejects_bar() {
        // `| integer` is malformed — `|` is a binary operator.
        assert!(parse_one("| integer").is_err());
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
            body_tokens,
            span: Span::DUMMY,
        })
    }

    #[test]
    fn build_env_resolves_simple_alias() {
        let attrs = vec![type_alias_attr("id", "integer")];
        let env = build_module_type_env(&attrs).unwrap();
        assert!(env.get("id").unwrap().is_equiv(&Descr::int()));
    }

    #[test]
    fn build_env_resolves_alias_of_alias_in_either_order() {
        // Declare in forward order: a refs b, b is plain.
        let attrs = vec![type_alias_attr("a", "b"), type_alias_attr("b", "integer")];
        let env = build_module_type_env(&attrs).unwrap();
        assert!(env.get("a").unwrap().is_equiv(&Descr::int()));
        assert!(env.get("b").unwrap().is_equiv(&Descr::int()));
    }

    #[test]
    fn build_env_resolves_composite_alias() {
        // pair := {id, id}; id := integer.
        let attrs = vec![
            type_alias_attr("pair", "{id, id}"),
            type_alias_attr("id", "integer"),
        ];
        let env = build_module_type_env(&attrs).unwrap();
        let expected = Descr::tuple_of([Descr::int(), Descr::int()]);
        assert!(env.get("pair").unwrap().is_equiv(&expected));
    }

    #[test]
    fn build_env_detects_simple_cycle() {
        let attrs = vec![type_alias_attr("a", "b"), type_alias_attr("b", "a")];
        let err = build_module_type_env(&attrs).unwrap_err();
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
        let err = build_module_type_env(&attrs).unwrap_err();
        assert!(
            err.msg.contains("cycle"),
            "expected cycle diag, got: {}",
            err.msg
        );
    }

    #[test]
    fn build_env_rejects_unknown_reference() {
        let attrs = vec![type_alias_attr("foo", "nonesuch")];
        let err = build_module_type_env(&attrs).unwrap_err();
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
        let err = build_module_type_env(&attrs).unwrap_err();
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
        let env = build_module_type_env(&attrs).unwrap();
        assert_eq!(env.len(), 1);
        assert!(env.get("id").unwrap().is_equiv(&Descr::int()));
    }

    #[test]
    fn build_env_empty_for_module_without_aliases() {
        let attrs: Vec<crate::ast::Attribute> = vec![];
        let env = build_module_type_env(&attrs).unwrap();
        assert!(env.is_empty());
    }

    #[test]
    fn build_env_resolves_arrow_using_alias() {
        let attrs = vec![
            type_alias_attr("id", "integer"),
            type_alias_attr("idfn", "(id) -> id"),
        ];
        let env = build_module_type_env(&attrs).unwrap();
        let expected = Descr::arrow([Descr::int()], Descr::int());
        assert!(env.get("idfn").unwrap().is_equiv(&expected));
    }

    #[test]
    fn consumed_count_reports_correct_position() {
        // Parser returns how many tokens it consumed, so callers can
        // continue parsing whatever follows (e.g., the `::` separator
        // in `@spec name(T) :: R`).
        let toks = Lexer::new("integer foo").tokenize().unwrap();
        let env = ModuleTypeEnv::new();
        let (d, consumed) = parse_type_expr(&toks, &env).unwrap();
        assert!(d.is_equiv(&Descr::int()));
        assert_eq!(consumed, 1, "consumed only the `integer` token");
    }
}
