use super::*;
use crate::modules::identity::ModuleName;

impl Parser {
    pub(super) fn parse_items_until(
        &mut self,
        terminators: &[Tok],
    ) -> PR<(Vec<Rc<Item>>, Vec<Attribute>)> {
        let mut items: Vec<Rc<Item>> = Vec::new();
        let mut order: Vec<(String, usize)> = Vec::new();
        let mut groups: std::collections::HashMap<(String, usize), FnDef> =
            std::collections::HashMap::new();
        // fz-ul4.31.2 — `moduledoc_attr` and `pending_fn_attrs` accumulate
        // structured `Attribute`s. The single-string `doc`/`moduledoc`
        // model is gone; .31.3/.31.4 extend the Attribute enum.
        let mut moduledoc_attr: Option<Attribute> = None;
        let mut module_aliases: Vec<Attribute> = Vec::new();
        let mut pending_fn_attrs: Vec<Attribute> = Vec::new();

        self.skip_newlines();
        while !self.peek_in(terminators) {
            match self.peek() {
                Tok::At => {
                    let attr = self.parse_attribute()?;
                    match &attr {
                        Attribute::ModuleDoc(_) => {
                            if moduledoc_attr.is_some() {
                                return self.err("duplicate @moduledoc".to_string());
                            }
                            moduledoc_attr = Some(attr);
                        }
                        Attribute::Doc(_) => {
                            if pending_fn_attrs.iter().any(
                                |a| matches!(a, Attribute::Doc(_)))
                            {
                                return self.err("duplicate @doc before fn".to_string());
                            }
                            pending_fn_attrs.push(attr);
                        }
                        Attribute::Spec(_) => {
                            // Multiple adjacent specs form an overload set for
                            // the following fn. Name/arity checks happen once
                            // the fn head is known.
                            pending_fn_attrs.push(attr);
                        }
                        Attribute::TypeAlias(_) => {
                            // fz-ul4.31.3 — @type belongs to the
                            // enclosing module's attrs alongside
                            // @moduledoc (module-level scope, not a
                            // pending-for-fn decoration).
                            module_aliases.push(attr);
                        }
                    }
                }
                Tok::Defmodule => {
                    flush_fn_groups(&mut items, &mut order, &mut groups);
                    let m = self.parse_module()?;
                    items.push(Rc::new(Item::Module(m)));
                }
                Tok::Defstruct => {
                    flush_fn_groups(&mut items, &mut order, &mut groups);
                    let s = self.parse_struct_def()?;
                    items.push(Rc::new(Item::Struct(s)));
                }
                Tok::Defprotocol => {
                    flush_fn_groups(&mut items, &mut order, &mut groups);
                    let protocol = self.parse_protocol()?;
                    items.push(Rc::new(Item::Protocol(protocol)));
                }
                Tok::Defimpl => {
                    flush_fn_groups(&mut items, &mut order, &mut groups);
                    let protocol_impl = self.parse_protocol_impl()?;
                    items.push(Rc::new(Item::ProtocolImpl(protocol_impl)));
                }
                Tok::Alias => {
                    flush_fn_groups(&mut items, &mut order, &mut groups);
                    let a = self.parse_alias()?;
                    items.push(Rc::new(a));
                }
                Tok::Import => {
                    flush_fn_groups(&mut items, &mut order, &mut groups);
                    let i = self.parse_import()?;
                    items.push(Rc::new(i));
                }
                Tok::Extern => {
                    flush_fn_groups(&mut items, &mut order, &mut groups);
                    let _attrs = std::mem::take(&mut pending_fn_attrs);
                    self.bump(); // consume `extern`
                    let def = self.parse_extern_item()?;
                    items.push(Rc::new(Item::Fn(def)));
                }
                Tok::Fn | Tok::Fnp | Tok::Defmacro => {
                    let start = self.cur_span();
                    let (name, name_span, clause, is_macro, is_private) =
                        self.parse_fn_clause()?;
                    let arity = clause.params.len();
                    let key = (name.clone(), arity);
                    if let Some(def) = groups.get_mut(&key) {
                        if def.is_macro != is_macro {
                            return self.err(format!("`{}` declared as both fn and defmacro", name));
                        }
                        if def.is_private != is_private {
                            return self.err(format!("`{}` declared as both fn and fnp", name));
                        }
                        // extend the def's span to cover this clause too
                        def.span = def.span.merge(clause.span);
                        def.clauses.push(clause);
                    } else {
                        let attrs = std::mem::take(&mut pending_fn_attrs);
                        // fz-ul4.31.4 — @spec name + arity must match
                        // the following fn's first clause.
                        for a in &attrs {
                            if let Attribute::Spec(s) = a {
                                if s.name != name {
                                    return self.err(format!(
                                        "@spec name `{}` doesn't match \
                                         following fn `{}`",
                                        s.name, name));
                                }
                                if s.param_body_tokens.len() != arity {
                                    return self.err(format!(
                                        "@spec arity {} doesn't match fn \
                                         `{}/{}`",
                                        s.param_body_tokens.len(),
                                        name,
                                        arity));
                                }
                            }
                        }
                        let clause_span = clause.span;
                        order.push(key.clone());
                        groups.insert(key, FnDef {
                            name,
                            name_span,
                            clauses: vec![clause],
                            is_macro,
                            is_private,
                            extern_abi: None,
                            extern_params: vec![],
                            extern_ret_tokens: TypeExprBody(vec![]),
                            variadic: false,
                            attrs,
                            span: start.merge(clause_span),
                        });
                    }
                }
                Tok::Ident(_) => {
                    flush_fn_groups(&mut items, &mut order, &mut groups);
                    let start = self.cur_span();
                    let e = self.parse_expr()?;
                    let (name, name_span, args): (String, Span, Vec<Spanned<Expr>>) =
                        match (e.node, e.span) {
                            (Expr::Call(callee, args), _) => match (callee.node, callee.span) {
                                (Expr::Var(n), cspan) => (n, cspan, args),
                                _ => return self.err(
                                    "item-level call must have a bare-name callee"),
                            },
                            _ => return self.err(
                                "expected a macro call at item position"),
                        };
                    items.push(Rc::new(Item::MacroCall {
                        name,
                        name_span,
                        args,
                        parent_module: None,
                        span: self.finish(start),
                    }));
                }
                _ => return self.err(format!(
                    "expected `fn`, `fnp`, `defmacro`, `defmodule`, `defprotocol`, `defimpl`, `alias`, `import`, `@`, or a macro call, got {:?}",
                    self.peek()
                )),
            }
            self.skip_newlines();
        }
        flush_fn_groups(&mut items, &mut order, &mut groups);
        if !pending_fn_attrs.is_empty() {
            let kind = match &pending_fn_attrs[0] {
                Attribute::Doc(_) => "@doc",
                Attribute::Spec(_) => "@spec",
                _ => "attribute",
            };
            return self.incomplete(format!("{} not followed by a fn, fnp, or defmacro", kind));
        }
        let mut module_attrs: Vec<Attribute> = moduledoc_attr.into_iter().collect();
        module_attrs.extend(module_aliases);
        Ok((items, module_attrs))
    }

    /// `@<ident> <string>`. Recognizes `@doc` and `@moduledoc`; rejects
    /// unknown attribute names. fz-ul4.31.3 / .31.4 extend the
    /// `Attribute` enum (and this fn) for `@type` and `@spec`.
    pub(super) fn parse_attribute(&mut self) -> PR<Attribute> {
        self.expect(&Tok::At, "`@`")?;
        let name = match self.bump() {
            Tok::Ident(n) => n,
            // `type` is a reserved keyword token from the lexer (.18.6
            // era), so allow it here for `@type` to lex.
            Tok::Type => "type".to_string(),
            other => {
                return self.err(format!(
                    "expected attribute name after `@`, got {:?}",
                    other
                ));
            }
        };
        match name.as_str() {
            "doc" | "moduledoc" => {
                let value = match self.bump() {
                    Tok::Binary(bytes) => match String::from_utf8(bytes) {
                        Ok(s) => s,
                        Err(e) => {
                            return self.err(format!("@{} requires UTF-8 text: {}", name, e));
                        }
                    },
                    other => {
                        return self.err(format!(
                            "expected string value after `@{}`, got {:?}",
                            name, other
                        ));
                    }
                };
                if name == "doc" {
                    Ok(Attribute::Doc(value))
                } else {
                    Ok(Attribute::ModuleDoc(value))
                }
            }
            "spec" => {
                // fz-ul4.31.4: `@spec name(T1, T2) :: R`. Bodies stored
                // as raw tokens; `SpecDecl::resolve` lowers them to
                // types against the module's ModuleTypeEnv in .31.5.
                let spec_name = match self.bump() {
                    Tok::Ident(n) => n,
                    other => {
                        return self
                            .err(format!("expected fn name after `@spec`, got {:?}", other));
                    }
                };
                self.expect(&Tok::LParen, "`(`")?;
                let mut param_body_tokens: Vec<TypeExprBody> = Vec::new();
                if !matches!(self.peek(), Tok::RParen) {
                    loop {
                        let toks = self.collect_spec_param_type_tokens();
                        if toks.is_empty() {
                            return self
                                .err("expected type expression in @spec param list".to_string());
                        }
                        param_body_tokens.push(TypeExprBody(toks));
                        if matches!(self.peek(), Tok::Comma) {
                            self.bump();
                            continue;
                        }
                        break;
                    }
                }
                self.expect(&Tok::RParen, "`)`")?;
                self.expect(&Tok::ColonColon, "`::`")?;
                let result_body_tokens = self.collect_type_body_tokens();
                if result_body_tokens.is_empty() {
                    return self
                        .err("expected result type expression after `::` in @spec".to_string());
                }
                let mut constraints = Vec::new();
                if self.eat(&Tok::When) {
                    loop {
                        let var = match self.bump() {
                            Tok::Ident(n) | Tok::KwKey(n) => n,
                            other => {
                                return self.err(format!(
                                    "expected type variable after `when`, got {:?}",
                                    other
                                ));
                            }
                        };
                        if !matches!(self.toks[self.pos - 1].tok, Tok::KwKey(_)) {
                            self.expect(&Tok::Colon, "`:`")?;
                        }
                        let toks = self.collect_spec_param_type_tokens();
                        if toks.is_empty() {
                            return self.err(format!(
                                "expected constraint type expression after `{}:`",
                                var
                            ));
                        }
                        constraints.push((var, TypeExprBody(toks)));
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                Ok(Attribute::Spec(SpecDecl {
                    name: spec_name,
                    param_body_tokens,
                    result_body_tokens: TypeExprBody(result_body_tokens),
                    constraints,
                }))
            }
            "type" => {
                // fz-ul4.31.3: `@type Name :: <type-expr>`. Body parsed
                // later via `type_expr::build_module_type_env` so forward
                // references between aliases in the same module resolve.
                let start = self.cur_span();
                let alias_name_span = self.cur_span();
                let alias_name = match self.bump() {
                    Tok::Upper(n) | Tok::Ident(n) => n,
                    other => {
                        return self.err(format!(
                            "expected type-alias name after `@type`, got {:?}",
                            other
                        ));
                    }
                };
                let mut params = Vec::new();
                if self.eat(&Tok::LParen) {
                    if !matches!(self.peek(), Tok::RParen) {
                        loop {
                            let param = match self.bump() {
                                Tok::Ident(n) => n,
                                other => {
                                    return self.err(format!(
                                        "expected type parameter name in @type head, got {:?}",
                                        other
                                    ));
                                }
                            };
                            params.push(param);
                            if !self.eat(&Tok::Comma) {
                                break;
                            }
                        }
                    }
                    self.expect(&Tok::RParen, "`)` after @type parameters")?;
                }
                self.expect(&Tok::ColonColon, "`::`")?;
                // Collect tokens until a top-level newline / eof / end.
                let body_tokens = self.collect_type_body_tokens();
                let end_span = self.cur_span();
                Ok(Attribute::TypeAlias(TypeAliasDecl {
                    name: alias_name,
                    name_span: alias_name_span,
                    params,
                    body_tokens: TypeExprBody(body_tokens),
                    span: start.merge(end_span),
                }))
            }
            other => self.err(format!(
                "unknown attribute `@{}` (only @doc, @moduledoc, @type supported)",
                other
            )),
        }
    }

    pub(super) fn collect_spec_param_type_tokens(&mut self) -> Vec<Token> {
        self.collect_balanced_type_tokens(TypeTokenBoundary::SpecParam)
    }

    pub(super) fn collect_fn_param_type_tokens(&mut self) -> Vec<Token> {
        self.collect_balanced_type_tokens(TypeTokenBoundary::FnParam)
    }

    /// Parse function parameter list with optional type annotations (`x :: T`).
    /// Returns (patterns, per-param type token vecs). Called from `parse_fn_clause`.
    #[allow(clippy::type_complexity)]
    pub(super) fn parse_fn_params(
        &mut self,
    ) -> PR<(Vec<Spanned<Pattern>>, Vec<Option<TypeExprBody>>)> {
        let mut patterns = Vec::new();
        let mut types: Vec<Option<TypeExprBody>> = Vec::new();
        self.skip_newlines();
        if matches!(self.peek(), Tok::RParen) {
            return Ok((patterns, types));
        }
        loop {
            patterns.push(self.parse_pattern()?);
            self.skip_newlines();
            let ty = if self.eat(&Tok::ColonColon) {
                let toks = self.collect_fn_param_type_tokens();
                if toks.is_empty() {
                    return self.err("expected type expression after `::`");
                }
                Some(TypeExprBody(toks))
            } else {
                None
            };
            types.push(ty);
            self.skip_newlines();
            if !self.eat(&Tok::Comma) {
                break;
            }
            self.skip_newlines();
        }
        Ok((patterns, types))
    }

    pub(super) fn collect_type_body_tokens(&mut self) -> Vec<Token> {
        self.collect_balanced_type_tokens(TypeTokenBoundary::TypeBody)
    }

    fn collect_balanced_type_tokens(&mut self, boundary: TypeTokenBoundary) -> Vec<Token> {
        let mut out: Vec<Token> = Vec::new();
        let mut depth: i32 = 0;
        loop {
            if boundary.stops_before(self.peek(), depth) {
                break;
            }
            match self.peek() {
                Tok::LParen | Tok::LBrack | Tok::LBrace => {
                    depth += 1;
                    out.push(self.toks[self.pos].clone());
                    self.pos += 1;
                }
                Tok::RParen | Tok::RBrack | Tok::RBrace => {
                    depth -= 1;
                    out.push(self.toks[self.pos].clone());
                    self.pos += 1;
                    if depth < 0 && boundary.stops_after_unmatched_close() {
                        break;
                    }
                }
                _ => {
                    out.push(self.toks[self.pos].clone());
                    self.pos += 1;
                }
            }
        }
        out
    }

    pub(super) fn peek_in(&self, terminators: &[Tok]) -> bool {
        terminators
            .iter()
            .any(|t| std::mem::discriminant(self.peek()) == std::mem::discriminant(t))
    }

    /// Parse one fn, fnp, or defmacro clause.
    /// Returns (name, name_span, clause, is_macro, is_private).
    pub(super) fn parse_fn_clause(&mut self) -> PR<(String, Span, FnClause, bool, bool)> {
        let start = self.cur_span();
        let (is_macro, is_private) = match self.peek() {
            Tok::Defmacro => {
                self.bump();
                (true, false)
            }
            Tok::Fn => {
                self.bump();
                (false, false)
            }
            Tok::Fnp => {
                self.bump();
                (false, true)
            }
            _ => {
                return self.err(format!(
                    "expected `fn`, `fnp`, or `defmacro`, got {:?}",
                    self.peek()
                ));
            }
        };
        let name_span = self.cur_span();
        let name = match self.bump() {
            Tok::Ident(n) => n,
            other => return self.err(format!("expected function name, got {:?}", other)),
        };
        self.expect(&Tok::LParen, "`(`")?;
        let (params, param_annotations) = self.parse_fn_params()?;
        self.expect(&Tok::RParen, "`)`")?;

        let guard = if matches!(self.peek(), Tok::When) {
            self.bump();
            Some(self.with_no_trailing_do(|p| p.parse_expr())?)
        } else {
            None
        };

        let body = if matches!(self.peek(), Tok::Comma)
            && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do")
        {
            self.bump();
            self.bump();
            self.parse_expr()?
        } else if matches!(self.peek(), Tok::Do) {
            self.bump();
            self.skip_newlines();
            let blk = self.parse_block_until(&[Tok::End])?;
            self.expect(&Tok::End, "`end`")?;
            blk
        } else {
            return self.err(format!(
                "expected `do` or `, do:` after function head, got {:?}",
                self.peek()
            ));
        };
        let span = self.finish(start);
        Ok((
            name,
            name_span,
            FnClause {
                params,
                param_annotations,
                guard,
                body,
                span,
            },
            is_macro,
            is_private,
        ))
    }

    /// `extern "C" fn name(type, type) :: RetType`
    /// Caller has already consumed `Tok::Extern`.
    pub(super) fn parse_extern_item(&mut self) -> PR<FnDef> {
        let start = self.cur_span();
        let abi = match self.bump() {
            Tok::Binary(bytes) => match String::from_utf8(bytes) {
                Ok(s) => s,
                Err(e) => {
                    return self.err(format!("extern ABI string must be valid UTF-8: {}", e));
                }
            },
            other => {
                return self.err(format!(
                    "expected ABI string after `extern`, got {:?}",
                    other
                ));
            }
        };
        self.expect(&Tok::Fn, "`fn` after extern ABI string")?;
        let name_span = self.cur_span();
        // fz-y3k — accept an optional single `lib::` prefix on the extern name.
        // The full string ("libc::open") is the fz-visible identifier; the
        // bare last segment ("open") is what `ir_lower` records as the C
        // symbol. Anything more elaborate (multi-segment paths, generics)
        // is rejected here.
        let first = match self.bump() {
            Tok::Ident(n) => n,
            other => return self.err(format!("expected function name, got {:?}", other)),
        };
        let name = if matches!(self.peek(), Tok::ColonColon) {
            self.bump();
            match self.bump() {
                Tok::Ident(n) => format!("{}::{}", first, n),
                other => {
                    return self.err(format!(
                        "expected extern symbol name after `{}::`, got {:?}",
                        first, other
                    ));
                }
            }
        } else {
            first
        };
        self.expect(&Tok::LParen, "`(`")?;
        // Extern param types are identifiers. Two accepted shapes per param:
        //   - bare type:        `cstring`
        //   - named:            `path :: cstring`  (the name is documentation
        //                                          only — it's discarded)
        // The collected `params` Vec holds the *type* name for each slot.
        // Type expressions that themselves contain brackets
        // still capture the first ident as the type — the depth counter avoids
        // bracketed inner idents overriding the outer type.
        let mut variadic = false;
        let extern_params: Vec<String> = if matches!(self.peek(), Tok::RParen) {
            vec![]
        } else {
            let mut params: Vec<String> = Vec::new();
            let mut depth = 0usize;
            let mut current_name: Option<String> = None;
            let mut after_dbl_colon = false;
            loop {
                match self.peek() {
                    Tok::Ellipsis if depth == 0 => {
                        if current_name.is_some() {
                            return self.err("expected `,` before extern variadic `...`");
                        }
                        variadic = true;
                        self.bump();
                        self.skip_newlines();
                        if !matches!(self.peek(), Tok::RParen) {
                            return self.err("extern variadic `...` must be the final parameter");
                        }
                        break;
                    }
                    Tok::LParen | Tok::LBrace | Tok::LBrack => {
                        depth += 1;
                        self.bump();
                    }
                    Tok::RParen | Tok::RBrace | Tok::RBrack if depth > 0 => {
                        depth -= 1;
                        self.bump();
                    }
                    Tok::RParen => {
                        params.push(current_name.take().unwrap_or_default());
                        break;
                    }
                    Tok::Comma if depth == 0 => {
                        params.push(current_name.take().unwrap_or_default());
                        after_dbl_colon = false;
                        self.bump();
                    }
                    Tok::ColonColon if depth == 0 => {
                        // fz-y3k — named-typed param: `<name> :: <type>`. The
                        // ident we already captured is the param name; the
                        // next top-level ident is the type and overrides.
                        after_dbl_colon = true;
                        self.bump();
                    }
                    Tok::Eof | Tok::Newline => {
                        return self.err("unexpected end of extern parameter list");
                    }
                    Tok::Nil => {
                        if depth == 0 && (current_name.is_none() || after_dbl_colon) {
                            current_name = Some("nil".into());
                            after_dbl_colon = false;
                        }
                        self.bump();
                    }
                    Tok::Ident(n) | Tok::Upper(n) => {
                        let name = n.clone();
                        if depth == 0 && (current_name.is_none() || after_dbl_colon) {
                            current_name = Some(name);
                            after_dbl_colon = false;
                        }
                        self.bump();
                    }
                    _ => {
                        self.bump();
                    }
                }
            }
            params
        };
        self.expect(&Tok::RParen, "`)`")?;
        self.expect(&Tok::ColonColon, "`::`")?;
        let mut extern_ret_tokens = Vec::new();
        while !matches!(self.peek(), Tok::Newline | Tok::Eof) {
            extern_ret_tokens.push(self.toks[self.pos].clone());
            self.bump();
        }
        let span = self.finish(start);
        Ok(FnDef {
            name,
            name_span,
            clauses: vec![],
            is_macro: false,
            is_private: false,
            extern_abi: Some(abi),
            extern_params,
            extern_ret_tokens: TypeExprBody(extern_ret_tokens),
            variadic,
            attrs: vec![],
            span,
        })
    }

    /// `alias A.B.C` or `alias A.B.C, as: D`.
    pub(super) fn parse_alias(&mut self) -> PR<Item> {
        let start = self.cur_span();
        self.expect(&Tok::Alias, "`alias`")?;
        let mut path: Vec<String> = Vec::new();
        match self.bump() {
            Tok::Upper(n) => path.push(n),
            other => {
                return self.err(format!(
                    "expected uppercase module path after `alias`, got {:?}",
                    other
                ));
            }
        }
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.bump() {
                Tok::Upper(n) => path.push(n),
                other => {
                    return self.err(format!(
                        "expected uppercase segment after `.` in alias path, got {:?}",
                        other
                    ));
                }
            }
        }
        let module_name = crate::modules::identity::ModuleName::from_segments(path);
        let as_name = if matches!(self.peek(), Tok::Comma)
            && matches!(self.peek_at(1), Tok::KwKey(s) if s == "as")
        {
            self.bump(); // ,
            self.bump(); // as:
            match self.bump() {
                Tok::Upper(n) => n,
                other => {
                    return self.err(format!(
                        "expected uppercase nickname after `as:`, got {:?}",
                        other
                    ));
                }
            }
        } else {
            module_name.last_segment().to_string()
        };
        Ok(Item::Alias {
            full_path: module_name,
            as_name,
            span: self.finish(start),
        })
    }

    /// `import Mod` | `import Mod, only: [f: 1, g: 2]` | `import Mod, except: [...]`.
    pub(super) fn parse_import(&mut self) -> PR<Item> {
        let start = self.cur_span();
        self.expect(&Tok::Import, "`import`")?;
        let mut path: Vec<String> = Vec::new();
        match self.bump() {
            Tok::Upper(n) => path.push(n),
            other => {
                return self.err(format!(
                    "expected uppercase module path after `import`, got {:?}",
                    other
                ));
            }
        }
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.bump() {
                Tok::Upper(n) => path.push(n),
                other => {
                    return self.err(format!(
                        "expected uppercase segment after `.`, got {:?}",
                        other
                    ));
                }
            }
        }
        let mut only: Option<Vec<(String, usize)>> = None;
        let mut except: Option<Vec<(String, usize)>> = None;
        if matches!(self.peek(), Tok::Comma)
            && let Tok::KwKey(s) = self.peek_at(1)
            && (s == "only" || s == "except")
        {
            self.bump();
            let kind = match self.bump() {
                Tok::KwKey(k) => k,
                _ => unreachable!(),
            };
            let pairs = self.parse_arity_kw_list()?;
            if kind == "only" {
                only = Some(pairs);
            } else {
                except = Some(pairs);
            }
        }
        Ok(Item::Import {
            path: crate::modules::identity::ModuleName::from_segments(path),
            only,
            except,
            span: self.finish(start),
        })
    }

    pub(super) fn parse_arity_kw_list(&mut self) -> PR<Vec<(String, usize)>> {
        self.expect(&Tok::LBrack, "`[`")?;
        let mut out: Vec<(String, usize)> = Vec::new();
        self.skip_newlines();
        if !matches!(self.peek(), Tok::RBrack) {
            loop {
                let name = match self.bump() {
                    Tok::KwKey(k) => k,
                    other => {
                        return self.err(format!(
                            "expected name: in import filter list, got {:?}",
                            other
                        ));
                    }
                };
                let arity = match self.bump() {
                    Tok::Int(n) if n >= 0 => n as usize,
                    other => {
                        return self.err(format!(
                            "expected non-negative arity after `{}:`, got {:?}",
                            name, other
                        ));
                    }
                };
                out.push((name, arity));
                self.skip_newlines();
                if !self.eat(&Tok::Comma) {
                    break;
                }
                self.skip_newlines();
            }
        }
        self.expect(&Tok::RBrack, "`]`")?;
        Ok(out)
    }

    pub(super) fn parse_upper_path(&mut self, context: &str) -> PR<(ModuleName, Span)> {
        let span = self.cur_span();
        let mut path: Vec<String> = Vec::new();
        match self.bump() {
            Tok::Upper(n) => path.push(n),
            other => {
                return self.err(format!(
                    "expected uppercase {} path, got {:?}",
                    context, other
                ));
            }
        }
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.bump() {
                Tok::Upper(n) => path.push(n),
                other => {
                    return self.err(format!(
                        "expected uppercase segment after `.` in {} path, got {:?}",
                        context, other
                    ));
                }
            }
        }
        Ok((ModuleName::from_segments(path), span))
    }

    pub(super) fn parse_protocol(&mut self) -> PR<ProtocolDef> {
        let start = self.cur_span();
        self.expect(&Tok::Defprotocol, "`defprotocol`")?;
        let (name, name_span) = self.parse_upper_path("protocol")?;
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();

        let mut callbacks = Vec::new();
        let mut attrs = Vec::new();
        let mut pending_attrs = Vec::new();
        while !matches!(self.peek(), Tok::End | Tok::Eof) {
            match self.peek() {
                Tok::At => {
                    let attr = self.parse_attribute()?;
                    match attr {
                        Attribute::ModuleDoc(_) | Attribute::TypeAlias(_) => attrs.push(attr),
                        Attribute::Doc(_) | Attribute::Spec(_) => pending_attrs.push(attr),
                    }
                }
                Tok::Fn => {
                    let callback =
                        self.parse_protocol_callback(std::mem::take(&mut pending_attrs))?;
                    callbacks.push(callback);
                }
                other => {
                    return self.err(format!(
                        "expected `fn`, `@`, or `end` in protocol body, got {:?}",
                        other
                    ));
                }
            }
            self.skip_newlines();
        }
        if !pending_attrs.is_empty() {
            return self.incomplete("protocol callback attribute not followed by `fn`");
        }
        self.expect(&Tok::End, "`end`")?;
        Ok(ProtocolDef {
            name,
            name_span,
            callbacks,
            attrs,
            span: self.finish(start),
        })
    }

    pub(super) fn parse_struct_def(&mut self) -> PR<StructDef> {
        let start = self.cur_span();
        self.expect(&Tok::Defstruct, "`defstruct`")?;
        self.expect(&Tok::LBrack, "`[`")?;
        let mut fields = Vec::new();
        self.skip_newlines();
        if !matches!(self.peek(), Tok::RBrack) {
            loop {
                let field = match self.bump() {
                    Tok::Atom(name) | Tok::Ident(name) | Tok::KwKey(name) => name,
                    other => {
                        return self
                            .err(format!("expected field atom in defstruct, got {:?}", other));
                    }
                };
                fields.push(field);
                self.skip_newlines();
                if !self.eat(&Tok::Comma) {
                    break;
                }
                self.skip_newlines();
            }
        }
        self.expect(&Tok::RBrack, "`]`")?;
        Ok(StructDef {
            module: ModuleName::from_segments(vec!["__unresolved_struct__".to_string()]),
            fields,
            span: self.finish(start),
        })
    }

    fn parse_protocol_callback(&mut self, attrs: Vec<Attribute>) -> PR<ProtocolCallback> {
        let start = self.cur_span();
        self.expect(&Tok::Fn, "`fn`")?;
        let name_span = self.cur_span();
        let name = match self.bump() {
            Tok::Ident(n) => n,
            other => return self.err(format!("expected protocol callback name, got {:?}", other)),
        };
        self.expect(&Tok::LParen, "`(`")?;
        let (params, _) = self.parse_fn_params()?;
        self.expect(&Tok::RParen, "`)`")?;
        if matches!(self.peek(), Tok::When) {
            return self.err("protocol callback declarations cannot have guards");
        }
        if matches!(self.peek(), Tok::Do)
            || (matches!(self.peek(), Tok::Comma)
                && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do"))
        {
            return self.err("protocol callback declarations cannot have bodies");
        }
        for attr in &attrs {
            if let Attribute::Spec(spec) = attr {
                if spec.name != name {
                    return self.err(format!(
                        "@spec name `{}` doesn't match protocol callback `{}`",
                        spec.name, name
                    ));
                }
                if spec.param_body_tokens.len() != params.len() {
                    return self.err(format!(
                        "@spec arity {} doesn't match protocol callback `{}/{}`",
                        spec.param_body_tokens.len(),
                        name,
                        params.len()
                    ));
                }
            }
        }
        Ok(ProtocolCallback {
            name,
            name_span,
            arity: params.len(),
            attrs,
            span: self.finish(start),
        })
    }

    pub(super) fn parse_protocol_impl(&mut self) -> PR<ProtocolImplDef> {
        let start = self.cur_span();
        self.expect(&Tok::Defimpl, "`defimpl`")?;
        let (protocol, protocol_span) = self.parse_upper_path("protocol")?;
        self.expect(&Tok::Comma, "`,`")?;
        match self.bump() {
            Tok::KwKey(k) if k == "for" => {}
            other => {
                return self.err(format!(
                    "expected `for:` after protocol name in defimpl, got {:?}",
                    other
                ));
            }
        }
        let (target_path, target_span) = self.parse_upper_path("implementation target")?;
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let (items, attrs) = self.parse_items_until(&[Tok::End])?;
        self.expect(&Tok::End, "`end`")?;
        Ok(ProtocolImplDef {
            protocol,
            protocol_span,
            target: ProtocolImplTarget {
                path: target_path,
                span: target_span,
            },
            items,
            attrs,
            span: self.finish(start),
        })
    }

    pub(super) fn parse_module(&mut self) -> PR<ModuleDef> {
        let start = self.cur_span();
        self.expect(&Tok::Defmodule, "`defmodule`")?;
        let (name_path, name_span) = self.parse_upper_path("module")?;
        let name = name_path.dotted();
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let (items, attrs) = self.parse_items_until(&[Tok::End])?;
        self.expect(&Tok::End, "`end`")?;
        Ok(ModuleDef {
            name,
            name_span,
            items,
            attrs,
            span: self.finish(start),
        })
    }
}

#[derive(Clone, Copy)]
enum TypeTokenBoundary {
    SpecParam,
    FnParam,
    TypeBody,
}

impl TypeTokenBoundary {
    fn stops_before(self, tok: &Tok, depth: i32) -> bool {
        match self {
            Self::SpecParam => {
                matches!(tok, Tok::Eof | Tok::Newline)
                    || (depth == 0 && matches!(tok, Tok::Comma | Tok::RParen))
            }
            Self::FnParam => {
                matches!(tok, Tok::Eof | Tok::End | Tok::Newline)
                    || (depth == 0 && matches!(tok, Tok::Comma | Tok::RParen))
            }
            Self::TypeBody => {
                matches!(tok, Tok::Eof | Tok::End)
                    || (depth == 0 && matches!(tok, Tok::Newline | Tok::When))
            }
        }
    }

    fn stops_after_unmatched_close(self) -> bool {
        matches!(self, Self::SpecParam | Self::TypeBody)
    }
}
