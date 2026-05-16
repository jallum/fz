use crate::ast::*;
use crate::diag::Span;
use crate::lexer::{Tok, Token};
use std::rc::Rc;

#[cfg(test)]
mod do_block_sugar_tests {
    use super::*;
    use crate::lexer::Lexer;

    fn parse_fn_body(src: &str) -> Expr {
        let wrapped = format!("fn _t() do {} end", src);
        let toks = Lexer::new(&wrapped).tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        match &*prog.items[0] {
            Item::Fn(d) => match &d.clauses[0].body.node {
                Expr::Block(xs) => xs[0].node.clone(),
                other => other.clone(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn trailing_do_block_appended_as_arg() {
        let e = parse_fn_body(
            r#"f("x") do
            1
            2
        end"#,
        );
        let Expr::Call(callee, args) = e else {
            panic!("not a call")
        };
        assert!(matches!(callee.node, Expr::Var(ref n) if n == "f"));
        assert_eq!(args.len(), 2, "name + body block");
        assert!(matches!(args[0].node, Expr::Str(_)));
        assert!(matches!(args[1].node, Expr::Block(_)));
    }

    #[test]
    fn comma_do_kw_appended_as_arg() {
        let e = parse_fn_body(r#"f("x"), do: 42"#);
        let Expr::Call(_, args) = e else {
            panic!("not a call")
        };
        assert_eq!(args.len(), 2);
        assert!(matches!(args[1].node, Expr::Int(42)));
    }

    #[test]
    fn item_level_call_parses_as_macro_call() {
        let toks = Lexer::new(
            r#"
test("addition") do
  1 + 2
end
"#,
        )
        .tokenize()
        .unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let mc = prog.items.iter().find_map(|it| match &**it {
            Item::MacroCall { name, args, .. } => Some((name.clone(), args.clone())),
            _ => None,
        });
        let (name, args) = mc.expect("expected an Item::MacroCall");
        assert_eq!(name, "test");
        assert_eq!(args.len(), 2, "name + body");
        assert!(matches!(args[0].node, Expr::Str(ref s) if s == "addition"));
        match &args[1].node {
            Expr::Block(_) | Expr::BinOp(_, _, _) => {}
            other => panic!("unexpected body shape: {:?}", other),
        }
    }

    #[test]
    fn item_level_call_inside_module() {
        let toks = Lexer::new(
            r#"
defmodule MyTest do
  test("addition") do
    1 + 2
  end
end
"#,
        )
        .tokenize()
        .unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let m = prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Module(m) => Some(m),
                _ => None,
            })
            .unwrap();
        assert!(
            m.items
                .iter()
                .any(|it| matches!(&**it, Item::MacroCall { .. }))
        );
    }

    #[test]
    fn plain_call_no_extra_arg() {
        let e = parse_fn_body("f(1, 2)");
        let Expr::Call(_, args) = e else { panic!() };
        assert_eq!(args.len(), 2);
    }
}

#[cfg(test)]
mod extern_parse_tests {
    use super::*;
    use crate::lexer::Lexer;

    fn parse_extern(src: &str) -> FnDef {
        let toks = Lexer::new(src).tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        match &*prog.items[0] {
            Item::Fn(d) => d.clone(),
            other => panic!("expected Item::Fn, got {:?}", other),
        }
    }

    #[test]
    fn extern_fn_no_params() {
        let d = parse_extern("extern \"C\" fn fz_halt() :: never\n");
        assert_eq!(d.name, "fz_halt");
        assert_eq!(d.extern_abi, Some("C".into()));
        assert_eq!(d.extern_param_count, 0);
        assert!(d.clauses.is_empty());
    }

    #[test]
    fn extern_fn_one_param() {
        let d = parse_extern("extern \"C\" fn fz_print(any) :: unit\n");
        assert_eq!(d.extern_param_count, 1);
    }

    #[test]
    fn extern_fn_two_params() {
        let d = parse_extern("extern \"C\" fn fz_assert_eq(any, any) :: unit\n");
        assert_eq!(d.extern_param_count, 2);
        assert!(!d.extern_ret_tokens.is_empty());
    }
}

/// Drain pending fn-clause groups into the items vec in declaration order.
fn flush_fn_groups(
    items: &mut Vec<Rc<Item>>,
    order: &mut Vec<String>,
    groups: &mut std::collections::HashMap<String, FnDef>,
) {
    for name in order.drain(..) {
        if let Some(def) = groups.remove(&name) {
            items.push(Rc::new(Item::Fn(def)));
        }
    }
}

#[derive(Debug)]
pub struct ParseError {
    pub msg: String,
    pub span: Span,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Plain-text fallback. The .20.6 renderer is the proper rendering
        // path; `to_diagnostic` is what the driver calls.
        write!(f, "parse error: {}", self.msg)
    }
}

impl ParseError {
    /// Promote a parse-time error into a structured Diagnostic. v1 maps
    /// every parse error to `parse/expected-token`; later passes can
    /// refine to specific codes (duplicate-doc, unknown-attribute, …)
    /// at each call site once `self.err(..)` learns to pick codes.
    pub fn to_diagnostic(&self) -> crate::diag::Diagnostic {
        crate::diag::Diagnostic::error(
            crate::diag::codes::PARSE_EXPECTED_TOKEN,
            self.msg.clone(),
            self.span,
        )
    }
}

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
}

type PR<T> = Result<T, ParseError>;

impl Parser {
    pub fn new(toks: Vec<Token>) -> Self {
        Self { toks, pos: 0 }
    }

    // --- token helpers ---

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }
    fn peek_at(&self, off: usize) -> &Tok {
        self.toks
            .get(self.pos + off)
            .map(|t| &t.tok)
            .unwrap_or(&Tok::Eof)
    }
    fn cur_span(&self) -> Span {
        self.toks[self.pos].span
    }
    /// Span of the last consumed token. Used when closing out a parse fn:
    /// the construct spans from its starting token through the last token
    /// it consumed.
    fn prev_span(&self) -> Span {
        if self.pos == 0 {
            Span::DUMMY
        } else {
            self.toks[self.pos - 1].span
        }
    }
    /// Build a span from a starting span through the last consumed token.
    fn finish(&self, start: Span) -> Span {
        start.merge(self.prev_span())
    }
    fn err<T>(&self, msg: impl Into<String>) -> PR<T> {
        Err(ParseError {
            msg: msg.into(),
            span: self.cur_span(),
        })
    }
    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].tok.clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(t) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, t: &Tok, what: &str) -> PR<()> {
        if self.eat(t) {
            Ok(())
        } else {
            self.err(format!("expected {}, got {:?}", what, self.peek()))
        }
    }
    fn skip_newlines(&mut self) {
        while matches!(self.peek(), Tok::Newline | Tok::Semi) {
            self.bump();
        }
    }

    // --- entry ---

    pub fn parse_program(&mut self) -> PR<Program> {
        let (items, top_attrs) = self.parse_items_until(&[Tok::Eof])?;
        for a in &top_attrs {
            match a {
                Attribute::ModuleDoc(_) => {
                    return self.err("@moduledoc only valid inside a defmodule body".to_string());
                }
                Attribute::TypeAlias(_) => {
                    return self.err("@type only valid inside a defmodule body".to_string());
                }
                _ => {}
            }
        }
        Ok(Program {
            items,
            module_docs: Default::default(),
            module_type_envs: Default::default(),
        })
    }

    /// Like `parse_program` but allows top-level `@type` declarations
    /// (and returns them separately). Used for the built-in runtime.fz
    /// prelude, which is not wrapped in a `defmodule`.
    pub fn parse_prelude(&mut self) -> PR<(Vec<Rc<Item>>, Vec<crate::ast::Attribute>)> {
        let (items, attrs) = self.parse_items_until(&[Tok::Eof])?;
        Ok((items, attrs))
    }

    fn parse_items_until(&mut self, terminators: &[Tok]) -> PR<(Vec<Rc<Item>>, Vec<Attribute>)> {
        let mut items: Vec<Rc<Item>> = Vec::new();
        let mut order: Vec<String> = Vec::new();
        let mut groups: std::collections::HashMap<String, FnDef> = std::collections::HashMap::new();
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
                            // fz-ul4.31.4 — one @spec per fn for v1.
                            // Multi-clause specs (union of arrows) are
                            // a deliberate followup.
                            if pending_fn_attrs.iter().any(
                                |a| matches!(a, Attribute::Spec(_)))
                            {
                                return self.err(
                                    "multiple @spec declarations for one fn \
                                     (v1 allows at most one)".to_string());
                            }
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
                    order.push(def.name.clone());
                    items.push(Rc::new(Item::Fn(def)));
                }
                Tok::Fn | Tok::Defmacro => {
                    let start = self.cur_span();
                    let (name, name_span, clause, is_macro) = self.parse_fn_clause()?;
                    if let Some(def) = groups.get_mut(&name) {
                        if def.is_macro != is_macro {
                            return self.err(format!("`{}` declared as both fn and defmacro", name));
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
                                if s.param_body_tokens.len() != clause.params.len() {
                                    return self.err(format!(
                                        "@spec arity {} doesn't match fn \
                                         `{}/{}`",
                                        s.param_body_tokens.len(),
                                        name,
                                        clause.params.len()));
                                }
                            }
                        }
                        let clause_span = clause.span;
                        order.push(name.clone());
                        groups.insert(name.clone(), FnDef {
                            name,
                            name_span,
                            clauses: vec![clause],
                            is_macro,
                            extern_abi: None,
                            extern_param_count: 0,
                            extern_ret_tokens: vec![],
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
                    "expected `fn`, `defmacro`, `defmodule`, `alias`, `import`, `@`, or a macro call, got {:?}",
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
            return self.err(format!("{} not followed by a fn or defmacro", kind));
        }
        let mut module_attrs: Vec<Attribute> = moduledoc_attr.into_iter().collect();
        module_attrs.extend(module_aliases);
        Ok((items, module_attrs))
    }

    /// `@<ident> <string>`. Recognizes `@doc` and `@moduledoc`; rejects
    /// unknown attribute names. fz-ul4.31.3 / .31.4 extend the
    /// `Attribute` enum (and this fn) for `@type` and `@spec`.
    fn parse_attribute(&mut self) -> PR<Attribute> {
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
                    Tok::Str(s) => s,
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
                // Descrs against the module's ModuleTypeEnv in .31.5.
                let start = self.cur_span();
                let name_span = self.cur_span();
                let spec_name = match self.bump() {
                    Tok::Ident(n) => n,
                    other => {
                        return self
                            .err(format!("expected fn name after `@spec`, got {:?}", other));
                    }
                };
                self.expect(&Tok::LParen, "`(`")?;
                let mut param_body_tokens: Vec<Vec<Token>> = Vec::new();
                if !matches!(self.peek(), Tok::RParen) {
                    loop {
                        let toks = self.collect_until_comma_or_rparen();
                        if toks.is_empty() {
                            return self
                                .err("expected type expression in @spec param list".to_string());
                        }
                        param_body_tokens.push(toks);
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
                let end_span = self.cur_span();
                Ok(Attribute::Spec(SpecDecl {
                    name: spec_name,
                    name_span,
                    param_body_tokens,
                    result_body_tokens,
                    span: start.merge(end_span),
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
                self.expect(&Tok::ColonColon, "`::`")?;
                // Collect tokens until a top-level newline / eof / end.
                let body_tokens = self.collect_type_body_tokens();
                let end_span = self.cur_span();
                Ok(Attribute::TypeAlias(TypeAliasDecl {
                    name: alias_name,
                    name_span: alias_name_span,
                    body_tokens,
                    span: start.merge(end_span),
                }))
            }
            other => self.err(format!(
                "unknown attribute `@{}` (only @doc, @moduledoc, @type supported)",
                other
            )),
        }
    }

    /// fz-ul4.31.4 — Collect one type-expression body inside an
    /// `@spec`'s param list. Stops at a top-level comma or `)`. Stops
    /// early on newline / eof to surface malformed input rather than
    /// running past the spec.
    fn collect_until_comma_or_rparen(&mut self) -> Vec<Token> {
        let mut out: Vec<Token> = Vec::new();
        let mut depth: i32 = 0;
        loop {
            match self.peek() {
                Tok::Comma | Tok::RParen if depth == 0 => break,
                Tok::Eof | Tok::Newline => break,
                Tok::LParen | Tok::LBrack | Tok::LBrace => {
                    depth += 1;
                    out.push(self.toks[self.pos].clone());
                    self.pos += 1;
                }
                Tok::RParen | Tok::RBrack | Tok::RBrace => {
                    depth -= 1;
                    out.push(self.toks[self.pos].clone());
                    self.pos += 1;
                    if depth < 0 {
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

    /// fz-ul4.31.3 — Consume the type-expression body tokens for an
    /// `@type` or `@spec` attribute. Stops at the first top-level
    /// newline / eof / module-end. Brackets, braces, and parens are
    /// balanced so a multi-line type body could in principle span lines
    /// inside brackets, but in v1 we only emit single-line bodies.
    fn collect_type_body_tokens(&mut self) -> Vec<Token> {
        let mut out: Vec<Token> = Vec::new();
        let mut depth: i32 = 0;
        loop {
            match self.peek() {
                Tok::Eof | Tok::End => break,
                Tok::Newline if depth == 0 => break,
                Tok::LParen | Tok::LBrack | Tok::LBrace => {
                    depth += 1;
                    out.push(self.toks[self.pos].clone());
                    self.pos += 1;
                }
                Tok::RParen | Tok::RBrack | Tok::RBrace => {
                    depth -= 1;
                    out.push(self.toks[self.pos].clone());
                    self.pos += 1;
                    if depth < 0 {
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

    fn peek_in(&self, terminators: &[Tok]) -> bool {
        terminators
            .iter()
            .any(|t| std::mem::discriminant(self.peek()) == std::mem::discriminant(t))
    }

    /// Parse one fn or defmacro clause. Returns (name, name_span, clause, is_macro).
    fn parse_fn_clause(&mut self) -> PR<(String, Span, FnClause, bool)> {
        let start = self.cur_span();
        let is_macro = match self.peek() {
            Tok::Defmacro => {
                self.bump();
                true
            }
            Tok::Fn => {
                self.bump();
                false
            }
            _ => {
                return self.err(format!(
                    "expected `fn` or `defmacro`, got {:?}",
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
        let params = self.parse_pattern_list(&Tok::RParen)?;
        self.expect(&Tok::RParen, "`)`")?;

        let guard = if matches!(self.peek(), Tok::When) {
            self.bump();
            Some(self.parse_expr()?)
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
                guard,
                body,
                span,
            },
            is_macro,
        ))
    }

    /// `extern "C" fn name(type, type) :: RetType`
    /// Caller has already consumed `Tok::Extern`.
    fn parse_extern_item(&mut self) -> PR<FnDef> {
        let start = self.cur_span();
        let abi = match self.bump() {
            Tok::Str(s) => s,
            other => {
                return self.err(format!(
                    "expected ABI string after `extern`, got {:?}",
                    other
                ));
            }
        };
        self.expect(&Tok::Fn, "`fn` after extern ABI string")?;
        let name_span = self.cur_span();
        let name = match self.bump() {
            Tok::Ident(n) => n,
            other => return self.err(format!("expected function name, got {:?}", other)),
        };
        self.expect(&Tok::LParen, "`(`")?;
        let extern_param_count = if matches!(self.peek(), Tok::RParen) {
            0
        } else {
            let mut count = 1usize;
            let mut depth = 0usize;
            loop {
                match self.peek() {
                    Tok::LParen | Tok::LBrace | Tok::LBrack => {
                        depth += 1;
                        self.bump();
                    }
                    Tok::RParen | Tok::RBrace | Tok::RBrack if depth > 0 => {
                        depth -= 1;
                        self.bump();
                    }
                    Tok::RParen => break,
                    Tok::Comma if depth == 0 => {
                        count += 1;
                        self.bump();
                    }
                    Tok::Eof | Tok::Newline => {
                        return self.err("unexpected end of extern parameter list");
                    }
                    _ => {
                        self.bump();
                    }
                }
            }
            count
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
            extern_abi: Some(abi),
            extern_param_count,
            extern_ret_tokens,
            attrs: vec![],
            span,
        })
    }

    /// `alias A.B.C` or `alias A.B.C, as: D`.
    fn parse_alias(&mut self) -> PR<Item> {
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
            path.last().cloned().expect("path is non-empty")
        };
        Ok(Item::Alias {
            full_path: path,
            as_name,
            span: self.finish(start),
        })
    }

    /// `import Mod` | `import Mod, only: [f: 1, g: 2]` | `import Mod, except: [...]`.
    fn parse_import(&mut self) -> PR<Item> {
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
            path,
            only,
            except,
            span: self.finish(start),
        })
    }

    fn parse_arity_kw_list(&mut self) -> PR<Vec<(String, usize)>> {
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

    fn parse_module(&mut self) -> PR<ModuleDef> {
        let start = self.cur_span();
        self.expect(&Tok::Defmodule, "`defmodule`")?;
        let name_span = self.cur_span();
        let name = match self.bump() {
            Tok::Upper(n) => n,
            other => {
                return self.err(format!(
                    "expected capitalized module name after `defmodule`, got {:?}",
                    other
                ));
            }
        };
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

    // --- patterns ---

    fn parse_pattern_list(&mut self, terminator: &Tok) -> PR<Vec<Spanned<Pattern>>> {
        let mut out = Vec::new();
        self.skip_newlines();
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(terminator) {
            return Ok(out);
        }
        loop {
            out.push(self.parse_pattern()?);
            self.skip_newlines();
            if !self.eat(&Tok::Comma) {
                break;
            }
            self.skip_newlines();
        }
        Ok(out)
    }

    fn parse_pattern(&mut self) -> PR<Spanned<Pattern>> {
        let start = self.cur_span();
        let p = self.parse_pattern_atom()?;
        if matches!(self.peek(), Tok::Eq) {
            if let Pattern::Var(n) = p.node {
                self.bump();
                let inner = self.parse_pattern()?;
                return Ok(Spanned::new(
                    Pattern::As(n, Box::new(inner)),
                    self.finish(start),
                ));
            }
            return Ok(p);
        }
        Ok(p)
    }

    fn parse_pattern_atom(&mut self) -> PR<Spanned<Pattern>> {
        let start = self.cur_span();
        let node = match self.peek().clone() {
            Tok::Underscore => {
                self.bump();
                Pattern::Wildcard
            }
            Tok::Ident(n) => {
                self.bump();
                Pattern::Var(n)
            }
            Tok::Int(n) => {
                self.bump();
                Pattern::Int(n)
            }
            Tok::Float(f) => {
                self.bump();
                Pattern::Float(f)
            }
            Tok::Str(s) => {
                self.bump();
                Pattern::Str(s)
            }
            Tok::Atom(a) => {
                self.bump();
                Pattern::Atom(a)
            }
            Tok::True => {
                self.bump();
                Pattern::Bool(true)
            }
            Tok::False => {
                self.bump();
                Pattern::Bool(false)
            }
            Tok::Nil => {
                self.bump();
                Pattern::Nil
            }
            Tok::Minus => {
                self.bump();
                match self.bump() {
                    Tok::Int(n) => Pattern::Int(-n),
                    Tok::Float(f) => Pattern::Float(-f),
                    other => {
                        return self.err(format!("expected number after `-`, got {:?}", other));
                    }
                }
            }
            Tok::LBrace => {
                self.bump();
                let elems = self.parse_pattern_list(&Tok::RBrace)?;
                self.expect(&Tok::RBrace, "`}`")?;
                Pattern::Tuple(elems)
            }
            Tok::LBitstr => {
                self.bump();
                let mut fields = Vec::new();
                self.skip_newlines();
                if !matches!(self.peek(), Tok::RBitstr) {
                    loop {
                        let value = self.parse_pattern_atom()?;
                        let spec = if self.eat(&Tok::ColonColon) {
                            self.parse_bit_spec()?
                        } else {
                            BitFieldSpec::default()
                        };
                        fields.push(BitField { value, spec });
                        self.skip_newlines();
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                        self.skip_newlines();
                    }
                }
                self.expect(&Tok::RBitstr, "`>>`")?;
                Pattern::Bitstring(fields)
            }
            Tok::LBrack => {
                self.bump();
                let mut elems = Vec::new();
                let mut tail: Option<Box<Spanned<Pattern>>> = None;
                self.skip_newlines();
                if !matches!(self.peek(), Tok::RBrack) {
                    loop {
                        elems.push(self.parse_pattern()?);
                        self.skip_newlines();
                        if self.eat(&Tok::Bar) {
                            tail = Some(Box::new(self.parse_pattern()?));
                            break;
                        }
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                        self.skip_newlines();
                    }
                }
                self.expect(&Tok::RBrack, "`]`")?;
                Pattern::List(elems, tail)
            }
            Tok::PercentLBrace => {
                self.bump();
                let mut pairs: Vec<(Spanned<Pattern>, Spanned<Pattern>)> = Vec::new();
                self.skip_newlines();
                if !matches!(self.peek(), Tok::RBrace) {
                    loop {
                        let key = if let Tok::KwKey(_) = self.peek() {
                            let key_span = self.cur_span();
                            let Tok::KwKey(name) = self.bump() else {
                                unreachable!()
                            };
                            Spanned::new(Pattern::Atom(name), key_span)
                        } else {
                            let k = self.parse_pattern_atom()?;
                            self.expect(&Tok::FatArrow, "`=>`")?;
                            k
                        };
                        let val = self.parse_pattern()?;
                        pairs.push((key, val));
                        self.skip_newlines();
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                        self.skip_newlines();
                    }
                }
                self.expect(&Tok::RBrace, "`}`")?;
                Pattern::Map(pairs)
            }
            other => return self.err(format!("invalid pattern start {:?}", other)),
        };
        Ok(Spanned::new(node, self.finish(start)))
    }

    // --- expressions (Pratt) ---

    pub fn parse_expr(&mut self) -> PR<Spanned<Expr>> {
        self.parse_bp(0)
    }

    pub fn parse_expr_eof(&mut self) -> PR<Spanned<Expr>> {
        self.skip_newlines();
        let e = self.parse_expr()?;
        self.skip_newlines();
        if !matches!(self.peek(), Tok::Eof) {
            return self.err(format!(
                "trailing tokens after expression: {:?}",
                self.peek()
            ));
        }
        Ok(e)
    }

    fn infix_bp(t: &Tok) -> Option<(u8, u8, BinOp)> {
        Some(match t {
            Tok::Pipe => (10, 11, BinOp::Pipe),
            Tok::OrOr => (20, 21, BinOp::Or),
            Tok::AndAnd => (30, 31, BinOp::And),
            Tok::EqEq => (40, 41, BinOp::Eq),
            Tok::NotEq => (40, 41, BinOp::Neq),
            Tok::Lt => (50, 51, BinOp::Lt),
            Tok::LtEq => (50, 51, BinOp::LtEq),
            Tok::Gt => (50, 51, BinOp::Gt),
            Tok::GtEq => (50, 51, BinOp::GtEq),
            Tok::Plus => (60, 61, BinOp::Add),
            Tok::Minus => (60, 61, BinOp::Sub),
            Tok::Star => (70, 71, BinOp::Mul),
            Tok::Slash => (70, 71, BinOp::Div),
            Tok::Percent => (70, 71, BinOp::Rem),
            _ => return None,
        })
    }

    fn parse_bp(&mut self, min_bp: u8) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        let mut lhs = self.parse_prefix()?;
        loop {
            match self.peek() {
                Tok::LParen => {
                    self.bump();
                    let mut args = self.parse_expr_list(&Tok::RParen)?;
                    self.expect(&Tok::RParen, "`)`")?;
                    if matches!(self.peek(), Tok::Do) {
                        self.bump();
                        self.skip_newlines();
                        let body = self.parse_block_until(&[Tok::End])?;
                        self.expect(&Tok::End, "`end`")?;
                        args.push(body);
                    } else if matches!(self.peek(), Tok::Comma)
                        && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do")
                    {
                        self.bump();
                        self.bump();
                        let body = self.parse_expr()?;
                        args.push(body);
                    }
                    let span = start.merge(self.prev_span());
                    lhs = Spanned::new(Expr::Call(Box::new(lhs), args), span);
                    continue;
                }
                Tok::Dot => {
                    self.bump();
                    let name = match self.bump() {
                        Tok::Ident(n) => n,
                        Tok::Upper(n) => n,
                        other => {
                            return self.err(format!("expected name after `.`, got {:?}", other));
                        }
                    };
                    let key_span = self.prev_span();
                    let span = start.merge(key_span);
                    // m.k desugars to m[:k] (atom-keyed Index)
                    lhs = Spanned::new(
                        Expr::Index(
                            Box::new(lhs),
                            Box::new(Spanned::new(Expr::Atom(name), key_span)),
                        ),
                        span,
                    );
                    continue;
                }
                Tok::LBrack => {
                    self.bump();
                    let key = self.parse_expr()?;
                    self.expect(&Tok::RBrack, "`]`")?;
                    let span = start.merge(self.prev_span());
                    lhs = Spanned::new(Expr::Index(Box::new(lhs), Box::new(key)), span);
                    continue;
                }
                _ => {}
            }
            if matches!(self.peek(), Tok::Eq) {
                if min_bp > 5 {
                    break;
                }
                self.bump();
                let rhs = self.parse_bp(5)?;
                let pat = expr_to_pattern(&lhs)?;
                let span = start.merge(self.prev_span());
                lhs = Spanned::new(Expr::Match(pat, Box::new(rhs)), span);
                continue;
            }
            let Some((lbp, rbp, op)) = Self::infix_bp(self.peek()) else {
                break;
            };
            if lbp < min_bp {
                break;
            }
            self.bump();
            let rhs = self.parse_bp(rbp)?;
            let span = start.merge(self.prev_span());
            lhs = Spanned::new(Expr::BinOp(op, Box::new(lhs), Box::new(rhs)), span);
        }
        Ok(lhs)
    }

    fn parse_prefix(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        let node = match self.peek().clone() {
            Tok::Int(n) => {
                self.bump();
                Expr::Int(n)
            }
            Tok::Float(f) => {
                self.bump();
                Expr::Float(f)
            }
            Tok::Str(s) => {
                self.bump();
                Expr::Str(s)
            }
            Tok::Atom(a) => {
                self.bump();
                Expr::Atom(a)
            }
            Tok::True => {
                self.bump();
                Expr::Bool(true)
            }
            Tok::False => {
                self.bump();
                Expr::Bool(false)
            }
            Tok::Nil => {
                self.bump();
                Expr::Nil
            }
            Tok::Ident(n) => {
                self.bump();
                Expr::Var(n)
            }
            Tok::Upper(n) => {
                self.bump();
                Expr::Var(n)
            }
            Tok::Minus => {
                self.bump();
                let e = self.parse_bp(80)?;
                Expr::UnOp(UnOp::Neg, Box::new(e))
            }
            Tok::Bang => {
                self.bump();
                let e = self.parse_bp(80)?;
                Expr::UnOp(UnOp::Not, Box::new(e))
            }
            Tok::LParen => {
                self.bump();
                self.skip_newlines();
                let e = self.parse_expr()?;
                self.skip_newlines();
                self.expect(&Tok::RParen, "`)`")?;
                return Ok(e);
            }
            Tok::LBrack => {
                self.bump();
                let mut elems = Vec::new();
                let mut tail: Option<Box<Spanned<Expr>>> = None;
                self.skip_newlines();
                if !matches!(self.peek(), Tok::RBrack) {
                    loop {
                        elems.push(self.parse_expr()?);
                        self.skip_newlines();
                        if self.eat(&Tok::Bar) {
                            self.skip_newlines();
                            tail = Some(Box::new(self.parse_expr()?));
                            self.skip_newlines();
                            break;
                        }
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                        self.skip_newlines();
                    }
                }
                self.expect(&Tok::RBrack, "`]`")?;
                Expr::List(elems, tail)
            }
            Tok::LBrace => {
                self.bump();
                let elems = self.parse_expr_list(&Tok::RBrace)?;
                self.expect(&Tok::RBrace, "`}`")?;
                Expr::Tuple(elems)
            }
            Tok::PercentLBrace => return self.parse_map_expr(),
            Tok::If => return self.parse_if(),
            Tok::Case => return self.parse_case(),
            Tok::Cond => return self.parse_cond(),
            Tok::With => return self.parse_with(),
            Tok::Do => {
                self.bump();
                self.skip_newlines();
                let blk = self.parse_block_until(&[Tok::End])?;
                self.expect(&Tok::End, "`end`")?;
                return Ok(blk);
            }
            Tok::Fn => return self.parse_lambda(),
            Tok::Quote => return self.parse_quote(),
            Tok::Unquote => return self.parse_unquote(),
            Tok::LBitstr => return self.parse_bitstring_expr(),
            Tok::Sigil(name) => {
                let kind = match name.as_str() {
                    "v" => VecKind::Numeric,
                    "b" => VecKind::Bytes,
                    "bits" => VecKind::Bits,
                    other => return self.err(format!("unknown sigil ~{}", other)),
                };
                self.bump();
                self.expect(&Tok::LBrack, "`[` after sigil")?;
                let elems = self.parse_expr_list(&Tok::RBrack)?;
                self.expect(&Tok::RBrack, "`]`")?;
                Expr::VecLit(kind, elems)
            }
            other => return self.err(format!("unexpected token {:?} at expression start", other)),
        };
        Ok(Spanned::new(node, self.finish(start)))
    }

    fn parse_expr_list(&mut self, terminator: &Tok) -> PR<Vec<Spanned<Expr>>> {
        let mut out = Vec::new();
        self.skip_newlines();
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(terminator) {
            return Ok(out);
        }
        loop {
            out.push(self.parse_expr()?);
            self.skip_newlines();
            if !self.eat(&Tok::Comma) {
                break;
            }
            self.skip_newlines();
        }
        Ok(out)
    }

    fn parse_block_until(&mut self, stops: &[Tok]) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        let mut exprs = Vec::new();
        loop {
            self.skip_newlines();
            if stops
                .iter()
                .any(|s| std::mem::discriminant(self.peek()) == std::mem::discriminant(s))
            {
                break;
            }
            if matches!(self.peek(), Tok::Eof) {
                break;
            }
            exprs.push(self.parse_expr()?);
            if !matches!(self.peek(), Tok::Newline | Tok::Semi) {
                if stops
                    .iter()
                    .any(|s| std::mem::discriminant(self.peek()) == std::mem::discriminant(s))
                {
                    break;
                }
                if matches!(self.peek(), Tok::Eof) {
                    break;
                }
                return self.err(format!(
                    "expected newline between expressions, got {:?}",
                    self.peek()
                ));
            }
        }
        if exprs.len() == 1 {
            Ok(exprs.pop().unwrap())
        } else {
            Ok(Spanned::new(Expr::Block(exprs), self.finish(start)))
        }
    }

    fn parse_quote(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::Quote, "`quote`")?;
        if matches!(self.peek(), Tok::Comma)
            && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do")
        {
            self.bump();
            self.bump();
            let e = self.parse_expr()?;
            return Ok(Spanned::new(Expr::Quote(Box::new(e)), self.finish(start)));
        }
        if matches!(self.peek(), Tok::KwKey(s) if s == "do") {
            self.bump();
            let e = self.parse_expr()?;
            return Ok(Spanned::new(Expr::Quote(Box::new(e)), self.finish(start)));
        }
        self.expect(&Tok::Do, "`do` or `do:` after `quote`")?;
        self.skip_newlines();
        let body = self.parse_block_until(&[Tok::End])?;
        self.expect(&Tok::End, "`end`")?;
        Ok(Spanned::new(
            Expr::Quote(Box::new(body)),
            self.finish(start),
        ))
    }

    fn parse_unquote(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::Unquote, "`unquote`")?;
        self.expect(&Tok::LParen, "`(` after `unquote`")?;
        self.skip_newlines();
        let e = self.parse_expr()?;
        self.skip_newlines();
        self.expect(&Tok::RParen, "`)`")?;
        Ok(Spanned::new(Expr::Unquote(Box::new(e)), self.finish(start)))
    }

    fn parse_if(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::If, "`if`")?;
        let cond = self.parse_expr()?;
        if matches!(self.peek(), Tok::Comma)
            && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do")
        {
            self.bump();
            self.bump();
            let then = self.parse_expr()?;
            let els = if matches!(self.peek(), Tok::Comma)
                && matches!(self.peek_at(1), Tok::KwKey(s) if s == "else")
            {
                self.bump();
                self.bump();
                Some(Box::new(self.parse_expr()?))
            } else {
                None
            };
            return Ok(Spanned::new(
                Expr::If(Box::new(cond), Box::new(then), els),
                self.finish(start),
            ));
        }
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let then = self.parse_block_until(&[Tok::Else, Tok::End])?;
        let els = if self.eat(&Tok::Else) {
            self.skip_newlines();
            Some(Box::new(self.parse_block_until(&[Tok::End])?))
        } else {
            None
        };
        self.expect(&Tok::End, "`end`")?;
        Ok(Spanned::new(
            Expr::If(Box::new(cond), Box::new(then), els),
            self.finish(start),
        ))
    }

    fn parse_case(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::Case, "`case`")?;
        let scrut = self.parse_expr()?;
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let mut clauses = Vec::new();
        while !matches!(self.peek(), Tok::End | Tok::Eof) {
            let cl_start = self.cur_span();
            let pat = self.parse_pattern()?;
            let guard = if matches!(self.peek(), Tok::When) {
                self.bump();
                Some(self.parse_expr()?)
            } else {
                None
            };
            self.expect(&Tok::Arrow, "`->`")?;
            self.skip_newlines();
            let body = self.parse_expr()?;
            let cspan = self.finish(cl_start);
            clauses.push(MatchClause {
                pattern: pat,
                guard,
                body,
                span: cspan,
            });
            self.skip_newlines();
        }
        self.expect(&Tok::End, "`end`")?;
        Ok(Spanned::new(
            Expr::Case(Box::new(scrut), clauses),
            self.finish(start),
        ))
    }

    /// `cond do <test> -> <body>; ...; end` — parsed as `Expr::Cond` whose
    /// arms are evaluated top-to-bottom until one's test is truthy.
    fn parse_cond(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::Cond, "`cond`")?;
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let mut arms: Vec<(Spanned<Expr>, Spanned<Expr>)> = Vec::new();
        while !matches!(self.peek(), Tok::End | Tok::Eof) {
            let test = self.parse_expr()?;
            self.expect(&Tok::Arrow, "`->`")?;
            self.skip_newlines();
            let body = self.parse_expr()?;
            arms.push((test, body));
            self.skip_newlines();
        }
        self.expect(&Tok::End, "`end`")?;
        Ok(Spanned::new(Expr::Cond(arms), self.finish(start)))
    }

    fn parse_bitstring_expr(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::LBitstr, "`<<`")?;
        let mut fields: Vec<BitField<Spanned<Expr>>> = Vec::new();
        self.skip_newlines();
        if !matches!(self.peek(), Tok::RBitstr) {
            loop {
                let value = self.parse_expr()?;
                let spec = if self.eat(&Tok::ColonColon) {
                    self.parse_bit_spec()?
                } else {
                    BitFieldSpec::default()
                };
                fields.push(BitField { value, spec });
                self.skip_newlines();
                if !self.eat(&Tok::Comma) {
                    break;
                }
                self.skip_newlines();
            }
        }
        self.expect(&Tok::RBitstr, "`>>`")?;
        Ok(Spanned::new(Expr::Bitstring(fields), self.finish(start)))
    }

    fn parse_bit_spec(&mut self) -> PR<BitFieldSpec> {
        let mut spec = BitFieldSpec::default();
        loop {
            match self.peek().clone() {
                Tok::Int(n) => {
                    self.bump();
                    spec.size = Some(BitSize::Literal(n as u32));
                }
                Tok::Ident(name) => {
                    self.bump();
                    self.apply_bit_modifier(&mut spec, &name)?;
                }
                other => return self.err(format!("expected bitstring modifier, got {:?}", other)),
            }
            if !self.eat(&Tok::Minus) {
                break;
            }
        }
        Ok(spec)
    }

    fn apply_bit_modifier(&mut self, spec: &mut BitFieldSpec, name: &str) -> PR<()> {
        match name {
            "integer" => spec.ty = BitType::Integer,
            "float" => spec.ty = BitType::Float,
            "binary" => spec.ty = BitType::Binary,
            "bits" | "bitstring" => spec.ty = BitType::Bits,
            "utf8" => spec.ty = BitType::Utf8,
            "utf16" => spec.ty = BitType::Utf16,
            "utf32" => spec.ty = BitType::Utf32,
            "big" => spec.endian = Endian::Big,
            "little" => spec.endian = Endian::Little,
            "native" => spec.endian = Endian::Native,
            "signed" => spec.signed = true,
            "unsigned" => spec.signed = false,
            "size" => {
                self.expect(&Tok::LParen, "`(`")?;
                spec.size = Some(self.parse_bit_size()?);
                self.expect(&Tok::RParen, "`)`")?;
            }
            "unit" => {
                self.expect(&Tok::LParen, "`(`")?;
                match self.bump() {
                    Tok::Int(n) => spec.unit = Some(n as u32),
                    other => return self.err(format!("unit expects int, got {:?}", other)),
                }
                self.expect(&Tok::RParen, "`)`")?;
            }
            other => return self.err(format!("unknown bitstring modifier: {}", other)),
        }
        Ok(())
    }

    fn parse_bit_size(&mut self) -> PR<BitSize> {
        Ok(match self.bump() {
            Tok::Int(n) => BitSize::Literal(n as u32),
            Tok::Ident(name) => BitSize::Var(name),
            other => return self.err(format!("size expects int or var, got {:?}", other)),
        })
    }

    fn parse_with(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::With, "`with`")?;
        let mut bindings: Vec<WithBinding> = Vec::new();
        loop {
            self.skip_newlines();
            let saved = self.pos;
            let try_pat = self.parse_pattern();
            if let Ok(pat) = try_pat {
                if matches!(self.peek(), Tok::LArrow) {
                    self.bump();
                    let e = self.parse_expr()?;
                    bindings.push(WithBinding::Match(pat, e));
                } else {
                    self.pos = saved;
                    let e = self.parse_expr()?;
                    bindings.push(WithBinding::Bare(e));
                }
            } else {
                self.pos = saved;
                let e = self.parse_expr()?;
                bindings.push(WithBinding::Bare(e));
            }
            self.skip_newlines();
            // `, do:` shorthand terminates the binding list. Without this
            // lookahead the loop greedily eats the comma and then fails to
            // parse `do:` as a binding head.
            if matches!(self.peek(), Tok::Comma)
                && !matches!(self.peek_at(1), Tok::KwKey(s) if s == "do")
            {
                self.bump();
                continue;
            }
            break;
        }
        let body;
        let mut else_clauses: Vec<MatchClause> = Vec::new();
        if matches!(self.peek(), Tok::Comma)
            && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do")
        {
            self.bump();
            self.bump();
            body = self.parse_expr()?;
        } else {
            self.expect(&Tok::Do, "`do`")?;
            self.skip_newlines();
            body = self.parse_block_until(&[Tok::Else, Tok::End])?;
            if self.eat(&Tok::Else) {
                self.skip_newlines();
                while !matches!(self.peek(), Tok::End | Tok::Eof) {
                    let cl_start = self.cur_span();
                    let pat = self.parse_pattern()?;
                    let guard = if matches!(self.peek(), Tok::When) {
                        self.bump();
                        Some(self.parse_expr()?)
                    } else {
                        None
                    };
                    self.expect(&Tok::Arrow, "`->`")?;
                    self.skip_newlines();
                    let cb = self.parse_expr()?;
                    let cspan = self.finish(cl_start);
                    else_clauses.push(MatchClause {
                        pattern: pat,
                        guard,
                        body: cb,
                        span: cspan,
                    });
                    self.skip_newlines();
                }
            }
            self.expect(&Tok::End, "`end`")?;
        }
        Ok(Spanned::new(
            Expr::With(bindings, Box::new(body), else_clauses),
            self.finish(start),
        ))
    }

    fn parse_map_expr(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::PercentLBrace, "`%{`")?;
        self.skip_newlines();
        let base = if !matches!(self.peek(), Tok::RBrace) {
            let first = self.parse_map_first_segment()?;
            match first {
                MapHead::Update(base) => Some(base),
                MapHead::Pair(k, v) => {
                    let mut pairs = vec![(k, v)];
                    self.skip_newlines();
                    if self.eat(&Tok::Comma) {
                        self.skip_newlines();
                        if !matches!(self.peek(), Tok::RBrace) {
                            self.parse_map_pairs_into(&mut pairs)?;
                        }
                    }
                    self.skip_newlines();
                    self.expect(&Tok::RBrace, "`}`")?;
                    return Ok(Spanned::new(Expr::Map(pairs), self.finish(start)));
                }
            }
        } else {
            self.expect(&Tok::RBrace, "`}`")?;
            return Ok(Spanned::new(Expr::Map(vec![]), self.finish(start)));
        };
        let base = base.unwrap();
        self.skip_newlines();
        let mut pairs: Vec<(Spanned<Expr>, Spanned<Expr>)> = Vec::new();
        if !matches!(self.peek(), Tok::RBrace) {
            self.parse_map_pairs_into(&mut pairs)?;
        }
        self.skip_newlines();
        self.expect(&Tok::RBrace, "`}`")?;
        Ok(Spanned::new(
            Expr::MapUpdate(Box::new(base), pairs),
            self.finish(start),
        ))
    }

    fn parse_map_first_segment(&mut self) -> PR<MapHead> {
        if let Tok::KwKey(_) = self.peek() {
            let key_span = self.cur_span();
            let Tok::KwKey(name) = self.bump() else {
                unreachable!()
            };
            let v = self.parse_expr()?;
            return Ok(MapHead::Pair(Spanned::new(Expr::Atom(name), key_span), v));
        }
        let first = self.parse_expr()?;
        if matches!(self.peek(), Tok::Bar) {
            self.bump();
            return Ok(MapHead::Update(first));
        }
        if self.eat(&Tok::FatArrow) {
            let v = self.parse_expr()?;
            return Ok(MapHead::Pair(first, v));
        }
        self.err(format!(
            "expected `=>` or `|` in map literal, got {:?}",
            self.peek()
        ))
    }

    fn parse_map_pairs_into(&mut self, pairs: &mut Vec<(Spanned<Expr>, Spanned<Expr>)>) -> PR<()> {
        loop {
            self.skip_newlines();
            if let Tok::KwKey(_) = self.peek() {
                let key_span = self.cur_span();
                let Tok::KwKey(name) = self.bump() else {
                    unreachable!()
                };
                let v = self.parse_expr()?;
                pairs.push((Spanned::new(Expr::Atom(name), key_span), v));
            } else {
                let k = self.parse_expr()?;
                if !self.eat(&Tok::FatArrow) {
                    return self.err(format!(
                        "expected `=>` after map key, got {:?}",
                        self.peek()
                    ));
                }
                let v = self.parse_expr()?;
                pairs.push((k, v));
            }
            self.skip_newlines();
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        Ok(())
    }

    fn parse_lambda(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::Fn, "`fn`")?;
        let params = if self.eat(&Tok::LParen) {
            let ps = self.parse_pattern_list(&Tok::RParen)?;
            self.expect(&Tok::RParen, "`)`")?;
            ps
        } else {
            vec![self.parse_pattern()?]
        };
        self.expect(&Tok::Arrow, "`->`")?;
        let body = self.parse_expr()?;
        Ok(Spanned::new(
            Expr::Lambda(params, Box::new(body)),
            self.finish(start),
        ))
    }
}

enum MapHead {
    Pair(Spanned<Expr>, Spanned<Expr>),
    Update(Spanned<Expr>),
}

/// LHS of `=` is a pattern; convert.
fn expr_to_pattern(e: &Spanned<Expr>) -> PR<Spanned<Pattern>> {
    let node = match &e.node {
        Expr::Var(n) if n == "_" => Pattern::Wildcard,
        Expr::Var(n) => Pattern::Var(n.clone()),
        Expr::Int(n) => Pattern::Int(*n),
        Expr::Float(f) => Pattern::Float(*f),
        Expr::Str(s) => Pattern::Str(s.clone()),
        Expr::Atom(a) => Pattern::Atom(a.clone()),
        Expr::Bool(b) => Pattern::Bool(*b),
        Expr::Nil => Pattern::Nil,
        Expr::Tuple(xs) => Pattern::Tuple(xs.iter().map(expr_to_pattern).collect::<PR<_>>()?),
        Expr::Map(pairs) => Pattern::Map(
            pairs
                .iter()
                .map(|(k, v)| Ok::<_, ParseError>((expr_to_pattern(k)?, expr_to_pattern(v)?)))
                .collect::<PR<_>>()?,
        ),
        Expr::List(xs, tail) => Pattern::List(
            xs.iter().map(expr_to_pattern).collect::<PR<_>>()?,
            tail.as_deref()
                .map(|e| expr_to_pattern(e).map(Box::new))
                .transpose()?,
        ),
        _ => {
            return Err(ParseError {
                msg: format!("expression cannot be used as pattern: {:?}", e.node),
                span: e.span,
            });
        }
    };
    Ok(Spanned::new(node, e.span))
}
