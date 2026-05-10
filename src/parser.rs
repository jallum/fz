use crate::ast::*;
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
            Item::Fn(d) => match &d.clauses[0].body {
                Expr::Block(xs) => xs[0].clone(),
                other => other.clone(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn trailing_do_block_appended_as_arg() {
        let e = parse_fn_body(r#"f("x") do
            1
            2
        end"#);
        let Expr::Call(callee, args) = e else { panic!("not a call") };
        assert!(matches!(*callee, Expr::Var(ref n) if n == "f"));
        assert_eq!(args.len(), 2, "name + body block");
        assert!(matches!(args[0], Expr::Str(_)));
        assert!(matches!(args[1], Expr::Block(_)));
    }

    #[test]
    fn comma_do_kw_appended_as_arg() {
        let e = parse_fn_body(r#"f("x"), do: 42"#);
        let Expr::Call(_, args) = e else { panic!("not a call") };
        assert_eq!(args.len(), 2);
        assert!(matches!(args[1], Expr::Int(42)));
    }

    #[test]
    fn plain_call_no_extra_arg() {
        let e = parse_fn_body("f(1, 2)");
        let Expr::Call(_, args) = e else { panic!() };
        assert_eq!(args.len(), 2);
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
    pub line: u32,
    pub col: u32,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "parse error at {}:{}: {}", self.line, self.col, self.msg)
    }
}

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
}

type PR<T> = Result<T, ParseError>;

impl Parser {
    pub fn new(toks: Vec<Token>) -> Self { Self { toks, pos: 0 } }

    // --- token helpers ---

    fn peek(&self) -> &Tok { &self.toks[self.pos].tok }
    fn peek_at(&self, off: usize) -> &Tok {
        self.toks.get(self.pos + off).map(|t| &t.tok).unwrap_or(&Tok::Eof)
    }
    fn line_col(&self) -> (u32, u32) {
        let t = &self.toks[self.pos];
        (t.line, t.col)
    }
    fn err<T>(&self, msg: impl Into<String>) -> PR<T> {
        let (line, col) = self.line_col();
        Err(ParseError { msg: msg.into(), line, col })
    }
    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].tok.clone();
        if self.pos + 1 < self.toks.len() { self.pos += 1; }
        t
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(t) {
            self.bump(); true
        } else { false }
    }
    fn expect(&mut self, t: &Tok, what: &str) -> PR<()> {
        if self.eat(t) { Ok(()) } else { self.err(format!("expected {}, got {:?}", what, self.peek())) }
    }
    fn skip_newlines(&mut self) {
        while matches!(self.peek(), Tok::Newline | Tok::Semi) { self.bump(); }
    }

    // --- entry ---

    pub fn parse_program(&mut self) -> PR<Program> {
        let (items, moduledoc) = self.parse_items_until(&[Tok::Eof])?;
        if moduledoc.is_some() {
            return self.err("@moduledoc only valid inside a defmodule body".to_string());
        }
        Ok(Program { items })
    }

    /// Parse a sequence of top-level items (fn/defmacro/defmodule). Used both
    /// at program top-level (terminator: Eof) and inside `defmodule … end`
    /// bodies (terminator: End). Fn clauses with the same name are merged
    /// into a single FnDef in declaration order. The optional out param
    /// returns a `@moduledoc "..."` if one was encountered (only meaningful
    /// when called for a module body).
    fn parse_items_until(&mut self, terminators: &[Tok]) -> PR<(Vec<Rc<Item>>, Option<String>)> {
        let mut items: Vec<Rc<Item>> = Vec::new();
        let mut order: Vec<String> = Vec::new();
        let mut groups: std::collections::HashMap<String, FnDef> =
            std::collections::HashMap::new();
        let mut moduledoc: Option<String> = None;
        let mut pending_doc: Option<String> = None;

        self.skip_newlines();
        while !self.peek_in(terminators) {
            match self.peek() {
                Tok::At => {
                    let (attr, val) = self.parse_attribute()?;
                    match attr.as_str() {
                        "moduledoc" => {
                            if moduledoc.is_some() {
                                return self.err("duplicate @moduledoc".to_string());
                            }
                            moduledoc = Some(val);
                        }
                        "doc" => {
                            if pending_doc.is_some() {
                                return self.err("duplicate @doc before fn".to_string());
                            }
                            pending_doc = Some(val);
                        }
                        other => return self.err(format!(
                            "unknown attribute `@{}` (only @doc and @moduledoc supported)",
                            other
                        )),
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
                Tok::Fn | Tok::Defmacro => {
                    let (name, clause, is_macro) = self.parse_fn_clause()?;
                    if let Some(def) = groups.get_mut(&name) {
                        if def.is_macro != is_macro {
                            return self.err(format!("`{}` declared as both fn and defmacro", name));
                        }
                        def.clauses.push(clause);
                    } else {
                        let doc = pending_doc.take();
                        order.push(name.clone());
                        groups.insert(name.clone(), FnDef {
                            name, clauses: vec![clause], is_macro, doc,
                        });
                    }
                }
                _ => return self.err(format!(
                    "expected `fn`, `defmacro`, `defmodule`, `alias`, `import`, or `@`, got {:?}",
                    self.peek()
                )),
            }
            self.skip_newlines();
        }
        flush_fn_groups(&mut items, &mut order, &mut groups);
        if pending_doc.is_some() {
            return self.err("@doc not followed by a fn or defmacro".to_string());
        }
        Ok((items, moduledoc))
    }

    /// `@<ident> <string>`. v1 only supports string-valued attributes.
    fn parse_attribute(&mut self) -> PR<(String, String)> {
        self.expect(&Tok::At, "`@`")?;
        let name = match self.bump() {
            Tok::Ident(n) => n,
            other => return self.err(format!(
                "expected attribute name after `@`, got {:?}", other
            )),
        };
        let value = match self.bump() {
            Tok::Str(s) => s,
            other => return self.err(format!(
                "expected string value after `@{}`, got {:?}", name, other
            )),
        };
        Ok((name, value))
    }

    fn peek_in(&self, terminators: &[Tok]) -> bool {
        terminators.iter().any(|t|
            std::mem::discriminant(self.peek()) == std::mem::discriminant(t))
    }

    /// Parse one fn or defmacro clause (the leading keyword has already been
    /// peeked). Returns (name, clause, is_macro).
    fn parse_fn_clause(&mut self) -> PR<(String, FnClause, bool)> {
        let is_macro = match self.peek() {
            Tok::Defmacro => { self.bump(); true }
            Tok::Fn => { self.bump(); false }
            _ => return self.err(format!("expected `fn` or `defmacro`, got {:?}", self.peek())),
        };
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
        } else { None };

        let body = if matches!(self.peek(), Tok::Comma) && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do") {
            self.bump(); self.bump();
            self.parse_expr()?
        } else if matches!(self.peek(), Tok::Do) {
            self.bump();
            self.skip_newlines();
            let blk = self.parse_block_until(&[Tok::End])?;
            self.expect(&Tok::End, "`end`")?;
            blk
        } else {
            return self.err(format!("expected `do` or `, do:` after function head, got {:?}", self.peek()));
        };
        Ok((name, FnClause { params, guard, body }, is_macro))
    }

    /// `alias A.B.C` or `alias A.B.C, as: D`.
    fn parse_alias(&mut self) -> PR<Item> {
        self.expect(&Tok::Alias, "`alias`")?;
        let mut path: Vec<String> = Vec::new();
        match self.bump() {
            Tok::Upper(n) => path.push(n),
            other => return self.err(format!(
                "expected uppercase module path after `alias`, got {:?}", other
            )),
        }
        // Subsequent `.UpperName` segments. The lexer emits Dot + Upper,
        // and Dot then dispatches into postfix in expressions; here we
        // walk it token-by-token.
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.bump() {
                Tok::Upper(n) => path.push(n),
                other => return self.err(format!(
                    "expected uppercase segment after `.` in alias path, got {:?}", other
                )),
            }
        }
        // Optional `, as: <Upper>` to override the nickname.
        let as_name = if matches!(self.peek(), Tok::Comma)
            && matches!(self.peek_at(1), Tok::KwKey(s) if s == "as")
        {
            self.bump(); // ,
            self.bump(); // as:
            match self.bump() {
                Tok::Upper(n) => n,
                other => return self.err(format!(
                    "expected uppercase nickname after `as:`, got {:?}", other
                )),
            }
        } else {
            // Default: last segment.
            path.last().cloned().expect("path is non-empty")
        };
        Ok(Item::Alias { full_path: path, as_name })
    }

    /// `import Mod` | `import Mod, only: [f: 1, g: 2]` | `import Mod, except: [...]`.
    fn parse_import(&mut self) -> PR<Item> {
        self.expect(&Tok::Import, "`import`")?;
        let mut path: Vec<String> = Vec::new();
        match self.bump() {
            Tok::Upper(n) => path.push(n),
            other => return self.err(format!(
                "expected uppercase module path after `import`, got {:?}", other
            )),
        }
        while matches!(self.peek(), Tok::Dot) {
            self.bump();
            match self.bump() {
                Tok::Upper(n) => path.push(n),
                other => return self.err(format!(
                    "expected uppercase segment after `.`, got {:?}", other
                )),
            }
        }
        let mut only: Option<Vec<(String, usize)>> = None;
        let mut except: Option<Vec<(String, usize)>> = None;
        // Optional `, only: [f: 1, g: 2]` or `, except: [...]`.
        if matches!(self.peek(), Tok::Comma) {
            // Lookahead must be `only:` or `except:`.
            if let Tok::KwKey(s) = self.peek_at(1) {
                if s == "only" || s == "except" {
                    self.bump(); // ,
                    let kind = match self.bump() {
                        Tok::KwKey(k) => k,
                        _ => unreachable!(),
                    };
                    let pairs = self.parse_arity_kw_list()?;
                    if kind == "only" { only = Some(pairs); }
                    else { except = Some(pairs); }
                }
            }
        }
        Ok(Item::Import { path, only, except })
    }

    /// Parse a keyword list of `[name: arity, name: arity]` for import filters.
    fn parse_arity_kw_list(&mut self) -> PR<Vec<(String, usize)>> {
        self.expect(&Tok::LBrack, "`[`")?;
        let mut out: Vec<(String, usize)> = Vec::new();
        self.skip_newlines();
        if !matches!(self.peek(), Tok::RBrack) {
            loop {
                let name = match self.bump() {
                    Tok::KwKey(k) => k,
                    other => return self.err(format!(
                        "expected name: in import filter list, got {:?}", other
                    )),
                };
                let arity = match self.bump() {
                    Tok::Int(n) if n >= 0 => n as usize,
                    other => return self.err(format!(
                        "expected non-negative arity after `{}:`, got {:?}", name, other
                    )),
                };
                out.push((name, arity));
                self.skip_newlines();
                if !self.eat(&Tok::Comma) { break; }
                self.skip_newlines();
            }
        }
        self.expect(&Tok::RBrack, "`]`")?;
        Ok(out)
    }

    fn parse_module(&mut self) -> PR<ModuleDef> {
        self.expect(&Tok::Defmodule, "`defmodule`")?;
        let name = match self.bump() {
            Tok::Upper(n) => n,
            other => return self.err(format!(
                "expected capitalized module name after `defmodule`, got {:?}", other
            )),
        };
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let (items, moduledoc) = self.parse_items_until(&[Tok::End])?;
        self.expect(&Tok::End, "`end`")?;
        Ok(ModuleDef { name, items, moduledoc })
    }

    // --- patterns ---

    fn parse_pattern_list(&mut self, terminator: &Tok) -> PR<Vec<Pattern>> {
        let mut out = Vec::new();
        self.skip_newlines();
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(terminator) { return Ok(out); }
        loop {
            out.push(self.parse_pattern()?);
            self.skip_newlines();
            if !self.eat(&Tok::Comma) { break; }
            self.skip_newlines();
        }
        Ok(out)
    }

    fn parse_pattern(&mut self) -> PR<Pattern> {
        // Support `name = pattern` as-pattern (Elixir style)
        let p = self.parse_pattern_atom()?;
        if matches!(self.peek(), Tok::Eq) {
            // only if `p` is a bare Var
            if let Pattern::Var(n) = p {
                self.bump();
                let inner = self.parse_pattern()?;
                return Ok(Pattern::As(n, Box::new(inner)));
            }
            return Ok(p);
        }
        Ok(p)
    }

    fn parse_pattern_atom(&mut self) -> PR<Pattern> {
        Ok(match self.peek().clone() {
            Tok::Underscore => { self.bump(); Pattern::Wildcard }
            Tok::Ident(n)   => { self.bump(); Pattern::Var(n) }
            Tok::Int(n)     => { self.bump(); Pattern::Int(n) }
            Tok::Float(f)   => { self.bump(); Pattern::Float(f) }
            Tok::Str(s)     => { self.bump(); Pattern::Str(s) }
            Tok::Atom(a)    => { self.bump(); Pattern::Atom(a) }
            Tok::True       => { self.bump(); Pattern::Bool(true) }
            Tok::False      => { self.bump(); Pattern::Bool(false) }
            Tok::Nil        => { self.bump(); Pattern::Nil }
            Tok::Minus => {
                self.bump();
                match self.bump() {
                    Tok::Int(n) => Pattern::Int(-n),
                    Tok::Float(f) => Pattern::Float(-f),
                    other => return self.err(format!("expected number after `-`, got {:?}", other)),
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
                        if !self.eat(&Tok::Comma) { break; }
                        self.skip_newlines();
                    }
                }
                self.expect(&Tok::RBitstr, "`>>`")?;
                Pattern::Bitstring(fields)
            }
            Tok::LBrack => {
                self.bump();
                let mut elems = Vec::new();
                let mut tail: Option<Box<Pattern>> = None;
                self.skip_newlines();
                if !matches!(self.peek(), Tok::RBrack) {
                    loop {
                        elems.push(self.parse_pattern()?);
                        self.skip_newlines();
                        if self.eat(&Tok::Bar) {
                            tail = Some(Box::new(self.parse_pattern()?));
                            break;
                        }
                        if !self.eat(&Tok::Comma) { break; }
                        self.skip_newlines();
                    }
                }
                self.expect(&Tok::RBrack, "`]`")?;
                Pattern::List(elems, tail)
            }
            Tok::PercentLBrace => {
                self.bump();
                let mut pairs: Vec<(Pattern, Pattern)> = Vec::new();
                self.skip_newlines();
                if !matches!(self.peek(), Tok::RBrace) {
                    loop {
                        // atom-key shorthand: `k: pat`
                        let key = if let Tok::KwKey(_) = self.peek() {
                            let Tok::KwKey(name) = self.bump() else { unreachable!() };
                            Pattern::Atom(name)
                        } else {
                            let k = self.parse_pattern_atom()?;
                            self.expect(&Tok::FatArrow, "`=>`")?;
                            k
                        };
                        // For atom-shorthand the `:` was the delimiter; otherwise we
                        // already consumed `=>`.
                        let val = self.parse_pattern()?;
                        pairs.push((key, val));
                        self.skip_newlines();
                        if !self.eat(&Tok::Comma) { break; }
                        self.skip_newlines();
                    }
                }
                self.expect(&Tok::RBrace, "`}`")?;
                Pattern::Map(pairs)
            }
            other => return self.err(format!("invalid pattern start {:?}", other)),
        })
    }

    // --- expressions (Pratt) ---

    pub fn parse_expr(&mut self) -> PR<Expr> { self.parse_bp(0) }

    /// REPL helper: parse a single expression and assert end-of-input.
    /// Used by the REPL when the input doesn't start a fn definition.
    pub fn parse_expr_eof(&mut self) -> PR<Expr> {
        self.skip_newlines();
        let e = self.parse_expr()?;
        self.skip_newlines();
        if !matches!(self.peek(), Tok::Eof) {
            return self.err(format!("trailing tokens after expression: {:?}", self.peek()));
        }
        Ok(e)
    }

    fn infix_bp(t: &Tok) -> Option<(u8, u8, BinOp)> {
        // (left, right, op). left < right => left-associative.
        Some(match t {
            Tok::Pipe   => (10, 11, BinOp::Pipe),
            Tok::OrOr   => (20, 21, BinOp::Or),
            Tok::AndAnd => (30, 31, BinOp::And),
            Tok::EqEq   => (40, 41, BinOp::Eq),
            Tok::NotEq  => (40, 41, BinOp::Neq),
            Tok::Lt     => (50, 51, BinOp::Lt),
            Tok::LtEq   => (50, 51, BinOp::LtEq),
            Tok::Gt     => (50, 51, BinOp::Gt),
            Tok::GtEq   => (50, 51, BinOp::GtEq),
            Tok::Plus   => (60, 61, BinOp::Add),
            Tok::Minus  => (60, 61, BinOp::Sub),
            Tok::Star   => (70, 71, BinOp::Mul),
            Tok::Slash  => (70, 71, BinOp::Div),
            Tok::Percent => (70, 71, BinOp::Rem),
            _ => return None,
        })
    }

    fn parse_bp(&mut self, min_bp: u8) -> PR<Expr> {
        let mut lhs = self.parse_prefix()?;
        loop {
            // postfix call / dot
            match self.peek() {
                Tok::LParen => {
                    self.bump();
                    let mut args = self.parse_expr_list(&Tok::RParen)?;
                    self.expect(&Tok::RParen, "`)`")?;
                    // Trailing do-block sugar: `f(args) do <body> end`
                    // appends <body> as a positional arg, and
                    // `f(args), do: <expr>` does the same with a single
                    // expr. Macros (e.g. test "x" do ... end) pull this
                    // last arg out as their body.
                    if matches!(self.peek(), Tok::Do) {
                        self.bump();
                        self.skip_newlines();
                        let body = self.parse_block_until(&[Tok::End])?;
                        self.expect(&Tok::End, "`end`")?;
                        args.push(body);
                    } else if matches!(self.peek(), Tok::Comma)
                        && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do")
                    {
                        self.bump(); self.bump();
                        let body = self.parse_expr()?;
                        args.push(body);
                    }
                    lhs = Expr::Call(Box::new(lhs), args);
                    continue;
                }
                Tok::Dot => {
                    self.bump();
                    let name = match self.bump() {
                        Tok::Ident(n) => n,
                        Tok::Upper(n) => n,
                        other => return self.err(format!("expected name after `.`, got {:?}", other)),
                    };
                    // `m.k` desugars to `m[:k]` when looking up a map key. We
                    // keep it as Dot in the AST and let the interpreter pick
                    // the right behavior — but since we don't have records, do
                    // it now: treat as Index on an atom.
                    lhs = Expr::Index(Box::new(lhs), Box::new(Expr::Atom(name)));
                    continue;
                }
                Tok::LBrack => {
                    self.bump();
                    let key = self.parse_expr()?;
                    self.expect(&Tok::RBrack, "`]`")?;
                    lhs = Expr::Index(Box::new(lhs), Box::new(key));
                    continue;
                }
                _ => {}
            }
            // = (match/bind) is right-assoc, lowest among these
            if matches!(self.peek(), Tok::Eq) {
                if min_bp > 5 { break; }
                self.bump();
                let rhs = self.parse_bp(5)?;
                let pat = expr_to_pattern(&lhs)?;
                lhs = Expr::Match(pat, Box::new(rhs));
                continue;
            }
            let Some((lbp, rbp, op)) = Self::infix_bp(self.peek()) else { break };
            if lbp < min_bp { break; }
            self.bump();
            let rhs = self.parse_bp(rbp)?;
            lhs = Expr::BinOp(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_prefix(&mut self) -> PR<Expr> {
        Ok(match self.peek().clone() {
            Tok::Int(n)   => { self.bump(); Expr::Int(n) }
            Tok::Float(f) => { self.bump(); Expr::Float(f) }
            Tok::Str(s)   => { self.bump(); Expr::Str(s) }
            Tok::Atom(a)  => { self.bump(); Expr::Atom(a) }
            Tok::True     => { self.bump(); Expr::Bool(true) }
            Tok::False    => { self.bump(); Expr::Bool(false) }
            Tok::Nil      => { self.bump(); Expr::Nil }
            Tok::Ident(n) => { self.bump(); Expr::Var(n) }
            Tok::Upper(n) => { self.bump(); Expr::Var(n) } // module ref; we'll resolve later
            Tok::Minus    => { self.bump(); let e = self.parse_bp(80)?; Expr::UnOp(UnOp::Neg, Box::new(e)) }
            Tok::Bang     => { self.bump(); let e = self.parse_bp(80)?; Expr::UnOp(UnOp::Not, Box::new(e)) }
            Tok::LParen => {
                self.bump();
                self.skip_newlines();
                let e = self.parse_expr()?;
                self.skip_newlines();
                self.expect(&Tok::RParen, "`)`")?;
                e
            }
            Tok::LBrack => {
                self.bump();
                let mut elems = Vec::new();
                let mut tail: Option<Box<Expr>> = None;
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
                        if !self.eat(&Tok::Comma) { break; }
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
            Tok::PercentLBrace => self.parse_map_expr()?,
            Tok::If => self.parse_if()?,
            Tok::Case => self.parse_case()?,
            Tok::With => self.parse_with()?,
            Tok::Do => {
                self.bump();
                self.skip_newlines();
                let blk = self.parse_block_until(&[Tok::End])?;
                self.expect(&Tok::End, "`end`")?;
                blk
            }
            Tok::Fn => self.parse_lambda()?,
            Tok::Quote => self.parse_quote()?,
            Tok::Unquote => self.parse_unquote()?,
            Tok::LBitstr => self.parse_bitstring_expr()?,
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
        })
    }

    fn parse_expr_list(&mut self, terminator: &Tok) -> PR<Vec<Expr>> {
        let mut out = Vec::new();
        self.skip_newlines();
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(terminator) { return Ok(out); }
        loop {
            out.push(self.parse_expr()?);
            self.skip_newlines();
            if !self.eat(&Tok::Comma) { break; }
            self.skip_newlines();
        }
        Ok(out)
    }

    fn parse_block_until(&mut self, stops: &[Tok]) -> PR<Expr> {
        let mut exprs = Vec::new();
        loop {
            self.skip_newlines();
            if stops.iter().any(|s| std::mem::discriminant(self.peek()) == std::mem::discriminant(s)) {
                break;
            }
            if matches!(self.peek(), Tok::Eof) { break; }
            exprs.push(self.parse_expr()?);
            // require newline / semi / a stop after each expr
            if !matches!(self.peek(), Tok::Newline | Tok::Semi) {
                if stops.iter().any(|s| std::mem::discriminant(self.peek()) == std::mem::discriminant(s)) {
                    break;
                }
                if matches!(self.peek(), Tok::Eof) { break; }
                return self.err(format!("expected newline between expressions, got {:?}", self.peek()));
            }
        }
        Ok(if exprs.len() == 1 { exprs.pop().unwrap() } else { Expr::Block(exprs) })
    }

    /// `quote do: <expr>` (one-line shorthand) or `quote do <stmts> end`.
    fn parse_quote(&mut self) -> PR<Expr> {
        self.expect(&Tok::Quote, "`quote`")?;
        // `, do: <expr>` shorthand
        if matches!(self.peek(), Tok::Comma) && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do") {
            self.bump(); // ,
            self.bump(); // do:
            let e = self.parse_expr()?;
            return Ok(Expr::Quote(Box::new(e)));
        }
        // `do: <expr>` without leading comma
        if matches!(self.peek(), Tok::KwKey(s) if s == "do") {
            self.bump();
            let e = self.parse_expr()?;
            return Ok(Expr::Quote(Box::new(e)));
        }
        self.expect(&Tok::Do, "`do` or `do:` after `quote`")?;
        self.skip_newlines();
        let body = self.parse_block_until(&[Tok::End])?;
        self.expect(&Tok::End, "`end`")?;
        Ok(Expr::Quote(Box::new(body)))
    }

    /// `unquote(<expr>)`.
    fn parse_unquote(&mut self) -> PR<Expr> {
        self.expect(&Tok::Unquote, "`unquote`")?;
        self.expect(&Tok::LParen, "`(` after `unquote`")?;
        self.skip_newlines();
        let e = self.parse_expr()?;
        self.skip_newlines();
        self.expect(&Tok::RParen, "`)`")?;
        Ok(Expr::Unquote(Box::new(e)))
    }

    fn parse_if(&mut self) -> PR<Expr> {
        self.expect(&Tok::If, "`if`")?;
        let cond = self.parse_expr()?;
        // either `, do: expr [, else: expr]` or `do ... [else ...] end`
        if matches!(self.peek(), Tok::Comma) && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do") {
            self.bump(); // ,
            self.bump(); // do:
            let then = self.parse_expr()?;
            let els = if matches!(self.peek(), Tok::Comma) && matches!(self.peek_at(1), Tok::KwKey(s) if s == "else") {
                self.bump(); self.bump();
                Some(Box::new(self.parse_expr()?))
            } else { None };
            return Ok(Expr::If(Box::new(cond), Box::new(then), els));
        }
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let then = self.parse_block_until(&[Tok::Else, Tok::End])?;
        let els = if self.eat(&Tok::Else) {
            self.skip_newlines();
            Some(Box::new(self.parse_block_until(&[Tok::End])?))
        } else { None };
        self.expect(&Tok::End, "`end`")?;
        Ok(Expr::If(Box::new(cond), Box::new(then), els))
    }

    fn parse_case(&mut self) -> PR<Expr> {
        self.expect(&Tok::Case, "`case`")?;
        let scrut = self.parse_expr()?;
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let mut clauses = Vec::new();
        while !matches!(self.peek(), Tok::End | Tok::Eof) {
            let pat = self.parse_pattern()?;
            let guard = if matches!(self.peek(), Tok::When) {
                self.bump();
                Some(self.parse_expr()?)
            } else { None };
            self.expect(&Tok::Arrow, "`->`")?;
            self.skip_newlines();
            // v0: a clause body is a single expression. Wrap in `do ... end` for blocks.
            let body = self.parse_expr()?;
            clauses.push(MatchClause { pattern: pat, guard, body });
            self.skip_newlines();
        }
        self.expect(&Tok::End, "`end`")?;
        Ok(Expr::Case(Box::new(scrut), clauses))
    }

    fn parse_bitstring_expr(&mut self) -> PR<Expr> {
        self.expect(&Tok::LBitstr, "`<<`")?;
        let mut fields: Vec<BitField<Expr>> = Vec::new();
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
                if !self.eat(&Tok::Comma) { break; }
                self.skip_newlines();
            }
        }
        self.expect(&Tok::RBitstr, "`>>`")?;
        Ok(Expr::Bitstring(fields))
    }

    /// Parse a `::`-suffix bitstring spec like `8`, `little-integer-32`,
    /// `binary-size(len)`, `unit(4)-size(n)`. Modifiers separated by `-`.
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
            if !self.eat(&Tok::Minus) { break; }
        }
        Ok(spec)
    }

    fn apply_bit_modifier(&mut self, spec: &mut BitFieldSpec, name: &str) -> PR<()> {
        match name {
            "integer" => spec.ty = BitType::Integer,
            "float"   => spec.ty = BitType::Float,
            "binary"  => spec.ty = BitType::Binary,
            "bits" | "bitstring" => spec.ty = BitType::Bits,
            "utf8"    => spec.ty = BitType::Utf8,
            "utf16"   => spec.ty = BitType::Utf16,
            "utf32"   => spec.ty = BitType::Utf32,
            "big"     => spec.endian = Endian::Big,
            "little"  => spec.endian = Endian::Little,
            "native"  => spec.endian = Endian::Native,
            "signed"   => spec.signed = true,
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

    fn parse_with(&mut self) -> PR<Expr> {
        self.expect(&Tok::With, "`with`")?;
        let mut bindings: Vec<WithBinding> = Vec::new();
        loop {
            self.skip_newlines();
            // A binding is either `pat <- expr` or a bare expression.
            // We try-parse a pattern + `<-`; if the `<-` isn't there we treat
            // what we parsed as a bare expression instead.
            let saved = self.pos;
            let try_pat = self.parse_pattern();
            if let Ok(pat) = try_pat {
                if matches!(self.peek(), Tok::LArrow) {
                    self.bump();
                    let e = self.parse_expr()?;
                    bindings.push(WithBinding::Match(pat, e));
                } else {
                    // not a binding — restore and parse as bare expr
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
            if matches!(self.peek(), Tok::Comma) {
                self.bump();
                continue;
            }
            break;
        }
        // Body: either `, do: expr` shorthand OR `do ... end` (with optional `else`).
        let body;
        let mut else_clauses: Vec<MatchClause> = Vec::new();
        if matches!(self.peek(), Tok::Comma) && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do") {
            self.bump(); self.bump();
            body = self.parse_expr()?;
        } else {
            self.expect(&Tok::Do, "`do`")?;
            self.skip_newlines();
            body = self.parse_block_until(&[Tok::Else, Tok::End])?;
            if self.eat(&Tok::Else) {
                self.skip_newlines();
                while !matches!(self.peek(), Tok::End | Tok::Eof) {
                    let pat = self.parse_pattern()?;
                    let guard = if matches!(self.peek(), Tok::When) {
                        self.bump();
                        Some(self.parse_expr()?)
                    } else { None };
                    self.expect(&Tok::Arrow, "`->`")?;
                    self.skip_newlines();
                    let cb = self.parse_expr()?;
                    else_clauses.push(MatchClause { pattern: pat, guard, body: cb });
                    self.skip_newlines();
                }
            }
            self.expect(&Tok::End, "`end`")?;
        }
        Ok(Expr::With(bindings, Box::new(body), else_clauses))
    }

    /// `%{ k: v, ... }`, `%{ k => v, ... }`, or `%{ base | k: v, ... }`.
    /// Mixed `:` (atom-key shorthand) and `=>` are allowed in the same literal.
    fn parse_map_expr(&mut self) -> PR<Expr> {
        self.expect(&Tok::PercentLBrace, "`%{`")?;
        self.skip_newlines();
        // Detect update form by looking ahead for `|` before `}` at depth 0.
        // Easiest: try parsing an expression; if next token is `|`, it's update.
        let base = if !matches!(self.peek(), Tok::RBrace) {
            // Tentative: parse the first key/expr. If we see `|`, base = that expr.
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
                    return Ok(Expr::Map(pairs));
                }
            }
        } else {
            self.expect(&Tok::RBrace, "`}`")?;
            return Ok(Expr::Map(vec![]));
        };
        // Update form: `%{ base | pairs }`
        let base = base.unwrap();
        self.skip_newlines();
        let mut pairs: Vec<(Expr, Expr)> = Vec::new();
        if !matches!(self.peek(), Tok::RBrace) {
            self.parse_map_pairs_into(&mut pairs)?;
        }
        self.skip_newlines();
        self.expect(&Tok::RBrace, "`}`")?;
        Ok(Expr::MapUpdate(Box::new(base), pairs))
    }

    /// First segment of `%{...}`: either an `update | ...` head, a single
    /// pair, or empty. Disambiguated by what follows the first sub-expression.
    fn parse_map_first_segment(&mut self) -> PR<MapHead> {
        // Atom-key shorthand at the head: `%{a: 1, ...}`
        if let Tok::KwKey(_) = self.peek() {
            let Tok::KwKey(name) = self.bump() else { unreachable!() };
            let v = self.parse_expr()?;
            return Ok(MapHead::Pair(Expr::Atom(name), v));
        }
        let first = self.parse_expr()?;
        // Update?  `base | ...`
        if matches!(self.peek(), Tok::Bar) {
            self.bump();
            return Ok(MapHead::Update(first));
        }
        if self.eat(&Tok::FatArrow) {
            let v = self.parse_expr()?;
            return Ok(MapHead::Pair(first, v));
        }
        self.err(format!("expected `=>` or `|` in map literal, got {:?}", self.peek()))
    }

    fn parse_map_pairs_into(&mut self, pairs: &mut Vec<(Expr, Expr)>) -> PR<()> {
        loop {
            self.skip_newlines();
            // atom shorthand
            if let Tok::KwKey(_) = self.peek() {
                let Tok::KwKey(name) = self.bump() else { unreachable!() };
                let v = self.parse_expr()?;
                pairs.push((Expr::Atom(name), v));
            } else {
                let k = self.parse_expr()?;
                if !self.eat(&Tok::FatArrow) {
                    return self.err(format!("expected `=>` after map key, got {:?}", self.peek()));
                }
                let v = self.parse_expr()?;
                pairs.push((k, v));
            }
            self.skip_newlines();
            if !self.eat(&Tok::Comma) { break; }
        }
        Ok(())
    }

    fn parse_lambda(&mut self) -> PR<Expr> {
        self.expect(&Tok::Fn, "`fn`")?;
        // `fn (p, ...) -> body` or `fn p -> body`
        let params = if self.eat(&Tok::LParen) {
            let ps = self.parse_pattern_list(&Tok::RParen)?;
            self.expect(&Tok::RParen, "`)`")?;
            ps
        } else {
            vec![self.parse_pattern()?]
        };
        self.expect(&Tok::Arrow, "`->`")?;
        let body = self.parse_expr()?;
        Ok(Expr::Lambda(params, Box::new(body)))
    }
}

enum MapHead {
    Pair(Expr, Expr),
    Update(Expr),
}

/// LHS of `=` is a pattern; convert.
fn expr_to_pattern(e: &Expr) -> PR<Pattern> {
    Ok(match e {
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
            pairs.iter()
                .map(|(k, v)| Ok::<_, ParseError>((expr_to_pattern(k)?, expr_to_pattern(v)?)))
                .collect::<PR<_>>()?,
        ),
        Expr::List(xs, tail) => Pattern::List(
            xs.iter().map(expr_to_pattern).collect::<PR<_>>()?,
            tail.as_deref().map(|e| expr_to_pattern(e).map(Box::new)).transpose()?,
        ),
        _ => return Err(ParseError {
            msg: format!("expression cannot be used as pattern: {:?}", e),
            line: 0, col: 0,
        }),
    })
}
