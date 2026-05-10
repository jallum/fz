use crate::ast::*;
use crate::lexer::{Tok, Token};
use std::rc::Rc;

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
        let mut items: Vec<Rc<Item>> = Vec::new();
        // Group fn clauses by name in declaration order.
        let mut order: Vec<String> = Vec::new();
        let mut groups: std::collections::HashMap<String, FnDef> =
            std::collections::HashMap::new();

        self.skip_newlines();
        while !matches!(self.peek(), Tok::Eof) {
            let is_macro = match self.peek() {
                Tok::Defmacro => { self.bump(); true }
                Tok::Fn => { self.bump(); false }
                _ => return self.err(format!("expected `fn` or `defmacro` at top level, got {:?}", self.peek())),
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

            // body: either `, do: expr` shorthand OR `do ... end`
            let body = if matches!(self.peek(), Tok::Comma) && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do") {
                self.bump(); // ,
                self.bump(); // do:
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

            let clause = FnClause { params, guard, body };
            if let Some(def) = groups.get_mut(&name) {
                if def.is_macro != is_macro {
                    return self.err(format!("`{}` declared as both fn and defmacro", name));
                }
                def.clauses.push(clause);
            } else {
                order.push(name.clone());
                groups.insert(name.clone(), FnDef { name, clauses: vec![clause], is_macro });
            }

            self.skip_newlines();
        }

        for name in order {
            if let Some(def) = groups.remove(&name) {
                items.push(Rc::new(Item::Fn(def)));
            }
        }
        Ok(Program { items })
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
            other => return self.err(format!("invalid pattern start {:?}", other)),
        })
    }

    // --- expressions (Pratt) ---

    fn parse_expr(&mut self) -> PR<Expr> { self.parse_bp(0) }

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
                    let args = self.parse_expr_list(&Tok::RParen)?;
                    self.expect(&Tok::RParen, "`)`")?;
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
                    lhs = Expr::Dot(Box::new(lhs), name);
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
