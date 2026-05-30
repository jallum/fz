use super::*;

/// Binding power for unary prefixes (`-`, `!`, `not`). Above every infix level
/// (Mul tops out at 110/111) so unary binds tightest, matching Elixir's
/// unary_op precedence (300): `-a * b` is `(-a) * b`, not `-(a * b)`.
const UNARY_BP: u8 = 120;

struct CallArgs {
    args: Vec<Spanned<Expr>>,
    keyword_arg_index: Option<usize>,
}

impl Parser {
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

    /// Infix binding powers, mirroring Elixir's operator precedence (higher
    /// binds tighter). Left-associative ops use `(n, n+1)`; right-associative
    /// ops use `(n+1, n)`. Two operators sit outside this table: `=` (match,
    /// Elixir level 100) is handled separately at min-bp 5, and the unary
    /// prefixes `-`/`!`/`not` (Elixir 300) bind tightest via `parse_bp(UNARY_BP)`.
    /// `not in` is two tokens, resolved directly in `parse_bp`.
    pub(super) fn infix_bp(t: &Tok) -> Option<(u8, u8, BinOp)> {
        Some(match t {
            Tok::OrOr => (20, 21, BinOp::Or),    // Elixir 120
            Tok::AndAnd => (30, 31, BinOp::And), // Elixir 130
            Tok::EqEq => (40, 41, BinOp::Eq),    // Elixir 140
            Tok::NotEq => (40, 41, BinOp::Neq),
            Tok::Lt => (50, 51, BinOp::Lt), // Elixir 150
            Tok::LtEq => (50, 51, BinOp::LtEq),
            Tok::Gt => (50, 51, BinOp::Gt),
            Tok::GtEq => (50, 51, BinOp::GtEq),
            Tok::Pipe => (60, 61, BinOp::Pipe), // |>  Elixir 160
            Tok::In => (70, 71, BinOp::In),     // in  Elixir 170
            Tok::SlashSlash => (81, 80, BinOp::RangeStep), // //  Elixir 190, right
            Tok::PlusPlus => (91, 90, BinOp::ListConcat), // ++  Elixir 200, right
            Tok::MinusMinus => (91, 90, BinOp::ListSubtract), // --
            Tok::Concat => (91, 90, BinOp::BinConcat), // <>
            Tok::DotDot => (91, 90, BinOp::Range), // ..  Elixir 200, right
            Tok::Plus => (100, 101, BinOp::Add), // Elixir 210
            Tok::Minus => (100, 101, BinOp::Sub),
            Tok::Star => (110, 111, BinOp::Mul), // Elixir 220
            Tok::Slash => (110, 111, BinOp::Div),
            Tok::Percent => (110, 111, BinOp::Rem),
            _ => return None,
        })
    }

    pub(super) fn parse_bp(&mut self, min_bp: u8) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        let mut lhs = self.parse_prefix()?;
        loop {
            if matches!(self.peek(), Tok::Newline)
                && Self::starts_expr_continuation(self.peek_after_newlines())
            {
                self.skip_newline_tokens();
            }
            match self.peek() {
                Tok::LParen => {
                    self.bump();
                    let mut call_args = self.parse_call_args()?;
                    self.expect(&Tok::RParen, "`)`")?;
                    if !self.suppress_trailing_do && matches!(self.peek(), Tok::Do) {
                        self.bump();
                        self.skip_newlines();
                        let body = self.parse_block_until(&[Tok::End])?;
                        self.expect(&Tok::End, "`end`")?;
                        Self::append_keyword_arg(&mut call_args, "do".to_string(), body);
                    } else if !self.suppress_trailing_do
                        && matches!(self.peek(), Tok::Comma)
                        && matches!(self.peek_at(1), Tok::KwKey(s) if s == "do")
                    {
                        self.bump();
                        let body = self.parse_keyword_pair()?.1;
                        Self::append_keyword_arg(&mut call_args, "do".to_string(), body);
                    }
                    let span = start.merge(self.prev_span());
                    lhs = Spanned::new(Expr::Call(Box::new(lhs), call_args.args), span);
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
                self.skip_newline_tokens();
                let rhs = self.parse_bp(5)?;
                let pat = expr_to_pattern(&lhs)?;
                let span = start.merge(self.prev_span());
                lhs = Spanned::new(Expr::Match(pat, Box::new(rhs)), span);
                continue;
            }
            // `not in` is two tokens; bind it at `in`'s level (Elixir 170).
            if matches!(self.peek(), Tok::Not) && matches!(self.peek_at(1), Tok::In) {
                let (lbp, rbp) = (70u8, 71u8);
                if lbp < min_bp {
                    break;
                }
                self.bump(); // not
                self.bump(); // in
                self.skip_newline_tokens();
                let rhs = self.parse_bp(rbp)?;
                let span = start.merge(self.prev_span());
                lhs = Spanned::new(
                    Expr::BinOp(BinOp::NotIn, Box::new(lhs), Box::new(rhs)),
                    span,
                );
                continue;
            }
            // No-parens call: a callable head followed by a space-separated
            // argument (`foo a, b`, `Enum.map xs, fn`). The arguments are full
            // expressions; greedy comma separation at statement/operand
            // position, single-arg inside a comma-delimited container.
            if Self::expr_is_callable_head(&lhs.node) && self.starts_no_parens_arg() {
                let mut call_args = self.parse_no_parens_args()?;
                self.attach_trailing_do(&mut call_args)?;
                let span = start.merge(self.prev_span());
                lhs = Spanned::new(Expr::Call(Box::new(lhs), call_args.args), span);
                self.saw_no_parens_call = true;
                continue;
            }
            // Bare `do … end` after a callable head with no positional args:
            // `foo do … end` is `foo([do: …])`, matching Elixir. Suppressed in
            // cond positions, where the block belongs to the surrounding form.
            if Self::expr_is_callable_head(&lhs.node)
                && !self.suppress_trailing_do
                && matches!(self.peek(), Tok::Do)
            {
                let mut call_args = CallArgs {
                    args: Vec::new(),
                    keyword_arg_index: None,
                };
                self.attach_trailing_do(&mut call_args)?;
                let span = start.merge(self.prev_span());
                lhs = Spanned::new(Expr::Call(Box::new(lhs), call_args.args), span);
                self.saw_no_parens_call = true;
                continue;
            }
            let Some((lbp, rbp, op)) = Self::infix_bp(self.peek()) else {
                break;
            };
            if lbp < min_bp {
                break;
            }
            self.bump();
            self.skip_newline_tokens();
            let rhs = self.parse_bp(rbp)?;
            let span = start.merge(self.prev_span());
            lhs = Spanned::new(Expr::BinOp(op, Box::new(lhs), Box::new(rhs)), span);
        }
        Ok(lhs)
    }

    fn starts_expr_continuation(tok: &Tok) -> bool {
        matches!(tok, Tok::Dot | Tok::Eq) || Self::infix_bp(tok).is_some()
    }

    /// A callable head for a no-parens call: a bare name (`foo`) or a
    /// module-qualified path (`Enum.map`, lowered to `Index`). Literals,
    /// completed calls, and operators are not heads.
    fn expr_is_callable_head(e: &Expr) -> bool {
        matches!(e, Expr::Var(_) | Expr::Index(_, _))
    }

    /// True when the current token can begin a no-parens call argument: it is
    /// separated from the head by trivia and is a value-starting token, not an
    /// operator, container close, or block keyword. `(` and `[` are excluded
    /// (the postfix loop owns them as paren-call and index). `+`/`-` count
    /// only when unary-positioned — space before the op, none before its
    /// operand — so `foo -1` is the argument `-1` while `foo - 1` is binary.
    fn starts_no_parens_arg(&self) -> bool {
        if !self.space_before_at(0) {
            return false;
        }
        match self.peek() {
            Tok::Int(_)
            | Tok::Float(_)
            | Tok::Binary(_)
            | Tok::Atom(_)
            | Tok::True
            | Tok::False
            | Tok::Nil
            | Tok::Ident(_)
            | Tok::Upper(_)
            | Tok::LBrace
            | Tok::PercentLBrace
            | Tok::LBitstr
            | Tok::Fn
            | Tok::KwKey(_)
            | Tok::Amp => true,
            Tok::Minus | Tok::Plus => !self.space_before_at(1),
            _ => false,
        }
    }

    /// Parse the arguments of a no-parens call. Each positional argument is a
    /// full expression parsed in a fresh (comma-unbound) context, so a nested
    /// no-parens call owns its own commas (`f g a, b` is `f(g(a, b))`). At
    /// statement/operand position arguments are comma-separated greedily;
    /// inside a comma-delimited container only one argument is taken, leaving
    /// the comma to the container.
    ///
    /// Trailing `key: value` pairs collapse into a single keyword-list
    /// argument appended last (`foo a, b: 1` is `foo(a, [b: 1])`), matching
    /// Elixir. A keyword key in head position makes the whole argument list a
    /// lone keyword list (`foo b: 1` is `foo([b: 1])`).
    ///
    /// Returns `CallArgs` so the do-block sugar can extend the trailing keyword
    /// list precisely: `keyword_arg_index` marks the collapsed keyword argument
    /// (if any), never a positional list literal — `foo [a: 1] do … end` keeps
    /// `[a: 1]` positional and adds a separate `[do: …]`, matching Elixir.
    fn parse_no_parens_args(&mut self) -> PR<CallArgs> {
        if matches!(self.peek(), Tok::KwKey(_)) {
            let kw = self.parse_no_parens_keyword_list()?;
            return Ok(CallArgs {
                args: vec![kw],
                keyword_arg_index: Some(0),
            });
        }
        let mut args = vec![self.with_comma_unbound(|p| p.parse_expr())?];
        if self.comma_bound {
            return Ok(CallArgs {
                args,
                keyword_arg_index: None,
            });
        }
        let mut keyword_arg_index = None;
        while self.eat(&Tok::Comma) {
            self.skip_newlines();
            if matches!(self.peek(), Tok::KwKey(_)) {
                args.push(self.parse_no_parens_keyword_list()?);
                keyword_arg_index = Some(args.len() - 1);
                break;
            }
            args.push(self.with_comma_unbound(|p| p.parse_expr())?);
        }
        Ok(CallArgs {
            args,
            keyword_arg_index,
        })
    }

    /// Attach a trailing `do … end` block to a no-parens call as a `do:`
    /// keyword argument, when the trailing-do sugar is enabled (it is
    /// suppressed in cond positions, where the block belongs to the
    /// surrounding `if`/`case`/… instead). Extends the call's trailing keyword
    /// list, or creates one — the same shape the paren-call path produces in
    /// `parse_bp`. The `, do:` shorthand needs no handling here: a keyword key
    /// after a comma is already collected by `parse_no_parens_keyword_list`.
    fn attach_trailing_do(&mut self, call_args: &mut CallArgs) -> PR<()> {
        if self.suppress_trailing_do || !matches!(self.peek(), Tok::Do) {
            return Ok(());
        }
        self.bump();
        self.skip_newlines();
        let body = self.parse_block_until(&[Tok::End])?;
        self.expect(&Tok::End, "`end`")?;
        Self::append_keyword_arg(call_args, "do".to_string(), body);
        Ok(())
    }

    /// Parse a comma-separated run of `key: value` pairs into a single keyword
    /// list (`Expr::List` of `{key, value}` tuples). Stops at the first token
    /// that does not continue the list — a newline, `end`, EOF, or any
    /// non-comma — without consuming it. Positional expressions cannot follow a
    /// keyword entry, so a comma must be followed by another keyword key.
    fn parse_no_parens_keyword_list(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        let mut entries = Vec::new();
        loop {
            let key_span = self.cur_span();
            let key = self.bump_keyword_key()?;
            let key = Spanned::new(Expr::Atom(key.node), key.span);
            self.skip_newlines();
            self.saw_no_parens_call = false;
            let value = self.with_comma_bound(|p| p.parse_expr())?;
            let value_is_no_parens_call =
                self.saw_no_parens_call && matches!(value.node, Expr::Call(_, _));
            entries.push(Self::keyword_pair_expr(key, value));

            let continues = self.at(&Tok::Comma) && matches!(self.peek_at(1), Tok::KwKey(_));
            // Elixir warns (and binds the trailing keyword into the inner call)
            // when a no-parens call is a keyword value with another keyword
            // entry after it: `b: bar x, c: 2` could mean `bar(x, c: 2)` or
            // `bar(x)` plus `c: 2`. fz keeps the trailing keyword in the outer
            // list; the diagnostic flags the divergence so the source can be
            // disambiguated with explicit parens.
            if continues && value_is_no_parens_call {
                let span = key_span.merge(self.prev_span());
                self.warn(
                    crate::diag::Diagnostic::warning(
                        crate::diag::codes::PARSE_AMBIGUOUS_NO_PARENS_KEYWORD,
                        "no-parens call as a keyword value before another keyword \
                         is ambiguous; add parentheses around the call's arguments",
                        span,
                    )
                    .with_label("this call's arguments may extend past the comma"),
                );
            }
            if !continues {
                break;
            }
            self.bump(); // comma
        }
        Ok(Spanned::new(Expr::List(entries, None), self.finish(start)))
    }

    pub(super) fn parse_prefix(&mut self) -> PR<Spanned<Expr>> {
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
            Tok::Binary(bytes) => {
                self.bump();
                // fz-axu.10 (L2) — Expr::Binary carries raw bytes; L3
                // validates UTF-8 and mints the utf8 brand.
                Expr::Binary(bytes)
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
                // fz-y3k — `libc::open` in expression position resolves to
                // a Var whose name matches the extern's fz_name in the
                // module's externs table. Require token adjacency so
                // `arg :: type` remains available for call-arg ascription.
                if matches!(self.peek(), Tok::ColonColon)
                    && self.prev_span().end == self.cur_span().start
                {
                    self.bump();
                    match self.bump() {
                        Tok::Ident(s) => Expr::Var(format!("{}::{}", n, s)),
                        other => {
                            return self
                                .err(format!("expected name after `{}::`, got {:?}", n, other));
                        }
                    }
                } else {
                    Expr::Var(n)
                }
            }
            Tok::Upper(n) => {
                self.bump();
                Expr::Var(n)
            }
            Tok::Minus => {
                self.bump();
                let e = self.parse_bp(UNARY_BP)?;
                Expr::UnOp(UnOp::Neg, Box::new(e))
            }
            Tok::Bang => {
                self.bump();
                let e = self.parse_bp(UNARY_BP)?;
                Expr::UnOp(UnOp::Not, Box::new(e))
            }
            Tok::Not => {
                self.bump();
                let e = self.parse_bp(UNARY_BP)?;
                Expr::UnOp(UnOp::Not, Box::new(e))
            }
            // `&` introduces one of three capture forms, disambiguated by the
            // single token after it (fz-g58.2.6):
            //   `&N`        — capture placeholder (an adjacent integer)
            //   `&(...)`    — capture expression over `&N` placeholders
            //   `&name/n`   — explicit function reference (fz-swt.5)
            // The first two desugar to a `Lambda` in fz-g58.15 (Arc 3).
            Tok::Amp
                if matches!(self.peek_at(1), Tok::Int(n) if *n >= 1)
                    && !self.space_before_at(1) =>
            {
                self.bump(); // &
                let Tok::Int(n) = self.bump() else {
                    unreachable!("guarded by the match arm");
                };
                Expr::CaptureArg(n as usize)
            }
            Tok::Amp if matches!(self.peek_at(1), Tok::LParen) => {
                self.bump(); // &
                self.bump(); // (
                self.skip_newlines();
                let body = self.with_comma_unbound(|p| p.parse_expr())?;
                self.skip_newlines();
                self.expect(&Tok::RParen, "`)` to close `&(...)` capture")?;
                Expr::Capture(Box::new(body))
            }
            // fz-swt.5: `&name/arity` or `&Mod.Sub.name/arity` — explicit
            // first-class function reference. `name` is captured as a
            // dotted string so the resolver/lowerer can do `(name, arity)`
            // lookup the same way Call does.
            Tok::Amp => {
                self.bump();
                let mut name = match self.bump() {
                    Tok::Ident(n) | Tok::Upper(n) => n,
                    other => {
                        return self.err(format!("expected name after `&`, got {:?}", other));
                    }
                };
                // Either a dotted name (`&Mod.Sub.fun/n`) or a library-
                // prefixed extern (`&libc::close/1`). Both join into a
                // single string that matches the entry in `ctx.fns` or
                // `ctx.externs` respectively.
                loop {
                    let sep = match self.peek() {
                        Tok::Dot => ".",
                        Tok::ColonColon => "::",
                        _ => break,
                    };
                    self.bump();
                    match self.bump() {
                        Tok::Ident(n) | Tok::Upper(n) => {
                            name.push_str(sep);
                            name.push_str(&n);
                        }
                        other => {
                            return self.err(format!(
                                "expected name after `{}` in `&...`, got {:?}",
                                sep, other
                            ));
                        }
                    }
                }
                self.expect(&Tok::Slash, "`/` after name in `&name/arity`")?;
                let arity = match self.bump() {
                    Tok::Int(n) if n >= 0 => n as usize,
                    other => {
                        return self.err(format!(
                            "expected non-negative integer arity after `/`, got {:?}",
                            other
                        ));
                    }
                };
                Expr::FnRef { name, arity }
            }
            Tok::LParen => {
                self.bump();
                self.skip_newlines();
                // A parenthesized expression is a fresh statement/operand
                // context: no-parens calls inside are greedy again.
                let e = self.with_comma_unbound(|p| p.parse_expr())?;
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
                        if matches!(self.peek(), Tok::KwKey(_)) {
                            elems.extend(self.parse_keyword_entries(&Tok::RBrack)?);
                            break;
                        }
                        elems.push(self.with_comma_bound(|p| p.parse_expr())?);
                        self.skip_newlines();
                        if self.eat(&Tok::Bar) {
                            self.skip_newlines();
                            tail = Some(Box::new(self.with_comma_bound(|p| p.parse_expr())?));
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
            Tok::Percent => return self.parse_struct_expr(),
            Tok::If => return self.parse_if(),
            Tok::Case => return self.parse_case(),
            Tok::Cond => return self.parse_cond(),
            Tok::With => return self.parse_with(),
            // fz-5vj — contextual: `receive do …` parses the new form;
            // `receive(...)` keeps working as a zero-arg function call
            // by emitting Expr::Var("receive") and letting postfix do
            // the call (lowering at src/ir_lower.rs:1111 still recognises
            // the name). fz-recv.A2 removes the bare-call form.
            Tok::Receive => {
                self.bump();
                if matches!(self.peek(), Tok::Do) {
                    return self.parse_receive_do(start);
                }
                Expr::Var("receive".to_string())
            }
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
                return self.err(format!("unsupported sigil ~{}", name));
            }
            Tok::Eof => return self.incomplete("unexpected end of input at expression start"),
            other => return self.err(format!("unexpected token {:?} at expression start", other)),
        };
        Ok(Spanned::new(node, self.finish(start)))
    }

    pub(super) fn parse_expr_list(&mut self, terminator: &Tok) -> PR<Vec<Spanned<Expr>>> {
        let mut out = Vec::new();
        self.skip_newlines();
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(terminator) {
            return Ok(out);
        }
        loop {
            out.push(self.with_comma_bound(|p| p.parse_expr())?);
            self.skip_newlines();
            if !self.eat(&Tok::Comma) {
                break;
            }
            self.skip_newlines();
        }
        Ok(out)
    }

    fn parse_call_args(&mut self) -> PR<CallArgs> {
        let mut out = Vec::new();
        let mut keyword_arg_index = None;
        self.skip_newlines();
        if matches!(self.peek(), Tok::RParen) {
            return Ok(CallArgs {
                args: out,
                keyword_arg_index,
            });
        }
        loop {
            if matches!(self.peek(), Tok::KwKey(_)) {
                keyword_arg_index = Some(out.len());
                out.push(self.parse_keyword_list_arg(&Tok::RParen)?);
                self.skip_newlines();
                if self.eat(&Tok::Comma) {
                    self.skip_newlines();
                }
                break;
            }
            let expr = self.with_comma_bound(|p| p.parse_expr())?;
            let arg = if self.eat(&Tok::ColonColon) {
                let mut ty_tokens = Vec::new();
                let mut depth = 0usize;
                loop {
                    match self.peek() {
                        Tok::LParen | Tok::LBrace | Tok::LBrack => {
                            depth += 1;
                            ty_tokens.push(self.toks[self.pos].clone());
                            self.bump();
                        }
                        Tok::RParen | Tok::RBrace | Tok::RBrack if depth > 0 => {
                            depth -= 1;
                            ty_tokens.push(self.toks[self.pos].clone());
                            self.bump();
                        }
                        Tok::Comma | Tok::RParen if depth == 0 => break,
                        Tok::Newline | Tok::Eof => break,
                        _ => {
                            ty_tokens.push(self.toks[self.pos].clone());
                            self.bump();
                        }
                    }
                }
                if ty_tokens.is_empty() {
                    return self.err("expected type expression after call argument `::`");
                }
                let span = expr.span.merge(self.prev_span());
                Spanned::new(
                    Expr::Ascribe(Box::new(expr), crate::ast::TypeExprBody(ty_tokens)),
                    span,
                )
            } else {
                expr
            };
            out.push(arg);
            self.skip_newlines();
            if !self.eat(&Tok::Comma) {
                break;
            }
            self.skip_newlines();
            if matches!(self.peek(), Tok::KwKey(_)) {
                keyword_arg_index = Some(out.len());
                out.push(self.parse_keyword_list_arg(&Tok::RParen)?);
                self.skip_newlines();
                if self.eat(&Tok::Comma) {
                    self.skip_newlines();
                }
                break;
            }
        }
        Ok(CallArgs {
            args: out,
            keyword_arg_index,
        })
    }

    fn parse_keyword_list_arg(&mut self, terminator: &Tok) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        let entries = self.parse_keyword_entries(terminator)?;
        Ok(Spanned::new(Expr::List(entries, None), self.finish(start)))
    }

    fn parse_keyword_entries(&mut self, terminator: &Tok) -> PR<Vec<Spanned<Expr>>> {
        let mut out = Vec::new();
        loop {
            let (key, value) = self.parse_keyword_pair()?;
            out.push(Self::keyword_pair_expr(key, value));
            if !self.continue_keyword_entries(
                terminator,
                "positional expression cannot follow keyword entries",
            )? {
                break;
            }
        }
        Ok(out)
    }

    fn parse_keyword_pair(&mut self) -> PR<(Spanned<Expr>, Spanned<Expr>)> {
        let key = self.bump_keyword_key()?;
        let key = Spanned::new(Expr::Atom(key.node), key.span);
        self.skip_newlines();
        let value = self.with_comma_bound(|p| p.parse_expr())?;
        Ok((key, value))
    }

    fn append_keyword_arg(call_args: &mut CallArgs, key: String, value: Spanned<Expr>) {
        let key_expr = Spanned::new(Expr::Atom(key), value.span);
        let entry = Self::keyword_pair_expr(key_expr, value);
        if let Some(idx) = call_args.keyword_arg_index
            && let Some(arg) = call_args.args.get_mut(idx)
            && let Expr::List(entries, None) = &mut arg.node
        {
            entries.push(entry);
            return;
        }
        let span = entry.span;
        call_args.keyword_arg_index = Some(call_args.args.len());
        call_args
            .args
            .push(Spanned::new(Expr::List(vec![entry], None), span));
    }

    fn keyword_pair_expr(key: Spanned<Expr>, value: Spanned<Expr>) -> Spanned<Expr> {
        let span = key.span.merge(value.span);
        Spanned::new(Expr::Tuple(vec![key, value]), span)
    }

    pub(super) fn parse_block_until(&mut self, stops: &[Tok]) -> PR<Spanned<Expr>> {
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
            // Each block statement is a fresh statement context.
            exprs.push(self.with_comma_unbound(|p| p.parse_expr())?);
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

    pub(super) fn parse_quote(&mut self) -> PR<Spanned<Expr>> {
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

    pub(super) fn parse_unquote(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::Unquote, "`unquote`")?;
        self.expect(&Tok::LParen, "`(` after `unquote`")?;
        self.skip_newlines();
        let e = self.parse_expr()?;
        self.skip_newlines();
        self.expect(&Tok::RParen, "`)`")?;
        Ok(Spanned::new(Expr::Unquote(Box::new(e)), self.finish(start)))
    }

    pub(super) fn parse_if(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::If, "`if`")?;
        let cond = self.with_no_trailing_do(|p| p.parse_expr())?;
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

    pub(super) fn parse_case(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::Case, "`case`")?;
        let scrut = if matches!(self.peek(), Tok::Do) {
            None
        } else {
            Some(Box::new(self.with_no_trailing_do(|p| p.parse_expr())?))
        };
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let mut clauses = Vec::new();
        while !matches!(self.peek(), Tok::End | Tok::Eof) {
            let cl_start = self.cur_span();
            let pat = self.parse_pattern()?;
            let guard = if matches!(self.peek(), Tok::When) {
                self.bump();
                Some(self.with_no_trailing_do(|p| p.parse_expr())?)
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
        Ok(Spanned::new(Expr::Case(scrut, clauses), self.finish(start)))
    }

    /// fz-5vj — `receive do <pat> [when <g>] -> <body>; … [after <t> ->
    /// <body>] end`. Caller has already consumed `Tok::Receive`; `start`
    /// is the span of that token (so the resulting node spans the full
    /// `receive…end`). No scrutinee — clauses match against messages
    /// popped from the mailbox.
    pub(super) fn parse_receive_do(&mut self, start: Span) -> PR<Spanned<Expr>> {
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let mut clauses = Vec::new();
        // Clauses run until we hit `after` (optional tail) or `end`.
        while !matches!(self.peek(), Tok::After | Tok::End | Tok::Eof) {
            let cl_start = self.cur_span();
            let pat = self.parse_pattern()?;
            let guard = if matches!(self.peek(), Tok::When) {
                self.bump();
                Some(self.with_no_trailing_do(|p| p.parse_expr())?)
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
        let after = if self.eat(&Tok::After) {
            self.skip_newlines();
            let af_start = self.cur_span();
            let timeout = self.with_no_trailing_do(|p| p.parse_expr())?;
            self.expect(&Tok::Arrow, "`->` after timeout expr in `after`")?;
            self.skip_newlines();
            let body = self.parse_expr()?;
            self.skip_newlines();
            Some(Box::new(AfterClause {
                timeout,
                body,
                span: self.finish(af_start),
            }))
        } else {
            None
        };
        self.expect(&Tok::End, "`end`")?;
        Ok(Spanned::new(
            Expr::Receive { clauses, after },
            self.finish(start),
        ))
    }

    /// `cond do <test> -> <body>; ...; end` — parsed as `Expr::Cond` whose
    /// arms are evaluated top-to-bottom until one's test is truthy.
    pub(super) fn parse_cond(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::Cond, "`cond`")?;
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let mut arms: Vec<(Spanned<Expr>, Spanned<Expr>)> = Vec::new();
        while !matches!(self.peek(), Tok::End | Tok::Eof) {
            let test = self.with_no_trailing_do(|p| p.parse_expr())?;
            self.expect(&Tok::Arrow, "`->`")?;
            self.skip_newlines();
            let body = self.parse_expr()?;
            arms.push((test, body));
            self.skip_newlines();
        }
        self.expect(&Tok::End, "`end`")?;
        Ok(Spanned::new(Expr::Cond(arms), self.finish(start)))
    }

    pub(super) fn parse_bitstring_expr(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::LBitstr, "`<<`")?;
        let mut fields: Vec<BitField<Spanned<Expr>>> = Vec::new();
        self.skip_newlines();
        if !matches!(self.peek(), Tok::RBitstr) {
            loop {
                let value = self.with_comma_bound(|p| p.parse_expr())?;
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

    pub(super) fn parse_bit_spec(&mut self) -> PR<BitFieldSpec> {
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

    pub(super) fn apply_bit_modifier(&mut self, spec: &mut BitFieldSpec, name: &str) -> PR<()> {
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

    pub(super) fn parse_bit_size(&mut self) -> PR<BitSize> {
        Ok(match self.bump() {
            Tok::Int(n) => BitSize::Literal(n as u32),
            Tok::Ident(name) => BitSize::Var(name),
            other => return self.err(format!("size expects int or var, got {:?}", other)),
        })
    }

    pub(super) fn parse_with(&mut self) -> PR<Spanned<Expr>> {
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
                    let e = self.with_no_trailing_do(|p| p.parse_expr())?;
                    bindings.push(WithBinding::Match(pat, e));
                } else {
                    self.pos = saved;
                    let e = self.with_no_trailing_do(|p| p.parse_expr())?;
                    bindings.push(WithBinding::Bare(e));
                }
            } else {
                self.pos = saved;
                let e = self.with_no_trailing_do(|p| p.parse_expr())?;
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
                        Some(self.with_no_trailing_do(|p| p.parse_expr())?)
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

    pub(super) fn parse_map_expr(&mut self) -> PR<Spanned<Expr>> {
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

    pub(super) fn parse_struct_expr(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::Percent, "`%`")?;
        let (module, _) = self.parse_upper_path("struct")?;
        self.expect(&Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        self.skip_newlines();
        if !matches!(self.peek(), Tok::RBrace) {
            loop {
                let field = match self.bump() {
                    Tok::KwKey(name) | Tok::Ident(name) | Tok::Atom(name) => name,
                    other => {
                        return self.err(format!("expected struct field name, got {:?}", other));
                    }
                };
                if !matches!(self.toks[self.pos - 1].tok, Tok::KwKey(_)) {
                    self.expect(&Tok::FatArrow, "`=>`")?;
                }
                let value = self.with_comma_bound(|p| p.parse_expr())?;
                fields.push((field, value));
                self.skip_newlines();
                if !self.eat(&Tok::Comma) {
                    break;
                }
                self.skip_newlines();
            }
        }
        self.expect(&Tok::RBrace, "`}`")?;
        Ok(Spanned::new(
            Expr::Struct { module, fields },
            self.finish(start),
        ))
    }

    fn parse_map_first_segment(&mut self) -> PR<MapHead> {
        if let Tok::KwKey(_) = self.peek() {
            let key_span = self.cur_span();
            let Tok::KwKey(name) = self.bump() else {
                unreachable!()
            };
            let v = self.with_comma_bound(|p| p.parse_expr())?;
            return Ok(MapHead::Pair(Spanned::new(Expr::Atom(name), key_span), v));
        }
        let first = self.with_comma_bound(|p| p.parse_expr())?;
        if matches!(self.peek(), Tok::Bar) {
            self.bump();
            return Ok(MapHead::Update(first));
        }
        if self.eat(&Tok::FatArrow) {
            let v = self.with_comma_bound(|p| p.parse_expr())?;
            return Ok(MapHead::Pair(first, v));
        }
        self.err(format!(
            "expected `=>` or `|` in map literal, got {:?}",
            self.peek()
        ))
    }

    pub(super) fn parse_map_pairs_into(
        &mut self,
        pairs: &mut Vec<(Spanned<Expr>, Spanned<Expr>)>,
    ) -> PR<()> {
        loop {
            self.skip_newlines();
            if let Tok::KwKey(_) = self.peek() {
                let key_span = self.cur_span();
                let Tok::KwKey(name) = self.bump() else {
                    unreachable!()
                };
                let v = self.with_comma_bound(|p| p.parse_expr())?;
                pairs.push((Spanned::new(Expr::Atom(name), key_span), v));
            } else {
                let k = self.with_comma_bound(|p| p.parse_expr())?;
                if !self.eat(&Tok::FatArrow) {
                    return self.err(format!(
                        "expected `=>` after map key, got {:?}",
                        self.peek()
                    ));
                }
                let v = self.with_comma_bound(|p| p.parse_expr())?;
                pairs.push((k, v));
            }
            self.skip_newlines();
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        Ok(())
    }

    /// `fn p1 -> b1; p2 when g -> b2; … end` — a non-empty list of clauses,
    /// mirroring Elixir's anonymous `fn`. The `end` terminator is required:
    /// without it a multi-clause body has no boundary. Clause structure matches
    /// `parse_case` (pattern list, optional `when` guard, `->`, body), so the
    /// two stay in lockstep. Single-clause unguarded lambdas run directly;
    /// multi-clause and guarded forms desugar in fz-g58.15 (Arc 3).
    pub(super) fn parse_lambda(&mut self) -> PR<Spanned<Expr>> {
        let start = self.cur_span();
        self.expect(&Tok::Fn, "`fn`")?;
        self.skip_newlines();
        let mut clauses = Vec::new();
        while !matches!(self.peek(), Tok::End | Tok::Eof) {
            let cl_start = self.cur_span();
            let params = if self.eat(&Tok::LParen) {
                let ps = self.parse_pattern_list(&Tok::RParen)?;
                self.expect(&Tok::RParen, "`)`")?;
                ps
            } else {
                vec![self.parse_pattern()?]
            };
            let guard = if matches!(self.peek(), Tok::When) {
                self.bump();
                Some(self.with_no_trailing_do(|p| p.parse_expr())?)
            } else {
                None
            };
            self.expect(&Tok::Arrow, "`->`")?;
            self.skip_newlines();
            // A lambda body is a fresh statement context (greedy no-parens calls).
            let body = self.with_comma_unbound(|p| p.parse_expr())?;
            let cspan = self.finish(cl_start);
            clauses.push(LambdaClause {
                params,
                guard,
                body,
                span: cspan,
            });
            self.skip_newlines();
        }
        self.expect(&Tok::End, "`end`")?;
        if clauses.is_empty() {
            return self.err("`fn` requires at least one `pattern -> body` clause");
        }
        Ok(Spanned::new(Expr::Lambda(clauses), self.finish(start)))
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
        Expr::Binary(s) => Pattern::Binary(s.clone()),
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
            return Err(ParseError::syntax(
                format!("expression cannot be used as pattern: {:?}", e.node),
                e.span,
            ));
        }
    };
    Ok(Spanned::new(node, e.span))
}
