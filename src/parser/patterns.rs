use super::*;

impl Parser {
    pub(super) fn parse_pattern_list(&mut self, terminator: &Tok) -> PR<Vec<Spanned<Pattern>>> {
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

    pub(super) fn parse_pattern(&mut self) -> PR<Spanned<Pattern>> {
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

    pub(super) fn parse_pattern_atom(&mut self) -> PR<Spanned<Pattern>> {
        let start = self.cur_span();
        let node = match self.peek().clone() {
            Tok::Underscore => {
                self.bump();
                Pattern::Wildcard
            }
            Tok::Caret => {
                // fz-5vj — `^name` pinned pattern var.
                self.bump();
                match self.bump() {
                    Tok::Ident(n) => Pattern::Pinned(n),
                    other => {
                        return self.err(format!(
                            "expected identifier after `^` in pattern, got {:?}",
                            other
                        ));
                    }
                }
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
            Tok::Binary(bytes) => {
                self.bump();
                // fz-axu.10 (L2) — Pattern::Binary carries raw bytes; L3
                // validates UTF-8 and brands when the subject is utf8.
                Pattern::Binary(bytes)
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
                        if matches!(self.peek(), Tok::KwKey(_)) {
                            elems.extend(self.parse_keyword_pattern_entries(&Tok::RBrack)?);
                            break;
                        }
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
            Tok::Percent => {
                self.bump();
                let (module, _) = self.parse_upper_path("struct pattern")?;
                self.expect(&Tok::LBrace, "`{`")?;
                let mut fields = Vec::new();
                self.skip_newlines();
                if !matches!(self.peek(), Tok::RBrace) {
                    loop {
                        let field = match self.bump() {
                            Tok::KwKey(name) | Tok::Ident(name) | Tok::Atom(name) => name,
                            other => {
                                return self
                                    .err(format!("expected struct field name, got {:?}", other));
                            }
                        };
                        if !matches!(self.toks[self.pos - 1].tok, Tok::KwKey(_)) {
                            self.expect(&Tok::FatArrow, "`=>`")?;
                        }
                        let value = self.parse_pattern()?;
                        fields.push((field, value));
                        self.skip_newlines();
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                        self.skip_newlines();
                    }
                }
                self.expect(&Tok::RBrace, "`}`")?;
                Pattern::Struct { module, fields }
            }
            other => return self.err(format!("invalid pattern start {:?}", other)),
        };
        Ok(Spanned::new(node, self.finish(start)))
    }

    fn parse_keyword_pattern_entries(&mut self, terminator: &Tok) -> PR<Vec<Spanned<Pattern>>> {
        let mut out = Vec::new();
        loop {
            let (key, value) = self.parse_keyword_pattern_pair()?;
            out.push(Self::keyword_pattern_pair(key, value));
            if !self.continue_keyword_entries(
                terminator,
                "positional pattern cannot follow keyword entries",
            )? {
                break;
            }
        }
        Ok(out)
    }

    fn parse_keyword_pattern_pair(&mut self) -> PR<(Spanned<Pattern>, Spanned<Pattern>)> {
        let key = self.bump_keyword_key()?;
        let key = Spanned::new(Pattern::Atom(key.node), key.span);
        self.skip_newlines();
        let value = self.parse_pattern()?;
        Ok((key, value))
    }

    fn keyword_pattern_pair(key: Spanned<Pattern>, value: Spanned<Pattern>) -> Spanned<Pattern> {
        let span = key.span.merge(value.span);
        Spanned::new(Pattern::Tuple(vec![key, value]), span)
    }
}
