use std::fmt;

use crate::diag::{FileId, Span};

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum Tok {
    // literals
    Int(i64),
    Float(f64),
    Binary(Vec<u8>),
    Atom(String),
    True,
    False,
    Nil,

    // identifiers / keys
    Ident(String),
    Upper(String), // Capitalized: module / type names
    KwKey(String), // `name:` shorthand for keyword-list key (incl. `do:`)

    // keywords
    Fn,
    Fnp,
    Extern,
    Defmacro,
    Defmodule,
    Defprotocol,
    Defimpl,
    Alias,
    Import,
    Do,
    End,
    If,
    Else,
    Case,
    Cond,
    When,
    With,
    Quote,
    Unquote,
    Type,
    In,  // membership operator: `x in xs`
    Not, // boolean negation and `not in`
    // fz-5vj — selective `receive do … after … end` syntax. `Receive`
    // is contextual: bare `receive(...)` (postfix call) still parses
    // through Expr::Var until fz-recv.A2 drops the bare-call form.
    Receive,
    After,

    // punctuation
    LParen,
    RParen,
    LBrack,
    RBrack,
    LBrace,
    RBrace,
    LBitstr,
    RBitstr,       // << and >>
    PercentLBrace, // %{   (map literal)
    Sigil(String), // ~name (followed by a delimiter token like LBrack)

    Comma,
    Dot,
    Ellipsis,
    Semi,
    Colon,
    ColonColon,
    Arrow,    // ->
    FatArrow, // =>
    LArrow,   // <-
    Pipe,     // |>
    Bar,      // |  (cons / pattern alt)
    Caret,    // ^  (pinned pattern var, fz-5vj)
    Underscore,

    // operators
    Eq, // =
    EqEq,
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Bang,
    AndAnd,
    OrOr,
    At,  // @ — for module attributes (@doc, @moduledoc)
    Amp, // & — for explicit function references (`&name/arity`, fz-swt.5)

    PlusPlus,   // ++  list concatenation
    MinusMinus, // --  list subtraction
    Concat,     // <>  binary concatenation
    DotDot,     // ..  range
    SlashSlash, // //  range step (`first..last//step`)

    Newline,
    Eof,
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
    /// True when at least one trivia byte (space, tab, CR, or comment)
    /// immediately precedes this token on the same line. The parser reads it
    /// to resolve spacing-sensitive grammar: a dual operator (`+`/`-`) with a
    /// space before but none after binds as a unary prefix (so `foo -1` is the
    /// call `foo(-1)`, not the subtraction `foo - 1`), and an identifier with
    /// no space before a following `(`/`[` is a call/access head. The lexer
    /// reports the spacing fact; the parser owns the grammatical decision.
    pub space_before: bool,
}

pub struct Lexer<'a> {
    src: &'a [u8],
    pos: usize,
    file: FileId,
}

#[derive(Debug)]
pub struct LexError {
    pub msg: String,
    pub span: Span,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Plain-text fallback. The .20.6 renderer is the proper rendering
        // path; `to_diagnostic` is what the driver calls.
        write!(f, "lex error: {}", self.msg)
    }
}

impl LexError {
    /// Promote a lex-time error into a structured Diagnostic. The headline
    /// is the lexer's message; the primary span is the offending byte.
    pub fn to_diagnostic(&self) -> crate::diag::Diagnostic {
        // The lexer currently reports every lex-time failure with the
        // same code and a specific message/span.
        crate::diag::Diagnostic::error(
            crate::diag::codes::LEX_UNEXPECTED_CHAR,
            self.msg.clone(),
            self.span,
        )
    }
}

impl<'a> Lexer<'a> {
    /// Lex with the default FileId(0). Suitable for the single-source path
    /// (`fz run <file>`). Multi-file paths (test_runner concatenating a
    /// prelude with user source) use `with_file`.
    pub fn new(src: &'a str) -> Self {
        Self::with_file(src, FileId(0))
    }

    pub fn with_file(src: &'a str, file: FileId) -> Self {
        Self {
            src: src.as_bytes(),
            pos: 0,
            file,
        }
    }

    fn peek(&self, off: usize) -> Option<u8> {
        self.src.get(self.pos + off).copied()
    }

    fn bump(&mut self) -> Option<u8> {
        let c = self.peek(0)?;
        self.pos += 1;
        Some(c)
    }

    fn span_from(&self, start: usize) -> Span {
        Span::new(self.file, start as u32, self.pos as u32)
    }

    fn eat_while(&mut self, mut pred: impl FnMut(u8) -> bool) {
        while let Some(c) = self.peek(0) {
            if pred(c) {
                self.bump();
            } else {
                break;
            }
        }
    }

    fn skip_trivia(&mut self) {
        loop {
            match self.peek(0) {
                Some(b' ') | Some(b'\t') | Some(b'\r') => {
                    self.bump();
                }
                Some(b'#') => {
                    self.eat_while(|c| c != b'\n');
                }
                _ => break,
            }
        }
    }

    fn ident_start(c: u8) -> bool {
        c.is_ascii_alphabetic() || c == b'_'
    }
    fn ident_cont(c: u8) -> bool {
        c.is_ascii_alphanumeric() || c == b'_' || c == b'?' || c == b'!'
    }

    fn read_ident(&mut self) -> String {
        let start = self.pos;
        self.bump();
        self.eat_while(Self::ident_cont);
        std::str::from_utf8(&self.src[start..self.pos])
            .unwrap()
            .to_string()
    }

    fn read_number(&mut self) -> Result<Tok, LexError> {
        // Hex / bin / oct prefixes
        if self.peek(0) == Some(b'0') {
            match self.peek(1) {
                Some(b'x') | Some(b'X') => {
                    self.bump();
                    self.bump();
                    let s = self.pos;
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == b'_');
                    let raw: String = std::str::from_utf8(&self.src[s..self.pos])
                        .unwrap()
                        .chars()
                        .filter(|c| *c != '_')
                        .collect();
                    return i64::from_str_radix(&raw, 16)
                        .map(Tok::Int)
                        .map_err(|e| self.err(e.to_string()));
                }
                Some(b'b') | Some(b'B') => {
                    self.bump();
                    self.bump();
                    let s = self.pos;
                    self.eat_while(|c| c == b'0' || c == b'1' || c == b'_');
                    let raw: String = std::str::from_utf8(&self.src[s..self.pos])
                        .unwrap()
                        .chars()
                        .filter(|c| *c != '_')
                        .collect();
                    return i64::from_str_radix(&raw, 2)
                        .map(Tok::Int)
                        .map_err(|e| self.err(e.to_string()));
                }
                Some(b'o') | Some(b'O') => {
                    self.bump();
                    self.bump();
                    let s = self.pos;
                    self.eat_while(|c| (b'0'..=b'7').contains(&c) || c == b'_');
                    let raw: String = std::str::from_utf8(&self.src[s..self.pos])
                        .unwrap()
                        .chars()
                        .filter(|c| *c != '_')
                        .collect();
                    return i64::from_str_radix(&raw, 8)
                        .map(Tok::Int)
                        .map_err(|e| self.err(e.to_string()));
                }
                _ => {}
            }
        }
        let start = self.pos;
        self.eat_while(|c| c.is_ascii_digit() || c == b'_');
        let mut is_float = false;
        if self.peek(0) == Some(b'.') && self.peek(1).is_some_and(|c| c.is_ascii_digit()) {
            is_float = true;
            self.bump();
            self.eat_while(|c| c.is_ascii_digit() || c == b'_');
        }
        let raw = std::str::from_utf8(&self.src[start..self.pos]).unwrap();
        let cleaned: String = raw.chars().filter(|c| *c != '_').collect();
        if is_float {
            cleaned
                .parse::<f64>()
                .map(Tok::Float)
                .map_err(|e| self.err(e.to_string()))
        } else {
            cleaned
                .parse::<i64>()
                .map(Tok::Int)
                .map_err(|e| self.err(e.to_string()))
        }
    }

    /// fz-axu.9 (L1) — byte-oriented quoted binary literal reader. Returns the
    /// raw bytes of the literal between the surrounding `"…"`. Escapes
    /// recognised: `\n \t \r \\ \"`. Any other backslash sequence is a
    /// hard error (formerly a silent passthrough that mis-encoded UTF-8
    /// for non-ASCII inputs). Caller has positioned at the opening `"`.
    ///
    /// fz-axu.25 (M4) UTF-8 invariant: every byte sequence this function
    /// returns is valid UTF-8. Source input is `&str` (already UTF-8),
    /// and all recognised escapes (`\n \t \r \\ \"`) produce ASCII bytes
    /// that preserve UTF-8 validity. Downstream lowering (L3) relies on
    /// this — when `\x`-style byte escapes are added, this invariant
    /// moves to the escape parser and L3 may need to re-check.
    fn read_quoted_binary_bytes(&mut self) -> Result<Vec<u8>, LexError> {
        self.bump(); // consume opening "
        let mut bytes: Vec<u8> = Vec::new();
        loop {
            match self.bump() {
                None => return Err(self.err("unterminated string".into())),
                Some(b'"') => return Ok(bytes),
                Some(b'\\') => match self.bump() {
                    Some(b'n') => bytes.push(b'\n'),
                    Some(b't') => bytes.push(b'\t'),
                    Some(b'r') => bytes.push(b'\r'),
                    Some(b'\\') => bytes.push(b'\\'),
                    Some(b'"') => bytes.push(b'"'),
                    Some(c) => {
                        return Err(self.err(format!(
                            "unknown escape `\\{}` in string literal",
                            c as char
                        )));
                    }
                    None => return Err(self.err("unterminated escape".into())),
                },
                Some(c) => bytes.push(c),
            }
        }
    }

    /// fz-axu.9 (L1) — UTF-8-validated text reader. Used at sites
    /// where the bytes name an identifier-like value (atom names via
    /// `:"foo"`, `@doc` text, extern ABI strings). Returns a `String`
    /// or surfaces a lex error on invalid UTF-8.
    fn read_string_utf8(&mut self) -> Result<String, LexError> {
        let bytes = self.read_quoted_binary_bytes()?;
        String::from_utf8(bytes).map_err(|e| self.err(format!("invalid UTF-8 in string: {}", e)))
    }

    fn read_quoted_binary(&mut self) -> Result<Tok, LexError> {
        Ok(Tok::Binary(self.read_quoted_binary_bytes()?))
    }

    fn err(&self, msg: String) -> LexError {
        // Caller's bump has typically already consumed the offending byte,
        // so back up by one to underline the character itself rather than
        // the position after it. At EOF (`pos == src.len()`), span is empty.
        let end = self.pos as u32;
        let start = if self.pos == 0 {
            0
        } else {
            end.saturating_sub(1)
        };
        LexError {
            msg,
            span: Span::new(self.file, start, end),
        }
    }

    fn keyword_or_ident(name: String) -> Tok {
        match name.as_str() {
            "fn" => Tok::Fn,
            "fnp" => Tok::Fnp,
            "extern" => Tok::Extern,
            "defmacro" => Tok::Defmacro,
            "defmodule" => Tok::Defmodule,
            "defprotocol" => Tok::Defprotocol,
            "defimpl" => Tok::Defimpl,
            "alias" => Tok::Alias,
            "import" => Tok::Import,
            "do" => Tok::Do,
            "end" => Tok::End,
            "if" => Tok::If,
            "else" => Tok::Else,
            "case" => Tok::Case,
            "cond" => Tok::Cond,
            "when" => Tok::When,
            "with" => Tok::With,
            "receive" => Tok::Receive,
            "after" => Tok::After,
            "quote" => Tok::Quote,
            "unquote" => Tok::Unquote,
            "type" => Tok::Type,
            "in" => Tok::In,
            "not" => Tok::Not,
            "true" => Tok::True,
            "false" => Tok::False,
            "nil" => Tok::Nil,
            "_" => Tok::Underscore,
            _ => {
                let first = name.as_bytes()[0];
                if first.is_ascii_uppercase() {
                    Tok::Upper(name)
                } else {
                    Tok::Ident(name)
                }
            }
        }
    }

    pub fn next_token(&mut self) -> Result<Token, LexError> {
        let before_trivia = self.pos;
        self.skip_trivia();
        let space_before = self.pos != before_trivia;
        let start = self.pos;
        let Some(c) = self.peek(0) else {
            return Ok(Token {
                tok: Tok::Eof,
                span: self.span_from(start),
                space_before,
            });
        };

        let tok = match c {
            b'\n' => {
                self.bump();
                Tok::Newline
            }
            b'(' => {
                self.bump();
                Tok::LParen
            }
            b')' => {
                self.bump();
                Tok::RParen
            }
            b'[' => {
                self.bump();
                Tok::LBrack
            }
            b']' => {
                self.bump();
                Tok::RBrack
            }
            b'{' => {
                self.bump();
                Tok::LBrace
            }
            b'}' => {
                self.bump();
                Tok::RBrace
            }
            b',' => {
                self.bump();
                Tok::Comma
            }
            b'.' if self.peek(1) == Some(b'.') && self.peek(2) == Some(b'.') => {
                self.bump();
                self.bump();
                self.bump();
                Tok::Ellipsis
            }
            b'.' if self.peek(1) == Some(b'.') => {
                self.bump();
                self.bump();
                Tok::DotDot
            }
            b'.' => {
                self.bump();
                Tok::Dot
            }
            b';' => {
                self.bump();
                Tok::Semi
            }
            b'@' => {
                self.bump();
                Tok::At
            }

            b'%' if self.peek(1) == Some(b'{') => {
                self.bump();
                self.bump();
                Tok::PercentLBrace
            }
            b'%' => {
                self.bump();
                Tok::Percent
            }

            b'~' if self.peek(1).is_some_and(|c| c.is_ascii_lowercase()) => {
                self.bump(); // ~
                let name = self.read_ident();
                Tok::Sigil(name)
            }

            b'<' => match self.peek(1) {
                Some(b'<') => {
                    self.bump();
                    self.bump();
                    Tok::LBitstr
                }
                Some(b'-') => {
                    self.bump();
                    self.bump();
                    Tok::LArrow
                }
                Some(b'=') => {
                    self.bump();
                    self.bump();
                    Tok::LtEq
                }
                Some(b'>') => {
                    self.bump();
                    self.bump();
                    Tok::Concat
                }
                _ => {
                    self.bump();
                    Tok::Lt
                }
            },
            b'>' => match self.peek(1) {
                Some(b'>') => {
                    self.bump();
                    self.bump();
                    Tok::RBitstr
                }
                Some(b'=') => {
                    self.bump();
                    self.bump();
                    Tok::GtEq
                }
                _ => {
                    self.bump();
                    Tok::Gt
                }
            },
            b'-' => match self.peek(1) {
                Some(b'>') => {
                    self.bump();
                    self.bump();
                    Tok::Arrow
                }
                Some(b'-') => {
                    self.bump();
                    self.bump();
                    Tok::MinusMinus
                }
                _ => {
                    self.bump();
                    Tok::Minus
                }
            },
            b'|' => match self.peek(1) {
                Some(b'>') => {
                    self.bump();
                    self.bump();
                    Tok::Pipe
                }
                Some(b'|') => {
                    self.bump();
                    self.bump();
                    Tok::OrOr
                }
                _ => {
                    self.bump();
                    Tok::Bar
                }
            },
            b'^' => {
                self.bump();
                Tok::Caret
            }
            b'&' => match self.peek(1) {
                Some(b'&') => {
                    self.bump();
                    self.bump();
                    Tok::AndAnd
                }
                // fz-swt.5: bare `&` introduces an explicit fn-ref (`&name/arity`).
                _ => {
                    self.bump();
                    Tok::Amp
                }
            },
            b'=' => match self.peek(1) {
                Some(b'=') => {
                    self.bump();
                    self.bump();
                    Tok::EqEq
                }
                Some(b'>') => {
                    self.bump();
                    self.bump();
                    Tok::FatArrow
                }
                _ => {
                    self.bump();
                    Tok::Eq
                }
            },
            b'!' => match self.peek(1) {
                Some(b'=') => {
                    self.bump();
                    self.bump();
                    Tok::NotEq
                }
                _ => {
                    self.bump();
                    Tok::Bang
                }
            },
            b'+' => match self.peek(1) {
                Some(b'+') => {
                    self.bump();
                    self.bump();
                    Tok::PlusPlus
                }
                _ => {
                    self.bump();
                    Tok::Plus
                }
            },
            b'*' => {
                self.bump();
                Tok::Star
            }
            b'/' => match self.peek(1) {
                Some(b'/') => {
                    self.bump();
                    self.bump();
                    Tok::SlashSlash
                }
                _ => {
                    self.bump();
                    Tok::Slash
                }
            },

            b':' => match self.peek(1) {
                Some(b':') => {
                    self.bump();
                    self.bump();
                    Tok::ColonColon
                }
                Some(c2) if Self::ident_start(c2) => {
                    self.bump(); // consume :
                    let name = self.read_ident();
                    Tok::Atom(name)
                }
                Some(b'"') => {
                    self.bump();
                    // fz-axu.9 (L1) — atom names must be valid UTF-8.
                    Tok::Atom(self.read_string_utf8()?)
                }
                _ => {
                    self.bump();
                    Tok::Colon
                }
            },

            b'"' => self.read_quoted_binary()?,
            c if c.is_ascii_digit() => self.read_number()?,
            c if Self::ident_start(c) => {
                let name = self.read_ident();
                // `name:` (but not `::`) is a keyword-list key like `do:`.
                if self.peek(0) == Some(b':') && self.peek(1) != Some(b':') {
                    self.bump();
                    Tok::KwKey(name)
                } else {
                    Self::keyword_or_ident(name)
                }
            }
            other => {
                self.bump();
                return Err(self.err(format!("unexpected character {:?}", other as char)));
            }
        };

        Ok(Token {
            tok,
            span: self.span_from(start),
            space_before,
        })
    }

    pub fn tokenize(self) -> Result<Vec<Token>, LexError> {
        self.tokenize_with_telemetry(&crate::telemetry::NullTelemetry)
    }

    /// Same as `tokenize` but opens a `[fz, lexer, pass]` span and emits
    /// a `[fz, lexer, tokens_built]` event with the final token count on
    /// success. The span's stop event records elapsed_ns. Callers that
    /// don't want observability can use `tokenize()` (NullTelemetry).
    pub fn tokenize_with_telemetry(
        mut self,
        tel: &dyn crate::telemetry::Telemetry,
    ) -> Result<Vec<Token>, LexError> {
        use crate::telemetry::TelemetryExt;
        let _span = tel.span(LEX_PASS_NAME, crate::telemetry::Metadata::new());
        let mut out = Vec::new();
        loop {
            let t = self.next_token()?;
            let done = matches!(t.tok, Tok::Eof);
            out.push(t);
            if done {
                tel.execute(
                    TOKENS_BUILT_NAME,
                    &crate::measurements! { count: out.len() },
                    &crate::telemetry::Metadata::new(),
                );
                return Ok(out);
            }
        }
    }
}

const LEX_PASS_NAME: &[&str] = &["fz", "lexer", "pass"];
const TOKENS_BUILT_NAME: &[&str] = &["fz", "lexer", "tokens_built"];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::SourceMap;

    #[test]
    fn tokens_carry_accurate_byte_spans() {
        let src = "fn foo(x), do: x + 1";
        let toks = Lexer::new(src).tokenize().expect("lex");
        // Every non-Eof token's span text matches the lexeme we expect.
        for t in &toks {
            let slice = &src[t.span.start as usize..t.span.end as usize];
            match &t.tok {
                Tok::Fn => assert_eq!(slice, "fn"),
                Tok::Ident(n) if n == "foo" => assert_eq!(slice, "foo"),
                Tok::Ident(n) if n == "x" => assert_eq!(slice, "x"),
                Tok::Int(1) => assert_eq!(slice, "1"),
                Tok::Plus => assert_eq!(slice, "+"),
                Tok::KwKey(k) if k == "do" => assert_eq!(slice, "do:"),
                _ => {}
            }
        }
    }

    #[test]
    fn locate_resolves_to_correct_line() {
        let src = "fn a(), do: 1\nfn b(), do: 2\n";
        let mut sm = SourceMap::new();
        let f = sm.add_file("t.fz", src);
        let toks = Lexer::with_file(src, f).tokenize().expect("lex");
        // Find the `b` ident; verify it locates to line 2.
        let b = toks
            .iter()
            .find(|t| matches!(&t.tok, Tok::Ident(n) if n == "b"))
            .expect("found b");
        let loc = sm.locate(b.span);
        assert_eq!(loc.line, 2);
        assert_eq!(loc.col, 4);
    }

    #[test]
    fn multi_file_spans_keep_their_file_id() {
        let mut sm = SourceMap::new();
        let a = sm.add_file("a.fz", "fn foo()");
        let b = sm.add_file("b.fz", "fn bar()");
        let toks_a = Lexer::with_file("fn foo()", a).tokenize().unwrap();
        let toks_b = Lexer::with_file("fn bar()", b).tokenize().unwrap();
        let foo = toks_a
            .iter()
            .find(|t| matches!(&t.tok, Tok::Ident(n) if n == "foo"))
            .unwrap();
        let bar = toks_b
            .iter()
            .find(|t| matches!(&t.tok, Tok::Ident(n) if n == "bar"))
            .unwrap();
        assert_eq!(foo.span.file, a);
        assert_eq!(bar.span.file, b);
        assert_eq!(
            &sm.file(foo.span.file).bytes[foo.span.start as usize..foo.span.end as usize],
            "foo"
        );
        assert_eq!(
            &sm.file(bar.span.file).bytes[bar.span.start as usize..bar.span.end as usize],
            "bar"
        );
    }

    // fz-axu.9 (L1) — byte-oriented quoted binary literals.

    #[test]
    fn binary_literal_carries_raw_bytes() {
        let toks = Lexer::new(r#""hi""#).tokenize().expect("lex");
        match &toks[0].tok {
            Tok::Binary(b) => assert_eq!(b, &b"hi".to_vec()),
            _ => panic!("expected Tok::Binary, got {:?}", toks[0].tok),
        }
    }

    #[test]
    fn binary_literal_preserves_non_ascii_utf8_bytes() {
        // "héllo" — `é` is 0xC3 0xA9 in UTF-8. Pre-L1 the lexer was
        // pushing each byte as a `char` via `c as char`, which
        // re-encoded into UTF-8 multi-byte garbage. Post-L1 the bytes
        // pass through unchanged.
        let toks = Lexer::new(r#""héllo""#).tokenize().expect("lex");
        match &toks[0].tok {
            Tok::Binary(b) => assert_eq!(b, "héllo".as_bytes()),
            _ => panic!("expected Tok::Binary"),
        }
    }

    #[test]
    fn binary_literal_handles_canonical_escapes() {
        let toks = Lexer::new(r#""a\nb\tc\\d\"e""#).tokenize().expect("lex");
        match &toks[0].tok {
            Tok::Binary(b) => assert_eq!(b, b"a\nb\tc\\d\"e"),
            _ => panic!("expected Tok::Binary"),
        }
    }

    #[test]
    fn binary_literal_rejects_unknown_escape() {
        let err = Lexer::new(r#""bad\q""#)
            .tokenize()
            .expect_err("unknown escape must fail");
        assert!(err.msg.contains("unknown escape"), "msg={}", err.msg);
    }

    // Note: `read_string_utf8`'s err path is defensive — the lexer
    // input is `&str`, so the bytes between `"…"` are always valid
    // UTF-8 today. Future escape forms (e.g. `\xff`) will be the first
    // way to surface that diagnostic.

    /// fz-axu.25 (M4) — guards the UTF-8 invariant L3 lowering relies on:
    /// every Tok::Binary payload produced by the lexer must be valid UTF-8.
    /// If `\x`-style byte escapes are added later, this test should fail
    /// and force a re-evaluation of where validation lives.
    #[test]
    fn str_tokens_are_invariantly_utf8() {
        let inputs = [
            r#""""#,              // empty
            r#""hello""#,         // ASCII
            r#""héllo""#,         // multi-byte UTF-8 codepoint
            r#""日本語""#,        // three-byte CJK
            r#""a\nb\tc\\d\"e""#, // all canonical escapes
        ];
        for src in inputs {
            let toks = Lexer::new(src).tokenize().expect("lex");
            match &toks[0].tok {
                Tok::Binary(bytes) => {
                    std::str::from_utf8(bytes)
                        .unwrap_or_else(|_| panic!("Tok::Binary must be UTF-8 for {}", src));
                }
                _ => panic!("expected Tok::Binary for {}", src),
            }
        }
    }

    // fz-g58.1.1 — Elixir-aligned operator tokens.

    /// Collect the non-Eof token kinds for a source, for compact assertions.
    fn toks_of(src: &str) -> Vec<Tok> {
        Lexer::new(src)
            .tokenize()
            .expect("lex")
            .into_iter()
            .map(|t| t.tok)
            .filter(|t| !matches!(t, Tok::Eof))
            .collect()
    }

    #[test]
    fn lexes_new_binary_operators() {
        assert_eq!(toks_of("a ++ b"), vec![id("a"), Tok::PlusPlus, id("b")]);
        assert_eq!(toks_of("a -- b"), vec![id("a"), Tok::MinusMinus, id("b")]);
        assert_eq!(toks_of("a <> b"), vec![id("a"), Tok::Concat, id("b")]);
    }

    #[test]
    fn lexes_range_and_step() {
        // `..` is its own token, distinct from `.` and `...`.
        assert_eq!(toks_of("1..10"), vec![Tok::Int(1), Tok::DotDot, Tok::Int(10)]);
        // `first..last//step` lexes as `..` then `//`.
        assert_eq!(
            toks_of("1..10//2"),
            vec![
                Tok::Int(1),
                Tok::DotDot,
                Tok::Int(10),
                Tok::SlashSlash,
                Tok::Int(2)
            ]
        );
    }

    #[test]
    fn dotdot_does_not_steal_from_ellipsis_or_float() {
        // `...` stays a single Ellipsis (more specific arm wins).
        assert_eq!(toks_of("..."), vec![Tok::Ellipsis]);
        // A decimal point with a following digit is still a float.
        assert_eq!(toks_of("1.5"), vec![Tok::Float(1.5)]);
        // A range over floats: `1.0..2.0`.
        assert_eq!(
            toks_of("1.0..2.0"),
            vec![Tok::Float(1.0), Tok::DotDot, Tok::Float(2.0)]
        );
    }

    #[test]
    fn concat_does_not_collide_with_bitstring_delimiters() {
        // `<>` is concat; `<<` / `>>` remain bitstring delimiters.
        assert_eq!(toks_of("<<>>"), vec![Tok::LBitstr, Tok::RBitstr]);
        assert_eq!(toks_of("a <> b"), vec![id("a"), Tok::Concat, id("b")]);
    }

    #[test]
    fn slashslash_distinct_from_slash() {
        assert_eq!(toks_of("a / b"), vec![id("a"), Tok::Slash, id("b")]);
        assert_eq!(toks_of("a // b"), vec![id("a"), Tok::SlashSlash, id("b")]);
    }

    #[test]
    fn lexes_membership_keywords() {
        assert_eq!(toks_of("x in xs"), vec![id("x"), Tok::In, id("xs")]);
        assert_eq!(
            toks_of("x not in xs"),
            vec![id("x"), Tok::Not, Tok::In, id("xs")]
        );
    }

    fn id(s: &str) -> Tok {
        Tok::Ident(s.to_string())
    }

    // fz-g58.1.2 — dual-op space sensitivity. The lexer records, per token,
    // whether trivia immediately precedes it. The parser (no-parens calls)
    // reads "space before the op, none before the following operand" as a
    // unary prefix.

    /// (tok, space_before) for each non-Eof token.
    fn spacing_of(src: &str) -> Vec<(Tok, bool)> {
        Lexer::new(src)
            .tokenize()
            .expect("lex")
            .into_iter()
            .map(|t| (t.tok, t.space_before))
            .filter(|(t, _)| !matches!(t, Tok::Eof))
            .collect()
    }

    /// Given `<head> <op> <operand>`, the op is unary-positioned iff it has a
    /// space before and the operand has none — the rule the parser applies.
    fn op_is_unary_positioned(src: &str) -> bool {
        let s = spacing_of(src);
        let op = s
            .iter()
            .position(|(t, _)| matches!(t, Tok::Minus | Tok::Plus))
            .expect("an op");
        s[op].1 && !s[op + 1].1
    }

    #[test]
    fn records_space_before_for_each_token() {
        // Leading token has no space before it; the rest are space-separated.
        assert_eq!(
            spacing_of("a - b"),
            vec![(id("a"), false), (Tok::Minus, true), (id("b"), true)]
        );
    }

    #[test]
    fn dual_op_spacing_distinguishes_unary_from_binary() {
        // `foo -1`: space before `-`, none before `1` → unary (the call foo(-1)).
        assert!(op_is_unary_positioned("foo -1"));
        // `foo - 1`: spaces on both sides → binary subtraction.
        assert!(!op_is_unary_positioned("foo - 1"));
        // `foo-1`: no space either side → binary.
        assert!(!op_is_unary_positioned("foo-1"));
        // `+` behaves the same as `-`.
        assert!(op_is_unary_positioned("foo +1"));
        assert!(!op_is_unary_positioned("foo + 1"));
    }

    #[test]
    fn adjacency_visible_for_call_and_access_heads() {
        // `foo(` — no space before `(` marks a call head; `foo (` has space.
        let call = spacing_of("foo(x)");
        let lp = call.iter().position(|(t, _)| matches!(t, Tok::LParen)).unwrap();
        assert!(!call[lp].1, "call-head `(` is adjacent to the identifier");
        let spaced = spacing_of("foo (x)");
        let lp2 = spaced.iter().position(|(t, _)| matches!(t, Tok::LParen)).unwrap();
        assert!(spaced[lp2].1, "spaced `(` is not a call head");
    }

    #[test]
    fn lex_error_carries_span_at_offending_byte() {
        let src = "fn `";
        let err = Lexer::new(src).tokenize().expect_err("should fail");
        // Backtick is at offset 3; err span points at it (or just after).
        assert!(
            err.span.start <= 3 && err.span.end >= 3,
            "span={:?}",
            err.span
        );
        assert_eq!(err.span.file, FileId(0));
    }

    // -- Telemetry integration (fz-ndf.8) --

    #[test]
    fn telemetry_emits_pass_span_and_token_count() {
        use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind, Value};

        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());

        let src = "fn foo(x), do: x + 1";
        let toks = Lexer::new(src).tokenize_with_telemetry(&tel).expect("lex");
        let expected_count = toks.len();

        // Span lifecycle: SpanStart + SpanStop bracketing the user event.
        assert_eq!(cap.count_by_kind(EventKind::SpanStart), 1);
        assert_eq!(cap.count_by_kind(EventKind::SpanStop), 1);
        assert_eq!(cap.count(&["fz", "lexer", "pass"]), 2); // start + stop

        // tokens_built event with the count measurement.
        let built = cap.last(&["fz", "lexer", "tokens_built"]).unwrap();
        match built.measurements.get("count") {
            Some(Value::U64(n)) => assert_eq!(*n as usize, expected_count),
            other => panic!("expected U64 count, got {:?}", other),
        }
    }

    #[test]
    fn telemetry_user_event_inherits_span_id() {
        use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind};

        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());

        let _ = Lexer::new("fn x() do, :ok end")
            .tokenize_with_telemetry(&tel)
            .expect("lex");

        // Find the SpanStart and the tokens_built event; same span_id.
        let start = cap
            .find(&["fz", "lexer", "pass"])
            .into_iter()
            .find(|e| e.kind == EventKind::SpanStart)
            .unwrap();
        let built = cap.last(&["fz", "lexer", "tokens_built"]).unwrap();
        assert_eq!(start.span_id, built.span_id);
        assert!(start.span_id > 0);
    }

    #[test]
    fn null_telemetry_is_a_silent_no_op() {
        use crate::telemetry::NullTelemetry;
        // Same call path; just verifies the null impl compiles + runs.
        let toks = Lexer::new("fn x(), do: :ok")
            .tokenize_with_telemetry(&NullTelemetry)
            .expect("lex");
        assert!(!toks.is_empty());
    }
}
