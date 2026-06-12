use std::fmt;
use std::rc::Rc;
use std::str::from_utf8;

use crate::compiler::source::{Id as CodeId, Span};
use crate::diag::Diagnostic;
use crate::diag::codes::LEX_UNEXPECTED_CHAR;
use crate::measurements;
use crate::telemetry::{Metadata, Telemetry, Value};

#[derive(Debug, Clone, PartialEq)]
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
    Defstruct,
    Defprotocol,
    Defimpl,
    Alias,
    Import,
    Require,
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
    And, // boolean conjunction: `a and b`
    Or,  // boolean disjunction: `a or b`
    // fz-5vj — selective `receive do … after … end` syntax. Plain
    // `receive()` has been removed; `receive` is a reserved keyword.
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

#[derive(Debug, Clone, PartialEq)]
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
    code_id: CodeId,
    source_name: Option<Rc<str>>,
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
    pub fn to_diagnostic(&self) -> Diagnostic {
        // The lexer currently reports every lex-time failure with the
        // same code and a specific message/span.
        Diagnostic::error(LEX_UNEXPECTED_CHAR, self.msg.clone(), self.span)
    }
}

impl<'a> Lexer<'a> {
    pub fn with_source_name(src: &'a str, source_name: impl AsRef<str>) -> Self {
        Self::with_code_id_and_source_name(src, CodeId(0), source_name)
    }

    pub fn with_code_id_and_source_name(src: &'a str, code_id: CodeId, source_name: impl AsRef<str>) -> Self {
        Self {
            src: src.as_bytes(),
            pos: 0,
            code_id,
            source_name: Some(Rc::from(source_name.as_ref())),
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
        Span::new(self.code_id, start as u32, self.pos as u32)
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
        from_utf8(&self.src[start..self.pos]).unwrap().to_string()
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
                    let raw: String = from_utf8(&self.src[s..self.pos])
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
                    let raw: String = from_utf8(&self.src[s..self.pos])
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
                    let raw: String = from_utf8(&self.src[s..self.pos])
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
        let raw = from_utf8(&self.src[start..self.pos]).unwrap();
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
                        return Err(self.err(format!("unknown escape `\\{}` in string literal", c as char)));
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

    fn keyword_value_starts_after_colon(&self) -> bool {
        matches!(
            self.peek(0),
            None | Some(b' ')
                | Some(b'\t')
                | Some(b'\r')
                | Some(b'\n')
                | Some(b'#')
                | Some(b')')
                | Some(b']')
                | Some(b'}')
                | Some(b',')
                | Some(b';')
        )
    }

    fn err(&self, msg: String) -> LexError {
        // Caller's bump has typically already consumed the offending byte,
        // so back up by one to underline the character itself rather than
        // the position after it. At EOF (`pos == src.len()`), span is empty.
        let end = self.pos as u32;
        let start = if self.pos == 0 { 0 } else { end.saturating_sub(1) };
        LexError {
            msg,
            span: Span::new(self.code_id, start, end),
        }
    }

    fn keyword_or_ident(name: String) -> Tok {
        match name.as_str() {
            "fn" => Tok::Fn,
            "fnp" => Tok::Fnp,
            "extern" => Tok::Extern,
            "defmacro" => Tok::Defmacro,
            "defmodule" => Tok::Defmodule,
            "defstruct" => Tok::Defstruct,
            "defprotocol" => Tok::Defprotocol,
            "defimpl" => Tok::Defimpl,
            "alias" => Tok::Alias,
            "import" => Tok::Import,
            "require" => Tok::Require,
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
            "and" => Tok::And,
            "or" => Tok::Or,
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
                Some(b'|') => return Err(self.err("`||` is not an operator; use `or`".to_string())),
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
                Some(b'&') => return Err(self.err("`&&` is not an operator; use `and`".to_string())),
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
                _ => return Err(self.err("`!` is not an operator; use `not`".to_string())),
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

            b'"' => {
                let bytes = self.read_quoted_binary_bytes()?;
                if self.peek(0) == Some(b':') && self.peek(1) != Some(b':') {
                    self.bump();
                    if self.keyword_value_starts_after_colon() {
                        Tok::KwKey(
                            String::from_utf8(bytes)
                                .map_err(|e| self.err(format!("invalid UTF-8 in string: {}", e)))?,
                        )
                    } else {
                        return Err(self.err("keyword argument must be followed by space after quoted key".into()));
                    }
                } else {
                    Tok::Binary(bytes)
                }
            }
            c if c.is_ascii_digit() => self.read_number()?,
            c if Self::ident_start(c) => {
                let name = self.read_ident();
                // `name:` (but not `::`) is a keyword-list key like `do:`.
                if self.peek(0) == Some(b':') && self.peek(1) != Some(b':') {
                    self.bump();
                    if self.keyword_value_starts_after_colon() {
                        Tok::KwKey(name)
                    } else {
                        return Err(self.err(format!("keyword argument must be followed by space after: {}:", name)));
                    }
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

    /// Opens a `[fz, lexer, pass]` span and emits a
    /// `[fz, lexer, tokens_built]` event with the final token count on
    /// success. The span's stop event records elapsed_ns.
    pub fn tokenize(mut self, tel: &dyn Telemetry) -> Result<Vec<Token>, LexError> {
        use crate::telemetry::TelemetryExt;
        let metadata = self.telemetry_metadata();
        let _span = tel.span(LEX_PASS_NAME, metadata.clone());
        let mut out = Vec::new();
        loop {
            let t = self.next_token()?;
            let done = matches!(t.tok, Tok::Eof);
            out.push(t);
            if done {
                tel.execute(TOKENS_BUILT_NAME, &measurements! { count: out.len() }, &metadata);
                return Ok(out);
            }
        }
    }

    fn telemetry_metadata(&self) -> Metadata<'static> {
        let mut metadata = Metadata::new();
        metadata.0.push(("code_id", Value::from(self.code_id.0)));
        if let Some(source_name) = &self.source_name {
            metadata.0.push(("source_name", Value::from(source_name.to_string())));
        }
        metadata
    }
}

const LEX_PASS_NAME: &[&str] = &["fz", "lexer", "pass"];
const TOKENS_BUILT_NAME: &[&str] = &["fz", "lexer", "tokens_built"];

#[cfg(test)]
#[path = "lexer_test.rs"]
mod lexer_test;
