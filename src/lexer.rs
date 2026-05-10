use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    // literals
    Int(i64),
    Float(f64),
    Str(String),
    Atom(String),
    True,
    False,
    Nil,

    // identifiers / keys
    Ident(String),
    Upper(String),       // Capitalized: module / type names
    KwKey(String),       // `name:` shorthand for keyword-list key (incl. `do:`)

    // keywords
    Fn,
    Defmacro,
    Defmodule,
    Alias,
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

    // punctuation
    LParen, RParen,
    LBrack, RBrack,
    LBrace, RBrace,
    LBitstr, RBitstr,    // << and >>
    PercentLBrace,       // %{   (map literal)
    Sigil(String),       // ~name (followed by a delimiter token like LBrack)

    Comma, Dot, Semi, Colon, ColonColon,
    Arrow,               // ->
    FatArrow,            // =>
    LArrow,              // <-
    Pipe,                // |>
    Bar,                 // |  (cons / pattern alt)
    Underscore,

    // operators
    Eq,                  // =
    EqEq, NotEq,
    Lt, LtEq, Gt, GtEq,
    Plus, Minus, Star, Slash, Percent,
    Bang, AndAnd, OrOr,

    Newline,
    Eof,
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub tok: Tok,
    pub line: u32,
    pub col: u32,
}

pub struct Lexer<'a> {
    src: &'a [u8],
    pos: usize,
    line: u32,
    col: u32,
}

#[derive(Debug)]
pub struct LexError {
    pub msg: String,
    pub line: u32,
    pub col: u32,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "lex error at {}:{}: {}", self.line, self.col, self.msg)
    }
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self { src: src.as_bytes(), pos: 0, line: 1, col: 1 }
    }

    fn peek(&self, off: usize) -> Option<u8> {
        self.src.get(self.pos + off).copied()
    }

    fn bump(&mut self) -> Option<u8> {
        let c = self.peek(0)?;
        self.pos += 1;
        if c == b'\n' { self.line += 1; self.col = 1; } else { self.col += 1; }
        Some(c)
    }

    fn eat_while(&mut self, mut pred: impl FnMut(u8) -> bool) {
        while let Some(c) = self.peek(0) {
            if pred(c) { self.bump(); } else { break; }
        }
    }

    fn skip_trivia(&mut self) {
        loop {
            match self.peek(0) {
                Some(b' ') | Some(b'\t') | Some(b'\r') => { self.bump(); }
                Some(b'#') => { self.eat_while(|c| c != b'\n'); }
                _ => break,
            }
        }
    }

    fn ident_start(c: u8) -> bool { c.is_ascii_alphabetic() || c == b'_' }
    fn ident_cont(c: u8) -> bool { c.is_ascii_alphanumeric() || c == b'_' || c == b'?' || c == b'!' }

    fn read_ident(&mut self) -> String {
        let start = self.pos;
        self.bump();
        self.eat_while(Self::ident_cont);
        std::str::from_utf8(&self.src[start..self.pos]).unwrap().to_string()
    }

    fn read_number(&mut self) -> Result<Tok, LexError> {
        // Hex / bin / oct prefixes
        if self.peek(0) == Some(b'0') {
            match self.peek(1) {
                Some(b'x') | Some(b'X') => {
                    self.bump(); self.bump();
                    let s = self.pos;
                    self.eat_while(|c| c.is_ascii_hexdigit() || c == b'_');
                    let raw: String = std::str::from_utf8(&self.src[s..self.pos]).unwrap().chars().filter(|c| *c != '_').collect();
                    return i64::from_str_radix(&raw, 16).map(Tok::Int).map_err(|e| self.err(e.to_string()));
                }
                Some(b'b') | Some(b'B') => {
                    self.bump(); self.bump();
                    let s = self.pos;
                    self.eat_while(|c| c == b'0' || c == b'1' || c == b'_');
                    let raw: String = std::str::from_utf8(&self.src[s..self.pos]).unwrap().chars().filter(|c| *c != '_').collect();
                    return i64::from_str_radix(&raw, 2).map(Tok::Int).map_err(|e| self.err(e.to_string()));
                }
                Some(b'o') | Some(b'O') => {
                    self.bump(); self.bump();
                    let s = self.pos;
                    self.eat_while(|c| (b'0'..=b'7').contains(&c) || c == b'_');
                    let raw: String = std::str::from_utf8(&self.src[s..self.pos]).unwrap().chars().filter(|c| *c != '_').collect();
                    return i64::from_str_radix(&raw, 8).map(Tok::Int).map_err(|e| self.err(e.to_string()));
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
            cleaned.parse::<f64>().map(Tok::Float).map_err(|e| self.err(e.to_string()))
        } else {
            cleaned.parse::<i64>().map(Tok::Int).map_err(|e| self.err(e.to_string()))
        }
    }

    fn read_string(&mut self) -> Result<Tok, LexError> {
        self.bump(); // consume opening "
        let mut s = String::new();
        loop {
            match self.bump() {
                None => return Err(self.err("unterminated string".into())),
                Some(b'"') => return Ok(Tok::Str(s)),
                Some(b'\\') => match self.bump() {
                    Some(b'n') => s.push('\n'),
                    Some(b't') => s.push('\t'),
                    Some(b'r') => s.push('\r'),
                    Some(b'\\') => s.push('\\'),
                    Some(b'"') => s.push('"'),
                    Some(c) => s.push(c as char),
                    None => return Err(self.err("unterminated escape".into())),
                },
                Some(c) => s.push(c as char),
            }
        }
    }

    fn err(&self, msg: String) -> LexError {
        LexError { msg, line: self.line, col: self.col }
    }

    fn keyword_or_ident(name: String) -> Tok {
        match name.as_str() {
            "fn" => Tok::Fn,
            "defmacro" => Tok::Defmacro,
            "defmodule" => Tok::Defmodule,
            "alias" => Tok::Alias,
            "do" => Tok::Do,
            "end" => Tok::End,
            "if" => Tok::If,
            "else" => Tok::Else,
            "case" => Tok::Case,
            "cond" => Tok::Cond,
            "when" => Tok::When,
            "with" => Tok::With,
            "quote" => Tok::Quote,
            "unquote" => Tok::Unquote,
            "type" => Tok::Type,
            "true" => Tok::True,
            "false" => Tok::False,
            "nil" => Tok::Nil,
            "_" => Tok::Underscore,
            _ => {
                let first = name.as_bytes()[0];
                if first.is_ascii_uppercase() { Tok::Upper(name) } else { Tok::Ident(name) }
            }
        }
    }

    pub fn next_token(&mut self) -> Result<Token, LexError> {
        self.skip_trivia();
        let line = self.line;
        let col = self.col;
        let Some(c) = self.peek(0) else {
            return Ok(Token { tok: Tok::Eof, line, col });
        };

        let tok = match c {
            b'\n' => { self.bump(); Tok::Newline }
            b'(' => { self.bump(); Tok::LParen }
            b')' => { self.bump(); Tok::RParen }
            b'[' => { self.bump(); Tok::LBrack }
            b']' => { self.bump(); Tok::RBrack }
            b'{' => { self.bump(); Tok::LBrace }
            b'}' => { self.bump(); Tok::RBrace }
            b',' => { self.bump(); Tok::Comma }
            b'.' => { self.bump(); Tok::Dot }
            b';' => { self.bump(); Tok::Semi }

            b'%' if self.peek(1) == Some(b'{') => { self.bump(); self.bump(); Tok::PercentLBrace }
            b'%' => { self.bump(); Tok::Percent }

            b'~' if self.peek(1).is_some_and(|c| c.is_ascii_lowercase()) => {
                self.bump(); // ~
                let name = self.read_ident();
                Tok::Sigil(name)
            }

            b'<' => match self.peek(1) {
                Some(b'<') => { self.bump(); self.bump(); Tok::LBitstr }
                Some(b'-') => { self.bump(); self.bump(); Tok::LArrow }
                Some(b'=') => { self.bump(); self.bump(); Tok::LtEq }
                _ => { self.bump(); Tok::Lt }
            },
            b'>' => match self.peek(1) {
                Some(b'>') => { self.bump(); self.bump(); Tok::RBitstr }
                Some(b'=') => { self.bump(); self.bump(); Tok::GtEq }
                _ => { self.bump(); Tok::Gt }
            },
            b'-' => match self.peek(1) {
                Some(b'>') => { self.bump(); self.bump(); Tok::Arrow }
                _ => { self.bump(); Tok::Minus }
            },
            b'|' => match self.peek(1) {
                Some(b'>') => { self.bump(); self.bump(); Tok::Pipe }
                Some(b'|') => { self.bump(); self.bump(); Tok::OrOr }
                _ => { self.bump(); Tok::Bar }
            },
            b'&' if self.peek(1) == Some(b'&') => { self.bump(); self.bump(); Tok::AndAnd }
            b'=' => match self.peek(1) {
                Some(b'=') => { self.bump(); self.bump(); Tok::EqEq }
                Some(b'>') => { self.bump(); self.bump(); Tok::FatArrow }
                _ => { self.bump(); Tok::Eq }
            },
            b'!' => match self.peek(1) {
                Some(b'=') => { self.bump(); self.bump(); Tok::NotEq }
                _ => { self.bump(); Tok::Bang }
            },
            b'+' => { self.bump(); Tok::Plus }
            b'*' => { self.bump(); Tok::Star }
            b'/' => { self.bump(); Tok::Slash }

            b':' => match self.peek(1) {
                Some(b':') => { self.bump(); self.bump(); Tok::ColonColon }
                Some(c2) if Self::ident_start(c2) => {
                    self.bump(); // consume :
                    let name = self.read_ident();
                    Tok::Atom(name)
                }
                Some(b'"') => {
                    self.bump();
                    let Tok::Str(s) = self.read_string()? else { unreachable!() };
                    Tok::Atom(s)
                }
                _ => { self.bump(); Tok::Colon }
            },

            b'"' => self.read_string()?,
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

        Ok(Token { tok, line, col })
    }

    pub fn tokenize(mut self) -> Result<Vec<Token>, LexError> {
        let mut out = Vec::new();
        loop {
            let t = self.next_token()?;
            let done = matches!(t.tok, Tok::Eof);
            out.push(t);
            if done { return Ok(out); }
        }
    }
}
