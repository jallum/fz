use std::collections::VecDeque;
use std::fmt;
use std::rc::Rc;
use std::str::from_utf8;

use unicode_normalization::{UnicodeNormalization, is_nfc};
use unicode_security::GeneralSecurityProfile;
use unicode_security::mixed_script::AugmentedScriptSet;

use crate::source::{SourceVersion, Span};
use crate::telemetry::{RawSpanTelemetry, Telemetry};

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
    Else,
    When,
    Type,
    In,  // membership operator: `x in xs`
    Not, // boolean negation and `not in`
    And, // boolean conjunction: `a and b`
    Or,  // boolean disjunction: `a or b`
    After,
    Rescue,
    Catch,

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
    /// `===` — strict equality. `==` compares numbers by value, so `1 == 1.0`
    /// is true; `===` asks whether two values are the same value, which is what
    /// membership, `--` and a map key mean.
    EqEqEq,
    NotEqEq,
    /// `&&` — `and` for any value: `nil` and `false` are false, anything else true.
    AndAnd,
    /// `||` — `or` for any value, answering the value that decided.
    OrOr,
    /// `!` — `not` for any value.
    Bang,
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

/// True for tokens whose grammar production is exclusively infix/postfix —
/// they never begin a fresh expression as a prefix. `Minus` and `Percent`
/// are the deliberate exceptions among the operator tokens, because both are
/// dual prefix/infix in fz's grammar: `parse_prefix` accepts `-` as unary
/// negation and `%` as a `%Foo{...}` struct literal, while `infix_bp` also
/// gives them subtraction and modulo. A `-` or `%` leading a fresh physical
/// line is therefore the start of a new statement (unary negation / struct
/// literal), not a continuation. This mirrors Elixir's `unary_op` token
/// classification (elixir_tokenizer.erl), which never swallows a preceding
/// eol for an ambiguous prefix-capable operator; `%` has no modulo in Elixir,
/// so that dual role is fz-specific and must be excluded here explicitly.
fn is_infix_only_continuation(tok: &Tok) -> bool {
    matches!(
        tok,
        Tok::Dot
            | Tok::Eq
            | Tok::When
            | Tok::Or
            | Tok::And
            | Tok::AndAnd
            | Tok::OrOr
            | Tok::EqEq
            | Tok::NotEq
            | Tok::EqEqEq
            | Tok::NotEqEq
            | Tok::Lt
            | Tok::LtEq
            | Tok::Gt
            | Tok::GtEq
            | Tok::Pipe
            | Tok::In
            | Tok::ColonColon
            | Tok::SlashSlash
            | Tok::PlusPlus
            | Tok::MinusMinus
            | Tok::Concat
            | Tok::DotDot
            | Tok::Plus
            | Tok::Star
            | Tok::Slash
    )
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
    text: &'a str,
    src: &'a [u8],
    pos: usize,
    source_version: SourceVersion,
    source_name: Option<Rc<str>>,
    /// fz-5xp.5 — one interpolated string literal lexes to SEVERAL tokens.
    /// `next_token` drains this before reading more source.
    pending: VecDeque<Token>,
}

/// What a complete source word is: a keyword (or `_`), a capitalised name, or
/// a lowercase name.
pub(crate) enum SourceWord {
    Keyword(Tok),
    Upper,
    Ident,
}

/// Classifies a source word. This is the one keyword table, used while lexing
/// and when a quoted name is checked against source spelling.
fn classify_source_word(name: &str) -> SourceWord {
    match name {
        "fn" => SourceWord::Keyword(Tok::Fn),
        "extern" => SourceWord::Keyword(Tok::Extern),
        "defmacro" => SourceWord::Keyword(Tok::Defmacro),
        "defmodule" => SourceWord::Keyword(Tok::Defmodule),
        "defstruct" => SourceWord::Keyword(Tok::Defstruct),
        "defprotocol" => SourceWord::Keyword(Tok::Defprotocol),
        "defimpl" => SourceWord::Keyword(Tok::Defimpl),
        "alias" => SourceWord::Keyword(Tok::Alias),
        "import" => SourceWord::Keyword(Tok::Import),
        "require" => SourceWord::Keyword(Tok::Require),
        "do" => SourceWord::Keyword(Tok::Do),
        "end" => SourceWord::Keyword(Tok::End),
        "else" => SourceWord::Keyword(Tok::Else),
        "when" => SourceWord::Keyword(Tok::When),
        "after" => SourceWord::Keyword(Tok::After),
        "rescue" => SourceWord::Keyword(Tok::Rescue),
        "catch" => SourceWord::Keyword(Tok::Catch),
        "type" => SourceWord::Keyword(Tok::Type),
        "in" => SourceWord::Keyword(Tok::In),
        "not" => SourceWord::Keyword(Tok::Not),
        "and" => SourceWord::Keyword(Tok::And),
        "or" => SourceWord::Keyword(Tok::Or),
        "true" => SourceWord::Keyword(Tok::True),
        "false" => SourceWord::Keyword(Tok::False),
        "nil" => SourceWord::Keyword(Tok::Nil),
        "_" => SourceWord::Keyword(Tok::Underscore),
        _ => {
            if name.as_bytes()[0].is_ascii_uppercase() {
                SourceWord::Upper
            } else {
                SourceWord::Ident
            }
        }
    }
}

/// Classifies a complete source word through the same spelling and keyword
/// authority used while lexing. `None` means source text cannot produce one
/// word token with this spelling.
pub(crate) fn source_word(name: &str) -> Option<SourceWord> {
    let mut chars = name.strip_suffix(is_name_mark).unwrap_or(name).chars();
    if !is_variable_start(chars.next()?)
        || !chars.all(is_word_continue)
        || !is_nfc(name)
        || name.contains(MICRO_SIGN)
        || !is_single_script(name)
    {
        return None;
    }
    let word = classify_source_word(name);
    if matches!(word, SourceWord::Upper) && invalid_alias_character(name).is_some() {
        return None;
    }
    Some(word)
}

const MICRO_SIGN: char = '\u{b5}';
const GREEK_SMALL_MU: char = '\u{3bc}';

/// Elixir folds the micro sign into Greek small mu in every name.
fn fold_micro_sign(c: char) -> char {
    if c == MICRO_SIGN { GREEK_SMALL_MU } else { c }
}

/// A character outside ASCII Elixir lets into a name must be one UTS 39 allows
/// in identifiers, or the micro sign, which is folded before it is checked.
fn is_allowed_outside_ascii(c: char) -> bool {
    c == MICRO_SIGN || c.identifier_allowed()
}

/// A name, atom or keyword key starts with an underscore, an ASCII letter, or
/// an allowed non-ASCII `XID_Start` character.
fn is_name_start(c: char) -> bool {
    if c.is_ascii() {
        c.is_ascii_alphabetic() || c == '_'
    } else {
        unicode_ident::is_xid_start(c) && is_allowed_outside_ascii(c)
    }
}

/// A variable or function name additionally cannot start with an uppercase or
/// titlecase letter outside ASCII; only atoms and keyword keys may.
fn is_variable_start(c: char) -> bool {
    is_name_start(c) && (c.is_ascii() || !is_uppercase_or_titlecase(c))
}

/// An uppercase letter, or a titlecase letter, which is not uppercase but has a
/// different lowercase form.
fn is_uppercase_or_titlecase(c: char) -> bool {
    c.is_uppercase() || c.to_lowercase().next() != Some(c)
}

/// The `?` or `!` that may end a name and nothing else in it.
fn is_name_mark(c: char) -> bool {
    matches!(c, '?' | '!')
}

/// Every character after the first and before the optional final mark: an
/// allowed `XID_Continue` character.
fn is_word_continue(c: char) -> bool {
    if c.is_ascii() {
        c.is_ascii_alphanumeric() || c == '_'
    } else {
        unicode_ident::is_xid_continue(c) && is_allowed_outside_ascii(c)
    }
}

/// Every underscore-separated chunk of a name draws its letters and digits
/// from one script (UTS 39 augmented script sets, as Elixir checks them), so
/// scripts mix only across an underscore.
fn is_single_script(name: &str) -> bool {
    name.split('_').all(|chunk| !resolved_script_set(chunk).is_empty())
}

/// The scripts every constraining character of the chunk can be written in.
fn resolved_script_set(chunk: &str) -> AugmentedScriptSet {
    chunk
        .chars()
        .filter(|c| constrains_script(*c))
        .fold(AugmentedScriptSet::default(), |mut set, c| {
            set.intersect_with(c.into());
            set
        })
}

/// Greek small mu is exempt because Elixir folds `µ` (U+00B5) into it and
/// lets both stand with any script. A non-ASCII character that UTS 39
/// restricts from identifiers can only reach a name by NFC composition, and
/// Elixir gives such a composed character no script either.
fn constrains_script(c: char) -> bool {
    c.is_ascii() || (c != GREEK_SMALL_MU && c.identifier_allowed())
}

/// The first character of a word spelled as an alias that is not an ASCII
/// letter, digit or underscore: a non-ASCII character or a `?` or `!` mark.
fn invalid_alias_character(name: &str) -> Option<char> {
    name.chars().find(|c| !(c.is_ascii_alphanumeric() || *c == '_'))
}

const UNICODE_ESCAPE_SHAPE: &str =
    "invalid Unicode escape character, expected \\uHHHH or \\u{H*} where H is a hexadecimal digit";

/// The name and escape letter of the whitespace characters a literal must spell as an escape.
fn whitespace_escape(c: char) -> Option<(&'static str, char)> {
    match c {
        ' ' => Some(("space", 's')),
        '\n' => Some(("newline", 'n')),
        '\t' => Some(("tab", 't')),
        '\r' => Some(("carriage return", 'r')),
        _ => None,
    }
}

/// Appends the UTF-8 encoding of `c`.
fn push_char(bytes: &mut Vec<u8>, c: char) {
    bytes.extend_from_slice(c.encode_utf8(&mut [0; 4]).as_bytes());
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

impl<'a> Lexer<'a> {
    pub fn with_source_version_and_name(
        src: &'a str,
        source_version: SourceVersion,
        source_name: impl AsRef<str>,
    ) -> Self {
        Self {
            text: src,
            src: src.as_bytes(),
            pos: 0,
            source_version,
            source_name: Some(Rc::from(source_name.as_ref())),
            pending: VecDeque::new(),
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
        Span::new(self.source_version, start as u32, self.pos as u32)
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

    /// The character that starts at byte offset `at`, if it is on a boundary.
    fn char_at(&self, at: usize) -> Option<char> {
        self.text.get(at..)?.chars().next()
    }

    /// The name at the cursor in its NFC spelling, which is how Elixir spells
    /// every unquoted name, with the micro sign folded into Greek small mu. The
    /// name ends after its first `?` or `!`. Spans keep the source text as
    /// written. A name mixing scripts is rejected.
    fn read_ident(&mut self) -> Result<String, LexError> {
        let start = self.pos;
        let first = self
            .char_at(start)
            .expect("a name is only read where a character was peeked");
        self.pos += first.len_utf8();
        while let Some(c) = self.char_at(self.pos).filter(|c| is_word_continue(*c)) {
            self.pos += c.len_utf8();
        }
        if self.char_at(self.pos).is_some_and(is_name_mark) {
            self.pos += 1;
        }
        let name: String = self.text[start..self.pos].chars().map(fold_micro_sign).nfc().collect();
        if !is_single_script(&name) {
            return Err(LexError {
                msg: format!("invalid mixed-script identifier found: {name}"),
                span: self.span_from(start),
            });
        }
        Ok(name)
    }

    /// A word that is not a keyword-list key: a keyword, variable, function
    /// name or alias. The first character as written decides which: only atoms
    /// and keys may start with a non-ASCII uppercase letter, and aliases are
    /// ASCII letters, digits and underscores only.
    fn bare_word_token(&mut self, name: String, start: usize) -> Result<Tok, LexError> {
        let first = self.char_at(start).expect("a word starts at a character");
        if !is_variable_start(first) {
            return Err(self.unexpected_character(start));
        }
        let tok = if first.is_ascii_uppercase() {
            Tok::Upper(name)
        } else {
            Self::keyword_or_ident(name)
        };
        if let Tok::Upper(alias) = &tok {
            self.reject_invalid_alias(alias, start)?;
        }
        Ok(tok)
    }

    /// The error names the first character an alias may not hold.
    fn reject_invalid_alias(&self, name: &str, start: usize) -> Result<(), LexError> {
        let Some(c) = invalid_alias_character(name) else {
            return Ok(());
        };
        Err(LexError {
            msg: format!(
                "invalid character {:?} (code point U+{:04X}) in alias (only ASCII characters are allowed): {}",
                c, c as u32, name
            ),
            span: self.span_from(start),
        })
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
        // An exponent, only after a fractional part: `1.0e14` is a float and
        // `1e10` is a syntax error, which is Elixir's rule rather than an
        // omission. The exponent must have at least one digit, so `1.0 end`
        // and `1.0end` keep their `e` -- the lookahead decides before any
        // input is consumed.
        if is_float && matches!(self.peek(0), Some(b'e') | Some(b'E')) {
            let signed = usize::from(matches!(self.peek(1), Some(b'+') | Some(b'-')));
            if self.peek(1 + signed).is_some_and(|c| c.is_ascii_digit()) {
                self.bump();
                for _ in 0..signed {
                    self.bump();
                }
                self.eat_while(|c| c.is_ascii_digit() || c == b'_');
            }
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
}

/// One piece of a string literal: literal bytes, or the SOURCE TEXT of an
/// `#{...}` expression, which is lexed on its own.
#[derive(Debug)]
enum StringPart {
    Bytes(Vec<u8>),
    /// Byte range into the enclosing source, naming the text between the
    /// braces.
    Interpolation(std::ops::Range<usize>),
}

impl<'a> Lexer<'a> {
    /// fz-5xp.5 — read a quoted literal as alternating literal bytes and
    /// `#{...}` expressions.
    ///
    /// An unescaped `#{` used to be copied through verbatim, so `"a#{1}b"`
    /// evaluated to the six characters `a#{1}b` -- a silent wrong answer, and
    /// the reason every error message a String library produced would have
    /// been wrong.
    fn read_quoted_binary_parts(&mut self) -> Result<Vec<StringPart>, LexError> {
        self.bump(); // consume opening "
        let mut parts: Vec<StringPart> = Vec::new();
        let mut bytes: Vec<u8> = Vec::new();
        loop {
            match self.bump() {
                None => return Err(self.err("unterminated string".into())),
                Some(b'"') => {
                    parts.push(StringPart::Bytes(bytes));
                    return Ok(parts);
                }
                Some(b'\\') => push_char(&mut bytes, self.read_escape()?),
                Some(b'#') if self.peek(0) == Some(b'{') => {
                    self.bump(); // consume {
                    let range = self.read_interpolation_range()?;
                    parts.push(StringPart::Bytes(std::mem::take(&mut bytes)));
                    parts.push(StringPart::Interpolation(range));
                }
                Some(c) => bytes.push(c),
            }
        }
    }

    /// A `"""` heredoc, read with Elixir's rules.
    ///
    /// The opening delimiter takes the rest of its line, the closing
    /// delimiter owns its own line, and that closing line's indentation is
    /// stripped from every content line. The content is the lines between
    /// them, each keeping its newline, so `"""\nhello\n"""` is `"hello\n"`
    /// and a heredoc with no lines is the empty binary.
    ///
    /// De-indenting happens as the bytes are read rather than in a second
    /// pass over a copy, because an interpolation carries a RANGE into the
    /// original source for the sub-lexer to re-read. A copy would renumber
    /// every such range.
    ///
    /// A line indented less than the closing delimiter gives up whatever
    /// leading whitespace it has, which is the value Elixir produces; Elixir
    /// also warns there, and fz does not yet.
    fn read_heredoc_parts(&mut self) -> Result<Vec<StringPart>, LexError> {
        self.pos += 3; // consume the opening """
        self.consume_heredoc_opening_line()?;
        let (body_end, indent) = self.find_heredoc_close(self.pos)?;

        let mut parts: Vec<StringPart> = Vec::new();
        let mut bytes: Vec<u8> = Vec::new();
        let mut at_line_start = true;
        while self.pos < body_end {
            if at_line_start {
                self.skip_heredoc_indent(indent, body_end);
                at_line_start = false;
                continue;
            }
            match self.bump() {
                None => return Err(self.err("unterminated heredoc".into())),
                Some(b'\n') => {
                    bytes.push(b'\n');
                    at_line_start = true;
                }
                Some(b'\\') => push_char(&mut bytes, self.read_escape()?),
                Some(b'#') if self.peek(0) == Some(b'{') => {
                    self.bump(); // consume {
                    let range = self.read_interpolation_range()?;
                    parts.push(StringPart::Bytes(std::mem::take(&mut bytes)));
                    parts.push(StringPart::Interpolation(range));
                }
                Some(c) => bytes.push(c),
            }
        }
        parts.push(StringPart::Bytes(bytes));
        self.pos = body_end + indent + 3; // past the closing line's indent and """
        Ok(parts)
    }

    /// Consume the rest of a heredoc's opening line, which Elixir allows to
    /// hold only whitespace: text there would have no indentation to measure
    /// against the closing delimiter.
    fn consume_heredoc_opening_line(&mut self) -> Result<(), LexError> {
        loop {
            match self.peek(0) {
                Some(b' ') | Some(b'\t') | Some(b'\r') => self.pos += 1,
                Some(b'\n') => {
                    self.pos += 1;
                    return Ok(());
                }
                Some(_) => {
                    self.pos += 1;
                    return Err(
                        self.err("a heredoc opening `\"\"\"` allows only whitespace before the end of its line".into())
                    );
                }
                None => return Err(self.err("unterminated heredoc".into())),
            }
        }
    }

    /// Find the line that closes a heredoc, answering where that line starts
    /// and how far it is indented. The start doubles as the end of the body,
    /// so the closing line contributes nothing to the content.
    fn find_heredoc_close(&self, from: usize) -> Result<(usize, usize), LexError> {
        let mut line_start = from;
        loop {
            if line_start > self.src.len() {
                return Err(self.err("unterminated heredoc".into()));
            }
            let mut cursor = line_start;
            while matches!(self.src.get(cursor), Some(b' ') | Some(b'\t')) {
                cursor += 1;
            }
            if self.src[cursor..].starts_with(b"\"\"\"") {
                return Ok((line_start, cursor - line_start));
            }
            match self.src[line_start..].iter().position(|c| *c == b'\n') {
                Some(offset) => line_start += offset + 1,
                None => return Err(self.err("unterminated heredoc".into())),
            }
        }
    }

    /// Drop up to the closing delimiter's indentation from a content line.
    fn skip_heredoc_indent(&mut self, indent: usize, body_end: usize) {
        let mut dropped = 0;
        while dropped < indent && self.pos < body_end && matches!(self.peek(0), Some(b' ') | Some(b'\t')) {
            self.pos += 1;
            dropped += 1;
        }
    }

    /// The text between `#{` and its matching `}`, with braces nested and
    /// string literals inside skipped so `"#{f(%{a: 1})}"` and
    /// `"#{g("}")}"` both find the right closer.
    fn read_interpolation_range(&mut self) -> Result<std::ops::Range<usize>, LexError> {
        let start = self.pos;
        let mut depth = 1usize;
        loop {
            match self.bump() {
                None => return Err(self.err("unterminated interpolation `#{`".into())),
                Some(b'{') => depth += 1,
                Some(b'}') => {
                    depth -= 1;
                    if depth == 0 {
                        return Ok(start..self.pos - 1);
                    }
                }
                Some(b'"') => {
                    // Skip a nested literal whole; its braces are not ours.
                    loop {
                        match self.bump() {
                            None => return Err(self.err("unterminated string in interpolation".into())),
                            Some(b'\\') => {
                                self.bump();
                            }
                            Some(b'"') => break,
                            Some(_) => {}
                        }
                    }
                }
                Some(_) => {}
            }
        }
    }

    /// The character an escape denotes, read after its backslash. Strings,
    /// heredocs and quoted atoms share this reader.
    fn read_escape(&mut self) -> Result<char, LexError> {
        let start = self.pos - 1;
        match self.bump() {
            Some(b'n') => Ok('\n'),
            Some(b't') => Ok('\t'),
            Some(b'r') => Ok('\r'),
            Some(b'\\') => Ok('\\'),
            Some(b'"') => Ok('"'),
            Some(b'#') => Ok('#'),
            Some(b'\'') => Ok('\''),
            Some(b's') => Ok(' '),
            Some(b'0') => Ok('\0'),
            Some(b'a') => Ok('\u{7}'),
            Some(b'b') => Ok('\u{8}'),
            Some(b'd') => Ok('\u{7f}'),
            Some(b'e') => Ok('\u{1b}'),
            Some(b'f') => Ok('\u{c}'),
            Some(b'v') => Ok('\u{b}'),
            Some(b'u') => self.read_unicode_escape(start),
            Some(c) => Err(self.escape_error(start, &format!("unknown escape `\\{}`", c as char))),
            None => Err(self.err("unterminated escape".into())),
        }
    }

    /// `?c` or `?\e`: the code point of one character or escape, as an integer.
    /// Elixir only warns about a literal whose character is whitespace; fz
    /// asks for the escape, because the bare form hides in a stray `?`.
    fn read_character_literal(&mut self, start: usize) -> Result<Tok, LexError> {
        self.bump(); // consume ?
        let Some(c) = self.char_at(self.pos) else {
            return Err(self.escape_error(start, "a character literal needs a character after `?`"));
        };
        let c = if c == '\\' {
            self.bump();
            if self.peek(0) == Some(b'u') {
                self.bump();
                return Err(self.escape_error(
                    start,
                    "`?\\u` is not an escape in a character literal; write the character itself",
                ));
            }
            self.read_escape()?
        } else {
            self.pos += c.len_utf8();
            if let Some((name, escape)) = whitespace_escape(c) {
                return Err(self.escape_error(start, &format!("write the {name} character literal as `?\\{escape}`")));
            }
            c
        };
        Ok(Tok::Int(i64::from(u32::from(c))))
    }

    /// `\uHHHH` or `\u{H...}` with one to six digits, after the `u`.
    fn read_unicode_escape(&mut self, start: usize) -> Result<char, LexError> {
        let braced = self.peek(0) == Some(b'{');
        if braced {
            self.bump();
        }
        let digits_start = self.pos;
        let limit = if braced { usize::MAX } else { 4 };
        let mut count = 0;
        while count < limit && self.peek(0).is_some_and(|c| c.is_ascii_hexdigit()) {
            self.bump();
            count += 1;
        }
        let text = self.text;
        let digits = &text[digits_start..self.pos];
        let well_formed = if braced {
            (1..=6).contains(&count) && self.peek(0) == Some(b'}')
        } else {
            count == 4
        };
        if !well_formed {
            return Err(self.escape_error(start, UNICODE_ESCAPE_SHAPE));
        }
        let value = u32::from_str_radix(digits, 16).expect("the digits are hexadecimal");
        if braced {
            self.bump(); // consume }
        }
        char::from_u32(value).ok_or_else(|| {
            self.escape_error(
                start,
                &format!("invalid or reserved Unicode code point \\u{{{digits}}}"),
            )
        })
    }

    /// An error underlining the escape from its backslash to the cursor.
    fn escape_error(&self, start: usize, msg: &str) -> LexError {
        LexError {
            msg: msg.to_string(),
            span: self.span_from(start),
        }
    }

    /// Desugar an interpolated literal into the tokens it means, which is
    /// exactly Elixir's own lowering:
    ///
    /// ```text
    /// "a#{x}b"   ->   "a" <> Kernel.to_string(x) <> "b"
    /// ```
    ///
    /// Doing it HERE rather than in the parser means the rest of the compiler
    /// never learns a new node: an interpolated string is ordinary concat and
    /// an ordinary call by the time anything else sees it. Empty literal
    /// pieces are dropped, so `"#{x}"` is one call rather than a concat with
    /// two empty binaries.
    fn interpolation_tokens(
        &mut self,
        parts: Vec<StringPart>,
        start: usize,
        space_before: bool,
    ) -> Result<Token, LexError> {
        let span = self.span_from(start);
        let mut pieces: Vec<Vec<Tok>> = Vec::new();
        for part in parts {
            match part {
                StringPart::Bytes(bytes) if bytes.is_empty() => {}
                StringPart::Bytes(bytes) => pieces.push(vec![Tok::Binary(bytes)]),
                StringPart::Interpolation(range) => {
                    let source = from_utf8(&self.src[range.clone()])
                        .map_err(|e| self.err(format!("invalid UTF-8 in interpolation: {}", e)))?;
                    let inner = Lexer::with_source_version_and_name(
                        source,
                        self.source_version,
                        self.source_name.as_deref().unwrap_or(""),
                    )
                    .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
                    .map_err(|e| self.err(format!("in interpolation: {}", e.msg)))?;
                    let mut toks: Vec<Tok> = inner
                        .into_iter()
                        .map(|token| token.tok)
                        .filter(|tok| !matches!(tok, Tok::Eof | Tok::Newline))
                        .collect();
                    if toks.is_empty() {
                        return Err(self.err("empty interpolation `#{}`".into()));
                    }
                    let mut call = vec![
                        Tok::Ident("Kernel".into()),
                        Tok::Dot,
                        Tok::Ident("to_string".into()),
                        Tok::LParen,
                    ];
                    call.append(&mut toks);
                    call.push(Tok::RParen);
                    pieces.push(call);
                }
            }
        }
        if pieces.is_empty() {
            pieces.push(vec![Tok::Binary(Vec::new())]);
        }
        let mut flat: Vec<Tok> = Vec::new();
        for (index, piece) in pieces.into_iter().enumerate() {
            if index > 0 {
                flat.push(Tok::Concat);
            }
            flat.extend(piece);
        }
        let mut iter = flat.into_iter();
        let first = iter.next().expect("at least one token");
        for tok in iter {
            self.pending.push_back(Token {
                tok,
                span,
                space_before: false,
            });
        }
        Ok(Token {
            tok: first,
            span,
            space_before,
        })
    }
}

impl<'a> Lexer<'a> {
    /// fz-axu.9 (L1) — byte-oriented quoted binary literal reader, for the
    /// sites that name a value rather than build one: atom names, `@doc`
    /// text, extern ABI strings. Interpolation is not meaningful there, so
    /// this reader keeps rejecting nothing and copying bytes; expression
    /// literals go through `read_quoted_binary_parts`.
    fn read_quoted_binary_bytes(&mut self) -> Result<Vec<u8>, LexError> {
        self.bump(); // consume opening "
        let mut bytes: Vec<u8> = Vec::new();
        loop {
            match self.bump() {
                None => return Err(self.err("unterminated string".into())),
                Some(b'"') => return Ok(bytes),
                Some(b'\\') => push_char(&mut bytes, self.read_escape()?),
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
            span: Span::new(self.source_version, start, end),
        }
    }

    /// Consumes the whole character at `start` and names it. The source is a
    /// `&str`, so `start` is always on a character boundary.
    fn unexpected_character(&mut self, start: usize) -> LexError {
        let ch = self.text[start..]
            .chars()
            .next()
            .expect("an unexpected character is only reported where a byte was peeked");
        self.pos = start + ch.len_utf8();
        LexError {
            msg: format!("unexpected character {:?}", ch),
            span: self.span_from(start),
        }
    }

    fn keyword_or_ident(name: String) -> Tok {
        match classify_source_word(&name) {
            SourceWord::Keyword(keyword) => keyword,
            SourceWord::Upper => Tok::Upper(name),
            SourceWord::Ident => Tok::Ident(name),
        }
    }

    pub fn next_token(&mut self) -> Result<Token, LexError> {
        if let Some(token) = self.pending.pop_front() {
            return Ok(token);
        }
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
                let name = self.read_ident()?;
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
                    if self.peek(0) == Some(b'=') {
                        self.bump();
                        Tok::EqEqEq
                    } else {
                        Tok::EqEq
                    }
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
                    if self.peek(0) == Some(b'=') {
                        self.bump();
                        Tok::NotEqEq
                    } else {
                        Tok::NotEq
                    }
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
                _ if self.char_at(self.pos + 1).is_some_and(is_name_start) => {
                    self.bump(); // consume :
                    let name = self.read_ident()?;
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

            b'"' if self.peek(1) == Some(b'"') && self.peek(2) == Some(b'"') => {
                let parts = self.read_heredoc_parts()?;
                if parts.iter().any(|part| matches!(part, StringPart::Interpolation(_))) {
                    return self.interpolation_tokens(parts, start, space_before);
                }
                match parts.into_iter().next() {
                    Some(StringPart::Bytes(bytes)) => Tok::Binary(bytes),
                    _ => Tok::Binary(Vec::new()),
                }
            }

            b'"' => {
                let parts = self.read_quoted_binary_parts()?;
                if parts.iter().any(|part| matches!(part, StringPart::Interpolation(_))) {
                    return self.interpolation_tokens(parts, start, space_before);
                }
                let bytes = match parts.into_iter().next() {
                    Some(StringPart::Bytes(bytes)) => bytes,
                    _ => Vec::new(),
                };
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
            b'?' => self.read_character_literal(start)?,
            c if c.is_ascii_digit() => self.read_number()?,
            _ if self.char_at(self.pos).is_some_and(is_name_start) => {
                let name = self.read_ident()?;
                // `name:` (but not `::`) is a keyword-list key like `do:`.
                if self.peek(0) == Some(b':') && self.peek(1) != Some(b':') {
                    self.bump();
                    if self.keyword_value_starts_after_colon() {
                        Tok::KwKey(name)
                    } else {
                        return Err(self.err(format!("keyword argument must be followed by space after: {}:", name)));
                    }
                } else {
                    self.bare_word_token(name, start)?
                }
            }
            _ => return Err(self.unexpected_character(start)),
        };

        Ok(Token {
            tok,
            span: self.span_from(start),
            space_before,
        })
    }

    /// Owns the eol/continuation decision at tokenize time (Elixir model:
    /// elixir_tokenizer.erl's `add_token_with_eol`/`previous_was_eol`). A
    /// physical newline is emitted as a first-class `Tok::Newline`. When
    /// the next real token is one that can *only* be infix/postfix — it has
    /// no unary/prefix production, see [`is_infix_only_continuation`] — any
    /// run of `Newline`s immediately before it is dropped, so the token
    /// continues the previous expression regardless of which line it
    /// starts. Tokens that double as a prefix (`Minus`, `Percent`, and
    /// anything else `parse_prefix` accepts) are excluded on purpose: a
    /// leading `-` or `%` after a real newline always starts a fresh
    /// statement (unary negation / `%Foo{...}` struct literal), never a
    /// continuation of the previous one — this is what lets the parser's
    /// Pratt loop stop at a bare `Newline` by construction, with no
    /// lookahead heuristic required downstream.
    pub fn tokenize<T: RawSpanTelemetry + ?Sized>(mut self, tel: &T) -> Result<Vec<Token>, LexError> {
        let _span = start_lexer_pass(tel, &self.source_version, &self.source_name);
        let mut out: Vec<Token> = Vec::new();
        loop {
            let t = self.next_token()?;
            let done = matches!(t.tok, Tok::Eof);
            if is_infix_only_continuation(&t.tok) {
                while matches!(out.last().map(|last| &last.tok), Some(Tok::Newline)) {
                    out.pop();
                }
            }
            out.push(t);
            if done {
                emit_tokens_built(tel, &self.source_version, &self.source_name, &out);
                return Ok(out);
            }
        }
    }
}

fn start_lexer_pass<'a, T: RawSpanTelemetry + ?Sized>(
    tel: &'a T,
    code: &SourceVersion,
    source_name: &Option<Rc<str>>,
) -> <T as RawSpanTelemetry>::Span2_0<'a, SourceVersion, Option<Rc<str>>> {
    use crate::telemetry::TelemetryExt;
    tel.raw_span2_0(LEX_PASS_NAME, code, source_name)
}

fn emit_tokens_built<T: Telemetry + ?Sized>(
    tel: &T,
    code: &SourceVersion,
    source_name: &Option<Rc<str>>,
    tokens: &Vec<Token>,
) {
    use crate::telemetry::TelemetryExt;
    tel.raw_event3(TOKENS_BUILT_NAME, code, source_name, tokens);
}

const LEX_PASS_NAME: &[&str] = &["fz", "lexer", "pass"];
const TOKENS_BUILT_NAME: &[&str] = &["fz", "lexer", "tokens_built"];

#[cfg(test)]
#[path = "lexer_test.rs"]
mod lexer_test;
