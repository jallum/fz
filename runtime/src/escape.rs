//! Backslash escapes: the one reader behind a string literal, a quoted atom, a
//! character literal and `Macro.unescape_string/1`.
//!
//! `read_escape` is the reader. The lexer reports what it refuses;
//! `unescape` applies Elixir's lenient rule to text that is already in a
//! program, such as the raw body of a sigil.

/// What an escape denotes: a character, which a string stores as its UTF-8
/// encoding, or a single byte, which `\xHH` stores as it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Escape {
    Char(char),
    Byte(u8),
}

impl Escape {
    pub fn push_onto(self, bytes: &mut Vec<u8>) {
        match self {
            Escape::Char(c) => bytes.extend_from_slice(c.encode_utf8(&mut [0; 4]).as_bytes()),
            Escape::Byte(b) => bytes.push(b),
        }
    }
}

/// An escape Elixir still reads but warns about.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeprecatedHex {
    /// `\xH`: one digit, where `\xHH` is the byte.
    OneDigit,
    /// `\x{H*}`: braces, where `\uHHHH` is the code point.
    Braced,
}

impl DeprecatedHex {
    /// Elixir's warning, word for word.
    pub fn warning(self) -> &'static str {
        match self {
            DeprecatedHex::OneDigit => {
                "\\xH inside strings/sigils/chars is deprecated, please use \\xHH (byte) or \\uHHHH (code point) instead"
            }
            DeprecatedHex::Braced => {
                "\\x{H*} inside strings/sigils/chars is deprecated, please use \\xHH (byte) or \\uHHHH (code point) instead"
            }
        }
    }
}

/// An escape that was read: what it denotes, how many bytes after the
/// backslash it took, and the deprecation it carries, if any.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReadEscape {
    pub escape: Escape,
    pub consumed: usize,
    pub deprecated: Option<DeprecatedHex>,
}

impl ReadEscape {
    fn current(escape: Escape, consumed: usize) -> Self {
        Self {
            escape,
            consumed,
            deprecated: None,
        }
    }
}

/// Why an escape was not read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EscapeError {
    /// The text ended at the backslash.
    Unterminated,
    /// The byte after the backslash names no escape. It is the one byte read.
    Unknown(u8),
    /// A `\u` or `\x` escape of the wrong form. `consumed` counts the bytes
    /// after the backslash that were read before the form failed.
    Malformed { message: String, consumed: usize },
}

pub const HEX_ESCAPE_SHAPE: &str = "invalid hex escape character, expected \\xHH where H is a hexadecimal digit";
pub const UNICODE_ESCAPE_SHAPE: &str =
    "invalid Unicode escape character, expected \\uHHHH or \\u{H*} where H is a hexadecimal digit";

/// The escape that starts right after a backslash, and how many bytes after
/// the backslash it takes.
pub fn read_escape(rest: &[u8]) -> Result<ReadEscape, EscapeError> {
    let Some(&first) = rest.first() else {
        return Err(EscapeError::Unterminated);
    };
    let named = match first {
        b'n' => '\n',
        b't' => '\t',
        b'r' => '\r',
        b'\\' => '\\',
        b'"' => '"',
        b'#' => '#',
        b'\'' => '\'',
        b's' => ' ',
        b'0' => '\0',
        b'a' => '\u{7}',
        b'b' => '\u{8}',
        b'd' => '\u{7f}',
        b'e' => '\u{1b}',
        b'f' => '\u{c}',
        b'v' => '\u{b}',
        b'u' => {
            return after_letter(read_unicode_escape(&rest[1..]).map(|(c, n)| ReadEscape::current(Escape::Char(c), n)));
        }
        b'x' => return after_letter(read_hex_escape(&rest[1..])),
        other => return Err(EscapeError::Unknown(other)),
    };
    Ok(ReadEscape::current(Escape::Char(named), 1))
}

/// What a `\u` or `\x` reader read, counted from the backslash's next byte
/// rather than from the byte after the letter.
fn after_letter(read: Result<ReadEscape, EscapeError>) -> Result<ReadEscape, EscapeError> {
    match read {
        Ok(read) => Ok(ReadEscape {
            consumed: read.consumed + 1,
            ..read
        }),
        Err(EscapeError::Malformed { message, consumed }) => Err(EscapeError::Malformed {
            message,
            consumed: consumed + 1,
        }),
        Err(other) => Err(other),
    }
}

/// Elixir's rule for text that is already in a program: a backslash and a
/// newline are removed, a backslash before a byte that names no escape leaves
/// the byte, and a lone final backslash stays. A `\u` or `\x` of the wrong form
/// is the error's message. Each deprecated escape read is in the second part, in
/// text order.
pub fn unescape(text: &[u8]) -> Result<(Vec<u8>, Vec<DeprecatedHex>), String> {
    let mut deprecated = Vec::new();
    let mut out = Vec::with_capacity(text.len());
    let mut at = 0;
    while at < text.len() {
        if text[at] != b'\\' {
            out.push(text[at]);
            at += 1;
            continue;
        }
        let rest = &text[at + 1..];
        at += 1 + match read_escape(rest) {
            Ok(read) => {
                read.escape.push_onto(&mut out);
                deprecated.extend(read.deprecated);
                read.consumed
            }
            Err(EscapeError::Unterminated) => {
                out.push(b'\\');
                0
            }
            Err(EscapeError::Unknown(b'\n')) => 1,
            Err(EscapeError::Unknown(b'\r')) if rest.get(1) == Some(&b'\n') => 2,
            Err(EscapeError::Unknown(byte)) => {
                out.push(byte);
                1
            }
            Err(EscapeError::Malformed { message, .. }) => return Err(message),
        };
    }
    Ok((out, deprecated))
}

/// `\uHHHH` or `\u{H...}` with one to six digits, after the `u`.
fn read_unicode_escape(rest: &[u8]) -> Result<(char, usize), EscapeError> {
    if rest.first() == Some(&b'{') {
        return read_braced_code_point(rest, 'u', UNICODE_ESCAPE_SHAPE);
    }
    let digits = hex_digits(rest, 4);
    if digits.len() != 4 {
        return Err(malformed(UNICODE_ESCAPE_SHAPE, digits.len()));
    }
    code_point(digits, 'u', 4)
}

/// `\xHH` is the byte of one or two hex digits, whatever it is; `\x{H...}`
/// is a code point, stored as its UTF-8 encoding. Elixir reads the one-digit
/// and braced forms too, and warns that they are deprecated; the result says
/// which form was read.
fn read_hex_escape(rest: &[u8]) -> Result<ReadEscape, EscapeError> {
    if rest.first() == Some(&b'{') {
        return read_braced_code_point(rest, 'x', HEX_ESCAPE_SHAPE).map(|(c, consumed)| ReadEscape {
            escape: Escape::Char(c),
            consumed,
            deprecated: Some(DeprecatedHex::Braced),
        });
    }
    let digits = hex_digits(rest, 2);
    if digits.is_empty() {
        return Err(malformed(HEX_ESCAPE_SHAPE, 0));
    }
    let byte = u8::from_str_radix(digits, 16).expect("one or two hexadecimal digits fit a byte");
    Ok(ReadEscape {
        escape: Escape::Byte(byte),
        consumed: digits.len(),
        deprecated: (digits.len() == 1).then_some(DeprecatedHex::OneDigit),
    })
}

/// The one to six digits of a braced escape and its closing brace, from the
/// opening one.
fn read_braced_code_point(rest: &[u8], letter: char, shape: &str) -> Result<(char, usize), EscapeError> {
    let digits = hex_digits(&rest[1..], usize::MAX);
    let digits_end = 1 + digits.len();
    if !(1..=6).contains(&digits.len()) || rest.get(digits_end) != Some(&b'}') {
        return Err(malformed(shape, digits_end));
    }
    code_point(digits, letter, digits_end + 1)
}

/// Up to `limit` hexadecimal digits at the start of `rest`.
fn hex_digits(rest: &[u8], limit: usize) -> &str {
    let len = rest.iter().take(limit).take_while(|c| c.is_ascii_hexdigit()).count();
    std::str::from_utf8(&rest[..len]).expect("hexadecimal digits are ASCII")
}

fn code_point(digits: &str, letter: char, consumed: usize) -> Result<(char, usize), EscapeError> {
    let value = u32::from_str_radix(digits, 16).expect("the digits are hexadecimal");
    match char::from_u32(value) {
        Some(c) => Ok((c, consumed)),
        None => Err(malformed(
            &format!("invalid or reserved Unicode code point \\{letter}{{{digits}}}"),
            consumed,
        )),
    }
}

fn malformed(message: &str, consumed: usize) -> EscapeError {
    EscapeError::Malformed {
        message: message.to_string(),
        consumed,
    }
}

#[cfg(test)]
#[path = "escape_test.rs"]
mod escape_test;
