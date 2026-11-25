use super::*;

fn read(text: &str) -> Result<(Escape, usize), EscapeError> {
    read_escape(text.as_bytes()).map(|read| (read.escape, read.consumed))
}

fn deprecation(text: &str) -> Option<DeprecatedHex> {
    read_escape(text.as_bytes()).expect("a well-formed escape").deprecated
}

#[test]
fn a_named_escape_is_one_byte_after_the_backslash() {
    for (text, expected) in [
        ("n", '\n'),
        ("t", '\t'),
        ("r", '\r'),
        ("\\", '\\'),
        ("\"", '"'),
        ("'", '\''),
        ("#", '#'),
        ("s", ' '),
        ("0", '\0'),
        ("a", '\u{7}'),
        ("b", '\u{8}'),
        ("d", '\u{7f}'),
        ("e", '\u{1b}'),
        ("f", '\u{c}'),
        ("v", '\u{b}'),
    ] {
        assert_eq!(read(text), Ok((Escape::Char(expected), 1)), "\\{text}");
    }
}

#[test]
fn a_unicode_escape_is_four_digits_or_a_braced_code_point() {
    assert_eq!(read("u00e9"), Ok((Escape::Char('é'), 5)));
    assert_eq!(read("u{1F600}"), Ok((Escape::Char('😀'), 8)));
    assert_eq!(read("u{e9}x"), Ok((Escape::Char('é'), 5)));
}

#[test]
fn a_hex_escape_is_one_byte_of_one_or_two_digits() {
    assert_eq!(read("x41"), Ok((Escape::Byte(0x41), 3)));
    assert_eq!(read("x4Z"), Ok((Escape::Byte(4), 2)));
    assert_eq!(read("xff"), Ok((Escape::Byte(0xff), 3)));
}

#[test]
fn a_one_digit_or_braced_hex_escape_is_read_and_flagged_deprecated() {
    assert_eq!(read("x4"), Ok((Escape::Byte(4), 2)));
    assert_eq!(read("x{41}"), Ok((Escape::Char('A'), 5)));
    assert_eq!(deprecation("x4"), Some(DeprecatedHex::OneDigit));
    assert_eq!(deprecation("x{41}"), Some(DeprecatedHex::Braced));
}

#[test]
fn the_current_escape_forms_are_not_deprecated() {
    for text in ["x41", "u00e9", "u{e9}", "n"] {
        assert_eq!(deprecation(text), None, "\\{text}");
    }
}

#[test]
fn a_malformed_escape_reports_what_it_read() {
    assert_eq!(
        read("u00"),
        Err(EscapeError::Malformed {
            message: UNICODE_ESCAPE_SHAPE.to_string(),
            consumed: 3
        })
    );
    assert_eq!(
        read("xZ"),
        Err(EscapeError::Malformed {
            message: HEX_ESCAPE_SHAPE.to_string(),
            consumed: 1
        })
    );
    assert_eq!(
        read("ud800"),
        Err(EscapeError::Malformed {
            message: "invalid or reserved Unicode code point \\u{d800}".to_string(),
            consumed: 5
        })
    );
}

#[test]
fn an_unknown_escape_and_a_missing_one_are_told_apart() {
    assert_eq!(read("q"), Err(EscapeError::Unknown(b'q')));
    assert_eq!(read(""), Err(EscapeError::Unterminated));
}

fn unescaped(text: &str) -> Result<String, String> {
    unescape(text.as_bytes()).map(|(bytes, _)| String::from_utf8(bytes).expect("UTF-8"))
}

#[test]
fn unescape_reads_the_escapes_a_string_literal_reads() {
    assert_eq!(unescaped(r"a\nb\tc\\d"), Ok("a\nb\tc\\d".to_string()));
    assert_eq!(unescaped(r"\x41é\u{1F600}"), Ok("Aé😀".to_string()));
    assert_eq!(unescaped("plain"), Ok("plain".to_string()));
}

/// Elixir's rule for text already in a program: an unknown escape leaves the
/// character, a backslash and a newline vanish, and a final backslash stays.
#[test]
fn unescape_is_lenient_where_the_lexer_is_not() {
    assert_eq!(unescaped(r"\q\1"), Ok("q1".to_string()));
    assert_eq!(unescaped("a\\\nb"), Ok("ab".to_string()));
    assert_eq!(unescaped("a\\\r\nb"), Ok("ab".to_string()));
    assert_eq!(unescaped("a\\"), Ok("a\\".to_string()));
}

#[test]
fn unescape_refuses_a_malformed_escape_with_its_message() {
    assert_eq!(unescaped(r"\u00"), Err(UNICODE_ESCAPE_SHAPE.to_string()));
    assert_eq!(unescaped(r"a\xZ"), Err(HEX_ESCAPE_SHAPE.to_string()));
}

#[test]
fn unescape_keeps_a_hex_escape_that_is_not_utf8_as_its_byte() {
    assert_eq!(unescape(br"\xff"), Ok((vec![0xff], vec![])));
}

#[test]
fn unescape_lists_the_deprecated_escapes_in_text_order() {
    assert_eq!(
        unescape(br"\x4\x41\x{42}"),
        Ok((
            vec![4, b'A', b'B'],
            vec![DeprecatedHex::OneDigit, DeprecatedHex::Braced]
        ))
    );
}
