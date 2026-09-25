use super::*;

#[test]
fn ascii_printable_passes() {
    assert!(is_printable_utf8("hello world"));
    assert!(is_printable_utf8(""));
    assert!(is_printable_utf8("/tmp/fz-x5m"));
}

#[test]
fn utf8_non_ascii_passes() {
    assert!(is_printable_utf8("héllo"));
    assert!(is_printable_utf8("日本語"));
}

#[test]
fn whitelisted_controls_pass() {
    assert!(is_printable_utf8("line\nbreak"));
    assert!(is_printable_utf8("tab\tseparated"));
    assert!(is_printable_utf8("\r\n"));
}

#[test]
fn other_controls_fail() {
    assert!(!is_printable_utf8("\x01"));
    assert!(!is_printable_utf8("\x00"));
    assert!(!is_printable_utf8("\x7f"));
    assert!(!is_printable_utf8("hello\x01world"));
}

#[test]
fn escape_round_trips_through_display() {
    assert_eq!(escape_for_display("a\nb"), "a\\nb");
    assert_eq!(escape_for_display("\"quoted\""), "\\\"quoted\\\"");
    assert_eq!(escape_for_display("plain"), "plain");
    assert_eq!(escape_for_display("a\tb\rc"), "a\\tb\\rc");
}
