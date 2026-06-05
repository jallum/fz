use super::*;
use crate::diag::SourceMap;

#[test]
fn tokens_carry_accurate_byte_spans() {
    let src = "fn foo(x), do: x + 1";
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
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
    let toks = Lexer::with_file_and_source_name(src, f, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
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
    let toks_a = Lexer::with_file_and_source_name("fn foo()", a, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
    let toks_b = Lexer::with_file_and_source_name("fn bar()", b, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
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
    let toks = Lexer::with_source_name(r#""hi""#, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
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
    let toks = Lexer::with_source_name(r#""héllo""#, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    match &toks[0].tok {
        Tok::Binary(b) => assert_eq!(b, "héllo".as_bytes()),
        _ => panic!("expected Tok::Binary"),
    }
}

#[test]
fn binary_literal_handles_canonical_escapes() {
    let toks = Lexer::with_source_name(r#""a\nb\tc\\d\"e""#, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    match &toks[0].tok {
        Tok::Binary(b) => assert_eq!(b, b"a\nb\tc\\d\"e"),
        _ => panic!("expected Tok::Binary"),
    }
}

#[test]
fn binary_literal_rejects_unknown_escape() {
    let err = Lexer::with_source_name(r#""bad\q""#, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
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
        let toks = Lexer::with_source_name(src, "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .expect("lex");
        match &toks[0].tok {
            Tok::Binary(bytes) => {
                from_utf8(bytes).unwrap_or_else(|_| panic!("Tok::Binary must be UTF-8 for {}", src));
            }
            _ => panic!("expected Tok::Binary for {}", src),
        }
    }
}

// fz-g58.1.1 — Elixir-aligned operator tokens.

/// Collect the non-Eof token kinds for a source, for compact assertions.
fn toks_of(src: &str) -> Vec<Tok> {
    Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
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
        vec![Tok::Int(1), Tok::DotDot, Tok::Int(10), Tok::SlashSlash, Tok::Int(2)]
    );
}

#[test]
fn dotdot_does_not_steal_from_ellipsis_or_float() {
    // `...` stays a single Ellipsis (more specific arm wins).
    assert_eq!(toks_of("..."), vec![Tok::Ellipsis]);
    // A decimal point with a following digit is still a float.
    assert_eq!(toks_of("1.5"), vec![Tok::Float(1.5)]);
    // A range over floats: `1.0..2.0`.
    assert_eq!(toks_of("1.0..2.0"), vec![Tok::Float(1.0), Tok::DotDot, Tok::Float(2.0)]);
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
    assert_eq!(toks_of("x not in xs"), vec![id("x"), Tok::Not, Tok::In, id("xs")]);
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
    Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
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
    let err = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect_err("should fail");
    // Backtick is at offset 3; err span points at it (or just after).
    assert!(err.span.start <= 3 && err.span.end >= 3, "span={:?}", err.span);
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
    let toks = Lexer::with_source_name(src, "<test>").tokenize(&tel).expect("lex");
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

    let _ = Lexer::with_source_name("fn x() do, :ok end", "<test>")
        .tokenize(&tel)
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
    // Same call path; just verifies the null impl compiles + runs.
    let toks = Lexer::with_source_name("fn x(), do: :ok", "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    assert!(!toks.is_empty());
}
