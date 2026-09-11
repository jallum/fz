use super::*;
use crate::source::SourceMap;

fn test_lexer(src: &str) -> Lexer<'_> {
    let mut sources = SourceMap::new();
    let version = sources.add_code(Some("<test>"), src);
    Lexer::with_source_version_and_name(src, version, "<test>")
}

// DROP: lexer infrastructure — span accuracy, no language semantics
#[test]
fn tokens_carry_accurate_byte_spans() {
    let src = "fn foo(x), do: x + 1";
    let toks = test_lexer(src)
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
fn definition_aliases_have_named_definition_tokens_distinct_from_lambdas() {
    let src = "def public(x), do: x\ndefp private(x), do: x\nfn x -> x end\n";
    let toks = test_lexer(src)
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let heads = toks
        .iter()
        .filter_map(|token| {
            let text = &src[token.span.start as usize..token.span.end as usize];
            matches!(text, "def" | "defp" | "fn").then_some(&token.tok)
        })
        .collect::<Vec<_>>();

    assert!(matches!(heads.as_slice(), [Tok::Def, Tok::Defp, Tok::Fn]));
}

// DROP: SourceMap line-resolution, pure infrastructure
#[test]
fn locate_resolves_to_correct_line() {
    let src = "fn a(), do: 1\nfn b(), do: 2\n";
    let mut sm = SourceMap::new();
    let f = sm.add_code(Some("t.fz"), src);
    let toks = Lexer::with_source_version_and_name(src, f, "<test>")
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

// DROP: multi-file span bookkeeping, pure infrastructure
#[test]
fn multi_file_spans_keep_their_source_versions() {
    let mut sm = SourceMap::new();
    let a = sm.add_code(Some("a.fz"), "fn foo()");
    let b = sm.add_code(Some("b.fz"), "fn bar()");
    let toks_a = Lexer::with_source_version_and_name("fn foo()", a, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
    let toks_b = Lexer::with_source_version_and_name("fn bar()", b, "<test>")
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
    assert_eq!(foo.span.source_version, a);
    assert_eq!(bar.span.source_version, b);
    assert_eq!(
        &sm.code(foo.span.source_version).bytes[foo.span.start as usize..foo.span.end as usize],
        "foo"
    );
    assert_eq!(
        &sm.code(bar.span.source_version).bytes[bar.span.start as usize..bar.span.end as usize],
        "bar"
    );
}

// fz-axu.9 (L1) — byte-oriented quoted binary literals.

// DROP: token payload encoding, lexer infrastructure
#[test]
fn binary_literal_carries_raw_bytes() {
    let toks = test_lexer(r#""hi""#)
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    match &toks[0].tok {
        Tok::Binary(b) => assert_eq!(b, &b"hi".to_vec()),
        _ => panic!("expected Tok::Binary, got {:?}", toks[0].tok),
    }
}

// DROP: UTF-8 byte passthrough in lexer, infrastructure
#[test]
fn binary_literal_preserves_non_ascii_utf8_bytes() {
    // "héllo" — `é` is 0xC3 0xA9 in UTF-8. Pre-L1 the lexer was
    // pushing each byte as a `char` via `c as char`, which
    // re-encoded into UTF-8 multi-byte garbage. Post-L1 the bytes
    // pass through unchanged.
    let toks = test_lexer(r#""héllo""#)
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    match &toks[0].tok {
        Tok::Binary(b) => assert_eq!(b, "héllo".as_bytes()),
        _ => panic!("expected Tok::Binary"),
    }
}

// DROP: escape-sequence decoding in lexer, infrastructure
#[test]
fn binary_literal_handles_canonical_escapes() {
    let toks = test_lexer(r#""a\nb\tc\\d\"e""#)
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    match &toks[0].tok {
        Tok::Binary(b) => assert_eq!(b, b"a\nb\tc\\d\"e"),
        _ => panic!("expected Tok::Binary"),
    }
}

// DROP: lexer error on bad escape, infrastructure
#[test]
fn binary_literal_rejects_unknown_escape() {
    let err = test_lexer(r#""bad\q""#)
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
// DROP: Tok::Binary UTF-8 invariant, lexer infrastructure
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
        let toks = test_lexer(src)
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
    test_lexer(src)
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex")
        .into_iter()
        .map(|t| t.tok)
        .filter(|t| !matches!(t, Tok::Eof))
        .collect()
}

// DROP: token shape for new binary operators, pure lexer
#[test]
fn lexes_new_binary_operators() {
    assert_eq!(toks_of("a ++ b"), vec![id("a"), Tok::PlusPlus, id("b")]);
    assert_eq!(toks_of("a -- b"), vec![id("a"), Tok::MinusMinus, id("b")]);
    assert_eq!(toks_of("a <> b"), vec![id("a"), Tok::Concat, id("b")]);
}

// DROP: range and step token shapes, pure lexer
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

// DROP: `..` vs `...` vs float disambiguation, pure lexer
#[test]
fn dotdot_does_not_steal_from_ellipsis_or_float() {
    // `...` stays a single Ellipsis (more specific arm wins).
    assert_eq!(toks_of("..."), vec![Tok::Ellipsis]);
    // A decimal point with a following digit is still a float.
    assert_eq!(toks_of("1.5"), vec![Tok::Float(1.5)]);
    // A range over floats: `1.0..2.0`.
    assert_eq!(toks_of("1.0..2.0"), vec![Tok::Float(1.0), Tok::DotDot, Tok::Float(2.0)]);
}

// DROP: `<>` vs `<<`/`>>` token disambiguation, pure lexer
#[test]
fn concat_does_not_collide_with_bitstring_delimiters() {
    // `<>` is concat; `<<` / `>>` remain bitstring delimiters.
    assert_eq!(toks_of("<<>>"), vec![Tok::LBitstr, Tok::RBitstr]);
    assert_eq!(toks_of("a <> b"), vec![id("a"), Tok::Concat, id("b")]);
}

// DROP: `//` vs `/` token disambiguation, pure lexer
#[test]
fn slashslash_distinct_from_slash() {
    assert_eq!(toks_of("a / b"), vec![id("a"), Tok::Slash, id("b")]);
    assert_eq!(toks_of("a // b"), vec![id("a"), Tok::SlashSlash, id("b")]);
}

// DROP: `in` / `not in` token shapes, pure lexer
#[test]
fn lexes_membership_keywords() {
    assert_eq!(toks_of("x in xs"), vec![id("x"), Tok::In, id("xs")]);
    assert_eq!(toks_of("x not in xs"), vec![id("x"), Tok::Not, Tok::In, id("xs")]);
}

// DROP: `require` keyword token shape, pure lexer
#[test]
fn lexes_require_as_a_first_class_keyword() {
    assert_eq!(
        toks_of("require Helpers"),
        vec![Tok::Require, Tok::Upper("Helpers".to_string())]
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
    test_lexer(src)
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

// DROP: space_before metadata recording, lexer infrastructure
#[test]
fn records_space_before_for_each_token() {
    // Leading token has no space before it; the rest are space-separated.
    assert_eq!(
        spacing_of("a - b"),
        vec![(id("a"), false), (Tok::Minus, true), (id("b"), true)]
    );
}

// DROP: space-sensitive unary/binary disambiguation, lexer metadata
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

// DROP: adjacency flag for call heads, lexer metadata
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

// DROP: lex error span position, pure infrastructure
#[test]
fn lex_error_carries_span_at_offending_byte() {
    let src = "fn `";
    let mut sources = SourceMap::new();
    let version = sources.add_code(Some("<test>"), src);
    let err = Lexer::with_source_version_and_name(src, version, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect_err("should fail");
    // Backtick is at offset 3; err span points at it (or just after).
    assert!(err.span.start <= 3 && err.span.end >= 3, "span={:?}", err.span);
    assert_eq!(err.span.source_version, version);
}

// -- Telemetry integration (fz-ndf.8) --

// DROP: lexer telemetry span and token count, infrastructure
#[test]
fn telemetry_emits_pass_span_and_token_count() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    cap.install(&tel, &[]);
    let observed = std::rc::Rc::new(std::cell::Cell::new(None));
    let sink = std::rc::Rc::clone(&observed);
    tel.attach_raw_event3::<crate::source::SourceVersion, Option<std::rc::Rc<str>>, Vec<Token>, _>(
        &["fz", "lexer", "tokens_built"],
        move |_, _, _, _, _, tokens| sink.set(Some(tokens.len())),
    );

    let src = "fn foo(x), do: x + 1";
    let toks = test_lexer(src).tokenize(&tel).expect("lex");
    let expected_count = toks.len();

    // Span lifecycle: SpanStart + SpanStop bracketing the user event.
    assert_eq!(cap.count_by_kind(EventKind::SpanStart), 1);
    assert_eq!(cap.count_by_kind(EventKind::SpanStop), 1);
    assert_eq!(cap.count(&["fz", "lexer", "pass"]), 2); // start + stop

    assert_eq!(observed.get(), Some(expected_count));
}

// DROP: lexer telemetry span_id inheritance, infrastructure
#[test]
fn telemetry_user_event_inherits_span_id() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind};

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    cap.install(&tel, &[]);

    let _ = test_lexer("fn x() do, :ok end").tokenize(&tel).expect("lex");

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

// DROP: null telemetry no-op, pure infrastructure
#[test]
fn null_telemetry_is_a_silent_no_op() {
    // Same call path; just verifies the null impl compiles + runs.
    let toks = test_lexer("fn x(), do: :ok")
        .tokenize(&crate::telemetry::sink::NullTelemetry)
        .expect("lex");
    assert!(!toks.is_empty());
}

/// Elixir's float-literal grammar requires a fractional part before any
/// exponent: `1e10` is a SyntaxError there, not a float, so accepting it here
/// would be a divergence rather than a convenience.
#[test]
fn float_literals_take_an_exponent_only_after_a_fraction() {
    for (source, expected) in [
        ("1.0e14", 1.0e14f64),
        ("1.0e-7", 1.0e-7),
        ("1.0E3", 1000.0),
        ("1.5e+3", 1500.0),
        ("1_000.5e-3", 1.0005),
        ("5.0e-324", 5.0e-324),
        ("1.7976931348623157e308", 1.7976931348623157e308),
    ] {
        assert_eq!(toks_of(source), vec![Tok::Float(expected)], "`{source}`");
    }
}

/// The exponent is taken only when a digit actually follows, so an `e` that
/// begins the next token is left alone -- `1.0end` must keep its `end`.
#[test]
fn a_trailing_e_without_digits_is_not_an_exponent() {
    assert_eq!(toks_of("1.0e"), vec![Tok::Float(1.0), Tok::Ident("e".to_string())]);
    // `end` is a keyword, so this also shows the number stopping cleanly at a
    // token boundary rather than at a character class.
    assert_eq!(toks_of("1.0end"), vec![Tok::Float(1.0), Tok::End]);
    assert_eq!(toks_of("1.0 e5"), vec![Tok::Float(1.0), Tok::Ident("e5".to_string())],);
}

// DROP: heredoc lexing, lexer infrastructure
#[test]
fn heredoc_is_one_token_holding_its_lines() {
    // `"""` used to be three quote characters: an empty string, then an
    // opening quote. The whole heredoc lexed as several tokens and the
    // content was silently dropped (fz-5xp.78).
    let toks = test_lexer("\"\"\"\nhello\n\"\"\"")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    match &toks[0].tok {
        Tok::Binary(b) => assert_eq!(b, b"hello\n", "a heredoc keeps each content line's newline"),
        other => panic!("expected one Tok::Binary, got {:?}", other),
    }
    assert!(
        matches!(toks[1].tok, Tok::Eof | Tok::Newline),
        "the heredoc should consume its closing delimiter, leaving nothing behind: {:?}",
        toks[1].tok
    );
}

// DROP: heredoc indentation rule, lexer infrastructure
#[test]
fn heredoc_strips_the_closing_delimiters_indentation() {
    // Elixir measures indentation from the closing `"""`, so text indented
    // further than the delimiter keeps the difference.
    let toks = test_lexer("\"\"\"\n  indented\n    deeper\n  \"\"\"")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    match &toks[0].tok {
        Tok::Binary(b) => assert_eq!(b, b"indented\n  deeper\n"),
        other => panic!("expected Tok::Binary, got {:?}", other),
    }
}

// DROP: heredoc edge case, lexer infrastructure
#[test]
fn heredoc_with_no_lines_is_the_empty_binary() {
    let toks = test_lexer("\"\"\"\n\"\"\"")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    match &toks[0].tok {
        Tok::Binary(b) => assert!(b.is_empty(), "an empty heredoc is the empty binary, not a newline"),
        other => panic!("expected Tok::Binary, got {:?}", other),
    }
}

// DROP: heredoc escapes, lexer infrastructure
#[test]
fn heredoc_decodes_escapes_like_any_other_string() {
    let toks = test_lexer("\"\"\"\na\\tb\n\"\"\"")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    match &toks[0].tok {
        Tok::Binary(b) => assert_eq!(b, b"a\tb\n"),
        other => panic!("expected Tok::Binary, got {:?}", other),
    }
}

// DROP: heredoc opening-line rule, lexer infrastructure
#[test]
fn heredoc_refuses_content_on_its_opening_line() {
    // Elixir rejects this outright rather than guessing what the author
    // meant, and so does fz: the text after `"""` has no defined indentation.
    let err = test_lexer("\"\"\"oops\nx\n\"\"\"")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect_err("content on the opening line should not lex");
    assert!(
        err.msg.contains("heredoc"),
        "the diagnostic should name the construct it is rejecting: {}",
        err.msg
    );
}
