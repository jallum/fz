use super::*;
use crate::source::SourceMap;

fn test_lexer(src: &str) -> Lexer<'_> {
    let mut sources = SourceMap::new();
    let version = sources.add_code(Some("<test>"), src);
    Lexer::with_source_version_and_name(src, version, "<test>")
}

#[test]
fn when_at_the_start_of_a_line_continues_the_previous_expression() {
    let tokens = test_lexer("value\n  when ready\nnext\n")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let kinds = tokens.into_iter().map(|token| token.tok).collect::<Vec<_>>();

    assert_eq!(
        kinds,
        vec![
            Tok::Ident("value".to_string()),
            Tok::When,
            Tok::Ident("ready".to_string()),
            Tok::Newline,
            Tok::Ident("next".to_string()),
            Tok::Newline,
            Tok::Eof,
        ]
    );
}

#[test]
fn rescue_and_catch_are_block_keywords() {
    let tokens = test_lexer("try do\n  x\nrescue\n  e -> e\ncatch\n  v -> v\nafter\n  y\nend\n")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let keywords = tokens
        .into_iter()
        .filter(|token| matches!(token.tok, Tok::Do | Tok::Rescue | Tok::Catch | Tok::After | Tok::End))
        .map(|token| token.tok)
        .collect::<Vec<_>>();

    assert_eq!(keywords, vec![Tok::Do, Tok::Rescue, Tok::Catch, Tok::After, Tok::End]);
}

#[test]
fn def_and_defp_are_ordinary_identifiers() {
    let tokens = test_lexer("def public(), do: 1\ndefp private(), do: 2\n")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let heads = tokens
        .into_iter()
        .filter_map(|token| match token.tok {
            Tok::Ident(name) if name == "def" || name == "defp" => Some(name),
            _ => None,
        })
        .collect::<Vec<_>>();

    assert_eq!(heads, ["def", "defp"]);
}

// DROP: lexer infrastructure — span accuracy, no language semantics
#[test]
fn tokens_carry_accurate_byte_spans() {
    let src = "def foo(x), do: x + 1";
    let toks = test_lexer(src)
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    // Every non-Eof token's span text matches the lexeme we expect.
    for t in &toks {
        let slice = &src[t.span.start as usize..t.span.end as usize];
        match &t.tok {
            Tok::Ident(n) if n == "def" => assert_eq!(slice, "def"),
            Tok::Ident(n) if n == "foo" => assert_eq!(slice, "foo"),
            Tok::Ident(n) if n == "x" => assert_eq!(slice, "x"),
            Tok::Int(1) => assert_eq!(slice, "1"),
            Tok::Plus => assert_eq!(slice, "+"),
            Tok::KwKey(k) if k == "do" => assert_eq!(slice, "do:"),
            _ => {}
        }
    }
}

// DROP: SourceMap line-resolution, pure infrastructure
#[test]
fn locate_resolves_to_correct_line() {
    let src = "def a(), do: 1\ndef b(), do: 2\n";
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
    assert_eq!(loc.col, 5);
}

// DROP: multi-file span bookkeeping, pure infrastructure
#[test]
fn multi_file_spans_keep_their_source_versions() {
    let mut sm = SourceMap::new();
    let a = sm.add_code(Some("a.fz"), "def foo()");
    let b = sm.add_code(Some("b.fz"), "def bar()");
    let toks_a = Lexer::with_source_version_and_name("def foo()", a, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
    let toks_b = Lexer::with_source_version_and_name("def bar()", b, "<test>")
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

#[test]
fn lexes_the_value_boolean_operators() {
    assert_eq!(toks_of("a || b"), vec![id("a"), Tok::OrOr, id("b")]);
    assert_eq!(toks_of("a && b"), vec![id("a"), Tok::AndAnd, id("b")]);
    assert_eq!(toks_of("!a"), vec![Tok::Bang, id("a")]);
    assert_eq!(toks_of("!!a"), vec![Tok::Bang, Tok::Bang, id("a")]);
}

#[test]
fn bang_does_not_steal_from_the_inequality_operators() {
    assert_eq!(toks_of("a != b"), vec![id("a"), Tok::NotEq, id("b")]);
    assert_eq!(toks_of("a !== b"), vec![id("a"), Tok::NotEqEq, id("b")]);
    assert_eq!(toks_of("!a != b"), vec![Tok::Bang, id("a"), Tok::NotEq, id("b")]);
}

#[test]
fn the_value_boolean_operators_stay_apart_from_pipe_bar_and_capture() {
    assert_eq!(toks_of("a |> b"), vec![id("a"), Tok::Pipe, id("b")]);
    assert_eq!(
        toks_of("[h | t]"),
        vec![Tok::LBrack, id("h"), Tok::Bar, id("t"), Tok::RBrack]
    );
    assert_eq!(toks_of("&foo/1"), vec![Tok::Amp, id("foo"), Tok::Slash, Tok::Int(1)]);
}

#[test]
fn a_line_starting_with_a_value_boolean_infix_continues_the_previous_expression() {
    assert_eq!(
        toks_of("a\n  || b\n  && c\n"),
        vec![id("a"), Tok::OrOr, id("b"), Tok::AndAnd, id("c"), Tok::Newline]
    );
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

    let src = "def foo(x), do: x + 1";
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

    let _ = test_lexer("def x() do, :ok end").tokenize(&tel).expect("lex");

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
    let toks = test_lexer("def x(), do: :ok")
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

#[test]
fn an_unexpected_non_ascii_character_is_named_whole_and_spanned_exactly() {
    let src = "caf€ = 1";
    let mut sources = SourceMap::new();
    let version = sources.add_code(Some("<test>"), src);
    let err = Lexer::with_source_version_and_name(src, version, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect_err("`€` is not an identifier character");
    assert_eq!(err.msg, "unexpected character '€'");
    assert_eq!(&src[err.span.start as usize..err.span.end as usize], "€");
}

fn lex_kinds(src: &str) -> Result<Vec<Tok>, LexError> {
    test_lexer(src)
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .map(|tokens| tokens.into_iter().map(|token| token.tok).collect())
}

/// A lowercase letter outside ASCII starts a variable, as it does in Elixir.
#[test]
fn a_variable_may_start_with_a_non_ascii_lowercase_letter() {
    assert_eq!(lex_kinds("éa").unwrap(), vec![Tok::Ident("éa".to_string()), Tok::Eof]);
}

/// A letter with no case, such as a CJK ideograph, starts a variable.
#[test]
fn a_variable_may_start_with_a_caseless_letter() {
    assert_eq!(
        lex_kinds("日本").unwrap(),
        vec![Tok::Ident("日本".to_string()), Tok::Eof]
    );
}

/// Non-ASCII XID_Continue characters continue a name, and `?` and `!` still end it.
#[test]
fn a_name_continues_through_non_ascii_letters_and_ends_with_a_mark() {
    assert_eq!(
        lex_kinds("café? naïve!").unwrap(),
        vec![
            Tok::Ident("café?".to_string()),
            Tok::Ident("naïve!".to_string()),
            Tok::Eof
        ]
    );
}

/// An atom spells its name by the same classes as a variable.
#[test]
fn an_atom_may_hold_non_ascii_letters() {
    assert_eq!(
        lex_kinds(":café").unwrap(),
        vec![Tok::Atom("café".to_string()), Tok::Eof]
    );
}

/// An atom may start with an uppercase letter outside ASCII, as in Elixir's `:Élixir`.
#[test]
fn an_atom_may_start_with_a_non_ascii_uppercase_letter() {
    assert_eq!(
        lex_kinds(":Élixir").unwrap(),
        vec![Tok::Atom("Élixir".to_string()), Tok::Eof]
    );
}

/// A titlecase letter cannot start an atom, which Elixir rejects as well.
#[test]
fn an_atom_cannot_start_with_a_titlecase_letter() {
    let error = lex_kinds(":ǅa").unwrap_err();
    assert_eq!(error.msg, "unexpected character 'ǅ'");
}

/// A keyword key is a name followed by a colon, so it takes non-ASCII letters too.
#[test]
fn a_keyword_key_may_hold_non_ascii_letters() {
    assert_eq!(lex_kinds("[café: 1]").unwrap()[1], Tok::KwKey("café".to_string()));
}

/// An uppercase letter outside ASCII cannot start a variable and is named whole.
#[test]
fn a_non_ascii_uppercase_letter_cannot_start_a_variable() {
    let error = lex_kinds("Élan").unwrap_err();
    assert_eq!(error.msg, "unexpected character 'É'");
}

/// A titlecase letter cannot start a variable either.
#[test]
fn a_titlecase_letter_cannot_start_a_variable() {
    let error = lex_kinds("ǅa").unwrap_err();
    assert_eq!(error.msg, "unexpected character 'ǅ'");
}

/// An alias is ASCII only; the first other character is named with its code point.
#[test]
fn an_alias_with_a_non_ascii_character_is_rejected() {
    let error = lex_kinds("Abé").unwrap_err();
    assert_eq!(
        error.msg,
        "invalid character 'é' (code point U+00E9) in alias (only ASCII characters are allowed): Abé"
    );
}

/// A keyword key is not an alias, so `Abé: 1` lexes as a key.
#[test]
fn a_capitalised_keyword_key_may_hold_non_ascii_letters() {
    assert_eq!(lex_kinds("[Abé: 1]").unwrap()[1], Tok::KwKey("Abé".to_string()));
}

/// The macro surface and the lexer answer "is this one source word" identically.
#[test]
fn source_word_classifies_non_ascii_names_as_the_lexer_does() {
    assert!(matches!(source_word("café"), Some(SourceWord::Ident)));
    assert!(source_word("Élan").is_none());
    assert!(source_word("Abé").is_none());
    assert!(matches!(source_word("Ab"), Some(SourceWord::Upper)));
    assert!(source_word("a€").is_none());
}

/// A keyword key may start with an uppercase letter outside ASCII, which a variable may not.
#[test]
fn a_keyword_key_may_start_with_a_non_ascii_uppercase_letter() {
    assert_eq!(lex_kinds("[Élan: 1]").unwrap()[1], Tok::KwKey("Élan".to_string()));
}

/// An unquoted name spelled with a combining accent lexes to the composed (NFC) spelling.
#[test]
fn an_unquoted_name_is_normalized_to_nfc() {
    assert_eq!(
        lex_kinds("cafe\u{301}").unwrap(),
        vec![Tok::Ident("caf\u{e9}".to_string()), Tok::Eof]
    );
}

/// An unquoted atom is normalized, so both spellings are one atom.
#[test]
fn an_unquoted_atom_is_normalized_to_nfc() {
    assert_eq!(
        lex_kinds(":cafe\u{301}").unwrap(),
        vec![Tok::Atom("caf\u{e9}".to_string()), Tok::Eof]
    );
}

/// A keyword key is normalized like any other unquoted name.
#[test]
fn a_keyword_key_is_normalized_to_nfc() {
    assert_eq!(
        lex_kinds("[cafe\u{301}: 1]").unwrap()[1],
        Tok::KwKey("caf\u{e9}".to_string())
    );
}

/// A quoted atom keeps the spelling it was written with, as in Elixir.
#[test]
fn a_quoted_atom_is_not_normalized() {
    assert_eq!(
        lex_kinds(":\"cafe\u{301}\"").unwrap(),
        vec![Tok::Atom("cafe\u{301}".to_string()), Tok::Eof]
    );
}

/// A string literal keeps its bytes; only names are normalized.
#[test]
fn a_string_is_not_normalized() {
    assert_eq!(
        lex_kinds("\"cafe\u{301}\"").unwrap(),
        vec![Tok::Binary("cafe\u{301}".as_bytes().to_vec()), Tok::Eof]
    );
}

/// A diagnostic span names the source as written, so normalization does not move it.
#[test]
fn a_normalized_name_keeps_the_span_of_its_source_text() {
    let tokens = test_lexer("cafe\u{301} = 1")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
    assert_eq!((tokens[0].span.start, tokens[0].span.end), (0, 6));
}

/// The macro surface rejects a spelling the lexer would have normalized,
/// because source text cannot produce a word token with that spelling.
#[test]
fn source_word_accepts_only_the_normalized_spelling() {
    assert!(matches!(source_word("caf\u{e9}"), Some(SourceWord::Ident)));
    assert!(source_word("cafe\u{301}").is_none());
}

/// A name mixing Latin and Cyrillic letters is rejected with Elixir's headline.
#[test]
fn a_name_mixing_latin_and_cyrillic_is_rejected() {
    let error = lex_kinds("a\u{430} = 1").unwrap_err();
    assert_eq!(error.msg, "invalid mixed-script identifier found: a\u{430}");
    assert_eq!((error.span.start, error.span.end), (0, 3));
}

/// The rule applies to atoms, keyword keys and the sigil name as to variables.
#[test]
fn an_atom_and_a_keyword_key_mixing_scripts_are_rejected() {
    assert!(
        lex_kinds(":a\u{430}")
            .unwrap_err()
            .msg
            .starts_with("invalid mixed-script")
    );
    assert!(
        lex_kinds("[a\u{430}: 1]")
            .unwrap_err()
            .msg
            .starts_with("invalid mixed-script")
    );
}

/// A quoted atom and a string may mix scripts: only names are checked.
#[test]
fn quoted_atoms_and_strings_may_mix_scripts() {
    assert!(lex_kinds(":\"a\u{430}\"").is_ok());
    assert!(lex_kinds("\"a\u{430}\"").is_ok());
}

/// A name wholly in one script, with digits and underscores, is accepted.
#[test]
fn a_single_script_name_with_digits_and_underscores_is_accepted() {
    assert!(lex_kinds("\u{43f}\u{440}\u{438}\u{432}\u{435}\u{442}_1").is_ok());
    assert!(lex_kinds("_\u{430}").is_ok());
    assert!(lex_kinds("a1_b").is_ok());
}

/// Han, Hiragana and Katakana together are one writing system (Japanese).
#[test]
fn han_hiragana_and_katakana_may_share_a_name() {
    assert!(lex_kinds("\u{65e5}\u{3042}\u{30a2}").is_ok());
    assert!(lex_kinds("\u{65e5}\u{ac00}").is_ok());
}

/// Han with Latin is mixed, as in Elixir.
#[test]
fn han_with_latin_is_rejected() {
    assert!(lex_kinds("\u{65e5}a").is_err());
}

/// Each underscore-separated chunk is checked alone, so scripts may be
/// separated by an underscore.
#[test]
fn scripts_separated_by_an_underscore_are_accepted() {
    assert!(lex_kinds("a_\u{430}").is_ok());
    assert!(lex_kinds("\u{430}_a_\u{3b1}").is_ok());
}

/// Non-ASCII digits belong to a script and do not mix with Latin letters.
#[test]
fn a_non_ascii_digit_belongs_to_its_script() {
    assert!(lex_kinds("a\u{661}").is_err());
    assert!(lex_kinds("\u{430}\u{661}").is_err());
}

/// The check follows normalization: a decomposed name is judged in its NFC spelling.
#[test]
fn the_script_check_sees_the_normalized_name() {
    assert!(lex_kinds("cafe\u{301}").is_ok());
}

/// The macro surface rejects a mixed-script word as the lexer does.
#[test]
fn source_word_rejects_a_mixed_script_name() {
    assert!(source_word("a\u{430}").is_none());
    assert!(matches!(source_word("\u{43f}\u{440}"), Some(SourceWord::Ident)));
}

/// Greek small mu mixes with any script, as Elixir allows because it folds `µ` into it.
#[test]
fn greek_small_mu_mixes_with_any_script() {
    assert!(lex_kinds("a\u{3bc}").is_ok());
    assert!(lex_kinds("\u{3bc}\u{65e5}").is_ok());
    assert!(lex_kinds("\u{3b1}\u{3bc}a").is_err());
}

fn string_bytes(src: &str) -> Vec<u8> {
    match lex_kinds(src).unwrap().remove(0) {
        Tok::Binary(bytes) => bytes,
        other => panic!("expected a binary, got {other:?}"),
    }
}

/// `\uHHHH` with exactly four hex digits is that code point, UTF-8 encoded.
#[test]
fn a_four_digit_unicode_escape_is_utf8_encoded() {
    assert_eq!(string_bytes(r#""\u00e9""#), "é".as_bytes());
    assert_eq!(string_bytes(r#""\u00E9""#), "é".as_bytes());
    assert_eq!(string_bytes(r#""\u0041""#), b"A");
}

/// `\u{H...}` with one to six hex digits is that code point, up to four bytes.
#[test]
fn a_braced_unicode_escape_is_utf8_encoded() {
    assert_eq!(string_bytes(r#""\u{e9}""#), "é".as_bytes());
    assert_eq!(string_bytes(r#""\u{1F600}""#), "😀".as_bytes());
    assert_eq!(string_bytes(r#""\u{000041}""#), b"A");
    assert_eq!(string_bytes(r#""\u{10FFFF}""#), "\u{10FFFF}".as_bytes());
    assert_eq!(string_bytes(r#""\u{0}""#), vec![0]);
}

/// Escapes and ordinary text interleave, and the last digit of a four-digit escape ends it.
#[test]
fn a_unicode_escape_sits_among_other_text() {
    assert_eq!(string_bytes(r#""a\u00e9b\u{42}\n""#), "aébB\n".as_bytes());
    assert_eq!(string_bytes(r#""\u00e9e""#), "ée".as_bytes());
}

/// A heredoc reads the same escapes as a string.
#[test]
fn a_heredoc_accepts_unicode_escapes() {
    assert_eq!(string_bytes("\"\"\"\n\\u00e9\\u{1F600}\n\"\"\"\n"), "é😀\n".as_bytes());
}

/// A quoted atom reads the same escapes as a string, so the two spellings name one atom.
#[test]
fn a_quoted_atom_accepts_unicode_escapes() {
    assert_eq!(
        lex_kinds(r#":"\u00e9""#).unwrap(),
        vec![Tok::Atom("é".to_string()), Tok::Eof]
    );
}

fn escape_error(src: &str) -> String {
    lex_kinds(src).unwrap_err().msg
}

const MALFORMED: &str = "invalid Unicode escape character, expected \\uHHHH or \\u{H*} where H is a hexadecimal digit";

/// A malformed `\u` escape is one error, whatever is wrong with it.
#[test]
fn a_malformed_unicode_escape_is_rejected() {
    for src in [
        r#""\u""#,
        r#""\u12""#,
        r#""\u12g4""#,
        r#""\u{}""#,
        r#""\u{ }""#,
        r#""\u{41 }""#,
        r#""\u{41""#,
        r#""\u{4g}""#,
        r#""\u{0000041}""#,
        r#""\u{-1}""#,
        r#""\u{41,42}""#,
    ] {
        assert_eq!(escape_error(src), MALFORMED, "{src}");
    }
}

/// A surrogate or a value above U+10FFFF is not a code point.
#[test]
fn a_unicode_escape_must_be_a_code_point() {
    assert_eq!(
        escape_error(r#""\ud800""#),
        "invalid or reserved Unicode code point \\u{d800}"
    );
    assert_eq!(
        escape_error(r#""\u{DFFF}""#),
        "invalid or reserved Unicode code point \\u{DFFF}"
    );
    assert_eq!(
        escape_error(r#""\u{110000}""#),
        "invalid or reserved Unicode code point \\u{110000}"
    );
}

/// A bad escape is underlined from its backslash to the end of what was read.
#[test]
fn a_bad_unicode_escape_underlines_the_escape() {
    let error = lex_kinds(r#""ab\u{110000}""#).unwrap_err();
    assert_eq!((error.span.start, error.span.end), (3, 13));
}

/// Code points that are legal but unassigned or non-characters are accepted, as in Elixir.
#[test]
fn a_non_character_code_point_is_accepted() {
    assert_eq!(string_bytes(r#""\uFFFF""#), "\u{FFFF}".as_bytes());
    assert_eq!(string_bytes(r#""\uD7FF""#), "\u{D7FF}".as_bytes());
    assert_eq!(string_bytes(r#""\uE000""#), "\u{E000}".as_bytes());
}
