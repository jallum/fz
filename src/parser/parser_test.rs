use super::*;
use crate::telemetry::Telemetry;

#[cfg(test)]
mod do_block_sugar_tests {
    use super::*;
    use crate::parser::lexer::Lexer;
    use Attribute::{Doc, Spec};
    use BinOp::{And, Or};

    fn parse_fn_body(src: &str, tel: &dyn Telemetry) -> Expr {
        let wrapped = format!("fn _t() do {} end", src);
        let toks = Lexer::with_source_name(&wrapped, "<test>").tokenize(tel).unwrap();
        let prog = Parser::new(toks).parse_program(tel).unwrap();
        match &*prog.items[0] {
            Item::Fn(d) => match &d.clauses[0].body.node {
                Expr::Block(xs) => xs[0].node.clone(),
                other => other.clone(),
            },
            _ => panic!(),
        }
    }

    fn parse_expr(src: &str, tel: &dyn Telemetry) -> Expr {
        let toks = Lexer::with_source_name(src, "<test>").tokenize(tel).unwrap();
        Parser::new(toks).parse_expr_eof().unwrap().node
    }

    // DROP: do-block sugar AST shape, pure parse structure
    #[test]
    fn trailing_do_block_appended_as_arg() {
        let e = parse_fn_body(
            r#"f("x") do
            1
            2
        end"#,
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::Call(callee, args) = e else {
            panic!("not a call")
        };
        assert!(matches!(callee.node, Expr::Var(ref n) if n == "f"));
        assert_eq!(args.len(), 2, "name + keyword list");
        assert!(matches!(args[0].node, Expr::Binary(_)));
        assert_keyword_list(&args[1], &[("do", "block")]);
    }

    // DROP: do-block keyword arg AST shape, pure parse structure
    #[test]
    fn comma_do_kw_appended_as_keyword_arg() {
        let e = parse_fn_body(r#"f("x"), do: 42"#, &crate::telemetry::ConfiguredTelemetry::new());
        let Expr::Call(_, args) = e else { panic!("not a call") };
        assert_eq!(args.len(), 2);
        assert_keyword_list(&args[1], &[("do", "int")]);
    }

    // DROP: keyword list desugars to atom-pair list, pure parse structure
    #[test]
    fn list_keyword_sugar_is_list_of_atom_pairs() {
        let e = parse_expr("[a: 1, b: 2]", &crate::telemetry::ConfiguredTelemetry::new());
        assert_keyword_list(&Spanned::dummy(e), &[("a", "int"), ("b", "int")]);
    }

    // DROP: keyword args collapse to single trailing list, pure parse structure
    #[test]
    fn call_keywords_are_single_trailing_list_arg() {
        let e = parse_expr("f(1, a: 2, b: 3)", &crate::telemetry::ConfiguredTelemetry::new());
        let Expr::Call(_, args) = e else { panic!("not a call") };
        assert_eq!(args.len(), 2);
        assert!(matches!(args[0].node, Expr::Int(1)));
        assert_keyword_list(&args[1], &[("a", "int"), ("b", "int")]);
    }

    // DROP: do-block merges with existing keyword list, pure parse structure
    #[test]
    fn trailing_do_merges_with_existing_keyword_arg() {
        let e = parse_expr(
            "f(1, timeout: 10) do 42 end",
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::Call(_, args) = e else { panic!("not a call") };
        assert_eq!(args.len(), 2);
        assert_keyword_list(&args[1], &[("timeout", "int"), ("do", "int")]);
    }

    // DROP: do-block vs explicit list non-merge boundary, pure parse structure
    #[test]
    fn trailing_do_does_not_merge_with_explicit_atom_pair_list() {
        let e = parse_expr(
            "f([{:timeout, 10}]) do 42 end",
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::Call(_, args) = e else { panic!("not a call") };
        assert_eq!(args.len(), 2);
        let Expr::List(items, None) = &args[0].node else {
            panic!("expected explicit list arg")
        };
        assert_eq!(items.len(), 1);
        assert_keyword_list(&args[1], &[("do", "int")]);
    }

    // DROP: keyword list pattern shape, pure parse structure
    #[test]
    fn list_keyword_sugar_works_in_patterns() {
        let toks = Lexer::with_source_name("fn opts([do: body, else: fallback]), do: body", "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let prog = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let Item::Fn(def) = &*prog.items[0] else {
            panic!("expected fn")
        };
        assert_keyword_pattern(&def.clauses[0].params[0], &[("do", "body"), ("else", "fallback")]);
    }

    // PICK: top-level macro call form with do-block body
    #[test]
    fn item_level_call_parses_as_macro_call() {
        let toks = Lexer::with_source_name(
            r#"
test("addition") do
  1 + 2
end
"#,
            "<test>",
        )
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
        let prog = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let mc = prog.items.iter().find_map(|it| match &**it {
            Item::MacroCall { name, args, .. } => Some((name.clone(), args.clone())),
            _ => None,
        });
        let (name, args) = mc.expect("expected an Item::MacroCall");
        assert_eq!(name, "test");
        assert_eq!(args.len(), 2, "name + keyword list");
        assert!(matches!(args[0].node, Expr::Binary(ref s) if s == b"addition"));
        match &args[1].node {
            Expr::List(_, None) => assert_keyword_list(&args[1], &[("do", "binop")]),
            other => panic!("unexpected body shape: {:?}", other),
        }
    }

    fn assert_keyword_list(arg: &Spanned<Expr>, expected: &[(&str, &str)]) {
        let Expr::List(items, None) = &arg.node else {
            panic!("expected keyword list, got {:?}", arg.node);
        };
        assert_eq!(items.len(), expected.len());
        for (item, (expected_key, expected_kind)) in items.iter().zip(expected.iter()) {
            let Expr::Tuple(pair) = &item.node else {
                panic!("expected keyword tuple, got {:?}", item.node);
            };
            assert_eq!(pair.len(), 2);
            assert!(matches!(&pair[0].node, Expr::Atom(key) if key == expected_key));
            match *expected_kind {
                "block" => assert!(matches!(pair[1].node, Expr::Block(_))),
                "binop" => assert!(matches!(pair[1].node, Expr::BinOp(_, _, _))),
                "int" => assert!(matches!(pair[1].node, Expr::Int(_))),
                other => panic!("unknown expected kind {}", other),
            }
        }
    }

    fn assert_keyword_pattern(arg: &Spanned<Pattern>, expected: &[(&str, &str)]) {
        let Pattern::List(items, None) = &arg.node else {
            panic!("expected keyword pattern list, got {:?}", arg.node);
        };
        assert_eq!(items.len(), expected.len());
        for (item, (expected_key, expected_var)) in items.iter().zip(expected.iter()) {
            let Pattern::Tuple(pair) = &item.node else {
                panic!("expected keyword pattern tuple, got {:?}", item.node);
            };
            assert_eq!(pair.len(), 2);
            assert!(matches!(&pair[0].node, Pattern::Atom(key) if key == expected_key));
            assert!(matches!(&pair[1].node, Pattern::Var(name) if name == expected_var));
        }
    }

    // PICK: macro call nested inside defmodule body
    #[test]
    fn item_level_call_inside_module() {
        let toks = Lexer::with_source_name(
            r#"
defmodule MyTest do
  test("addition") do
    1 + 2
  end
end
"#,
            "<test>",
        )
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
        let prog = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let m = prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Module(m) => Some(m),
                _ => None,
            })
            .unwrap();
        assert!(m.items.iter().any(|it| matches!(&**it, Item::MacroCall { .. })));
    }

    // PICK: protocol definition with @doc/@spec attributed callbacks
    #[test]
    fn parses_protocol_callbacks_with_specs() {
        let toks = Lexer::with_source_name(
            r#"
defprotocol Enumerable do
  @doc "Reduce values"
  @spec reduce(t, acc, reducer) :: acc
  fn reduce(enumerable, acc, reducer)
end
"#,
            "<test>",
        )
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
        let prog = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let Item::Protocol(protocol) = &*prog.items[0] else {
            panic!("expected protocol");
        };
        assert_eq!(protocol.name.dotted(), "Enumerable");
        assert_eq!(protocol.callbacks.len(), 1);
        assert_eq!(protocol.callbacks[0].name, "reduce");
        assert_eq!(protocol.callbacks[0].arity, 3);
        assert!(protocol.callbacks[0].attrs.iter().any(|attr| matches!(attr, Doc(_))));
        assert!(protocol.callbacks[0].attrs.iter().any(|attr| matches!(attr, Spec(_))));
    }

    // PICK: defimpl block with a concrete function body
    #[test]
    fn parses_protocol_impl_with_function_body() {
        let toks = Lexer::with_source_name(
            r#"
defimpl Enumerable, for: List do
  fn reduce(xs, acc, reducer), do: acc
end
"#,
            "<test>",
        )
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
        let prog = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let Item::ProtocolImpl(protocol_impl) = &*prog.items[0] else {
            panic!("expected protocol impl");
        };
        assert_eq!(protocol_impl.protocol.dotted(), "Enumerable");
        assert_eq!(protocol_impl.target.path.dotted(), "List");
        assert_eq!(protocol_impl.items.len(), 1);
        assert!(matches!(&*protocol_impl.items[0], Item::Fn(def) if def.name == "reduce"));
    }

    // PICK: protocol callbacks must not have bodies — language invariant
    #[test]
    fn protocol_callback_rejects_body() {
        let toks = Lexer::with_source_name(
            r#"
defprotocol Bad do
  fn reduce(xs), do: xs
end
"#,
            "<test>",
        )
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
        let err = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap_err();
        assert!(err.msg.contains("cannot have bodies"), "unexpected error: {:?}", err);
    }

    // PICK: defimpl must supply for: target — language invariant
    #[test]
    fn protocol_impl_requires_for_target() {
        let toks = Lexer::with_source_name("defimpl Enumerable, target: List do\nend\n", "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let err = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap_err();
        assert!(err.msg.contains("for:"), "unexpected error: {:?}", err);
    }

    // DROP: plain call arg count, pure parse structure
    #[test]
    fn plain_call_no_extra_arg() {
        let e = parse_fn_body("f(1, 2)", &crate::telemetry::ConfiguredTelemetry::new());
        let Expr::Call(_, args) = e else { panic!() };
        assert_eq!(args.len(), 2);
    }

    // DROP: newline continuation rule for match operator, pure parse structure
    #[test]
    fn newline_before_match_operator_continues_expression() {
        let e = parse_expr("x\n  =\n    41", &crate::telemetry::ConfiguredTelemetry::new());
        assert!(matches!(e, Expr::Match(_, _)));
    }

    // DROP: newline before `[` starts new statement, pure parse structure
    #[test]
    fn newline_before_list_starts_next_expression_not_index() {
        let wrapped = r#"
fn _t() do
  h
  []
end
"#;
        let toks = Lexer::with_source_name(wrapped, "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let prog = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let Item::Fn(def) = &*prog.items[0] else {
            panic!("expected fn")
        };
        let Expr::Block(exprs) = &def.clauses[0].body.node else {
            panic!("expected block")
        };
        assert_eq!(exprs.len(), 2);
        assert!(matches!(exprs[0].node, Expr::Var(ref name) if name == "h"));
        assert!(matches!(exprs[1].node, Expr::List(ref items, None) if items.is_empty()));
    }

    // PICK: same-name different-arity functions are distinct definitions
    #[test]
    fn same_name_different_arity_forms_distinct_fn_defs() {
        let toks = Lexer::with_source_name(
            r#"
fn spawn(fun), do: fun.()
fn spawn(fun, opts), do: fun.()
"#,
            "<test>",
        )
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
        let prog = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let arities: Vec<usize> = prog
            .items
            .iter()
            .filter_map(|item| match &**item {
                Item::Fn(def) if def.name == "spawn" => Some(def.clauses[0].params.len()),
                _ => None,
            })
            .collect();
        assert_eq!(arities, vec![1, 2]);
    }

    // PICK: `fnp` keyword marks function as private
    #[test]
    fn fnp_parses_as_private_function_def() {
        let toks = Lexer::with_source_name("fnp helper(x), do: x\n", "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let prog = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let Item::Fn(def) = &*prog.items[0] else {
            panic!("expected fn");
        };
        assert_eq!(def.name, "helper");
        assert!(def.is_private);
        assert!(!def.is_macro);
    }

    /// fz-rcp.1 — call-postfix `do … end` sugar must be suppressed in
    /// cond position; otherwise `if pred(h) do … end` parses the
    /// then-arm as a second arg to `pred`, leaving `else`/`end`
    /// floating.
    // PICK: if-cond call does not consume the then-arm as an argument
    #[test]
    fn cond_call_in_if_does_not_swallow_do_block() {
        let e = parse_fn_body(
            r#"if pred(h) do
                1
            else
                2
            end"#,
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::If(cond, _, els) = e else {
            panic!("expected If, got {:?}", e);
        };
        // cond must be `pred(h)` with exactly one arg, not `pred(h, then_block)`.
        let Expr::Call(_, args) = &cond.node else {
            panic!("expected cond to be a Call");
        };
        assert_eq!(args.len(), 1, "cond Call ate the then-arm as an arg");
        assert!(els.is_some(), "else branch lost");
    }

    // ──────────────────────────────────────────────────────────────
    // fz-5vj — `receive do … after … end` parser tests
    // ──────────────────────────────────────────────────────────────

    // PICK: receive with single clause and no after-timeout
    #[test]
    fn receive_single_clause_no_after_parses() {
        let e = parse_fn_body(
            r#"receive do
                msg -> msg
            end"#,
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::Receive { clauses, after } = e else {
            panic!("expected Receive, got {:?}", e);
        };
        assert_eq!(clauses.len(), 1);
        assert!(after.is_none());
        assert!(matches!(clauses[0].pattern.node, Pattern::Var(ref n) if n == "msg"));
        assert!(clauses[0].guard.is_none());
    }

    // PICK: receive dispatches on multiple message patterns
    #[test]
    fn receive_multi_clause_parses() {
        let e = parse_fn_body(
            r#"receive do
                {:get, k} -> 1
                {:put, k, v} -> 2
                :stop -> 3
            end"#,
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::Receive { clauses, after } = e else {
            panic!("expected Receive, got {:?}", e);
        };
        assert_eq!(clauses.len(), 3);
        assert!(after.is_none());
    }

    // PICK: receive clause carries a when-guard on the pattern
    #[test]
    fn receive_clause_with_guard_parses() {
        let e = parse_fn_body(
            r#"receive do
                n when n > 0 -> n
            end"#,
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::Receive { clauses, after } = e else {
            panic!("expected Receive");
        };
        assert!(after.is_none());
        assert!(clauses[0].guard.is_some());
    }

    // PICK: receive after-timeout clause with deadline and body
    #[test]
    fn receive_with_after_parses() {
        let e = parse_fn_body(
            r#"receive do
                msg -> msg
            after
                500 -> :timeout
            end"#,
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::Receive { clauses, after } = e else {
            panic!("expected Receive");
        };
        assert_eq!(clauses.len(), 1);
        let af = after.expect("after clause parsed");
        assert!(matches!(af.timeout.node, Expr::Int(500)));
        assert!(matches!(af.body.node, Expr::Atom(ref a) if a == "timeout"));
    }

    // PICK: receive after 0 is the non-blocking peek form
    #[test]
    fn receive_with_after_zero_parses() {
        // `after 0` is the peek form.
        let e = parse_fn_body(
            r#"receive do
                msg -> msg
            after
                0 -> nil
            end"#,
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::Receive { clauses: _, after } = e else {
            panic!("expected Receive");
        };
        let af = after.expect("after clause parsed");
        assert!(matches!(af.timeout.node, Expr::Int(0)));
    }

    // PICK: receive after :infinity timeout atom is preserved
    #[test]
    fn receive_with_after_infinity_parses() {
        let e = parse_fn_body(
            r#"receive do
                msg -> msg
            after
                :infinity -> :never
            end"#,
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::Receive { clauses: _, after } = e else {
            panic!("expected Receive");
        };
        let af = after.expect("after clause parsed");
        assert!(matches!(af.timeout.node, Expr::Atom(ref a) if a == "infinity"));
    }

    // PICK: pinned variable `^ref` in receive pattern
    #[test]
    fn receive_pinned_pattern_var_parses() {
        let e = parse_fn_body(
            r#"receive do
                {:reply, ^ref, v} -> v
            end"#,
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::Receive { clauses, .. } = e else {
            panic!("expected Receive");
        };
        let Pattern::Tuple(elems) = &clauses[0].pattern.node else {
            panic!("expected tuple pattern");
        };
        assert_eq!(elems.len(), 3);
        assert!(matches!(elems[0].node, Pattern::Atom(ref a) if a == "reply"));
        assert!(matches!(elems[1].node, Pattern::Pinned(ref n) if n == "ref"));
        assert!(matches!(elems[2].node, Pattern::Var(ref v) if v == "v"));
    }

    // PICK: `receive()` call form is rejected — language invariant
    #[test]
    fn bare_receive_call_is_rejected() {
        let wrapped = "fn _t() do receive() end";
        let toks = Lexer::with_source_name(wrapped, "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let err = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap_err();
        assert!(
            err.msg.contains("plain `receive()` has been removed"),
            "unexpected parse error: {:?}",
            err
        );
    }

    /// case scrutinee, cond test, with binding source, and when-guard
    /// are all cond-position and must suppress the sugar.
    // fz-swt.5 — explicit `&name/arity` fn references.

    // PICK: `&name/arity` function reference expression
    #[test]
    fn fn_ref_bare_name_parses() {
        let e = parse_fn_body("&foo/1", &crate::telemetry::ConfiguredTelemetry::new());
        match e {
            Expr::FnRef { name, arity } => {
                assert_eq!(name, "foo");
                assert_eq!(arity, 1);
            }
            other => panic!("expected FnRef, got {:?}", other),
        }
    }

    // PICK: `&name/0` zero-arity function reference
    #[test]
    fn fn_ref_zero_arity_parses() {
        let e = parse_fn_body("&do_it/0", &crate::telemetry::ConfiguredTelemetry::new());
        match e {
            Expr::FnRef { name, arity } => {
                assert_eq!(name, "do_it");
                assert_eq!(arity, 0);
            }
            other => panic!("expected FnRef, got {:?}", other),
        }
    }

    // PICK: `&Mod.fun/2` module-qualified function reference
    #[test]
    fn fn_ref_module_qualified_parses() {
        // `&Mod.fun/2` captures the full dotted path as the name.
        let e = parse_fn_body("&Mod.fun/2", &crate::telemetry::ConfiguredTelemetry::new());
        match e {
            Expr::FnRef { name, arity } => {
                assert_eq!(name, "Mod.fun");
                assert_eq!(arity, 2);
            }
            other => panic!("expected FnRef, got {:?}", other),
        }
    }

    // PICK: `&+/2` operator function references for higher-order use
    #[test]
    fn fn_ref_bare_arithmetic_operators_parse() {
        for (src, expected_name) in [
            ("&+/2", "+"),
            ("&-/2", "-"),
            ("&*/2", "*"),
            ("&//2", "/"),
            ("&%/2", "%"),
        ] {
            match parse_fn_body(src, &crate::telemetry::ConfiguredTelemetry::new()) {
                Expr::FnRef { name, arity } => {
                    assert_eq!(name, expected_name);
                    assert_eq!(arity, 2);
                }
                other => panic!("expected FnRef for {src}, got {:?}", other),
            }
        }
    }

    // PICK: `&Kernel.+/2` module-qualified operator function references
    #[test]
    fn fn_ref_module_qualified_arithmetic_operators_parse() {
        for (src, expected_name) in [
            ("&Kernel.+/2", "Kernel.+"),
            ("&Kernel.-/2", "Kernel.-"),
            ("&Kernel.*/2", "Kernel.*"),
            ("&Kernel.//2", "Kernel./"),
            ("&Kernel.%/2", "Kernel.%"),
        ] {
            match parse_fn_body(src, &crate::telemetry::ConfiguredTelemetry::new()) {
                Expr::FnRef { name, arity } => {
                    assert_eq!(name, expected_name);
                    assert_eq!(arity, 2);
                }
                other => panic!("expected FnRef for {src}, got {:?}", other),
            }
        }
    }

    // PICK: `&A.B.run/3` deep module-qualified function reference
    #[test]
    fn fn_ref_nested_module_qualified_parses() {
        let e = parse_fn_body("&A.B.run/3", &crate::telemetry::ConfiguredTelemetry::new());
        match e {
            Expr::FnRef { name, arity } => {
                assert_eq!(name, "A.B.run");
                assert_eq!(arity, 3);
            }
            other => panic!("expected FnRef, got {:?}", other),
        }
    }

    // PICK: function reference passed as argument to a call
    #[test]
    fn fn_ref_as_call_arg_parses() {
        // Ensures &name/arity composes naturally inside argument lists.
        let e = parse_fn_body("apply(&foo/1, 7)", &crate::telemetry::ConfiguredTelemetry::new());
        let Expr::Call(_, args) = e else { panic!() };
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0].node, Expr::FnRef { name, arity }
            if name == "foo" && *arity == 1));
    }

    // PICK: `and`/`or` keyword boolean operators over C-style `&&`/`||`
    #[test]
    fn and_or_keywords_parse_as_boolean_binops() {
        // fz uses Elixir's `and`/`or`, not C-style `&&`/`||`.
        let Expr::BinOp(op, _, _) = parse_fn_body("true and false", &crate::telemetry::ConfiguredTelemetry::new())
        else {
            panic!()
        };
        assert!(matches!(op, And));
        let Expr::BinOp(op, _, _) = parse_fn_body("true or false", &crate::telemetry::ConfiguredTelemetry::new())
        else {
            panic!()
        };
        assert!(matches!(op, Or));
    }

    // PICK: `&&`/`||`/`!` are removed — language-level migration invariant
    #[test]
    fn c_style_boolean_operators_are_lex_errors() {
        // `&&`/`||`/`!` were removed in favour of `and`/`or`/`not`; the lexer
        // rejects them with a migration hint. Bare `&` (fn-ref) still lexes.
        let tel = crate::telemetry::ConfiguredTelemetry::new();
        for src in ["true && false", "true || false", "!true"] {
            let err = Lexer::with_source_name(src, "<test>")
                .tokenize(&tel)
                .expect_err("should reject C-style op");
            assert!(
                err.msg.contains("use `and`") || err.msg.contains("use `or`") || err.msg.contains("use `not`"),
                "msg={}",
                err.msg
            );
        }
        assert!(
            Lexer::with_source_name("apply(&foo/1, 7)", "<test>")
                .tokenize(&tel)
                .is_ok()
        );
    }

    // PICK: case when-guard call does not consume the clause body
    #[test]
    fn cond_call_in_case_when_guard_does_not_swallow_do_block() {
        // when-guard pred(h) followed by `->` body that itself contains
        // a do-block. The guard expr must stop at the body's `->`.
        let e = parse_fn_body(
            r#"case x do
                _ when pred(h) -> f() do
                    1
                end
            end"#,
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        let Expr::Case(_, clauses) = e else {
            panic!("expected Case");
        };
        let guard = clauses[0].guard.as_ref().expect("guard parsed");
        let Expr::Call(_, args) = &guard.node else {
            panic!("expected guard to be a Call");
        };
        assert_eq!(args.len(), 1, "guard Call ate the body do-block");
    }
}

#[cfg(test)]
mod extern_parse_tests {
    use super::*;
    use crate::parser::lexer::Lexer;

    fn parse_extern(src: &str) -> FnDef {
        let toks = Lexer::with_source_name(src, "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let prog = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        match &*prog.items[0] {
            Item::Fn(d) => d.clone(),
            other => panic!("expected Item::Fn, got {:?}", other),
        }
    }

    // DROP: extern FFI declaration AST shape, no compiler2 analogue yet
    #[test]
    fn extern_fn_no_params() {
        let d = parse_extern("extern \"C\" fn fz_halt() :: never\n");
        assert_eq!(d.name, "fz_halt");
        assert_eq!(d.extern_abi, Some("C".into()));
        assert_eq!(d.extern_param_tokens.len(), 0);
        assert!(d.clauses.is_empty());
    }

    // DROP: extern FFI param count, no compiler2 analogue yet
    #[test]
    fn extern_fn_one_param() {
        let d = parse_extern("extern \"C\" fn fz_print(any) :: unit\n");
        assert_eq!(d.extern_param_tokens.len(), 1);
    }

    // DROP: extern FFI two-param and return tokens, no compiler2 analogue yet
    #[test]
    fn extern_fn_two_params() {
        let d = parse_extern("extern \"C\" fn fz_pair(any, any) :: unit\n");
        assert_eq!(d.extern_param_tokens.len(), 2);
        assert!(!d.variadic);
        assert!(!d.extern_ret_tokens.0.is_empty());
    }

    // DROP: extern FFI variadic `...` marker, no compiler2 analogue yet
    #[test]
    fn extern_fn_variadic_marker() {
        let d = parse_extern("extern \"C\" fn libc::open(path :: cstring, flags :: integer, ...) :: integer\n");
        assert_eq!(d.name, "libc::open");
        assert_eq!(d.extern_param_tokens.len(), 2);
        assert_eq!(d.extern_param_tokens[0].0.len(), 1);
        assert_eq!(d.extern_param_tokens[1].0.len(), 1);
        assert!(d.variadic);
    }

    // DROP: extern FFI complex param shapes and type constraints, no compiler2 analogue yet
    #[test]
    fn extern_fn_preserves_param_shapes_and_constraints() {
        let d = parse_extern(
            "extern \"C\" fn fz_make_resource(t, dtor :: (t) -> nil) :: resource(t) when t: integer | cpointer\n",
        );
        assert_eq!(d.extern_param_tokens.len(), 2);
        assert_eq!(d.extern_constraints.len(), 1);
        assert!(!d.extern_ret_tokens.0.is_empty());
        assert!(
            d.extern_param_tokens[1]
                .0
                .iter()
                .any(|token| matches!(token.tok, Tok::Arrow)),
            "destructor param should preserve the arrow type body",
        );
    }

    // DROP: extern FFI rejects non-final `...`, no compiler2 analogue yet
    #[test]
    fn extern_fn_variadic_marker_must_be_final() {
        let toks = Lexer::with_source_name("extern \"C\" fn bad(integer, ..., integer) :: integer\n", "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let err = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap_err();
        assert!(err.msg.contains("must be the final parameter"), "{err:?}");
    }

    // DROP: type ascription on call arg preserved in AST, pure parse structure
    #[test]
    fn call_arg_ascription_is_preserved() {
        let toks = Lexer::with_source_name("fn main(), do: libc::open(path, flags, mode :: integer)\n", "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let prog = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let Item::Fn(d) = &*prog.items[0] else {
            panic!("expected fn");
        };
        let Expr::Call(_, args) = &d.clauses[0].body.node else {
            panic!("expected call");
        };
        assert_eq!(args.len(), 3);
        let Expr::Ascribe(inner, ty) = &args[2].node else {
            panic!("expected ascribed call arg");
        };
        assert!(matches!(inner.node, Expr::Var(ref name) if name == "mode"));
        assert!(matches!(ty.0.first().map(|t| &t.tok), Some(Tok::Ident(name)) if name == "integer"));
    }
}

#[cfg(test)]
mod telemetry_tests {
    use super::*;
    use crate::parser::lexer::Lexer;

    // DROP: parser telemetry span and item count, infrastructure
    #[test]
    fn telemetry_emits_pass_span_and_item_count() {
        use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind, Value};
        use EventKind::{SpanStart, SpanStop};
        use Value::U64;

        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());

        let toks = Lexer::with_source_name("fn id(x), do: x\nfn main(), do: id(1)\n", "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .expect("lex");
        let prog = Parser::new(toks).parse_program(&tel).expect("parse");

        assert_eq!(cap.count_by_kind(SpanStart), 1);
        assert_eq!(cap.count_by_kind(SpanStop), 1);
        assert_eq!(cap.count(PARSE_PASS_NAME), 2);

        let built = cap.last(ITEMS_BUILT_NAME).unwrap();
        match built.measurements.get("count") {
            Some(U64(n)) => assert_eq!(*n as usize, prog.items.len()),
            other => panic!("expected U64 count, got {:?}", other),
        }
    }

    // DROP: parser telemetry span_id inheritance, infrastructure
    #[test]
    fn telemetry_user_event_inherits_span_id() {
        use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind};
        use EventKind::SpanStart;

        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());

        let toks = Lexer::with_source_name("fn main(), do: :ok", "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .expect("lex");
        let _ = Parser::new(toks).parse_program(&tel).expect("parse");

        let start = cap
            .find(PARSE_PASS_NAME)
            .into_iter()
            .find(|e| e.kind == SpanStart)
            .unwrap();
        let built = cap.last(ITEMS_BUILT_NAME).unwrap();
        assert_eq!(start.span_id, built.span_id);
        assert!(start.span_id > 0);
    }

    // DROP: null telemetry no-op, pure infrastructure
    #[test]
    fn null_telemetry_is_a_silent_no_op() {
        let toks = Lexer::with_source_name("fn main(), do: :ok", "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .expect("lex");
        let prog = Parser::new(toks)
            .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
            .expect("parse");
        assert_eq!(prog.items.len(), 1);
    }
}

#[cfg(test)]
mod elixir_operator_precedence_tests {
    use super::*;
    use crate::parser::lexer::Lexer;
    use BinOp::{Add, BinConcat, Eq, In, ListConcat, ListSubtract, Mul, NotIn, Pipe, Range, RangeStep};
    use UnOp::{Neg, Not};

    fn parse(src: &str, tel: &dyn Telemetry) -> Expr {
        let toks = Lexer::with_source_name(src, "<test>").tokenize(tel).unwrap();
        Parser::new(toks).parse_expr_eof().unwrap().node
    }

    /// Parse `src` and destructure its top-level binary operation, returning
    /// owned operand clones so the result outlives the parsed tree.
    fn binop(src: &str, tel: &dyn Telemetry) -> (BinOp, Expr, Expr) {
        match parse(src, tel) {
            Expr::BinOp(op, a, b) => (op, a.node, b.node),
            other => panic!("expected BinOp, got {:?}", other),
        }
    }

    // PICK: `++`, `--`, `<>`, `..`, `in`, `not in` map to correct BinOps
    #[test]
    fn new_operators_parse_to_their_binops() {
        assert!(matches!(
            parse("a ++ b", &crate::telemetry::ConfiguredTelemetry::new()),
            Expr::BinOp(ListConcat, _, _)
        ));
        assert!(matches!(
            parse("a -- b", &crate::telemetry::ConfiguredTelemetry::new()),
            Expr::BinOp(ListSubtract, _, _)
        ));
        assert!(matches!(
            parse("a <> b", &crate::telemetry::ConfiguredTelemetry::new()),
            Expr::BinOp(BinConcat, _, _)
        ));
        assert!(matches!(
            parse("a .. b", &crate::telemetry::ConfiguredTelemetry::new()),
            Expr::BinOp(Range, _, _)
        ));
        assert!(matches!(
            parse("a in b", &crate::telemetry::ConfiguredTelemetry::new()),
            Expr::BinOp(In, _, _)
        ));
        assert!(matches!(
            parse("a not in b", &crate::telemetry::ConfiguredTelemetry::new()),
            Expr::BinOp(NotIn, _, _)
        ));
    }

    // PICK: `++` list concat is right-associative
    #[test]
    fn concat_is_right_associative() {
        // a ++ b ++ c  =>  a ++ (b ++ c)
        let (op, _a, rhs) = binop("a ++ b ++ c", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(op, ListConcat);
        assert!(
            matches!(rhs, Expr::BinOp(ListConcat, _, _)),
            "++ must be right-associative"
        );
    }

    // PICK: arithmetic binds tighter than list concat
    #[test]
    fn arithmetic_binds_tighter_than_concat() {
        // a ++ b + c  =>  a ++ (b + c)
        let (op, _a, rhs) = binop("a ++ b + c", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(op, ListConcat);
        assert!(matches!(rhs, Expr::BinOp(Add, _, _)));
    }

    // PICK: `1..10//2` stepped range precedence — range then step
    #[test]
    fn stepped_range_groups_as_range_then_step() {
        // 1..10//2  =>  (1..10) // 2
        let (op, lhs, _step) = binop("1..10//2", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(op, RangeStep);
        assert!(matches!(lhs, Expr::BinOp(Range, _, _)));
    }

    // PICK: unary negation binds tighter than multiplication
    #[test]
    fn unary_binds_tighter_than_multiplication() {
        // -a * b  =>  (-a) * b
        let (op, lhs, _b) = binop("-a * b", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(op, Mul);
        assert!(matches!(lhs, Expr::UnOp(Neg, _)));
    }

    // PICK: `not x` prefix keyword parses as UnOp::Not
    #[test]
    fn prefix_not_parses_as_unop_not() {
        assert!(matches!(
            parse("not x", &crate::telemetry::ConfiguredTelemetry::new()),
            Expr::UnOp(Not, _)
        ));
    }

    // PICK: pipe `|>` binds tighter than equality comparison
    #[test]
    fn pipe_binds_tighter_than_comparison() {
        // a |> f() == b  =>  (a |> f()) == b
        let (op, lhs, _b) = binop("a |> f() == b", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(op, Eq);
        assert!(matches!(lhs, Expr::BinOp(Pipe, _, _)));
    }

    // PICK: `in` membership binds looser than arithmetic
    #[test]
    fn membership_is_looser_than_arithmetic() {
        // 1 + 2 in xs  =>  (1 + 2) in xs
        let (op, lhs, _b) = binop("1 + 2 in xs", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(op, In);
        assert!(matches!(lhs, Expr::BinOp(Add, _, _)));
    }
}

#[cfg(test)]
mod no_parens_call_tests {
    use super::*;
    use crate::parser::lexer::Lexer;
    use BinOp::{Add, Sub};
    use UnOp::Neg;

    fn parse(src: &str, tel: &dyn Telemetry) -> Expr {
        let toks = Lexer::with_source_name(src, "<test>").tokenize(tel).unwrap();
        Parser::new(toks).parse_expr_eof().unwrap().node
    }

    /// Parse `src` and destructure a top-level call into (callee, owned args).
    fn call(src: &str, tel: &dyn Telemetry) -> (Expr, Vec<Expr>) {
        match parse(src, tel) {
            Expr::Call(callee, args) => (callee.node, args.into_iter().map(|a| a.node).collect()),
            other => panic!("expected Call, got {:?}", other),
        }
    }

    fn var(e: &Expr) -> &str {
        match e {
            Expr::Var(n) => n,
            other => panic!("expected Var, got {:?}", other),
        }
    }

    // DROP: no-parens call single argument, pure parse structure
    #[test]
    fn single_arg() {
        let (c, args) = call("foo a", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(var(&c), "foo");
        assert_eq!(args.len(), 1);
        assert_eq!(var(&args[0]), "a");
    }

    // DROP: no-parens call multiple arguments, pure parse structure
    #[test]
    fn many_args() {
        let (c, args) = call("foo a, b, c", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(var(&c), "foo");
        assert_eq!(args.len(), 3);
    }

    // DROP: no-parens call arg is a full expression, pure parse structure
    #[test]
    fn arg_is_a_full_expression() {
        // foo a + b  =>  foo(a + b)
        let (_c, args) = call("foo a + b", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0], Expr::BinOp(Add, _, _)));
    }

    // DROP: nested no-parens calls grab greedy argument span, pure parse structure
    #[test]
    fn nested_call_grabs_all_args() {
        // f g a, b  =>  f(g(a, b))
        let (c, args) = call("f g a, b", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(var(&c), "f");
        assert_eq!(args.len(), 1, "outer call takes one arg");
        let Expr::Call(inner, inner_args) = &args[0] else {
            panic!("inner not a call: {:?}", args[0])
        };
        assert_eq!(var(&inner.node), "g");
        assert_eq!(inner_args.len(), 2, "inner call grabbed both args");
    }

    // DROP: no-parens outer arg then nested call, pure parse structure
    #[test]
    fn arg_then_nested_call() {
        // f a, g b  =>  f(a, g(b))
        let (c, args) = call("f a, g b", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(var(&c), "f");
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[1], Expr::Call(_, a) if a.len() == 1));
    }

    // DROP: no-parens call in operand position inside binop, pure parse structure
    #[test]
    fn recognized_in_operand_position() {
        // 1 + foo a  =>  1 + foo(a)
        let Expr::BinOp(Add, _l, r) = parse("1 + foo a", &crate::telemetry::ConfiguredTelemetry::new()) else {
            panic!("not an addition")
        };
        assert!(matches!(&r.node, Expr::Call(c, a)
                if matches!(&c.node, Expr::Var(n) if n == "foo") && a.len() == 1));
    }

    // DROP: spacing disambiguates unary vs binary in no-parens call, pure parse structure
    #[test]
    fn dual_op_spacing_selects_unary_argument() {
        // foo -1  =>  foo(-1)  (unary, because space before `-`, none after)
        let (c, args) = call("foo -1", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(var(&c), "foo");
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0], Expr::UnOp(Neg, _)));
        // foo - 1  =>  binary subtraction, not a call
        assert!(matches!(
            parse("foo - 1", &crate::telemetry::ConfiguredTelemetry::new()),
            Expr::BinOp(Sub, _, _)
        ));
    }

    // DROP: module-qualified no-parens call head shape, pure parse structure
    #[test]
    fn module_qualified_head() {
        // Enum.map xs, f  =>  (Enum.map)(xs, f)
        let (c, args) = call("Enum.map xs, f", &crate::telemetry::ConfiguredTelemetry::new());
        assert!(matches!(c, Expr::Index(_, _)), "head is qualified: {:?}", c);
        assert_eq!(args.len(), 2);
    }

    // DROP: comma inside container limits no-parens call arg span, pure parse structure
    #[test]
    fn container_keeps_its_comma() {
        // [foo a, b]  =>  [foo(a), b]: the comma belongs to the list, so the
        // no-parens call inside a container takes a single argument.
        let Expr::List(items, None) = parse("[foo a, b]", &crate::telemetry::ConfiguredTelemetry::new()) else {
            panic!("not a list")
        };
        assert_eq!(items.len(), 2, "comma belongs to the list");
        assert!(matches!(&items[0].node, Expr::Call(c, a)
                if matches!(&c.node, Expr::Var(n) if n == "foo") && a.len() == 1));
        assert_eq!(var(&items[1].node), "b");
    }

    // DROP: bare variable without args is not a call, pure parse structure
    #[test]
    fn bare_var_is_not_a_call() {
        assert!(matches!(
            parse("foo", &crate::telemetry::ConfiguredTelemetry::new()),
            Expr::Var(_)
        ));
        assert!(matches!(
            parse("foo + 1", &crate::telemetry::ConfiguredTelemetry::new()),
            Expr::BinOp(Add, _, _)
        ));
    }

    // DROP: parenthesized call unaffected by no-parens rules, pure parse structure
    #[test]
    fn paren_call_unaffected() {
        let (c, args) = call("foo(a, b)", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(var(&c), "foo");
        assert_eq!(args.len(), 2);
    }

    /// A keyword list is `Expr::List` of `{key_atom, value}` tuples. Returns
    /// the atom keys in order.
    fn kw_keys(e: &Expr) -> Vec<String> {
        let Expr::List(entries, None) = e else {
            panic!("expected keyword list, got {:?}", e);
        };
        entries
            .iter()
            .map(|entry| match &entry.node {
                Expr::Tuple(pair) => match &pair[0].node {
                    Expr::Atom(k) => k.clone(),
                    other => panic!("key not an atom: {:?}", other),
                },
                other => panic!("entry not a tuple: {:?}", other),
            })
            .collect()
    }

    // DROP: trailing keyword in no-parens call becomes one list arg, pure parse structure
    #[test]
    fn trailing_keyword_collapses_into_one_list() {
        // foo a, b: 1  =>  foo(a, [b: 1])
        let (c, args) = call("foo a, b: 1", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(var(&c), "foo");
        assert_eq!(args.len(), 2);
        assert_eq!(var(&args[0]), "a");
        assert_eq!(kw_keys(&args[1]), vec!["b"]);
    }

    // DROP: multiple trailing keywords stay in one list arg, pure parse structure
    #[test]
    fn many_trailing_keywords_stay_in_one_list() {
        // foo a, b: 1, c: 2  =>  foo(a, [b: 1, c: 2])
        let (_c, args) = call("foo a, b: 1, c: 2", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(args.len(), 2, "the keywords are one trailing arg");
        assert_eq!(kw_keys(&args[1]), vec!["b", "c"]);
    }

    // DROP: leading keyword in no-parens call is a lone list arg, pure parse structure
    #[test]
    fn leading_keyword_is_a_lone_list() {
        // foo b: 1  =>  foo([b: 1])
        let (c, args) = call("foo b: 1", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(var(&c), "foo");
        assert_eq!(args.len(), 1);
        assert_eq!(kw_keys(&args[0]), vec!["b"]);
    }

    // DROP: nested no-parens call captures trailing keywords, pure parse structure
    #[test]
    fn nested_call_grabs_trailing_keywords() {
        // f g a, b: 1  =>  f(g(a, [b: 1]))
        let (c, args) = call("f g a, b: 1", &crate::telemetry::ConfiguredTelemetry::new());
        assert_eq!(var(&c), "f");
        assert_eq!(args.len(), 1);
        let Expr::Call(_inner, inner_args) = &args[0] else {
            panic!("inner not a call: {:?}", args[0])
        };
        assert_eq!(inner_args.len(), 2);
        assert_eq!(kw_keys(&inner_args[1].node), vec!["b"]);
    }
}

/// A no-parens call used as a keyword value, with another keyword after it, is
/// ambiguous — fz keeps the trailing keyword in the outer list where Elixir
/// would fold it into the inner call. The parser flags it with a telemetry
/// warning so the divergence is observable. These tests watch that event.
#[cfg(test)]
mod no_parens_keyword_ambiguity_tests {
    use super::*;
    use crate::parser::lexer::Lexer;
    use crate::telemetry::bus::ConfiguredTelemetry;
    use crate::telemetry::capture::Capture;

    const WARNING: &[&str] = &["fz", "diag", "warning"];

    /// Parse `body` as the lone statement of a function, with a capture sink
    /// attached, and return how many ambiguity warnings the parser emitted.
    fn warnings_for(body: &str) -> usize {
        let src = format!("fn _t() do\n  {}\nend\n", body);
        let toks = Lexer::with_source_name(&src, "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        let capture = Capture::new();
        let tel = ConfiguredTelemetry::new();
        tel.attach(&["fz", "diag"], capture.handler());
        Parser::new(toks).parse_program(&tel).expect("parse");
        capture.count(WARNING)
    }

    // DROP: ambiguous no-parens keyword value emits diagnostic warning, infrastructure
    #[test]
    fn no_parens_value_before_keyword_warns() {
        // foo a, b: bar x, c: 2 — `bar x` is a no-parens call, `c: 2` follows.
        assert_eq!(warnings_for("foo a, b: bar x, c: 2"), 1);
    }

    // DROP: parenthesized keyword value emits no warning, infrastructure
    #[test]
    fn parenthesized_value_is_unambiguous() {
        // bar(x) has explicit parens — no ambiguity, no warning.
        assert_eq!(warnings_for("foo a, b: bar(x), c: 2"), 0);
    }

    // DROP: no trailing keyword means no ambiguity warning, infrastructure
    #[test]
    fn no_trailing_keyword_is_unambiguous() {
        // bar x is the last entry; nothing could bind past it.
        assert_eq!(warnings_for("foo a, b: bar x"), 0);
    }

    // DROP: literal keyword value emits no ambiguity warning, infrastructure
    #[test]
    fn literal_value_before_keyword_does_not_warn() {
        // foo a, b: 1, c: 2 — the value is a literal, not a no-parens call.
        assert_eq!(warnings_for("foo a, b: 1, c: 2"), 0);
    }
}

/// fz-g58.2.5 — anonymous `fn … end` parses to a clause list. A single
/// unguarded clause is the directly-runnable shape; multi-clause and guarded
/// forms parse here but defer execution to the Arc 3 desugar.
mod lambda_tests {
    use super::*;
    use crate::ast::lambda_direct_clause;
    use crate::parser::lexer::Lexer;

    fn parse(src: &str, tel: &dyn Telemetry) -> Program {
        let toks = Lexer::with_source_name(src, "<test>").tokenize(tel).unwrap();
        Parser::new(toks).parse_program(tel).unwrap()
    }

    /// Parse the first fn's single-expression body (the lambda under test).
    fn body(src: &str, tel: &dyn Telemetry) -> Expr {
        let prog = parse(src, tel);
        match &*prog.items[0] {
            Item::Fn(d) => match &d.clauses[0].body.node {
                Expr::Block(xs) => xs[0].node.clone(),
                other => other.clone(),
            },
            _ => panic!("expected fn item"),
        }
    }

    // PICK: single-clause unguarded lambda is directly callable
    #[test]
    fn single_clause_fn_is_one_clause() {
        let Expr::Lambda(clauses) = body(
            "fn _t() do\n  fn x -> x + 1 end\nend\n",
            &crate::telemetry::ConfiguredTelemetry::new(),
        ) else {
            panic!("expected lambda");
        };
        assert_eq!(clauses.len(), 1);
        assert!(clauses[0].guard.is_none());
        assert_eq!(clauses[0].params.len(), 1);
        // The directly-runnable shape: one clause, no guard.
        assert!(lambda_direct_clause(&clauses).is_some());
    }

    // DROP: parenthesized lambda params, pure parse structure
    #[test]
    fn parenthesized_params_parse() {
        let Expr::Lambda(clauses) = body(
            "fn _t() do\n  fn (x, y) -> x + y end\nend\n",
            &crate::telemetry::ConfiguredTelemetry::new(),
        ) else {
            panic!("expected lambda");
        };
        assert_eq!(clauses.len(), 1);
        assert_eq!(clauses[0].params.len(), 2);
    }

    // PICK: multi-clause lambda collects all clauses and is not directly callable
    #[test]
    fn multi_clause_fn_collects_every_clause() {
        let Expr::Lambda(clauses) = body(
            "fn _t() do\n  fn 0 -> :zero\n     n -> n end\nend\n",
            &crate::telemetry::ConfiguredTelemetry::new(),
        ) else {
            panic!("expected lambda");
        };
        assert_eq!(clauses.len(), 2);
        // Multi-clause is not directly runnable; it awaits the Arc 3 desugar.
        assert!(lambda_direct_clause(&clauses).is_none());
    }

    // PICK: guarded lambda clause carries the when-guard, not directly callable
    #[test]
    fn guard_is_captured_on_the_clause() {
        let Expr::Lambda(clauses) = body(
            "fn _t() do\n  fn x when x > 0 -> x\n     _ -> 0 end\nend\n",
            &crate::telemetry::ConfiguredTelemetry::new(),
        ) else {
            panic!("expected lambda");
        };
        assert_eq!(clauses.len(), 2);
        assert!(clauses[0].guard.is_some());
        // A guard makes even a single clause non-direct.
        assert!(lambda_direct_clause(&clauses).is_none());
    }

    // PICK: single guarded clause is not directly callable — needs desugar
    #[test]
    fn single_guarded_clause_is_not_direct() {
        let Expr::Lambda(clauses) = body(
            "fn _t() do\n  fn x when x > 0 -> x end\nend\n",
            &crate::telemetry::ConfiguredTelemetry::new(),
        ) else {
            panic!("expected lambda");
        };
        assert_eq!(clauses.len(), 1);
        assert!(clauses[0].guard.is_some());
        assert!(lambda_direct_clause(&clauses).is_none());
    }

    // DROP: lambda without `end` is a parse error, parser error recovery
    #[test]
    fn missing_end_is_a_parse_error() {
        // Without `end`, the lambda swallows the enclosing `end`; the fn item
        // never closes, so parsing fails.
        let toks = Lexer::with_source_name("fn _t() do\n  fn x -> x + 1\nend\n", "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        assert!(
            Parser::new(toks)
                .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
                .is_err()
        );
    }

    // DROP: lambda in do-shorthand body must have its own `end`, parse boundary
    #[test]
    fn do_shorthand_lambda_body_needs_end_before_next_item() {
        // `fn make(), do: fn x -> x end` is the lambda as a `do:` body. The
        // lambda's own `end` closes it; the following item parses cleanly.
        let prog = parse(
            "fn make(), do: fn x -> x + 1 end\nfn main(), do: make()\n",
            &crate::telemetry::ConfiguredTelemetry::new(),
        );
        assert_eq!(prog.items.len(), 2);
        let Item::Fn(d) = &*prog.items[0] else {
            panic!("expected fn item");
        };
        let Expr::Lambda(clauses) = &d.clauses[0].body.node else {
            panic!("expected lambda body");
        };
        assert_eq!(clauses.len(), 1, "lambda must not absorb the next item");
    }

    // DROP: lambda in do-shorthand without `end` is a parse error, parser error recovery
    #[test]
    fn do_shorthand_lambda_without_end_is_a_parse_error() {
        // Drop the `end`: the lambda runs past the newline into `fn main`,
        // which is not a valid clause, so the program fails to parse.
        let toks = Lexer::with_source_name("fn make(), do: fn x -> x + 1\nfn main(), do: make()\n", "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        assert!(
            Parser::new(toks)
                .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
                .is_err()
        );
    }
}

/// fz-g58.2.6 — `&` capture forms. Three shapes disambiguated by the token
/// after `&`: placeholder `&N`, capture expression `&(...)`, and the existing
/// function reference `&name/arity`. The first two parse to `CaptureArg` /
/// `Capture` and desugar to a `Lambda` in fz-g58.15 (Arc 3); the reference
/// form keeps producing `FnRef`.
mod capture_tests {
    use super::*;
    use crate::parser::lexer::Lexer;
    use BinOp::Add;

    fn expr(src: &str) -> Expr {
        let toks = Lexer::with_source_name(src, "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap();
        Parser::new(toks).parse_expr_eof().unwrap().node
    }

    // PICK: `&1`, `&3` positional placeholders parse as CaptureArg
    #[test]
    fn placeholder_parses_to_capture_arg() {
        assert!(matches!(expr("&1"), Expr::CaptureArg(1)));
        assert!(matches!(expr("&3"), Expr::CaptureArg(3)));
    }

    // PICK: `&(expr)` capture wraps body expression with placeholder
    #[test]
    fn capture_expr_wraps_its_body() {
        // &(&1 + 1) => Capture(BinOp(Add, CaptureArg(1), Int(1)))
        let Expr::Capture(body) = expr("&(&1 + 1)") else {
            panic!("expected capture");
        };
        let Expr::BinOp(Add, lhs, rhs) = &body.node else {
            panic!("expected binop body, got {:?}", body.node);
        };
        assert!(matches!(lhs.node, Expr::CaptureArg(1)));
        assert!(matches!(rhs.node, Expr::Int(1)));
    }

    // PICK: capture expression with multiple positional placeholders
    #[test]
    fn capture_expr_holds_multiple_placeholders() {
        let Expr::Capture(body) = expr("&(&1 + &2)") else {
            panic!("expected capture");
        };
        let Expr::BinOp(Add, lhs, rhs) = &body.node else {
            panic!("expected binop body");
        };
        assert!(matches!(lhs.node, Expr::CaptureArg(1)));
        assert!(matches!(rhs.node, Expr::CaptureArg(2)));
    }

    // PICK: `&foo/1` still produces FnRef, not Capture
    #[test]
    fn fn_reference_still_parses_to_fnref() {
        assert!(matches!(expr("&foo/1"), Expr::FnRef { arity: 1, .. }));
        let Expr::FnRef { name, arity } = expr("&Mod.bar/2") else {
            panic!("expected fnref");
        };
        assert_eq!(name, "Mod.bar");
        assert_eq!(arity, 2);
    }

    // PICK: capture expression passed as argument in a function call
    #[test]
    fn capture_appears_as_a_call_argument() {
        // Enum.map(xs, &(&1 * 2)) — the capture rides in as the last arg.
        let Expr::Call(_, args) = expr("Enum.map(xs, &(&1 * 2))") else {
            panic!("expected call");
        };
        assert_eq!(args.len(), 2);
        assert!(matches!(args[1].node, Expr::Capture(_)));
    }

    // PICK: anonymous function call uses `fun.(args)` dot-call syntax
    #[test]
    fn anonymous_function_call_uses_dot_parens() {
        let Expr::ClosureCall(callee, args) = expr("fun.(1, 2)") else {
            panic!("expected closure call");
        };
        assert!(matches!(callee.node, Expr::Var(ref n) if n == "fun"));
        assert_eq!(args.len(), 2);
    }

    // DROP: named call vs local variable disambiguation, pure parse structure
    #[test]
    fn bare_call_stays_named_call_even_when_target_name_looks_like_a_local() {
        let Expr::Call(callee, args) = expr("count(1)") else {
            panic!("expected named call");
        };
        assert!(matches!(callee.node, Expr::Var(ref n) if n == "count"));
        assert_eq!(args.len(), 1);
    }
}
