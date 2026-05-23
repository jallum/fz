use super::*;

#[cfg(test)]
mod do_block_sugar_tests {
    use super::*;
    use crate::lexer::Lexer;

    fn parse_fn_body(src: &str) -> Expr {
        let wrapped = format!("fn _t() do {} end", src);
        let toks = Lexer::new(&wrapped).tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        match &*prog.items[0] {
            Item::Fn(d) => match &d.clauses[0].body.node {
                Expr::Block(xs) => xs[0].node.clone(),
                other => other.clone(),
            },
            _ => panic!(),
        }
    }

    #[test]
    fn trailing_do_block_appended_as_arg() {
        let e = parse_fn_body(
            r#"f("x") do
            1
            2
        end"#,
        );
        let Expr::Call(callee, args) = e else {
            panic!("not a call")
        };
        assert!(matches!(callee.node, Expr::Var(ref n) if n == "f"));
        assert_eq!(args.len(), 2, "name + body block");
        assert!(matches!(args[0].node, Expr::Binary(_)));
        assert!(matches!(args[1].node, Expr::Block(_)));
    }

    #[test]
    fn comma_do_kw_appended_as_arg() {
        let e = parse_fn_body(r#"f("x"), do: 42"#);
        let Expr::Call(_, args) = e else {
            panic!("not a call")
        };
        assert_eq!(args.len(), 2);
        assert!(matches!(args[1].node, Expr::Int(42)));
    }

    #[test]
    fn item_level_call_parses_as_macro_call() {
        let toks = Lexer::new(
            r#"
test("addition") do
  1 + 2
end
"#,
        )
        .tokenize()
        .unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let mc = prog.items.iter().find_map(|it| match &**it {
            Item::MacroCall { name, args, .. } => Some((name.clone(), args.clone())),
            _ => None,
        });
        let (name, args) = mc.expect("expected an Item::MacroCall");
        assert_eq!(name, "test");
        assert_eq!(args.len(), 2, "name + body");
        assert!(matches!(args[0].node, Expr::Binary(ref s) if s == b"addition"));
        match &args[1].node {
            Expr::Block(_) | Expr::BinOp(_, _, _) => {}
            other => panic!("unexpected body shape: {:?}", other),
        }
    }

    #[test]
    fn item_level_call_inside_module() {
        let toks = Lexer::new(
            r#"
defmodule MyTest do
  test("addition") do
    1 + 2
  end
end
"#,
        )
        .tokenize()
        .unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let m = prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Module(m) => Some(m),
                _ => None,
            })
            .unwrap();
        assert!(
            m.items
                .iter()
                .any(|it| matches!(&**it, Item::MacroCall { .. }))
        );
    }

    #[test]
    fn plain_call_no_extra_arg() {
        let e = parse_fn_body("f(1, 2)");
        let Expr::Call(_, args) = e else { panic!() };
        assert_eq!(args.len(), 2);
    }

    /// fz-rcp.1 — call-postfix `do … end` sugar must be suppressed in
    /// cond position; otherwise `if pred(h) do … end` parses the
    /// then-arm as a second arg to `pred`, leaving `else`/`end`
    /// floating.
    #[test]
    fn cond_call_in_if_does_not_swallow_do_block() {
        let e = parse_fn_body(
            r#"if pred(h) do
                1
            else
                2
            end"#,
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

    #[test]
    fn receive_single_clause_no_after_parses() {
        let e = parse_fn_body(
            r#"receive do
                msg -> msg
            end"#,
        );
        let Expr::Receive { clauses, after } = e else {
            panic!("expected Receive, got {:?}", e);
        };
        assert_eq!(clauses.len(), 1);
        assert!(after.is_none());
        assert!(matches!(clauses[0].pattern.node, Pattern::Var(ref n) if n == "msg"));
        assert!(clauses[0].guard.is_none());
    }

    #[test]
    fn receive_multi_clause_parses() {
        let e = parse_fn_body(
            r#"receive do
                {:get, k} -> 1
                {:put, k, v} -> 2
                :stop -> 3
            end"#,
        );
        let Expr::Receive { clauses, after } = e else {
            panic!("expected Receive, got {:?}", e);
        };
        assert_eq!(clauses.len(), 3);
        assert!(after.is_none());
    }

    #[test]
    fn receive_clause_with_guard_parses() {
        let e = parse_fn_body(
            r#"receive do
                n when n > 0 -> n
            end"#,
        );
        let Expr::Receive { clauses, after } = e else {
            panic!("expected Receive");
        };
        assert!(after.is_none());
        assert!(clauses[0].guard.is_some());
    }

    #[test]
    fn receive_with_after_parses() {
        let e = parse_fn_body(
            r#"receive do
                msg -> msg
            after
                500 -> :timeout
            end"#,
        );
        let Expr::Receive { clauses, after } = e else {
            panic!("expected Receive");
        };
        assert_eq!(clauses.len(), 1);
        let af = after.expect("after clause parsed");
        assert!(matches!(af.timeout.node, Expr::Int(500)));
        assert!(matches!(af.body.node, Expr::Atom(ref a) if a == "timeout"));
    }

    #[test]
    fn receive_with_after_zero_parses() {
        // `after 0` is the peek form.
        let e = parse_fn_body(
            r#"receive do
                msg -> msg
            after
                0 -> nil
            end"#,
        );
        let Expr::Receive { clauses: _, after } = e else {
            panic!("expected Receive");
        };
        let af = after.expect("after clause parsed");
        assert!(matches!(af.timeout.node, Expr::Int(0)));
    }

    #[test]
    fn receive_with_after_infinity_parses() {
        let e = parse_fn_body(
            r#"receive do
                msg -> msg
            after
                :infinity -> :never
            end"#,
        );
        let Expr::Receive { clauses: _, after } = e else {
            panic!("expected Receive");
        };
        let af = after.expect("after clause parsed");
        assert!(matches!(af.timeout.node, Expr::Atom(ref a) if a == "infinity"));
    }

    #[test]
    fn receive_pinned_pattern_var_parses() {
        let e = parse_fn_body(
            r#"receive do
                {:reply, ^ref, v} -> v
            end"#,
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

    #[test]
    fn legacy_receive_call_still_parses() {
        // fz-5vj keeps the old `receive()` form working until fz-recv.A2.
        let e = parse_fn_body("receive()");
        let Expr::Call(callee, args) = e else {
            panic!("expected Call, got {:?}", e);
        };
        assert!(matches!(callee.node, Expr::Var(ref n) if n == "receive"));
        assert!(args.is_empty());
    }

    /// case scrutinee, cond test, with binding source, and when-guard
    /// are all cond-position and must suppress the sugar.
    // fz-swt.5 — explicit `&name/arity` fn references.

    #[test]
    fn fn_ref_bare_name_parses() {
        let e = parse_fn_body("&foo/1");
        match e {
            Expr::FnRef { name, arity } => {
                assert_eq!(name, "foo");
                assert_eq!(arity, 1);
            }
            other => panic!("expected FnRef, got {:?}", other),
        }
    }

    #[test]
    fn fn_ref_zero_arity_parses() {
        let e = parse_fn_body("&do_it/0");
        match e {
            Expr::FnRef { name, arity } => {
                assert_eq!(name, "do_it");
                assert_eq!(arity, 0);
            }
            other => panic!("expected FnRef, got {:?}", other),
        }
    }

    #[test]
    fn fn_ref_module_qualified_parses() {
        // `&Mod.fun/2` captures the full dotted path as the name.
        let e = parse_fn_body("&Mod.fun/2");
        match e {
            Expr::FnRef { name, arity } => {
                assert_eq!(name, "Mod.fun");
                assert_eq!(arity, 2);
            }
            other => panic!("expected FnRef, got {:?}", other),
        }
    }

    #[test]
    fn fn_ref_nested_module_qualified_parses() {
        let e = parse_fn_body("&A.B.run/3");
        match e {
            Expr::FnRef { name, arity } => {
                assert_eq!(name, "A.B.run");
                assert_eq!(arity, 3);
            }
            other => panic!("expected FnRef, got {:?}", other),
        }
    }

    #[test]
    fn fn_ref_as_call_arg_parses() {
        // Ensures &name/arity composes naturally inside argument lists.
        let e = parse_fn_body("apply(&foo/1, 7)");
        let Expr::Call(_, args) = e else { panic!() };
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0].node, Expr::FnRef { name, arity }
            if name == "foo" && *arity == 1));
    }

    #[test]
    fn double_ampersand_is_still_andand() {
        // Defensive: adding bare `&` to the lexer must not break `&&`.
        let e = parse_fn_body("true && false");
        let Expr::BinOp(op, _, _) = e else { panic!() };
        assert!(matches!(op, BinOp::And));
    }

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
    use crate::lexer::Lexer;

    fn parse_extern(src: &str) -> FnDef {
        let toks = Lexer::new(src).tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        match &*prog.items[0] {
            Item::Fn(d) => d.clone(),
            other => panic!("expected Item::Fn, got {:?}", other),
        }
    }

    #[test]
    fn extern_fn_no_params() {
        let d = parse_extern("extern \"C\" fn fz_halt() :: never\n");
        assert_eq!(d.name, "fz_halt");
        assert_eq!(d.extern_abi, Some("C".into()));
        assert_eq!(d.extern_params.len(), 0);
        assert!(d.clauses.is_empty());
    }

    #[test]
    fn extern_fn_one_param() {
        let d = parse_extern("extern \"C\" fn fz_print(any) :: unit\n");
        assert_eq!(d.extern_params.len(), 1);
    }

    #[test]
    fn extern_fn_two_params() {
        let d = parse_extern("extern \"C\" fn fz_assert_eq(any, any) :: unit\n");
        assert_eq!(d.extern_params.len(), 2);
        assert!(!d.extern_ret_tokens.0.is_empty());
    }
}

#[cfg(test)]
mod telemetry_tests {
    use super::*;
    use crate::lexer::Lexer;

    #[test]
    fn telemetry_emits_pass_span_and_item_count() {
        use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind, Value};

        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());

        let toks = Lexer::new("fn id(x), do: x\nfn main(), do: id(1)\n")
            .tokenize()
            .expect("lex");
        let prog = Parser::new(toks)
            .parse_program_with_telemetry(&tel)
            .expect("parse");

        assert_eq!(cap.count_by_kind(EventKind::SpanStart), 1);
        assert_eq!(cap.count_by_kind(EventKind::SpanStop), 1);
        assert_eq!(cap.count(PARSE_PASS_NAME), 2);

        let built = cap.last(ITEMS_BUILT_NAME).unwrap();
        match built.measurements.get("count") {
            Some(Value::U64(n)) => assert_eq!(*n as usize, prog.items.len()),
            other => panic!("expected U64 count, got {:?}", other),
        }
    }

    #[test]
    fn telemetry_user_event_inherits_span_id() {
        use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind};

        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());

        let toks = Lexer::new("fn main(), do: :ok").tokenize().expect("lex");
        let _ = Parser::new(toks)
            .parse_program_with_telemetry(&tel)
            .expect("parse");

        let start = cap
            .find(PARSE_PASS_NAME)
            .into_iter()
            .find(|e| e.kind == EventKind::SpanStart)
            .unwrap();
        let built = cap.last(ITEMS_BUILT_NAME).unwrap();
        assert_eq!(start.span_id, built.span_id);
        assert!(start.span_id > 0);
    }

    #[test]
    fn null_telemetry_is_a_silent_no_op() {
        use crate::telemetry::NullTelemetry;

        let toks = Lexer::new("fn main(), do: :ok").tokenize().expect("lex");
        let prog = Parser::new(toks)
            .parse_program_with_telemetry(&NullTelemetry)
            .expect("parse");
        assert_eq!(prog.items.len(), 1);
    }
}
