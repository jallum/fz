use super::*;
use crate::frontend::resolve::flatten_modules;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;

fn parse(src: &str) -> Program {
    let toks = Lexer::new(src).tokenize().expect("lex");
    Parser::new(toks).parse_program().expect("parse")
}

/// Run the full pipeline (parse → flatten → expand → eval main) and
/// return main's return value.
fn run(src: &str) -> Value {
    let prog = parse(src);
    let mut ct = crate::types::new();
    let mut prog = flatten_modules(&mut ct, prog).expect("flatten");
    expand_program(&mut prog).expect("expand");
    let interp = CompileTimeEvaluator::new();
    interp.load_program(&prog).expect("load");
    interp.call_named("main", vec![]).expect("eval")
}

fn expanded_main_body(src: &str) -> Expr {
    let mut prog = parse(src);
    expand_program(&mut prog).expect("expand");
    let item = prog.items.first().expect("main item");
    let Item::Fn(def) = &**item else {
        panic!("expected fn item");
    };
    def.clauses[0].body.node.clone()
}

#[test]
fn defmacro_increments_arg() {
    // Classic Elixir-shape macro: receives arg as quoted form, returns
    // a quote that adds 1 to it.
    let src = r#"
defmacro plus_one(x) do
  quote do: unquote(x) + 1
end
fn main() do
  plus_one(41)
end
"#;
    assert!(matches!(run(src), Value::Int(42)));
}

#[test]
fn macro_inside_fn_body() {
    let src = r#"
defmacro double(x) do
  quote do: unquote(x) * 2
end
fn run() do
  a = double(10)
  b = double(20)
  a + b
end
fn main() do run() end
"#;
    assert!(matches!(run(src), Value::Int(60)));
}

#[test]
fn macro_returns_a_call() {
    // Macro that splices its arg into a call to a regular fn.
    let src = r#"
fn helper(x) do x * 3 end
defmacro use_helper(x) do
  quote do: helper(unquote(x))
end
fn main() do use_helper(7) end
"#;
    assert!(matches!(run(src), Value::Int(21)));
}

#[test]
fn nested_macro_expansion() {
    // Macro M2 wraps M1's output. Expander must re-expand the result.
    let src = r#"
defmacro m1(x) do quote do: unquote(x) + 1 end
defmacro m2(x) do quote do: m1(unquote(x)) end
fn main() do m2(40) end
"#;
    assert!(matches!(run(src), Value::Int(41)));
}

#[test]
fn macro_args_are_not_pre_expanded() {
    // If macro args were expanded first, m2(m1(0)) would call m1 first
    // and m2 would see 1. Macros receive args quoted, so m2 sees the
    // AST of `m1(0)` and decides what to do with it. Here m2 just
    // splices it into its result, so the final code is `m1(0) + 5` =
    // 1 + 5 = 6.
    let src = r#"
defmacro m1(x) do quote do: unquote(x) + 1 end
defmacro m2(x) do quote do: unquote(x) + 5 end
fn main() do m2(m1(0)) end
"#;
    assert!(matches!(run(src), Value::Int(6)));
}

#[test]
fn runaway_macro_caught() {
    // A macro that expands to itself: m(x) -> m(x). Should bail at the
    // depth limit instead of overflowing the stack.
    let src = r#"
defmacro loop_m(x) do
  quote do: loop_m(unquote(x))
end
fn main() do loop_m(0) end
"#;
    let mut prog = parse(src);
    let res = expand_program(&mut prog);
    assert!(res.is_err(), "expected expansion error");
    assert!(
        matches!(*res.unwrap_err(), MacroError::ExpansionLoop { .. }),
        "expected ExpansionLoop variant"
    );
}

#[test]
fn hygiene_macro_local_does_not_shadow_caller() {
    // Without hygiene, the macro's `t = 99` would clobber the
    // caller's `t`. With hygiene, the macro's `t` becomes a fresh
    // gensym so the caller's binding survives.
    let src = r#"
defmacro set_local() do
  quote do: t = 99
end
fn main() do
  t = 1
  set_local()
  t
end
"#;
    let v = run(src);
    assert!(
        matches!(v, Value::Int(1)),
        "expected caller's t (1) to survive, got {:?}",
        v
    );
}

#[test]
fn hygiene_unquoted_var_keeps_caller_name() {
    // Vars spliced via unquote come from the caller's evaluation
    // context — their VALUES, not their names — so hygiene doesn't
    // affect them. Here unquote(x) splices the literal 7.
    let src = r#"
defmacro emit(x) do
  quote do: unquote(x) + 1
end
fn main() do
  x = 7
  emit(x)
end
"#;
    assert!(matches!(run(src), Value::Int(8)));
}

#[test]
fn hygiene_consistent_within_one_invocation() {
    // The same macro-introduced name used twice in the body must map
    // to the SAME gensym, otherwise t = something; t + t breaks.
    let src = r#"
defmacro double_via_temp(x) do
  quote do
t = unquote(x)
t + t
  end
end
fn main() do
  t = 100
  double_via_temp(21)
end
"#;
    // Macro returns Block([t__hyg_N = 21, t__hyg_N + t__hyg_N]) → 42.
    // Caller's t stays at 100; macro's t__hyg_N is 21+21.
    assert!(matches!(run(src), Value::Int(42)));
}

#[test]
fn cross_module_macro_resolves_quote_against_home_module() {
    // Macro M.bump's body refers to bare `helper`. Resolution
    // qualifies it as M.helper inside the quote, so when expanded
    // into a different module's caller the spliced AST carries the
    // home-module path.
    let src = r#"
defmodule M do
  fn helper(x), do: x + 100
  defmacro bump(x) do
quote do: helper(unquote(x))
  end
end
defmodule User do
  fn run(), do: M.bump(7)
end
fn main() do User.run() end
"#;
    // M.bump expands at compile time into M.helper(7) (a fully
    // qualified call), so the result is 107.
    assert!(matches!(run(src), Value::Int(107)), "expected 107, got {:?}", run(src));
}

#[test]
fn imported_macro_works_unqualified() {
    let src = r#"
defmodule M do
  defmacro bump(x), do: quote do: unquote(x) + 1
end
defmodule User do
  import M, only: [bump: 1]
  fn run(), do: bump(41)
end
fn main() do User.run() end
"#;
    assert!(matches!(run(src), Value::Int(42)));
}

#[test]
fn item_macro_produces_fn_def() {
    // `make_const(name, value)` builds a zero-arg fn that returns the
    // given value. Demonstrates the .16.3 item-producing path:
    // - top-level Item::MacroCall is parsed (.16.2),
    // - the macro returns {:fn_def, name_atom, body_expr},
    // - the expander splices in a real Item::Fn,
    // - the rest of the program can call it.
    let src = r#"
defmacro make_const(name, value) do
  {:fn_def, name, value}
end

make_const(:answer, 42)

fn main() do
  answer()
end
"#;
    assert!(matches!(run(src), Value::Int(42)), "expected 42, got {:?}", run(src));
}

#[test]
fn item_macro_produces_list_of_fns() {
    // Returning a list of :fn_def tuples splices multiple items.
    let src = r#"
defmacro pair(a, b) do
  [
{:fn_def, :first, a},
{:fn_def, :second, b}
  ]
end

pair(10, 20)

fn main() do
  first() + second()
end
"#;
    assert!(matches!(run(src), Value::Int(30)));
}

#[test]
fn item_macro_inside_defmodule_qualifies_names() {
    // .16.5: the resolver stamps the parent module path on the
    // MacroCall so the splicer can prefix the spliced fn names.
    let src = r#"
defmacro make_const(name, value) do
  {:fn_def, name, value}
end

defmodule Constants do
  make_const(:pi_ish, 314)
end

fn main() do
  Constants.pi_ish()
end
"#;
    assert!(matches!(run(src), Value::Int(314)), "expected 314, got {:?}", run(src));
}

#[test]
fn no_macros_is_a_noop() {
    // Pipeline without macros must not regress.
    let src = "fn main() do 1 + 2 end";
    let mut prog = parse(src);
    expand_program(&mut prog).expect("expand");
    let interp = CompileTimeEvaluator::new();
    interp.load_program(&prog).expect("load");
    let v = interp.call_named("main", vec![]).expect("eval");
    assert!(matches!(v, Value::Int(3)));
}

#[test]
fn pipe_into_call_rewrites_during_expansion() {
    let src = "fn add2(x), do: x + 2\nfn main(), do: 1 |> add2()";
    assert!(matches!(run(src), Value::Int(3)));
}

#[test]
fn operator_sugars_rewrite_to_runtime_calls() {
    let body = expanded_main_body(
        r#"fn main() do
  {
[1] ++ [2],
[1, 2, 1] -- [1],
"a" <> "b",
1..3,
1..3//2
  }
end"#,
    );
    let Expr::Tuple(values) = &body else {
        panic!("expected tuple");
    };

    assert_call_name(&values[0], "List.concat", 2);
    assert_call_name(&values[1], "List.subtract", 2);
    assert!(matches!(values[2].node, Expr::BinOp(BinOp::BinConcat, _, _)));
    assert_call_name(&values[3], "Range.new", 3);
    assert_call_name(&values[4], "Range.new", 3);
}

#[test]
fn membership_sugars_rewrite_to_enum_member() {
    let body = expanded_main_body(
        r#"fn main() do
  {
2 in [1, 2, 3],
4 not in [1, 2, 3]
  }
end"#,
    );
    let Expr::Tuple(values) = &body else {
        panic!("expected tuple");
    };

    assert_call_name(&values[0], "Enum.member?", 2);
    let Expr::UnOp(UnOp::Not, inner) = &values[1].node else {
        panic!("expected not wrapping Enum.member?, got {:?}", values[1].node);
    };
    assert_call_name(inner, "Enum.member?", 2);
}

fn assert_call_name(expr: &Spanned<Expr>, expected: &str, arity: usize) {
    let Expr::Call(callee, args) = &expr.node else {
        panic!("expected call, got {:?}", expr.node);
    };
    let Expr::Var(name) = &callee.node else {
        panic!("expected var callee, got {:?}", callee.node);
    };
    assert_eq!(name, expected);
    assert_eq!(args.len(), arity);
}

#[test]
fn capture_shorthand_desugars_to_runnable_lambda() {
    let src = "fn main() do\n  f = &(&1 + &2)\n  f.(20, 22)\nend";
    assert!(matches!(run(src), Value::Int(42)));
}

#[test]
fn bare_capture_arg_desugars_to_identity_lambda() {
    let src = "fn main() do\n  f = &1\n  f.(42)\nend";
    assert!(matches!(run(src), Value::Int(42)));
}

#[test]
fn multi_clause_lambda_desugars_to_case_dispatch() {
    let src = r#"
fn main() do
  f = fn
0 -> :zero
n when n > 0 -> :pos
_ -> :other
  end
  {f.(0), f.(2), f.(-1)}
end
"#;
    let got = run(src);
    assert_eq!(format!("{}", got), "{:zero, :pos, :other}");
}

// ----- .20.3: SpanOrigin lineage on expanded code -----

/// Source-only fn bodies retain `SpanOrigin::Source` after expansion.
/// (Sanity-checks the default — without this we couldn't trust any
/// of the Expanded checks below.)
#[test]
fn parser_nodes_have_source_origin() {
    let src = "fn main(), do: 1 + 2";
    let mut prog = parse(src);
    expand_program(&mut prog).expect("expand");
    let Item::Fn(def) = &*prog.items[0] else { panic!() };
    let body = &def.clauses[0].body;
    assert!(matches!(body.origin, SpanOrigin::Source));
}

/// After a macro expands, the synthesized body carries
/// `SpanOrigin::Expanded { macro_call: <call-site span> }`. The
/// `macro_call` span equals the body before expansion (the call
/// expression at the post-resolution AST).
#[test]
fn macro_expansion_stamps_expanded_origin() {
    let src = r#"
defmacro plus_one(x) do
  quote do: unquote(x) + 1
end
fn main() do plus_one(41) end
"#;
    let mut prog = parse(src);

    // Capture the macro call's span BEFORE expansion replaces it.
    let call_span_before = {
        let Item::Fn(def) = &*prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "main" => Some(it.clone()),
                _ => None,
            })
            .unwrap()
        else {
            panic!()
        };
        // main's body is the macro Call expression directly.
        def.clauses[0].body.span
    };

    expand_program(&mut prog).expect("expand");

    let Item::Fn(def) = &*prog
        .items
        .iter()
        .find_map(|it| match &**it {
            Item::Fn(d) if d.name == "main" => Some(it.clone()),
            _ => None,
        })
        .unwrap()
    else {
        panic!()
    };
    let body = &def.clauses[0].body;
    // The post-expansion body is `unquote_result + 1`. It must carry
    // Expanded lineage pointing at the original call site, plus a
    // definition span pointing at the defmacro declaration.
    let (macro_call, definition) = match body.origin {
        SpanOrigin::Expanded { macro_call, definition } => (macro_call, definition),
        other => panic!("expected Expanded lineage, got {:?}", other),
    };
    assert_eq!(
        macro_call, call_span_before,
        "macro_call should point at the user's plus_one(41) call"
    );
    // The defmacro plus_one(x) do … end declaration must be the source
    // for `definition`.
    let def_span = definition.expect("definition span should be populated");
    let def_text = &src[def_span.start as usize..def_span.end as usize];
    assert!(
        def_text.starts_with("defmacro plus_one"),
        "definition span should slice the defmacro declaration, got {:?}",
        def_text
    );
    // The body's own span should also point at the call site (since
    // the decoded tree had DUMMY everywhere, we filled it in).
    assert_eq!(body.span, call_span_before);
}

/// Children of an expanded tree inherit the same macro_call lineage.
/// (v1: every decoded node was DUMMY, so the walker stamps them all.)
#[test]
fn macro_expansion_lineage_reaches_children() {
    let src = r#"
defmacro plus_one(x) do
  quote do: unquote(x) + 1
end
fn main() do plus_one(41) end
"#;
    let mut prog = parse(src);
    expand_program(&mut prog).expect("expand");
    let Item::Fn(def) = &*prog
        .items
        .iter()
        .find_map(|it| match &**it {
            Item::Fn(d) if d.name == "main" => Some(it.clone()),
            _ => None,
        })
        .unwrap()
    else {
        panic!()
    };
    let body = &def.clauses[0].body;
    // The body is BinOp(Add, lhs, rhs). Both operands should carry
    // Expanded lineage.
    let Expr::BinOp(_, lhs, rhs) = &body.node else {
        panic!("expected BinOp, got {:?}", body.node);
    };
    assert!(
        matches!(lhs.origin, SpanOrigin::Expanded { .. }),
        "lhs should carry Expanded lineage, got {:?}",
        lhs.origin
    );
    assert!(
        matches!(rhs.origin, SpanOrigin::Expanded { .. }),
        "rhs should carry Expanded lineage, got {:?}",
        rhs.origin
    );
}

/// Nested macros: when M2 expands into M1(unquote(x)) and M1 then
/// expands, the FINAL node's lineage points at... the OUTERMOST
/// user call site (M2(40)), per the design decision in the ticket.
/// (Each re-expansion stamps with its own call_span, overwriting the
/// previous Expanded marker. Since `expand_expr` recurses depth-first
/// after the rewrite, the OUTER expansion runs last and wins.)
#[test]
fn nested_macro_lineage_keeps_outermost_call_site() {
    let src = r#"
defmacro m1(x) do quote do: unquote(x) + 1 end
defmacro m2(x) do quote do: m1(unquote(x)) end
fn main() do m2(40) end
"#;
    let mut prog = parse(src);
    let outer_call_span = {
        let Item::Fn(def) = &*prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "main" => Some(it.clone()),
                _ => None,
            })
            .unwrap()
        else {
            panic!()
        };
        def.clauses[0].body.span
    };
    expand_program(&mut prog).expect("expand");
    let Item::Fn(def) = &*prog
        .items
        .iter()
        .find_map(|it| match &**it {
            Item::Fn(d) if d.name == "main" => Some(it.clone()),
            _ => None,
        })
        .unwrap()
    else {
        panic!()
    };
    let body = &def.clauses[0].body;
    match body.origin {
        SpanOrigin::Expanded { macro_call, .. } => {
            assert_eq!(
                macro_call, outer_call_span,
                "outermost call site should win for nested macros"
            );
        }
        other => panic!("expected Expanded lineage, got {:?}", other),
    }
}

/// Item-macros that produce `:fn_def` tuples: the synthesized
/// `Item::Fn` body inherits the Expanded lineage of the
/// `Item::MacroCall` that produced it. `make_const(:answer, 42)`
/// splices an `answer/0` fn whose body should point at the
/// `make_const(...)` call site.
#[test]
fn item_macro_splice_body_carries_expanded_lineage() {
    let src = r#"
defmacro make_const(name, value) do
  {:fn_def, name, value}
end

make_const(:answer, 42)

fn main(), do: answer()
"#;
    let mut prog = parse(src);
    // Find the original `make_const(...)` MacroCall's span before expansion.
    let macro_call_span = prog
        .items
        .iter()
        .find_map(|it| match &**it {
            Item::MacroCall { name, span, .. } if name == "make_const" => Some(*span),
            _ => None,
        })
        .expect("make_const MacroCall pre-expansion");

    expand_program(&mut prog).expect("expand");

    let Item::Fn(answer) = &*prog
        .items
        .iter()
        .find_map(|it| match &**it {
            Item::Fn(d) if d.name == "answer" => Some(it.clone()),
            _ => None,
        })
        .expect("answer fn after expansion")
    else {
        panic!()
    };
    let body = &answer.clauses[0].body;
    match body.origin {
        SpanOrigin::Expanded { macro_call, definition } => {
            assert_eq!(
                macro_call, macro_call_span,
                "spliced fn's body should point at the make_const(...) call"
            );
            let def_span = definition.expect("definition span on item-macro splice");
            let def_text = &src[def_span.start as usize..def_span.end as usize];
            assert!(
                def_text.starts_with("defmacro make_const"),
                "definition span should slice the defmacro declaration"
            );
        }
        other => panic!("expected Expanded origin, got {:?}", other),
    }
}

// ----- .21 step 2: MacroError carries a real call-site Span -----

/// A runaway macro produces an `ExpansionLoop` whose Span points at
/// the offending expression (the recursive `loop_m(...)` node), not
/// `Span::DUMMY`. The renderer relies on this to underline source.
#[test]
fn expansion_loop_diag_has_real_span() {
    let src = r#"
defmacro loop_m(x) do
  quote do: loop_m(unquote(x))
end
fn main() do loop_m(0) end
"#;
    let mut prog = parse(src);
    let err = expand_program(&mut prog).unwrap_err();
    let d = err.to_diagnostic();
    assert_ne!(d.primary.span, Span::DUMMY, "ExpansionLoop should carry a real span");
    assert_eq!(d.code, codes::MACRO_EXPANSION_LOOP);
}

/// A body-failure carries both the call-site span (primary) and the
/// defmacro span (secondary), so the renderer can show both locations.
#[test]
fn body_failed_diag_has_call_and_def_spans() {
    // Macro body that calls a non-existent function: the body errors at
    // runtime, surfacing as MacroError::BodyFailed.
    let src = r#"
defmacro bad() do
  no_such_function()
end
fn main() do bad() end
"#;
    let mut prog = parse(src);
    let err = expand_program(&mut prog).unwrap_err();
    match *err {
        MacroError::BodyFailed {
            call_span, def_span, ..
        } => {
            assert_ne!(call_span, Span::DUMMY, "BodyFailed should carry a real call_span");
            let ds = def_span.expect("def_span should be populated");
            let def_text = &src[ds.start as usize..ds.end as usize];
            assert!(
                def_text.starts_with("defmacro bad"),
                "def_span should slice the defmacro decl, got {:?}",
                def_text
            );
        }
        other => panic!("expected BodyFailed, got {:?}", other),
    }
}

/// Definition span is `None` if the macro isn't loaded via
/// `load_program` — sanity-checking the lookup fallback so that
/// an unknown macro doesn't crash, just yields a None definition.
/// (This case is reachable from the REPL when a macro is referenced
/// before its defining input has been processed; the planner/expander
/// errors out earlier today, but the lineage path stays safe.)
#[test]
fn missing_def_span_falls_back_to_none() {
    use crate::diag::{FileId, Span};
    // Build a tree manually and stamp with no definition.
    let mut e = Spanned::dummy(Expr::Int(42));
    let call_span = Span::new(FileId(0), 10, 20);
    super::stamp_expanded(&mut e, call_span, None);
    match e.origin {
        SpanOrigin::Expanded { macro_call, definition } => {
            assert_eq!(macro_call, call_span);
            assert_eq!(definition, None);
        }
        other => panic!("got {:?}", other),
    }
}
