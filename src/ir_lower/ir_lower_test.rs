use super::*;
use crate::dispatch_matrix::DispatchConst;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardExpr};
use crate::telemetry::Telemetry;

fn lower_src(src: &str, tel: &dyn Telemetry) -> Module {
    let toks = Lexer::with_source_name(src, "<test>").tokenize(tel).expect("lex");
    let prog = Parser::new(toks).parse_program(tel).expect("parse");
    lower_program(&mut crate::types::new(), &prog, tel).expect("lower failed")
}

fn lower_flat_src(src: &str, tel: &dyn Telemetry) -> (crate::types::DefaultTypes, Module) {
    let toks = Lexer::with_source_name(src, "<test>").tokenize(tel).expect("lex");
    let prog = Parser::new(toks).parse_program(tel).expect("parse");
    let mut ct = crate::types::new();
    let prog = flatten_modules(&mut ct, prog, tel).expect("flatten");
    let module = lower_program(&mut ct, &prog, tel).expect("lower failed");
    (ct, module)
}

fn lower_src_with_capture(src: &str, tel: &ConfiguredTelemetry) -> (Module, Capture) {
    let cap = Capture::new();
    let handler_id = tel.attach(&[], cap.handler());
    let toks = Lexer::with_source_name(src, "<test>").tokenize(tel).expect("lex");
    let prog = Parser::new(toks).parse_program(tel).expect("parse");
    let module = lower_program(&mut crate::types::new(), &prog, tel).expect("lower failed");
    assert!(tel.detach(handler_id), "temporary lower capture should detach");
    (module, cap)
}

fn lower_src_err(src: &str, tel: &dyn Telemetry) -> LowerError {
    let toks = Lexer::with_source_name(src, "<test>").tokenize(tel).expect("lex");
    let prog = Parser::new(toks).parse_program(tel).expect("parse");
    lower_program(&mut crate::types::new(), &prog, tel).expect_err("expected lower error")
}

#[test]
fn struct_record_type_registers_opaque_underlying_tuple_in_schema_order() {
    let (mut ct, m) = lower_flat_src(
        r#"
defmodule Range do
  defstruct [:first, :last, :step]
  @type t :: %Range{first: integer, last: integer, step: integer}
  fn new(first, last, step), do: %Range{first: first, last: last, step: step}
end
"#,
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let inner = m
        .opaque_inners
        .get("impl-target::Range")
        .expect("Range struct underlying tuple")
        .clone();
    let fields = ct.tuple_projections(&inner, 3);
    let int = ct.int();
    assert!(fields.iter().all(|field| ct.is_equivalent(field, &int)));
}

/// fz-qbg.4 — Compile + run a fz program through the JIT and return
/// captured stdout (joined by newline). Mirrors `ir_codegen::tests::
/// capture_main`; lets ir_lower-level tests assert end-to-end runtime
/// correctness rather than just IR shape.
fn run_and_capture(src: &str, tel: &ConfiguredTelemetry) -> String {
    let mut graph = linked_runtime_graph(src, tel);
    let entry = graph.linked_module().fn_by_name("main").expect("no main fn").id;
    let (module, module_plan) = graph.cloned_linked_module_plan();
    let compiled = compile_planned(graph.types(), &module, &module_plan, tel).expect("compile planned");
    let dbg = DbgCapture::new();
    let handler_id = tel.attach(&[], dbg.handler());
    let mut rt = Runtime::new(&compiled, 1, tel);
    let _ = rt.spawn(entry);
    rt.run_until_idle();
    assert!(tel.detach(handler_id), "temporary debug capture should detach");
    dbg.lines().join("\n")
}

fn count_prims(m: &Module, pred: impl Fn(&Prim) -> bool) -> usize {
    m.fns
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.stmts)
        .filter(|stmt| {
            let Stmt::Let(_, prim) = stmt;
            pred(prim)
        })
        .count()
}

fn count_prims_in_fn(f: &FnIr, pred: impl Fn(&Prim) -> bool) -> usize {
    f.blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter(|stmt| {
            let Stmt::Let(_, prim) = stmt;
            pred(prim)
        })
        .count()
}

fn first_make_closure(f: &FnIr) -> (FnId, Vec<Var>) {
    f.blocks
        .iter()
        .flat_map(|block| &block.stmts)
        .find_map(|stmt| {
            let Stmt::Let(_, prim) = stmt;
            if let Prim::MakeClosure(_, lambda_id, captured) = prim {
                Some((*lambda_id, captured.clone()))
            } else {
                None
            }
        })
        .expect("expected closure construction")
}

fn first_make_fn_ref(f: &FnIr) -> FnId {
    f.blocks
        .iter()
        .flat_map(|block| &block.stmts)
        .find_map(|stmt| {
            let Stmt::Let(_, prim) = stmt;
            if let Prim::MakeFnRef(_, fn_id) = prim {
                Some(*fn_id)
            } else {
                None
            }
        })
        .expect("expected fn ref construction")
}

#[test]
fn lower_const_int_returns_in_entry_block() {
    let m = lower_src("fn f() do 42 end", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("const(42)"), "{}", s);
    assert!(s.contains("return v"), "{}", s);
}

#[test]
fn lower_var_lookup() {
    let m = lower_src("fn id(x), do: x", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("return v0"), "got:\n{}", s);
}

#[test]
fn lower_binop_add() {
    let m = lower_src("fn add1(x), do: x + 1", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("const(1)"), "{}", s);
    assert!(s.contains(" + "), "{}", s);
}

#[test]
fn lower_unop_neg() {
    let m = lower_src("fn neg(x), do: -x", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("- v0"));
}

#[test]
fn lower_tail_call_uses_tail_call() {
    let m = lower_src(
        "fn caller(x), do: callee(x)\nfn callee(y), do: y",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("tail_call"), "got:\n{}", s);
}

#[test]
fn lower_nontail_call_splits_into_continuation() {
    let m = lower_src(
        "fn caller(x), do: callee(x) + 1\nfn callee(y), do: y",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    // "call fnN" where N is callee's FnId (shifts with runtime.fz prelude).
    assert!(s.contains("call fn"), "expected explicit call, got:\n{}", s);
    assert!(s.contains("cont(fn"), "expected continuation, got:\n{}", s);
    // Continuation fn is named "k_{FnId}"; FnId shifts with runtime.fz prelude.
    assert!(
        s.contains(" k_") || s.contains("lambda_"),
        "expected continuation fn, got:\n{}",
        s
    );
}

#[test]
fn lower_program_returns_normalized_call_continuation_captures() {
    let (m, cap) = lower_src_with_capture(
        "fn callee(x), do: x\nfn caller(x, y), do: callee(x) + x",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let caller = m.fn_by_name("caller").expect("caller fn missing");
    let continuation = caller
        .blocks
        .iter()
        .find_map(|b| {
            if let Term::Call { continuation, .. } = &b.terminator {
                Some(continuation)
            } else {
                None
            }
        })
        .expect("caller should contain non-tail call");
    let ev = cap
        .find(&["fz", "ir", "capture_norm", "captures_pruned"])
        .into_iter()
        .find(|ev| {
            matches!(
                ev.metadata.get("producer"),
                Some(Value::Str(s)) if s.as_ref() == "call_continuation"
            ) && matches!(
                ev.measurements.get("fn_id"),
                Some(Value::U64(id)) if *id == continuation.fn_id.0 as u64
            )
        })
        .expect("captures_pruned event");
    assert!(matches!(ev.measurements.get("before_captures"), Some(Value::U64(2))));
    assert!(matches!(ev.measurements.get("after_captures"), Some(Value::U64(1))));
    assert!(matches!(ev.measurements.get("pruned_captures"), Some(Value::U64(1))));

    assert_eq!(
        continuation.captured.len(),
        1,
        "only x is live after callee(x); y must not survive as a continuation capture"
    );

    let k = m.fn_by_id(continuation.fn_id);
    let entry = k.block(k.entry);
    assert_eq!(
        entry.params.len(),
        2,
        "continuation entry should be [result, x], not [result, x, y]"
    );
}

#[test]
fn lower_records_declared_spec_overload_set() {
    let m = lower_src(
        "@spec pick(integer) :: integer\n\
         @spec pick(float) :: float\n\
         fn pick(x), do: x",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let pick = m.fn_by_name("pick").expect("pick fn missing");
    let specs = m.declared_specs.get(&pick.id).expect("declared specs missing");
    assert_eq!(specs.arrows.len(), 2);
}

#[test]
fn lower_records_source_function_correspondence() {
    let m = lower_src(
        "@spec drop(Enumerable.t(a), integer) :: [a]\n\
         fn drop(_enumerable, _count), do: []",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let drop = m.fn_by_name("drop").expect("drop fn missing");
    let groups = m
        .function_correspondence
        .get(&drop.id)
        .expect("function correspondence missing");
    assert_eq!(
        groups,
        &vec![StructuralCorrespondenceGroup {
            var: TypeVarId(0),
            occurrences: vec![
                StructuralOccurrence::Param {
                    param_index: 0,
                    path: vec![StructuralPathStep::NamedArg(0)],
                },
                StructuralOccurrence::Result {
                    path: vec![StructuralPathStep::ListElem],
                },
            ],
        }]
    );
}

#[test]
fn lower_synthesizes_direct_call_continuation_correspondence() {
    let m = lower_src(
        "@spec id(a) :: a\n\
         fn id(x), do: x\n\
         @spec pair_after_id(a) :: {a, a}\n\
         fn pair_after_id(x) do\n\
           y = id(x)\n\
           {x, y}\n\
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let pair_after_id = m.fn_by_name("pair_after_id").expect("pair_after_id fn missing");
    let continuation = m
        .fns
        .iter()
        .find(|f| f.name.starts_with("k_") && f.owner_module == pair_after_id.owner_module)
        .expect("continuation fn missing");
    let groups = m
        .function_correspondence
        .get(&continuation.id)
        .expect("continuation correspondence missing");
    assert_eq!(
        groups,
        &vec![StructuralCorrespondenceGroup {
            var: TypeVarId(0),
            occurrences: vec![
                StructuralOccurrence::Param {
                    param_index: 0,
                    path: vec![],
                },
                StructuralOccurrence::Param {
                    param_index: 1,
                    path: vec![],
                },
                StructuralOccurrence::Result {
                    path: vec![StructuralPathStep::TupleElem(0)],
                },
                StructuralOccurrence::Result {
                    path: vec![StructuralPathStep::TupleElem(1)],
                },
            ],
        }]
    );
}

#[test]
fn lower_persists_direct_call_continuation_provenance() {
    let m = lower_src(
        "@spec id(a) :: a\n\
         fn id(x), do: x\n\
         fn pair_after_id(x) do\n\
           y = id(x)\n\
           {x, y}\n\
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let pair_after_id = m.fn_by_name("pair_after_id").expect("pair_after_id fn missing");
    let continuation = m
        .fns
        .iter()
        .find(|f| f.name.starts_with("k_") && f.owner_module == pair_after_id.owner_module)
        .expect("continuation fn missing");
    let provenance = m
        .continuation_provenance
        .get(&continuation.id)
        .expect("continuation provenance missing");
    let id = m.fn_by_name("id").expect("id fn missing");
    assert_eq!(
        provenance,
        &ContinuationProvenance {
            caller: pair_after_id.id,
            captured: vec![pair_after_id.block(pair_after_id.entry).params[0]],
            capture_param_offset: 1,
            kind: ContinuationProvenanceKind::DirectCall {
                callee: id.id,
                args: vec![pair_after_id.block(pair_after_id.entry).params[0]],
            },
        }
    );
}

#[test]
fn lower_synthesizes_closure_call_continuation_correspondence() {
    let m = lower_src(
        "@spec apply_pair((a) -> b, a) :: {a, b}\n\
         fn apply_pair(f, x) do\n\
           y = f.(x)\n\
           {x, y}\n\
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let apply_pair = m.fn_by_name("apply_pair").expect("apply_pair fn missing");
    let continuation = m
        .fns
        .iter()
        .find(|f| f.name.starts_with("k_") && f.owner_module == apply_pair.owner_module)
        .expect("continuation fn missing");
    let groups = m
        .function_correspondence
        .get(&continuation.id)
        .expect("continuation correspondence missing");
    assert_eq!(
        groups,
        &vec![
            StructuralCorrespondenceGroup {
                var: TypeVarId(0),
                occurrences: vec![
                    StructuralOccurrence::Param {
                        param_index: 0,
                        path: vec![],
                    },
                    StructuralOccurrence::Result {
                        path: vec![StructuralPathStep::TupleElem(1)],
                    },
                ],
            },
            StructuralCorrespondenceGroup {
                var: TypeVarId(1),
                occurrences: vec![
                    StructuralOccurrence::Param {
                        param_index: 2,
                        path: vec![],
                    },
                    StructuralOccurrence::Result {
                        path: vec![StructuralPathStep::TupleElem(0)],
                    },
                ],
            },
        ]
    );
}

#[test]
fn lower_persists_matcher_body_continuation_provenance() {
    let m = lower_src(
        "fn f(x) do\n\
           case x do\n\
             [head | tail] -> {head, tail}\n\
           end\n\
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let continuation = m
        .fns
        .iter()
        .find(|f| f.name.starts_with("case_clause_"))
        .expect("matcher-body continuation missing");
    let provenance = m
        .continuation_provenance
        .get(&continuation.id)
        .expect("matcher-body provenance missing");
    match &provenance.kind {
        ContinuationProvenanceKind::DispatchBody { bindings } => {
            assert_eq!(provenance.capture_param_offset, 0);
            assert_eq!(bindings.len(), 2, "expected head/tail bindings");
        }
        other => panic!("expected matcher-body provenance, got {:?}", other),
    }
}

#[test]
fn lower_if_uses_continuation_fns() {
    // fz-duq.2 — `if` lowers to: outer fn with Term::If + per-arm
    // TailCalls into separate fns (if_then / if_else / optional
    // if_join). The old block-join shape is gone.
    let m = lower_src(
        "fn pos(x), do: if x > 0, do: 1, else: -1",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("if v"), "expected If terminator: {}", s);
    assert!(s.contains("if_then"), "expected if_then arm fn: {}", s);
    assert!(s.contains("if_else"), "expected if_else arm fn: {}", s);
    assert!(s.contains("tail_call"), "expected TailCall from arm block: {}", s);
    // Tail-position if: no join fn (arms self-Return).
    assert!(
        !s.contains("if_join"),
        "tail-position if should not need a join fn: {}",
        s
    );
}

#[test]
fn fz_84m_repro_a_prints_99() {
    // fz-84m repro A — constant cond + non-tail call in if-arm.
    // Pre-fz-duq.2 panicked at fz_ir.rs:453 (block_mut "unknown
    // block") during IR construction. Now runs end-to-end.
    let out = run_and_capture(
        "fn helper(), do: 7\n\
         fn main() do\n\
           if 1 == 0 do dbg(helper()) else dbg(99) end\n\
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    assert_eq!(out, "99");
}

#[test]
fn fz_84m_repro_b_prints_7_then_99() {
    // fz-84m repro B — tail-call in if-arm + per-callsite narrowing.
    // Pre-fz-duq.2 silently dropped the tail call by overwriting its
    // TailCall terminator with `Goto(join_b, [Var(0)])`, propagating
    // the sentinel as the if's value. Result: exit 0, no stdout.
    let out = run_and_capture(
        "fn helper(), do: 7\n\
         fn pick(n) do if n == 0 do helper() else 99 end end\n\
         fn main() do dbg(pick(0)); dbg(pick(1)) end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    assert_eq!(out, "7\n99");
}

#[test]
fn lower_case_uses_per_clause_cont_fns() {
    // fz-duq.3 — `case` lowers each clause body into its own cont fn
    // so that internal CPS-splits stay confined.
    let m = lower_src(
        "fn helper(), do: 7\n\
         fn classify(n) do\n\
           case n do\n\
             0 -> helper()\n\
             _ -> 99\n\
           end\n\
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("case_clause_0"), "expected clause cont: {}", s);
    assert!(s.contains("case_clause_1"), "expected clause cont: {}", s);
    // Tail-position case: no join fn.
    assert!(
        !s.contains("case_join"),
        "tail-position case should not need a join fn: {}",
        s
    );
}

#[test]
fn lower_cond_uses_per_arm_cont_fns() {
    // fz-duq.4 — cond arms each lower into their own cont fn so that
    // both test- and body-side CPS-splits stay confined.
    let m = lower_src(
        "fn helper(), do: 7\n\
         fn route(n) do\n\
           cond do\n\
             n == 0 -> helper()\n\
             true -> 99\n\
           end\n\
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("cond_arm_0"), "expected arm cont: {}", s);
    assert!(s.contains("cond_arm_1"), "expected arm cont: {}", s);
    assert!(s.contains("cond_fail"), "expected fail cont: {}", s);
}

#[test]
fn lower_with_uses_continuation_fns() {
    // fz-duq.4 — `with`'s mismatch funnel becomes a continuation fn
    // (`with_fail`) and each else-clause body lives in its own cont fn.
    let m = lower_src(
        "fn f(v) do\n\
           with :ok <- v do\n\
             1\n\
           else\n\
             :err -> 2\n\
           end\n\
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("with_fail"), "expected with_fail cont: {}", s);
    assert!(s.contains("with_else_0"), "expected else clause cont: {}", s);
}

#[test]
fn lower_case_with_call_in_clause_no_panic() {
    // case body with a call (was silently broken via Bug 2 — same
    // class as fz-84m's if repros).
    let _ = lower_src(
        "fn helper(), do: 7\n\
         fn classify(n) do\n\
           case n do\n\
             0 -> helper()\n\
             _ -> 99\n\
           end\n\
         end\n\
         fn main() do\n\
           dbg(classify(0))\n\
           dbg(classify(5))\n\
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
}

#[test]
fn fz_ben_tuple_pattern_typetest_routes_non_tuple_to_else() {
    // fz-ben — `{:ok, x}` pattern on `:err` (a non-tuple). Pre-fix,
    // lower_pattern_bind for Pattern::Tuple unconditionally emitted
    // `Prim::TupleField(:err, 0)`, which codegen lowered to a
    // `load notrap aligned :err+16` reading heap garbage. With
    // `notrap` swallowing the SIGSEGV, this fixture silently failed
    // (exit 0, no stdout). After fix: a TypeTest gates the
    // projection — non-tuple subjects route to the fail_block, which
    // dispatches the else-clause `:err -> 0`.
    let out = run_and_capture(
        "fn f(v) do\n\
           with {:ok, x} <- v do x else :err -> 0 end\n\
         end\n\
         fn main() do dbg(f(:err)) end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    assert_eq!(out, "0");
}

#[test]
fn fz_84m_repro_c_prints_7_then_99_no_narrowing() {
    // fz-84m repro C — same bug shape as B but with `n > 0` rather
    // than `n == 0`, so the planner doesn't narrow either arm. Proves
    // the bug was structural in lowering, not type-narrowing driven.
    let out = run_and_capture(
        "fn helper(), do: 7\n\
         fn pick(n) do if n > 0 do helper() else 99 end end\n\
         fn main() do dbg(pick(5)); dbg(pick(0)) end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    assert_eq!(out, "7\n99");
}

#[test]
fn lower_if_nontail_uses_join_fn() {
    // Non-tail if (used as call argument): all three cont fns minted.
    let m = lower_src(
        "fn id(x), do: x\n\
         fn pick(x), do: id(if x > 0, do: 1, else: -1)",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("if_then"), "{}", s);
    assert!(s.contains("if_else"), "{}", s);
    assert!(s.contains("if_join"), "expected join fn for non-tail: {}", s);
}

#[test]
fn non_tail_if_call_arm_flows_through_join() {
    // The branch body is not final tail position when the if has a join.
    // Pre-fix, `fun.(head)` returned directly from if_then and skipped the
    // surrounding list construction.
    let out = run_and_capture(
        "fn map_every_list([], _nth, _index, _fun), do: []\n\
         fn map_every_list([head | tail], nth, index, fun) do\n\
           next = if (index % nth) == 0, do: fun.(head), else: head\n\
           [next | map_every_list(tail, nth, index + 1, fun)]\n\
         end\n\
         fn main() do\n\
           dbg(map_every_list([1, 2, 3, 4], 2, 0, fn (x) -> x * 100 end))\n\
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    assert_eq!(out, "[100, 2, 300, 4]");
}

#[test]
fn non_tail_case_call_arm_flows_through_join() {
    let out = run_and_capture(
        "fn pick(x, fun) do\n\
           next = case x do\n\
             0 -> fun.(x)\n\
             _ -> x\n\
           end\n\
           [next]\n\
         end\n\
         fn main() do dbg(pick(0, fn (x) -> x + 1 end)) end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    assert_eq!(out, "[1]");
}

#[test]
fn non_tail_cond_call_arm_flows_through_join() {
    let out = run_and_capture(
        "fn pick(x, fun) do\n\
           next = cond do\n\
             x == 0 -> fun.(x)\n\
             true -> x\n\
           end\n\
           [next]\n\
         end\n\
         fn main() do dbg(pick(0, fn (x) -> x + 1 end)) end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    assert_eq!(out, "[1]");
}

#[test]
fn lower_block_evaluates_last_expr() {
    let m = lower_src(
        "fn b() do\n  1\n  2\n  3\nend",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("const(1)"), "{}", s);
    assert!(s.contains("const(2)"), "{}", s);
    assert!(s.contains("const(3)"), "{}", s);
    assert!(s.contains("return v"), "{}", s);
}

#[test]
fn lower_list_makes_list_prim() {
    let m = lower_src("fn l(), do: [1, 2]", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("list(["), "{}", s);
    assert!(!s.contains("list([] |"), "no-tail list shouldn't have | sep: {}", s);
}

#[test]
fn lower_list_with_tail() {
    let m = lower_src("fn l(t), do: [1 | t]", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("] | v0)"), "expected list with v0 (param t) tail: {}", s);
}

#[test]
fn lower_tuple_makes_tuple_prim() {
    let m = lower_src("fn t(), do: {1, :ok}", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("tuple(["), "{}", s);
}

#[test]
fn lower_tuple_pattern_projects_fields() {
    let m = lower_src("fn first({a, b}), do: a", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("tuple_field(v0, 0)"), "got:\n{}", s);
    assert!(s.contains("tuple_field(v0, 1)"), "got:\n{}", s);
}

#[test]
fn lower_match_expr_binds_var() {
    let m = lower_src(
        "fn m(p) do\n  x = p\n  x\nend",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("return v0"), "got:\n{}", s);
}

/// fz-fyq.3 — `collect_diagnostics` filters `unreachable-arm` to
/// `BranchOrigin::User`. A destructure (`{a,b} = ...`) and a fn-clause
/// dispatch both synthesize Ifs the planner can prove dead-edged; neither
/// should warn. User-authored Ifs whose dead branch the planner can
/// prove (here: `if true do A else B` where the else is structurally
/// unreachable) still do.
#[test]
fn unreachable_arm_silenced_on_synthesized_ifs() {
    let m = lower_src(
        concat!(
            "fn fst(0), do: :zero\n",
            "fn fst(_), do: :other\n",
            "fn main() do\n",
            "  {a, b} = {1, 2}\n",
            "  fst(a + b)\n",
            "end\n",
        ),
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let mut ct = crate::types::new();
    let mt = plan_module_with_role(&mut ct, &m, &crate::telemetry::ConfiguredTelemetry::new(), "test");
    let diags = collect_diagnostics(&mut ct, &m, &mt, &crate::telemetry::ConfiguredTelemetry::new());
    let unreachable: Vec<_> = diags
        .as_slice()
        .iter()
        .filter(|d| d.code == codes::TYPE_UNREACHABLE_ARM)
        .collect();
    assert!(
        unreachable.is_empty(),
        "synthesized dispatch Ifs must not warn; got {:?}",
        unreachable
    );
}

/// fz-bsx.5 — the dead-binop ("always false") diagnostic is observed
/// through the telemetry bus ([fz, diag, warning] carrying
/// type/dead-binop), per the project's telemetry-over-stderr policy.
#[test]
fn dead_binop_diagnostic_observable_via_telemetry() {
    let m = lower_src(
        "fn main() do\n  dbg(1 == :ok)\nend\n",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let mut ct = crate::types::new();
    let mt = plan_module_with_role(&mut ct, &m, &crate::telemetry::ConfiguredTelemetry::new(), "test");
    let diags = collect_diagnostics(&mut ct, &m, &mt, &crate::telemetry::ConfiguredTelemetry::new());

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "diag"], cap.handler());
    emit_through(&tel, None, diags.as_slice());

    assert!(
        cap.count(&["fz", "diag", "warning"]) >= 1,
        "dead-binop warning must surface on the telemetry bus"
    );
    assert!(
        diags.as_slice().iter().any(|d| d.code == codes::TYPE_DEAD_BINOP),
        "the surfaced warning carries the type/dead-binop code",
    );
}

#[test]
fn generated_dead_binop_diagnostic_is_not_rendered() {
    let mut f = FnBuilder::new(FnId(0), "generated");
    let entry = f.block(vec![]);
    let one = f.let_(entry, Prim::Const(Const::Int(1)));
    let atom = f.let_(entry, Prim::Const(Const::Atom(0)));
    let eq = f.let_(entry, Prim::BinOp(BinOp::Eq, one, atom));
    f.set_terminator(entry, Term::Return(eq));
    let mut mb = ModuleBuilder::new();
    mb.add_fn(f.build());
    let m = mb.build();

    let mut ct = crate::types::new();
    let mt = plan_module_with_role(&mut ct, &m, &crate::telemetry::ConfiguredTelemetry::new(), "test");
    let diags = collect_diagnostics(&mut ct, &m, &mt, &crate::telemetry::ConfiguredTelemetry::new());

    assert!(
        !diags.as_slice().iter().any(|d| d.code == codes::TYPE_DEAD_BINOP),
        "generated comparisons without source spans must not render dead-binop diagnostics",
    );
}

/// `ModulePlan::dead_branches` publishes only branch facts that are safe
/// for shared-body mutation. Narrow recursive list-dispatch facts stay on
/// the individual `SpecPlan`, because folding the canonical body with them
/// would make the body invalid for wider keys.
#[test]
fn dead_branches_published_for_destructure_and_recursive_list_dispatch() {
    // Irrefutable destructure on a known-2-tuple — the planner proves
    // the synthesized fail edge dead under the one live spec.
    let m = lower_src(
        "fn main() do\n  {a, b} = {1, 2}\n  a + b\nend\n",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let mut ct = crate::types::new();
    let mt = plan_module_with_role(&mut ct, &m, &crate::telemetry::ConfiguredTelemetry::new(), "test");
    assert!(
        mt.dead_branches.values().any(|d| matches!(d, DeadBranch::Else)),
        "expected an Else dead branch for {{a,b}} = {{1,2}}; got {:?}",
        mt.dead_branches
    );

    // Recursive sum — with `[]` and `[_ | _]` modeled as disjoint
    // shapes, clause-dispatch branches can be proven dead per
    // specialized dispatch block.
    let m2 = lower_src(
        concat!(
            "fn sum([]), do: 0\n",
            "fn sum([h | t]), do: h + sum(t)\n",
            "fn main(), do: sum([1, 2, 3])\n",
        ),
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let mt2 = plan_module_with_role(&mut ct, &m2, &crate::telemetry::ConfiguredTelemetry::new(), "test");
    let sum_fid = m2.fn_by_name("sum").expect("sum exists").id;
    assert!(
        mt2.specs
            .iter()
            .any(|(key, spec)| key.fn_id == sum_fid && !spec.dead_branches.is_empty()),
        "sum/1 should keep per-spec dead clause-dispatch facts with explicit list shapes; got {:?}",
        mt2.specs
            .iter()
            .filter(|(key, _)| key.fn_id == sum_fid)
            .map(|(key, spec)| (key, &spec.dead_branches))
            .collect::<Vec<_>>()
    );
}

/// fz-fyq.1 — every lowering path that synthesizes a `Term::If` tags it
/// with the right `BranchOrigin`. Cover one source program that exercises
/// each origin and assert the right set appears in the lowered module.
#[test]
fn branch_origin_tagged_per_lowering_path() {
    let m = lower_src(
        concat!(
            // ParamGuard: typed param synthesizes a TypeTest If.
            "fn f(x :: integer), do: x\n",
            // ClauseDispatch (multi-clause): two clauses on a literal.
            "fn g(0), do: :zero\n",
            "fn g(_), do: :other\n",
            // PatternBind: `{a, b} = ...` synthesizes Ifs that check tuple arity.
            "fn h() do\n",
            "  {a, b} = {1, 2}\n",
            "  a + b\n",
            "end\n",
            // User: hand-written `if`.
            "fn i(n), do: if n > 0, do: 1, else: 0\n",
        ),
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let mut seen: HashSet<BranchOrigin> = HashSet::new();
    for f in &m.fns {
        for b in &f.blocks {
            if let Term::If { origin, .. } = &b.terminator {
                seen.insert(*origin);
            }
        }
    }
    assert!(seen.contains(&BranchOrigin::User), "missing User: {:?}", seen);
    assert!(
        seen.contains(&BranchOrigin::PatternBind),
        "missing PatternBind: {:?}",
        seen
    );
    assert!(
        seen.contains(&BranchOrigin::ClauseDispatch),
        "missing ClauseDispatch: {:?}",
        seen,
    );
    assert!(
        seen.contains(&BranchOrigin::ParamGuard),
        "missing ParamGuard: {:?}",
        seen,
    );
}

#[test]
fn multi_clause_dispatch_lowers_dispatch_graph_inline() {
    // fz-puj.52.7 — multi-clause fns lower the DispatchGraph inline
    // into the user fn again so dispatch does not become a separate
    // spec-producing matcher fn.
    let m = lower_src(
        "fn fact(0), do: 1\nfn fact(n), do: n * fact(n - 1)",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(!s.contains("fact_matcher_"), "did not expect fact_matcher_N fn: {}", s);
    assert!(s.contains("if v"), "expected pattern test If: {}", s);
    assert!(s.contains("halt v"), "expected halt in fail block:\n{}", s);
    assert!(s.contains(":atom_"), "expected interned atom in fail block:\n{}", s);
}

#[test]
fn lower_lambda_creates_separate_fn_and_closure() {
    let m = lower_src(
        "fn mk(x), do: fn(y) -> x + y end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("closure(fn"), "expected closure prim, got:\n{}", s);
    assert!(s.contains("lambda_"), "expected lambda fn name: {}", s);
    assert!(
        m.fns.len() >= 2,
        "expected ≥2 fns (mk + lambda + prelude), got {}",
        m.fns.len()
    );
    assert!(m.fns.iter().any(|f| f.name == "mk"), "expected 'mk' fn");
    assert!(
        m.fns.iter().any(|f| f.name.starts_with("lambda_")),
        "expected lambda fn"
    );
}

#[test]
fn lower_named_fn_ref_emits_thin_fn_ref_prim() {
    let m = lower_src(
        "fn id(x), do: x\nfn main(), do: &id/1",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let main = m.fn_by_name("main").expect("main fn missing");
    let fn_id = first_make_fn_ref(main);

    assert_eq!(m.fn_by_id(fn_id).name, "id");
    assert_eq!(count_prims_in_fn(main, |prim| matches!(prim, Prim::MakeClosure(..))), 0);
}

#[test]
fn lower_bare_top_level_fn_value_emits_thin_fn_ref_prim() {
    let m = lower_src(
        "fn id(x), do: x\nfn main(), do: id",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let main = m.fn_by_name("main").expect("main fn missing");
    let fn_id = first_make_fn_ref(main);

    assert_eq!(m.fn_by_id(fn_id).name, "id");
    assert_eq!(count_prims_in_fn(main, |prim| matches!(prim, Prim::MakeClosure(..))), 0);
}

#[test]
fn lower_lambda_captures_only_referenced_outer_names() {
    let m = lower_src(
        "fn mk(x, y), do: fn(z) -> x + z end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let mk = m.fn_by_name("mk").expect("mk fn missing");
    let (lambda_id, captured) = first_make_closure(mk);

    assert_eq!(
        captured.len(),
        1,
        "lambda body reads x but not y, so only x should be captured"
    );

    let lambda = m.fn_by_id(lambda_id);
    assert_eq!(
        lambda.block(lambda.entry).params.len(),
        2,
        "entry params should be [captured x, lambda arg z]"
    );
}

#[test]
fn lower_lambda_with_no_outer_reads_has_no_captures() {
    let m = lower_src(
        "fn mk(x), do: fn(y) -> y + 1 end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let mk = m.fn_by_name("mk").expect("mk fn missing");
    let lambda_id = first_make_fn_ref(mk);

    assert_eq!(
        count_prims_in_fn(mk, |prim| matches!(prim, Prim::MakeClosure(..))),
        0,
        "lambda body reads no outer names, so it should lower as a thin fn ref"
    );

    let lambda = m.fn_by_id(lambda_id);
    assert_eq!(
        lambda.block(lambda.entry).params.len(),
        1,
        "entry params should contain only lambda arg y"
    );
}

/// A direct `dbg(x)` call is an identity expression with a side-effecting
/// `fz_dbg_value(any)` extern. It must not create a call edge to the
/// polymorphic runtime-library wrapper, or the planner specializes the
/// wrapper and its trivial continuations once per concrete argument type.
#[test]
fn dbg_call_lowers_to_identity_extern_intrinsic() {
    let m = lower_src("fn p(), do: dbg(1)", &crate::telemetry::ConfiguredTelemetry::new());
    let p = m.fn_by_name("p").expect("p fn missing");
    let entry = p.block(p.entry);
    let (extern_dest, eid, args) = entry
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            Stmt::Let(dest, Prim::Extern(_, eid, args)) => Some((*dest, *eid, args.as_slice())),
            _ => None,
        })
        .expect("direct dbg call should lower to a Prim::Extern");
    let decl = m.extern_by_id(eid);

    assert_eq!(decl.fz_name, "Kernel.fz_dbg_value");
    assert_eq!(decl.symbol, "fz_dbg_value");
    assert_eq!(decl.params, vec![ExternTy::Any]);
    assert_eq!(decl.ret, ExternTy::Any);
    assert_eq!(args.len(), 1);
    assert_eq!(args[0].marshal, ExternMarshal::Fixed(ExternTy::Any));
    let Term::Return(returned) = entry.terminator else {
        panic!("expected p to return dbg's input value, got {:?}", entry.terminator);
    };
    assert_eq!(returned, args[0].var);
    assert_ne!(
        extern_dest, returned,
        "direct dbg returns the source value, not the extern's any result"
    );
}

/// Function references still target the runtime-library wrapper, because a
/// named callable needs a stable `FnId`; only direct source calls are
/// intrinsic-lowered.
#[test]
fn dbg_function_reference_routes_through_runtime_fz_wrapper() {
    let m = lower_src("fn p(), do: &dbg/1", &crate::telemetry::ConfiguredTelemetry::new());
    let dbg = m
        .fns
        .iter()
        .find(|f| f.name == "Kernel.dbg" && f.block(f.entry).params.len() == 1)
        .expect("Kernel.dbg/1 prelude fn missing");
    let p = m.fn_by_name("p").expect("p fn missing");
    let fn_id = first_make_fn_ref(p);

    assert_eq!(fn_id, dbg.id);
}

/// `spawn(x)` routes through the runtime.fz prelude import to
/// `Kernel.spawn/1`, whose implementation owns the raw extern.
#[test]
fn spawn_callsite_routes_through_runtime_fz_wrapper() {
    let m = lower_src(
        "fn child(), do: 0\nfn p() do spawn(child) end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    assert!(
        !m.fns.iter().any(|f| f.name == "fz_spawn_thunk"),
        "spawn must not synthesize fz_spawn_thunk; fns: {:?}",
        m.fns.iter().map(|f| &f.name).collect::<Vec<_>>()
    );
    let spawn = m
        .fns
        .iter()
        .find(|f| f.name == "Kernel.spawn" && f.block(f.entry).params.len() == 1)
        .expect("Kernel.spawn/1 prelude fn missing");
    let p = m.fn_by_name("p").expect("p fn missing");
    let entry = p.block(p.entry);
    let Term::TailCall { callee, .. } = entry.terminator else {
        panic!("expected p to tail-call spawn/1, got {:?}", entry.terminator);
    };
    assert_eq!(callee, spawn.id);
    assert!(
        spawn.blocks.iter().any(|b| b.stmts.iter().any(|stmt| {
            let Stmt::Let(_, prim) = stmt;
            matches!(prim, Prim::Extern(_, _, _))
        })),
        "Kernel.spawn/1 must call its runtime extern"
    );
}

#[test]
fn spawn_wrapper_extern_keeps_intrinsic_boundary_identity() {
    let m = lower_src(
        "fn child(), do: nil\nfn main() do spawn(child) end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let spawn = m
        .fns
        .iter()
        .find(|f| f.name == "Kernel.spawn" && f.block(f.entry).params.len() == 1)
        .expect("Kernel.spawn/1 prelude fn missing");
    let (ident, args) = spawn
        .blocks
        .iter()
        .flat_map(|block| block.stmts.iter())
        .find_map(|stmt| match stmt {
            Stmt::Let(_, Prim::Extern(ident, _, args)) => Some((ident, args.as_slice())),
            _ => None,
        })
        .expect("Kernel.spawn/1 must contain a runtime extern");

    assert_eq!(args.len(), 1, "spawn wrapper should pass exactly one callable");
    assert_ne!(
        ident.span(),
        Span::DUMMY,
        "runtime extern boundary must carry an intrinsic callsite span"
    );
}

#[test]
fn lambda_tail_receive_does_not_terminate_enclosing_spawn_call() {
    let m = lower_src(
        "fn p(parent) do\nspawn(fn () -> send(parent, receive do x -> x end) end)\nend",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let p = m.fn_by_name("p").expect("p fn missing");
    let entry = p.block(p.entry);
    let spawn = m
        .fns
        .iter()
        .find(|f| f.name == "Kernel.spawn" && f.block(f.entry).params.len() == 1)
        .expect("Kernel.spawn/1 prelude fn missing");
    let callee = match entry.terminator {
        Term::TailCall { callee, .. } => callee,
        ref other => panic!("expected enclosing fn to tail-call spawn/1, got {:?}", other),
    };
    assert_eq!(callee, spawn.id);
    assert!(
        !p.blocks
            .iter()
            .any(|b| matches!(b.terminator, Term::ReceiveMatched { .. })),
        "lambda lowering must not leak receive termination into the caller"
    );
}

/// `spawn/2` follows the same prelude-import path as `spawn/1`.
#[test]
fn spawn2_routes_through_runtime_fz_wrapper() {
    let m = lower_src(
        "fn child(), do: 0\nfn p() do spawn(child, 4096) end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    assert!(
        !m.fns.iter().any(|f| f.name == "fz_spawn_thunk"),
        "spawn/2 must not synthesize fz_spawn_thunk"
    );
    let spawn = m
        .fns
        .iter()
        .find(|f| f.name == "Kernel.spawn" && f.block(f.entry).params.len() == 2)
        .expect("Kernel.spawn/2 prelude fn missing");
    let p = m.fn_by_name("p").expect("p fn missing");
    let entry = p.block(p.entry);
    let Term::TailCall { callee, .. } = entry.terminator else {
        panic!("expected p to tail-call spawn/2, got {:?}", entry.terminator);
    };
    assert_eq!(callee, spawn.id);
    assert!(
        spawn.blocks.iter().any(|b| b.stmts.iter().any(|stmt| {
            let Stmt::Let(_, prim) = stmt;
            matches!(prim, Prim::Extern(_, _, _))
        })),
        "Kernel.spawn/2 must call its runtime extern"
    );
}

/// The lowerer no longer synthesizes fz_spawn_thunk for any program.
#[test]
fn spawn_free_program_has_no_compiler_spawn_thunk() {
    let m = lower_src("fn p(), do: 0", &crate::telemetry::ConfiguredTelemetry::new());
    assert!(
        !m.fns.iter().any(|f| f.name == "fz_spawn_thunk"),
        "expected no compiler-synthesized fz_spawn_thunk"
    );
}

#[test]
fn unbound_var_returns_lower_error() {
    let err = lower_src_err("fn f(), do: missing", &crate::telemetry::ConfiguredTelemetry::new());
    assert!(matches!(err, LowerError::Unbound { .. }));
}

/// .21 step 3: lower errors carry a real Span of the offending node,
/// not Span::DUMMY.
#[test]
fn unbound_var_diag_has_real_span() {
    let err = lower_src_err("fn f(), do: missing", &crate::telemetry::ConfiguredTelemetry::new());
    let d = err.to_diagnostic();
    assert_ne!(
        d.primary.span,
        Span::DUMMY,
        "lower diagnostic should carry the unbound Var's span"
    );
    assert_eq!(d.code, codes::LOWER_UNBOUND);
}

#[test]
fn unbound_callee_returns_lower_error() {
    let err = lower_src_err("fn f(), do: nonesuch(1)", &crate::telemetry::ConfiguredTelemetry::new());
    assert!(matches!(err, LowerError::Unbound { .. }));
}

#[test]
fn empty_case_returns_unsupported() {
    let err = lower_src_err(
        "fn f() do case 1 do end end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    assert!(matches!(err, LowerError::Unsupported { .. }));
}

#[test]
fn map_lowers_to_make_map() {
    let m = lower_src("fn m(), do: %{k: 1}", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("map({"), "got:\n{}", s);
}

#[test]
fn map_update_lowers() {
    let m = lower_src(
        "fn u(m), do: %{m | k: 2}",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("map_update("), "got:\n{}", s);
}

#[test]
fn index_lowers_to_map_get() {
    let m = lower_src("fn g(m), do: m[:k]", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("map_get("), "got:\n{}", s);
}

#[test]
fn bitstring_expr_lowers() {
    let m = lower_src("fn b(), do: << 0xA5 >>", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("bitstring(["), "got:\n{}", s);
}

#[test]
fn case_lowers_dispatch_graph_inline() {
    // fz-puj.52.7 — case sites lower the DispatchGraph inline so the
    // planner does not see a case_matcher_N function boundary.
    let m = lower_src(
        r#"
fn c(x) do
  case x do
0 -> :zero
_ -> :other
  end
end
"#,
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(
        !s.contains("case_matcher_"),
        "did not expect case_matcher_N fn in module dump: {}",
        s
    );
    assert!(s.contains("if v"), "expected if for inline pattern check: {}", s);
    assert!(s.contains("tail_call"), "expected tail_call to clause cont fns: {}", s);
}

#[test]
fn cond_lowers() {
    // cond is parsed; lowering should emit If terminators.
    let m = lower_src(
        r#"
fn c(x) do
  cond do
x > 0 -> :pos
true -> :nonpos
  end
end
"#,
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("if v"), "got:\n{}", s);
}

#[test]
fn with_simple_lowers() {
    let m = lower_src(
        r#"
fn w() do
  with {:ok, a} <- {:ok, 1}, do: a
end
"#,
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("tuple_field"), "expected pattern projection: {}", s);
}

#[test]
fn map_pattern_uses_map_get_check() {
    let m = lower_src(
        "fn first(%{name: n}), do: n",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let s = format!("{}", m);
    assert!(s.contains("map_get("), "got:\n{}", s);
}

#[test]
fn inline_dispatch_reuses_tuple_subject_across_test_guard_and_binding() {
    let m = lower_src(
        "fn positive(n), do: n > 0
         fn classify(t) do
           case t do
             {:ok, x} when positive(x) -> x + x
             _ -> 0
           end
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );

    let classify = m.fn_by_name("classify").expect("classify fn");
    let field_1_count = count_prims_in_fn(classify, |prim| matches!(prim, Prim::TupleField(_, 1)));
    assert_eq!(
        field_1_count, 1,
        "tuple field used by guard and binding should materialize once:\n{}",
        m
    );
}

#[test]
fn inline_dispatch_reuses_list_head_across_guard_and_binding() {
    let m = lower_src(
        "fn positive(n), do: n > 0
         fn classify(xs) do
           case xs do
             [h | _] when positive(h) -> h + h
             _ -> 0
           end
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );

    let classify = m.fn_by_name("classify").expect("classify fn");
    let head_count = count_prims_in_fn(classify, |prim| matches!(prim, Prim::ListHead(_)));
    assert_eq!(
        head_count, 1,
        "list head used by guard and binding should materialize once:\n{}",
        m
    );
}

#[test]
fn inline_dispatch_reuses_map_value_across_guard_and_binding() {
    let m = lower_src(
        "fn positive(n), do: n > 0
         fn classify(m) do
           case m do
             %{id: x} when positive(x) -> x + x
             _ -> 0
           end
         end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );

    let map_get_count = count_prims(&m, |prim| matches!(prim, Prim::MatcherMapGet(_, _)));
    assert_eq!(
        map_get_count, 1,
        "map value used by guard and binding should materialize once:\n{}",
        m
    );
}

#[test]
fn bitstring_pattern_lowers_to_per_field_reads() {
    let m = lower_src("fn p(<<x::8>>), do: x", &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("bit_reader_init("), "got:\n{}", s);
    assert!(s.contains("bit_read_field("), "got:\n{}", s);
    assert!(s.contains("bit_reader_done("), "got:\n{}", s);
}

#[test]
fn quote_returns_post_expansion_node() {
    // Skip macro expansion to surface the leftover-quote error path.
    let err = lower_src_err("fn f(), do: quote do: 1", &crate::telemetry::ConfiguredTelemetry::new());
    assert!(matches!(err, LowerError::PostExpansionNode { .. }));
}

/// Span round-trip: AST nodes parsed by the parser carry non-DUMMY spans
/// that slice back to their source lexemes.
#[test]
fn parser_attaches_real_spans_to_expressions() {
    let src = "fn ident(x), do: x + 1";
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let Item::Fn(def) = &*prog.items[0] else {
        panic!("expected fn")
    };
    // The body `x + 1` is a BinOp; its span should be non-DUMMY and
    // slice to the operator-bracketed substring.
    let body = &def.clauses[0].body;
    assert!(!body.span.is_dummy());
    let lexeme = &src[body.span.start as usize..body.span.end as usize];
    assert!(
        lexeme.contains('+'),
        "body span should cover the binop expression, got {:?}",
        lexeme
    );
}

/// FnDef.name_span pinpoints the source name token (not the whole def).
#[test]
fn parser_records_fn_name_span() {
    let src = "fn foobar(), do: 0";
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let Item::Fn(def) = &*prog.items[0] else {
        panic!("expected fn")
    };
    let name_text = &src[def.name_span.start as usize..def.name_span.end as usize];
    assert_eq!(name_text, "foobar");
}

// ----- .20.4: SourceInfo side-tables -----

/// Pattern-bound parameters record their name + binding span in
/// `Module.source`. The ticket's canonical test: lower a `double(x)`
/// function and verify the param's Var → "x", span → the `x` token.
#[test]
fn pattern_var_records_source_name_and_span() {
    let src = "fn double(x), do: x * 2";
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let m = lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower");
    let f = m.fn_by_name("double").unwrap();
    let param = f.blocks[0].params[0];
    assert_eq!(m.source.var_name_of(param), Some("x"));
    let sp = m.source.var_span_of(param);
    assert!(!sp.is_dummy());
    let txt = &src[sp.start as usize..sp.end as usize];
    assert_eq!(txt, "x");
}

/// Every top-level fn gets its source span recorded under
/// `fn_span[fn_id.0]`.
#[test]
fn fn_span_records_def_position() {
    let src = "fn alpha(), do: 1\nfn beta(), do: 2";
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let m = lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower");
    let beta = m.fn_by_name("beta").unwrap();
    let sp = m.source.fn_span_of(beta.id);
    let txt = &src[sp.start as usize..sp.end as usize];
    assert!(txt.starts_with("fn beta"));
}

/// CPS continuations created when a non-tail Call splits use the
/// originating call expression's span as their `fn_span`, so a
/// diagnostic on the continuation can point at where the work
/// originated in source.
#[test]
fn continuation_fn_span_points_at_originating_call() {
    // `callee(x) + 1` forces a non-tail Call -> CPS split.
    let src = "fn callee(y), do: y\nfn caller(x), do: callee(x) + 1";
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let m = lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower");
    let caller = m.fn_by_name("caller").unwrap();
    // The continuation fn is the one whose name starts with "k_".
    // Filter out continuations from the runtime.fz prelude (e.g.
    // Utf8.from_bytes also CPS-splits) by checking FnCategory.
    let k = m
        .fns
        .iter()
        .find(|f| f.name.starts_with("k_") && f.category == FnCategory::CpsCont && f.id.0 >= caller.id.0)
        .expect("expected a continuation fn in user code");
    let cont_span = m.source.fn_span_of(k.id);
    assert!(!cont_span.is_dummy());
    // The originating call is `callee(x)` inside `caller`'s body.
    // The continuation's fn_span must be inside caller's source range.
    let caller_span = m.source.fn_span_of(caller.id);
    assert!(
        cont_span.start >= caller_span.start && cont_span.end <= caller_span.end,
        "continuation span {:?} should lie within caller's range {:?}",
        cont_span,
        caller_span
    );
    let txt = &src[cont_span.start as usize..cont_span.end as usize];
    assert!(
        txt.contains("callee"),
        "continuation span should cover the originating call, got {:?}",
        txt
    );
}

/// Compiler-introduced Vars (constants, tuple projections, etc.)
/// keep their source-expression span on `var_span` and an empty
/// name on `var_name`. .20.8's diagnostic renderer uses the empty-
/// name signal to render "this value" instead of "`<name>`".
#[test]
fn temp_var_records_span_and_empty_name() {
    // `x + 1` produces a Const(1) Var whose source position is the
    // literal `1` in the body.
    let src = "fn add_one(x), do: x + 1";
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let m = lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower");
    let f = m.fn_by_name("add_one").unwrap();
    // Find a Var bound to `Const(Int(1))`.
    let mut const1_var: Option<Var> = None;
    for blk in &f.blocks {
        for s in &blk.stmts {
            let Stmt::Let(v, prim) = s;
            if matches!(prim, Prim::Const(Const::Int(1))) {
                const1_var = Some(*v);
            }
        }
    }
    let v = const1_var.expect("Const(1) Var");
    // No source name on this temp.
    assert_eq!(m.source.var_name_of(v), None);
    // But its span points at the `1` literal.
    let sp = m.source.var_span_of(v);
    let txt = &src[sp.start as usize..sp.end as usize];
    assert_eq!(txt, "1");
}

#[test]
fn self_recursive_fn_has_back_edge() {
    // fz-qbg.2: with multi-clause body cont fns, prelude multi-clause
    // fns (`print`) contribute TailCalls to their per-clause
    // cont fns earlier in module order. Look up `loop` specifically
    // rather than the first TailCall anywhere.
    let m = lower_src("fn loop(n), do: loop(n)", &crate::telemetry::ConfiguredTelemetry::new());
    let loop_fn = m.fn_by_name("loop").expect("loop fn missing");
    let (callee, is_back_edge) = loop_fn
        .blocks
        .iter()
        .find_map(|b| {
            if let Term::TailCall {
                ident: _,
                callee,
                is_back_edge,
                ..
            } = &b.terminator
            {
                Some((*callee, *is_back_edge))
            } else {
                None
            }
        })
        .expect("no TailCall in loop");
    assert!(is_back_edge, "self-recursion must be a back-edge; callee={:?}", callee);
}

#[test]
fn non_recursive_call_is_not_back_edge() {
    let m = lower_src(
        "fn id(x), do: x\nfn main(), do: id(1)",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    // Find the TailCall from main to id.
    let mut found = false;
    for f in &m.fns {
        if f.name == "main" {
            for b in &f.blocks {
                if let Term::TailCall { is_back_edge, .. } = &b.terminator {
                    assert!(!is_back_edge, "non-recursive call must NOT be back-edge");
                    found = true;
                }
            }
        }
    }
    assert!(found, "no TailCall from main");
}

#[test]
fn extern_fn_registers_in_module_externs() {
    let toks = Lexer::with_source_name(
        "extern \"C\" fn fz_nop(any) :: nil\nfn main() do fz_nop(1) end\n",
        "<test>",
    )
    .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
    .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let module = lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower");
    // fz_nop is at the end (user externs follow runtime.fz externs).
    let nop = module
        .externs
        .iter()
        .find(|e| e.fz_name == "fz_nop")
        .expect("fz_nop not found in externs");
    assert_eq!(nop.id.0 + 1, module.externs.len() as u32);
    assert_eq!(nop.params, vec![ExternTy::Any]);
    assert_eq!(nop.ret, ExternTy::Unit);
    // main's IR references fz_nop as the last (user) extern — its index
    // moves whenever runtime.fz grows. The test inspects only that
    // it lands in extern position #(externs.len()-1).
    let last_extern_idx = module.externs.len() - 1;
    let ir = format!("{}", module);
    let needle = format!("extern#{}", last_extern_idx);
    assert!(ir.contains(&needle), "expected {} in IR:\n{}", needle, ir);
}

/// fz-0cv — `binary` lowers to ExternTy::Binary; `cstring` lowers to
/// ExternTy::CString. Both are distinct from ExternTy::Any.
#[test]
fn binary_and_cstring_lower_to_distinct_extern_tys() {
    let src = "\
extern \"C\" fn fz_open(cstring, integer) :: integer
extern \"C\" fn fz_write(integer, binary, integer) :: integer
fn main() do fz_open(\"x\", 0) end
";
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let module = lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower");
    let open = module
        .externs
        .iter()
        .find(|e| e.fz_name == "fz_open")
        .expect("fz_open missing");
    assert_eq!(open.params, vec![ExternTy::CString, ExternTy::I64]);
    let write = module
        .externs
        .iter()
        .find(|e| e.fz_name == "fz_write")
        .expect("fz_write missing");
    assert_eq!(write.params, vec![ExternTy::I64, ExternTy::Binary, ExternTy::I64]);
    // Sanity: previous `binary` → ExternTy::Any mapping is gone.
    assert_ne!(write.params[1], ExternTy::Any);
}

/// fz-eol — `&libc::close/1` resolves to a synthesized top-level
/// wrapper fn whose body contains a single `Prim::Extern` call. This
/// is the canonical shape `resolve_dtor_from_closure` walks at
/// runtime so `make_resource(_, &libc::close/1)` resolves to
/// libc::close. The wrapper has zero captures so the AOT static dtor
/// table accepts it.
#[test]
fn fn_ref_to_extern_synthesizes_wrapper() {
    let src = "\
extern \"C\" fn libc::close(integer) :: integer
fn main() do &libc::close/1 end
";
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let module = lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower");
    let wrap = module
        .fns
        .iter()
        .find(|f| f.name.contains("libc::close"))
        .expect("synthesized wrapper not found");
    let has_extern = wrap
        .blocks
        .iter()
        .any(|b| b.stmts.iter().any(|s| matches!(s, Stmt::Let(_, Prim::Extern(_, _, _)))));
    assert!(
        has_extern,
        "wrapper fn must contain a Prim::Extern statement; got: {}",
        wrap.name
    );
}

/// fz-y3k — `extern "C" fn libc::open(path :: cstring, integer) :: integer`
/// produces an extern whose fz_name carries the `libc::` prefix while
/// the linker-visible symbol is the bare last segment. Named-typed
/// params (`path :: cstring`) parse identically to positional ones.
#[test]
fn extern_with_library_prefix_splits_fz_name_from_symbol() {
    let src = "\
extern \"C\" fn libc::open(path :: cstring, integer) :: integer
fn main() do libc::open(\"x\", 0) end
";
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let module = lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower");
    let open = module
        .externs
        .iter()
        .find(|e| e.fz_name == "libc::open")
        .expect("libc::open missing from module.externs");
    assert_eq!(open.symbol, "open", "linker symbol is the bare suffix");
    assert_eq!(open.params, vec![ExternTy::CString, ExternTy::I64]);
}

/// fz-jex — calling an extern with the wrong arg count must produce a
/// LowerError at compile time, not a silent codegen truncation that
/// panics at runtime in fz_unbox_int with a tag mismatch.
#[test]
fn extern_call_arity_mismatch_is_lower_error() {
    let src = "\
extern \"C\" fn libc::open(path :: cstring, integer, integer) :: integer
fn main() do libc::open(\"x\", \"x\", 0, 0) end
";
    let err = lower_src_err(src, &crate::telemetry::ConfiguredTelemetry::new());
    match err {
        LowerError::Unsupported { what, .. } => {
            assert!(
                what.contains("open") && what.contains("3") && what.contains("4"),
                "expected arity-mismatch message naming open/3 vs 4 args, got: {}",
                what
            );
        }
        other => panic!("expected Unsupported arity error, got {:?}", other),
    }
}

#[test]
fn variadic_extern_records_decl_and_call_marshal_specs() {
    let src = "\
extern \"C\" fn libc::open(path :: cstring, flags :: integer, ...) :: integer
fn main() do libc::open(\"x\", 0, 0o644 :: integer) end
";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    let open = m
        .externs
        .iter()
        .find(|e| e.fz_name == "libc::open")
        .expect("libc::open missing");
    assert!(open.variadic);
    assert_eq!(open.params, vec![ExternTy::CString, ExternTy::I64]);

    let main = m.fn_by_name("main").expect("main missing");
    let extern_args = main
        .blocks
        .iter()
        .flat_map(|b| b.stmts.iter())
        .find_map(|s| match s {
            Stmt::Let(_, Prim::Extern(_, _, args)) => Some(args),
            _ => None,
        })
        .expect("extern call missing");
    assert_eq!(extern_args.len(), 3);
    assert_eq!(extern_args[0].marshal, ExternMarshal::Fixed(ExternTy::CString));
    assert_eq!(extern_args[1].marshal, ExternMarshal::Fixed(ExternTy::I64));
    assert_eq!(extern_args[2].marshal, ExternMarshal::Ascribed(ExternTy::I64));
}

#[test]
fn variadic_extern_unascribed_extra_arg_stays_auto() {
    let src = "\
extern \"C\" fn libc::printf(fmt :: cstring, ...) :: integer
fn main() do libc::printf(\"%d\", 7) end
";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    let main = m.fn_by_name("main").expect("main missing");
    let extern_args = main
        .blocks
        .iter()
        .flat_map(|b| b.stmts.iter())
        .find_map(|s| match s {
            Stmt::Let(_, Prim::Extern(_, _, args)) => Some(args),
            _ => None,
        })
        .expect("extern call missing");
    assert_eq!(extern_args[1].marshal, ExternMarshal::Auto);
}

#[test]
fn variadic_extern_too_few_args_is_lower_error() {
    let src = "\
extern \"C\" fn libc::open(path :: cstring, flags :: integer, ...) :: integer
fn main() do libc::open(\"x\") end
";
    let err = lower_src_err(src, &crate::telemetry::ConfiguredTelemetry::new());
    match err {
        LowerError::Unsupported { what, .. } => {
            assert!(
                what.contains("open") && what.contains("at least 2") && what.contains("1"),
                "expected variadic arity message, got: {}",
                what
            );
        }
        other => panic!("expected Unsupported arity error, got {:?}", other),
    }
}

#[test]
fn extern_id_is_stable_and_extern_idx_is_consistent() {
    let toks = Lexer::with_source_name(
        "extern \"C\" fn fz_nop(any) :: nil\nfn main() do fz_nop(1) end\n",
        "<test>",
    )
    .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
    .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let module = lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower");
    // extern_idx must have an entry for every extern.
    assert_eq!(module.extern_idx.len(), module.externs.len());
    // Each extern's id field must resolve via extern_by_id to itself.
    for (i, e) in module.externs.iter().enumerate() {
        assert_eq!(module.extern_idx[&e.id], i, "extern_idx out of sync at index {}", i);
        assert_eq!(module.extern_by_id(e.id).fz_name, e.fz_name);
    }
    // ExternIds are monotonically increasing (counter-based, not len()-based).
    let ids: Vec<u32> = module.externs.iter().map(|e| e.id.0).collect();
    assert!(
        ids.windows(2).all(|w| w[0] < w[1]),
        "ExternIds not monotonic: {:?}",
        ids
    );
}

/// fz-f88.5 — every lowered FnIr carries an origin category. This
/// test pins the contract: prelude fns are `Prelude`, user fns are
/// `User`, and the well-known synthesized cont families
/// (fn_clause_, k_, lambda_, if_, case_) map to their respective
/// variants based on name prefix.
#[test]
fn fn_category_tags_match_origin() {
    // Mix user fns covering: multi-clause dispatch (-> MultiClauseCont),
    // CPS-split via non-tail call (-> CpsCont), and lambda lifting
    // (-> LambdaLift).
    let src = "\
fn id(x), do: x
fn pick(:a), do: 1
fn pick(:b), do: 2
fn make_adder(x), do: fn (z) -> x + z end

fn main() do
  id(pick(:a))
  make_adder(1)
end
";
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let module = lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower");

    let user_names = ["id", "pick", "make_adder", "main"];
    for f in &module.fns {
        let expected = if user_names.contains(&f.name.as_str()) {
            FnCategory::User
        } else if f.name.starts_with("fn_clause_") {
            FnCategory::MultiClauseCont
        } else if f.name.starts_with("lambda_") {
            FnCategory::LambdaLift
        } else if f.name.starts_with("k_") {
            FnCategory::CpsCont
        } else if f.name.contains("_matcher_") {
            // Internal matchers are no longer production lowering
            // artifacts, but keep the category rule for any explicit
            // matcher helper tests that construct such fns.
            FnCategory::Matcher
        } else if f.name.starts_with("if_")
            || f.name.starts_with("case_")
            || f.name.starts_with("cond_")
            || f.name.starts_with("with_")
        {
            FnCategory::ControlFlowCont
        } else {
            // Anything else must be prelude lowered from runtime.fz.
            FnCategory::Prelude
        };
        assert_eq!(
            f.category, expected,
            "{} (id {}) categorized as {:?}, expected {:?}",
            f.name, f.id.0, f.category, expected,
        );
    }
}

// fz-puj.52.7 — internal case / multi-clause / with-else dispatch no
// longer mints production matcher fns. Receive remains the ABI-driven
// matcher-fn path.

// ----- fz-puj.36 (H7) — SourcePatternRows construction from receive clauses -----

fn parse_receive_clauses(src: &str, tel: &dyn Telemetry) -> Vec<MatchClause> {
    let toks = Lexer::with_source_name(src, "<test>").tokenize(tel).expect("lex");
    let prog = Parser::new(toks).parse_program(tel).expect("parse");
    fn find_receive(e: &Expr) -> Option<&Vec<MatchClause>> {
        match e {
            Expr::Receive { clauses, .. } => Some(clauses),
            Expr::Block(es) => es.iter().find_map(|s| find_receive(&s.node)),
            _ => None,
        }
    }
    for item in &prog.items {
        if let Item::Fn(fd) = item.as_ref() {
            for clause in &fd.clauses {
                if let Some(rxs) = find_receive(&clause.body.node) {
                    return rxs.clone();
                }
            }
        }
    }
    panic!("no receive clauses found in source");
}

#[test]
fn build_receive_pattern_rows_one_clause_shape() {
    let clauses = parse_receive_clauses(
        "fn rx() do receive do {:ping, _} -> :pong end end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let source_patterns = build_receive_pattern_rows(Var(0), &clauses);
    assert_eq!(source_patterns.subjects, vec![Var(0)]);
    assert_eq!(source_patterns.rows.len(), 1);
    assert_eq!(source_patterns.rows[0].patterns.len(), 1);
    assert!(source_patterns.rows[0].preconditions.is_empty());
    assert!(source_patterns.rows[0].guard.is_none());
    assert_eq!(source_patterns.rows[0].body_id, 0);
}

#[test]
fn build_receive_pattern_rows_multi_clause_preserves_order_and_ids() {
    let clauses = parse_receive_clauses(
        "fn rx() do receive do
            :ping -> :pong
            {:msg, _} -> :ok
            _ -> :other
        end end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let source_patterns = build_receive_pattern_rows(Var(7), &clauses);
    assert_eq!(source_patterns.subjects, vec![Var(7)]);
    assert_eq!(source_patterns.rows.len(), 3);
    for (i, row) in source_patterns.rows.iter().enumerate() {
        assert_eq!(row.body_id, i as PatternBodyId);
        assert_eq!(row.patterns.len(), 1);
        assert!(row.preconditions.is_empty());
    }
}

#[test]
fn build_receive_pattern_rows_carries_guard() {
    let clauses = parse_receive_clauses(
        "fn rx() do receive do
            n when n > 0 -> :positive
            _ -> :other
        end end",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let source_patterns = build_receive_pattern_rows(Var(0), &clauses);
    assert_eq!(source_patterns.rows.len(), 2);
    assert!(
        source_patterns.rows[0].guard.is_some(),
        "first clause's `when n > 0` guard must appear in row[0].guard"
    );
    assert!(source_patterns.rows[1].guard.is_none());
}

#[test]
fn case_guard_with_pure_user_fn_inlines_and_lowers() {
    let src = "fn is_pos(n) do n > 0 end
               fn main() do
                 case 5 do
                   n when is_pos(n) -> :pos
                   _ -> :neg
                 end
               end";
    let _ = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
}

#[test]
fn case_guard_with_multi_clause_user_fn_lowers_dispatch() {
    let src = "fn is_pos(0) do false end
               fn is_pos(n) do n > 0 end
               fn main() do
                 case 5 do
                   n when is_pos(n) -> dbg(1)
                   _ -> dbg(0)
                 end
               end";
    assert_eq!(
        run_and_capture(src, &crate::telemetry::ConfiguredTelemetry::new()).trim(),
        "1"
    );
}

#[test]
fn guarded_list_cons_clause_survives_compiled_folding() {
    let src = "fn partition(_, [], lo, hi), do: {lo, hi}
               fn partition(p, [h | t], lo, hi) when h < p, do: partition(p, t, [h | lo], hi)
               fn partition(p, [h | t], lo, hi), do: partition(p, t, lo, [h | hi])
               fn main() do dbg(partition(3, [1, 4, 2], [], [])) end";
    assert_eq!(
        run_and_capture(src, &crate::telemetry::ConfiguredTelemetry::new()).trim(),
        "{[2, 1], [4]}"
    );
}

// ----- fz-yxs (E2) — selective receive lowering -----

#[test]
fn lower_receive_one_clause_emits_receive_matched() {
    let src = "fn loop_one() do
          receive do
            {:ping, sender} -> :pong
          end
        end";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(
        s.contains("receive_matched [1 clauses]"),
        "expected Term::ReceiveMatched, got:\n{}",
        s
    );
    assert!(
        s.contains("rx_clause_0_body"),
        "expected clause body fn name, got:\n{}",
        s
    );
}

#[test]
fn lower_receive_after_clause_emits_after_body() {
    let src = "fn rx_timeout() do
          receive do
            {:done, x} -> x
          after 100 -> :timeout
          end
        end";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(s.contains("rx_after_body"), "expected after body fn, got:\n{}", s);
    assert!(
        s.contains("after("),
        "expected after annotation on terminator, got:\n{}",
        s
    );
}

#[test]
fn lower_receive_pinned_resolves_outer_scope() {
    let src = "fn rx_pinned(want) do
          receive do
            {^want, payload} -> payload
          end
        end";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    let s = format!("{}", m);
    assert!(
        s.contains("pinned=[^want="),
        "expected pinned `want` resolved against outer scope, got:\n{}",
        s
    );
}

#[test]
fn lower_receive_pinned_unbound_is_error() {
    let src = "fn rx() do
          receive do
            {^nope, _} -> 0
          end
        end";
    let err = lower_src_err(src, &crate::telemetry::ConfiguredTelemetry::new());
    match err {
        LowerError::Unbound { name, .. } => {
            assert_eq!(name, "^nope");
        }
        other => panic!("expected Unbound(^nope), got {:?}", other),
    }
}

#[test]
fn lower_receive_planner_accepts_well_formed() {
    // Acceptance bullet: planner accepts well-formed selective receive.
    let src = "fn rx() do
          receive do
            {:ping, _} -> 1
            {:pong, _} -> 2
          end
        end";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    // Typing must not panic and must produce a ModulePlan for the
    // module. We don't pin the return type — that depends on the
    // body return type which the bodies set to const ints.
    let mut ct = crate::types::new();
    let mt = plan_module_with_role(&mut ct, &m, &crate::telemetry::ConfiguredTelemetry::new(), "test");
    // No diagnostics from the pure-guard / pure-pattern pass either.
    let diags = collect_diagnostics(&mut ct, &m, &mt, &crate::telemetry::ConfiguredTelemetry::new());
    let impure: Vec<_> = diags
        .as_slice()
        .iter()
        .filter(|d| d.code == codes::TYPE_IMPURE_RECEIVE_GUARD)
        .collect();
    assert!(impure.is_empty(), "unexpected purity diags: {:?}", impure);
}

#[test]
fn lower_receive_rejects_impure_guard() {
    // The helper body calls an extern-backed runtime fn, so it cannot
    // lower into the restricted dispatch guard subset.
    let src = "fn helper(), do: make_ref()
        fn rx() do
          receive do
            {:foo, _} when helper() -> 0
          end
        end";
    let err = lower_src_err(src, &crate::telemetry::ConfiguredTelemetry::new());
    assert!(
        format!("{:?}", err).contains("UnsupportedGuardExpr"),
        "expected restricted guard-lowering error, got {:?}",
        err
    );
}

fn first_receive_dispatch(m: &Module) -> Option<&PatternDispatchPlan> {
    for f in &m.fns {
        for b in &f.blocks {
            if let Term::ReceiveMatched { dispatch, .. } = &b.terminator {
                return Some(dispatch.as_ref());
            }
        }
    }
    None
}

fn dispatch_has_guard_dispatch(dispatch: &PatternDispatchPlan) -> bool {
    fn expr_has_dispatch(expr: &PatternGuardExpr) -> bool {
        match expr {
            PatternGuardExpr::Dispatch { .. } => true,
            PatternGuardExpr::Unary { expr, .. } => expr_has_dispatch(expr),
            PatternGuardExpr::Binary { lhs, rhs, .. } => expr_has_dispatch(lhs) || expr_has_dispatch(rhs),
            PatternGuardExpr::Const(_) | PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => false,
        }
    }
    dispatch.guards.iter().any(expr_has_dispatch)
}

#[test]
fn receive_guard_with_single_clause_helper_lowers_into_dispatch() {
    let src = "fn positive(n), do: n > 0
        fn rx() do
          receive do
            n when positive(n) -> n
            _ -> 0
          end
        end";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    let dispatch = first_receive_dispatch(&m).expect("receive dispatch");
    assert!(
        !dispatch.guards.is_empty(),
        "expected inlined helper guard in dispatch: {:#?}",
        dispatch
    );
}

#[test]
fn receive_guard_capture_walks_helper_call_args() {
    let src = "fn positive(n), do: n > 0
        fn rx(limit) do
          receive do
            n when positive(n + limit) -> n
            _ -> 0
          end
        end";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    let dispatch = first_receive_dispatch(&m).expect("receive dispatch");
    assert!(
        dispatch.pinned.iter().any(|pinned| pinned.name == "limit"),
        "expected guard call argument capture in dispatch pinned inputs: {:#?}",
        dispatch
    );
}

#[test]
fn receive_guard_with_transitive_helper_lowers_into_dispatch() {
    let src = "fn positive(n), do: n > 0
        fn wanted(n), do: positive(n)
        fn rx() do
          receive do
            n when wanted(n) -> n
            _ -> 0
          end
        end";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    let dispatch = first_receive_dispatch(&m).expect("receive dispatch");
    assert!(
        !dispatch.guards.is_empty(),
        "expected transitive helper guard in dispatch: {:#?}",
        dispatch
    );
}

#[test]
fn receive_guard_with_multi_clause_helper_lowers_dispatch() {
    let src = "fn wanted({:ok, n}), do: n > 0
        fn wanted(_), do: false
        fn rx() do
          receive do
            msg when wanted(msg) -> msg
            _ -> 0
          end
        end";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    let dispatch = first_receive_dispatch(&m).expect("receive dispatch");
    assert!(
        dispatch_has_guard_dispatch(dispatch),
        "expected multi-clause helper guard dispatch in receive dispatch: {:#?}",
        dispatch
    );
}

#[test]
fn receive_guard_helper_dispatch_handles_destructuring() {
    let src = "fn wanted({:ok, {n, _}}), do: n > 0
        fn wanted(_), do: false
        fn rx() do
          receive do
            msg when wanted(msg) -> msg
            _ -> 0
          end
        end";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    let dispatch = first_receive_dispatch(&m).expect("receive dispatch");
    assert!(
        dispatch_has_guard_dispatch(dispatch),
        "expected nested helper dispatch for destructuring helper: {:#?}",
        dispatch
    );
}

#[test]
fn receive_dispatch_prepares_heap_map_keys_outside_graph() {
    let src = "fn rx() do
          receive do
            %{\"id\" => value} -> value
            _ -> 0
          end
        end";
    let m = lower_src(src, &crate::telemetry::ConfiguredTelemetry::new());
    let dispatch = first_receive_dispatch(&m).expect("receive dispatch");
    assert_eq!(dispatch.prepared_keys, vec![DispatchConst::Utf8Binary(b"id".to_vec())]);
    let s = format!("{}", m);
    assert!(
        s.contains("pinned=[^__dispatch_key_0="),
        "expected prepared map key to be threaded as receive pinned input, got:\n{}",
        s
    );
}

// ----------------------------------------------------------------
// fz-axu.24 (M3) — brand-mint visibility gate
// ----------------------------------------------------------------

fn module_with_brand_in_fn(fn_name: &str, brand_tag: &str) -> (Module, HashMap<(FnId, BlockId), Vec<Span>>) {
    let mut b = FnBuilder::new(FnId(0), fn_name);
    let entry = b.block(vec![]);
    let bs = b.let_(entry, Prim::ConstBitstring(vec![104], 8));
    let branded = b.let_(entry, Prim::Brand(bs, brand_tag.to_string()));
    b.set_terminator(entry, Term::Halt(branded));
    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    (mb.build(), HashMap::new())
}

#[test]
fn brand_visibility_passes_for_builtin_utf8_anywhere() {
    // Built-in `utf8` (no `::` in tag) has no owner; minting it
    // from any fn — even a user module — is allowed.
    let (m, spans) = module_with_brand_in_fn("Mail.send", "utf8");
    let fn_spans = HashMap::new();
    check_brand_visibility(&mut crate::types::new(), &m, &spans, &fn_spans).expect("utf8 mint must be allowed");
}

#[test]
fn brand_visibility_passes_when_fn_owns_brand() {
    // Brand `Mail::Email` minted from fn `Mail.send` (using_module
    // = "Mail") is fine — same owner.
    let (m, spans) = module_with_brand_in_fn("Mail.send", "Mail::Email");
    let fn_spans = HashMap::new();
    check_brand_visibility(&mut crate::types::new(), &m, &spans, &fn_spans).expect("same-module mint must be allowed");
}

#[test]
fn brand_visibility_rejects_cross_module_mint() {
    // Brand `Mail::Email` minted from fn `Other.handler`
    // (using_module = "Other") must be rejected.
    let (m, spans) = module_with_brand_in_fn("Other.handler", "Mail::Email");
    let fn_spans = HashMap::new();
    let err = check_brand_visibility(&mut crate::types::new(), &m, &spans, &fn_spans)
        .expect_err("cross-module mint must be rejected");
    match err {
        LowerError::BrandMintVisibility {
            brand,
            owner_module,
            using_module,
            ..
        } => {
            assert_eq!(brand, "Mail::Email");
            assert_eq!(owner_module, "Mail");
            assert_eq!(using_module, "Other");
        }
        _ => panic!("expected BrandMintVisibility, got {:?}", err),
    }
}

#[test]
fn brand_visibility_rejects_top_level_mint_of_owned_brand() {
    // Top-level fn `main` (no module prefix) trying to mint a
    // module-owned brand is also rejected.
    let (m, spans) = module_with_brand_in_fn("main", "Mail::Email");
    let fn_spans = HashMap::new();
    let err = check_brand_visibility(&mut crate::types::new(), &m, &spans, &fn_spans)
        .expect_err("top-level mint of owned brand must be rejected");
    let diag = err.to_diagnostic();
    assert!(
        diag.message.contains("<top-level>"),
        "diag should mention top-level using_module: {}",
        diag.message,
    );
}
