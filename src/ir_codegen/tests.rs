use super::*;
use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, Module, Prim, Term};
use crate::ir_lower::lower_program;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::types::{ClosureTypes, KeySlot, Types};
use cranelift_codegen::ir::types;

// fz-yan.1 — after the runtime split, false halts as its reserved
// atom ID (2). Tests previously asserted 0 from the special-bits
// derivation; the named constant makes the new semantics explicit.
const FALSE_HALT: i64 = fz_runtime::any_value::FALSE_ATOM_ID as i64;

fn lower_src(src: &str) -> Module {
    let toks = Lexer::new(src).tokenize().expect("lex");
    let prog = Parser::new(toks).parse_program().expect("parse");
    lower_program(&mut crate::types::ConcreteTypes, &prog).expect("lower")
}

fn lower_resolved_src(src: &str) -> Module {
    let toks = Lexer::new(src).tokenize().expect("lex");
    let prog = Parser::new(toks).parse_program().expect("parse");
    let mut t = crate::types::ConcreteTypes;
    let prog = crate::resolve::flatten_modules(&mut t, prog).expect("resolve");
    lower_program(&mut t, &prog).expect("lower")
}

fn join_return_ty(
    t: &mut crate::types::ConcreteTypes,
    f: &crate::fz_ir::FnIr,
    ft: &crate::ir_planner::SpecPlan,
) -> crate::types::Ty {
    let mut joined: Option<crate::types::Ty> = None;
    for b in &f.blocks {
        if let Term::Return(v) = &b.terminator {
            let d = ft.vars.get(v).cloned().unwrap_or_else(|| t.any());
            joined = Some(match joined {
                Some(prev) => t.union(prev, d),
                None => d,
            });
        }
    }
    joined.unwrap_or_else(|| t.any())
}

/// fz-cps.1.7 — every zero-capture `MakeClosure(f, [])` target gets
/// one entry in `static_closure_targets`. Multiple `MakeClosure(f, [])`
/// sites for the same `f` share a single entry (cl_sid keyed). At
/// runtime `make_process` allocates one Box per entry; two
/// `fz_get_static_closure(cl_sid)` calls in the same Process return
/// pointer-identical results. See docs/cps-in-clif.md §8.2.
#[test]
fn static_closure_targets_registered_for_zero_cap_make_closure() {
    // fz-jg5.6: the reducer would dissolve this program to constants
    // (no MakeClosure survives). Disable it so this test exercises the
    // codegen infrastructure that handles closures *the reducer can't
    // dissolve* — opaque/runtime-driven uses.
    let src = "fn f(x), do: x + 1\n\
               fn g(x), do: x * 2\n\
               fn apply(h, x), do: h(x)\n\
               fn main() do\n\
                 print(apply(f, 1))\n\
                 print(apply(g, 2))\n\
               end";
    let m = lower_src(src);
    let compiled = crate::ir_codegen::with_reducer_disabled(|| {
        compile(
            &mut crate::types::ConcreteTypes,
            &m,
            &crate::telemetry::NullTelemetry,
        )
        .expect("compile")
    });
    let targets = compiled.static_closure_targets();
    // At minimum, `f` and `g` are registered.
    assert!(
        targets.len() >= 2,
        "expected ≥2 static closure targets (f, g); got {}: {:?}",
        targets.len(),
        targets
            .iter()
            .map(|(s, f, _, _)| (s, f))
            .collect::<Vec<_>>(),
    );
    // Distinct cl_sids and distinct code addresses.
    let mut cl_sids: Vec<u32> = targets.iter().map(|(s, _, _, _)| *s).collect();
    cl_sids.sort();
    cl_sids.dedup();
    assert_eq!(
        cl_sids.len(),
        targets.len(),
        "cl_sids must be unique across static_closure_targets entries"
    );
    for (_, _, ptr, _) in targets {
        assert!(
            !ptr.is_null(),
            "static-closure code pointer must be a resolved address"
        );
    }
}

/// fz-cps.1.7 — `make_process` populates `Process.static_closures` from
/// the compiled module's targets, and `fz_get_static_closure(cl_sid)`
/// returns the singleton's pointer. Two lookups return the same
/// pointer (singleton identity).
#[test]
fn static_closure_lookup_returns_singleton_pointer() {
    let src = "fn f(x), do: x + 1\n\
               fn apply(h, x), do: h(x)\n\
               fn main() do print(apply(f, 1)) end";
    let m = lower_src(src);
    // fz-jg5.6: reducer-disabled — see note on the sibling test above.
    let compiled = crate::ir_codegen::with_reducer_disabled(|| {
        compile(
            &mut crate::types::ConcreteTypes,
            &m,
            &crate::telemetry::NullTelemetry,
        )
        .expect("compile")
    });
    let targets = compiled.static_closure_targets();
    let (cl_sid, _, _, _) = *targets.first().expect("at least one static closure target");
    let mut p = compiled.make_process();
    let _current_process =
        fz_runtime::process::CurrentProcessGuard::install(&mut p as *mut Process);
    let a = fz_runtime::ir_runtime::fz_get_static_closure(cl_sid);
    let b = fz_runtime::ir_runtime::fz_get_static_closure(cl_sid);
    assert_eq!(a, b, "static-closure lookup must return the same pointer");
    assert_ne!(a, 0, "static-closure lookup must return non-null");
}

#[test]
fn aot_compile_produces_object_with_main_symbol() {
    let src = "fn add1(n) do n + 1 end\nfn main() do print(add1(41)) end";
    let m = lower_src(src);
    let artifact = compile_aot(
        &mut crate::types::ConcreteTypes,
        &m,
        "add1_smoke",
        &crate::telemetry::NullTelemetry,
    )
    .expect("compile_aot");
    assert!(
        !artifact.object.is_empty(),
        "AOT object should be non-empty"
    );
    // Post-.6.3, compile_aot emits a C-callable `main` symbol that
    // wraps fz_aot_run_main. The artifact's main_symbol surfaces that for
    // the linker.
    let main_sym = artifact.main_symbol.expect("main_symbol set");
    assert_eq!(main_sym, "main", "expected C-callable main symbol");
    // Sanity: object-file magic bytes for the host target. ELF starts
    // with 0x7f 'E' 'L' 'F'; Mach-O starts with 0xfeedface/0xfeedfacf
    // (or their byte-swapped 64-bit variants).
    let magic_ok = matches!(
        &artifact.object[..4],
        [0x7f, b'E', b'L', b'F']
            | [0xce, 0xfa, 0xed, 0xfe]
            | [0xcf, 0xfa, 0xed, 0xfe]
            | [0xfe, 0xed, 0xfa, 0xce]
            | [0xfe, 0xed, 0xfa, 0xcf]
    );
    assert!(
        magic_ok,
        "unexpected object magic: {:02x?}",
        &artifact.object[..4]
    );
}

fn run_main(src: &str) -> i64 {
    let m = lower_src(src);
    let entry = m.fn_by_name("main").unwrap().id;
    compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap()
    .run(entry)
}

fn run_main_after_heap_reset(src: &str) -> (i64, Module) {
    let m = lower_src(src);
    let entry = m.fn_by_name("main").unwrap().id;
    heap_reset_for_test();
    let r = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap()
    .run(entry);
    (r, m)
}

fn capture_main(src: &str) -> Vec<String> {
    let m = lower_src(src);
    capture_main_module(m)
}

fn capture_main_resolved(src: &str) -> Vec<String> {
    let m = lower_resolved_src(src);
    capture_main_module(m)
}

fn capture_main_module(m: Module) -> Vec<String> {
    let entry = m.fn_by_name("main").unwrap().id;
    heap_reset_for_test();
    let _ = test_capture_take();
    let _ = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap()
    .run(entry);
    test_capture_take()
}

fn run_main_and_count_live(src: &str) -> usize {
    let m = lower_src(src);
    let entry = m.fn_by_name("main").unwrap().id;
    let compiled = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    let mut process = compiled.make_process();
    let _ = compiled.run_in(entry, &mut process);
    process.heap.live_count()
}

// ----- fz-ul4.19.6: atom-table policy (shared, mutex-protected) -----

/// Two Processes built from the SAME CompiledModule observe equal
/// atom ids for the same atom literal. Atoms are u32s baked into
/// compiled code; they're the same bytes regardless of which Process
/// runs the code. Confirms .19.6's "global shared singleton" policy
/// is the actual semantics today (per ir_lower::AtomTable being
/// CompiledModule-scoped).
#[test]
fn atom_identity_preserved_across_processes_from_same_module() {
    // `:ok` halts as the atom's raw u32 id. Run two Processes; the halt
    // value must match because the atom id was assigned once at compile time.
    let src = "fn main(), do: :ok";
    let m = lower_src(src);
    let compiled = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    let entry = m.fn_by_name("main").unwrap().id;

    let mut pa = compiled.make_process();
    let mut pb = compiled.make_process();
    let ra = compiled.run_in(entry, &mut pa);
    let rb = compiled.run_in(entry, &mut pb);
    assert_eq!(
        ra, rb,
        "atom id stable across processes from the same module"
    );
}

/// fz-yan.4 — `nil`, `true`, and `false` are reserved at atom IDs 0/1/2
/// in every module. AtomTable::new() pre-interns these so the reserved
/// IDs are stable and downstream codegen / runtime can rely on them
/// (see fz_runtime::any_value::{NIL,TRUE,FALSE}_ATOM_ID). Pin the halt
/// values against the named constants so any future re-shuffling of
/// the intern order is caught at this layer.
#[test]
fn reserved_atom_ids_are_stable() {
    use fz_runtime::any_value::{FALSE_ATOM_ID, NIL_ATOM_ID, TRUE_ATOM_ID};
    assert_eq!(NIL_ATOM_ID, 0);
    assert_eq!(TRUE_ATOM_ID, 1);
    assert_eq!(FALSE_ATOM_ID, 2);
    assert_eq!(run_main("fn main(), do: nil"), NIL_ATOM_ID as i64);
    assert_eq!(run_main("fn main(), do: true"), TRUE_ATOM_ID as i64);
    assert_eq!(run_main("fn main(), do: false"), FALSE_ATOM_ID as i64);
}

// ----- fz-ul4.11.32: per-Process state isolation -----

/// Two Processes built from the same CompiledModule run independent
/// programs that each construct a map. PRE-MIGRATION (when MAP_BUILDER
/// was a shared TLS slot) the second `run_in` would inherit or corrupt
/// the first's in-flight builder state. Post-migration, each Process
/// owns its own builder fields and the two runs are fully independent.
#[test]
fn two_processes_run_independent_map_builds() {
    // Both programs use distinct keys + values so a corruption would
    // show up as a wrong halt value (halt reads tag bits of the map
    // pointer; we observe by reading specific entries via fz-level
    // map syntax).
    let src_a = "fn main(), do: %{1 => 10, 2 => 20}[1]";
    let src_b = "fn main(), do: %{3 => 30, 4 => 40}[3]";

    let ma = lower_src(src_a);
    let mb = lower_src(src_b);
    let mut ct = crate::types::ConcreteTypes;
    let ca = compile(&mut ct, &ma, &crate::telemetry::NullTelemetry).unwrap();
    let cb = compile(&mut ct, &mb, &crate::telemetry::NullTelemetry).unwrap();
    let entry_a = ma.fn_by_name("main").unwrap().id;
    let entry_b = mb.fn_by_name("main").unwrap().id;

    let mut pa = ca.make_process();
    let mut pb = cb.make_process();

    // Run a, then b, then a again (interleaved) — each should see only
    // its own state. If MAP_BUILDER were shared TLS, the second run
    // would either panic on stale state or compute the wrong value.
    let ra = ca.run_in(entry_a, &mut pa);
    let rb = cb.run_in(entry_b, &mut pb);
    let ra2 = ca.run_in(entry_a, &mut pa);

    assert_eq!(ra, 10, "process a's first run returns map[1] = 10");
    assert_eq!(rb, 30, "process b's run returns map[3] = 30");
    assert_eq!(
        ra2, 10,
        "process a's second run returns 10 (independent of b)"
    );

    // Each Process accumulated its own heap allocations. The map
    // alloc lives on the Process's heap.
    assert!(pa.heap.live_count() > 0, "process a has live heap allocs");
    assert!(pb.heap.live_count() > 0, "process b has live heap allocs");
}

#[test]
fn run_in_restores_existing_current_process() {
    let src = "fn main(), do: 1";
    let m = lower_src(src);
    let compiled = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    let entry = m.fn_by_name("main").unwrap().id;

    let mut outer = compiled.make_process();
    let outer_ptr = &mut outer as *mut Process;
    let _outer_guard = fz_runtime::process::CurrentProcessGuard::install(outer_ptr);

    let mut inner = compiled.make_process();
    let inner_result = compiled.run_in(entry, &mut inner);

    assert_eq!(inner_result, 1);
    let restored = fz_runtime::process::CURRENT_PROCESS.with(|c| c.get());
    assert_eq!(
        restored, outer_ptr,
        "run_in must restore the caller's current process"
    );
}

// ----- simple scalar / arithmetic tests -----

#[test]
fn const_int_runs_and_halts_with_value() {
    assert_eq!(run_main("fn main() do 42 end"), 42);
}

#[test]
fn binop_int_addition_runs() {
    assert_eq!(run_main("fn main(), do: 40 + 2"), 42);
}

#[test]
fn binop_chain_runs() {
    assert_eq!(run_main("fn main(), do: (1 + 2) * 7"), 21);
}

#[test]
fn if_then_else_runs() {
    assert_eq!(run_main("fn main(), do: if 1 < 2, do: 100, else: 200"), 100);
}

#[test]
fn print_builtin_routes_through_runtime() {
    assert_eq!(capture_main("fn main(), do: print(40 + 2)"), vec!["42"]);
}

#[test]
fn process_heap_alloc_stats_is_callable_from_fz() {
    let lines = capture_main_resolved(
        "fn main() do\n  xs = [1, 2]\n  print(xs)\n  stats = Process.heap_alloc_stats()\n  print(stats[:list_cons_allocs])\n  print(stats[:map_allocs])\nend",
    );
    assert_eq!(lines, vec!["[1, 2]", "2", "0"]);
}

#[test]
fn assert_builtin_keeps_scalar_kind_separate_from_raw_payload() {
    assert_eq!(
        run_main("fn main(), do: assert(2)"),
        fz_runtime::any_value::NIL_ATOM_ID as i64
    );
    assert_eq!(
        run_main("fn main(), do: assert_neq(true, 1)"),
        fz_runtime::any_value::NIL_ATOM_ID as i64
    );
}

#[test]
fn unop_neg_runs() {
    assert_eq!(run_main("fn main(), do: -7"), -7);
}

#[test]
fn atom_const_returns_atom_id() {
    // fz-yan.1 — AtomTable reserves ids 0/1/2 for nil/true/false at
    // construction. fz-axu.13 — Utf8.from_bytes in the prelude interns
    // `:ok` first (id=3), so user references to :ok return that id.
    // `match_error` / `function_clause` intern later in the prelude.
    assert_eq!(run_main("fn main(), do: :ok"), 4);
}

// ----- .11.8 frame-allocation tests -----

#[test]
fn add1_via_call_returns_42() {
    assert_eq!(
        run_main("fn add1(n), do: n + 1\nfn main(), do: add1(41)"),
        42
    );
}

#[test]
fn binop_with_inner_nontail_call() {
    assert_eq!(
        run_main("fn add1(n), do: n + 1\nfn main(), do: add1(40) + 2"),
        43
    );
}

#[test]
fn fact_5_smaller_repro() {
    assert_eq!(
        run_main(
            r#"
fn fact(0), do: 1
fn fact(n), do: n * fact(n - 1)
fn main(), do: fact(5)
"#
        ),
        120
    );
}

#[test]
fn fact_10_runs_via_recursion_and_continuation_chain() {
    assert_eq!(
        run_main(
            r#"
fn fact(0), do: 1
fn fact(n), do: n * fact(n - 1)
fn main(), do: fact(10)
"#
        ),
        3628800
    );
}

#[test]
fn count_100k_stays_bounded_via_tail_call_frame_reuse() {
    assert_eq!(
        run_main(
            r#"
fn count(0, acc), do: acc
fn count(n, acc), do: count(n - 1, acc + 1)
fn main(), do: count(100000, 0)
"#
        ),
        100_000
    );
}

#[test]
fn render_any_value_dispatches_per_tag() {
    assert_eq!(
        fz_runtime::any_value::debug::render_value(fz_runtime::any_value::AnyValue::int(42)),
        "42"
    );
    assert_eq!(
        fz_runtime::any_value::debug::render_value(fz_runtime::any_value::AnyValue::int(0)),
        "0"
    );
    assert_eq!(
        fz_runtime::any_value::debug::render_value(fz_runtime::any_value::AnyValue::int(-7)),
        "-7"
    );
    assert_eq!(
        fz_runtime::any_value::debug::render_value(fz_runtime::any_value::AnyValue::nil_atom()),
        "nil"
    );
    assert_eq!(
        fz_runtime::any_value::debug::render_value(fz_runtime::any_value::AnyValue::bool_atom(
            true
        )),
        "true"
    );
    assert_eq!(
        fz_runtime::any_value::debug::render_value(fz_runtime::any_value::AnyValue::bool_atom(
            false
        )),
        "false"
    );
    // Atom rendering needs a populated Process.atom_names; with an
    // empty table render falls back to `:atom_N`. The full
    // source-name path is verified end-to-end by the fixture matrix
    // (hello.fz post fz-ul4.25 re-bless).
    assert_eq!(
        fz_runtime::any_value::debug::render_value(fz_runtime::any_value::AnyValue::atom(3)),
        ":atom_3"
    );
}

#[test]
fn print_captures_atom_and_specials() {
    assert_eq!(
        capture_main("fn main() do\n  print(:ok)\n  print(true)\n  print(false)\nend"),
        vec![":ok", "true", "false"]
    );
}

// ----- .11.13 map tests -----

#[test]
fn print_atom_keyed_map_renders_canonically() {
    assert_eq!(
        capture_main("fn main(), do: print(%{a: 1, b: 2})"),
        vec!["%{:a => 1, :b => 2}"]
    );
}

#[test]
fn map_get_returns_value_or_nil() {
    assert_eq!(
        run_main("fn main(), do: %{a: 10, b: 20}[:a] + %{a: 10, b: 20}[:b]"),
        30
    );
}

#[test]
fn map_update_returns_new_map_originals_unchanged() {
    assert_eq!(
        capture_main(
            r#"
fn main() do
  m = %{a: 1, b: 2}
  m2 = %{m | a: 99}
  print(m)
  print(m2)
end
"#
        ),
        vec!["%{:a => 1, :b => 2}", "%{:a => 99, :b => 2}",]
    );
}

// ----- .11.12 bitstring tests -----

#[test]
fn print_bitstring_literal_via_jit() {
    assert_eq!(
        capture_main("fn main(), do: print(<<0xff, 0xab>>)"),
        vec!["<<255, 171>>"]
    );
}

#[test]
fn match_simple_header_and_rest() {
    assert_eq!(
        capture_main(
            r#"
fn parse(<<n, rest::binary>>), do: {n, rest}
fn main(), do: print(parse(<<0xa5, 0x01, 0x02>>))
"#
        ),
        vec!["{165, <<1, 2>>}"]
    );
}

#[test]
fn match_variable_size_payload_via_size_var() {
    assert_eq!(
        capture_main(
            r#"
fn parse(<<len, payload::binary-size(len), rest::binary>>) do
  {len, payload, rest}
end
fn main(), do: print(parse(<<3, 0x01, 0x02, 0x03, 0xff>>))
"#
        ),
        vec!["{3, <<1, 2, 3>>, <<255>>}"]
    );
}

// ----- .11.11 tuple tests -----

#[test]
fn print_tuple_pair_renders() {
    assert_eq!(capture_main("fn main(), do: print({1, 2})"), vec!["{1, 2}"]);
}

#[test]
fn fst_snd_destructure_tuple() {
    assert_eq!(
        run_main(
            r#"
fn fst({a, _}), do: a
fn snd({_, b}), do: b
fn main(), do: fst({10, 20}) + snd({30, 40})
"#
        ),
        50
    );
}

#[test]
fn print_mixed_type_tuple() {
    assert_eq!(
        capture_main("fn main(), do: print({1, :ok, true})"),
        vec!["{1, :ok, true}"]
    );
}

#[test]
fn tuple_literal_initializes_scalar_fields_without_boxing() {
    let m = lower_src("fn main(), do: print({1, 2.5, :ok})");
    let ir = get_main_ir(&m);
    assert!(
        ir.contains("@fz_struct_set_field_int"),
        "integer tuple field should use typed destination setter:\n{}",
        ir
    );
    assert!(
        ir.contains("@fz_struct_set_field_float"),
        "float tuple field should use typed destination setter:\n{}",
        ir
    );
    assert!(
        ir.contains("@fz_struct_set_field_atom"),
        "atom tuple field should use typed destination setter:\n{}",
        ir
    );
    assert!(
        !ir.contains("@fz_box_int_for_any") && !ir.contains("@fz_box_float_for_any"),
        "numeric tuple fields should not allocate boxes before initialization:\n{}",
        ir
    );
}

// ----- .11.10 list tests -----

#[test]
fn print_list_literal_renders_via_jit() {
    assert_eq!(
        capture_main("fn main(), do: print([1, 2, 3])"),
        vec!["[1, 2, 3]"]
    );
}

#[test]
fn sum_list_via_head_tail_recursion() {
    assert_eq!(
        run_main(
            r#"
fn sum([]), do: 0
fn sum([h | t]), do: h + sum(t)
fn main(), do: sum([1, 2, 3, 4, 5])
"#
        ),
        15
    );
}

#[test]
fn box_unbox_int_roundtrip_via_neg_neg() {
    for n in &[0i64, 1, -1, 42, -42, 1_000_000_000] {
        let src = format!("fn main(), do: -(-({}))", n);
        assert_eq!(run_main(&src), *n, "round-trip failed for {}", n);
    }
}

#[test]
fn mutual_recursion_even_odd_small_n() {
    assert_eq!(
        run_main(
            r#"
fn even(0), do: true
fn even(n), do: odd(n - 1)
fn odd(0), do: false
fn odd(n), do: even(n - 1)
fn main(), do: even(10)
"#
        ),
        1
    );
}

// ----- .11.19 closure tests -----

#[test]
fn apply_simple_closure_no_captures() {
    assert_eq!(
        run_main(
            r#"
fn double(x), do: x * 2
fn apply_f(f, n), do: f(n)
fn main(), do: apply_f(double, 21)
"#
        ),
        42
    );
}

#[test]
fn closure_captures_local_value() {
    assert_eq!(
        run_main(
            r#"
fn make_adder(k), do: fn(x) -> x + k
fn main() do
  f = make_adder(10)
  f(5)
end
"#
        ),
        15
    );
}

#[test]
fn map_higher_order_renders_doubled_list() {
    assert_eq!(
        capture_main(
            r#"
fn double(x), do: x * 2
fn map_l(_, []), do: []
fn map_l(f, [h | t]), do: [f(h) | map_l(f, t)]
fn main(), do: print(map_l(double, [1, 2, 3]))
"#
        ),
        vec!["[2, 4, 6]"]
    );
}

// ----- .11.21 structural equality tests -----

#[test]
fn list_structural_eq_same_content_distinct_allocations() {
    assert_eq!(run_main("fn main(), do: [1, 2, 3] == [1, 2, 3]"), 1);
}

#[test]
fn list_structural_eq_length_mismatch_is_false() {
    assert_eq!(run_main("fn main(), do: [1, 2] == [1, 2, 3]"), FALSE_HALT);
}

#[test]
fn tuple_structural_eq_same_arity_and_content() {
    assert_eq!(run_main("fn main(), do: {1, :ok} == {1, :ok}"), 1);
}

#[test]
fn tuple_eq_different_arity_is_false() {
    assert_eq!(run_main("fn main(), do: {1, 2} == {1, 2, 3}"), FALSE_HALT);
}

#[test]
fn bitstring_structural_eq_byte_aligned() {
    assert_eq!(run_main("fn main(), do: <<1, 2, 3>> == <<1, 2, 3>>"), 1);
}

#[test]
fn map_structural_eq_ignores_construction_order() {
    assert_eq!(run_main("fn main(), do: %{a: 1, b: 2} == %{b: 2, a: 1}"), 1);
}

#[test]
fn map_eq_different_value_is_false() {
    assert_eq!(
        run_main("fn main(), do: %{a: 1, b: 2} == %{a: 1, b: 3}"),
        FALSE_HALT
    );
}

#[test]
fn heterogeneous_kinds_compare_unequal() {
    assert_eq!(run_main("fn main(), do: [1, 2] == {1, 2}"), FALSE_HALT);
}

#[test]
fn nested_map_with_list_structural_eq() {
    assert_eq!(run_main("fn main(), do: %{x: [1, 2]} == %{x: [1, 2]}"), 1);
}

#[test]
fn neq_inverts_structural_eq() {
    assert_eq!(run_main("fn main(), do: [1, 2] != [1, 2]"), FALSE_HALT);
    assert_eq!(run_main("fn main(), do: [1, 2] != [1, 3]"), 1);
}

// ----- .11.20 float representation tests -----

#[test]
fn float_const_halt_round_trips_via_bits() {
    let (halt, _m) = run_main_after_heap_reset("fn main(), do: 2.5");
    assert_eq!(f64::from_bits(halt as u64), 2.5);
}

#[test]
fn print_float_renders_with_explicit_dot_zero() {
    assert_eq!(
        capture_main("fn main() do\n  print(4.0)\n  print(2.5)\nend"),
        vec!["4.0", "2.5"]
    );
}

#[test]
fn float_arithmetic_promotes_via_runtime_helper() {
    assert_eq!(run_main("fn main(), do: 1.5 + 2.5 == 4.0"), 1);
}

#[test]
fn mixed_int_float_arithmetic_promotes() {
    assert_eq!(run_main("fn main(), do: 1 + 2.0 == 3.0"), 1);
}

#[test]
fn mixed_int_float_eq_does_not_promote() {
    assert_eq!(run_main("fn main(), do: 1 == 1.0"), FALSE_HALT);
}

#[test]
fn float_literals_compare_equal_by_value() {
    assert_eq!(run_main("fn main(), do: 1.5 == 1.5"), 1);
}

#[test]
fn float_ordered_comparison_dispatches_through_helper() {
    assert_eq!(run_main("fn main(), do: 1.5 < 2.0"), 1);
}

#[test]
fn float_bit_field_round_trips_via_bitstring() {
    let (halt, _m) = run_main_after_heap_reset("fn main(), do: <<2.5::float>>");
    let halt = halt as u64;
    let p = fz_runtime::any_value::bitstring_addr_from_tagged(halt).unwrap();
    let bytes = unsafe {
        std::slice::from_raw_parts(
            fz_runtime::any_value::bitstring_bytes_ptr(p as *const u8),
            8,
        )
    };
    let mut buf = [0u8; 8];
    buf.copy_from_slice(bytes);
    let f = f64::from_bits(u64::from_be_bytes(buf));
    assert_eq!(f, 2.5);
}

#[test]
fn cons_with_float_head_no_box() {
    assert_eq!(
        run_main_and_count_live("fn main(), do: [3.14]"),
        1,
        "float list literal should allocate only the cons cell"
    );
}

#[test]
fn render_raw_float_in_container() {
    assert_eq!(capture_main("fn main(), do: print([1.5])"), vec!["[1.5]"]);
}

#[test]
fn float_list_head_projects_raw_f64() {
    let src = "fn first([h | _]), do: h\nfn main(), do: first([2.5])";
    let (halt, _m) = run_main_after_heap_reset(src);
    assert_eq!(f64::from_bits(halt as u64), 2.5);
}

#[test]
fn equality_float_in_container() {
    assert_eq!(run_main("fn main(), do: [1.5] == [1.5]"), 1);
}

#[test]
fn map_with_float_value_no_box() {
    assert_eq!(
        run_main_and_count_live("fn main(), do: %{a: 3.14}"),
        1,
        "float map literal should allocate only the map"
    );
}

#[test]
fn map_with_float_key_no_box() {
    assert_eq!(
        run_main_and_count_live("fn main(), do: %{3.14 => :ok}"),
        1,
        "float map key should allocate only the map"
    );
}

#[test]
fn map_literal_and_update_use_destinations_not_repeated_puts() {
    let m = lower_src(
        "fn main() do\n  m = %{a: 1, b: 2}\n  n = %{m | a: 3, c: 4}\n  print(n[:a])\nend",
    );
    let ir = get_main_ir(&m);
    assert!(
        ir.contains("@fz_map_dest_begin")
            && ir.contains("@fz_map_dest_begin_update")
            && ir.contains("@fz_map_dest_put")
            && ir.contains("@fz_map_dest_freeze"),
        "map literals and updates should lower through destination begin/put/freeze:\n{}",
        ir
    );
    assert!(
        !ir.contains(concat!("@fz_map", "_builder_")),
        "map destinations should not expose the old builder helper surface:\n{}",
        ir
    );
    assert!(
        !ir.contains("@fz_map_put_"),
        "known-entry map construction should not be repeated immutable map_put copies:\n{}",
        ir
    );
}

#[test]
fn tail_call_closure_reuses_frame_via_count_loop() {
    // Self-applying closure to force TailCallClosure on every iteration.
    assert_eq!(
        run_main(
            r#"
fn loop_with(f, 0, acc), do: acc
fn loop_with(f, n, acc), do: f(f, n - 1, acc + 1)
fn main(), do: loop_with(loop_with, 100000, 0)
"#
        ),
        100_000
    );
}

// ---- fz-ul4.11.24.4: arithmetic dispatch elision ----
//
// These two tests synthesize IR directly via FnBuilder rather than
// going through source: they exercise codegen with an entry-block
// parameter at Top (impossible from a top-level fn declared in fz
// source) so the planner is forced to retain dispatch. Keeping them
// hand-built is the cleanest expression of the assertion.

#[test]
fn list_projection_accepts_block_env_nonempty_fact() {
    let mut t = crate::types::ConcreteTypes;
    let xs = crate::fz_ir::Var(1);
    let mut fn_types = crate::ir_planner::SpecPlan::default();
    let list_ty = {
        let elem = t.any();
        t.list(elem)
    };
    fn_types.vars.insert(xs, list_ty);

    let mut block_env = std::collections::HashMap::new();
    let nonempty_ty = {
        let elem = t.any();
        t.non_empty_list(elem)
    };
    block_env.insert(xs, nonempty_ty);

    assert!(
        list_projection_is_safe(&mut t, &fn_types, xs, Some(&block_env)),
        "branch-narrowed block env should make direct list projection safe"
    );
}

#[test]
fn list_projection_rejects_unnarrowed_block_env() {
    let mut t = crate::types::ConcreteTypes;
    let xs = crate::fz_ir::Var(1);
    let mut fn_types = crate::ir_planner::SpecPlan::default();
    let list_ty = {
        let elem = t.any();
        t.list(elem)
    };
    fn_types.vars.insert(xs, list_ty.clone());

    let mut block_env = std::collections::HashMap::new();
    block_env.insert(xs, list_ty);

    assert!(
        !list_projection_is_safe(&mut t, &fn_types, xs, Some(&block_env)),
        "possibly-empty list facts must stay on the checked helper path"
    );
}

fn build_int_const_add_module() -> Module {
    use crate::fz_ir::{FnBuilder, ModuleBuilder};
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let two = b.let_(entry, Prim::Const(Const::Int(2)));
    let sum = b.let_(entry, Prim::BinOp(BinOp::Add, one, two));
    b.set_terminator(entry, Term::Halt(sum));
    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    mb.build()
}

fn build_top_param_add_module() -> Module {
    use crate::fz_ir::{FnBuilder, ModuleBuilder};
    let mut b = FnBuilder::new(FnId(0), "main");
    let x = b.fresh_var();
    let entry = b.block(vec![x]);
    let one = b.let_(entry, Prim::Const(Const::Int(1)));
    let sum = b.let_(entry, Prim::BinOp(BinOp::Add, x, one));
    b.set_terminator(entry, Term::Halt(sum));
    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    mb.build()
}

fn get_main_ir(m: &Module) -> String {
    ir_text_record_enable();
    let _ = compile(
        &mut crate::types::ConcreteTypes,
        m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    let ir = ir_text_record_take();
    ir.into_iter()
        .find(|(n, _)| n == "main")
        .map(|(_, s)| s)
        .expect("no main ir captured")
}

#[test]
fn arith_int_int_elides_dispatch() {
    let m = build_int_const_add_module();
    let ir = get_main_ir(&m);
    assert!(
        !ir.contains("brif"),
        "elision should drop the both_int branch:\n{}",
        ir
    );
}

#[test]
fn arith_top_param_keeps_dispatch() {
    let m = build_top_param_add_module();
    let ir = get_main_ir(&m);
    assert!(
        ir.contains("brif"),
        "dispatch should be retained for Top operands:\n{}",
        ir
    );
}

// --- fz-ul4.27.6.2.2 — build_fn_signature ---

#[test]
fn signature_uniform_when_not_native() {
    // `fn add(a, b) do a + b end` lowered, typed, then asked for a
    // uniform sig. Should be `(i64, i64) -> i64` regardless of param
    // types.
    let m = lower_src("fn add(a, b) do a + b end\nfn main() do print(add(1, 2)) end");
    let mt = crate::ir_planner::plan_module(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    );
    let add_idx = m.fns.iter().position(|f| f.name == "add").unwrap();
    let ft = mt.any_spec_for(m.fns[add_idx].id).expect("registered spec");
    let mut t = crate::types::ConcreteTypes;
    let rd = join_return_ty(&mut t, &m.fns[add_idx], ft);
    let prs = build_param_reprs(&mut t, &m.fns[add_idx], ft);
    let sig = build_fn_signature(
        &prs,
        ArgRepr::from_ty(&mut t, &rd),
        false,
        true,
        None,
        false,
        None,
    );
    assert_eq!(sig.params.len(), 2);
    assert_eq!(sig.returns.len(), 1);
    assert_eq!(sig.params[0].value_type, types::I64);
    assert_eq!(sig.params[1].value_type, types::I64);
    assert_eq!(sig.returns[0].value_type, types::I64);
}

#[test]
fn signature_native_uses_typed_params_and_cont() {
    // Same `add` fn, this time the planner has narrowed entry params to
    // int via call-site narrowing. Native sig should be
    // `(i64, i64, cont: i64) -> i64`.
    // fz-cps.1.a (fz-siu.1.1): trailing cont:i64 per §2.1.
    let m = lower_src("fn add(a, b) do a + b end\nfn main() do print(add(1, 2)) end");
    let mt = crate::ir_planner::plan_module(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    );
    let add_idx = m.fns.iter().position(|f| f.name == "add").unwrap();
    let ft = mt.any_spec_for(m.fns[add_idx].id).expect("registered spec");
    let mut t = crate::types::ConcreteTypes;
    let rd = join_return_ty(&mut t, &m.fns[add_idx], ft);
    let prs = build_param_reprs(&mut t, &m.fns[add_idx], ft);
    let sig = build_fn_signature(
        &prs,
        ArgRepr::from_ty(&mut t, &rd),
        true,
        false,
        None,
        false,
        None,
    );
    // 2 entry params + cont.
    assert_eq!(sig.params.len(), 3);
    assert_eq!(sig.returns.len(), 1);
    // Trailing cont is i64.
    assert_eq!(sig.params.last().unwrap().value_type, types::I64);
    // Return is i64 (tagged or raw-int — both ride i64 register).
    assert_eq!(sig.returns[0].value_type, types::I64);
}

#[test]
fn signature_native_arity_matches_entry_params_plus_cont() {
    // .27.13: native sig is per-type typed. For `dist(x, y)` called
    // with `dist(1.5, 2.5)`, call-site narrowing types `x` and `y` as
    // float-only → AbiParam(f64). Return joins every Term::Return val
    // type; here that's float-only → f64.
    // fz-cps.1.a (fz-siu.1.1): trailing cont:i64 per §2.1.
    let m = lower_src("fn dist(x, y) do x * x + y * y end\nfn main() do print(dist(1.5, 2.5)) end");
    let mt = crate::ir_planner::plan_module(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    );
    let dist_idx = m.fns.iter().position(|f| f.name == "dist").unwrap();
    let ft = mt
        .any_spec_for(m.fns[dist_idx].id)
        .expect("registered spec");
    let mut t = crate::types::ConcreteTypes;
    let rd = join_return_ty(&mut t, &m.fns[dist_idx], ft);
    let prs = build_param_reprs(&mut t, &m.fns[dist_idx], ft);
    let sig = build_fn_signature(
        &prs,
        ArgRepr::from_ty(&mut t, &rd),
        true,
        false,
        None,
        false,
        None,
    );
    // 2 entry params + cont.
    assert_eq!(sig.params.len(), 3);
    assert_eq!(sig.params[0].value_type, types::F64);
    assert_eq!(sig.params[1].value_type, types::F64);
    assert_eq!(sig.params[2].value_type, types::I64); // cont
    // fz-cps.1.2: native return canonicalized to i64 (cont indirect
    // sig is `(i64, i64) -> i64 tail`; caller's return type must
    // match per Cranelift's tail-call verifier).
    assert_eq!(sig.returns[0].value_type, types::I64);
}

// ----- fz-ul4.29.2: SpecRegistry infrastructure -----

#[test]
fn spec_registry_registers_any_key_per_fn_with_spec_id_eq_fn_id() {
    // Two-fn module. After compile(&mut crate::types::ConcreteTypes, ), spec_registry holds one any-key
    // spec per fn; the SpecId.0 == FnId.0 invariant is asserted at
    // build time (debug_assert in compile_with_backend).
    let m = lower_src("fn add(a, b) do a + b end\nfn main() do print(add(1, 2)) end");
    let compiled = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    // Drive a run to ensure the pipeline ran the registry construction
    // path; the assertion lives in compile_with_backend.
    let _ = compiled.run(m.fn_by_name("main").unwrap().id);
}

#[test]
fn spec_registry_any_key_lookup() {
    // Use the registry directly to verify register/resolve/any_key
    // contracts. Doesn't go through compile(&mut crate::types::ConcreteTypes, ).
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::ConcreteTypes;
    let fid = FnId(0);
    let any_key_2 = vec![t.any(); 2];
    let sid = reg.register(&t, fid, any_key_2.clone());
    assert_eq!(sid.0, 0, "first registration gets SpecId(0)");
    // Re-registering the same key returns the same SpecId.
    let sid2 = reg.register(&t, fid, any_key_2.clone());
    assert_eq!(sid, sid2);
    // Resolve roundtrips.
    let resolved = reg.resolve(&t, fid, &any_key_2);
    assert_eq!(resolved, Some(sid));
    // any_key helper.
    let via_any = reg.any_key(fid, 2);
    assert_eq!(via_any, sid);
    // A different fn gets a different SpecId.
    let other_sid = reg.register(&t, FnId(1), Vec::<KeySlot>::new());
    assert_eq!(other_sid.0, 1);
    assert_eq!(reg.len(), 2);
}

#[test]
fn spec_registry_distinct_narrow_keys() {
    // The registry distinguishes narrow keys via the exact-match
    // fast path. Subsumption fallback is exercised below.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::ConcreteTypes;
    let fid = FnId(0);
    let int1 = vec![t.int()];
    let float1 = vec![t.float()];
    let sid_int = reg.register(&t, fid, int1.clone());
    let sid_float = reg.register(&t, fid, float1.clone());
    assert_ne!(
        sid_int, sid_float,
        "int-key and float-key must be distinct SpecIds"
    );
    // Exact-match fast path returns identity.
    assert_eq!(reg.resolve(&t, fid, &int1), Some(sid_int));
    assert_eq!(reg.resolve(&t, fid, &float1), Some(sid_float));
    // No covering spec for atom under the registered set → None.
    let atom1 = vec![t.atom()];
    assert_eq!(reg.resolve(&t, fid, &atom1), None);
}

// ----- fz-ul4.29.11: subsumption-based callsite dispatch -----

#[test]
fn resolve_subsumes_narrower_query_to_wider_registered_spec() {
    // Only [int] registered; query [int_lit(4)] should subsume to it.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::ConcreteTypes;
    let fid = FnId(0);
    let int = t.int();
    let int_spec = reg.register(&t, fid, vec![int]);
    let q = vec![t.int_lit(4)];
    assert_eq!(reg.resolve(&t, fid, &q), Some(int_spec));
}

#[test]
fn resolve_picks_narrowest_among_multiple_supertype_matches() {
    // Both [int] and [any] cover [int_lit(4)]. [int] is narrower; pick it.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::ConcreteTypes;
    let fid = FnId(0);
    let any = t.any();
    let any_spec = reg.register(&t, fid, vec![any]);
    let int = t.int();
    let int_spec = reg.register(&t, fid, vec![int]);
    let q = vec![t.int_lit(4)];
    let resolved = reg.resolve(&t, fid, &q);
    assert_eq!(
        resolved,
        Some(int_spec),
        "should pick narrower [int] over wider [any]; got {:?}, any={:?}, int={:?}",
        resolved,
        any_spec,
        int_spec
    );
}

#[test]
fn resolve_returns_none_when_nothing_covers() {
    // [float] registered; query [int_lit(4)] is not a subtype → None.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::ConcreteTypes;
    let fid = FnId(0);
    let float = t.float();
    reg.register(&t, fid, vec![float]);
    let q = vec![t.int_lit(4)];
    assert_eq!(
        reg.resolve(&t, fid, &q),
        None,
        "int_lit(4) is not a subtype of float; no covering spec"
    );
}

#[test]
fn resolve_subtype_incomparable_uses_stable_precedence() {
    // [int, any] (sid A) and [any, atom] (sid B). Query [int_lit(4), :foo]
    // is covered by both; neither key is a subtype of the other on every
    // axis. Stable per-family precedence, not incidental SpecId order,
    // breaks the tie.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::ConcreteTypes;
    let fid = FnId(0);
    let int = t.int();
    let any_a = t.any();
    let sid_a = reg.register_with_precedence(&t, fid, vec![int, any_a], 1);
    let any_b = t.any();
    let atom = t.atom();
    let sid_b = reg.register_with_precedence(&t, fid, vec![any_b, atom], 0);
    assert!(
        sid_a.0 < sid_b.0,
        "test expects precedence and SpecId order to diverge"
    );
    let q = vec![t.int_lit(4), t.atom_lit(":foo")];
    let resolved = reg.resolve(&t, fid, &q).expect("a covering spec exists");
    assert_eq!(
        resolved, sid_b,
        "subtype-incomparable matches should honor stable precedence; got {:?}, a={:?}, b={:?}",
        resolved, sid_a, sid_b
    );
}

#[test]
fn resolve_exact_match_takes_fast_path() {
    // Exact-match registration resolves to the same SpecId — verifies
    // the O(1) fast path still works alongside subsumption fallback.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::ConcreteTypes;
    let fid = FnId(0);
    let key = vec![t.int(), t.float()];
    let sid = reg.register(&t, fid, key.clone());
    assert_eq!(reg.resolve(&t, fid, &key), Some(sid));
}

#[test]
fn resolve_per_fn_isolation() {
    // Specs for one fn must not subsume queries for a different fn.
    let mut reg = SpecRegistry::new();
    let mut t = crate::types::ConcreteTypes;
    let any = t.any();
    let _sid0 = reg.register(&t, FnId(0), vec![any]);
    // No spec registered for FnId(1) — even though FnId(0) has an
    // any-key, it shouldn't cover queries to FnId(1).
    let q = vec![t.int()];
    assert_eq!(reg.resolve(&t, FnId(1), &q), None);
}

// ----- fz-ul4.11.15.6: hot-loop continuation allocation reduction -----

/// Lazy continuation materialization keeps straight native continuation chains
/// off the heap even when the inliner is disabled.
///
/// Uses 10 nested step calls (step(step(...step(0)...))) so the
/// continuation chain is clear without triggering the multi-clause dispatch
/// codegen path that requires the inliner to succeed.
#[test]
fn hot_loop_native_continuations_allocate_no_heap_closures() {
    // 10 nested calls to step — each is a Call+Cont site pre-inline.
    let src = "fn step(x), do: x + 1\n\
               fn main(), do: step(step(step(step(step(step(step(step(step(step(0))))))))))";

    let mut ct = crate::types::ConcreteTypes;
    // Pre-inline run: compile with the inliner bypassed.
    let pre_count = with_inline_disabled(|| {
        let m = lower_src(src);
        fz_runtime::ir_runtime::frame_alloc_count_reset();
        let entry = m.fn_by_name("main").unwrap().id;
        let r = compile(&mut ct, &m, &crate::telemetry::NullTelemetry)
            .unwrap()
            .run(entry);
        assert_eq!(r, 10, "pre-inline result must be 10");
        fz_runtime::ir_runtime::frame_alloc_count_take()
    });

    // Post-inline run: normal compile (inliner active).
    let m = lower_src(src);
    fz_runtime::ir_runtime::frame_alloc_count_reset();
    let entry = m.fn_by_name("main").unwrap().id;
    let post_result = compile(&mut ct, &m, &crate::telemetry::NullTelemetry)
        .unwrap()
        .run(entry);
    let post_count = fz_runtime::ir_runtime::frame_alloc_count_take();

    assert_eq!(post_result, 10, "post-inline result must still be 10");
    assert_eq!(
        pre_count, 0,
        "pre-inline native continuation chain should not allocate heap closures"
    );
    assert_eq!(
        post_count, 0,
        "post-inline native continuation chain should not allocate heap closures"
    );
}

/// fz-zj3 — box_int constant fold: Const::Int(n) lowered as RawInt must be
/// retagged as a single iconst ((n<<3)|TAG_INT), not ishl_imm + bor_imm.
#[test]
fn box_int_const_fold_eliminates_ishl_bor() {
    // send(2, 41) passes integer constants to an extern taking ValueRef args.
    // Before the fix: v9=iconst 2; ishl_imm v9,3; bor_imm result,1 (3 insns).
    // After: v9=iconst 2; v11=iconst 17 — raw_int_consts hit in tagged_get.
    let src = "fn relay(), do: send(1, receive() + 1)\n\
               fn main() do\n\
                 spawn(relay)\n\
                 send(2, 41)\n\
                 print(receive())\n\
               end";
    let m = lower_src(src);
    ir_text_record_enable();
    let _ = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    let ir = ir_text_record_take();
    let main_ir = ir
        .iter()
        .find(|(n, _)| n == "main")
        .map(|(_, s)| s.as_str())
        .unwrap_or("");
    // send(2, 41): pid crosses as raw i64 (2), while the message is boxed once
    // at the any boundary and then rides the mailbox as a single any value ref.
    // The old split `{value, kind}` side tag must not appear.
    assert!(
        main_ir.contains("iconst.i64 2")
            && main_ir.contains("iconst.i64 41")
            && main_ir.contains("@fz_box_int_for_any")
            && !main_ir.contains("iconst.i8 13"),
        "expected raw pid 2 and boxed tagged-ref message for send(2, 41):\n{}",
        main_ir
    );
    assert!(
        !main_ir.contains("ishl_imm"),
        "spurious ishl_imm in main CLIF — box_int fold not applied:\n{}",
        main_ir
    );
}

#[test]
fn mailbox_with_float_boxes_only_at_send_boundary() {
    let src = "fn main() do\n  send(self(), 3.14)\n  nil\nend";
    let m = lower_src(src);
    ir_text_record_enable();
    let _ = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    let ir = ir_text_record_take();
    let main_ir = ir
        .iter()
        .find(|(n, _)| n == "main")
        .map(|(_, s)| s.as_str())
        .unwrap_or("");
    assert!(
        main_ir.contains("fz_box_float_for_any") && main_ir.contains("fz_send_ref"),
        "expected float send to box explicitly at the one-word send boundary:\n{}",
        main_ir
    );
}

/// fz-li4 — Term::Receive with a natively-callable continuation must not
/// emit a box→unbox roundtrip for raw-int captures. Before the fix,
/// needs_blanket_retag fell through to `_ => true` for Term::Receive,
/// forcing ishl_imm+bor_imm on every raw var immediately before the
/// fz_receive_park call — then the cont had to sshr_imm them back out.
#[test]
fn receive_native_cont_no_box_unbox_roundtrip() {
    let src = "fn relay(), do: send(1, receive() + 1)\n\
               fn main() do\n\
                 spawn(relay)\n\
                 send(2, 41)\n\
                 print(receive())\n\
               end";
    let m = lower_src(src);
    ir_text_record_enable();
    let _ = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    let ir = ir_text_record_take();
    let relay_ir = ir
        .iter()
        .find(|(n, _)| n == "relay")
        .map(|(_, s)| s.as_str())
        .unwrap_or("");
    // The relay fn holds one raw-int capture (1). With the fix it is
    // stored directly — no ishl_imm or bor_imm should appear in relay's
    // block. (Arithmetic in the receive continuation is a different fn.)
    assert!(
        !relay_ir.contains("ishl_imm"),
        "spurious box in relay CLIF — integer capture was re-tagged before Receive:\n{}",
        relay_ir
    );
}

/// fz-jiw — TypeTest i1 cached in `condition` map; Term::If consumes it
/// directly, bypassing bool_to_fz → is_truthy roundtrip.
/// Before the fix: brif was preceded by `icmp ne v, nil`, `icmp ne v, false`,
/// `band` (3 extra instructions decoding the tagged bool back to i1).
/// After: the i1 produced by `icmp_imm eq (v & 7), TAG_INT` is reused
/// directly — no `icmp ne` appears in the branching block.
///
/// fz-ul4.43.A/B note: literal-only call sites are now fully resolved by
/// per-spec fold, so the brif is in `check`'s any-key spec rather than in
/// main. Route via a closure call to force the any-key spec.
#[test]
fn condition_cache_bypasses_is_truthy_in_type_dispatch() {
    let src = "fn check(x :: integer) do :is_int end\n\
               fn check(x) do :other end\n\
               fn main() do\n\
                 c = fn(x) -> check(x)\n\
                 print(c(42))\n\
                 print(c(:foo))\n\
               end";
    let m = lower_src(src);
    ir_text_record_enable();
    let _ = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    let ir = ir_text_record_take();
    // fz-ul4.43.A/B note: per-spec fold may eliminate every brif if it can
    // statically resolve the dispatch. The codegen fast-path is still
    // correct; for any spec that DOES retain a brif, verify no spurious
    // icmp-ne decode appears next to it.
    let with_brif: Vec<(&str, &str)> = ir
        .iter()
        .filter(|(_, s)| s.contains("brif"))
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect();
    for (n, s) in &with_brif {
        assert!(
            !s.contains("icmp ne"),
            "spurious is_truthy icmp ne in {} CLIF — condition cache not applied:\n{}",
            n,
            s
        );
    }
}

/// fz-h4q — ArgRepr::Condition: pure-branch TypeTest does not materialize a
/// tagged bool. Before the fix: every boolean prim emitted bool_to_fz eagerly
/// (select + true/false words), then is_truthy decoded it back to i1. After:
/// the i1 is stored as ArgRepr::Condition and fed directly to brif. Strict
/// value decoding may use unrelated `select`s, so this test gates the bool
/// materialization constants instead of banning every select in the function.
#[test]
fn pure_branch_type_test_does_not_materialize_bool() {
    // fz-ul4.43.A/B note: route via closure so check's any-key spec retains
    // the TypeTest+If (per-spec fold otherwise eliminates it).
    let src = "fn check(x :: integer) do :is_int end\n\
               fn check(x) do :other end\n\
               fn main() do\n\
                 c = fn(x) -> check(x)\n\
                 print(c(42))\n\
                 print(c(:foo))\n\
               end";
    let m = lower_src(src);
    ir_text_record_enable();
    let _ = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    let ir = ir_text_record_take();
    let with_brif: Vec<(&str, &str)> = ir
        .iter()
        .filter(|(_, s)| s.contains("brif"))
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect();
    for (n, s) in &with_brif {
        assert!(
            !(s.contains("iconst.i64 10") || s.contains("iconst.i64 18")),
            "spurious bool_to_fz constants in {} CLIF — bool was emitted eagerly:\n{}",
            n,
            s
        );
    }
}

/// fz-2tc — unit-return extern results whose dest var is unused emit no
/// iconst at all (DeadUnit path). Live results use cached_iconst so they
/// share the canonical nil atom payload if the same block already holds one.
/// hello: print(42), print(:ok), print(true) are all unit-return externs
/// whose nil results are dead — only print(nil)'s result is live (passed
/// to the continuation). The old encoded nil scalar (`iconst.i64 2`) must
/// not appear; canonical nil is raw atom id 0 with kind tag 15.
#[test]
fn dead_unit_extern_result_elided() {
    let src = "fn main() do\n\
                 print(40 + 2)\n\
                 print(:ok)\n\
                 print(true)\n\
                 print(nil)\n\
               end";
    let m = lower_src(src);
    ir_text_record_enable();
    let _ = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    let ir = ir_text_record_take();
    let main_ir = ir
        .iter()
        .find(|(n, _)| n == "main")
        .map(|(_, s)| s.as_str())
        .unwrap_or("");
    // Dead nil results are gone, and live nil is not the old encoded scalar.
    let nil_count = main_ir.matches("iconst.i64 2").count();
    assert_eq!(
        nil_count, 0,
        "expected no encoded nil iconsts in main CLIF (got {}):\n{}",
        nil_count, main_ir
    );
    assert!(
        main_ir.contains("@fz_box_atom_for_any"),
        "expected live nil to cross the ValueRef ABI by boxing the atom payload:\n{}",
        main_ir
    );
}

/// fz-o2g — Const::Nil/Bool/Atom use canonical raw+kind parts. The old
/// encoded nil scalar (`iconst.i64 2`) should not survive codegen.
#[test]
fn const_nil_bool_atom_deduplicated_within_block() {
    let src = "fn main() do\n\
                 print(nil)\n\
               end";
    let m = lower_src(src);
    ir_text_record_enable();
    let _ = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .unwrap();
    let ir = ir_text_record_take();
    let main_ir = ir
        .iter()
        .find(|(n, _)| n == "main")
        .map(|(_, s)| s.as_str())
        .unwrap_or("");
    let nil_count = main_ir.matches("iconst.i64 2").count();
    assert_eq!(
        nil_count, 0,
        "expected no encoded nil iconsts in main, got {}:\n{}",
        nil_count, main_ir
    );
    assert!(
        main_ir.contains("@fz_box_atom_for_any"),
        "expected live nil to cross the ValueRef ABI by boxing the atom payload:\n{}",
        main_ir
    );
}

/// fz-5j5.2 / fz-za0.2 — plan_module is called exactly 3 times in the
/// codegen pipeline. The final pass runs after destination lowering so
/// dispatch metadata covers the optimized IR; codegen then merges narrower
/// pre-DP facts for vars that destination lowering did not semantically change.
#[test]
fn plan_module_called_exactly_three_times_in_pipeline() {
    let src = "fn main(), do: print(42)";
    let m = lower_src(src);
    crate::ir_planner::PLAN_MODULE_CALLS.with(|c| c.set(0));
    compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .expect("compile");
    let count = crate::ir_planner::PLAN_MODULE_CALLS.with(|c| c.get());
    assert_eq!(count, 3, "plan_module called {} times, expected 3", count);
}

#[test]
fn frontend_to_codegen_pretyped_pipeline_types_exactly_three_times() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let cap = crate::telemetry::Capture::new();
    tel.attach(&[], cap.handler());

    let src = "fn id(x), do: x\nfn main(), do: print(id(42))\n";
    let mut t = crate::types::ConcreteTypes;
    let frontend = match crate::frontend::compile_source_with_types(
        &mut t,
        src.to_string(),
        "test.fz".to_string(),
        &tel,
    ) {
        Ok(frontend) => frontend,
        Err(_) => panic!("frontend"),
    };

    compile_pretyped(&mut t, &frontend.module, &frontend.module_types, &tel).expect("compile");

    assert_eq!(
        cap.count(&["fz", "planner", "planned"]),
        2,
        "frontend-to-codegen pretyped path should reuse frontend ModulePlan while the internal destination retype stays telemetry-silent"
    );
}

#[test]
fn resolve_tcc_body_handles_callclosure_with_captures() {
    let src = r#"
fn each(_, []), do: nil
fn each(f, [h | t]) do
  f(h)
  each(f, t)
end

fn main() do
  k = 10
  each(fn(x) -> print(x + k), [1, 2, 3])
end
"#;
    let m = lower_src(src);
    let mt = crate::ir_planner::plan_module(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    );
    let mut t = crate::types::ConcreteTypes;
    let mut reg = SpecRegistry::new();
    let mut spec_keys: Vec<_> = mt.specs.keys().cloned().collect();
    spec_keys.sort_by(|a, b| {
        a.fn_id
            .0
            .cmp(&b.fn_id.0)
            .then_with(|| format!("{:?}", a.input).cmp(&format!("{:?}", b.input)))
            .then_with(|| format!("{:?}", a.demand).cmp(&format!("{:?}", b.demand)))
    });
    for key in spec_keys {
        reg.register(&t, key.fn_id, key.input);
    }

    let mut found = None;
    for (key, ft) in &mt.specs {
        for f in &m.fns {
            for blk in &f.blocks {
                if let Term::CallClosure { closure, args, .. } = &blk.terminator
                    && ft
                        .vars
                        .get(closure)
                        .and_then(|ty| t.closure_lit_parts(ty))
                        .is_some()
                    && key.fn_id == f.id
                {
                    found = Some((f.id, key.input.clone(), *closure, args.clone(), ft));
                    break;
                }
            }
            if found.is_some() {
                break;
            }
        }
        if found.is_some() {
            break;
        }
    }

    let (caller_fid, caller_key, closure, args, ft) =
        found.expect("expected a typed CallClosure over a singleton closure-lit");
    let mut ct = crate::types::ConcreteTypes;
    let (body_fid, body_sid) = resolve_tcc_body(&mut ct, &closure, &args, ft, &m, &reg)
        .expect("closure body should resolve");
    assert_eq!(m.fn_by_id(caller_fid).name, "fn_clause_1");
    let caller_closure_ty = match &caller_key[0] {
        Some(ty) => ty,
        None => panic!("caller key slot 0 should be observed"),
    };
    let crate::types::ClosureLitInfo {
        target: closure_target,
        captures,
    } = t
        .closure_lit_parts(caller_closure_ty)
        .expect("caller key slot 0 should be a singleton closure-lit");
    let closure_fn_id: FnId = closure_target.into();
    // Recursive entry keys widen numeric call arguments immediately, but
    // closure captures remain part of the closure value identity.
    assert_eq!(captures, &[t.int_lit(10)]);
    assert_eq!(
        m.fn_by_id(closure_fn_id).name,
        m.fn_by_id(body_fid).name,
        "slot 0 closure-lit should target the same lambda body resolve_tcc_body picked"
    );
    let h_expected = t.int();
    assert_eq!(caller_key[1], Some(h_expected.clone()));
    let h_list_expected = t.list(h_expected.clone());
    assert_eq!(caller_key[2], Some(h_list_expected));
    assert!(
        m.fn_by_id(body_fid).name.starts_with("lambda_"),
        "expected resolved body to be the synthesized lambda, got {}",
        m.fn_by_id(body_fid).name
    );
    let resolved_key: Vec<KeySlot> = reg
        .iter()
        .find(|(sid, _)| sid.0 == body_sid)
        .map(|(_, key)| key.input.clone())
        .expect("resolved sid registered");
    assert_eq!(resolved_key.len(), 2, "resolved key shape: [capture, x]");
    // Capture identity is preserved; the call argument is widened.
    let k_expected = t.int_lit(10);
    assert_eq!(resolved_key[0], Some(k_expected));
    assert_eq!(resolved_key[1], Some(h_expected));
}

#[test]
fn tailcall_closure_capture_repro_emits_live_cont_body() {
    let src = r#"
fn each(_, []), do: nil
fn each(f, [h | t]) do
  f(h)
  each(f, t)
end

fn main() do
  k = 10
  each(fn(x) -> print(x + k), [1, 2, 3])
end
"#;
    let m = lower_src(src);
    ir_text_record_enable();
    let _ = compile(
        &mut crate::types::ConcreteTypes,
        &m,
        &crate::telemetry::NullTelemetry,
    )
    .expect("compile");
    let ir = ir_text_record_take();
    let names: Vec<String> = ir.iter().map(|(name, _)| name.clone()).collect();
    let cont_body = ir
        .iter()
        .find(|(name, _)| name.starts_with("k_"))
        .map(|(_, body)| body.as_str())
        .unwrap_or_else(|| panic!("expected emitted k_* body, saw {:?}", names));
    assert!(
        !cont_body.contains("trap user"),
        "k_* continuation should not compile as an unreached trap stub:\n{}",
        cont_body
    );
    assert!(
        cont_body.contains("@fz_closure_get_capture_ref")
            && cont_body.contains("call fn0")
            && cont_body.contains("call fn3"),
        "k_* continuation should project captures through the closure env accessors:\n{}",
        cont_body
    );
}

#[test]
fn tailcall_closure_capture_repro_marks_cont_spec_reachable() {
    let src = r#"
fn each(_, []), do: nil
fn each(f, [h | t]) do
  f(h)
  each(f, t)
end

fn main() do
  k = 10
  each(fn(x) -> print(x + k), [1, 2, 3])
end
"#;
    let m = lower_src(src);
    let mut ct = crate::types::ConcreteTypes;
    let mt = crate::ir_planner::plan_module(&mut ct, &m, &crate::telemetry::NullTelemetry);
    let mut reg = SpecRegistry::new();
    let mut spec_keys: Vec<_> = mt.specs.keys().cloned().collect();
    spec_keys.sort_by(|a, b| {
        a.fn_id
            .0
            .cmp(&b.fn_id.0)
            .then_with(|| format!("{:?}", a.input).cmp(&format!("{:?}", b.input)))
            .then_with(|| format!("{:?}", a.demand).cmp(&format!("{:?}", b.demand)))
    });
    let mut cont_sids: Vec<u32> = Vec::new();
    for key in spec_keys {
        let sid = reg.register(&ct, key.fn_id, key.input);
        if m.fn_by_id(key.fn_id).name.starts_with("k_") {
            cont_sids.push(sid.0);
        }
    }
    let main_fid = m
        .fns
        .iter()
        .find(|f| f.name == "main")
        .map(|f| f.id.0)
        .expect("expected main fn");
    let reachable = crate::ir_planner::reachable_specs(&mut ct, &m, &reg, &mt, [main_fid]);
    assert!(!cont_sids.is_empty(), "expected at least one k_* spec");
    // Closure captures stay part of the closure identity, so the k_* cont
    // spec remains reachable from main and must not be emitted as a trap.
    assert!(
        cont_sids.iter().any(|sid| reachable.contains(sid)),
        "expected at least one k_* spec to be reachable from main; \
         cont_sids={:?}, reached={:?}",
        cont_sids,
        reachable,
    );
}

// ===== fz-s9y.4 — empty list ≠ nil =====

/// fz-s9y.4 — `fn f([])` does NOT match a `nil` argument. Pre-fz-s9y,
/// `nil` and `[]` shared a runtime bit pattern, so this call would
/// have matched the `[]` clause and returned 1. After the split,
/// `nil` falls through to `:function_clause` halt.
#[test]
fn nil_does_not_match_empty_list_pattern() {
    // function_clause is intern id 1 (see prelude in ir_lower).
    let halt = run_main("fn f([]), do: 1\nfn main(), do: f(nil)");
    // Halt value of the atom :function_clause is its id (1).
    // Confirmed by the existing atom_const_returns_atom_id test.
    // fz-axu.13 — Utf8 module shifted the prelude's atom-intern order;
    // function_clause now lands at id 3 (nil=0, true=1, false=2 are
    // reserved; function_clause interns first among the prelude's
    // multi-clause dispatch atoms).
    assert_eq!(
        halt, 3,
        "expected :function_clause halt (id=3); got {}",
        halt
    );
}

/// fz-s9y.4 — `fn f(nil)` does NOT match an `[]` argument. Symmetric
/// to the above. Pre-fz-s9y the call would have matched the `nil`
/// clause via conflation.
#[test]
fn empty_list_does_not_match_nil_pattern() {
    let halt = run_main("fn f(nil), do: 1\nfn main(), do: f([])");
    // fz-axu.13 — Utf8 module shifted the prelude's atom-intern order;
    // function_clause now lands at id 3 (nil=0, true=1, false=2 are
    // reserved; function_clause interns first among the prelude's
    // multi-clause dispatch atoms).
    assert_eq!(
        halt, 3,
        "expected :function_clause halt (id=3); got {}",
        halt
    );
}

/// fz-s9y.4 — `print(nil)` and `print([])` render as distinct strings.
/// The fixtures/empty_list_distinct_from_nil fixture exercises this
/// end-to-end; this is the focused codegen-level pin.
#[test]
fn print_distinguishes_nil_from_empty_list() {
    let lines = capture_main("fn main() do\n  print(nil)\n  print([])\nend");
    assert_eq!(lines, vec!["nil".to_string(), "[]".to_string()]);
}

// ===== fz-swt.10 — refcount + dtor on the JIT path =========================
//
// Same shape as the interp-leg tests in `ir_interp::resource_bif_tests` but
// run through the JIT path: `compile(&mut crate::types::ConcreteTypes, &module).run(main_fn)`. The JIT lowers
// the `make_resource(payload, &dwrap/1)` call to an extern call against the
// `fz_make_resource` symbol bound in `JitBackend::new()`; that symbol
// dispatches through the `MakeResourceHook` we install for the duration of
// the test (the helper takes a `&Module` so the hook thunk can walk the
// dtor closure's IR body — see `src/runtime.rs`).
//
// Dtor firing relies on the per-process MSO sweep running at heap drop. The
// `heap_reset_for_test` call between tests drops the previous test's
// DEFAULT_PROCESS heap (and so fires any unrooted Resource dtors from
// earlier runs into a fresh counter snapshot).

mod resource_jit_tests {
    use super::*;
    use crate::ir_interp::{
        tests_support_dtor_fired, tests_support_dtor_last_payload, tests_support_dtor_reset,
        tests_support_lock,
    };

    /// Drive `main` through the JIT with the `MakeResourceHook` wired up
    /// to walk `module`. Returns after the heap has been dropped so the
    /// dtor counters reflect every Resource the run produced.
    fn run_jit_with_resources(src: &str) {
        let module = lower_src(src);
        let entry = module.fn_by_name("main").expect("main fn").id;
        let compiled = compile(
            &mut crate::types::ConcreteTypes,
            &module,
            &crate::telemetry::NullTelemetry,
        )
        .expect("compile");
        // Install the make-resource hook against this module so the JIT-
        // emitted call into `fz_make_resource` resolves the dtor closure.
        let prev = crate::runtime::install_make_resource_hook_with_module(&module);
        heap_reset_for_test();
        let _ = compiled.run(entry);
        // Drop the per-test DEFAULT_PROCESS to fire MSO sweep + dtors.
        heap_reset_for_test();
        crate::runtime::clear_make_resource_hook_with_module(prev);
    }

    /// fz-swt.10 acceptance — JIT-leg round trip mirroring
    /// `make_resource_bif_round_trip` from the interp leg.
    #[test]
    fn make_resource_round_trip_in_jit() {
        let _g = tests_support_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tests_support_dtor_reset();
        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn main() do
  r = make_resource(42, &dwrap/1)
  nil
end
"#;
        run_jit_with_resources(src);
        assert_eq!(
            tests_support_dtor_fired(),
            1,
            "JIT-built resource must fire its dtor exactly once at heap drop",
        );
        assert_eq!(
            tests_support_dtor_last_payload(),
            42,
            "fz-4mk: dtor body runs as fz code; `:: integer` marshal class unboxes \
             before the C extern, so the recorded payload is the raw int 42",
        );
    }

    /// fz-swt.10 acceptance — aliasing inside one JIT-run process still
    /// produces exactly one dtor invocation. Mirrors the interp leg's
    /// `aliasing_in_one_process_fires_dtor_once`.
    #[test]
    fn aliasing_in_one_jit_process_fires_dtor_once() {
        let _g = tests_support_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tests_support_dtor_reset();
        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn main() do
  r1 = make_resource(7, &dwrap/1)
  r2 = r1
  r3 = r2
  nil
end
"#;
        run_jit_with_resources(src);
        assert_eq!(
            tests_support_dtor_fired(),
            1,
            "three JIT-bound aliases of one resource must still produce one dtor call",
        );
        assert_eq!(tests_support_dtor_last_payload(), 7);
    }

    /// fz-swt.10 acceptance — two distinct `make_resource` calls each
    /// fire once. Mirrors the interp leg's
    /// `two_distinct_resources_each_fire_once`.
    #[test]
    fn two_distinct_resources_in_jit_each_fire_once() {
        let _g = tests_support_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tests_support_dtor_reset();
        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn main() do
  a = make_resource(11, &dwrap/1)
  b = make_resource(22, &dwrap/1)
  nil
end
"#;
        run_jit_with_resources(src);
        assert_eq!(
            tests_support_dtor_fired(),
            2,
            "two distinct JIT-built resources must each fire their dtor exactly once",
        );
    }
}
