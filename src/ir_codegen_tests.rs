use super::*;
use crate::ir_lower::lower_program;
use crate::lexer::Lexer;
use crate::parser::Parser;

fn lower_src(src: &str) -> Module {
    let toks = Lexer::new(src).tokenize().expect("lex");
    let prog = Parser::new(toks).parse_program().expect("parse");
    lower_program(&prog).expect("lower")
}

fn join_return_descrs(
    f: &crate::fz_ir::FnIr,
    ft: &crate::ir_typer::FnTypes,
) -> crate::types::Descr {
    let mut joined: Option<crate::types::Descr> = None;
    for b in &f.blocks {
        if let Term::Return(v) = &b.terminator {
            let d = ft
                .vars
                .get(v)
                .cloned()
                .unwrap_or_else(crate::types::Descr::any);
            joined = Some(match joined {
                Some(prev) => prev.union(&d),
                None => d,
            });
        }
    }
    joined.unwrap_or_else(crate::types::Descr::any)
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
    let compiled = crate::ir_codegen::with_reducer_disabled(|| compile(&m).expect("compile"));
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
            "static-closure stub_fp must be a resolved address"
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
    let compiled = crate::ir_codegen::with_reducer_disabled(|| compile(&m).expect("compile"));
    let targets = compiled.static_closure_targets();
    let (cl_sid, _, _, _) = *targets.first().expect("at least one static closure target");
    let mut p = compiled.make_process();
    let prev = fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(&mut p as *mut Process));
    let a = fz_runtime::ir_runtime::fz_get_static_closure(cl_sid);
    let b = fz_runtime::ir_runtime::fz_get_static_closure(cl_sid);
    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
    assert_eq!(a, b, "static-closure lookup must return the same pointer");
    assert_ne!(a, 0, "static-closure lookup must return non-null");
}

#[test]
fn aot_compile_produces_object_with_main_symbol() {
    let src = "fn add1(n) do n + 1 end\nfn main() do print(add1(41)) end";
    let m = lower_src(src);
    let artifact = compile_aot(&m, "add1_smoke").expect("compile_aot");
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
    compile(&m).unwrap().run(entry)
}

fn run_main_after_heap_reset(src: &str) -> (i64, Module) {
    let m = lower_src(src);
    let entry = m.fn_by_name("main").unwrap().id;
    heap_reset_for_test();
    let r = compile(&m).unwrap().run(entry);
    (r, m)
}

fn capture_main(src: &str) -> Vec<String> {
    let m = lower_src(src);
    let entry = m.fn_by_name("main").unwrap().id;
    heap_reset_for_test();
    let _ = test_capture_take();
    let _ = compile(&m).unwrap().run(entry);
    test_capture_take()
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
    // `:ok` halts as the atom's u32 id (well, the FzValue bits which
    // encode (id << 3) | TAG_ATOM = 0b010). Run two Processes; the
    // halt value must match because the atom id was assigned once
    // at compile time.
    let src = "fn main(), do: :ok";
    let m = lower_src(src);
    let compiled = compile(&m).unwrap();
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
    let ca = compile(&ma).unwrap();
    let cb = compile(&mb).unwrap();
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
fn unop_neg_runs() {
    assert_eq!(run_main("fn main(), do: -7"), -7);
}

#[test]
fn atom_const_returns_atom_id() {
    // match_error (id=0) and function_clause (id=1) intern during prelude
    // lowering; :ok is the next user atom (id=2).
    assert_eq!(run_main("fn main(), do: :ok"), 2);
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
fn render_fz_value_dispatches_per_tag() {
    use fz_runtime::fz_value::FzValue;
    assert_eq!(
        fz_runtime::fz_value::debug::render(FzValue::from_int(42).0),
        "42"
    );
    assert_eq!(
        fz_runtime::fz_value::debug::render(FzValue::from_int(0).0),
        "0"
    );
    assert_eq!(
        fz_runtime::fz_value::debug::render(FzValue::from_int(-7).0),
        "-7"
    );
    assert_eq!(fz_runtime::fz_value::debug::render(FzValue::NIL.0), "nil");
    assert_eq!(fz_runtime::fz_value::debug::render(FzValue::TRUE.0), "true");
    assert_eq!(
        fz_runtime::fz_value::debug::render(FzValue::FALSE.0),
        "false"
    );
    // Atom rendering needs a populated Process.atom_names; with an
    // empty table render falls back to `:atom_N`. The full
    // source-name path is verified end-to-end by the fixture matrix
    // (hello.fz post fz-ul4.25 re-bless).
    assert_eq!(
        fz_runtime::fz_value::debug::render(FzValue::from_atom_id(3).0),
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
    assert_eq!(run_main("fn main(), do: [1, 2] == [1, 2, 3]"), 0);
}

#[test]
fn tuple_structural_eq_same_arity_and_content() {
    assert_eq!(run_main("fn main(), do: {1, :ok} == {1, :ok}"), 1);
}

#[test]
fn tuple_eq_different_arity_is_false() {
    assert_eq!(run_main("fn main(), do: {1, 2} == {1, 2, 3}"), 0);
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
    assert_eq!(run_main("fn main(), do: %{a: 1, b: 2} == %{a: 1, b: 3}"), 0);
}

#[test]
fn heterogeneous_kinds_compare_unequal() {
    assert_eq!(run_main("fn main(), do: [1, 2] == {1, 2}"), 0);
}

#[test]
fn nested_map_with_list_structural_eq() {
    assert_eq!(run_main("fn main(), do: %{x: [1, 2]} == %{x: [1, 2]}"), 1);
}

#[test]
fn neq_inverts_structural_eq() {
    assert_eq!(run_main("fn main(), do: [1, 2] != [1, 2]"), 0);
    assert_eq!(run_main("fn main(), do: [1, 2] != [1, 3]"), 1);
}

// ----- .11.20 boxed-float tests -----

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
    assert_eq!(run_main("fn main(), do: 1 == 1.0"), 0);
}

#[test]
fn distinct_boxed_floats_compare_equal_by_value() {
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
    let p = fz_runtime::fz_value::FzValue(halt).unbox_ptr().unwrap();
    let bytes = unsafe { std::slice::from_raw_parts((p as *const u8).add(24), 8) };
    let mut buf = [0u8; 8];
    buf.copy_from_slice(bytes);
    let f = f64::from_bits(u64::from_be_bytes(buf));
    assert_eq!(f, 2.5);
}

// ----- .11.14 vec tests -----

#[test]
fn print_vec_i64_renders_via_jit() {
    assert_eq!(
        capture_main("fn main(), do: print(~v[1, 2, 3])"),
        vec!["~v[1, 2, 3]"]
    );
}

#[test]
fn print_vec_u8_renders_via_jit() {
    assert_eq!(
        capture_main("fn main(), do: print(~b[0xff, 0xab])"),
        vec!["~b[255, 171]"]
    );
}

#[test]
fn print_vec_bit_renders_via_jit() {
    assert_eq!(
        capture_main("fn main(), do: print(~bits[1, 0, 1, 1])"),
        vec!["~bits[1, 0, 1, 1]"]
    );
}

#[test]
fn vec_f64_codegen_blocks_with_pointer_to_followup_ticket() {
    // ~v[1.0, 2.0] lowers fine post-.24.5 but codegen still gates VecF64 at .11.23.
    let m = lower_src("fn main(), do: ~v[1.0, 2.0]");
    let err = match compile(&m) {
        Ok(_) => panic!("VecF64 codegen should be gated"),
        Err(e) => e,
    };
    let msg = format!("{:?}", err);
    assert!(msg.contains("11.23"), "expected ticket reference: {}", msg);
}

#[test]
fn vec_get_returns_indexed_element() {
    assert_eq!(run_main("fn main(), do: vec_get(~v[10, 20, 30], 1)"), 20);
}

#[test]
fn vec_get_out_of_bounds_returns_nil() {
    assert_eq!(run_main("fn main(), do: vec_get(~v[1, 2], 10)"), 0);
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
// source) so the typer is forced to retain dispatch. Keeping them
// hand-built is the cleanest expression of the assertion.

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
    let _ = compile(m).unwrap();
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
    // Descrs.
    let m = lower_src("fn add(a, b) do a + b end\nfn main() do print(add(1, 2)) end");
    let mt = crate::ir_typer::type_module(&m);
    let add_idx = m.fns.iter().position(|f| f.name == "add").unwrap();
    let ft = mt.any_spec_for(m.fns[add_idx].id).expect("registered spec");
    let rd = join_return_descrs(&m.fns[add_idx], ft);
    let prs = build_param_reprs(&m.fns[add_idx], ft);
    let sig = build_fn_signature(&prs, ArgRepr::from_descr(&rd), false, true, None);
    assert_eq!(sig.params.len(), 2);
    assert_eq!(sig.returns.len(), 1);
    assert_eq!(sig.params[0].value_type, types::I64);
    assert_eq!(sig.params[1].value_type, types::I64);
    assert_eq!(sig.returns[0].value_type, types::I64);
}

#[test]
fn signature_native_uses_typed_params_and_cont() {
    // Same `add` fn, this time the typer has narrowed entry params to
    // int via call-site narrowing. Native sig should be
    // `(i64, i64, cont: i64) -> i64`.
    // fz-cps.1.a (fz-siu.1.1): trailing cont:i64 per §2.1.
    let m = lower_src("fn add(a, b) do a + b end\nfn main() do print(add(1, 2)) end");
    let mt = crate::ir_typer::type_module(&m);
    let add_idx = m.fns.iter().position(|f| f.name == "add").unwrap();
    let ft = mt.any_spec_for(m.fns[add_idx].id).expect("registered spec");
    let rd = join_return_descrs(&m.fns[add_idx], ft);
    let prs = build_param_reprs(&m.fns[add_idx], ft);
    let sig = build_fn_signature(&prs, ArgRepr::from_descr(&rd), true, false, None);
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
    // .27.13: native sig is per-Descr typed. For `dist(x, y)` called
    // with `dist(1.5, 2.5)`, call-site narrowing types `x` and `y` as
    // float-only → AbiParam(f64). Return joins every Term::Return val
    // Descr; here that's float-only → f64.
    // fz-cps.1.a (fz-siu.1.1): trailing cont:i64 per §2.1.
    let m =
        lower_src("fn dist(x, y) do x * x + y * y end\nfn main() do print(dist(1.5, 2.5)) end");
    let mt = crate::ir_typer::type_module(&m);
    let dist_idx = m.fns.iter().position(|f| f.name == "dist").unwrap();
    let ft = mt
        .any_spec_for(m.fns[dist_idx].id)
        .expect("registered spec");
    let rd = join_return_descrs(&m.fns[dist_idx], ft);
    let prs = build_param_reprs(&m.fns[dist_idx], ft);
    let sig = build_fn_signature(&prs, ArgRepr::from_descr(&rd), true, false, None);
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
    // Two-fn module. After compile(), spec_registry holds one any-key
    // spec per fn; the SpecId.0 == FnId.0 invariant is asserted at
    // build time (debug_assert in compile_with_backend).
    let m = lower_src("fn add(a, b) do a + b end\nfn main() do print(add(1, 2)) end");
    let compiled = compile(&m).unwrap();
    // Drive a run to ensure the pipeline ran the registry construction
    // path; the assertion lives in compile_with_backend.
    let _ = compiled.run(m.fn_by_name("main").unwrap().id);
}

#[test]
fn spec_registry_any_key_lookup() {
    // Use the registry directly to verify register/resolve/any_key
    // contracts. Doesn't go through compile().
    let mut reg = SpecRegistry::new();
    let fid = FnId(0);
    let any_key_2 = vec![crate::types::Descr::any(); 2];
    let sid = reg.register(fid, any_key_2.clone());
    assert_eq!(sid.0, 0, "first registration gets SpecId(0)");
    // Re-registering the same key returns the same SpecId.
    let sid2 = reg.register(fid, any_key_2.clone());
    assert_eq!(sid, sid2);
    // Resolve roundtrips.
    let resolved = reg.resolve(fid, &any_key_2);
    assert_eq!(resolved, Some(sid));
    // any_key helper.
    let via_any = reg.any_key(fid, 2);
    assert_eq!(via_any, sid);
    // A different fn gets a different SpecId.
    let other_sid = reg.register(FnId(1), vec![]);
    assert_eq!(other_sid.0, 1);
    assert_eq!(reg.len(), 2);
}

#[test]
fn spec_registry_distinct_narrow_keys() {
    // The registry distinguishes narrow keys via the exact-match
    // fast path. Subsumption fallback is exercised below.
    let mut reg = SpecRegistry::new();
    let fid = FnId(0);
    let int1 = vec![crate::types::Descr::int()];
    let float1 = vec![crate::types::Descr::float()];
    let sid_int = reg.register(fid, int1.clone());
    let sid_float = reg.register(fid, float1.clone());
    assert_ne!(
        sid_int, sid_float,
        "int-key and float-key must be distinct SpecIds"
    );
    // Exact-match fast path returns identity.
    assert_eq!(reg.resolve(fid, &int1), Some(sid_int));
    assert_eq!(reg.resolve(fid, &float1), Some(sid_float));
    // No covering spec for atom under the registered set → None.
    let atom1 = vec![crate::types::Descr::atom_top()];
    assert_eq!(reg.resolve(fid, &atom1), None);
}

// ----- fz-ul4.29.11: subsumption-based callsite dispatch -----

#[test]
fn resolve_subsumes_narrower_query_to_wider_registered_spec() {
    // Only [int] registered; query [int_lit(4)] should subsume to it.
    let mut reg = SpecRegistry::new();
    let fid = FnId(0);
    let int_spec = reg.register(fid, vec![crate::types::Descr::int()]);
    let q = vec![crate::types::Descr::int_lit(4)];
    assert_eq!(reg.resolve(fid, &q), Some(int_spec));
}

#[test]
fn resolve_picks_narrowest_among_multiple_supertype_matches() {
    // Both [int] and [any] cover [int_lit(4)]. [int] is narrower; pick it.
    let mut reg = SpecRegistry::new();
    let fid = FnId(0);
    let any_spec = reg.register(fid, vec![crate::types::Descr::any()]);
    let int_spec = reg.register(fid, vec![crate::types::Descr::int()]);
    let q = vec![crate::types::Descr::int_lit(4)];
    let resolved = reg.resolve(fid, &q);
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
    let fid = FnId(0);
    reg.register(fid, vec![crate::types::Descr::float()]);
    let q = vec![crate::types::Descr::int_lit(4)];
    assert_eq!(
        reg.resolve(fid, &q),
        None,
        "int_lit(4) is not a subtype of float; no covering spec"
    );
}

#[test]
fn resolve_subtype_incomparable_picks_lowest_specid() {
    // [int, any] (sid A) and [any, atom] (sid B). Query [int_lit(4), :foo]
    // is covered by both; neither key is a subtype of the other on every
    // axis. Deterministic tiebreak picks the lowest SpecId.
    let mut reg = SpecRegistry::new();
    let fid = FnId(0);
    let int = crate::types::Descr::int();
    let any = crate::types::Descr::any();
    let atom = crate::types::Descr::atom_top();
    let sid_a = reg.register(fid, vec![int.clone(), any.clone()]);
    let sid_b = reg.register(fid, vec![any.clone(), atom.clone()]);
    let q = vec![
        crate::types::Descr::int_lit(4),
        crate::types::Descr::atom_lit(":foo"),
    ];
    let resolved = reg.resolve(fid, &q).expect("a covering spec exists");
    assert_eq!(
        resolved, sid_a,
        "subtype-incomparable matches: lowest SpecId wins; got {:?}, a={:?}, b={:?}",
        resolved, sid_a, sid_b
    );
}

#[test]
fn resolve_exact_match_takes_fast_path() {
    // Exact-match registration resolves to the same SpecId — verifies
    // the O(1) fast path still works alongside subsumption fallback.
    let mut reg = SpecRegistry::new();
    let fid = FnId(0);
    let key = vec![crate::types::Descr::int(), crate::types::Descr::float()];
    let sid = reg.register(fid, key.clone());
    assert_eq!(reg.resolve(fid, &key), Some(sid));
}

#[test]
fn resolve_per_fn_isolation() {
    // Specs for one fn must not subsume queries for a different fn.
    let mut reg = SpecRegistry::new();
    let _sid0 = reg.register(FnId(0), vec![crate::types::Descr::any()]);
    // No spec registered for FnId(1) — even though FnId(0) has an
    // any-key, it shouldn't cover queries to FnId(1).
    let q = vec![crate::types::Descr::int()];
    assert_eq!(reg.resolve(FnId(1), &q), None);
}

// ----- fz-ul4.11.15.6: hot-loop frame alloc reduction -----

/// Pre-inline: each `step(...)` call allocates a continuation frame.
/// Post-inline: `step` is inlined — those allocs vanish.
/// The post count must be < 50% of the pre count.
///
/// Uses 10 nested step calls (step(step(...step(0)...))) so the
/// pre/post ratio is clear without triggering the multi-clause
/// dispatch codegen path that requires the inliner to succeed.
#[test]
fn hot_loop_inline_reduces_frame_allocs() {
    // 10 nested calls to step — each is a Call+Cont site pre-inline.
    let src = "fn step(x), do: x + 1\n\
               fn main(), do: step(step(step(step(step(step(step(step(step(step(0))))))))))";

    // Pre-inline run: compile with the inliner bypassed.
    let pre_count = with_inline_disabled(|| {
        let m = lower_src(src);
        fz_runtime::ir_runtime::frame_alloc_count_reset();
        let entry = m.fn_by_name("main").unwrap().id;
        let r = compile(&m).unwrap().run(entry);
        assert_eq!(r, 10, "pre-inline result must be 10");
        fz_runtime::ir_runtime::frame_alloc_count_take()
    });

    // Post-inline run: normal compile (inliner active).
    let m = lower_src(src);
    fz_runtime::ir_runtime::frame_alloc_count_reset();
    let entry = m.fn_by_name("main").unwrap().id;
    let post_result = compile(&m).unwrap().run(entry);
    let post_count = fz_runtime::ir_runtime::frame_alloc_count_take();

    assert_eq!(post_result, 10, "post-inline result must still be 10");
    assert!(
        pre_count >= 5,
        "pre-inline: expected >= 5 allocs for step cont closures, got {}",
        pre_count
    );
    assert!(
        post_count * 2 < pre_count,
        "post-inline frame allocs ({}) must be < 50% of pre-inline ({})",
        post_count,
        pre_count
    );
}

/// fz-zj3 — box_int constant fold: Const::Int(n) lowered as RawInt must be
/// retagged as a single iconst ((n<<3)|TAG_INT), not ishl_imm + bor_imm.
#[test]
fn box_int_const_fold_eliminates_ishl_bor() {
    // send(2, 41) passes integer constants to an extern taking Tagged args.
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
    let _ = compile(&m).unwrap();
    let ir = ir_text_record_take();
    let main_ir = ir
        .iter()
        .find(|(n, _)| n == "main")
        .map(|(_, s)| s.as_str())
        .unwrap_or("");
    // send(2, 41): the tagged forms of 2 and 41 are iconst 17 and iconst 329.
    // The ishl_imm + bor_imm sequence should not appear for these constants.
    assert!(
        main_ir.contains("iconst.i64 17") && main_ir.contains("iconst.i64 329"),
        "expected pre-tagged iconst 17 and 329 for send(2, 41):\n{}",
        main_ir
    );
    assert!(
        !main_ir.contains("ishl_imm"),
        "spurious ishl_imm in main CLIF — box_int fold not applied:\n{}",
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
    let _ = compile(&m).unwrap();
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
    let _ = compile(&m).unwrap();
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

/// fz-h4q — ArgRepr::Condition: pure-branch TypeTest produces no `select`
/// instruction. Before the fix: every boolean prim emitted bool_to_fz eagerly
/// (select + two iconst for true/false), then is_truthy decoded it back to i1.
/// After: the i1 is stored as ArgRepr::Condition and fed directly to brif —
/// zero `select` instructions in the dispatching block.
#[test]
fn pure_branch_type_test_emits_no_select() {
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
    let _ = compile(&m).unwrap();
    let ir = ir_text_record_take();
    let with_brif: Vec<(&str, &str)> = ir
        .iter()
        .filter(|(_, s)| s.contains("brif"))
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect();
    for (n, s) in &with_brif {
        assert!(
            !s.contains("select"),
            "spurious select in {} CLIF — bool_to_fz was emitted eagerly:\n{}",
            n,
            s
        );
    }
}

/// fz-2tc — unit-return extern results whose dest var is unused emit no
/// iconst at all (DeadUnit path). Live results use cached_iconst so they
/// share an existing nil if the same block already holds one.
/// hello: print(42), print(:ok), print(true) are all unit-return externs
/// whose nil results are dead — only print(nil)'s result is live (passed
/// to the continuation). Before: 5 × `iconst.i64 3`. After: ≤ 2.
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
    let _ = compile(&m).unwrap();
    let ir = ir_text_record_take();
    let main_ir = ir
        .iter()
        .find(|(n, _)| n == "main")
        .map(|(_, s)| s.as_str())
        .unwrap_or("");
    // Dead nil results are gone. Count occurrences of "iconst.i64 3".
    let nil_count = main_ir.matches("iconst.i64 3").count();
    assert!(
        nil_count <= 2,
        "expected ≤ 2 nil iconsts in main CLIF (got {}); dead unit results not elided:\n{}",
        nil_count,
        main_ir
    );
    // The live nil (used as continuation arg) must still be present.
    assert!(
        main_ir.contains("iconst.i64 3"),
        "expected at least one nil iconst:\n{}",
        main_ir
    );
}

/// fz-o2g — Const::Nil/Bool/Atom through cached_iconst. The nil arg
/// to print(nil) and the live unit-extern result both call
/// cached_iconst(NIL_BITS) and must share the same SSA value — one
/// iconst.i64 3, not two.
#[test]
fn const_nil_bool_atom_deduplicated_within_block() {
    let src = "fn main() do\n\
                 print(nil)\n\
               end";
    let m = lower_src(src);
    ir_text_record_enable();
    let _ = compile(&m).unwrap();
    let ir = ir_text_record_take();
    let main_ir = ir
        .iter()
        .find(|(n, _)| n == "main")
        .map(|(_, s)| s.as_str())
        .unwrap_or("");
    let nil_count = main_ir.matches("iconst.i64 3").count();
    assert_eq!(
        nil_count, 1,
        "expected exactly 1 nil iconst in main (Const::Nil and unit-extern result share via cached_iconst), got {}:\n{}",
        nil_count, main_ir
    );
}

/// fz-5j5.2 — type_module is called exactly 2 times in the codegen
/// pipeline. The earlier 3-call shape had a redundant middle call:
/// rewrite_vec_kinds and rewrite_known_target_closures read/write
/// orthogonal slices of ModuleTypes, so they share one pre-rewrite
/// snapshot. Pre-rewrite + post-reduce = 2 genuinely distinct typings.
#[test]
fn type_module_called_exactly_twice_in_pipeline() {
    let src = "fn main(), do: print(42)";
    let m = lower_src(src);
    crate::ir_typer::TYPE_MODULE_CALLS.with(|c| c.set(0));
    compile(&m).expect("compile");
    let count = crate::ir_typer::TYPE_MODULE_CALLS.with(|c| c.get());
    assert_eq!(count, 2, "type_module called {} times, expected 2", count);
}
