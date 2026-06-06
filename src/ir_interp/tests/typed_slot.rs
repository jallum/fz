use crate::exec::runtime::DbgCapture;
use crate::frontend::{FrontendOk, compile_source_with_types};
use crate::ir_interp::*;
use crate::ir_lower::lower_program;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::bus::ConfiguredTelemetry;
use crate::test_support::linked_runtime_graph;
use fz_runtime::any_value::ListCons;
use fz_runtime::any_value::ValueKind;
use std::ptr::null_mut;

use crate::fz_ir::Module;

fn compile_source(src: String, source_name: String) -> FrontendOk {
    let mut t = crate::types::new();
    let tel = ConfiguredTelemetry::new();
    compile_source_with_types(&mut t, src, source_name, &tel)
        .unwrap_or_else(|err| panic!("frontend: {:?}", err.diagnostics))
}

fn lower_src(src: &str) -> Module {
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower")
}

fn run(src: &str) -> i64 {
    let m = lower_src(src);
    run_main(&crate::telemetry::ConfiguredTelemetry::new(), &m).expect("interp run")
}

fn run_checked(src: &str) -> i64 {
    let frontend = compile_source(src.to_string(), "interp-test.fz".to_string());
    run_main(&crate::telemetry::ConfiguredTelemetry::new(), &frontend.module).expect("interp run")
}

fn run_runtime_graph(src: &str) -> i64 {
    let mut graph = linked_runtime_graph(src, &crate::telemetry::ConfiguredTelemetry::new());
    let module = graph.linked_module().clone();
    let module_plan = graph.linked_module_plan().clone();
    let (halt, _) = run_main_with_plan(
        graph.types(),
        &crate::telemetry::ConfiguredTelemetry::new(),
        &module,
        module_plan,
    )
    .expect("interp run");
    halt
}

fn capture_runtime_graph(src: &str) -> String {
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());
    let mut graph = linked_runtime_graph(src, &tel);
    let module = graph.linked_module().clone();
    let module_plan = graph.linked_module_plan().clone();
    run_main_with_plan(graph.types(), &tel, &module, module_plan).expect("interp run");
    dbg.lines().join("\n")
}

fn capture(src: &str) -> String {
    let m = lower_src(src);
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());
    run_main(&tel, &m).expect("interp run");
    dbg.lines().join("\n")
}

fn checked_halt_and_closure_allocs(src: &str) -> (i64, u64) {
    let frontend = compile_source(src.to_string(), "interp-test.fz".to_string());
    let (halt, runtime) =
        run_main_with_runtime(&crate::telemetry::ConfiguredTelemetry::new(), &frontend.module).expect("interp run");
    let task = runtime.task(1).expect("main task remains registered");
    let closure_allocs = task.heap.alloc_stats_snapshot().closure.allocs;
    (halt, closure_allocs)
}

fn checked_halt_and_capture(src: &str) -> (i64, String, Module) {
    let frontend = compile_source(src.to_string(), "interp-test.fz".to_string());
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());
    let (halt, _runtime) = run_main_with_runtime(&tel, &frontend.module).expect("interp run");
    (halt, dbg.lines().join("\n"), frontend.module)
}

#[test]
fn interp_typed_int_arithmetic_full_i64() {
    assert_eq!(run("fn main(), do: 4611686018427387904 + 7"), 4611686018427387911);
}

#[test]
fn interp_static_protocol_dispatch_uses_planned_impl() {
    assert_eq!(
        run_checked(
            r#"
defprotocol Integerish do
  fn id(value)
end

defimpl Integerish, for: Integer do
  fn id(value), do: value + 1
end

fn main(), do: Integerish.id(41)
"#,
        ),
        42
    );
}

#[test]
fn interp_typed_float_raw() {
    assert_eq!(f64::from_bits(run("fn main(), do: 1.5 + 2.5") as u64), 4.0);
}

#[test]
fn interp_render_raw_float_in_container() {
    assert_eq!(capture("fn main(), do: dbg([1.5])"), "[1.5]");
}

#[test]
fn interp_named_fn_ref_does_not_allocate_closure_object() {
    let (halt, closure_allocs) = checked_halt_and_closure_allocs(
        r#"
        fn id(x), do: x
        fn apply(f, x), do: f.(x)
        fn main() do
          f = &id/1
          r = apply(f, 41)
          r
        end
    "#,
    );
    assert_eq!(halt, 41);
    assert_eq!(
        closure_allocs, 0,
        "thin named fn refs should not allocate closure objects in interp"
    );
}

#[test]
fn interp_zero_capture_lambda_does_not_allocate_closure_object() {
    let (halt, closure_allocs) = checked_halt_and_closure_allocs(
        r#"
        fn apply(f, x), do: f.(x)
        fn main() do
          f = fn (x) -> x end
          r = apply(f, 41)
          r
        end
    "#,
    );
    assert_eq!(halt, 41);
    assert_eq!(
        closure_allocs, 0,
        "zero-capture lambdas lower to thin fn refs and should not allocate closure objects in interp",
    );
}

#[test]
fn interp_captured_lambda_still_allocates_closure_object() {
    let (halt, closure_allocs) = checked_halt_and_closure_allocs(
        r#"
        fn apply(f, x), do: f.(x)
        fn main() do
          k = 7
          f = fn (x) -> x + k end
          r = apply(f, 1)
          r
        end
    "#,
    );
    assert_eq!(halt, 8);
    assert_eq!(closure_allocs, 1, "captured lambdas remain heap closures in interp",);
}

#[test]
fn interp_checked_joined_thin_fn_refs_remain_callable_locally() {
    assert_eq!(
        run_checked(
            r#"
fn add_a(x, acc), do: acc + x
fn add_b(x, acc), do: acc + x

fn main() do
  reducer = case 0 == 0 do
    true -> add_a
    _ -> add_b
  end
  reducer.(1, 0)
end
"#,
        ),
        1
    );
}

#[test]
fn interp_runtime_graph_enum_reduce_wrapper_runs() {
    assert_eq!(
        run_runtime_graph(
            r#"
fn main() do
  Enum.reduce([1, 2, 3], 0, fn (x, acc) -> acc + x end)
end
"#,
        ),
        6
    );
}

#[test]
fn interp_runtime_graph_preserves_planned_continuation_specs_after_non_tail_calls() {
    let got = capture_runtime_graph(
        r#"
fn main() do
  xs = [1, 2, 3, 4, 5]
  range = 1..5

  dbg(Enum.take(xs, 3))
  dbg(Enum.take(xs, 0))
  dbg(Enum.take(xs, 9))
  dbg(Enum.take(xs, -2))
  dbg(Enum.take(range, -2))
end
"#,
    );
    assert_eq!(
        got, "[1, 2, 3]\n[]\n[1, 2, 3, 4, 5]\n[4, 5]\n[4, 5]",
        "interpreter continuations must retain their planner-selected specs across chained non-tail calls",
    );
}

#[test]
fn interp_runtime_graph_joined_thin_fn_refs_remain_callable_across_enum_reduce() {
    assert_eq!(
        run_runtime_graph(
            r#"
fn add_a(x, acc), do: acc + x
fn add_b(x, acc), do: acc + x

fn main() do
  xs = [1, 2, 3]
  stats0 = Process.heap_alloc_stats()
  reducer = case stats0[:allocs] == 0 do
    true -> add_a
    _ -> add_b
  end
  Enum.reduce(xs, 0, reducer)
end
"#,
        ),
        6
    );
}

#[test]
fn frontend_only_checked_interp_surfaces_unlinked_process_heap_alloc_stats_halt() {
    let (halt, got, module) = checked_halt_and_capture(
        r#"
fn main() do
  stats = Process.heap_alloc_stats()
  dbg(stats[:allocs])
  dbg(stats[:closure_allocs])
end
"#,
    );
    let expected = module
        .atom_names
        .iter()
        .position(|name| name == "external_module_unlinked")
        .expect("frontend-only module interns external_module_unlinked") as i64;
    assert_eq!(halt, expected);
    assert_eq!(got, "");
}

#[test]
fn interp_runtime_graph_heap_alloc_stats_exposes_closure_allocs_key() {
    let got = capture_runtime_graph(
        r#"
fn add(x, acc), do: acc + x

fn main() do
  stats0 = Process.heap_alloc_stats()
  dbg(stats0[:closure_allocs])
  f = fn (x) -> x + 1 end
  r = f.(41)
  stats1 = Process.heap_alloc_stats()
  dbg(stats1[:closure_allocs])
  s = add(1, 0)
  dbg(Process.heap_alloc_stats()[:closure_allocs])
end
"#,
    );
    assert_eq!(
        got, "0\n0\n0",
        "linked runtime graph should expose :closure_allocs as a stable atom-keyed map entry",
    );
}

#[test]
fn interp_runtime_graph_heap_alloc_stats_reports_captured_closure_allocs() {
    let got = capture_runtime_graph(
        r#"
fn main() do
  stats0 = Process.heap_alloc_stats()
  dbg(stats0[:closure_allocs])
  k = 7
  f = fn (x) -> x + k end
  r = f.(1)
  stats1 = Process.heap_alloc_stats()
  dbg(stats1[:closure_allocs])
end
"#,
    );
    assert_eq!(
        got, "0\n1",
        "linked runtime graph should report captured closure heap allocations via Process.heap_alloc_stats()",
    );
}

#[test]
fn interp_equality_float_in_container() {
    assert_eq!(run("fn main(), do: [1.5] == [1.5]"), 1);
}

#[test]
fn interp_receive_matcher_float_in_container() {
    assert_eq!(
        run(r#"
            fn main() do
              send(self(), [2.5])
              receive do
                [2.5] -> 7
              end
            end
        "#),
        7
    );
}

#[test]
fn interp_deep_copy_float_in_container_preserves_raw_slot() {
    let m = lower_src(
        r#"
        fn main() do
          send(self(), [2.5])
          nil
        end
    "#,
    );
    let (_, runtime) = run_main_with_runtime(&crate::telemetry::ConfiguredTelemetry::new(), &m).expect("interp run");

    let task = runtime.task(1).expect("main task remains registered");
    let any_ref = task.mailbox.front().expect("self-send remains queued");
    assert_eq!(any_ref.tag(), ValueKind::LIST);
    let list = any_ref.list_addr().expect("mailbox keeps tagged list ref");
    let head = unsafe { (*(list as *const ListCons)).head_value() };
    assert_eq!(head.kind(), ValueKind::FLOAT);
    assert_eq!(f64::from_bits(head.raw()), 2.5);
}

#[test]
fn persistent_runtime_drives_entries_without_resetting_mailbox() {
    let m = lower_src(
        r#"
        fn first() do
          send(self(), 41)
          nil
        end

        fn second() do
          receive do
            x -> x
          end
        end
    "#,
    );
    let first = m.fn_by_name("first").expect("first fn").id;
    let second = m.fn_by_name("second").expect("second fn").id;
    let mut t = crate::types::new();
    let mut runtime = IrInterpRuntime::fresh_with_root(&m);

    runtime.enqueue_entry(&m, 1, first, vec![]).expect("enqueue first");
    let first_done = runtime
        .drive_until_idle(&mut t, &crate::telemetry::ConfiguredTelemetry::new(), Some(1))
        .expect("drive first");
    assert_eq!(first_done.len(), 1);
    assert_eq!(
        runtime.task(1).expect("root task").mailbox.len(),
        1,
        "first drive leaves self-sent message in persistent mailbox",
    );

    runtime.enqueue_entry(&m, 1, second, vec![]).expect("enqueue second");
    let second_done = runtime
        .drive_until_idle(&mut t, &crate::telemetry::ConfiguredTelemetry::new(), Some(1))
        .expect("drive second");
    assert_eq!(second_done.last().and_then(|(_, value)| value.as_i64()), Some(41),);
    assert_eq!(
        runtime.task(1).expect("root task").mailbox.len(),
        0,
        "second drive observes and consumes first drive's message",
    );
}

#[test]
fn interp_reductions_yield_allocation_light_loops() {
    let m = lower_src(
        r#"
        fn count(0, acc), do: acc
        fn count(n, acc), do: count(n - 1, acc + 1)

        fn child(parent) do
          count(5000, 0)
          send(parent, 99)
        end

        fn main() do
          me = self()
          spawn(fn () -> child(me) end)
          count(5000, 0)
          receive do
            x -> x
          end
        end
    "#,
    );

    let (halt, runtime) = run_main_with_runtime(&crate::telemetry::ConfiguredTelemetry::new(), &m).expect("interp run");

    assert_eq!(halt, 99);
    let main = runtime.task(1).expect("main task remains registered");
    let child = runtime.task(2).expect("child task remains registered");
    assert!(
        main.reduction_yields > 0,
        "main should yield on reduction budget exhaustion"
    );
    assert!(
        child.reduction_yields > 0,
        "child should yield on reduction budget exhaustion"
    );
    assert_eq!(main.allocation_pressure_yields, 0);
    assert_eq!(child.allocation_pressure_yields, 0);
    assert_eq!(main.interpreter_yields, 0, "test should be allocation-light");
    assert_eq!(child.interpreter_yields, 0, "test should be allocation-light");
}

#[test]
fn interp_quiet_quanta_moves_only_at_scheduler_boundaries() {
    let m = lower_src(
        r#"
        fn count(0, acc), do: acc
        fn count(n, acc), do: count(n - 1, acc + 1)
        fn main(), do: count(250, 0)
    "#,
    );
    let main = m.fn_by_name("main").expect("main").id;
    let mut t = crate::types::new();
    let mut runtime = IrInterpRuntime::fresh_with_root(&m);
    runtime.enqueue_entry(&m, 1, main, vec![]).expect("enqueue main");
    runtime.task_mut(1).expect("main task").reductions_per_quantum = 100;

    let completions = runtime
        .drive_until_idle(&mut t, &crate::telemetry::ConfiguredTelemetry::new(), None)
        .expect("drive interp");
    let halt = completions
        .iter()
        .rev()
        .find_map(|(pid, value)| (*pid == 1).then_some(value.as_i64().expect("int halt")))
        .expect("main completion");

    let task = runtime.task(1).expect("main task remains registered");
    assert_eq!(halt, 250);
    assert!(task.reduction_yields > 0);
    assert_eq!(
        task.quiet_quanta, task.reduction_yields as u8,
        "quiet_quanta should move once per scheduler yield, not once per interpreted back edge"
    );
    assert_eq!(task.interpreter_yields, 0);
}

#[test]
fn interp_allocation_pressure_yields_before_budget_exhaustion() {
    let m = lower_src(
        r#"
        fn sum(0, acc, _), do: acc
        fn sum(n, acc, _), do: sum(n - 1, acc + n, [n])
        fn main(), do: sum(10, 0, nil)
    "#,
    );
    let main = m.fn_by_name("main").expect("main").id;
    let mut t = crate::types::new();
    let mut runtime = IrInterpRuntime::fresh_with_root(&m);
    runtime.enqueue_entry(&m, 1, main, vec![]).expect("enqueue main");
    {
        let task = runtime.task_mut(1).expect("main task");
        task.reductions_per_quantum = 1000;
        task.heap.allocation_watermark = null_mut();
    }

    let completions = runtime
        .drive_until_idle(&mut t, &crate::telemetry::ConfiguredTelemetry::new(), None)
        .expect("drive interp");
    let halt = completions
        .iter()
        .rev()
        .find_map(|(pid, value)| (*pid == 1).then_some(value.as_i64().expect("int halt")))
        .expect("main completion");

    let task = runtime.task(1).expect("main task remains registered");
    assert_eq!(halt, 55);
    assert!(
        task.heap.gc_run_count > 0,
        "allocation pressure should force scheduler-boundary GC"
    );
    assert_eq!(
        task.reduction_yields, 0,
        "allocation pressure should not be counted as ordinary reduction exhaustion"
    );
    assert!(
        task.allocation_pressure_yields > 0,
        "allocation pressure should have its own cause-specific counter"
    );
    // fz-mif: an allocation-pressure yield banks only the reductions genuinely
    // burned before the budget was force-zeroed — never a phantom full quantum.
    // This tiny program trips pressure once, early in the quantum, so the
    // banked count is positive but strictly below a quantum. The pre-fz-mif
    // over-count credited a whole quantum per pressure yield; these two bounds
    // pin the honest accounting against regression in either direction.
    assert!(
        task.reductions_executed > 0,
        "allocation pressure should still bank the reductions genuinely burned"
    );
    assert!(
        task.reductions_executed < task.reductions_per_quantum as u64,
        "allocation pressure must not credit a phantom full quantum"
    );
}

#[test]
fn interp_typed_int_send_receive_boundary() {
    assert_eq!(
        run(r#"
            fn main() do
              send(self(), 4611686018427387904)
              receive do
                x -> x
              end
            end
            "#,),
        4611686018427387904
    );
}

#[test]
fn interp_typed_int_list_head_boundary() {
    assert_eq!(
        run(r#"
            fn first([h | _]), do: h
            fn main(), do: first([4611686018427387904])
        "#),
        4611686018427387904
    );
}

#[test]
fn interp_typed_int_map_get_boundary() {
    assert_eq!(
        run("fn main(), do: %{answer: 4611686018427387904}.answer"),
        4611686018427387904
    );
}

#[test]
fn interp_ref_bifs_read_scalars_from_list_map_and_tuple() {
    assert_eq!(
        capture(
            r#"
            fn tuple_second({_, x}), do: x
            fn list_head([h | _]), do: h
            fn main() do
              dbg({list_head([7]), %{answer: 42}.answer, tuple_second({:ok, 1.5})})
            end
        "#
        ),
        "{7, 42, 1.5}"
    );
}

#[test]
fn interp_ref_bifs_read_heap_values_from_list_map_and_tuple() {
    assert_eq!(
        capture(
            r#"
            fn tuple_second({_, x}), do: x
            fn list_head([h | _]), do: h
            fn main() do
              dbg({list_head([[1]]), %{child: [2]}.child, tuple_second({:ok, [3]})})
            end
        "#
        ),
        "{[1], [2], [3]}"
    );
}

#[test]
fn interp_typed_int_dispatch_and_return_flow() {
    assert_eq!(
        run(r#"
            fn bump(x :: integer), do: x + 7
            fn bump(_), do: 0
            fn main(), do: bump(4611686018427387904)
        "#),
        4611686018427387911
    );
}

#[test]
fn interp_typed_int_sender_wakes_blocked_receiver() {
    assert_eq!(
        run(r#"
            fn child(parent) do
              send(parent, 4611686018427387904)
            end
            fn main() do
              me = self()
              spawn(fn () -> child(me) end)
              receive do
                x -> x
              end
            end
        "#),
        4611686018427387904
    );
}
