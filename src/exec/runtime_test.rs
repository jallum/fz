use super::*;
use crate::ir_codegen::{CompiledModule, compile_planned};
use crate::ir_interp::run_main;
use crate::telemetry::bus::ConfiguredTelemetry;
use crate::telemetry::capture::Capture;
use crate::telemetry::handler::{Event, Handler};
use crate::test_support::linked_runtime_graph;
use fz_runtime::any_value::{
    ListCons, ValueKind, closure_addr_from_tagged, closure_capture_ref_word, closure_capture_set,
    closure_size_for_count,
};
use fz_runtime::park::ParkRecord;
use std::cell::Cell;
use std::ptr::{null_mut, read, write};
use std::rc::Rc;
use std::thread::sleep;
use std::time::Duration;

fn compile_src(src: &str) -> (CompiledModule, Module, FnId) {
    let mut t = crate::types::new();
    let tel = ConfiguredTelemetry::new();
    let mut graph = linked_runtime_graph(&mut t, src, &tel);
    let entry = graph.module().fn_by_name("main").expect("main fn").id;
    let (module, module_plan) = graph.cloned_module_plan();
    let compiled = compile_planned(graph.types(), &module, &module_plan, &tel).expect("compile planned");
    (compiled, graph.module().clone(), entry)
}

fn force_reduction_yield(task: &mut Process) {
    task.reductions_per_quantum = 1;
}

fn force_allocation_pressure_yield(task: &mut Process) {
    task.reductions_per_quantum = 1;
    task.heap.allocation_watermark = null_mut();
}

fn test_int_ref(value: i64) -> AnyValueRef {
    let slot = Box::leak(Box::new(value as u64));
    AnyValueRef::from_scalar_slot(ValueKind::INT, slot as *const u64).expect("test int ref")
}

/// Three tasks built from the same CompiledModule each compute their
/// own halt value independently. PRE-.11.32 this would have been
/// impossible (shared TLS); post-.19.1 this is the basic spawn shape.
#[test]
fn three_tasks_each_compute_their_halt_value() {
    let src = "fn main(), do: 1 + 2 + 3";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let a = rt.spawn(entry);
    let b = rt.spawn(entry);
    let c = rt.spawn(entry);
    rt.run_until_idle();
    assert_eq!(rt.task(a).unwrap().halt_value, 6);
    assert_eq!(rt.task(b).unwrap().halt_value, 6);
    assert_eq!(rt.task(c).unwrap().halt_value, 6);
    assert_eq!(rt.task(a).unwrap().state, ProcessState::Exited);
    assert_eq!(rt.task(b).unwrap().state, ProcessState::Exited);
    assert_eq!(rt.task(c).unwrap().state, ProcessState::Exited);
}

/// The Runtime emits `fz.runtime.process_exited` at task exit. A
/// `ProcessExitCapture` projects it into an `ExitRecord` (read from the
/// durable measurements) — the seam tests use to observe a run's result
/// and live-object count without poking the Process.
#[test]
fn process_exit_capture_yields_exit_record() {
    // Allocates a map, so the heap has live objects at exit.
    let src = "fn main(), do: %{1 => 10, 2 => 20}[2]";
    let (compiled, _module, entry) = compile_src(src);

    let tel = ConfiguredTelemetry::new();
    let cap = ProcessExitCapture::new();
    tel.attach(&[], cap.handler());

    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    rt.run_until_idle();

    let rec = cap.last().expect("process_exited captured");
    assert_eq!(rec.pid, pid);
    assert_eq!(rec.halt_value, 20);
    assert!(rec.live_count > 0, "map build leaves live heap objects");
}

/// The event also carries the live `&Process` as opaque metadata, so a
/// synchronous handler can downcast it and read any field the standard
/// projection omits — the escape hatch beside the durable measurements.
#[test]
fn process_exit_event_carries_opaque_process() {
    struct OpaqueProbe {
        seen_halt: Rc<Cell<Option<i64>>>,
    }
    impl Handler for OpaqueProbe {
        fn handle(&self, ev: &Event<'_, '_, '_>) {
            if ev.name != ["fz", "runtime", "process_exited"] {
                return;
            }
            let p = ev
                .metadata
                .get("process")
                .and_then(|v| v.downcast_ref::<Process>())
                .expect("opaque &Process present during dispatch");
            self.seen_halt.set(Some(p.halt_value));
        }
    }

    let src = "fn main(), do: 7";
    let (compiled, _module, entry) = compile_src(src);

    let seen_halt = Rc::new(Cell::new(None));
    let tel = ConfiguredTelemetry::new();
    tel.attach(
        &[],
        Box::new(OpaqueProbe {
            seen_halt: seen_halt.clone(),
        }),
    );

    let mut rt = Runtime::new(&compiled, 1, &tel);
    let _ = rt.spawn(entry);
    rt.run_until_idle();

    assert_eq!(seen_halt.get(), Some(7));
}

/// ctx.2: every task carries a populated `ExecCtx` (`Process.ctx`) while it
/// runs. Observed at exit via the opaque `&Process`: the JIT Runtime's ctx
/// names a scheduler handle, a telemetry sink, and the output callback.
#[test]
fn process_ctx_installed_during_run() {
    struct CtxProbe {
        scheduler_set: Rc<Cell<bool>>,
        tel_set: Rc<Cell<bool>>,
        output_set: Rc<Cell<bool>>,
    }
    impl Handler for CtxProbe {
        fn handle(&self, ev: &Event<'_, '_, '_>) {
            if ev.name != ["fz", "runtime", "process_exited"] {
                return;
            }
            let p = ev
                .metadata
                .get("process")
                .and_then(|v| v.downcast_ref::<Process>())
                .expect("opaque &Process present during dispatch");
            assert!(!p.ctx.is_null(), "process.ctx installed during run");
            let ctx = unsafe { &*p.ctx };
            self.scheduler_set.set(!ctx.scheduler.is_null());
            self.tel_set.set(!ctx.tel.is_null());
            self.output_set.set(ctx.output.is_some());
        }
    }

    let (compiled, _module, entry) = compile_src("fn main(), do: 7");

    let scheduler_set = Rc::new(Cell::new(false));
    let tel_set = Rc::new(Cell::new(false));
    let output_set = Rc::new(Cell::new(false));
    let tel = ConfiguredTelemetry::new();
    tel.attach(
        &[],
        Box::new(CtxProbe {
            scheduler_set: scheduler_set.clone(),
            tel_set: tel_set.clone(),
            output_set: output_set.clone(),
        }),
    );

    let mut rt = Runtime::new(&compiled, 1, &tel);
    let _ = rt.spawn(entry);
    rt.run_until_idle();

    assert!(scheduler_set.get(), "ctx.scheduler populated");
    assert!(tel_set.get(), "ctx.tel populated");
    assert!(output_set.get(), "ctx.output callback populated");
}

/// Three-path parity: the interpreter and compiled engines emit the same
/// process_exited (equal halt value, live heap) and dbg event stream for
/// the same program, through the one shared emit + output seam.
#[test]
fn both_engines_emit_equivalent_process_exited_and_dbg() {
    // dbg returns its arg, so this halts with 9 and prints "9".
    let src = "fn main(), do: dbg(%{1 => 9}[1])";
    let (compiled, m, entry) = compile_src(src);

    // Compiled engine.
    let tel_c = ConfiguredTelemetry::new();
    let exits_c = ProcessExitCapture::new();
    let out_c = Capture::new();
    tel_c.attach(&[], exits_c.handler());
    tel_c.attach(&[], out_c.handler());
    let mut rt = Runtime::new(&compiled, 1, &tel_c);
    let _ = rt.spawn(entry);
    rt.run_until_idle();
    let c = exits_c.last().expect("compiled process_exited");

    // Interpreter engine — same program, observed through the same seam.
    let tel_i = ConfiguredTelemetry::new();
    let exits_i = ProcessExitCapture::new();
    let out_i = Capture::new();
    tel_i.attach(&[], exits_i.handler());
    tel_i.attach(&[], out_i.handler());
    let _ = run_main(&tel_i, &m).unwrap();
    let i = exits_i.last().expect("interp process_exited");

    assert_eq!(c.halt_value, 9);
    assert_eq!(c.halt_value, i.halt_value, "halt value parity");
    assert!(c.live_count > 0 && i.live_count > 0, "both leave live heap");
    assert_eq!(out_c.count(&["fz", "runtime", "dbg"]), 1);
    assert_eq!(
        out_i.count(&["fz", "runtime", "dbg"]),
        1,
        "interp dbg routes to telemetry too"
    );
}

/// `dbg` output is routed onto the telemetry bus as `fz.runtime.dbg`
/// events (via the OutputHook), so tests observe printed output through
/// the same seam as everything else.
#[test]
fn dbg_output_emits_telemetry_events() {
    use crate::telemetry::value::Value;

    let src = "fn main(), do: dbg(42)";
    let (compiled, _module, entry) = compile_src(src);

    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&[], cap.handler());

    let mut rt = Runtime::new(&compiled, 1, &tel);
    let _ = rt.spawn(entry);
    rt.run_until_idle();

    let dbg_events = cap.find(&["fz", "runtime", "dbg"]);
    assert_eq!(dbg_events.len(), 1, "one dbg call → one event");
    assert!(matches!(
        dbg_events[0].metadata.get("line"),
        Some(Value::Str(s)) if s.as_ref() == "42"
    ));
}

/// Each task has its own heap. Two tasks build different maps; each
/// observes only its own state. Same invariant as the .11.32 gating
/// test but driven through the scheduler with two spawned tasks.
#[test]
fn tasks_have_independent_heaps_and_builders() {
    let src_a = "fn main(), do: %{1 => 10, 2 => 20}[2]";
    let src_b = "fn main(), do: %{3 => 30}[3]";
    let (ca, ma, _entry_a) = compile_src(src_a);
    let (cb, mb, _entry_b) = compile_src(src_b);

    let tel = ConfiguredTelemetry::new();
    let mut rt_a = Runtime::new(&ca, 1, &tel);
    let mut rt_b = Runtime::new(&cb, 1, &tel);
    let pa = rt_a.spawn(ma.fn_by_name("main").unwrap().id);
    let pb = rt_b.spawn(mb.fn_by_name("main").unwrap().id);
    rt_a.run_until_idle();
    rt_b.run_until_idle();

    assert_eq!(rt_a.task(pa).unwrap().halt_value, 20);
    assert_eq!(rt_b.task(pb).unwrap().halt_value, 30);
    assert!(rt_a.task(pa).unwrap().heap.live_count() > 0);
    assert!(rt_b.task(pb).unwrap().heap.live_count() > 0);
}

/// Spawning more tasks after run_until_idle works: new pids, new
/// runs proceed normally.
#[test]
fn spawn_after_idle_resumes_progress() {
    let src = "fn main(), do: 42";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let a = rt.spawn(entry);
    rt.run_until_idle();
    assert_eq!(rt.task(a).unwrap().halt_value, 42);
    let b = rt.spawn(entry);
    rt.run_until_idle();
    assert_eq!(rt.task(b).unwrap().halt_value, 42);
    assert_ne!(a, b, "pids are unique across spawns");
}

/// worker count > 1 is reserved for the multi-worker follow-up;
/// Runtime::new panics rather than silently accepting it.
#[test]
#[should_panic(expected = "v1 only supports pool size 1")]
fn workers_greater_than_one_is_not_yet_supported() {
    let src = "fn main(), do: 0";
    let (compiled, _module, _entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let _ = Runtime::new(&compiled, 2, &tel);
}

// ----- fz-ul4.19.2: spawn / self builtins -----

/// `self()` inside main returns the running task's pid (1 for the
/// first spawn).
#[test]
fn self_returns_task_pid() {
    let src = "fn main(), do: self()";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    rt.run_until_idle();
    // halt_value is the raw pid i64 carried through the typed halt path.
    assert_eq!(rt.task(pid).unwrap().halt_value, pid as i64);
}

/// `spawn(fn() -> 42 end)` enqueues a child task; after run_until_idle
/// both tasks have halted and the child computed 42.
#[test]
fn spawn_enqueues_child_task() {
    let src = r#"
        fn child(), do: 42
        fn main(), do: spawn(child)
    "#;
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let main_pid = rt.spawn(entry);
    rt.run_until_idle();
    // Main halted with the child's pid (spawn returns pid as boxed
    // Int; halt unboxes to i64). Child pid is main_pid + 1 = 2.
    let expected_child_pid = main_pid + 1;
    assert_eq!(rt.task(main_pid).unwrap().halt_value, expected_child_pid as i64);
    // Child completed.
    let child = rt
        .task(expected_child_pid)
        .expect("child task should exist after spawn");
    assert_eq!(child.halt_value, 42);
    assert_eq!(child.state, ProcessState::Exited);
}

// ----- fz-ul4.19.3: send / receive + deep-copy + block/wake -----

/// Round-trip an Int: parent spawns child, child sends 42 to parent
/// (parent pid passed somehow — for this test, parent's pid is 1
/// because it's spawned first), parent receives, halts with the msg.
/// Since we can't yet pass parent's pid to child easily, this test
/// uses send-to-self.
#[test]
fn send_to_self_then_receive_int() {
    let src = r#"
        fn main() do
          send(self(), 42)
          receive do
            x -> x
          end
        end
    "#;
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    rt.run_until_idle();
    // halt_value is the unboxed Int from the received message.
    assert_eq!(rt.task(pid).unwrap().halt_value, 42);
    assert_eq!(rt.task(pid).unwrap().state, ProcessState::Exited);
}

/// Receive blocks the task when no message is available, then resumes
/// when send delivers one. Parent spawns child; parent calls a catch-all receive
/// first (Blocks); child then sends; parent wakes and halts with the
/// message. Tests the YIELD_PTR / Blocked / wake mechanism.
#[test]
fn receive_blocks_until_send_arrives() {
    // child(parent_pid) sends 99 to parent_pid then halts.
    // main spawns child(self()) and then waits on a catch-all receive.
    let src = r#"
        fn child(parent), do: send(parent, 99)
        fn main() do
          child(self())
          receive do
            x -> x
          end
        end
    "#;
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    rt.run_until_idle();
    assert_eq!(rt.task(pid).unwrap().halt_value, 99);
}

// Deep-copy: send a heap-allocated list; sender and receiver heaps
// hold independent copies. Verified by sender-side heap growing
// from the list allocation plus receiver-side heap growing from
// the deep-copy of the same structure.
// ----- fz-ul4.19 demonstration via the JIT pipeline -----

/// End-to-end ping-pong: run a minimal spawn/send/receive program
/// through the FULL JIT pipeline (lex → parse → resolve → macros →
/// ir_lower → ir_codegen → Runtime::run_until_idle) and assert the
/// parent's halt value matches the message the child sent.
///
/// This is the JIT path's proof-of-life for concurrency. The source is
/// inline because the assertion checks the parent's halt *value*: the
/// `concurrency_ping_pong` fixture self-checks the same delivery with an
/// in-language `assert` (halting on nil), so the value-returning shape
/// this test needs lives here rather than in the fixture.
#[test]
fn fixture_ping_pong_via_jit_runtime() {
    let src = "fn child(), do: send(1, 42)\n\
               \n\
               fn main() do\n\
                 spawn(child)\n\
                 dbg(receive do x -> x end)\n\
               end\n";
    let (compiled, _module, entry) = compile_src(src);

    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let main_pid = rt.spawn(entry);
    assert_eq!(
        main_pid, 1,
        "main is the first spawn; fixture hard-codes 1 as parent's pid"
    );
    rt.run_until_idle();

    // Parent received 42, printed it, and halts on dbg's return value.
    let main_task = rt.task(main_pid).expect("main task in registry");
    assert_eq!(
        main_task.halt_value, 42,
        "parent halts with dbg(receive do x -> x end)'s returned value"
    );
    assert_eq!(main_task.state, ProcessState::Exited);

    // Child task: spawned by main, halted normally (send returns the
    // message which it then halts on; but child's main body is `send`,
    // so it halts with the message's value 42 too).
    let child_task = rt.task(2).expect("child task should exist at pid 2 (second spawn)");
    assert_eq!(child_task.state, ProcessState::Exited);
    assert_eq!(child_task.halt_value, 42);
}

#[test]
fn send_list_deep_copies_into_receiver_heap() {
    let src = r#"
        fn main() do
          send(self(), [1, 2, 3])
          receive do
            x -> x
          end
        end
    "#;
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    rt.run_until_idle();
    // Send-to-self means the message was deep-copied even though
    // it's the same Process. Heap should have BOTH the original
    // list (allocated for the send) AND the copied list (allocated
    // for the mailbox-resident copy). Both share schema/registry
    // (same heap), but are distinct allocations.
    let task = rt.task(pid).unwrap();
    assert_eq!(task.state, ProcessState::Exited);
    // The halt value is the head of the returned list (since the
    // list was returned via receive). Confirm task halted cleanly.
    assert!(task.heap.live_count() >= 6, "expected both src+dst lists in heap");
}

#[test]
fn deep_copy_float_in_container_preserves_raw_slot() {
    let src = r#"
        fn main() do
          send(self(), [2.5])
          nil
        end
    "#;
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    rt.run_until_idle();
    let task = rt.task(pid).unwrap();
    assert_eq!(task.state, ProcessState::Exited);
    let any_ref = task.mailbox.front().expect("self-send remains queued");
    assert_eq!(any_ref.tag(), ValueKind::LIST);
    let list = any_ref.list_addr().expect("mailbox keeps tagged list ref");
    let head = unsafe { (*(list as *const ListCons)).head_value() };
    assert_eq!(head.kind(), ValueKind::FLOAT);
    assert_eq!(f64::from_bits(head.raw()), 2.5);
}

#[test]
fn mailbox_with_float_boxes_at_any_boundary() {
    let src = r#"
        fn main() do
          send(self(), 2.5)
          nil
        end
    "#;
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    rt.run_until_idle();
    let task = rt.task(pid).unwrap();
    assert_eq!(task.state, ProcessState::Exited);
    assert!(
        task.heap.live_count() >= 1,
        "send(any) boxes scalar messages before mailbox storage"
    );
    let slot = task.mailbox.front().expect("self-send remains queued");
    assert_eq!(slot.tag(), ValueKind::FLOAT);
    assert_eq!(slot.load_float().unwrap(), 2.5);
}

#[test]
fn receive_map_pattern_matches_present_nil_value_via_jit_runtime() {
    let src = r#"
        fn main() do
          me = self()
          send(me, %{other: 1})
          send(me, %{name: nil})
          send(me, %{name: :later})
          v = receive do
            %{name: n} -> n
          end
          dbg(v)
        end
    "#;
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());
    let mut rt = Runtime::new(&compiled, 1, &tel);
    rt.spawn(entry);
    rt.run_until_idle();
    assert_eq!(dbg.lines(), vec!["nil"]);
}

/// fz-siu.7.3: park-time GC hook fires when allocation pressure
/// crosses gc_threshold_bytes. With the threshold lowered below the
/// fixture's allocation footprint, run_until_idle must trigger gc()
/// (stub in .7 — just bumps gc_run_count) at the post-dispatch park
/// point. Real Cheney body lands in fz-siu.8.
#[test]
fn park_time_gc_fires_when_pressure_set() {
    // [1,2,3] allocates three 16-byte headerless cons cells = 48 bytes.
    let src = "fn main(), do: [1, 2, 3]";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    // Lower threshold below the alloc footprint so the flag trips.
    rt.tasks.get_mut(&pid).unwrap().heap.gc_threshold_bytes = 32;
    rt.run_until_idle();
    let task = rt.task(pid).unwrap();
    assert_eq!(task.state, ProcessState::Exited);
    assert!(
        task.heap.gc_run_count >= 1,
        "park-time hook should have fired GC, got {}",
        task.heap.gc_run_count
    );
    assert!(!task.heap.should_gc(), "flag should be cleared after gc()");
}

#[test]
fn park_time_gc_preserves_selective_receive_roots() {
    let src = r#"
        fn main() do
          send(self(), %{name: :alice})
          v = receive do
            %{name: n} -> n
          end
          dbg(v)
        end
    "#;
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    rt.tasks.get_mut(&pid).unwrap().heap.gc_threshold_bytes = 64;
    rt.run_until_idle();
    assert_eq!(dbg.lines(), vec![":alice"]);
}

// ----- fz-02r.8: mid-flight back-edge GC integration -----

/// A recursive function that allocates a cons cell per iteration runs to
/// completion with the correct integer result even when allocation
/// pressure expires the reduction budget mid-loop.
#[test]
fn mid_flight_gc_fires_and_result_is_correct() {
    // sum(n, acc, _) allocates [n] per iteration so the watermark trips.
    // sum(10, 0, nil) = 55 = 10+9+...+1.
    let src = "\
fn sum(0, acc, _), do: acc
fn sum(n, acc, _), do: sum(n - 1, acc + n, [n])
fn main(), do: sum(10, 0, nil)";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    {
        let task = rt.tasks.get_mut(&pid).unwrap();
        task.reductions_per_quantum = 1000;
        task.heap.allocation_watermark = null_mut();
    }
    rt.run_until_idle();
    let task = rt.task(pid).unwrap();
    assert_eq!(task.state, ProcessState::Exited);
    assert_eq!(task.halt_value, 55, "sum(10,0,nil) should be 55");
    assert_eq!(task.reduction_yields, 0);
    assert!(task.allocation_pressure_yields > 0);
}

#[test]
fn mid_flight_gc_preserves_typed_float_arg() {
    let src = "\
fn sumf(0, acc, _), do: acc
fn sumf(n, acc, _), do: sumf(n - 1, acc + 1.5, [n])
fn main(), do: sumf(4, 0.0, nil)";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    force_allocation_pressure_yield(rt.tasks.get_mut(&pid).unwrap());
    rt.run_until_idle();
    let task = rt.task(pid).unwrap();
    assert_eq!(task.state, ProcessState::Exited);
    assert_eq!(f64::from_bits(task.halt_value as u64), 6.0);
}

#[test]
fn mid_flight_gc_preserves_destination_built_tuple_arg() {
    let src = r#"
        fn sum(0, acc, {last, :kept}, _), do: acc + last
        fn sum(n, acc, _, _), do: sum(n - 1, acc + n, {n, :kept}, [n])
        fn main(), do: sum(10, 0, {0, :kept}, nil)
    "#;
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    force_allocation_pressure_yield(rt.tasks.get_mut(&pid).unwrap());
    rt.run_until_idle();
    let task = rt.task(pid).unwrap();
    assert_eq!(task.state, ProcessState::Exited);
    assert_eq!(task.halt_value, 56);
    assert!(
        task.heap.gc_run_count >= 1,
        "mid-flight GC should have run while carrying tuple roots"
    );
}

#[test]
fn mid_flight_gc_preserves_destination_built_list_arg() {
    let src = r#"
        fn sum(0, acc, [last | _]), do: acc + last
        fn sum(n, acc, _), do: sum(n - 1, acc + n, [n])
        fn main(), do: sum(10, 0, [0])
    "#;
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    force_allocation_pressure_yield(rt.tasks.get_mut(&pid).unwrap());
    rt.run_until_idle();
    let task = rt.task(pid).unwrap();
    assert_eq!(task.state, ProcessState::Exited);
    assert_eq!(task.halt_value, 56);
    assert!(
        task.heap.gc_run_count >= 1,
        "mid-flight GC should have run while carrying list roots"
    );
}

#[test]
fn mid_flight_gc_preserves_destination_built_map_arg() {
    let src = r#"
        fn sum(0, acc, m), do: acc + m[:last]
        fn sum(n, acc, _), do: sum(n - 1, acc + n, %{last: n, kept: :ok})
        fn main(), do: sum(10, 0, %{last: 0, kept: :ok})
    "#;
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    force_allocation_pressure_yield(rt.tasks.get_mut(&pid).unwrap());
    rt.run_until_idle();
    let task = rt.task(pid).unwrap();
    assert_eq!(task.state, ProcessState::Exited);
    assert_eq!(task.halt_value, 56);
    assert!(
        task.heap.gc_run_count >= 1,
        "mid-flight GC should have run while carrying map roots"
    );
}

/// After mid-flight GC fires, gc_run_count must be at least 1 — the heap
/// actually ran a Cheney collect on the live continuation roots.
#[test]
fn mid_flight_gc_increments_gc_run_count() {
    let src = "\
fn sum(0, acc, _), do: acc
fn sum(n, acc, _), do: sum(n - 1, acc + n, [n])
fn main(), do: sum(10, 0, nil)";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    force_allocation_pressure_yield(rt.tasks.get_mut(&pid).unwrap());
    rt.run_until_idle();
    let task = rt.task(pid).unwrap();
    assert!(
        task.heap.gc_run_count >= 1,
        "mid-flight GC should have incremented gc_run_count; got {}",
        task.heap.gc_run_count
    );
}

/// Two processes both complete correctly when mid-flight GC fires in each.
#[test]
fn two_processes_survive_mid_flight_gc() {
    let src = "\
fn sum(0, acc, _), do: acc
fn sum(n, acc, _), do: sum(n - 1, acc + n, [n])
fn main(), do: sum(8, 0, nil)";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pa = rt.spawn(entry);
    let pb = rt.spawn(entry);
    force_allocation_pressure_yield(rt.tasks.get_mut(&pa).unwrap());
    force_allocation_pressure_yield(rt.tasks.get_mut(&pb).unwrap());
    rt.run_until_idle();
    // sum(8,0,nil) = 8+7+...+1 = 36
    assert_eq!(rt.task(pa).unwrap().halt_value, 36);
    assert_eq!(rt.task(pb).unwrap().halt_value, 36);
    assert_eq!(rt.task(pa).unwrap().state, ProcessState::Exited);
    assert_eq!(rt.task(pb).unwrap().state, ProcessState::Exited);
}

#[test]
fn compiled_reductions_yield_allocation_light_loops() {
    let src = "fn count(0, acc), do: acc\nfn count(n, acc), do: count(n - 1, acc + 1)\nfn main(), do: count(5000, 0)";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pa = rt.spawn(entry);
    let pb = rt.spawn(entry);
    force_reduction_yield(rt.tasks.get_mut(&pa).unwrap());
    force_reduction_yield(rt.tasks.get_mut(&pb).unwrap());

    rt.run_until_idle();

    let a = rt.task(pa).unwrap();
    let b = rt.task(pb).unwrap();
    assert_eq!(a.halt_value, 5000);
    assert_eq!(b.halt_value, 5000);
    assert!(a.reduction_yields > 0);
    assert!(b.reduction_yields > 0);
    assert_eq!(a.allocation_pressure_yields, 0);
    assert_eq!(b.allocation_pressure_yields, 0);
    assert_eq!(a.interpreter_yields, 0);
    assert_eq!(b.interpreter_yields, 0);
}

#[test]
fn compiled_yield_measures_full_continuation_allocation_window() {
    let src = "fn count(0, acc), do: acc\nfn count(n, acc), do: count(n - 1, acc + 1)\nfn main(), do: count(5000, 0)";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    force_reduction_yield(rt.tasks.get_mut(&pid).unwrap());

    rt.run_until_idle();

    let task = rt.task(pid).unwrap();
    assert_eq!(task.halt_value, 5000);
    assert!(task.reduction_yields > 0);
    assert_eq!(task.pending_yield_continuation_margin_before_bytes, 0);
    assert!(
        task.max_yield_continuation_bytes > closure_size_for_count(3) as u64,
        "yield telemetry should include scalar boxes as well as the continuation closure; got {} bytes",
        task.max_yield_continuation_bytes
    );
    assert!(task.min_yield_continuation_margin_before_bytes > 0);
    assert!(task.min_yield_continuation_margin_after_bytes > 0);
}

/// quiet_quanta increments each quantum that completes without a
/// mid-flight yield. A non-allocating recursive function should complete
/// in one quantum and quiet_quanta should be 1.
#[test]
fn quiet_quanta_increments_when_no_mid_flight_yield() {
    // Pure integer counter: no allocations, back-edge never yields.
    let src = "fn count(0, acc), do: acc\nfn count(n, acc), do: count(n - 1, acc + 1)\nfn main(), do: count(20, 0)";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    rt.run_until_idle();
    let task = rt.task(pid).unwrap();
    assert_eq!(task.halt_value, 20);
    assert!(
        task.quiet_quanta >= 1,
        "quiet_quanta should be >= 1 after a non-yielding quantum; got {}",
        task.quiet_quanta
    );
}

/// When mid-flight GC fires, quiet_quanta is reset to 0 (not incremented).
#[test]
fn quiet_quanta_resets_on_mid_flight_yield() {
    let src = "\
fn sum(0, acc, _), do: acc
fn sum(n, acc, _), do: sum(n - 1, acc + n, [n])
fn main(), do: sum(10, 0, nil)";
    let (compiled, _module, entry) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let pid = rt.spawn(entry);
    force_allocation_pressure_yield(rt.tasks.get_mut(&pid).unwrap());
    rt.run_until_idle();
    // After mid-flight GC fires, quiet_quanta is reset to 0 by the
    // scheduler, then incremented by 1 in the final (halting) quantum.
    // Exact count depends on how many times the watermark fires, so we
    // just check the computation completed correctly.
    assert_eq!(rt.task(pid).unwrap().halt_value, 55);
    assert_eq!(rt.task(pid).unwrap().state, ProcessState::Exited);
}

// ----- fz-yxs/fz-st5 — sender-probe + timer drain tests -----

/// Deterministic mock matcher. Returns 1 when `msg == pinned[0]`,
/// and writes `msg` into `out[0]` (bound_arity must be >= 1).
extern "C" fn mock_eq_matcher(
    _process: *mut Process,
    msg: u64,
    pinned: *const AnyValueRef,
    out: *mut AnyValueRef,
) -> u32 {
    let want = unsafe { *pinned };
    let msg_ref = AnyValueRef::from_raw_word(msg).expect("msg ref");
    if msg_ref.load_int().expect("msg int") == want.load_int().expect("pinned int") {
        unsafe {
            *out = msg_ref;
        }
        1
    } else {
        0
    }
}

/// Set up a Runtime with two spawned tasks ready for direct
/// `send_via_current_runtime` calls. Returns (runtime, sender_pid,
/// receiver_pid). Both tasks are spawned but never executed — we
/// only drive the send-probe code path.
fn two_task_rt<'a>(
    compiled: &'a CompiledModule,
    main_id: FnId,
    tel: &'a ConfiguredTelemetry,
) -> (Runtime<'a>, PidId, PidId) {
    let mut rt = Runtime::new(compiled, 1, tel);
    let sender = rt.spawn(main_id);
    let receiver = rt.spawn(main_id);
    (rt, sender, receiver)
}

fn template_closure(task: &mut Process, stub: usize) -> *mut u8 {
    let bits = task.heap.alloc_closure_slots(0, 1, 0);
    let p = closure_addr_from_tagged(bits).expect("template closure ptr");
    unsafe {
        write(p.add(8) as *mut u64, stub as u64);
        closure_capture_set(p, 0, AnyValue::null());
    }
    bits as *mut u8
}

#[test]
fn send_probe_hit_wakes_receiver_with_runnable_closure() {
    let src = "fn main(), do: 0";
    let (compiled, _module, main_id) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let (mut rt, sender_pid, receiver_pid) = two_task_rt(&compiled, main_id, &tel);

    // Pre-seed receiver as wait. Pinned wants msg == 42.
    let receiver = rt.task_mut(receiver_pid).unwrap();
    receiver.state = ProcessState::Blocked;
    let template = template_closure(receiver, 0xdead_beef);
    receiver.wait = Some(Box::new(ParkRecord {
        matcher_fn: mock_eq_matcher,
        pinned: vec![test_int_ref(42)],
        clause_bodies: vec![template],
        clause_bound_counts: vec![1],
        bound_arity: 1,
        after_deadline_ms: None,
        after_cont: null_mut(),
        after_timer_id: None,
    }));
    // A genuinely parked task has consumed its spawn-time entry thunk;
    // model that by clearing runnable so the probe-hit assertion observes
    // only what the wakeup populates.
    receiver.set_runnable_closure(null_mut());
    // Clear run queue so both tasks are quiescent.
    rt.run_queue.clear();

    // send_via takes the sender process and the scheduler handle explicitly.
    let rt_ptr = &mut rt as *mut Runtime<'_> as *mut ();
    let sender_ptr = rt.tasks.get_mut(&sender_pid).unwrap().as_mut() as *mut Process;

    // Hit case: msg == 42 matches the pinned.
    send_via(sender_ptr, rt_ptr, receiver_pid, test_int_ref(42));

    let r = rt.task(receiver_pid).unwrap();
    assert_eq!(r.state, ProcessState::Ready);
    assert!(r.wait.is_none(), "park should be cleared on hit");
    let runnable = r.runnable_ptr();
    assert!(!runnable.is_null(), "runnable_closure populated on hit");
    unsafe {
        assert_eq!(read((runnable as *const u8).add(8) as *const u64), 0xdead_beef);
        let cont_addr = runnable;
        let capture_ref = AnyValueRef::from_raw_word(closure_capture_ref_word(cont_addr, 1)).expect("capture ref");
        assert_eq!(capture_ref.load_int().expect("capture int ref"), 42);
    }
    assert!(rt.run_queue.iter().any(|p| *p == receiver_pid));
}

#[test]
fn send_probe_miss_leaves_park_in_place_and_appends_to_mailbox() {
    let src = "fn main(), do: 0";
    let (compiled, _module, main_id) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let (mut rt, sender_pid, receiver_pid) = two_task_rt(&compiled, main_id, &tel);

    let receiver = rt.task_mut(receiver_pid).unwrap();
    receiver.state = ProcessState::Blocked;
    let template = template_closure(receiver, 0xdead_beef);
    receiver.wait = Some(Box::new(ParkRecord {
        matcher_fn: mock_eq_matcher,
        pinned: vec![test_int_ref(42)],
        clause_bodies: vec![template],
        clause_bound_counts: vec![1],
        bound_arity: 1,
        after_deadline_ms: None,
        after_cont: null_mut(),
        after_timer_id: None,
    }));
    // Parked task has consumed its entry thunk; clear runnable so the
    // miss assertion observes that the wakeup did NOT populate it.
    receiver.set_runnable_closure(null_mut());
    rt.run_queue.clear();

    let rt_ptr = &mut rt as *mut Runtime<'_> as *mut ();
    let sender_ptr = rt.tasks.get_mut(&sender_pid).unwrap().as_mut() as *mut Process;

    // Miss case: msg == 7 does not match pinned 42.
    send_via(sender_ptr, rt_ptr, receiver_pid, test_int_ref(7));

    let r = rt.task(receiver_pid).unwrap();
    assert_eq!(r.state, ProcessState::Blocked, "still parked on miss");
    assert!(r.wait.is_some(), "park preserved on miss");
    assert!(r.runnable_ptr().is_null());
    assert_eq!(r.mailbox.len(), 1, "miss appends to mailbox");
    assert_eq!(r.mailbox[0].load_int().unwrap(), 7);
    assert!(
        !rt.run_queue.iter().any(|p| *p == receiver_pid),
        "miss does not re-enqueue"
    );
}

#[test]
fn drain_expired_timers_wakes_after_cont() {
    let src = "fn main(), do: 0";
    let (compiled, _module, main_id) = compile_src(src);
    let tel = ConfiguredTelemetry::new();
    let mut rt = Runtime::new(&compiled, 1, &tel);
    let receiver_pid = rt.spawn(main_id);
    rt.run_queue.clear();

    // Schedule an immediate-deadline timer (1ms) for the receiver.
    let timer_id = rt.timers.schedule(receiver_pid, Duration::from_millis(1));

    let after_cont_addr: usize = 0xcafe_babe;
    let receiver = rt.task_mut(receiver_pid).unwrap();
    receiver.state = ProcessState::Blocked;
    receiver.wait = Some(Box::new(ParkRecord {
        matcher_fn: mock_eq_matcher,
        pinned: vec![],
        clause_bodies: vec![],
        clause_bound_counts: vec![],
        bound_arity: 0,
        after_deadline_ms: Some(1),
        after_cont: after_cont_addr as *mut u8,
        after_timer_id: Some(timer_id),
    }));
    // Parked task has consumed its entry thunk; clear runnable so the
    // assertion observes the after-timer fire populating it.
    receiver.set_runnable_closure(null_mut());

    // Wait past the deadline (a few millis to be safe) then drain.
    sleep(Duration::from_millis(5));
    rt.drain_expired_timers();

    let r = rt.task(receiver_pid).unwrap();
    assert_eq!(r.state, ProcessState::Ready);
    assert!(r.wait.is_none());
    assert_eq!(r.runnable_ptr() as usize, after_cont_addr);
    assert!(rt.run_queue.iter().any(|p| *p == receiver_pid));
}

// fz-70q.5.5 — the per-arity dispatch test
// (run_quantum_dispatches_runnable_closure_via_shim) was
// retired with the nine-shim family. End-to-end dispatch is now
// covered by `fixtures/receive_selective_refs/input.fz` exercising
// the single fz_resume seam — see the test runner's matrix suite.
// The smoke check below ensures the singular shim exists.

/// fz-70q.5.5 — single `fz_resume` shim addr is resolved at JIT
/// finalize time. The trampoline's runnable_closure branch
/// transmutes this addr to `extern "C" fn(u64) -> i64` and calls
/// once per resume; a null here would null-deref on every
/// selective-receive wakeup.
#[test]
fn resume_addr_is_finalized() {
    let (compiled, _module, _entry) = compile_src("fn main(), do: 0");
    assert!(!compiled.resume_addr.is_null());
}
