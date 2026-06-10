// ----- fz-yxs/fz-2v3 — selective receive interp tests -----

use crate::exec::runtime::DbgCapture;
use crate::fz_ir::Module;
use crate::ir_interp::{AnyValue, IrInterpRuntime, run_main};
use crate::ir_lower::lower_program;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::bus::ConfiguredTelemetry;
use std::fs::read_to_string;

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

fn run_and_capture(src: &str) -> Result<String, String> {
    let m = lower_src(src);
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());
    run_main(&tel, &m)?;
    Ok(dbg.lines().join("\n"))
}

fn drive_completion_i64(done: &[(u32, AnyValue)], pid: u32) -> Option<i64> {
    done.iter()
        .rev()
        .find_map(|(done_pid, value)| (*done_pid == pid).then(|| value.as_i64()).flatten())
}

/// Initial-scan hit: the message is already in the mailbox at the
/// point the receive runs (self-send then receive).
// PICKED: pinned-ref receive matches pre-queued tagged message correctly
#[test]
fn initial_scan_pinned_match() {
    let src = r#"
        fn main() do
          ref = make_ref()
          send(self(), {:reply, ref, 7})
          v = receive do
            {:reply, ^ref, val} -> val
          end
          dbg(v)
        end
    "#;
    let out = run_and_capture(src).expect("interp run");
    assert!(out.contains("7"), "expected 7, got: {}", out);
}

/// Sender-side probe hit: receiver parks, then a sender delivers a
/// matching message; the sender-side probe wakes the receiver with
/// the matched body.
// PICKED: spawn delivers tagged message that unblocks selective receive
#[test]
fn sender_side_probe_match() {
    let src = r#"
        fn child(parent) do
          send(parent, {:reply, :tag, 99})
        end
        fn main() do
          me = self()
          spawn(fn () -> child(me) end)
          v = receive do
            {:reply, :tag, val} -> val
          end
          dbg(v)
        end
    "#;
    let out = run_and_capture(src).expect("interp run");
    assert!(out.contains("99"), "expected 99, got: {}", out);
}

// DROP: old-world IrInterpRuntime multi-drive API, no compiler2 analogue
#[test]
fn persistent_plain_receive_resumes_after_later_drive_send() {
    let m = lower_src(
        r#"
        fn wait_plain() do
          receive do
            x -> x
          end
        end

        fn send_plain(pid) do
          send(pid, 77)
        end
    "#,
    );
    let wait = m.fn_by_name("wait_plain").expect("wait_plain").id;
    let send = m.fn_by_name("send_plain").expect("send_plain").id;
    let mut t = crate::types::new();
    let mut runtime = IrInterpRuntime::fresh_with_root(&m);
    let tel = ConfiguredTelemetry::new();

    runtime.enqueue_entry(&m, &tel, 1, wait, vec![]).expect("enqueue wait");
    let first = runtime
        .drive_until_idle(&mut t, &tel, Some(1))
        .expect("drive blocked wait");
    assert!(first.is_empty(), "blocked receive must not complete");

    runtime.spawn(&m, send, vec![AnyValue::Int(1)]).expect("spawn sender");
    let second = runtime.drive_until_idle(&mut t, &tel, Some(1)).expect("drive sender");
    assert_eq!(drive_completion_i64(&second, 1), Some(77));
}

// DROP: old-world multi-image runtime code swapping, no compiler2 analogue
#[test]
fn spawned_child_resumes_with_original_code_image_after_root_advances() {
    let first_image = lower_src(
        r#"
        fn child(parent) do
          msg = receive do
            x -> x
          end
          send(parent, msg)
        end

        fn start_child() do
          me = self()
          spawn(fn () -> child(me) end)
        end
    "#,
    );
    let second_image = lower_src(
        r#"
        fn send_to_child(pid) do
          send(pid, 99)
        end

        fn receive_reply() do
          receive do
            x -> x
          end
        end
    "#,
    );
    let start_child = first_image.fn_by_name("start_child").expect("start_child").id;
    let send_to_child = second_image.fn_by_name("send_to_child").expect("send_to_child").id;
    let receive_reply = second_image.fn_by_name("receive_reply").expect("receive_reply").id;
    let mut t = crate::types::new();
    let mut runtime = IrInterpRuntime::fresh_with_root(&first_image);
    let tel = ConfiguredTelemetry::new();

    runtime
        .enqueue_entry(&first_image, &tel, 1, start_child, vec![])
        .expect("enqueue start_child");
    let child_started = runtime
        .drive_until_idle(&mut t, &tel, Some(1))
        .expect("drive start_child");
    assert_eq!(drive_completion_i64(&child_started, 1), Some(2));

    runtime
        .enqueue_entry(&second_image, &tel, 1, send_to_child, vec![AnyValue::Int(2)])
        .expect("enqueue send_to_child");
    runtime
        .drive_until_idle(&mut t, &tel, Some(1))
        .expect("drive send_to_child");

    runtime
        .enqueue_entry(&second_image, &tel, 1, receive_reply, vec![])
        .expect("enqueue receive_reply");
    let reply = runtime
        .drive_until_idle(&mut t, &tel, Some(1))
        .expect("drive receive_reply");
    assert_eq!(drive_completion_i64(&reply, 1), Some(99));
}

// DROP: old-world IrInterpRuntime multi-drive API, no compiler2 analogue
#[test]
fn persistent_selective_receive_resumes_after_later_drive_send() {
    let m = lower_src(
        r#"
        fn wait_selective() do
          receive do
            {:reply, value} -> value
          end
        end

        fn send_selective(pid) do
          send(pid, {:reply, 88})
        end
    "#,
    );
    let wait = m.fn_by_name("wait_selective").expect("wait_selective").id;
    let send = m.fn_by_name("send_selective").expect("send_selective").id;
    let mut t = crate::types::new();
    let mut runtime = IrInterpRuntime::fresh_with_root(&m);
    let tel = ConfiguredTelemetry::new();

    runtime.enqueue_entry(&m, &tel, 1, wait, vec![]).expect("enqueue wait");
    let first = runtime
        .drive_until_idle(&mut t, &tel, Some(1))
        .expect("drive blocked selective wait");
    assert!(first.is_empty(), "blocked selective receive must not complete");

    runtime
        .spawn(&m, send, vec![AnyValue::Int(1)])
        .expect("spawn selective sender");
    let second = runtime
        .drive_until_idle(&mut t, &tel, Some(1))
        .expect("drive selective sender");
    assert_eq!(drive_completion_i64(&second, 1), Some(88));
}

/// `after 0` fires the after body when nothing in the mailbox matches.
// PICKED: receive after 0 fires immediately when no message matches
#[test]
fn after_zero_fires_immediately_on_empty_mailbox() {
    let src = r#"
        fn main() do
          v = receive do
            {:never, _} -> 11
          after 0 -> 12
          end
          dbg(v)
        end
    "#;
    let out = run_and_capture(src).expect("interp run");
    assert!(out.contains("12"), "expected 12, got: {}", out);
}

/// Receiver-side scan finds a message left in the mailbox by an
/// earlier `receive` that skipped it.
// PICKED: selective receive retrieves out-of-order message skipped earlier
#[test]
fn receiver_scan_finds_earlier_skipped_message() {
    let src = r#"
        fn main() do
          me = self()
          send(me, {:a, 1})
          send(me, {:b, 2})
          vb = receive do
            {:b, x} -> x
          end
          va = receive do
            {:a, x} -> x
          end
          dbg(va + vb)
        end
    "#;
    let out = run_and_capture(src).expect("interp run");
    assert!(out.contains("3"), "expected 3, got: {}", out);
}

// DROP: old-world interp telemetry probe-miss counters, no compiler2 analogue
#[test]
fn receive_reuses_lowered_dispatch_during_interp_probes() {
    use crate::telemetry::{Capture, ConfiguredTelemetry, Value as TelemetryValue};

    let src = r#"
        fn main() do
          me = self()
          send(me, {:skip, 0})
          send(me, {:skip, 1})
          send(me, {:hit, 2})
          v = receive do
            {:hit, x} -> x
          end
          dbg(v)
        end
    "#;
    let m = lower_src(src);
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "interp", "receive"], cap.handler());
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());
    run_main(&tel, &m).expect("interp run");
    let out = dbg.lines().join("\n");
    assert!(out.contains("2"), "expected 2, got: {}", out);
    assert_eq!(
        cap.count(&["fz", "interp", "receive", "probe_miss"]),
        2,
        "two skipped mailbox messages should be observed as receive dispatch misses"
    );
    let hits = cap.find(&["fz", "interp", "receive", "probe_hit"]);
    assert_eq!(hits.len(), 1, "exactly one receive dispatch hit expected");
    let hit = &hits[0];
    assert!(matches!(
        hit.measurements.get("clause_idx"),
        Some(TelemetryValue::U64(0))
    ));
    assert!(matches!(
        hit.measurements.get("bound_count"),
        Some(TelemetryValue::U64(1))
    ));
}

// PICKED: map pattern in receive matches correct message from mailbox
#[test]
fn receive_map_probe_uses_dispatch_without_ast_pattern_walk() {
    let src = r#"
        fn main() do
          me = self()
          send(me, :skip)
          send(me, %{name: 42, age: 30})
          v = receive do
            %{name: n} -> n
          end
          dbg(v)
        end
    "#;
    let m = lower_src(src);
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());
    run_main(&tel, &m).expect("interp run");
    let out = dbg.lines().join("\n");
    assert!(out.contains("42"), "expected 42, got: {}", out);
}

// PICKED: map receive pattern matches key whose value is nil
#[test]
fn receive_map_pattern_matches_present_nil_value() {
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
    let m = lower_src(src);
    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    tel.attach(&[], dbg.handler());
    run_main(&tel, &m).expect("interp run");
    let out = dbg.lines().join("\n");
    assert_eq!(out, "nil", "present nil map value must match, got: {}", out);
}

/// fixtures/receive_selective_refs/input.fz — the design proof point
/// for fz-recv: sender-side miss, sender-side hit, and receiver-side
/// scan hit in a single trace. See docs/receive-matched-stress-test.html.
// PICKED: pinned-ref selective receive with out-of-order server replies
#[test]
fn fixture_receive_selective_refs() {
    let src = read_to_string("fixtures/receive_selective_refs/input.fz").expect("read fixture");
    let out = run_and_capture(&src).expect("interp run");
    assert!(out.contains("3"), "expected 3, got: {}", out);
}
