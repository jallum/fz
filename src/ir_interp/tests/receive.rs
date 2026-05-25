// ----- fz-yxs/fz-2v3 — selective receive interp tests -----

use crate::fz_ir::Module;
use crate::ir_interp::run_main;
use crate::lexer::Lexer;
use crate::parser::Parser;

fn lower_src(src: &str) -> Module {
    let toks = Lexer::new(src).tokenize().expect("lex");
    let prog = Parser::new(toks).parse_program().expect("parse");
    crate::ir_lower::lower_program(&mut crate::types::ConcreteTypes, &prog).expect("lower")
}

fn run_and_capture(src: &str) -> Result<String, String> {
    let m = lower_src(src);
    let _ = fz_runtime::ir_runtime::test_capture_take();
    run_main(&crate::telemetry::NullTelemetry, &m)?;
    Ok(fz_runtime::ir_runtime::test_capture_take().join("\n"))
}

/// Initial-scan hit: the message is already in the mailbox at the
/// point the receive runs (self-send then receive).
#[test]
fn initial_scan_pinned_match() {
    let src = r#"
        fn main() do
          ref = make_ref()
          send(self(), {:reply, ref, 7})
          v = receive do
            {:reply, ^ref, val} -> val
          end
          print(v)
        end
    "#;
    let out = run_and_capture(src).expect("interp run");
    assert!(out.contains("7"), "expected 7, got: {}", out);
}

/// Sender-side probe hit: receiver parks, then a sender delivers a
/// matching message; the sender-side probe wakes the receiver with
/// the matched body.
#[test]
fn sender_side_probe_match() {
    let src = r#"
        fn child(parent) do
          send(parent, {:reply, :tag, 99})
        end
        fn main() do
          me = self()
          spawn(fn () -> child(me))
          v = receive do
            {:reply, :tag, val} -> val
          end
          print(v)
        end
    "#;
    let out = run_and_capture(src).expect("interp run");
    assert!(out.contains("99"), "expected 99, got: {}", out);
}

/// `after 0` fires the after body when nothing in the mailbox matches.
#[test]
fn after_zero_fires_immediately_on_empty_mailbox() {
    let src = r#"
        fn main() do
          v = receive do
            {:never, _} -> 11
          after 0 -> 12
          end
          print(v)
        end
    "#;
    let out = run_and_capture(src).expect("interp run");
    assert!(out.contains("12"), "expected 12, got: {}", out);
}

/// Receiver-side scan finds a message left in the mailbox by an
/// earlier `receive` that skipped it.
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
          print(va + vb)
        end
    "#;
    let out = run_and_capture(src).expect("interp run");
    assert!(out.contains("3"), "expected 3, got: {}", out);
}

#[test]
fn receive_reuses_lowered_matcher_during_interp_probes() {
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
          print(v)
        end
    "#;
    let m = lower_src(src);
    let tel = ConfiguredTelemetry::new();
    let cap = Capture::new();
    tel.attach(&["fz", "interp", "receive"], cap.handler());
    crate::pattern_matrix::reset_compile_count();
    let _ = fz_runtime::ir_runtime::test_capture_take();
    run_main(&tel, &m).expect("interp run");
    let out = fz_runtime::ir_runtime::test_capture_take().join("\n");
    assert!(out.contains("2"), "expected 2, got: {}", out);
    assert_eq!(
        cap.count(&["fz", "interp", "receive", "probe_miss"]),
        2,
        "two skipped mailbox messages should be observed as receive matcher misses"
    );
    let hits = cap.find(&["fz", "interp", "receive", "probe_hit"]);
    assert_eq!(hits.len(), 1, "exactly one receive matcher hit expected");
    let hit = &hits[0];
    assert!(matches!(
        hit.measurements.get("clause_idx"),
        Some(TelemetryValue::U64(0))
    ));
    assert!(matches!(
        hit.measurements.get("bound_count"),
        Some(TelemetryValue::U64(1))
    ));
    assert_eq!(
        crate::pattern_matrix::compile_count(),
        0,
        "interp receive probes must reuse the lowered Matcher instead of recompiling per message"
    );
}

#[test]
fn receive_map_probe_uses_matcher_without_ast_pattern_walk() {
    let src = r#"
        fn main() do
          me = self()
          send(me, :skip)
          send(me, %{name: 42, age: 30})
          v = receive do
            %{name: n} -> n
          end
          print(v)
        end
    "#;
    let m = lower_src(src);
    let _ = fz_runtime::ir_runtime::test_capture_take();
    run_main(&crate::telemetry::NullTelemetry, &m).expect("interp run");
    let out = fz_runtime::ir_runtime::test_capture_take().join("\n");
    assert!(out.contains("42"), "expected 42, got: {}", out);
}

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
          print(v)
        end
    "#;
    let m = lower_src(src);
    let _ = fz_runtime::ir_runtime::test_capture_take();
    run_main(&crate::telemetry::NullTelemetry, &m).expect("interp run");
    let out = fz_runtime::ir_runtime::test_capture_take().join("\n");
    assert_eq!(out, "nil", "present nil map value must match, got: {}", out);
}

/// fixtures/receive_selective_refs/input.fz — the design proof point
/// for fz-recv: sender-side miss, sender-side hit, and receiver-side
/// scan hit in a single trace. See docs/receive-matched-stress-test.html.
#[test]
fn fixture_receive_selective_refs() {
    let src = std::fs::read_to_string("fixtures/receive_selective_refs/input.fz")
        .expect("read fixture");
    let out = run_and_capture(&src).expect("interp run");
    assert!(out.contains("3"), "expected 3, got: {}", out);
}
