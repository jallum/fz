use super::*;
use crate::telemetry::bus::ConfiguredTelemetry;
use crate::telemetry::sink::{Telemetry, TelemetryExt};
use crate::telemetry::value::Value;
use crate::{measurements, metadata};

#[test]
fn capture_starts_empty() {
    let c = Capture::new();
    assert_eq!(c.len(), 0);
    assert!(c.is_empty());
}

#[test]
fn handler_records_each_emit() {
    let t = ConfiguredTelemetry::new();
    let c = Capture::new();
    t.attach(&[], c.handler());
    t.emit(&["fz", "a"]);
    t.emit(&["fz", "b"]);
    assert_eq!(c.len(), 2);
}

#[test]
fn captured_event_carries_owned_measurements_and_metadata() {
    let t = ConfiguredTelemetry::new();
    let c = Capture::new();
    t.attach(&[], c.handler());
    t.execute(
        &["fz", "lex", "tokens_built"],
        &measurements! { count: 42u64 },
        &metadata! { source: "main.fz" },
    );
    let ev = c.last(&["fz", "lex", "tokens_built"]).unwrap();
    assert!(matches!(ev.measurements.get("count"), Some(Value::U64(42))));
    assert!(matches!(ev.metadata.get("source"), Some(Value::Str(_))));
}

#[test]
fn count_matches_exact_name_only() {
    let t = ConfiguredTelemetry::new();
    let c = Capture::new();
    t.attach(&[], c.handler());
    t.emit(&["fz", "a"]);
    t.emit(&["fz", "a"]);
    t.emit(&["fz", "b"]);
    assert_eq!(c.count(&["fz", "a"]), 2);
    assert_eq!(c.count(&["fz", "b"]), 1);
    assert_eq!(c.count(&["fz"]), 0);
    assert_eq!(c.count(&["fz", "c"]), 0);
}

#[test]
fn find_returns_events_under_prefix() {
    let t = ConfiguredTelemetry::new();
    let c = Capture::new();
    t.attach(&[], c.handler());
    t.emit(&["fz", "lex", "a"]);
    t.emit(&["fz", "lex", "b"]);
    t.emit(&["fz", "parse", "x"]);
    assert_eq!(c.find(&["fz", "lex"]).len(), 2);
    assert_eq!(c.find(&["fz"]).len(), 3);
    assert_eq!(c.find(&[]).len(), 3);
}

#[test]
fn last_returns_most_recent_with_exact_name() {
    let t = ConfiguredTelemetry::new();
    let c = Capture::new();
    t.attach(&[], c.handler());
    t.execute(&["fz", "x"], &measurements! { n: 1i64 }, &Metadata::new());
    t.execute(&["fz", "x"], &measurements! { n: 2i64 }, &Metadata::new());
    let ev = c.last(&["fz", "x"]).unwrap();
    assert!(matches!(ev.measurements.get("n"), Some(Value::I64(2))));
}

#[test]
fn span_events_captured_with_kind() {
    let t = ConfiguredTelemetry::new();
    let c = Capture::new();
    t.attach(&[], c.handler());
    {
        let _s = t.span(&["fz", "lex", "pass"], Metadata::new());
    }
    assert_eq!(c.count_by_kind(EventKind::SpanStart), 1);
    assert_eq!(c.count_by_kind(EventKind::SpanStop), 1);
    assert_eq!(c.count_by_kind(EventKind::SpanException), 0);
}

#[test]
fn clear_drops_history_but_keeps_handler_live() {
    let t = ConfiguredTelemetry::new();
    let c = Capture::new();
    t.attach(&[], c.handler());
    t.emit(&["fz", "a"]);
    assert_eq!(c.len(), 1);
    c.clear();
    assert_eq!(c.len(), 0);
    t.emit(&["fz", "b"]);
    assert_eq!(c.len(), 1);
}

#[test]
fn contains_is_a_convenience_for_count_gt_zero() {
    let t = ConfiguredTelemetry::new();
    let c = Capture::new();
    t.attach(&[], c.handler());
    t.emit(&["fz", "x"]);
    assert!(c.contains(&["fz", "x"]));
    assert!(!c.contains(&["fz", "y"]));
}

#[test]
fn capture_observes_only_attached_prefix() {
    let t = ConfiguredTelemetry::new();
    let c = Capture::new();
    t.attach(&["fz", "lex"], c.handler());
    t.emit(&["fz", "lex", "a"]);
    t.emit(&["fz", "parse", "x"]);
    assert_eq!(c.len(), 1);
    assert!(c.contains(&["fz", "lex", "a"]));
}
