use std::panic::{AssertUnwindSafe, catch_unwind};
use std::thread::sleep;
use std::time::Duration;

use super::*;
use crate::telemetry::capture::Capture;
use crate::telemetry::sink::TelemetryExt;
use crate::telemetry::value::Value;
use crate::{measurements, metadata};

#[test]
fn attach_returns_increasing_ids() {
    let t = ConfiguredTelemetry::new();
    let a = t.attach(&[], Box::new(NoopHandler));
    let b = t.attach(&["fz"], Box::new(NoopHandler));
    assert_ne!(a, b);
    assert_eq!(t.handler_count(), 2);
}

#[test]
fn detach_removes_a_handler() {
    let t = ConfiguredTelemetry::new();
    let a = t.attach(&[], Box::new(NoopHandler));
    let b = t.attach(&[], Box::new(NoopHandler));
    assert_eq!(t.handler_count(), 2);
    assert!(t.detach(a));
    assert_eq!(t.handler_count(), 1);
    assert!(!t.detach(a), "detaching twice returns false");
    assert!(t.detach(b));
    assert_eq!(t.handler_count(), 0);
}

#[test]
fn empty_prefix_matches_every_event() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&[], cap.handler());
    t.emit(&["fz", "a"]);
    t.emit(&["other"]);
    assert_eq!(cap.len(), 2);
}

#[test]
fn prefix_filters_non_matching_events() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&["fz", "lex"], cap.handler());
    t.emit(&["fz", "lex", "tokens_built"]);
    t.emit(&["fz", "parse", "ast"]);
    t.emit(&["other"]);
    let evs = cap.events();
    assert_eq!(evs.len(), 1);
    assert_eq!(evs[0].name, vec!["fz", "lex", "tokens_built"]);
}

#[test]
fn multiple_handlers_fan_out_independently() {
    let t = ConfiguredTelemetry::new();
    let all = Capture::new();
    let only_lex = Capture::new();
    t.attach(&[], all.handler());
    t.attach(&["fz", "lex"], only_lex.handler());
    t.emit(&["fz", "lex", "x"]);
    t.emit(&["fz", "parse", "y"]);
    assert_eq!(all.len(), 2);
    assert_eq!(only_lex.len(), 1);
}

#[test]
fn span_lifecycle_emits_synthetic_events() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&[], cap.handler());
    {
        let _s = t.span(&["fz", "lex", "pass"], metadata! { fn_name: "main" });
        t.execute(
            &["fz", "lex", "tokens_built"],
            &measurements! { count: 17u64 },
            &Metadata::new(),
        );
    }
    let evs = cap.events();
    // Expected: span.start, then user event, then span.stop.
    assert_eq!(evs.len(), 3);
    assert!(matches!(evs[0].kind, EventKind::SpanStart));
    assert!(matches!(evs[1].kind, EventKind::Event));
    assert!(matches!(evs[2].kind, EventKind::SpanStop));
}

#[test]
fn events_during_span_inherit_span_id() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&[], cap.handler());
    {
        let _s = t.span(&["fz", "outer"], Metadata::new());
        t.emit(&["fz", "user", "event"]);
    }
    let evs = cap.events();
    // outer.start, user.event, outer.stop
    let outer_id = evs[0].span_id;
    assert!(outer_id > 0);
    assert_eq!(evs[1].kind, EventKind::Event);
    assert_eq!(evs[1].span_id, outer_id);
    assert_eq!(evs[1].parent_span_id, 0);
}

#[test]
fn nested_spans_set_parent_span_id() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&[], cap.handler());
    {
        let _outer = t.span(&["fz", "outer"], Metadata::new());
        {
            let _inner = t.span(&["fz", "outer", "inner"], Metadata::new());
            t.emit(&["fz", "u"]);
        }
    }
    let evs = cap.events();
    // outer.start (id=1, parent=0)
    // inner.start (id=2, parent=1)
    // user event (id=2, parent=1)
    // inner.stop  (id=2, parent=1)
    // outer.stop  (id=1, parent=0)
    assert_eq!(evs.len(), 5);
    assert_eq!(evs[0].span_id, 1);
    assert_eq!(evs[0].parent_span_id, 0);
    assert_eq!(evs[1].span_id, 2);
    assert_eq!(evs[1].parent_span_id, 1);
    assert_eq!(evs[2].kind, EventKind::Event);
    assert_eq!(evs[2].span_id, 2);
    assert_eq!(evs[2].parent_span_id, 1);
    assert_eq!(evs[3].kind, EventKind::SpanStop);
    assert_eq!(evs[3].span_id, 2);
    assert_eq!(evs[4].kind, EventKind::SpanStop);
    assert_eq!(evs[4].span_id, 1);
    assert_eq!(evs[4].parent_span_id, 0);
}

#[test]
fn span_stop_event_carries_elapsed_ns() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&[], cap.handler());
    {
        let _s = t.span(&["fz", "x"], Metadata::new());
        sleep(Duration::from_micros(50));
    }
    let evs = cap.events();
    let stop = evs
        .iter()
        .find(|ev| ev.kind == EventKind::SpanStop)
        .expect("expected SpanStop event");
    let ns = match stop.measurements.get("elapsed_ns") {
        Some(Value::U64(n)) => *n,
        other => panic!("expected elapsed_ns U64, got {:?}", other),
    };
    assert!(ns > 0);
}

#[test]
fn span_stop_event_carries_close_payload() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&[], cap.handler());
    {
        let mut span = t.span(&["fz", "x"], Metadata::new());
        span.close_with(measurements! { jobs_ran: 3u64 }, metadata! { outcome: "ok" });
    }
    let events = cap.events();
    let stop = events
        .iter()
        .find(|ev| ev.kind == EventKind::SpanStop)
        .expect("expected SpanStop event");
    assert!(matches!(stop.measurements.get("jobs_ran"), Some(Value::U64(3))));
    assert!(matches!(
        stop.metadata.get("outcome"),
        Some(Value::Str(value)) if value.as_ref() == "ok"
    ));
}

#[test]
fn panic_inside_span_emits_exception_event() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&[], cap.handler());
    let r = catch_unwind(AssertUnwindSafe(|| {
        let _s = t.span(&["fz", "boom"], Metadata::new());
        panic!("planned");
    }));
    assert!(r.is_err());
    let evs = cap.events();
    assert_eq!(evs.len(), 2);
    assert_eq!(evs[0].kind, EventKind::SpanStart);
    assert_eq!(evs[1].kind, EventKind::SpanException);
}

struct NoopHandler;
impl Handler for NoopHandler {
    fn handle(&self, _: &Event<'_, '_, '_>) {}
}
