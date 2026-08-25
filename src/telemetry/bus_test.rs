use std::cell::{Cell, RefCell};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::rc::Rc;
use std::thread::sleep;
use std::time::Duration;

use super::*;
use crate::telemetry::capture::Capture;
use crate::telemetry::sink::{RawSpanStop1 as _, RawSpanStop2 as _, TelemetryExt};
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
    t.event_lazy(&["fz", "a"], Metadata::new);
    t.event_lazy(&["other"], Metadata::new);
    assert_eq!(cap.len(), 2);
}

#[test]
fn prefix_filters_non_matching_events() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&["fz", "lex"], cap.handler());
    t.event_lazy(&["fz", "lex", "tokens_built"], Metadata::new);
    t.event_lazy(&["fz", "parse", "ast"], Metadata::new);
    t.event_lazy(&["other"], Metadata::new);
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
    t.event_lazy(&["fz", "lex", "x"], Metadata::new);
    t.event_lazy(&["fz", "parse", "y"], Metadata::new);
    assert_eq!(all.len(), 2);
    assert_eq!(only_lex.len(), 1);
}

#[test]
fn raw_event_handlers_receive_original_references_independently() {
    let t = ConfiguredTelemetry::new();
    let pointer = Rc::new(Cell::new(std::ptr::null::<String>()));
    let retained = Rc::new(RefCell::new(Vec::new()));
    let pointer_sink = Rc::clone(&pointer);
    let retained_sink = Rc::clone(&retained);
    t.attach_raw_event2::<String, u64, _>(&["fz", "raw"], move |_, _, _, text, _| {
        pointer_sink.set(text);
    });
    t.attach_raw_event2::<String, u64, _>(&["fz", "raw"], move |_, _, _, text, count| {
        retained_sink.borrow_mut().push((text.clone(), *count));
    });
    let text = String::from("value");
    let count = 7_u64;

    t.raw_event2(&["fz", "raw", "event"], &text, &count);

    assert_eq!(pointer.get(), &text);
    assert_eq!(&*retained.borrow(), &[(String::from("value"), 7)]);
}

#[test]
fn legacy_handlers_do_not_enable_raw_events() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&["fz", "raw"], cap.handler());
    let value = 41_u64;

    t.raw_event1(&["fz", "raw", "event"], &value);

    assert!(cap.events().is_empty());
}

#[test]
fn raw_event_registration_filters_type_prefix_and_detach() {
    let t = ConfiguredTelemetry::new();
    let calls = Rc::new(Cell::new(0));
    let sink = Rc::clone(&calls);
    let id = t.attach_raw_event1::<u64, _>(&["fz", "raw"], move |_, _, _, _| {
        sink.set(sink.get() + 1);
    });
    let value = 1_u64;
    let wrong = 1_u32;

    t.raw_event1(&["other"], &value);
    t.raw_event1(&["fz", "raw"], &wrong);
    t.raw_event1(&["fz", "raw"], &value);
    assert_eq!(calls.get(), 1);
    assert!(t.detach(id));
    t.raw_event1(&["fz", "raw"], &value);
    assert_eq!(calls.get(), 1);
}

#[test]
fn raw_lifecycle_observes_without_payload_registration_and_detaches() {
    let t = ConfiguredTelemetry::new();
    let observed = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&observed);
    let id = t.attach_raw_lifecycle(
        &["fz", "raw"],
        move |name, kind, span_id, parent_span_id, elapsed_ns| {
            sink.borrow_mut()
                .push((name.to_vec(), kind, span_id, parent_span_id, elapsed_ns));
        },
    );
    let value = 1_u64;

    t.raw_event1(&["fz", "raw", "event"], &value);
    t.raw_span1_1::<u64, u64>(&["fz", "raw", "span"], &value).stop1(&value);
    t.raw_span1_1::<u64, u64>(&["fz", "raw", "failed"], &value).exception();

    let events = observed.borrow();
    assert_eq!(
        events.iter().map(|event| event.1).collect::<Vec<_>>(),
        [
            EventKind::Event,
            EventKind::SpanStart,
            EventKind::SpanStop,
            EventKind::SpanStart,
            EventKind::SpanException,
        ]
    );
    assert_eq!(events[1].2, events[2].2);
    assert_eq!(events[3].2, events[4].2);
    assert!(events[2].4.is_some());
    assert!(events[4].4.is_some());
    drop(events);

    assert!(t.detach(id));
    t.raw_event1(&["fz", "raw", "event"], &value);
    assert_eq!(observed.borrow().len(), 5);
}

#[test]
fn raw_span_future_signature_controls_state_before_timing() {
    let t = ConfiguredTelemetry::new();
    let calls = Rc::new(Cell::new(0));
    let start_sink = Rc::clone(&calls);
    let stop_sink = Rc::clone(&calls);
    let exception_sink = Rc::clone(&calls);
    t.attach_raw_span0_1::<u64, _, _, _>(
        &["fz", "raw", "span"],
        move |_, _, _| start_sink.set(start_sink.get() + 1),
        move |_, _, _, _, _| stop_sink.set(stop_sink.get() + 1),
        move |_, _, _, _| exception_sink.set(exception_sink.get() + 1),
    );

    let span = t.raw_span0_1::<String>(&["fz", "raw", "span"]);

    assert_eq!(span.span_id(), 0);
    assert_eq!(t.next_span_id.get(), 1);
    assert!(t.span_stack.borrow().is_empty());
    assert_eq!(calls.get(), 0);
}

#[test]
fn raw_span_handlers_match_both_signatures_and_borrow_both_phases() {
    let t = ConfiguredTelemetry::new();
    let start_pointer = Rc::new(Cell::new(std::ptr::null::<String>()));
    let stop_pointer = Rc::new(Cell::new(std::ptr::null::<Vec<u8>>()));
    let wrong_calls = Rc::new(Cell::new(0));
    let start_sink = Rc::clone(&start_pointer);
    let stop_sink = Rc::clone(&stop_pointer);
    let wrong_start = Rc::clone(&wrong_calls);
    let wrong_stop = Rc::clone(&wrong_calls);
    let wrong_exception = Rc::clone(&wrong_calls);
    t.attach_raw_span1_2::<String, String, u64, _, _, _>(
        &["fz", "raw", "span"],
        move |_, _, _, _| wrong_start.set(wrong_start.get() + 1),
        move |_, _, _, _, _, _| wrong_stop.set(wrong_stop.get() + 1),
        move |_, _, _, _| wrong_exception.set(wrong_exception.get() + 1),
    );
    t.attach_raw_span1_2::<String, Vec<u8>, u64, _, _, _>(
        &["fz", "raw", "span"],
        move |_, _, _, value| start_sink.set(value),
        move |_, _, _, elapsed_ns, value, _| {
            assert!(elapsed_ns > 0);
            stop_sink.set(value);
        },
        |_, _, _, _| panic!("unexpected exception"),
    );
    let start = String::from("start");
    let stop = vec![1_u8, 2];
    let stop_count = 2_u64;

    let span = t.raw_span1_2::<String, Vec<u8>, u64>(&["fz", "raw", "span"], &start);
    sleep(Duration::from_micros(50));
    span.stop2(&stop, &stop_count);

    assert_eq!(start_pointer.get(), &start);
    assert_eq!(stop_pointer.get(), &stop);
    assert_eq!(wrong_calls.get(), 0);
    assert!(t.span_stack.borrow().is_empty());
}

#[test]
fn dropping_payload_span_invokes_payloadless_exception() {
    let t = ConfiguredTelemetry::new();
    let exceptions = Rc::new(Cell::new(0));
    let sink = Rc::clone(&exceptions);
    t.attach_raw_span0_1::<u64, _, _, _>(
        &["fz", "raw", "span"],
        |_, _, _| {},
        |_, _, _, _, _| panic!("unexpected stop"),
        move |_, _, _, elapsed_ns| {
            assert!(elapsed_ns > 0);
            sink.set(sink.get() + 1);
        },
    );

    let span = t.raw_span0_1::<u64>(&["fz", "raw", "span"]);
    sleep(Duration::from_micros(50));
    drop(span);

    assert_eq!(exceptions.get(), 1);
    assert!(t.span_stack.borrow().is_empty());
}

#[test]
fn unwinding_payload_span_invokes_payloadless_exception() {
    let t = ConfiguredTelemetry::new();
    let exceptions = Rc::new(Cell::new(0));
    let sink = Rc::clone(&exceptions);
    t.attach_raw_span1_2::<String, Vec<u8>, u64, _, _, _>(
        &["fz", "raw", "span"],
        |_, _, _, _| {},
        |_, _, _, _, _, _| panic!("unexpected stop"),
        move |_, _, _, _| sink.set(sink.get() + 1),
    );

    let result = catch_unwind(AssertUnwindSafe(|| {
        let start = String::from("start");
        let _span = t.raw_span1_2::<String, Vec<u8>, u64>(&["fz", "raw", "span"], &start);
        panic!("planned");
    }));

    assert!(result.is_err());
    assert_eq!(exceptions.get(), 1);
    assert!(t.span_stack.borrow().is_empty());
}

#[test]
fn null_telemetry_raw_boundary_is_a_no_op() {
    let t = crate::NullTelemetry;
    let start = String::from("start");
    let stop = vec![1_u8, 2];

    t.raw_event1(&["fz", "raw"], &start);
    let stop_count = 2_u64;
    let span = t.raw_span1_2::<String, Vec<u8>, u64>(&["fz", "raw", "span"], &start);
    assert_eq!(std::mem::size_of_val(&span), 0);
    assert!(!std::mem::needs_drop::<crate::telemetry::sink::NullSpan>());
    span.stop2(&stop, &stop_count);
}

#[test]
fn raw_boundary_inventory_exercises_fixed_arities() {
    let t = ConfiguredTelemetry::new();
    t.attach_raw_event0(&["fz", "raw", "zero"], |_, _, _| {});
    t.attach_raw_event3::<u8, u16, u32, _>(&["fz", "raw", "three"], |_, _, _, _, _, _| {});
    t.attach_raw_span0_0(&["fz", "raw", "span0"], |_, _, _| {}, |_, _, _, _| {}, |_, _, _, _| {});
    t.attach_raw_span2_0::<u8, u16, _, _, _>(
        &["fz", "raw", "span2"],
        |_, _, _, _, _| {},
        |_, _, _, _| {},
        |_, _, _, _| {},
    );
    t.attach_raw_span0_1::<u64, _, _, _>(
        &["fz", "raw", "exception"],
        |_, _, _| {},
        |_, _, _, _, _| {},
        |_, _, _, _| {},
    );
    let a = 1_u8;
    let b = 2_u16;
    let c = 3_u32;

    t.raw_event0(&["fz", "raw", "zero"]);
    t.raw_event3(&["fz", "raw", "three"], &a, &b, &c);
    t.raw_span0_0(&["fz", "raw", "span0"]).stop0();
    t.raw_span2_0(&["fz", "raw", "span2"], &a, &b).stop0();
    t.raw_span0_1::<u64>(&["fz", "raw", "exception"]).exception();
    t.raw_span0_1::<u64>(&["fz", "raw", "exception"]).stop1(&1);

    assert!(t.span_stack.borrow().is_empty());
}

#[test]
fn span_lifecycle_emits_synthetic_events() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&[], cap.handler());
    {
        let _s = t.span_lazy(&["fz", "lex", "pass"], || metadata! { fn_name: "main" });
        t.execute_lazy(&["fz", "lex", "tokens_built"], || {
            (measurements! { count: 17u64 }, Metadata::new())
        });
    }
    let evs = cap.events();
    // Expected: span.start, then user event, then span.stop.
    assert_eq!(evs.len(), 3);
    assert!(matches!(evs[0].kind, EventKind::SpanStart));
    assert!(matches!(evs[1].kind, EventKind::Event));
    assert!(matches!(evs[2].kind, EventKind::SpanStop));
}

#[test]
fn descendant_handler_keeps_its_parent_lazy_span_active() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&["fz", "outer", "child"], cap.handler());
    let constructed = std::cell::Cell::new(0);
    {
        let _parent = t.span_lazy(&["fz", "outer"], || {
            constructed.set(constructed.get() + 1);
            Metadata::new()
        });
        t.execute_lazy(&["fz", "outer", "child", "event"], || {
            (Measurements::new(), Metadata::new())
        });
    }

    assert_eq!(constructed.get(), 1);
    let event = cap.last(&["fz", "outer", "child", "event"]).expect("child event");
    assert!(event.span_id > 0);
}

#[test]
fn events_during_span_inherit_span_id() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&[], cap.handler());
    {
        let _s = t.span_lazy(&["fz", "outer"], Metadata::new);
        t.event_lazy(&["fz", "user", "event"], Metadata::new);
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
        let _outer = t.span_lazy(&["fz", "outer"], Metadata::new);
        {
            let _inner = t.span_lazy(&["fz", "outer", "inner"], Metadata::new);
            t.event_lazy(&["fz", "u"], Metadata::new);
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
        let _s = t.span_lazy(&["fz", "x"], Metadata::new);
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
fn panic_inside_span_emits_exception_event() {
    let t = ConfiguredTelemetry::new();
    let cap = Capture::new();
    t.attach(&[], cap.handler());
    let r = catch_unwind(AssertUnwindSafe(|| {
        let _s = t.span_lazy(&["fz", "boom"], Metadata::new);
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
