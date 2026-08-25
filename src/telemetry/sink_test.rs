use std::cell::{Cell, RefCell};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::thread::sleep;
use std::time::Duration;

use super::*;
use crate::metadata;

#[test]
fn telemetry_is_object_safe() {
    let bus = crate::telemetry::ConfiguredTelemetry::new();
    let t: &dyn Telemetry = &bus;
    t.event_lazy(&["fz", "x"], Metadata::new);
}

#[test]
fn ext_span_is_callable_through_dyn() {
    let bus = crate::telemetry::ConfiguredTelemetry::new();
    let t: &dyn Telemetry = &bus;
    t.attach(&["fz"], Box::new(|_: &crate::telemetry::Event<'_, '_, '_>| {}));
    let span = t.span_lazy(&["fz", "any", "pass"], || metadata! { x: 1i64 });
    assert_eq!(span.span_id(), 1);
    assert_eq!(span.name(), &["fz", "any", "pass"]);
}

#[test]
fn ext_span_is_callable_through_concrete() {
    let t = crate::telemetry::ConfiguredTelemetry::new();
    t.attach(&["fz"], Box::new(|_: &crate::telemetry::Event<'_, '_, '_>| {}));
    let span = t.span_lazy(&["fz", "any", "pass"], Metadata::new);
    assert_eq!(span.span_id(), 1);
}

#[test]
fn detached_span_does_not_construct_payload_without_a_handler() {
    let tel = NullTelemetry;
    let projections = Cell::new(0);
    let span = tel.start_span_lazy(&["fz", "x"], || {
        projections.set(projections.get() + 1);
        Metadata::new()
    });
    tel.stop_span_lazy(span, || {
        projections.set(projections.get() + 1);
        (Measurements::new(), Metadata::new())
    });
    assert_eq!(projections.get(), 0);
}

#[test]
fn detached_span_preserves_parent_linkage_until_stop() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let capture = crate::telemetry::Capture::new();
    capture.install(&tel, &[]);
    let span = tel.start_span_lazy(&["fz", "parent"], Metadata::new);
    tel.event_lazy(&["fz", "child"], Metadata::new);
    tel.stop_span_lazy(span, || (Measurements::new(), Metadata::new()));
    let parent = capture.last(&["fz", "parent"]).expect("parent stop");
    let child = capture.last(&["fz", "child"]).expect("child event");
    assert_eq!(child.span_id, parent.span_id);
}

#[test]
fn dyn_telemetry_attach_and_detach_dispatch_to_configured_bus() {
    let bus = crate::telemetry::ConfiguredTelemetry::new();
    let t: &dyn Telemetry = &bus;
    let cap = crate::telemetry::Capture::new();

    let handler_id = t.attach(&["fz"], cap.handler());
    t.event_lazy(&["fz", "x"], Metadata::new);
    assert_eq!(cap.len(), 1);
    assert!(t.detach(handler_id));
    t.event_lazy(&["fz", "y"], Metadata::new);
    assert_eq!(cap.len(), 1);
}

/// Tiny mock that counts each method call. Used by sibling tests
/// in fz-ndf.4 onward — here it just demonstrates the trait is
/// straightforwardly implementable.
struct CountingMock {
    executes: Cell<u32>,
    starts: Cell<u32>,
    stops: Cell<u32>,
    exceptions: Cell<u32>,
}

impl CountingMock {
    fn new() -> Self {
        Self {
            executes: 0.into(),
            starts: 0.into(),
            stops: 0.into(),
            exceptions: 0.into(),
        }
    }
}

impl Telemetry for CountingMock {
    fn dispatch(&self, _: &[&'static str], _: &Measurements, _: &Metadata) {
        self.executes.set(self.executes.get() + 1);
    }
    fn span_start(&self, _: &[&'static str], _: &Metadata) -> u64 {
        let id = self.starts.get() as u64 + 1;
        self.starts.set(self.starts.get() + 1);
        id
    }
    fn span_stop(&self, _: &[&'static str], _: u64, _: u64, _: &Measurements, _: &Metadata) {
        self.stops.set(self.stops.get() + 1);
    }
    fn span_exception(&self, _: &[&'static str], _: u64, _: u64, _: &Measurements, _: &Metadata) {
        self.exceptions.set(self.exceptions.get() + 1);
    }
}

#[test]
fn mock_impl_records_execute_calls() {
    let m = CountingMock::new();
    m.event_lazy(&["fz", "x"], Metadata::new);
    m.event_lazy(&["fz", "y"], Metadata::new);
    assert_eq!(m.executes.get(), 2);
}

#[test]
fn lazy_event_does_not_construct_payload_without_matching_handler() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let constructed = Cell::new(0);

    tel.execute_lazy(&["fz", "compiler2", "event"], || {
        constructed.set(constructed.get() + 1);
        (Measurements::new(), Metadata::new())
    });

    assert_eq!(constructed.get(), 0);
}

#[test]
fn null_telemetry_does_not_construct_event_or_span_payloads() {
    let tel = NullTelemetry;
    let constructed = Cell::new(0);

    assert_eq!(std::mem::size_of_val(&tel), 0);

    tel.execute_lazy(&["fz", "compiler2", "event"], || {
        constructed.set(constructed.get() + 1);
        (Measurements::new(), Metadata::new())
    });
    let span = tel.span_lazy(&["fz", "compiler2", "span"], || {
        constructed.set(constructed.get() + 1);
        Metadata::new()
    });
    span.stop_with_lazy(|| {
        constructed.set(constructed.get() + 1);
        (Measurements::new(), Metadata::new())
    });

    assert_eq!(constructed.get(), 0);
}

#[test]
fn lazy_event_constructs_payload_only_for_matching_handler() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let cap = crate::telemetry::Capture::new();
    tel.attach(&["fz", "compiler2"], cap.handler());
    let constructed = Cell::new(0);

    tel.execute_lazy(&["fz", "compiler2", "event"], || {
        constructed.set(constructed.get() + 1);
        (Measurements::new(), Metadata::new())
    });

    assert_eq!(constructed.get(), 1);
    assert_eq!(cap.len(), 1);
}

#[test]
fn lazy_event_with_does_not_construct_handler_scoped_payload_without_matching_handler() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let constructed = Cell::new(0);

    tel.execute_lazy_with(&["fz", "compiler2", "event"], |_emit| {
        constructed.set(constructed.get() + 1);
    });

    assert_eq!(constructed.get(), 0);
}

#[test]
fn lazy_span_does_not_construct_metadata_without_matching_handler() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let constructed = Cell::new(0);

    let span = tel.span_lazy(&["fz", "compiler2", "span"], || {
        constructed.set(constructed.get() + 1);
        Metadata::new()
    });

    assert_eq!(constructed.get(), 0);
    assert_eq!(span.span_id(), 0);

    let cap = crate::telemetry::Capture::new();
    tel.attach(&["fz", "compiler2"], cap.handler());
    let active = tel.span_lazy(&["fz", "compiler2", "span"], Metadata::new);
    assert_eq!(active.span_id(), 1);
}

#[test]
fn disabled_span_does_not_construct_stop_payload() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let constructed = Cell::new(0);
    let span = tel.span_lazy(&["fz", "compiler2", "span"], Metadata::new);

    span.stop_with_lazy(|| {
        constructed.set(constructed.get() + 1);
        (Measurements::new(), Metadata::new())
    });

    assert_eq!(constructed.get(), 0);
}

#[test]
fn mock_assigns_increasing_span_ids() {
    let m = CountingMock::new();
    let a = m.span_start(&["fz", "x", "pass"], &Metadata::new());
    let b = m.span_start(&["fz", "y", "pass"], &Metadata::new());
    assert_eq!(a, 1);
    assert_eq!(b, 2);
    assert_eq!(m.starts.get(), 2);
}

// Richer recording mock for verifying Span's Drop semantics.
struct RecordingMock {
    next_id: Cell<u64>,
    records: RefCell<Vec<SpanRec>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SpanRec {
    Start { name: Vec<&'static str>, id: u64 },
    Stop { name: Vec<&'static str>, id: u64 },
    Exception { name: Vec<&'static str>, id: u64 },
}

impl RecordingMock {
    fn new() -> Self {
        Self {
            next_id: 1.into(),
            records: Vec::new().into(),
        }
    }
}

impl Telemetry for RecordingMock {
    fn dispatch(&self, _: &[&'static str], _: &Measurements, _: &Metadata) {}
    fn span_start(&self, name: &[&'static str], _: &Metadata) -> u64 {
        let id = self.next_id.get();
        self.next_id.set(id + 1);
        self.records.borrow_mut().push(SpanRec::Start {
            name: name.to_vec(),
            id,
        });
        id
    }
    fn span_stop(&self, name: &[&'static str], id: u64, _: u64, _: &Measurements, _: &Metadata) {
        self.records.borrow_mut().push(SpanRec::Stop {
            name: name.to_vec(),
            id,
        });
    }
    fn span_exception(&self, name: &[&'static str], id: u64, _: u64, _: &Measurements, _: &Metadata) {
        self.records.borrow_mut().push(SpanRec::Exception {
            name: name.to_vec(),
            id,
        });
    }
}

#[test]
fn span_drop_emits_stop_in_normal_path() {
    let m = RecordingMock::new();
    {
        let _s = m.span_lazy(&["fz", "lex", "pass"], Metadata::new);
    }
    let recs = m.records.borrow();
    assert_eq!(recs.len(), 2);
    assert!(matches!(recs[0], SpanRec::Start { id: 1, .. }));
    assert!(matches!(recs[1], SpanRec::Stop { id: 1, .. }));
}

#[test]
fn span_drop_emits_exception_when_unwinding() {
    let m = RecordingMock::new();
    let result = catch_unwind(AssertUnwindSafe(|| {
        let _s = m.span_lazy(&["fz", "x", "pass"], Metadata::new);
        panic!("boom");
    }));
    assert!(result.is_err());
    let recs = m.records.borrow();
    assert_eq!(recs.len(), 2);
    assert!(matches!(recs[0], SpanRec::Start { id: 1, .. }));
    assert!(matches!(recs[1], SpanRec::Exception { id: 1, .. }));
}

#[test]
fn nested_spans_get_distinct_ids_and_drop_lifo() {
    let m = RecordingMock::new();
    {
        let _outer = m.span_lazy(&["fz", "outer"], Metadata::new);
        {
            let _inner = m.span_lazy(&["fz", "outer", "inner"], Metadata::new);
        }
    }
    let recs = m.records.borrow();
    assert_eq!(recs.len(), 4);
    // Lifecycle: outer start, inner start, inner stop, outer stop.
    assert!(matches!(recs[0], SpanRec::Start { id: 1, .. }));
    assert!(matches!(recs[1], SpanRec::Start { id: 2, .. }));
    assert!(matches!(recs[2], SpanRec::Stop { id: 2, .. }));
    assert!(matches!(recs[3], SpanRec::Stop { id: 1, .. }));
}

#[test]
fn span_drop_reports_nonzero_elapsed_ns() {
    // Capture elapsed via a custom mock that grabs the duration.
    struct Capture {
        elapsed: Cell<u64>,
    }
    impl Telemetry for Capture {
        fn dispatch(&self, _: &[&'static str], _: &Measurements, _: &Metadata) {}
        fn span_start(&self, _: &[&'static str], _: &Metadata) -> u64 {
            42
        }
        fn span_stop(&self, _: &[&'static str], _: u64, ns: u64, _: &Measurements, _: &Metadata) {
            self.elapsed.set(ns);
        }
        fn span_exception(&self, _: &[&'static str], _: u64, _: u64, _: &Measurements, _: &Metadata) {}
    }

    let c = Capture { elapsed: 0.into() };
    {
        let _s = c.span_lazy(&["fz", "x"], Metadata::new);
        // Burn a small but reliable amount of time so elapsed > 0.
        sleep(Duration::from_micros(50));
    }
    assert!(c.elapsed.get() > 0, "expected nonzero elapsed_ns");
}

#[test]
fn span_stop_with_emits_borrowed_opaque_payload_once() {
    struct OutputMock {
        stops: Cell<u32>,
        outputs: RefCell<Option<Vec<u64>>>,
    }

    impl Telemetry for OutputMock {
        fn dispatch(&self, _: &[&'static str], _: &Measurements, _: &Metadata) {}

        fn span_start(&self, _: &[&'static str], _: &Metadata) -> u64 {
            1
        }

        fn span_stop(&self, _: &[&'static str], _: u64, _: u64, _: &Measurements, metadata: &Metadata) {
            self.stops.set(self.stops.get() + 1);
            let outputs = metadata
                .get("outputs")
                .and_then(|value| value.downcast_ref::<Vec<u64>>())
                .expect("outputs metadata should carry the borrowed vec");
            self.outputs.replace(Some(outputs.clone()));
        }

        fn span_exception(&self, _: &[&'static str], _: u64, _: u64, _: &Measurements, _: &Metadata) {}
    }

    let tel = OutputMock {
        stops: Cell::new(0),
        outputs: RefCell::new(None),
    };
    let outputs = vec![1_u64, 2, 3];

    {
        let span = tel.span_lazy(&["fz", "x"], Metadata::new);
        span.stop_with(
            &Measurements::new(),
            &crate::metadata! { outputs: crate::telemetry::opaque(&outputs) },
        );
    }

    assert_eq!(
        tel.stops.get(),
        1,
        "stop_with should suppress drop-time duplicate closes"
    );
    assert_eq!(
        tel.outputs.into_inner(),
        Some(vec![1, 2, 3]),
        "handlers should be able to copy the borrowed outputs payload"
    );
}
