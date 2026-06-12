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
    t.emit(&["fz", "x"]);
}

#[test]
fn ext_span_is_callable_through_dyn() {
    let bus = crate::telemetry::ConfiguredTelemetry::new();
    let t: &dyn Telemetry = &bus;
    let span = t.span(&["fz", "any", "pass"], metadata! { x: 1i64 });
    assert_eq!(span.span_id(), 1);
    assert_eq!(span.name(), &["fz", "any", "pass"]);
}

#[test]
fn ext_span_is_callable_through_concrete() {
    let t = crate::telemetry::ConfiguredTelemetry::new();
    let span = t.span(&["fz", "any", "pass"], Metadata::new());
    assert_eq!(span.span_id(), 1);
}

#[test]
fn dyn_telemetry_attach_and_detach_dispatch_to_configured_bus() {
    let bus = crate::telemetry::ConfiguredTelemetry::new();
    let t: &dyn Telemetry = &bus;
    let cap = crate::telemetry::Capture::new();

    let handler_id = t.attach(&["fz"], cap.handler());
    t.emit(&["fz", "x"]);
    assert_eq!(cap.len(), 1);
    assert!(t.detach(handler_id));
    t.emit(&["fz", "y"]);
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
    fn execute(&self, _: &[&'static str], _: &Measurements, _: &Metadata) {
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
    m.emit(&["fz", "x"]);
    m.emit(&["fz", "y"]);
    assert_eq!(m.executes.get(), 2);
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
    fn execute(&self, _: &[&'static str], _: &Measurements, _: &Metadata) {}
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
        let _s = m.span(&["fz", "lex", "pass"], Metadata::new());
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
        let _s = m.span(&["fz", "x", "pass"], Metadata::new());
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
        let _outer = m.span(&["fz", "outer"], Metadata::new());
        {
            let _inner = m.span(&["fz", "outer", "inner"], Metadata::new());
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
        fn execute(&self, _: &[&'static str], _: &Measurements, _: &Metadata) {}
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
        let _s = c.span(&["fz", "x"], Metadata::new());
        // Burn a small but reliable amount of time so elapsed > 0.
        sleep(Duration::from_micros(50));
    }
    assert!(c.elapsed.get() > 0, "expected nonzero elapsed_ns");
}

#[test]
fn span_close_with_attaches_payload_to_stop_event() {
    let bus = crate::telemetry::ConfiguredTelemetry::new();
    let cap = crate::telemetry::Capture::new();
    bus.attach(&[], cap.handler());

    {
        let mut span = bus.span(&["fz", "x"], Metadata::new());
        span.close_with(
            crate::measurements! { jobs_ran: 3u64 },
            crate::metadata! { outcome: "ok" },
        );
    }

    let stop = cap
        .events()
        .iter()
        .find(|event| matches!(event.kind, crate::telemetry::EventKind::SpanStop))
        .cloned()
        .expect("expected span stop event");
    assert!(matches!(
        stop.measurements.get("jobs_ran"),
        Some(crate::telemetry::Value::U64(3))
    ));
    assert!(matches!(
        stop.metadata.get("outcome"),
        Some(crate::telemetry::Value::Str(value)) if value.as_ref() == "ok"
    ));
}

#[test]
fn span_stop_with_emits_borrowed_opaque_payload_once() {
    struct OutputMock {
        stops: Cell<u32>,
        outputs: RefCell<Option<Vec<u64>>>,
    }

    impl Telemetry for OutputMock {
        fn execute(&self, _: &[&'static str], _: &Measurements, _: &Metadata) {}

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
        let span = tel.span(&["fz", "x"], Metadata::new());
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
