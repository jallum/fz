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
    fn span_stop(&self, _: &[&'static str], _: u64, _: u64) {
        self.stops.set(self.stops.get() + 1);
    }
    fn span_exception(&self, _: &[&'static str], _: u64, _: u64) {
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
    fn span_stop(&self, name: &[&'static str], id: u64, _: u64) {
        self.records.borrow_mut().push(SpanRec::Stop {
            name: name.to_vec(),
            id,
        });
    }
    fn span_exception(&self, name: &[&'static str], id: u64, _: u64) {
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
        fn span_stop(&self, _: &[&'static str], _: u64, ns: u64) {
            self.elapsed.set(ns);
        }
        fn span_exception(&self, _: &[&'static str], _: u64, _: u64) {}
    }

    let c = Capture { elapsed: 0.into() };
    {
        let _s = c.span(&["fz", "x"], Metadata::new());
        // Burn a small but reliable amount of time so elapsed > 0.
        sleep(Duration::from_micros(50));
    }
    assert!(c.elapsed.get() > 0, "expected nonzero elapsed_ns");
}
