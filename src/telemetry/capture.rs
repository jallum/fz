//! Test-facing handler that captures every event into an owned buffer.
//!
//! Tests construct a `Capture`, attach it to their `ConfiguredTelemetry`,
//! drive the code under test, then query the captured stream for assertions:
//!
//! ```ignore
//! let tel = ConfiguredTelemetry::new();
//! let cap = Capture::new();
//! tel.attach(&[], cap.handler());
//! run_pass(&tel);
//! assert_eq!(cap.count(&["fz", "ir_lower", "matcher_built"]), 3);
//! ```
//!
//! The whole compiler is observable through this seam — no `#[cfg(test)] pub`
//! peeking into pass internals.

use std::cell::{Ref, RefCell};
use std::io::Write;
use std::rc::Rc;

use super::event::{Measurements, Metadata};
use super::handler::{Event, EventKind, Handler};

/// One captured event in fully-owned form. Constructed by `Capture` from
/// each borrowed `Event` it sees.
#[derive(Debug, Clone)]
pub struct OwnedEvent {
    pub name: Vec<&'static str>,
    pub kind: EventKind,
    pub measurements: Measurements<'static>,
    pub metadata: Metadata<'static>,
    pub span_id: u64,
    pub parent_span_id: u64,
}

impl OwnedEvent {
    fn from_borrowed(ev: &Event<'_, '_, '_>) -> Self {
        Self {
            name: ev.name.to_vec(),
            kind: ev.kind,
            measurements: ev.measurements.durable_owned(),
            metadata: ev.metadata.durable_owned(),
            span_id: ev.span_id,
            parent_span_id: ev.parent_span_id,
        }
    }
}

/// Captures the event stream for test inspection. Cheap to construct;
/// `handler()` yields a handler that shares the same underlying buffer,
/// so the test holds the `Capture` and attaches the handler to the bus.
pub struct Capture {
    events: Rc<RefCell<Vec<OwnedEvent>>>,
}

impl Capture {
    pub fn new() -> Self {
        Self {
            events: Rc::new(RefCell::new(Vec::new())),
        }
    }

    /// Returns a handler that, when attached to a `ConfiguredTelemetry`,
    /// records every matching event into this capture's buffer.
    pub fn handler(&self) -> Box<dyn Handler> {
        Box::new(CaptureHandler {
            events: self.events.clone(),
        })
    }

    /// Borrow the full event stream.
    #[cfg(test)]
    pub fn events(&self) -> Ref<'_, Vec<OwnedEvent>> {
        self.events.borrow()
    }

    /// Total number of captured events.
    pub fn len(&self) -> usize {
        self.events.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.events.borrow().is_empty()
    }

    /// Forget every captured event so far. Lets a single test drive
    /// multiple scenarios against the same capture instance.
    pub fn clear(&self) {
        self.events.borrow_mut().clear();
    }

    /// Number of events whose name matches `name` exactly.
    pub fn count(&self, name: &[&str]) -> usize {
        self.events.borrow().iter().filter(|ev| ev.name == name).count()
    }

    /// Owned snapshots of events whose name starts with `prefix`. The
    /// empty prefix `&[]` returns everything.
    pub fn find(&self, prefix: &[&str]) -> Vec<OwnedEvent> {
        self.events
            .borrow()
            .iter()
            .filter(|ev| ev.name.starts_with(prefix))
            .cloned()
            .collect()
    }

    /// The most recently captured event with the given exact name.
    pub fn last(&self, name: &[&str]) -> Option<OwnedEvent> {
        self.events.borrow().iter().rev().find(|ev| ev.name == name).cloned()
    }

    /// True if any captured event matches `name`.
    pub fn contains(&self, name: &[&str]) -> bool {
        self.count(name) > 0
    }

    /// Count events by `kind`. Useful for "no errors emitted" assertions.
    pub fn count_by_kind(&self, kind: EventKind) -> usize {
        self.events.borrow().iter().filter(|ev| ev.kind == kind).count()
    }
}

impl Default for Capture {
    fn default() -> Self {
        Self::new()
    }
}

struct CaptureHandler {
    events: Rc<RefCell<Vec<OwnedEvent>>>,
}

impl Handler for CaptureHandler {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        self.events.borrow_mut().push(OwnedEvent::from_borrowed(ev));
    }
}

/// Shared test utility: returns a `(buf, writer)` pair where `writer` is a
/// `Box<dyn Write + 'static>` that appends to `buf`. Use wherever tests need
/// a capturable `Write` sink (JsonlBackend, DiagRenderer, etc.).
pub fn vec_writer() -> (Rc<RefCell<Vec<u8>>>, Box<dyn Write>) {
    let buf: Rc<RefCell<Vec<u8>>> = Rc::new(RefCell::new(Vec::new()));
    struct W(Rc<RefCell<Vec<u8>>>);
    impl Write for W {
        fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
            self.0.borrow_mut().extend_from_slice(data);
            Ok(data.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    (buf.clone(), Box::new(W(buf)))
}

#[cfg(test)]
mod tests {
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
}
