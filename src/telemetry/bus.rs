//! The concrete `Telemetry` implementation: handler registry, prefix-based
//! routing, span stack, monotonic id counters.
//!
//! `ConfiguredTelemetry` is the impl the driver instantiates and threads
//! through the compiler as `&dyn Telemetry`. Handlers are attached at setup
//! and observe every matching event. Single-threaded by design — no
//! `Send + Sync` bounds — the test harness and CLI driver each own their
//! own bus.

use std::cell::{Cell, RefCell};

use crate::measurements;

use super::event::{Measurements, Metadata};
use super::handler::{Event, EventKind, Handler, HandlerId};
use super::sink::Telemetry;

struct Entry {
    #[cfg(test)]
    id: HandlerId,
    prefix: Vec<&'static str>,
    handler: Box<dyn Handler>,
}

pub struct ConfiguredTelemetry {
    handlers: RefCell<Vec<Entry>>,
    next_handler_id: Cell<u64>,
    next_span_id: Cell<u64>,
    /// Stack of open span ids — used to populate `span_id` and
    /// `parent_span_id` on every event emitted while spans are open.
    span_stack: RefCell<Vec<u64>>,
}

impl ConfiguredTelemetry {
    pub fn new() -> Self {
        Self {
            handlers: RefCell::new(Vec::new()),
            next_handler_id: Cell::new(1),
            next_span_id: Cell::new(1),
            span_stack: RefCell::new(Vec::new()),
        }
    }

    /// Attach `handler` to events whose name starts with `prefix`.
    /// The empty prefix `&[]` matches everything. Returns the id for
    /// later detach.
    pub fn attach(&self, prefix: &[&'static str], handler: Box<dyn Handler>) -> HandlerId {
        let id = HandlerId(self.next_handler_id.get());
        self.next_handler_id.set(id.0 + 1);
        self.handlers.borrow_mut().push(Entry {
            #[cfg(test)]
            id,
            prefix: prefix.to_vec(),
            handler,
        });
        id
    }

    /// Remove a previously attached handler. Returns true if removed.
    #[cfg(test)]
    pub fn detach(&self, id: HandlerId) -> bool {
        let mut h = self.handlers.borrow_mut();
        if let Some(pos) = h.iter().position(|e| e.id == id) {
            h.remove(pos);
            true
        } else {
            false
        }
    }

    /// Number of currently attached handlers. Test/diagnostic helper.
    #[cfg(test)]
    pub fn handler_count(&self) -> usize {
        self.handlers.borrow().len()
    }

    fn current_span_ids(&self) -> (u64, u64) {
        let s = self.span_stack.borrow();
        match s.len() {
            0 => (0, 0),
            1 => (s[0], 0),
            n => (s[n - 1], s[n - 2]),
        }
    }

    fn dispatch<'ev, 'meas, 'meta>(
        &self,
        name: &'ev [&'static str],
        kind: EventKind,
        measurements: &'ev Measurements<'meas>,
        metadata: &'ev Metadata<'meta>,
        span_id: u64,
        parent_span_id: u64,
    ) {
        let ev = Event {
            name,
            kind,
            measurements,
            metadata,
            span_id,
            parent_span_id,
        };
        // Handlers borrow immutably while dispatching. A handler that
        // attaches/detaches mid-dispatch would re-borrow mutably and panic;
        // that's a programmer error, not a runtime case to defend against.
        let h = self.handlers.borrow();
        for entry in h.iter() {
            if name.starts_with(&entry.prefix) {
                entry.handler.handle(&ev);
            }
        }
    }
}

impl Default for ConfiguredTelemetry {
    fn default() -> Self {
        Self::new()
    }
}

impl Telemetry for ConfiguredTelemetry {
    fn execute(&self, name: &[&'static str], measurements: &Measurements, metadata: &Metadata) {
        let (span_id, parent_span_id) = self.current_span_ids();
        self.dispatch(name, EventKind::Event, measurements, metadata, span_id, parent_span_id);
    }

    fn span_start(&self, name: &[&'static str], metadata: &Metadata) -> u64 {
        let id = self.next_span_id.get();
        self.next_span_id.set(id + 1);
        // Parent is the current top before we push.
        let parent_id = self.span_stack.borrow().last().copied().unwrap_or(0);
        self.span_stack.borrow_mut().push(id);
        self.dispatch(
            name,
            EventKind::SpanStart,
            &Measurements::new(),
            metadata,
            id,
            parent_id,
        );
        id
    }

    fn span_stop(&self, name: &[&'static str], span_id: u64, elapsed_ns: u64) {
        self.close_span(name, span_id, elapsed_ns, EventKind::SpanStop);
    }

    fn span_exception(&self, name: &[&'static str], span_id: u64, elapsed_ns: u64) {
        self.close_span(name, span_id, elapsed_ns, EventKind::SpanException);
    }
}

impl ConfiguredTelemetry {
    fn close_span(&self, name: &[&'static str], span_id: u64, elapsed_ns: u64, kind: EventKind) {
        let parent_id = {
            let s = self.span_stack.borrow();
            // Walk from the top to find the one being closed. Spans drop
            // LIFO so it should be the top, but if a panic unwinds multiple
            // layers we tolerate any position.
            let pos = s.iter().rposition(|&x| x == span_id);
            pos.and_then(|i| (i > 0).then(|| s[i - 1])).unwrap_or(0)
        };
        let m = measurements! { elapsed_ns: elapsed_ns };
        self.dispatch(name, kind, &m, &Metadata::new(), span_id, parent_id);
        // Pop after dispatch so within-handler peeks at the stack still
        // see the span as "open." Bind the position first so the
        // immutable borrow is released before borrow_mut.
        let pos = self.span_stack.borrow().iter().rposition(|&x| x == span_id);
        if let Some(pos) = pos {
            self.span_stack.borrow_mut().remove(pos);
        }
    }
}

#[cfg(test)]
mod tests {
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
}
