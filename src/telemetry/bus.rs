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

    fn attach(&self, prefix: &[&'static str], handler: Box<dyn Handler>) -> HandlerId {
        ConfiguredTelemetry::attach(self, prefix, handler)
    }

    fn detach(&self, id: HandlerId) -> bool {
        ConfiguredTelemetry::detach(self, id)
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
#[path = "bus_test.rs"]
mod bus_test;
