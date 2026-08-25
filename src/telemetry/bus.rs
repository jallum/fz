//! The concrete `Telemetry` implementation: handler registry, prefix-based
//! routing, span stack, monotonic id counters.
//!
//! `ConfiguredTelemetry` is the impl the driver instantiates and hands by value
//! to the compiler. Handlers are attached at setup and observe every matching
//! event. Single-threaded by design — no `Send + Sync` bounds — each compiler
//! root owns its bus and lends it only to short-lived execution contexts.

use std::any::{Any, TypeId};
use std::cell::{Cell, RefCell};
use std::convert::Infallible;

use crate::measurements;

use super::event::{Measurements, Metadata};
use super::handler::{Event, EventKind, Handler, HandlerId};
use super::sink::{RawSpanTelemetry, Span, Telemetry};

struct Entry {
    id: HandlerId,
    prefix: Vec<&'static str>,
    handler: Box<dyn Handler>,
}

#[cfg(test)]
type Event0 = dyn Fn(&[&'static str], u64, u64);
type Event1 = dyn Fn(&[&'static str], u64, u64, &dyn Any);
type Event2 = dyn Fn(&[&'static str], u64, u64, &dyn Any, &dyn Any);
type Event3 = dyn Fn(&[&'static str], u64, u64, &dyn Any, &dyn Any, &dyn Any);
type Event4 = dyn Fn(&[&'static str], u64, u64, &dyn Any, &dyn Any, &dyn Any, &dyn Any);
type Span0 = dyn Fn(&[&'static str], u64, u64);
type Span1 = dyn Fn(&[&'static str], u64, u64, &dyn Any);
type Span2 = dyn Fn(&[&'static str], u64, u64, &dyn Any, &dyn Any);
type SpanStop0 = dyn Fn(&[&'static str], u64, u64, u64);
type SpanStop1 = dyn Fn(&[&'static str], u64, u64, u64, &dyn Any);
type SpanStop2 = dyn Fn(&[&'static str], u64, u64, u64, &dyn Any, &dyn Any);

enum RawEventCallback {
    #[cfg(test)]
    Zero(Box<Event0>),
    One(Box<Event1>),
    Two(Box<Event2>),
    Three(Box<Event3>),
    Four(Box<Event4>),
}

struct RawEventEntry {
    id: HandlerId,
    prefix: Vec<&'static str>,
    callback: RawEventCallback,
}

type RawLifecycleCallback = dyn Fn(&[&'static str], EventKind, u64, u64, Option<u64>);

struct RawLifecycleEntry {
    id: HandlerId,
    prefix: Vec<&'static str>,
    callback: Box<RawLifecycleCallback>,
}

enum RawSpanStart {
    Zero(Box<Span0>),
    One(Box<Span1>),
    Two(Box<Span2>),
}

enum RawSpanStop {
    Zero(Box<SpanStop0>),
    One(Box<SpanStop1>),
    Two(Box<SpanStop2>),
}

struct RawSpanEntry {
    id: HandlerId,
    prefix: Vec<&'static str>,
    start_1: TypeId,
    start_2: TypeId,
    stop_1: TypeId,
    stop_2: TypeId,
    start: RawSpanStart,
    stop: RawSpanStop,
    exception: Box<SpanStop0>,
}

macro_rules! attach_raw_event {
    ($method:ident, $variant:ident $(, $ty:ident $arg:ident)*) => {
        pub fn $method<$($ty: Any,)* F>(&self, prefix: &[&'static str], handler: F) -> HandlerId
        where
            F: Fn(&[&'static str], u64, u64, $(&$ty),*) + 'static,
        {
            self.attach_raw_event(
                prefix,
                RawEventCallback::$variant(Box::new(move |name, span_id, parent_span_id, $($arg),*| {
                    $(let Some($arg) = $arg.downcast_ref::<$ty>() else { return; };)*
                    handler(name, span_id, parent_span_id, $($arg),*);
                })),
            )
        }
    };
}

macro_rules! attach_raw_span {
    (
        $method:ident,
        [$($ty:ident),*],
        $start_variant:ident [$($start_ty:ident $start_arg:ident),*],
        $stop_variant:ident [$($stop_ty:ident $stop_arg:ident),*],
        $s1:ty, $s2:ty, $p1:ty, $p2:ty
    ) => {
        pub fn $method<$($ty: Any,)* FS, FP, FE>(
            &self,
            prefix: &[&'static str],
            start: FS,
            stop: FP,
            exception: FE,
        ) -> HandlerId
        where
            FS: Fn(&[&'static str], u64, u64, $(&$start_ty),*) + 'static,
            FP: Fn(&[&'static str], u64, u64, u64, $(&$stop_ty),*) + 'static,
            FE: Fn(&[&'static str], u64, u64, u64) + 'static,
        {
            self.attach_raw_span(
                prefix,
                TypeId::of::<$s1>(),
                TypeId::of::<$s2>(),
                TypeId::of::<$p1>(),
                TypeId::of::<$p2>(),
                RawSpanStart::$start_variant(Box::new(move |name, span_id, parent_span_id, $($start_arg),*| {
                    $(let $start_arg = $start_arg.downcast_ref::<$start_ty>().expect("matched raw span start type");)*
                    start(name, span_id, parent_span_id, $($start_arg),*);
                })),
                RawSpanStop::$stop_variant(Box::new(move |name, span_id, parent_span_id, elapsed_ns, $($stop_arg),*| {
                    $(let $stop_arg = $stop_arg.downcast_ref::<$stop_ty>().expect("matched raw span stop type");)*
                    stop(name, span_id, parent_span_id, elapsed_ns, $($stop_arg),*);
                })),
                Box::new(exception),
            )
        }
    };
}

macro_rules! dispatch_raw_event {
    ($method:ident, $variant:ident $(, $arg:ident)*) => {
        fn $method(&self, name: &[&'static str], $($arg: &dyn Any),*) {
            let (span_id, parent_span_id) = self.current_span_ids();
            for entry in self.raw_events.borrow().iter() {
                if name.starts_with(&entry.prefix) {
                    if let RawEventCallback::$variant(callback) = &entry.callback {
                        callback(name, span_id, parent_span_id, $($arg),*);
                    }
                }
            }
            self.dispatch_raw_lifecycle(name, EventKind::Event, span_id, parent_span_id, None);
        }
    };
}

macro_rules! dispatch_raw_span_start {
    ($method:ident, $variant:ident $(, $arg:ident)*) => {
        fn $method(
            &self,
            name: &[&'static str],
            start_1: TypeId,
            start_2: TypeId,
            stop_1: TypeId,
            stop_2: TypeId,
            $($arg: &dyn Any),*
        ) -> u64 {
            let has_typed_handler = self.raw_spans.borrow().iter().any(|entry| {
                entry.matches(name, start_1, start_2, stop_1, stop_2)
                    && matches!(entry.start, RawSpanStart::$variant(_))
            });
            if !has_typed_handler && !self.raw_lifecycle_enables_span(name) {
                return 0;
            }
            let (span_id, parent_span_id) = self.begin_span();
            if has_typed_handler {
                for entry in self.raw_spans.borrow().iter() {
                    if entry.matches(name, start_1, start_2, stop_1, stop_2) {
                        if let RawSpanStart::$variant(callback) = &entry.start {
                            callback(name, span_id, parent_span_id, $($arg),*);
                        }
                    }
                }
            }
            self.dispatch_raw_lifecycle(name, EventKind::SpanStart, span_id, parent_span_id, None);
            span_id
        }
    };
}

macro_rules! dispatch_raw_span_stop {
    ($method:ident, $variant:ident $(, $arg:ident)*) => {
        fn $method(
            &self,
            name: &[&'static str],
            span_id: u64,
            elapsed_ns: u64,
            start_1: TypeId,
            start_2: TypeId,
            stop_1: TypeId,
            stop_2: TypeId,
            $($arg: &dyn Any),*
        ) {
            let parent_span_id = self.span_parent(span_id);
            for entry in self.raw_spans.borrow().iter() {
                if entry.matches(name, start_1, start_2, stop_1, stop_2) {
                    if let RawSpanStop::$variant(callback) = &entry.stop {
                        callback(name, span_id, parent_span_id, elapsed_ns, $($arg),*);
                    }
                }
            }
            self.dispatch_raw_lifecycle(
                name,
                EventKind::SpanStop,
                span_id,
                parent_span_id,
                Some(elapsed_ns),
            );
            self.finish_span(span_id);
        }
    };
}

macro_rules! forward_raw_event {
    ($method:ident $(, $arg:ident)*) => {
        fn $method(&self, name: &[&'static str], $($arg: &dyn Any),*) {
            ConfiguredTelemetry::$method(self, name, $($arg),*);
        }
    };
}

macro_rules! forward_raw_span_start {
    ($method:ident $(, $arg:ident)*) => {
        fn $method(
            &self,
            name: &[&'static str],
            start_1: TypeId,
            start_2: TypeId,
            stop_1: TypeId,
            stop_2: TypeId,
            $($arg: &dyn Any),*
        ) -> u64 {
            ConfiguredTelemetry::$method(self, name, start_1, start_2, stop_1, stop_2, $($arg),*)
        }
    };
}

macro_rules! forward_raw_span_stop {
    ($method:ident $(, $arg:ident)*) => {
        fn $method(
            &self,
            name: &[&'static str],
            span_id: u64,
            elapsed_ns: u64,
            start_1: TypeId,
            start_2: TypeId,
            stop_1: TypeId,
            stop_2: TypeId,
            $($arg: &dyn Any),*
        ) {
            ConfiguredTelemetry::$method(
                self, name, span_id, elapsed_ns, start_1, start_2, stop_1, stop_2, $($arg),*
            );
        }
    };
}

fn remove_entry<T>(entries: &mut Vec<T>, id: HandlerId, entry_id: impl Fn(&T) -> HandlerId) -> bool {
    if let Some(position) = entries.iter().position(|entry| entry_id(entry) == id) {
        entries.remove(position);
        true
    } else {
        false
    }
}

impl RawSpanEntry {
    fn matches(&self, name: &[&'static str], start_1: TypeId, start_2: TypeId, stop_1: TypeId, stop_2: TypeId) -> bool {
        name.starts_with(&self.prefix)
            && self.start_1 == start_1
            && self.start_2 == start_2
            && self.stop_1 == stop_1
            && self.stop_2 == stop_2
    }
}

pub struct ConfiguredTelemetry {
    handlers: RefCell<Vec<Entry>>,
    raw_events: RefCell<Vec<RawEventEntry>>,
    raw_spans: RefCell<Vec<RawSpanEntry>>,
    raw_lifecycle: RefCell<Vec<RawLifecycleEntry>>,
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
            raw_events: RefCell::new(Vec::new()),
            raw_spans: RefCell::new(Vec::new()),
            raw_lifecycle: RefCell::new(Vec::new()),
            next_handler_id: Cell::new(1),
            next_span_id: Cell::new(1),
            span_stack: RefCell::new(Vec::new()),
        }
    }

    /// Attach `handler` to events whose name starts with `prefix`.
    /// The empty prefix `&[]` matches everything. Returns the id for
    /// later detach.
    pub fn attach(&self, prefix: &[&'static str], handler: Box<dyn Handler>) -> HandlerId {
        let id = self.next_id();
        self.handlers.borrow_mut().push(Entry {
            id,
            prefix: prefix.to_vec(),
            handler,
        });
        id
    }

    fn attach_raw_event(&self, prefix: &[&'static str], callback: RawEventCallback) -> HandlerId {
        let id = self.next_id();
        self.raw_events.borrow_mut().push(RawEventEntry {
            id,
            prefix: prefix.to_vec(),
            callback,
        });
        id
    }

    #[cfg(test)]
    attach_raw_event!(attach_raw_event0, Zero);
    attach_raw_event!(attach_raw_event1, One, A a);
    attach_raw_event!(attach_raw_event2, Two, A a, B b);
    attach_raw_event!(attach_raw_event3, Three, A a, B b, C c);
    attach_raw_event!(attach_raw_event4, Four, A a, B b, C c, D d);

    pub fn attach_raw_lifecycle<F>(&self, prefix: &[&'static str], handler: F) -> HandlerId
    where
        F: Fn(&[&'static str], EventKind, u64, u64, Option<u64>) + 'static,
    {
        let id = self.next_id();
        self.raw_lifecycle.borrow_mut().push(RawLifecycleEntry {
            id,
            prefix: prefix.to_vec(),
            callback: Box::new(handler),
        });
        id
    }

    fn attach_raw_span(
        &self,
        prefix: &[&'static str],
        start_1: TypeId,
        start_2: TypeId,
        stop_1: TypeId,
        stop_2: TypeId,
        start: RawSpanStart,
        stop: RawSpanStop,
        exception: Box<SpanStop0>,
    ) -> HandlerId {
        let id = self.next_id();
        self.raw_spans.borrow_mut().push(RawSpanEntry {
            id,
            prefix: prefix.to_vec(),
            start_1,
            start_2,
            stop_1,
            stop_2,
            start,
            stop,
            exception,
        });
        id
    }

    #[cfg(test)]
    attach_raw_span!(attach_raw_span0_0, [], Zero [], Zero [], Infallible, Infallible, Infallible, Infallible);
    attach_raw_span!(attach_raw_span0_1, [P1], Zero [], One [P1 p1], Infallible, Infallible, P1, Infallible);
    attach_raw_span!(attach_raw_span1_0, [S1], One [S1 s1], Zero [], S1, Infallible, Infallible, Infallible);
    attach_raw_span!(attach_raw_span1_1, [S1, P1], One [S1 s1], One [P1 p1], S1, Infallible, P1, Infallible);
    attach_raw_span!(attach_raw_span1_2, [S1, P1, P2], One [S1 s1], Two [P1 p1, P2 p2], S1, Infallible, P1, P2);
    attach_raw_span!(attach_raw_span2_0, [S1, S2], Two [S1 s1, S2 s2], Zero [], S1, S2, Infallible, Infallible);

    /// Remove a previously attached handler. Returns true if removed.
    pub fn detach(&self, id: HandlerId) -> bool {
        remove_entry(&mut self.handlers.borrow_mut(), id, |entry| entry.id)
            || remove_entry(&mut self.raw_events.borrow_mut(), id, |entry| entry.id)
            || remove_entry(&mut self.raw_spans.borrow_mut(), id, |entry| entry.id)
            || remove_entry(&mut self.raw_lifecycle.borrow_mut(), id, |entry| entry.id)
    }

    /// Number of currently attached handlers. Test/diagnostic helper.
    #[cfg(test)]
    pub fn handler_count(&self) -> usize {
        self.handlers.borrow().len()
            + self.raw_events.borrow().len()
            + self.raw_spans.borrow().len()
            + self.raw_lifecycle.borrow().len()
    }

    fn next_id(&self) -> HandlerId {
        let id = HandlerId(self.next_handler_id.get());
        self.next_handler_id.set(id.0 + 1);
        id
    }

    fn current_span_ids(&self) -> (u64, u64) {
        let s = self.span_stack.borrow();
        match s.len() {
            0 => (0, 0),
            1 => (s[0], 0),
            n => (s[n - 1], s[n - 2]),
        }
    }

    fn begin_span(&self) -> (u64, u64) {
        let id = self.next_span_id.get();
        self.next_span_id.set(id + 1);
        let parent_id = self.span_stack.borrow().last().copied().unwrap_or(0);
        self.span_stack.borrow_mut().push(id);
        (id, parent_id)
    }

    fn span_parent(&self, span_id: u64) -> u64 {
        let spans = self.span_stack.borrow();
        spans
            .iter()
            .rposition(|&id| id == span_id)
            .and_then(|position| (position > 0).then(|| spans[position - 1]))
            .unwrap_or(0)
    }

    fn finish_span(&self, span_id: u64) {
        let position = self.span_stack.borrow().iter().rposition(|&id| id == span_id);
        if let Some(position) = position {
            self.span_stack.borrow_mut().remove(position);
        }
    }

    fn raw_lifecycle_enables_span(&self, name: &[&'static str]) -> bool {
        self.raw_lifecycle
            .borrow()
            .iter()
            .any(|entry| name.starts_with(&entry.prefix) || entry.prefix.starts_with(name))
    }

    fn dispatch_raw_lifecycle(
        &self,
        name: &[&'static str],
        kind: EventKind,
        span_id: u64,
        parent_span_id: u64,
        elapsed_ns: Option<u64>,
    ) {
        for entry in self.raw_lifecycle.borrow().iter() {
            if name.starts_with(&entry.prefix) {
                (entry.callback)(name, kind, span_id, parent_span_id, elapsed_ns);
            }
        }
    }

    #[cfg(test)]
    dispatch_raw_event!(dispatch_raw_event0, Zero);
    dispatch_raw_event!(dispatch_raw_event1, One, a);
    dispatch_raw_event!(dispatch_raw_event2, Two, a, b);
    dispatch_raw_event!(dispatch_raw_event3, Three, a, b, c);
    dispatch_raw_event!(dispatch_raw_event4, Four, a, b, c, d);

    dispatch_raw_span_start!(start_raw_span0, Zero);
    dispatch_raw_span_start!(start_raw_span1, One, a);
    dispatch_raw_span_start!(start_raw_span2, Two, a, b);

    dispatch_raw_span_stop!(stop_raw_span0, Zero);
    dispatch_raw_span_stop!(stop_raw_span1, One, a);
    dispatch_raw_span_stop!(stop_raw_span2, Two, a, b);

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
    fn is_enabled(&self, name: &[&'static str]) -> bool {
        self.handlers
            .borrow()
            .iter()
            .any(|entry| name.starts_with(&entry.prefix))
    }

    fn is_span_enabled(&self, name: &[&'static str]) -> bool {
        self.handlers
            .borrow()
            .iter()
            .any(|entry| name.starts_with(&entry.prefix) || entry.prefix.starts_with(name))
    }

    fn dispatch(&self, name: &[&'static str], measurements: &Measurements, metadata: &Metadata) {
        let (span_id, parent_span_id) = self.current_span_ids();
        self.dispatch(name, EventKind::Event, measurements, metadata, span_id, parent_span_id);
    }

    fn span_start(&self, name: &[&'static str], metadata: &Metadata) -> u64 {
        let (id, parent_id) = self.begin_span();
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

    fn span_stop(
        &self,
        name: &[&'static str],
        span_id: u64,
        elapsed_ns: u64,
        measurements: &Measurements,
        metadata: &Metadata,
    ) {
        self.close_span(name, span_id, elapsed_ns, measurements, metadata, EventKind::SpanStop);
    }

    fn span_exception(
        &self,
        name: &[&'static str],
        span_id: u64,
        elapsed_ns: u64,
        measurements: &Measurements,
        metadata: &Metadata,
    ) {
        self.close_span(
            name,
            span_id,
            elapsed_ns,
            measurements,
            metadata,
            EventKind::SpanException,
        );
    }

    fn attach(&self, prefix: &[&'static str], handler: Box<dyn Handler>) -> HandlerId {
        ConfiguredTelemetry::attach(self, prefix, handler)
    }

    fn detach(&self, id: HandlerId) -> bool {
        ConfiguredTelemetry::detach(self, id)
    }

    #[cfg(test)]
    forward_raw_event!(dispatch_raw_event0);
    forward_raw_event!(dispatch_raw_event1, a);
    forward_raw_event!(dispatch_raw_event2, a, b);
    forward_raw_event!(dispatch_raw_event3, a, b, c);
    forward_raw_event!(dispatch_raw_event4, a, b, c, d);

    forward_raw_span_start!(start_raw_span0);
    forward_raw_span_start!(start_raw_span1, a);
    forward_raw_span_start!(start_raw_span2, a, b);

    forward_raw_span_stop!(stop_raw_span0);
    forward_raw_span_stop!(stop_raw_span1, a);
    forward_raw_span_stop!(stop_raw_span2, a, b);

    fn exception_raw_span(
        &self,
        name: &[&'static str],
        span_id: u64,
        elapsed_ns: u64,
        start_1: TypeId,
        start_2: TypeId,
        stop_1: TypeId,
        stop_2: TypeId,
    ) {
        let parent_span_id = self.span_parent(span_id);
        for entry in self.raw_spans.borrow().iter() {
            if entry.matches(name, start_1, start_2, stop_1, stop_2) {
                (entry.exception)(name, span_id, parent_span_id, elapsed_ns);
            }
        }
        self.dispatch_raw_lifecycle(
            name,
            EventKind::SpanException,
            span_id,
            parent_span_id,
            Some(elapsed_ns),
        );
        self.finish_span(span_id);
    }
}

impl RawSpanTelemetry for ConfiguredTelemetry {
    type Span0_0<'a>
        = Span<'a, Self>
    where
        Self: 'a;
    type Span0_1<'a, P1: Any>
        = Span<'a, Self, Infallible, Infallible, P1>
    where
        Self: 'a;
    type Span1_0<'a, S1: Any>
        = Span<'a, Self, S1>
    where
        Self: 'a;
    type Span1_1<'a, S1: Any, P1: Any>
        = Span<'a, Self, S1, Infallible, P1>
    where
        Self: 'a;
    type Span1_2<'a, S1: Any, P1: Any, P2: Any>
        = Span<'a, Self, S1, Infallible, P1, P2>
    where
        Self: 'a;
    type Span2_0<'a, S1: Any, S2: Any>
        = Span<'a, Self, S1, S2>
    where
        Self: 'a;

    #[inline(always)]
    fn make_span0_0<'a>(&'a self, name: &'a [&'static str], span_id: u64) -> Self::Span0_0<'a> {
        Span::new_raw(self, name, span_id)
    }

    #[inline(always)]
    fn make_span0_1<'a, P1: Any>(&'a self, name: &'a [&'static str], span_id: u64) -> Self::Span0_1<'a, P1> {
        Span::new_raw(self, name, span_id)
    }

    #[inline(always)]
    fn make_span1_0<'a, S1: Any>(&'a self, name: &'a [&'static str], span_id: u64) -> Self::Span1_0<'a, S1> {
        Span::new_raw(self, name, span_id)
    }

    #[inline(always)]
    fn make_span1_1<'a, S1: Any, P1: Any>(
        &'a self,
        name: &'a [&'static str],
        span_id: u64,
    ) -> Self::Span1_1<'a, S1, P1> {
        Span::new_raw(self, name, span_id)
    }

    #[inline(always)]
    fn make_span1_2<'a, S1: Any, P1: Any, P2: Any>(
        &'a self,
        name: &'a [&'static str],
        span_id: u64,
    ) -> Self::Span1_2<'a, S1, P1, P2> {
        Span::new_raw(self, name, span_id)
    }

    #[inline(always)]
    fn make_span2_0<'a, S1: Any, S2: Any>(
        &'a self,
        name: &'a [&'static str],
        span_id: u64,
    ) -> Self::Span2_0<'a, S1, S2> {
        Span::new_raw(self, name, span_id)
    }
}

impl ConfiguredTelemetry {
    fn close_span(
        &self,
        name: &[&'static str],
        span_id: u64,
        elapsed_ns: u64,
        measurements: &Measurements,
        metadata: &Metadata,
        kind: EventKind,
    ) {
        let parent_id = self.span_parent(span_id);
        let mut m = measurements! { elapsed_ns: elapsed_ns };
        m.0.extend(measurements.iter().cloned());
        self.dispatch(name, kind, &m, metadata, span_id, parent_id);
        self.finish_span(span_id);
    }
}

#[cfg(test)]
#[path = "bus_test.rs"]
mod bus_test;
