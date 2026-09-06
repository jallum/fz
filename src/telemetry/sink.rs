//! The `Telemetry` trait — the compiler-facing observability surface.
//!
//! Compiler code preserves the concrete sink type through the object-safe event
//! surface and the associated raw-span guard capability. Legacy payload methods
//! remain for tests and compatibility emitters.

use std::any::{Any, TypeId};
use std::convert::Infallible;
use std::marker::PhantomData;
use std::thread::panicking;
use std::time::Instant;

use super::event::{Measurements, Metadata};
use super::handler::{Handler, HandlerId};

macro_rules! raw_event_core {
    ($method:ident $(, $arg:ident)*) => {
        fn $method(&self, _name: &[&'static str], $($arg: &dyn Any),*) {}
    };
}

macro_rules! raw_span_start_core {
    ($method:ident $(, $arg:ident)*) => {
        fn $method(
            &self,
            _name: &[&'static str],
            _start_1: TypeId,
            _start_2: TypeId,
            _stop_1: TypeId,
            _stop_2: TypeId,
            $($arg: &dyn Any),*
        ) -> u64 {
            0
        }
    };
}

macro_rules! raw_span_stop_core {
    ($method:ident $(, $arg:ident)*) => {
        fn $method(
            &self,
            _name: &[&'static str],
            _span_id: u64,
            _elapsed_ns: u64,
            _start_1: TypeId,
            _start_2: TypeId,
            _stop_1: TypeId,
            _stop_2: TypeId,
            $($arg: &dyn Any),*
        ) {
        }
    };
}

/// The compiler's observability bus. Every observable thing the compiler
/// does — diagnostics, stats, and span boundaries — flows
/// through one of these methods.
///
/// Fatal errors are *not* on this trait; they stay on `Result<T, FatalError>`.
/// Telemetry is purely the side channel.
pub trait Telemetry {
    /// Returns whether at least one handler will observe an event at `name`.
    fn is_enabled(&self, _name: &[&'static str]) -> bool {
        true
    }

    fn is_span_enabled(&self, name: &[&'static str]) -> bool {
        self.is_enabled(name)
    }

    /// Returns whether a typed raw-event or raw-lifecycle subscriber observes `name`.
    fn is_raw_event_enabled(&self, name: &[&'static str]) -> bool {
        self.is_enabled(name)
    }

    /// Emit a single event. `name` is the hierarchical path
    /// (e.g. `&["fz", "lexer", "tokens_built"]`); `measurements` carry
    /// numeric data fit for aggregation; `metadata` carries everything else.
    fn dispatch(&self, name: &[&'static str], measurements: &Measurements, metadata: &Metadata);

    /// Open a new span. Returns the assigned `span_id` (opaque to callers
    /// other than the matching `span_stop` / `span_exception`). Impls
    /// typically also emit a `[..name, "start"]` event here.
    fn span_start(&self, name: &[&'static str], metadata: &Metadata) -> u64;

    /// Close a span normally. Impls typically emit a `[..name, "stop"]`
    /// event carrying `elapsed_ns` plus any caller-supplied stop payload.
    fn span_stop(
        &self,
        name: &[&'static str],
        span_id: u64,
        elapsed_ns: u64,
        measurements: &Measurements,
        metadata: &Metadata,
    );

    /// Close a span that was unwound by a panic. Impls typically emit a
    /// `[..name, "exception"]` event carrying `elapsed_ns` plus any
    /// caller-supplied stop payload.
    fn span_exception(
        &self,
        name: &[&'static str],
        span_id: u64,
        elapsed_ns: u64,
        measurements: &Measurements,
        metadata: &Metadata,
    );

    /// Attach `handler` to events whose name starts with `prefix`.
    /// Implementations that are not a configurable bus may reject this.
    fn attach(&self, _prefix: &[&'static str], _handler: Box<dyn Handler>) -> HandlerId {
        panic!("telemetry handler attachment is unsupported for this telemetry implementation")
    }

    /// Remove a previously attached handler. Returns true if removed.
    fn detach(&self, _id: HandlerId) -> bool {
        false
    }

    raw_event_core!(dispatch_raw_event0);
    raw_event_core!(dispatch_raw_event1, _a);
    raw_event_core!(dispatch_raw_event2, _a, _b);
    raw_event_core!(dispatch_raw_event3, _a, _b, _c);

    raw_span_start_core!(start_raw_span0);
    raw_span_start_core!(start_raw_span1, _a);
    raw_span_start_core!(start_raw_span2, _a, _b);

    raw_span_stop_core!(stop_raw_span0);
    raw_span_stop_core!(stop_raw_span1, _a);

    fn exception_raw_span(
        &self,
        _name: &[&'static str],
        _span_id: u64,
        _elapsed_ns: u64,
        _start_1: TypeId,
        _start_2: TypeId,
        _stop_1: TypeId,
        _stop_2: TypeId,
    ) {
    }
}

/// Zero-sized telemetry for callers that install no observation path.
/// Generic compiler code can monomorphize these empty methods away.
#[derive(Debug, Default, Clone, Copy)]
pub struct NullTelemetry;

pub struct NullSpan;

pub trait RawSpanGuard {
    fn exception(self);
}

pub trait RawSpanStop0: RawSpanGuard {
    fn stop0(self);
}

pub trait RawSpanStop1<P1: Any>: RawSpanGuard {
    fn stop1(self, value: &P1);
}

pub trait RawSpanTelemetry: Telemetry {
    type Span0_0<'a>: RawSpanStop0
    where
        Self: 'a;
    type Span0_1<'a, P1: Any>: RawSpanStop1<P1>
    where
        Self: 'a;
    type Span1_0<'a, S1: Any>: RawSpanStop0
    where
        Self: 'a;
    type Span1_1<'a, S1: Any, P1: Any>: RawSpanStop1<P1>
    where
        Self: 'a;
    type Span2_0<'a, S1: Any, S2: Any>: RawSpanStop0
    where
        Self: 'a;

    fn make_span0_0<'a>(&'a self, name: &'a [&'static str], span_id: u64) -> Self::Span0_0<'a>;
    fn make_span0_1<'a, P1: Any>(&'a self, name: &'a [&'static str], span_id: u64) -> Self::Span0_1<'a, P1>;
    fn make_span1_0<'a, S1: Any>(&'a self, name: &'a [&'static str], span_id: u64) -> Self::Span1_0<'a, S1>;
    fn make_span1_1<'a, S1: Any, P1: Any>(
        &'a self,
        name: &'a [&'static str],
        span_id: u64,
    ) -> Self::Span1_1<'a, S1, P1>;
    fn make_span2_0<'a, S1: Any, S2: Any>(
        &'a self,
        name: &'a [&'static str],
        span_id: u64,
    ) -> Self::Span2_0<'a, S1, S2>;
}

impl Telemetry for NullTelemetry {
    fn is_enabled(&self, _name: &[&'static str]) -> bool {
        false
    }

    fn is_span_enabled(&self, _name: &[&'static str]) -> bool {
        false
    }

    fn dispatch(&self, _name: &[&'static str], _measurements: &Measurements, _metadata: &Metadata) {}

    fn span_start(&self, _name: &[&'static str], _metadata: &Metadata) -> u64 {
        0
    }

    fn span_stop(
        &self,
        _name: &[&'static str],
        _span_id: u64,
        _elapsed_ns: u64,
        _measurements: &Measurements,
        _metadata: &Metadata,
    ) {
    }

    fn span_exception(
        &self,
        _name: &[&'static str],
        _span_id: u64,
        _elapsed_ns: u64,
        _measurements: &Measurements,
        _metadata: &Metadata,
    ) {
    }
}

impl RawSpanGuard for NullSpan {
    fn exception(self) {}
}

impl RawSpanStop0 for NullSpan {
    fn stop0(self) {}
}

impl<P1: Any> RawSpanStop1<P1> for NullSpan {
    fn stop1(self, _value: &P1) {}
}

impl RawSpanTelemetry for NullTelemetry {
    type Span0_0<'a>
        = NullSpan
    where
        Self: 'a;
    type Span0_1<'a, P1: Any>
        = NullSpan
    where
        Self: 'a;
    type Span1_0<'a, S1: Any>
        = NullSpan
    where
        Self: 'a;
    type Span1_1<'a, S1: Any, P1: Any>
        = NullSpan
    where
        Self: 'a;
    type Span2_0<'a, S1: Any, S2: Any>
        = NullSpan
    where
        Self: 'a;

    #[inline(always)]
    fn make_span0_0<'a>(&'a self, _name: &'a [&'static str], _span_id: u64) -> Self::Span0_0<'a> {
        NullSpan
    }

    #[inline(always)]
    fn make_span0_1<'a, P1: Any>(&'a self, _name: &'a [&'static str], _span_id: u64) -> Self::Span0_1<'a, P1> {
        NullSpan
    }

    #[inline(always)]
    fn make_span1_0<'a, S1: Any>(&'a self, _name: &'a [&'static str], _span_id: u64) -> Self::Span1_0<'a, S1> {
        NullSpan
    }

    #[inline(always)]
    fn make_span1_1<'a, S1: Any, P1: Any>(
        &'a self,
        _name: &'a [&'static str],
        _span_id: u64,
    ) -> Self::Span1_1<'a, S1, P1> {
        NullSpan
    }

    #[inline(always)]
    fn make_span2_0<'a, S1: Any, S2: Any>(
        &'a self,
        _name: &'a [&'static str],
        _span_id: u64,
    ) -> Self::Span2_0<'a, S1, S2> {
        NullSpan
    }
}

/// Configured raw-span guard. An active guard captures the start time and emits
/// stop or exception lifecycle. An inactive configured guard contains no
/// telemetry state; `NullTelemetry` uses the separate non-dropping `NullSpan`.
///
/// The `span_id` carried here is opaque to client code; the bus impl
/// (fz-ndf.5) uses it to thread parent linkage into child events emitted
/// while the span is live.
pub struct Span<
    'a,
    T: Telemetry + ?Sized,
    S1: Any = Infallible,
    S2: Any = Infallible,
    P1: Any = Infallible,
    P2: Any = Infallible,
> {
    active: Option<ActiveSpan<'a, T>>,
    marker: PhantomData<fn(&S1, &S2, &P1, &P2)>,
}

#[cfg(test)]
pub struct DetachedSpan<'a> {
    active: Option<DetachedActiveSpan<'a>>,
}

#[cfg(test)]
struct DetachedActiveSpan<'a> {
    name: &'a [&'static str],
    span_id: u64,
    start: Instant,
}

#[cfg(test)]
impl<'a> DetachedSpan<'a> {
    fn new(name: &'a [&'static str], span_id: u64) -> Self {
        Self {
            active: Some(DetachedActiveSpan {
                name,
                span_id,
                start: Instant::now(),
            }),
        }
    }

    fn disabled() -> Self {
        Self { active: None }
    }
}

struct ActiveSpan<'a, T: Telemetry + ?Sized> {
    tel: &'a T,
    name: &'a [&'static str],
    span_id: u64,
    start: Instant,
    stop_measurements: Measurements<'static>,
    stop_metadata: Metadata<'static>,
    closed: bool,
    raw: bool,
}

#[cfg(test)]
impl<'a, T: Telemetry + ?Sized> Span<'a, T> {
    pub(super) fn new(tel: &'a T, name: &'a [&'static str], span_id: u64) -> Self {
        Self {
            active: Some(ActiveSpan {
                tel,
                name,
                span_id,
                start: Instant::now(),
                stop_measurements: Measurements::new(),
                stop_metadata: Metadata::new(),
                closed: false,
                raw: false,
            }),
            marker: PhantomData,
        }
    }

    pub(super) fn disabled() -> Self {
        Self {
            active: None,
            marker: PhantomData,
        }
    }

    /// Close the span immediately with borrowed payload. Useful when the stop
    /// data is only valid for the current scope and should not be copied into
    /// the guard for drop-time emission.
    pub fn stop_with<'meas, 'meta>(mut self, measurements: &Measurements<'meas>, metadata: &Metadata<'meta>) {
        if let Some(active) = self.active.as_mut() {
            let elapsed_ns = active.start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
            active
                .tel
                .span_stop(active.name, active.span_id, elapsed_ns, measurements, metadata);
            active.closed = true;
        }
    }

    pub fn stop_with_lazy<'meas, 'meta>(self, payload: impl FnOnce() -> (Measurements<'meas>, Metadata<'meta>)) {
        if self.active.is_some() {
            let (measurements, metadata) = payload();
            self.stop_with(&measurements, &metadata);
        }
    }
}

impl<'a, T: Telemetry + ?Sized, S1: Any, S2: Any, P1: Any, P2: Any> Span<'a, T, S1, S2, P1, P2> {
    pub(super) fn new_raw(tel: &'a T, name: &'a [&'static str], span_id: u64) -> Self {
        Self {
            active: (span_id != 0).then(|| ActiveSpan {
                tel,
                name,
                span_id,
                start: Instant::now(),
                stop_measurements: Measurements::new(),
                stop_metadata: Metadata::new(),
                closed: false,
                raw: true,
            }),
            marker: PhantomData,
        }
    }

    fn elapsed(active: &ActiveSpan<'_, T>) -> u64 {
        active.start.elapsed().as_nanos().min(u64::MAX as u128) as u64
    }

    fn close_raw_exception(active: &mut ActiveSpan<'_, T>) {
        active.tel.exception_raw_span(
            active.name,
            active.span_id,
            Self::elapsed(active),
            TypeId::of::<S1>(),
            TypeId::of::<S2>(),
            TypeId::of::<P1>(),
            TypeId::of::<P2>(),
        );
        active.closed = true;
    }

    pub fn exception(mut self) {
        if let Some(active) = self.active.as_mut() {
            Self::close_raw_exception(active);
        }
    }

    #[cfg(test)]
    pub fn span_id(&self) -> u64 {
        self.active.as_ref().map_or(0, |active| active.span_id)
    }

    #[cfg(test)]
    pub fn name(&self) -> &[&'static str] {
        self.active.as_ref().map_or(&[], |active| active.name)
    }
}

#[cfg(test)]
impl<T: Telemetry + ?Sized, S1: Any, S2: Any> Span<'_, T, S1, S2> {
    pub fn stop0(mut self) {
        if let Some(active) = self.active.as_mut() {
            active.tel.stop_raw_span0(
                active.name,
                active.span_id,
                Self::elapsed(active),
                TypeId::of::<S1>(),
                TypeId::of::<S2>(),
                TypeId::of::<Infallible>(),
                TypeId::of::<Infallible>(),
            );
            active.closed = true;
        }
    }
}

impl<T: Telemetry + ?Sized, S1: Any, S2: Any, P1: Any, P2: Any> Drop for Span<'_, T, S1, S2, P1, P2> {
    fn drop(&mut self) {
        if let Some(active) = self.active.as_mut() {
            if active.closed {
                return;
            }
            let elapsed_ns = Self::elapsed(active);
            let stop_1 = TypeId::of::<P1>();
            let stop_2 = TypeId::of::<P2>();
            if active.raw
                && !panicking()
                && stop_1 == TypeId::of::<Infallible>()
                && stop_2 == TypeId::of::<Infallible>()
            {
                active.tel.stop_raw_span0(
                    active.name,
                    active.span_id,
                    elapsed_ns,
                    TypeId::of::<S1>(),
                    TypeId::of::<S2>(),
                    stop_1,
                    stop_2,
                );
            } else if active.raw {
                Self::close_raw_exception(active);
            } else if panicking() {
                active.tel.span_exception(
                    active.name,
                    active.span_id,
                    elapsed_ns,
                    &active.stop_measurements,
                    &active.stop_metadata,
                );
            } else {
                active.tel.span_stop(
                    active.name,
                    active.span_id,
                    elapsed_ns,
                    &active.stop_measurements,
                    &active.stop_metadata,
                );
            }
        }
    }
}

impl<T: Telemetry + ?Sized, S1: Any, S2: Any, P1: Any, P2: Any> RawSpanGuard for Span<'_, T, S1, S2, P1, P2> {
    fn exception(self) {
        Span::exception(self);
    }
}

impl<T: Telemetry + ?Sized, S1: Any, S2: Any> RawSpanStop0 for Span<'_, T, S1, S2> {
    fn stop0(mut self) {
        if let Some(active) = self.active.as_mut() {
            active.tel.stop_raw_span0(
                active.name,
                active.span_id,
                Self::elapsed(active),
                TypeId::of::<S1>(),
                TypeId::of::<S2>(),
                TypeId::of::<Infallible>(),
                TypeId::of::<Infallible>(),
            );
            active.closed = true;
        }
    }
}

impl<T: Telemetry + ?Sized, S1: Any, S2: Any, P1: Any> RawSpanStop1<P1> for Span<'_, T, S1, S2, P1> {
    fn stop1(mut self, value: &P1) {
        if let Some(active) = self.active.as_mut() {
            active.tel.stop_raw_span1(
                active.name,
                active.span_id,
                Self::elapsed(active),
                TypeId::of::<S1>(),
                TypeId::of::<S2>(),
                TypeId::of::<P1>(),
                TypeId::of::<Infallible>(),
                value,
            );
            active.closed = true;
        }
    }
}

macro_rules! raw_event_ext {
    ($method:ident, $dispatch:ident $(, $ty:ident $arg:ident)*) => {
        fn $method<$($ty: Any),*>(&self, name: &[&'static str], $($arg: &$ty),*) {
            self.$dispatch(name, $($arg),*);
        }
    };
}

macro_rules! raw_span_ext {
    ($method:ident, $make:ident, $guard:ident, $start:ident, [$($ty:ident),*], [$($arg_ty:ident $arg:ident),*], [$($guard_ty:ty),*], $s1:ty, $s2:ty, $p1:ty, $p2:ty) => {
        #[inline(always)]
        fn $method<'a, $($ty: Any),*>(
            &'a self,
            name: &'a [&'static str],
            $($arg: &$arg_ty),*
        ) -> <Self as RawSpanTelemetry>::$guard<'a, $($guard_ty),*>
        where
            Self: RawSpanTelemetry,
        {
            self.$make(
                name,
                self.$start(
                    name,
                    TypeId::of::<$s1>(),
                    TypeId::of::<$s2>(),
                    TypeId::of::<$p1>(),
                    TypeId::of::<$p2>(),
                    $($arg),*
                ),
            )
        }
    };
}

/// Typed raw telemetry helpers plus test-only legacy payload helpers.
pub trait TelemetryExt: Telemetry {
    #[cfg(test)]
    fn execute_lazy<'meas, 'meta>(
        &self,
        name: &[&'static str],
        payload: impl FnOnce() -> (Measurements<'meas>, Metadata<'meta>),
    );

    #[cfg(test)]
    fn execute_lazy_with(
        &self,
        name: &[&'static str],
        payload: impl FnOnce(&mut dyn FnMut(&Measurements<'_>, &Metadata<'_>)),
    );

    #[cfg(test)]
    fn event_lazy<'meta>(&self, name: &[&'static str], metadata: impl FnOnce() -> Metadata<'meta>);

    #[cfg(test)]
    fn span_lazy<'a, 'meta>(
        &'a self,
        name: &'a [&'static str],
        metadata: impl FnOnce() -> Metadata<'meta>,
    ) -> Span<'a, Self>;

    #[cfg(test)]
    fn start_span_lazy<'a, 'meta>(
        &self,
        name: &'a [&'static str],
        metadata: impl FnOnce() -> Metadata<'meta>,
    ) -> DetachedSpan<'a>;

    #[cfg(test)]
    fn stop_span_lazy<'meas, 'meta>(
        &self,
        span: DetachedSpan<'_>,
        payload: impl FnOnce() -> (Measurements<'meas>, Metadata<'meta>),
    );

    #[cfg(test)]
    fn raw_event0(&self, name: &[&'static str]) {
        self.dispatch_raw_event0(name);
    }
    raw_event_ext!(raw_event1, dispatch_raw_event1, A a);
    raw_event_ext!(raw_event2, dispatch_raw_event2, A a, B b);
    raw_event_ext!(raw_event3, dispatch_raw_event3, A a, B b, C c);

    #[cfg(test)]
    raw_span_ext!(
        raw_span0_0,
        make_span0_0,
        Span0_0,
        start_raw_span0,
        [],
        [],
        [],
        Infallible,
        Infallible,
        Infallible,
        Infallible
    );
    raw_span_ext!(
        raw_span0_1,
        make_span0_1,
        Span0_1,
        start_raw_span0,
        [P1],
        [],
        [P1],
        Infallible,
        Infallible,
        P1,
        Infallible
    );
    raw_span_ext!(raw_span1_0, make_span1_0, Span1_0, start_raw_span1, [S1], [S1 first], [S1], S1, Infallible, Infallible, Infallible);
    raw_span_ext!(raw_span1_1, make_span1_1, Span1_1, start_raw_span1, [S1, P1], [S1 first], [S1, P1], S1, Infallible, P1, Infallible);
    raw_span_ext!(raw_span2_0, make_span2_0, Span2_0, start_raw_span2, [S1, S2], [S1 first, S2 second], [S1, S2], S1, S2, Infallible, Infallible);
}

#[cfg(test)]
fn make_span<'a, T: Telemetry + ?Sized>(tel: &'a T, name: &'a [&'static str], metadata: Metadata) -> Span<'a, T> {
    let span_id = tel.span_start(name, &metadata);
    Span::new(tel, name, span_id)
}

impl<T: Telemetry + ?Sized> TelemetryExt for T {
    #[cfg(test)]
    fn execute_lazy<'meas, 'meta>(
        &self,
        name: &[&'static str],
        payload: impl FnOnce() -> (Measurements<'meas>, Metadata<'meta>),
    ) {
        if self.is_enabled(name) {
            let (measurements, metadata) = payload();
            self.dispatch(name, &measurements, &metadata);
        }
    }

    #[cfg(test)]
    fn execute_lazy_with(
        &self,
        name: &[&'static str],
        payload: impl FnOnce(&mut dyn FnMut(&Measurements<'_>, &Metadata<'_>)),
    ) {
        if self.is_enabled(name) {
            let mut dispatch = |measurements: &Measurements<'_>, metadata: &Metadata<'_>| {
                self.dispatch(name, measurements, metadata);
            };
            payload(&mut dispatch);
        }
    }

    #[cfg(test)]
    fn event_lazy<'meta>(&self, name: &[&'static str], metadata: impl FnOnce() -> Metadata<'meta>) {
        self.execute_lazy(name, || (Measurements::new(), metadata()));
    }

    #[cfg(test)]
    fn span_lazy<'a, 'meta>(
        &'a self,
        name: &'a [&'static str],
        metadata: impl FnOnce() -> Metadata<'meta>,
    ) -> Span<'a, Self> {
        if self.is_span_enabled(name) {
            make_span(self, name, metadata())
        } else {
            Span::disabled()
        }
    }

    #[cfg(test)]
    fn start_span_lazy<'a, 'meta>(
        &self,
        name: &'a [&'static str],
        metadata: impl FnOnce() -> Metadata<'meta>,
    ) -> DetachedSpan<'a> {
        if self.is_span_enabled(name) {
            DetachedSpan::new(name, self.span_start(name, &metadata()))
        } else {
            DetachedSpan::disabled()
        }
    }

    #[cfg(test)]
    fn stop_span_lazy<'meas, 'meta>(
        &self,
        span: DetachedSpan<'_>,
        payload: impl FnOnce() -> (Measurements<'meas>, Metadata<'meta>),
    ) {
        if let Some(active) = span.active {
            let (measurements, metadata) = payload();
            let elapsed_ns = active.start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
            self.span_stop(active.name, active.span_id, elapsed_ns, &measurements, &metadata);
        }
    }
}

#[cfg(test)]
#[path = "sink_test.rs"]
mod sink_test;
