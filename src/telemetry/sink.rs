//! The `Telemetry` trait — the compiler-facing observability surface.
//!
//! Compiler code depends only on the trait. The driver constructs whichever
//! concrete impl it wants (see fz-ndf.5 for the configured impl) and threads
//! borrowed concrete handlers through generic compiler paths. Tests may still
//! use trait objects when dynamic dispatch is intentional (fz-ndf.6).
//!
//! Span semantics — start/stop/exception events, elapsed_ns, parent linkage —
//! land in fz-ndf.4.

use std::thread::panicking;
use std::time::Instant;

use super::event::{Measurements, Metadata};
use super::handler::{Handler, HandlerId};

/// The compiler's observability bus. Every observable thing the compiler
/// does — diagnostics, stats, span boundaries, artifact dumps — flows
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
}

/// Zero-sized telemetry for callers that install no observation path.
/// Generic compiler code can monomorphize these empty methods away.
#[derive(Debug, Default, Clone, Copy)]
pub struct NullTelemetry;

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

/// RAII guard returned by `TelemetryExt::span_lazy`. An active guard captures
/// the start time; on `Drop`, it computes elapsed ns and calls back into the
/// bus — `span_exception` when the scope is unwinding from a panic,
/// `span_stop` otherwise. A disabled guard contains no telemetry state.
///
/// The `span_id` carried here is opaque to client code; the bus impl
/// (fz-ndf.5) uses it to thread parent linkage into child events emitted
/// while the span is live.
pub struct Span<'a, T: Telemetry + ?Sized> {
    active: Option<ActiveSpan<'a, T>>,
}

struct ActiveSpan<'a, T: Telemetry + ?Sized> {
    tel: &'a T,
    name: &'a [&'static str],
    span_id: u64,
    start: Instant,
    stop_measurements: Measurements<'static>,
    stop_metadata: Metadata<'static>,
    closed: bool,
}

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
            }),
        }
    }

    pub(super) fn disabled() -> Self {
        Self { active: None }
    }

    fn set_stop_payload(&mut self, measurements: Measurements<'static>, metadata: Metadata<'static>) {
        if let Some(active) = self.active.as_mut() {
            active.stop_measurements = measurements;
            active.stop_metadata = metadata;
        }
    }

    pub fn close_with_lazy(&mut self, payload: impl FnOnce() -> (Measurements<'static>, Metadata<'static>)) {
        if self.active.is_some() {
            let (measurements, metadata) = payload();
            self.set_stop_payload(measurements, metadata);
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

    /// Opaque identifier for this span. The bus impl uses this to attach
    /// `parent_span_id` to events emitted while the span is open.
    #[cfg(test)]
    pub fn span_id(&self) -> u64 {
        match &self.active {
            Some(active) => active.span_id,
            None => 0,
        }
    }

    /// Hierarchical name of the span. Useful for tests and renderers.
    #[cfg(test)]
    pub fn name(&self) -> &[&'static str] {
        match &self.active {
            Some(active) => active.name,
            None => &[],
        }
    }
}

impl<T: Telemetry + ?Sized> Drop for Span<'_, T> {
    fn drop(&mut self) {
        if let Some(active) = self.active.as_ref() {
            if active.closed {
                return;
            }
            let elapsed_ns = active.start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
            if panicking() {
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

/// Lazy telemetry helpers for concrete handlers and intentional trait objects
/// without erasing the concrete type in generic compiler code.
pub trait TelemetryExt: Telemetry {
    fn execute_lazy<'meas, 'meta>(
        &self,
        name: &[&'static str],
        payload: impl FnOnce() -> (Measurements<'meas>, Metadata<'meta>),
    );

    fn execute_lazy_with(
        &self,
        name: &[&'static str],
        payload: impl FnOnce(&mut dyn FnMut(&Measurements<'_>, &Metadata<'_>)),
    );

    fn event_lazy<'meta>(&self, name: &[&'static str], metadata: impl FnOnce() -> Metadata<'meta>);

    fn span_lazy<'a, 'meta>(
        &'a self,
        name: &'a [&'static str],
        metadata: impl FnOnce() -> Metadata<'meta>,
    ) -> Span<'a, Self>;
}

fn make_span<'a, T: Telemetry + ?Sized>(tel: &'a T, name: &'a [&'static str], metadata: Metadata) -> Span<'a, T> {
    let span_id = tel.span_start(name, &metadata);
    Span::new(tel, name, span_id)
}

impl<T: Telemetry + ?Sized> TelemetryExt for T {
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

    fn event_lazy<'meta>(&self, name: &[&'static str], metadata: impl FnOnce() -> Metadata<'meta>) {
        self.execute_lazy(name, || (Measurements::new(), metadata()));
    }

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
}

#[cfg(test)]
#[path = "sink_test.rs"]
mod sink_test;
