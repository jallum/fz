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
    /// Emit a single event. `name` is the hierarchical path
    /// (e.g. `&["fz", "lexer", "tokens_built"]`); `measurements` carry
    /// numeric data fit for aggregation; `metadata` carries everything else.
    fn execute(&self, name: &[&'static str], measurements: &Measurements, metadata: &Metadata);

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

    /// Emit an event with no payload. Shorthand for
    /// `execute(name, &Measurements::new(), &Metadata::new())`.
    fn emit(&self, name: &[&'static str]) {
        self.execute(name, &Measurements::new(), &Metadata::new());
    }

    /// Emit an event carrying only metadata (no measurements). Metadata is
    /// passed by value and borrowed for the dispatch — no heap allocation
    /// since `Metadata` uses inline `SmallVec` storage for ≤ 4 entries.
    fn event(&self, name: &[&'static str], metadata: Metadata) {
        self.execute(name, &Measurements::new(), &metadata);
    }
}

/// Zero-sized telemetry for callers that install no observation path.
/// Generic compiler code can monomorphize these empty methods away.
#[derive(Debug, Default, Clone, Copy)]
pub struct NullTelemetry;

impl Telemetry for NullTelemetry {
    fn execute(&self, _name: &[&'static str], _measurements: &Measurements, _metadata: &Metadata) {}

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

/// RAII guard returned by `TelemetryExt::span`. Captures the start time
/// when constructed; on `Drop`, computes elapsed ns and calls back into
/// the bus — `span_exception` when the scope is unwinding from a panic,
/// `span_stop` otherwise.
///
/// The `span_id` carried here is opaque to client code; the bus impl
/// (fz-ndf.5) uses it to thread parent linkage into child events emitted
/// while the span is live.
pub struct Span<'a, T: Telemetry + ?Sized> {
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
            tel,
            name,
            span_id,
            start: Instant::now(),
            stop_measurements: Measurements::new(),
            stop_metadata: Metadata::new(),
            closed: false,
        }
    }

    /// Replace the payload that will be attached to the eventual stop or
    /// exception event for this span.
    pub fn close_with(&mut self, measurements: Measurements<'static>, metadata: Metadata<'static>) {
        self.stop_measurements = measurements;
        self.stop_metadata = metadata;
    }

    /// Close the span immediately with borrowed payload. Useful when the stop
    /// data is only valid for the current scope and should not be copied into
    /// the guard for drop-time emission.
    pub fn stop_with<'meas, 'meta>(mut self, measurements: &Measurements<'meas>, metadata: &Metadata<'meta>) {
        let elapsed_ns = self.start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
        self.tel
            .span_stop(self.name, self.span_id, elapsed_ns, measurements, metadata);
        self.closed = true;
    }

    /// Opaque identifier for this span. The bus impl uses this to attach
    /// `parent_span_id` to events emitted while the span is open.
    #[cfg(test)]
    pub fn span_id(&self) -> u64 {
        self.span_id
    }

    /// Hierarchical name of the span. Useful for tests and renderers.
    #[cfg(test)]
    pub fn name(&self) -> &[&'static str] {
        self.name
    }
}

impl<T: Telemetry + ?Sized> Drop for Span<'_, T> {
    fn drop(&mut self) {
        if self.closed {
            return;
        }
        let elapsed_ns = self.start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
        if panicking() {
            self.tel.span_exception(
                self.name,
                self.span_id,
                elapsed_ns,
                &self.stop_measurements,
                &self.stop_metadata,
            );
        } else {
            self.tel.span_stop(
                self.name,
                self.span_id,
                elapsed_ns,
                &self.stop_measurements,
                &self.stop_metadata,
            );
        }
    }
}

/// Ergonomic extension trait giving `t.span(...)` on concrete handlers and
/// intentional trait objects without erasing the concrete type in generic code.
pub trait TelemetryExt: Telemetry {
    fn span<'a>(&'a self, name: &'a [&'static str], metadata: Metadata) -> Span<'a, Self>;
}

fn make_span<'a, T: Telemetry + ?Sized>(tel: &'a T, name: &'a [&'static str], metadata: Metadata) -> Span<'a, T> {
    let span_id = tel.span_start(name, &metadata);
    Span::new(tel, name, span_id)
}

impl<T: Telemetry + ?Sized> TelemetryExt for T {
    fn span<'a>(&'a self, name: &'a [&'static str], metadata: Metadata) -> Span<'a, Self> {
        make_span(self, name, metadata)
    }
}

#[cfg(test)]
#[path = "sink_test.rs"]
mod sink_test;
