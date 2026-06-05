//! The `Telemetry` trait — the compiler-facing observability surface.
//!
//! Compiler code depends only on the trait. The driver constructs whichever
//! concrete impl it wants (see fz-ndf.5 for the configured impl) and threads
//! `&dyn Telemetry` through. Tests pass capture impls (fz-ndf.6).
//!
//! Span semantics — start/stop/exception events, elapsed_ns, parent linkage —
//! land in fz-ndf.4.

use std::thread::panicking;
use std::time::Instant;

use super::event::{Measurements, Metadata};

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
    /// event carrying `elapsed_ns`.
    fn span_stop(&self, name: &[&'static str], span_id: u64, elapsed_ns: u64);

    /// Close a span that was unwound by a panic. Impls typically emit a
    /// `[..name, "exception"]` event carrying `elapsed_ns`.
    fn span_exception(&self, name: &[&'static str], span_id: u64, elapsed_ns: u64);

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

/// RAII guard returned by `TelemetryExt::span`. Captures the start time
/// when constructed; on `Drop`, computes elapsed ns and calls back into
/// the bus — `span_exception` when the scope is unwinding from a panic,
/// `span_stop` otherwise.
///
/// The `span_id` carried here is opaque to client code; the bus impl
/// (fz-ndf.5) uses it to thread parent linkage into child events emitted
/// while the span is live.
pub struct Span<'a> {
    tel: &'a dyn Telemetry,
    name: Box<[&'static str]>,
    span_id: u64,
    start: Instant,
}

impl<'a> Span<'a> {
    pub(super) fn new(tel: &'a dyn Telemetry, name: &[&'static str], span_id: u64) -> Self {
        Self {
            tel,
            name: Box::from(name),
            span_id,
            start: Instant::now(),
        }
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
        &self.name
    }
}

impl Drop for Span<'_> {
    fn drop(&mut self) {
        let elapsed_ns = self.start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
        if panicking() {
            self.tel.span_exception(&self.name, self.span_id, elapsed_ns);
        } else {
            self.tel.span_stop(&self.name, self.span_id, elapsed_ns);
        }
    }
}

/// Ergonomic extension trait giving `t.span(...)` on any `&dyn Telemetry`.
/// Split off the main trait so `Telemetry` stays dyn-safe and impl-free.
pub trait TelemetryExt {
    fn span(&self, name: &[&'static str], metadata: Metadata) -> Span<'_>;
}

fn make_span<'a>(tel: &'a dyn Telemetry, name: &[&'static str], metadata: Metadata) -> Span<'a> {
    let span_id = tel.span_start(name, &metadata);
    Span::new(tel, name, span_id)
}

// Two impls so `t.span(...)` works for both concrete impls (which coerce
// `&T` to `&dyn Telemetry` thanks to `T: Sized`) and trait objects
// (which already are `&dyn Telemetry`). The Sized blanket and the `dyn`
// impl don't overlap because `dyn Telemetry: !Sized`.
impl<T: Telemetry> TelemetryExt for T {
    fn span(&self, name: &[&'static str], metadata: Metadata) -> Span<'_> {
        make_span(self, name, metadata)
    }
}

impl TelemetryExt for dyn Telemetry + '_ {
    fn span(&self, name: &[&'static str], metadata: Metadata) -> Span<'_> {
        make_span(self, name, metadata)
    }
}

#[cfg(test)]
#[path = "sink_test.rs"]
mod sink_test;
