//! The `Telemetry` trait — the compiler-facing surface — plus the
//! `NullTelemetry` no-op implementation passed by default.
//!
//! Compiler code depends only on the trait. The driver constructs whichever
//! concrete impl it wants (see fz-ndf.5 for the configured impl) and threads
//! `&dyn Telemetry` through. Tests pass capture impls (fz-ndf.6). Production
//! binaries that just want silence pass `&NullTelemetry`.
//!
//! Span semantics — start/stop/exception events, elapsed_ns, parent linkage —
//! land in fz-ndf.4. This ticket gives Span the data shape it needs; its Drop
//! behavior is a no-op stub until then.

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
    fn execute(
        &self,
        name: &[&'static str],
        measurements: &Measurements,
        metadata: &Metadata,
    );

    /// Open a new span. Returns the assigned `span_id` (opaque to callers
    /// other than the matching `span_stop` / `span_exception`). Impls
    /// typically also emit a `[..name, "start"]` event here.
    fn span_start(&self, name: &'static [&'static str], metadata: &Metadata) -> u64;

    /// Close a span normally. Impls typically emit a `[..name, "stop"]`
    /// event carrying `elapsed_ns`.
    fn span_stop(&self, name: &'static [&'static str], span_id: u64, elapsed_ns: u64);

    /// Close a span that was unwound by a panic. Impls typically emit a
    /// `[..name, "exception"]` event carrying `elapsed_ns`.
    fn span_exception(&self, name: &'static [&'static str], span_id: u64, elapsed_ns: u64);
}

/// No-op implementation. Every method returns immediately and allocates
/// nothing. The compiler treats `&NullTelemetry` as the "silent" default
/// when the driver doesn't want observability.
#[derive(Debug, Clone, Copy, Default)]
pub struct NullTelemetry;

impl Telemetry for NullTelemetry {
    #[inline]
    fn execute(&self, _: &[&'static str], _: &Measurements, _: &Metadata) {}

    #[inline]
    fn span_start(&self, _: &'static [&'static str], _: &Metadata) -> u64 {
        0
    }

    #[inline]
    fn span_stop(&self, _: &'static [&'static str], _: u64, _: u64) {}

    #[inline]
    fn span_exception(&self, _: &'static [&'static str], _: u64, _: u64) {}
}

/// RAII guard returned by `TelemetryExt::span`. In fz-ndf.3 this is a
/// data-only placeholder; fz-ndf.4 gives it a `Drop` impl that calls
/// `span_stop` (or `span_exception` on a panicking unwind).
pub struct Span<'a> {
    tel: &'a dyn Telemetry,
    name: &'static [&'static str],
    span_id: u64,
}

impl<'a> Span<'a> {
    pub(super) fn new(
        tel: &'a dyn Telemetry,
        name: &'static [&'static str],
        span_id: u64,
    ) -> Self {
        Self { tel, name, span_id }
    }

    /// Opaque identifier for this span. Child events (and nested spans)
    /// can attach this as `parent_span_id` metadata.
    pub fn span_id(&self) -> u64 {
        self.span_id
    }

    /// Read-only access to the bus this span is bound to, so callers can
    /// emit events *within* the span without re-threading the telemetry
    /// reference.
    pub fn tel(&self) -> &'a dyn Telemetry {
        self.tel
    }

    /// Hierarchical name of the span. Useful for tests and renderers.
    pub fn name(&self) -> &'static [&'static str] {
        self.name
    }
}

/// Ergonomic extension trait giving `t.span(...)` on any `&dyn Telemetry`.
/// Split off the main trait so `Telemetry` stays dyn-safe and impl-free.
pub trait TelemetryExt {
    fn span(&self, name: &'static [&'static str], metadata: Metadata) -> Span<'_>;
}

// Two impls so `t.span(...)` works for both concrete impls (which coerce
// `&T` to `&dyn Telemetry` thanks to `T: Sized`) and trait objects
// (which already are `&dyn Telemetry`). The Sized blanket and the `dyn`
// impl don't overlap because `dyn Telemetry: !Sized`.
impl<T: Telemetry> TelemetryExt for T {
    fn span(&self, name: &'static [&'static str], metadata: Metadata) -> Span<'_> {
        let span_id = self.span_start(name, &metadata);
        Span::new(self, name, span_id)
    }
}

impl TelemetryExt for dyn Telemetry + '_ {
    fn span(&self, name: &'static [&'static str], metadata: Metadata) -> Span<'_> {
        let span_id = self.span_start(name, &metadata);
        Span::new(self, name, span_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{measurements, metadata};

    #[test]
    fn null_execute_is_a_noop() {
        let t = NullTelemetry;
        t.execute(
            &["fz", "any", "event"],
            &measurements! { count: 3i64 },
            &metadata! { fn_name: "x" },
        );
        // No panic, no observable effect. Test passes if we got here.
    }

    #[test]
    fn null_span_lifecycle_returns_zero_id() {
        let t = NullTelemetry;
        let id = t.span_start(&["fz", "x", "pass"], &Metadata::new());
        assert_eq!(id, 0);
        t.span_stop(&["fz", "x", "pass"], id, 0);
        t.span_exception(&["fz", "x", "pass"], id, 0);
    }

    #[test]
    fn telemetry_is_object_safe() {
        let t: &dyn Telemetry = &NullTelemetry;
        t.execute(&["fz", "x"], &Measurements::new(), &Metadata::new());
    }

    #[test]
    fn ext_span_is_callable_through_dyn() {
        let t: &dyn Telemetry = &NullTelemetry;
        let span = t.span(&["fz", "any", "pass"], metadata! { x: 1i64 });
        assert_eq!(span.span_id(), 0);
        assert_eq!(span.name(), &["fz", "any", "pass"]);
    }

    #[test]
    fn ext_span_is_callable_through_concrete() {
        let t = NullTelemetry;
        let span = t.span(&["fz", "any", "pass"], Metadata::new());
        assert_eq!(span.span_id(), 0);
    }

    /// Tiny mock that counts each method call. Used by sibling tests
    /// in fz-ndf.4 onward — here it just demonstrates the trait is
    /// straightforwardly implementable.
    struct CountingMock {
        executes: std::cell::Cell<u32>,
        starts: std::cell::Cell<u32>,
        stops: std::cell::Cell<u32>,
        exceptions: std::cell::Cell<u32>,
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
        fn span_start(&self, _: &'static [&'static str], _: &Metadata) -> u64 {
            let id = self.starts.get() as u64 + 1;
            self.starts.set(self.starts.get() + 1);
            id
        }
        fn span_stop(&self, _: &'static [&'static str], _: u64, _: u64) {
            self.stops.set(self.stops.get() + 1);
        }
        fn span_exception(&self, _: &'static [&'static str], _: u64, _: u64) {
            self.exceptions.set(self.exceptions.get() + 1);
        }
    }

    #[test]
    fn mock_impl_records_execute_calls() {
        let m = CountingMock::new();
        m.execute(&["fz", "x"], &Measurements::new(), &Metadata::new());
        m.execute(&["fz", "y"], &Measurements::new(), &Metadata::new());
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
}
