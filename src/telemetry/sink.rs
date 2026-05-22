//! The `Telemetry` trait — the compiler-facing surface — plus the
//! `NullTelemetry` no-op implementation passed by default.
//!
//! Compiler code depends only on the trait. The driver constructs whichever
//! concrete impl it wants (see fz-ndf.5 for the configured impl) and threads
//! `&dyn Telemetry` through. Tests pass capture impls (fz-ndf.6). Production
//! binaries that just want silence pass `&NullTelemetry`.
//!
//! Span semantics — start/stop/exception events, elapsed_ns, parent linkage —
//! land in fz-ndf.4.

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
    fn span_start(&self, _: &[&'static str], _: &Metadata) -> u64 {
        0
    }

    #[inline]
    fn span_stop(&self, _: &[&'static str], _: u64, _: u64) {}

    #[inline]
    fn span_exception(&self, _: &[&'static str], _: u64, _: u64) {}
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
    start: std::time::Instant,
}

impl<'a> Span<'a> {
    pub(super) fn new(tel: &'a dyn Telemetry, name: &[&'static str], span_id: u64) -> Self {
        Self {
            tel,
            name: Box::from(name),
            span_id,
            start: std::time::Instant::now(),
        }
    }

    /// Opaque identifier for this span. The bus impl uses this to attach
    /// `parent_span_id` to events emitted while the span is open.
    #[allow(dead_code)]
    pub fn span_id(&self) -> u64 {
        self.span_id
    }

    /// Read-only access to the bus this span is bound to, so callers can
    /// emit events *within* the span without re-threading the telemetry
    /// reference.
    #[allow(dead_code)]
    pub fn tel(&self) -> &'a dyn Telemetry {
        self.tel
    }

    /// Hierarchical name of the span. Useful for tests and renderers.
    #[allow(dead_code)]
    pub fn name(&self) -> &[&'static str] {
        &self.name
    }
}

impl Drop for Span<'_> {
    fn drop(&mut self) {
        let elapsed_ns = self.start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
        if std::thread::panicking() {
            self.tel
                .span_exception(&self.name, self.span_id, elapsed_ns);
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

    // Richer recording mock for verifying Span's Drop semantics.
    struct RecordingMock {
        next_id: std::cell::Cell<u64>,
        records: std::cell::RefCell<Vec<SpanRec>>,
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
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
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
            elapsed: std::cell::Cell<u64>,
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
            std::thread::sleep(std::time::Duration::from_micros(50));
        }
        assert!(c.elapsed.get() > 0, "expected nonzero elapsed_ns");
    }

    #[test]
    fn null_telemetry_span_drop_is_silent() {
        // Sanity: with NullTelemetry, Drop runs but does nothing observable.
        let t = NullTelemetry;
        let _ = t.span(&["fz", "x"], Metadata::new());
    }
}
