//! Test-facing capture of the *public* compiler2 trace — the JSONL stream
//! that survives `is_public_compiler2_trace_event` (`jsonl.rs`), the same
//! allowlist production applies via `fz2 --log-telemetry`.
//!
//! This parses the rendered JSONL string domain rather than reusing
//! `Capture` (`capture.rs`). `Capture` attaches ahead of the allowlist and
//! exposes pre-projection `Any` payloads — using it here would let a test
//! see facts the public artifact never renders. The public trace *is* the
//! text `JsonlBackend::new_public_writer` writes; parsing exactly that text
//! is the only way to test what the artifact actually shows, not what the
//! compiler happened to compute along the way.
//!
//! `PublicEvent` and the parser itself live in `causal` (`causal.rs`), which
//! is `pub`: the cross-process acceptance test in `tests/fz2_cli.rs` is an
//! integration test and cannot see a `#[cfg(test)]` module. One parser reads
//! the artifact for both.
//!
//! `JsonlBackend`'s public writer is buffered (64KB threshold) and only
//! flushes its tail reliably on `Drop` (fz-kdt.34's own multi-day
//! misdiagnosis was a truncated read of exactly this buffer). `PublicTrace`
//! encapsulates that lifecycle: `compile` drives inside an inner scope, lets
//! the `Compiler2` — and with it the `ConfiguredTelemetry` and the backend's
//! last `Rc` — drop, and only then parses the shared buffer.

use crate::compiler2::{CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, FactKey, Job, RootSubmission};

use super::ConfiguredTelemetry;
use super::capture::vec_writer;
use super::causal::{PublicEvent, parse_public_trace};
use super::handler::EventKind;
use super::jsonl::JsonlBackend;

/// A `span_start`/`span_stop` pair from the public stream, matched by
/// `span_id`. `stop` is `None` only if the stream ended before the span
/// closed — for a `Resolved` compile that never happens.
#[derive(Debug, Clone)]
pub struct PublicSpan {
    pub span_id: u64,
    pub parent_span_id: u64,
    pub start: PublicEvent,
    pub stop: Option<PublicEvent>,
}

/// A compile driven under a public-only telemetry writer, with the
/// resulting public JSONL stream parsed into `PublicEvent`s in emission
/// order. Mirrors `ExUnit.CaptureLog.with_log`: the action's result
/// (`outcome`) and the artifact it produced travel together.
pub struct PublicTrace {
    pub outcome: DriveOutcome<Job, FactKey>,
    events: Vec<PublicEvent>,
}

impl PublicTrace {
    /// Compiles `source` — which must define `main/0`, the same requirement
    /// `fz2 run`/`interp`/`build` place on their input — through a fresh
    /// `Compiler2` wired to a public-only `JsonlBackend`, and returns the
    /// outcome plus the fully flushed public stream it produced.
    pub fn compile(source: &str) -> Self {
        let telemetry = ConfiguredTelemetry::new();
        let (buf, writer) = vec_writer();
        JsonlBackend::new_public_writer(writer).install(&telemetry);

        // The `Compiler2` owns the `ConfiguredTelemetry`, which in turn
        // owns the last `Rc<JsonlBackend>`. Only when `compiler` drops at
        // the end of this block does the backend drop and flush its
        // buffered tail into `buf` — reading `buf` before that observes a
        // truncated stream.
        let outcome = {
            let mut compiler = Compiler2::new(telemetry);
            compiler.submit_code(CodeSubmission {
                name: Some("public_trace.fz".to_string()),
                text: source.to_string(),
            });
            compiler.submit_root(RootSubmission {
                module_name: None,
                name: "main".to_string(),
                arity: 0,
                need: ExecutableNeed::Value,
            });
            compiler.drive()
        };

        let events = parse_public_trace(&buf.borrow());
        Self { outcome, events }
    }

    /// Compile and request the interpreter backend so product-search events
    /// are included in the captured public stream.
    pub fn compile_backend(source: &str) -> Self {
        let telemetry = ConfiguredTelemetry::new();
        let (buf, writer) = vec_writer();
        JsonlBackend::new_public_writer(writer).install(&telemetry);

        let outcome = {
            let mut compiler = Compiler2::new(telemetry);
            compiler.set_output(Box::new(fz_runtime::output::NullOutput));
            compiler.submit_code(CodeSubmission {
                name: Some("public_product_trace.fz".to_string()),
                text: source.to_string(),
            });
            let root = compiler.submit_root(RootSubmission {
                module_name: None,
                name: "main".to_string(),
                arity: 0,
                need: ExecutableNeed::Value,
            });
            let outcome = compiler.drive();
            assert!(matches!(outcome, DriveOutcome::Resolved));
            compiler
                .run_root_interp(root)
                .unwrap_or_else(|error| panic!("public product trace failed: {error}"));
            outcome
        };

        let events = parse_public_trace(&buf.borrow());
        Self { outcome, events }
    }

    /// The public stream in emission order.
    pub fn events(&self) -> &[PublicEvent] {
        &self.events
    }

    /// Events whose name matches `name` exactly, in emission order.
    pub fn events_named(&self, name: &[&str]) -> Vec<&PublicEvent> {
        self.events
            .iter()
            .filter(|ev| ev.name.iter().map(String::as_str).eq(name.iter().copied()))
            .collect()
    }

    /// Every span in the stream, paired by `span_id`, ordered by each
    /// span's `span_start`.
    pub fn spans(&self) -> Vec<PublicSpan> {
        let mut spans: Vec<PublicSpan> = Vec::new();
        let mut index_by_span_id = std::collections::HashMap::new();
        for event in &self.events {
            match event.kind {
                EventKind::SpanStart => {
                    index_by_span_id.insert(event.span_id, spans.len());
                    spans.push(PublicSpan {
                        span_id: event.span_id,
                        parent_span_id: event.parent_span_id,
                        start: event.clone(),
                        stop: None,
                    });
                }
                EventKind::SpanStop | EventKind::SpanException => {
                    if let Some(&index) = index_by_span_id.get(&event.span_id) {
                        spans[index].stop = Some(event.clone());
                    }
                }
                EventKind::Event => {}
            }
        }
        spans
    }

    /// Spans (see `spans`) whose start event matches `name` exactly.
    pub fn spans_named(&self, name: &[&str]) -> Vec<PublicSpan> {
        self.spans()
            .into_iter()
            .filter(|span| span.start.name.iter().map(String::as_str).eq(name.iter().copied()))
            .collect()
    }
}

#[cfg(test)]
#[path = "public_trace_test.rs"]
mod public_trace_test;
