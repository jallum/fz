//! Handlers and the Event they receive.
//!
//! A `Handler` is just "something that wants to observe events." Renderers,
//! file backends, JSON-lines writers, schema validators, and the test
//! `Capture` (fz-ndf.6) are all handlers. The `ConfiguredTelemetry` bus
//! routes events to handlers whose registered prefix matches.

use super::event::{Measurements, Metadata};

/// Distinguishes a regular event from the synthetic start/stop/exception
/// events emitted by a span's lifecycle. Renderers typically format the
/// event name plus a `.start`/`.stop`/`.exception` suffix for span events;
/// keeping the kind on the event (rather than mangling the name) lets
/// handlers match on the structural name without losing context.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventKind {
    /// User-emitted via `execute`.
    Event,
    /// Synthetic — span open.
    SpanStart,
    /// Synthetic — span close, normal path.
    SpanStop,
    /// Synthetic — span close, unwinding from a panic.
    SpanException,
}

impl EventKind {
    #[allow(dead_code)]
    pub fn is_span(self) -> bool {
        !matches!(self, EventKind::Event)
    }
}

/// One observable thing the compiler emitted. Borrowed view — handlers
/// that retain events (e.g. the test `Capture`) must clone into owned form.
#[derive(Debug)]
pub struct Event<'a> {
    pub name: &'a [&'static str],
    pub kind: EventKind,
    pub measurements: &'a Measurements,
    pub metadata: &'a Metadata,
    /// Span this event belongs to, or 0 if no span is open. For
    /// SpanStart/Stop/Exception this is the span's own id.
    pub span_id: u64,
    /// Parent of the current span, or 0 if at the top level.
    pub parent_span_id: u64,
}

/// Subscriber to the event stream.
pub trait Handler {
    fn handle(&self, ev: &Event<'_>);
}

/// Opaque identifier for an attached handler. Used by `detach` to remove.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HandlerId(pub(super) u64);
