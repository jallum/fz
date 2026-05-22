//! Telemetry: the compiler's observability bus (fz-ndf arc).
//!
//! The compiler emits structured events — diagnostics, stats, spans, dumps,
//! internal markers — through a `Telemetry` trait. The driver constructs a
//! configured impl and threads `&dyn Telemetry` into the compiler; tests can
//! pass a capture impl; production binaries pass renderers and file backends.
//! When `NullTelemetry` is passed, every emit is a no-op.
//!
//! This file currently exposes only the value types (fz-ndf.1). The trait,
//! spans, specs, handlers, and concrete impls land in subsequent tickets.

// API surface consumed progressively by subsequent fz-ndf tickets.
// Suppress unused noise at module scope rather than peppering attributes.
#![allow(dead_code, unused_imports)]

pub mod bus;
pub mod capture;
pub mod diag_render;
pub mod event;
pub mod handler;
pub mod jsonl;
pub mod sink;
pub mod spec;
pub mod stats;
pub mod value;

pub use bus::ConfiguredTelemetry;
pub use capture::{Capture, OwnedEvent};
pub use diag_render::{DiagOutput, DiagRenderer};
pub use event::{Measurements, Metadata};
pub use handler::{Event, EventKind, Handler, HandlerId};
pub use jsonl::JsonlBackend;
pub use sink::{NullTelemetry, Span, Telemetry, TelemetryExt};
pub use spec::{EventDecl, KeySpec, KeyType, Level, Spec};
pub use stats::StatsHandler;
pub use value::Value;
