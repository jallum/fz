//! Telemetry: the compiler's observability bus (fz-ndf arc).
//!
//! All compiler outputs that are not control-flow (fatal errors stay on
//! `Result<T, FatalError>`) flow through the telemetry bus:
//! diagnostics, pass spans, stats, IR dumps, and internal markers.
//!
//! # Design
//!
//! - **`Telemetry` trait** (`sink`): the only interface the compiler depends on.
//!   `NullTelemetry` is the zero-cost no-op impl used when no observability is
//!   wanted.
//! - **`ConfiguredTelemetry`** (`bus`): the driver's concrete impl. Maintains
//!   a handler registry with prefix-based routing and a span stack for parent
//!   tracking. Single-threaded (`RefCell`, no `Send`/`Sync`).
//! - **Handlers** (`handler`): `Handler::handle(&Event<'_>)` receives every
//!   routed event. Concrete impls: `Capture` (tests), `DiagRenderer`
//!   (diagnostics → stderr/writer), `JsonlBackend` (file logging),
//!   `StatsHandler` (event counters).
//! - **Specs** (`spec`): const-constructible `Spec`/`EventDecl`/`KeySpec`
//!   types. Each subsystem exposes `pub const SPEC` naming every event it
//!   emits.
//! - **Macros** (`measurements!`, `metadata!` in `macros`): ergonomic
//!   construction of event payloads.
//!
//! # Print-site policy
//!
//! `println!`/`eprintln!` at a call site inside a `Handler::handle()` impl is
//! correct — handlers are the rendering layer. Outside a handler:
//! - **UX / argument-parsing errors** (usage messages, bad flags, file-not-found
//!   at startup) stay as `eprintln!` — these are user-facing CLI errors, not
//!   observability.
//! - **Language built-ins** (`eval.rs` `print/1`) stay as `println!` — they
//!   are the fz program's stdout, not compiler output.
//! - **Runtime simulation warnings** (`ir_interp.rs` send/dtor errors) stay as
//!   `eprintln!` — these are interpreter runtime stderr, not compilation events.
//! - Everything else should be a `tel.execute(...)` call.

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
// Capture and OwnedEvent are test-facing API: used inside #[cfg(test)] blocks
// in sibling modules and in diag::driver tests. Not consumed in the live pipeline.
#[allow(unused_imports)]
pub use capture::{Capture, OwnedEvent};
pub use diag_render::DiagRenderer;
pub use event::{Measurements, Metadata};
pub use handler::{Event, Handler};
// EventKind: used in handler impls and tests. HandlerId: returned by attach(),
// needed by detach() callers — not yet wired in the main pipeline.
#[allow(unused_imports)]
pub use handler::{EventKind, HandlerId};
pub use jsonl::JsonlBackend;
pub use sink::{NullTelemetry, Telemetry, TelemetryExt};
// Span: returned by TelemetryExt::span; used in tests and by future span-aware callers.
#[allow(unused_imports)]
pub use sink::Span;
pub use spec::{EventDecl, KeySpec, Spec};
pub use stats::StatsHandler;
pub use value::Value;
