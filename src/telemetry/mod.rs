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
//!   `StatsHandler` (event counters), `SchemaValidator` (debug assertions).
//! - **Specs** (`spec`): const-constructible `Spec`/`EventDecl`/`KeySpec`
//!   types. Each subsystem exposes `pub const SPEC` naming every event it
//!   emits. The driver can register specs with `SchemaValidator` in debug
//!   builds to catch wiring bugs.
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

// Suppress unused noise: the module is consumed progressively and some re-exports
// have no non-test caller yet in the live pipeline.
#![allow(dead_code, unused_imports)]

pub mod bus;
pub mod capture;
pub mod diag_render;
pub mod event;
pub mod handler;
pub mod jsonl;
pub mod schema_validator;
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
pub use schema_validator::SchemaValidator;
pub use sink::{NullTelemetry, Span, Telemetry, TelemetryExt};
pub use spec::{EventDecl, KeySpec, KeyType, Level, Spec};
pub use stats::StatsHandler;
pub use value::Value;
