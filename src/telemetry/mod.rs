//! Telemetry: the compiler's observability bus (fz-ndf arc).
//!
//! All compiler outputs that are not control-flow (fatal errors stay on
//! `Result<T, FatalError>`) flow through the telemetry bus:
//! diagnostics, pass spans, stats, IR dumps, and internal markers.
//!
//! # Design
//!
//! - **`Telemetry` trait** (`sink`): the only interface the compiler depends on.
//! - **`ConfiguredTelemetry`** (`bus`): the driver's concrete impl. Maintains
//!   a handler registry with prefix-based routing and a span stack for parent
//!   tracking. Single-threaded (`RefCell`, no `Send`/`Sync`).
//! - **Handlers** (`handler`): `Handler::handle(&Event<'_, '_, '_>)` receives every
//!   routed event. Concrete impls: `Capture` (tests), `DiagRenderer`
//!   (diagnostics → stderr/writer), `JsonlBackend` (file logging),
//!   `StatsHandler` (event counters).
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
#[cfg(test)]
pub mod capture;
pub mod diag_render;
pub mod event;
pub mod handler;
pub mod jsonl;
pub mod sink;
pub mod stats;
pub mod value;

use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_COMPILE_NONCE: AtomicU64 = AtomicU64::new(1);

pub use bus::ConfiguredTelemetry;
#[cfg(test)]
pub use capture::Capture;
pub use diag_render::DiagRenderer;
pub use event::{Measurements, Metadata};
#[cfg(test)]
pub use handler::EventKind;
pub use handler::{Event, Handler, HandlerId};
pub use jsonl::JsonlBackend;
pub use sink::{Telemetry, TelemetryExt};
pub use stats::StatsHandler;
pub use value::{Value, opaque, opaque_debug};

pub(crate) fn next_compile_nonce() -> u64 {
    NEXT_COMPILE_NONCE.fetch_add(1, Ordering::Relaxed)
}
