//! Telemetry: the compiler's observability bus (fz-ndf arc).
//!
//! All compiler outputs that are not control-flow (fatal errors stay on
//! `Result<T, FatalError>`) flow through the telemetry bus:
//! diagnostics, pass spans, stats, and internal markers. Requested output such
//! as IR dumps uses a separate synchronous sink.
//!
//! # Design
//!
//! - **`Telemetry` and `RawSpanTelemetry` traits** (`sink`): the event surface
//!   and concrete raw-span guard capability used by the compiler.
//! - **`ConfiguredTelemetry`** (`bus`): the driver's concrete impl. Maintains
//!   exact typed raw registries, a payload-free lifecycle registry, and a span
//!   stack for parent tracking. Single-threaded (`RefCell`, no `Send`/`Sync`).
//! - **Raw handlers** (`bus`): exact type/arity callbacks receive borrowed
//!   authorities; lifecycle observers receive structure without payloads.
//! - **Legacy handlers** (`handler`): compatibility events used by legacy
//!   emitters and tests. They do not enable raw events.
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
//! - Everything else should use typed raw telemetry methods with existing
//!   references and direct scalars.

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

pub use bus::ConfiguredTelemetry;
#[cfg(test)]
pub use capture::Capture;
pub use event::{Measurements, Metadata};
#[cfg(test)]
pub use handler::Event;
#[cfg(test)]
pub use handler::EventKind;
pub use jsonl::JsonlBackend;
pub use sink::{RawSpanGuard, RawSpanStop1, RawSpanStop2, RawSpanTelemetry, Telemetry, TelemetryExt};
pub use stats::StatsHandler;
pub use value::{Value, opaque};
