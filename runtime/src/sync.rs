//! fz-q8d.3 — sync primitives abstraction.
//!
//! Under `cfg(loom)`, atomics and thread primitives route through
//! `loom`'s instrumented implementations so the loom model checker can
//! enumerate every legal interleaving. Default builds (no `--cfg loom`)
//! use the stdlib types directly with zero overhead.
//!
//! Production code that participates in concurrency (today: just
//! `SharedBin::refcount` and the retain/release primitives in
//! `procbin.rs`) imports `AtomicUsize`, `Ordering`, and `fence` from
//! here, not from `std::sync::atomic`. This single seam is what lets
//! the loom test exercise the ordering claims the source comments make.

#[cfg(loom)]
pub use loom::sync::atomic::{AtomicUsize, Ordering, fence};

#[cfg(not(loom))]
pub use std::sync::atomic::{AtomicUsize, Ordering, fence};
