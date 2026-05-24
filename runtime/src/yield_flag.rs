//! Global cooperative yield flag for the fz scheduler.
//!
//! `FZ_SHOULD_YIELD` is a global (not per-process) because:
//!   (a) Native Tail-CC JIT fns have no cheap path to the current process —
//!       the flag must be reachable via a single known address.
//!   (b) External timer/signal handlers can set it without knowing which
//!       process is running — the foundation for future soft preemption.
//!
//! The JIT emits a 3-instruction inline check at every back-edge:
//!   load.i8 global_value(%fz_should_yield_data) + 0
//!   brz flag, $fast
//!   ; slow: build continuation closure, call fz_yield_mid_flight, return YIELD_PTR
//!   $fast: return_call callee(args...)

use std::sync::atomic::AtomicU8;

#[unsafe(no_mangle)]
pub static FZ_SHOULD_YIELD: AtomicU8 = AtomicU8::new(0);
