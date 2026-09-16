//! Per-task execution context.
//!
//! `ExecCtx` is hung off every `Process` (via `Process.ctx`) so that the
//! per-task FFI fns (BIFs) reach scheduler services, the output context, and
//! runtime services through an **explicit pointer** rather than thread-local
//! singletons. Whichever scheduler owns the `Process` — the JIT `Runtime`, the
//! interpreter, or the AOT shim — builds one `ExecCtx` and points its
//! processes' `ctx` at it.
//!
//! The runtime crate cannot name the binary's `Runtime`, `Telemetry`, or
//! types (the staticlib does not link against the codegen crate — see
//! `scheduler_hooks`), so the scheduler handle and output context are
//! type-erased here and re-narrowed by the binary-side
//! callbacks, the same bridging the hook fn-pointers already do.
//!
//! This dispatch table replaces the old per-thread scheduler-hook slots with a
//! per-context value. Per-context, not per-thread, is what lets two schedulers
//! be live at once on one worker without clobbering each other.

use crate::process::Process;
use crate::scheduler_hooks::{FaultHook, OutputHook, SendHook, SpawnHook, TimerCancelHook, TimerScheduleHook};
use std::ptr::{null, null_mut};

/// The execution-context dispatch table for a running task. See module docs.
///
/// All pointers are type-erased and owned by the scheduler that built the
/// context; the context (and the things it points at) outlive any FFI call
/// made under the owning `Process`.
#[derive(Clone, Copy)]
pub struct ExecCtx {
    /// Type-erased scheduler handle — `*mut Runtime<'_>` on the JIT path, the
    /// AOT scheduler state on the AOT path. The callbacks below re-narrow it.
    pub scheduler: *mut (),
    /// Type-erased scheduler-owned context that receives `dbg`/print bytes.
    pub output_context: *const (),
    /// Immutable program arguments, excluding the executable name. The owning
    /// scheduler keeps this vector alive for every process it dispatches.
    pub argv: *const [String],
    pub spawn: Option<SpawnHook>,
    pub send: Option<SendHook>,
    pub fault: Option<FaultHook>,
    pub output: Option<OutputHook>,
    /// Raw binary output, distinct from `output` so `dbg` retains its
    /// line-oriented rendering contract.
    pub output_write: Option<OutputHook>,
    pub timer_schedule: Option<TimerScheduleHook>,
    pub timer_cancel: Option<TimerCancelHook>,
}

impl ExecCtx {
    /// An empty context: no scheduler, no sink, no callbacks. Used as the
    /// inert default before a scheduler installs a real one.
    pub const fn empty() -> Self {
        Self {
            scheduler: null_mut(),
            output_context: null(),
            argv: std::ptr::slice_from_raw_parts(null(), 0),
            spawn: None,
            send: None,
            fault: None,
            output: None,
            output_write: None,
            timer_schedule: None,
            timer_cancel: None,
        }
    }
}

impl Default for ExecCtx {
    fn default() -> Self {
        Self::empty()
    }
}

/// Schedule an after-timer through a process's execution context. Returns the
/// new `TimerId`, or `None` when the context wires no timer (e.g. a test that
/// doesn't stand up a scheduler) — the caller treats that as an indefinite park.
pub fn timer_schedule(process: &Process, pid: u32, after_ms: u64) -> Option<u64> {
    if process.ctx.is_null() {
        return None;
    }
    let ctx = unsafe { &*process.ctx };
    ctx.timer_schedule.map(|f| f(ctx.scheduler, pid, after_ms))
}

/// Cancel a previously scheduled after-timer through a process's context.
/// No-op when the context wires no timer.
pub fn timer_cancel(process: &Process, timer_id: u64) {
    if process.ctx.is_null() {
        return;
    }
    let ctx = unsafe { &*process.ctx };
    if let Some(f) = ctx.timer_cancel {
        f(ctx.scheduler, timer_id);
    }
}

#[cfg(test)]
#[path = "exec_ctx_test.rs"]
mod exec_ctx_test;
