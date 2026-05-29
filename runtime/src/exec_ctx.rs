//! Per-task execution context.
//!
//! `ExecCtx` is hung off every `Process` (via `Process.ctx`) so that the
//! per-task FFI fns (BIFs) reach scheduler services, the telemetry sink, and
//! the IR module through an **explicit pointer** rather than thread-local
//! singletons. Whichever scheduler owns the `Process` — the JIT `Runtime`, the
//! interpreter, or the AOT shim — builds one `ExecCtx` and points its
//! processes' `ctx` at it.
//!
//! The runtime crate cannot name the binary's `Runtime`, `Telemetry`, or
//! `fz_ir::Module` types (the staticlib does not link against the codegen
//! crate — see `scheduler_hooks`), so the scheduler handle, telemetry sink,
//! and module are type-erased here and re-narrowed by the binary-side
//! callbacks, the same bridging the hook fn-pointers already do.
//!
//! This is the dispatch table that currently lives in the `CURRENT_RUNTIME`,
//! `CURRENT_TEL`, `CURRENT_MODULE` thread-locals and the per-thread hook
//! slots — relocated into a per-context value. Per-context, not per-thread, is
//! what lets two schedulers be live at once on one worker without clobbering
//! each other.

use crate::scheduler_hooks::{
    MakeResourceHook, OutputHook, SendHook, SpawnHook, SpawnOptHook, TimerCancelHook,
    TimerScheduleHook,
};

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
    /// Type-erased telemetry sink (`*const dyn Telemetry` in the binary) that
    /// the `output` callback routes `dbg`/print lines to.
    pub tel: *const (),
    /// Type-erased `*const fz_ir::Module` for `make_resource` dtor resolution.
    pub module: *const (),

    pub spawn: Option<SpawnHook>,
    pub spawn_opt: Option<SpawnOptHook>,
    pub send: Option<SendHook>,
    pub output: Option<OutputHook>,
    pub make_resource: Option<MakeResourceHook>,
    pub timer_schedule: Option<TimerScheduleHook>,
    pub timer_cancel: Option<TimerCancelHook>,
}

impl ExecCtx {
    /// An empty context: no scheduler, no sink, no callbacks. Used as the
    /// inert default before a scheduler installs a real one.
    pub const fn empty() -> Self {
        Self {
            scheduler: std::ptr::null_mut(),
            tel: std::ptr::null(),
            module: std::ptr::null(),
            spawn: None,
            spawn_opt: None,
            send: None,
            output: None,
            make_resource: None,
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
pub fn timer_schedule(process: &crate::process::Process, pid: u32, after_ms: u64) -> Option<u64> {
    if process.ctx.is_null() {
        return None;
    }
    let ctx = unsafe { &*process.ctx };
    ctx.timer_schedule.map(|f| f(ctx.scheduler, pid, after_ms))
}

/// Cancel a previously scheduled after-timer through a process's context.
/// No-op when the context wires no timer.
pub fn timer_cancel(process: &crate::process::Process, timer_id: u64) {
    if process.ctx.is_null() {
        return;
    }
    let ctx = unsafe { &*process.ctx };
    if let Some(f) = ctx.timer_cancel {
        f(ctx.scheduler, timer_id);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    extern "C" fn sample_send(
        _sender: *mut crate::process::Process,
        _scheduler: *mut (),
        _pid: u32,
        _msg: u64,
    ) {
    }

    #[test]
    fn empty_ctx_has_null_handles_and_no_callbacks() {
        let ctx = ExecCtx::empty();
        assert!(ctx.scheduler.is_null());
        assert!(ctx.tel.is_null());
        assert!(ctx.module.is_null());
        assert!(ctx.send.is_none());
        assert!(ctx.spawn.is_none());
    }

    #[test]
    fn populated_ctx_reads_its_fields_back() {
        let mut scheduler = 0u64;
        let tel = 7u64;
        let module = 9u64;
        let ctx = ExecCtx {
            scheduler: (&mut scheduler) as *mut u64 as *mut (),
            tel: (&tel) as *const u64 as *const (),
            module: (&module) as *const u64 as *const (),
            send: Some(sample_send),
            ..ExecCtx::empty()
        };
        assert_eq!(ctx.scheduler, (&mut scheduler) as *mut u64 as *mut ());
        assert_eq!(ctx.tel, (&tel) as *const u64 as *const ());
        assert_eq!(ctx.module, (&module) as *const u64 as *const ());
        assert!(ctx.send.is_some());
    }
}
