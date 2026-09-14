//! Callback *type* definitions for the scheduler services the per-task FFI fns
//! (`fz_spawn`, `fz_send`, `fz_panic`, after-timers, dbg output) drive.
//!
//! Background: these services semantically belong to the runtime substrate (they
//! manipulate Process state), but the *scheduler* — `Runtime` in src/runtime.rs —
//! depends on `CompiledModule` (codegen-side, JIT-only). So `Runtime` stays in the
//! binary, and the runtime crate can't name it directly; the binary supplies
//! `extern "C"` callbacks that re-narrow a type-erased scheduler handle.
//!
//! Those callbacks no longer live in per-thread hook slots. Each one is a field
//! of the running task's [`crate::exec_ctx::ExecCtx`], installed by whichever
//! scheduler owns the Process and passed its erased scheduler handle explicitly.
//! Per-context, not per-thread, is what lets independent schedulers be live at
//! once. This module now only defines the callback fn-pointer *types* (the shape
//! of those ExecCtx fields) plus the `YIELD_PTR` sentinel.

use crate::process::Process;

/// Non-pointer trampoline sentinel: fz_receive_attempt returns this when
/// the mailbox is empty so the JIT trampoline parks the task instead of
/// dispatching the returned ptr. 0x1 is never 16-aligned so it cannot
/// collide with a real heap pointer. (Originally lived in the binary's
/// ir_codegen.rs; lifted here for fz-ul4.23.10 since both the scheduler
/// — in the binary's Runtime — and fz_receive_attempt
/// — in this crate — need it.)
pub const YIELD_PTR: u64 = 0x1;

/// fz_spawn FFI signature on the binary side. fz-ul4.29.5: takes the
/// closure_bits (AnyValue ptr) and returns the new pid. The hook handles
/// deep-copy of the closure into the new task's heap, dispatch via the
/// closure's code pointer to materialize the initial frame, and enqueue.
pub type SpawnHook = extern "C" fn(sender: *mut Process, scheduler: *mut (), closure_bits: u64) -> u32;

/// fz_send FFI signature on the binary side: takes receiver pid plus the
/// one-word any value ref to deliver. The binary's send_via_current_runtime
/// handles the deep-copy into the receiver's heap and the wake-up.
pub type SendHook = extern "C" fn(sender: *mut Process, scheduler: *mut (), receiver_pid: u32, msg_ref_word: u64);

/// Process-fault notification used by a runtime helper whose source contract
/// returns `never`. The value remains owned by `process`; callbacks consume it
/// synchronously and must not retain the raw word past the call.
pub type FaultHook = extern "C" fn(process: *mut Process, context: *mut (), value_ref_word: u64);

pub type OutputHook = unsafe extern "C" fn(context: *const (), line_ptr: *const u8, line_len: usize);

/// fz-yxs/fz-st5 — after-timer schedule hook. Called by
/// `fz_receive_park_matched` when the park record carries a non-`None`
/// after_deadline_ms. The binary owns the `Runtime` (and its
/// `TimerWheel`) so the actual schedule lives there; this hook is the
/// crossing through the staticlib boundary. Returns the fresh
/// `TimerId` (u64) so the FFI can stash it on the park record for
/// later cancellation.
pub type TimerScheduleHook = extern "C" fn(scheduler: *mut (), pid: u32, after_ms: u64) -> u64;

/// fz-yxs/fz-st5 — counterpart cancel hook, fired when a matcher hit
/// (sender-probe or initial-scan) wakes the receiver before the timer
/// expires. No-op when `timer_id` is unknown (already fired).
pub type TimerCancelHook = extern "C" fn(scheduler: *mut (), timer_id: u64);

// fz-vdt ctx.4-6: the per-thread scheduler-hook slots are gone. Each callback
// now lives on the running task's `ExecCtx` (see exec_ctx.rs) — per-context,
// not per-thread — so independent schedulers can be live at once. Only the
// callback *type* definitions above remain, as the shape of those ExecCtx fields.
