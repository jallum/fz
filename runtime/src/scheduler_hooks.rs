//! Hooks the fz binary installs into the runtime staticlib so the
//! per-task FFI fns (`fz_spawn`, `fz_send`) can drive a Runtime that
//! the staticlib itself doesn't link against.
//!
//! Background: spawn / send semantically belong to the runtime substrate
//! (they manipulate Process state), but the *scheduler* — `Runtime` in
//! src/runtime.rs — depends on `CompiledModule` (codegen-side, JIT-only
//! today). So Runtime stays in the binary, and the runtime crate exposes
//! function-pointer slots that the binary fills in before driving any
//! task.
//!
//! Lifecycle:
//!
//!   1. Binary builds a Runtime around a CompiledModule.
//!   2. Before `run_until_idle`, binary calls install_spawn_hook /
//!      install_send_hook with extern "C" callbacks that close over the
//!      Runtime via the existing CURRENT_RUNTIME TLS (a *mut ()).
//!   3. JIT'd code (or interp / AOT entry shim) calls fz_spawn /
//!      fz_send; those dispatch through the hooks.
//!   4. After `run_until_idle`, binary clears the hooks (so a later call
//!      from outside a Runtime fails loudly).

use std::cell::Cell;

/// Non-pointer trampoline sentinel: fz_receive_attempt returns this when
/// the mailbox is empty so the JIT trampoline parks the task instead of
/// dispatching the returned ptr. 0x1 is never 16-aligned so it cannot
/// collide with a real heap pointer. (Originally lived in the binary's
/// ir_codegen.rs; lifted here for fz-ul4.23.10 since both the trampoline
/// — in the binary's CompiledModule::run_internal — and fz_receive_attempt
/// — in this crate — need it.)
pub const YIELD_PTR: u64 = 0x1;

/// fz_spawn FFI signature on the binary side. fz-ul4.29.5: takes the
/// closure_bits (AnyValue ptr) and returns the new pid. The hook handles
/// deep-copy of the closure into the new task's heap, dispatch via the
/// closure's code pointer to materialize the initial frame, and enqueue.
pub type SpawnHook = extern "C" fn(closure_bits: u64) -> u32;

/// fz-siu.12: fz_spawn_opt FFI signature. Like SpawnHook but also accepts
/// min_heap_size (bytes, already unboxed from AnyValue). v1: hint accepted
/// and ignored by the binary; hook body is identical to SpawnHook.
pub type SpawnOptHook = extern "C" fn(closure_bits: u64, min_heap_size: u32) -> u32;

/// fz_send FFI signature on the binary side: takes receiver pid plus the
/// one-word tagged value ref to deliver. The binary's send_via_current_runtime
/// handles the deep-copy into the receiver's heap and the wake-up.
pub type SendHook = extern "C" fn(receiver_pid: u32, msg_ref_word: u64);

/// fz-swt.10 — `fz_make_resource(payload, dtor_closure)` FFI signature on
/// the binary side. The runtime crate forwards the raw integer payload and an
/// opaque `TaggedValueRef` closure word through this hook so the binary can
/// resolve the dtor C-ABI fn pointer from the closure value (the binary holds
/// the IR `Module` and can walk the closure's body to find the underlying
/// `Prim::Extern`). The hook allocates the off-heap `Resource` + on-heap stub
/// on the current process heap and returns the resulting tagged resource
/// pointer.
pub type MakeResourceHook = extern "C" fn(payload_raw: u64, dtor_ref: u64) -> u64;

/// fz-yxs/fz-st5 — after-timer schedule hook. Called by
/// `fz_receive_park_matched` when the park record carries a non-`None`
/// after_deadline_ms. The binary owns the `Runtime` (and its
/// `TimerWheel`) so the actual schedule lives there; this hook is the
/// crossing through the staticlib boundary. Returns the fresh
/// `TimerId` (u64) so the FFI can stash it on the park record for
/// later cancellation.
pub type TimerScheduleHook = extern "C" fn(pid: u32, after_ms: u64) -> u64;

/// fz-yxs/fz-st5 — counterpart cancel hook, fired when a matcher hit
/// (sender-probe or initial-scan) wakes the receiver before the timer
/// expires. No-op when `timer_id` is unknown (already fired).
pub type TimerCancelHook = extern "C" fn(timer_id: u64);

// Per-thread hook storage. A Runtime is single-worker by design
// (fz-ul4.19.1) and "the current Runtime" is a per-thread concept — same
// shape as CURRENT_PROCESS (runtime/src/process.rs) and CURRENT_RUNTIME
// (src/runtime.rs). Storing the hooks per-thread lets independent
// Runtimes run on independent threads (e.g. cargo's parallel test
// harness) without clobbering each other's dispatch table.
//
// fz-esw: an earlier attempt at thread_local! produced duplicate
// __ZN…_tlv$init symbols in AOT-linked binaries, so install and dispatch
// resolved to different slots. That bug was caused by the slot being
// defined in the binary crate and crossing the staticlib boundary
// through extern "C". The .23.10 move lifted scheduler_hooks into this
// crate; CURRENT_PROCESS demonstrates that runtime-crate TLS works fine
// under AOT.
thread_local! {
    static SPAWN_HOOK: Cell<usize> = const { Cell::new(0) };
    static SPAWN_OPT_HOOK: Cell<usize> = const { Cell::new(0) };
    static SEND_HOOK: Cell<usize> = const { Cell::new(0) };
    static MAKE_RESOURCE_HOOK: Cell<usize> = const { Cell::new(0) };
    static TIMER_SCHEDULE_HOOK: Cell<usize> = const { Cell::new(0) };
    static TIMER_CANCEL_HOOK: Cell<usize> = const { Cell::new(0) };
}

pub fn install_spawn_hook(hook: SpawnHook) {
    SPAWN_HOOK.with(|c| c.set(hook as usize));
}

pub fn clear_spawn_hook() {
    SPAWN_HOOK.with(|c| c.set(0));
}

pub fn install_spawn_opt_hook(hook: SpawnOptHook) {
    SPAWN_OPT_HOOK.with(|c| c.set(hook as usize));
}

pub fn clear_spawn_opt_hook() {
    SPAWN_OPT_HOOK.with(|c| c.set(0));
}

pub fn install_send_hook(hook: SendHook) {
    SEND_HOOK.with(|c| c.set(hook as usize));
}

pub fn clear_send_hook() {
    SEND_HOOK.with(|c| c.set(0));
}

pub fn install_timer_schedule_hook(hook: TimerScheduleHook) {
    TIMER_SCHEDULE_HOOK.with(|c| c.set(hook as usize));
}

pub fn clear_timer_schedule_hook() {
    TIMER_SCHEDULE_HOOK.with(|c| c.set(0));
}

pub fn install_timer_cancel_hook(hook: TimerCancelHook) {
    TIMER_CANCEL_HOOK.with(|c| c.set(hook as usize));
}

pub fn clear_timer_cancel_hook() {
    TIMER_CANCEL_HOOK.with(|c| c.set(0));
}

/// Crate-internal dispatchers. Return `None` when the hook is not
/// installed — the caller decides whether absence is fatal. The
/// after-timer path treats absence as "no timer wired" (interp-style
/// indefinite park) so the runtime keeps working in test contexts
/// that don't stand up a Runtime.
pub(crate) fn dispatch_timer_schedule(pid: u32, after_ms: u64) -> Option<u64> {
    let raw = TIMER_SCHEDULE_HOOK.with(|c| c.get());
    if raw == 0 {
        return None;
    }
    let hook: TimerScheduleHook = unsafe { std::mem::transmute(raw) };
    Some(hook(pid, after_ms))
}

/// fz-yxs/fz-st5 — public cancel dispatcher. Called by the binary's
/// sender-probe path (and by the after-timer fire path if a follow-up
/// landing wires it that way) to retire a previously scheduled timer
/// when a matcher hit gets there first. No-op if the hook isn't
/// installed (e.g. unit tests that don't drive a Runtime).
pub fn dispatch_timer_cancel(timer_id: u64) {
    let raw = TIMER_CANCEL_HOOK.with(|c| c.get());
    if raw == 0 {
        return;
    }
    let hook: TimerCancelHook = unsafe { std::mem::transmute(raw) };
    hook(timer_id);
}

pub(crate) fn dispatch_spawn(closure_bits: u64) -> u32 {
    let raw = SPAWN_HOOK.with(|c| c.get());
    if raw == 0 {
        panic!(
            "fz_spawn called outside a Runtime — install_spawn_hook \
             must be called before driving any task"
        );
    }
    let hook: SpawnHook = unsafe { std::mem::transmute(raw) };
    hook(closure_bits)
}

pub(crate) fn dispatch_spawn_opt(closure_bits: u64, min_heap_size: u32) -> u32 {
    let raw = SPAWN_OPT_HOOK.with(|c| c.get());
    if raw == 0 {
        panic!(
            "fz_spawn_opt called outside a Runtime — install_spawn_opt_hook \
             must be called before driving any task"
        );
    }
    let hook: SpawnOptHook = unsafe { std::mem::transmute(raw) };
    hook(closure_bits, min_heap_size)
}

pub(crate) fn dispatch_send(receiver_pid: u32, msg_ref_word: u64) {
    let raw = SEND_HOOK.with(|c| c.get());
    if raw == 0 {
        panic!(
            "fz_send called outside a Runtime — install_send_hook \
             must be called before driving any task"
        );
    }
    let hook: SendHook = unsafe { std::mem::transmute(raw) };
    hook(receiver_pid, msg_ref_word);
}

pub fn install_make_resource_hook(hook: MakeResourceHook) {
    MAKE_RESOURCE_HOOK.with(|c| c.set(hook as usize));
}

pub fn clear_make_resource_hook() {
    MAKE_RESOURCE_HOOK.with(|c| c.set(0));
}

pub(crate) fn dispatch_make_resource(payload_raw: u64, dtor_ref: u64) -> u64 {
    let raw = MAKE_RESOURCE_HOOK.with(|c| c.get());
    if raw == 0 {
        panic!(
            "fz_make_resource called outside a Runtime — \
             install_make_resource_hook must be called before driving any task"
        );
    }
    let hook: MakeResourceHook = unsafe { std::mem::transmute(raw) };
    hook(payload_raw, dtor_ref)
}
