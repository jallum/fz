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

use std::sync::atomic::{AtomicUsize, Ordering};

/// Non-pointer trampoline sentinel: fz_receive_attempt returns this when
/// the mailbox is empty so the JIT trampoline parks the task instead of
/// dispatching the returned ptr. 0x1 is never 16-aligned so it cannot
/// collide with a real heap pointer. (Originally lived in the binary's
/// ir_codegen.rs; lifted here for fz-ul4.23.10 since both the trampoline
/// — in the binary's CompiledModule::run_internal — and fz_receive_attempt
/// — in this crate — need it.)
pub const YIELD_PTR: u64 = 0x1;

/// fz_spawn FFI signature on the binary side: takes a raw fn_id, returns
/// the new pid as raw u32. (FnId / PidId are u32 newtypes in the binary;
/// the runtime crate uses raw u32 to keep the type out of its surface.)
pub type SpawnHook = extern "C" fn(fn_id: u32) -> u32;

/// fz_send FFI signature on the binary side: takes receiver pid and the
/// message's raw FzValue bits. The binary's send_via_current_runtime
/// handles the deep-copy into the receiver's heap and the wake-up.
pub type SendHook = extern "C" fn(receiver_pid: u32, msg_bits: u64);

// Hook storage. AtomicUsize-backed globals instead of thread_local —
// the thread_local form turned out to expose a subtle issue where the
// `SPAWN_HOOK.with(...)` accessor in install / dispatch sites ended up
// resolving to different TLS slots in AOT-linked binaries (multiple
// `__ZN...SPAWN_HOOK..._tlv$init` symbols with different hashes), so
// install would write into one and dispatch would read from another,
// always-None. A regular static is single-threaded by construction
// (v1 AOT/JIT runtime is single-worker per fz-ul4.19.1) and dodges
// the TLS-instance issue entirely.
static SPAWN_HOOK: AtomicUsize = AtomicUsize::new(0);
static SEND_HOOK: AtomicUsize = AtomicUsize::new(0);

pub fn install_spawn_hook(hook: SpawnHook) {
    SPAWN_HOOK.store(hook as usize, Ordering::SeqCst);
}

pub fn clear_spawn_hook() {
    SPAWN_HOOK.store(0, Ordering::SeqCst);
}

pub fn install_send_hook(hook: SendHook) {
    SEND_HOOK.store(hook as usize, Ordering::SeqCst);
}

pub fn clear_send_hook() {
    SEND_HOOK.store(0, Ordering::SeqCst);
}

pub(crate) fn dispatch_spawn(fn_id: u32) -> u32 {
    let raw = SPAWN_HOOK.load(Ordering::SeqCst);
    if raw == 0 {
        panic!(
            "fz_spawn called outside a Runtime — install_spawn_hook \
             must be called before driving any task"
        );
    }
    let hook: SpawnHook = unsafe { std::mem::transmute(raw) };
    hook(fn_id)
}

pub(crate) fn dispatch_send(receiver_pid: u32, msg_bits: u64) {
    let raw = SEND_HOOK.load(Ordering::SeqCst);
    if raw == 0 {
        panic!(
            "fz_send called outside a Runtime — install_send_hook \
             must be called before driving any task"
        );
    }
    let hook: SendHook = unsafe { std::mem::transmute(raw) };
    hook(receiver_pid, msg_bits);
}
