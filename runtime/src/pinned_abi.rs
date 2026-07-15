//! Rust-to-generated-code call wrappers for Cranelift's pinned register.
//!
//! Cranelift removes the pinned register from generated functions'
//! callee-saved set. These wrappers preserve Rust's caller state while a
//! scheduler dispatch runs with the current `Process*` installed in that
//! register.

use crate::process::Process;
use std::arch::asm;

/// # Safety
/// `func` must point to a finalized generated function with the matching
/// Tail-CC entry signature, and `process` must be a valid pointer to a live
/// `Process` that outlives the call — it is installed in the pinned register
/// for the call's duration while the host's register value is saved/restored.
#[cfg(target_arch = "aarch64")]
pub unsafe fn call1(func: *const u8, process: *mut Process, a0: u64) -> i64 {
    let ret: i64;
    unsafe {
        asm!(
            "str x21, [sp, #-16]!",
            "mov x21, {process}",
            "blr {func}",
            "ldr x21, [sp], #16",
            func = in(reg) func,
            process = in(reg) process,
            inout("x0") a0 => ret,
            // x21 is hardcoded scratch inside the template (it carries the
            // pinned-register value across the `blr`); it must be reserved
            // here so the allocator can't also hand it to `func`/`process`.
            // Left unreserved, `func` can land in x21 and the `mov x21,
            // {process}` clobbers it before `blr {func}` substitutes to
            // `blr x21` — jumping through the process pointer instead of
            // the callee, a release-only miscompile (register choice is
            // optimization-level-dependent).
            out("x21") _,
            clobber_abi("C"),
        );
    }
    ret
}

/// # Safety
/// `func` must point to a finalized generated function with the matching
/// Tail-CC entry signature, and `process` must be a valid pointer to a live
/// `Process` that outlives the call — it is installed in the pinned register
/// for the call's duration while the host's register value is saved/restored.
#[cfg(target_arch = "aarch64")]
pub unsafe fn call2(func: *const u8, process: *mut Process, a0: u64, a1: u64) -> i64 {
    let ret: i64;
    unsafe {
        asm!(
            "str x21, [sp, #-16]!",
            "mov x21, {process}",
            "blr {func}",
            "ldr x21, [sp], #16",
            func = in(reg) func,
            process = in(reg) process,
            inout("x0") a0 => ret,
            in("x1") a1,
            // See call1: x21 is hardcoded scratch in the template and must
            // be reserved so `func`/`process` can't be allocated there and
            // get clobbered by `mov x21, {process}` before the `blr`.
            out("x21") _,
            clobber_abi("C"),
        );
    }
    ret
}

/// # Safety
/// `func` must point to a finalized generated function with the matching
/// Tail-CC entry signature, and `process` must be a valid pointer to a live
/// `Process` that outlives the call — it is installed in the pinned register
/// for the call's duration while the host's register value is saved/restored.
#[cfg(target_arch = "x86_64")]
pub unsafe fn call1(func: *const u8, process: *mut Process, a0: u64) -> i64 {
    let ret: i64;
    unsafe {
        asm!(
            "sub rsp, 16",
            "mov [rsp], r15",
            "mov r15, {process}",
            "call {func}",
            "mov r15, [rsp]",
            "add rsp, 16",
            func = in(reg) func,
            process = in(reg) process,
            inout("rdi") a0 => _,
            lateout("rax") ret,
            // r15 is hardcoded scratch in the template; reserve it so the
            // allocator can't hand it to `func`/`process` too (see call1's
            // aarch64 twin for the collision this prevents).
            out("r15") _,
            clobber_abi("C"),
        );
    }
    ret
}

/// # Safety
/// `func` must point to a finalized generated function with the matching
/// Tail-CC entry signature, and `process` must be a valid pointer to a live
/// `Process` that outlives the call — it is installed in the pinned register
/// for the call's duration while the host's register value is saved/restored.
#[cfg(target_arch = "x86_64")]
pub unsafe fn call2(func: *const u8, process: *mut Process, a0: u64, a1: u64) -> i64 {
    let ret: i64;
    unsafe {
        asm!(
            "sub rsp, 16",
            "mov [rsp], r15",
            "mov r15, {process}",
            "call {func}",
            "mov r15, [rsp]",
            "add rsp, 16",
            func = in(reg) func,
            process = in(reg) process,
            inout("rdi") a0 => _,
            inout("rsi") a1 => _,
            lateout("rax") ret,
            // See call1: r15 is hardcoded scratch and must be reserved.
            out("r15") _,
            clobber_abi("C"),
        );
    }
    ret
}

/// # Safety
/// `func` must point to a finalized generated function with the matching
/// Tail-CC entry signature. This portable fallback cannot pin `process`, so
/// callers that depend on the pinned register are unsupported on this arch.
#[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
pub unsafe fn call1(func: *const u8, _process: *mut Process, a0: u64) -> i64 {
    use std::mem::transmute;
    let f: extern "C" fn(u64) -> i64 = unsafe { transmute(func) };
    f(a0)
}

/// # Safety
/// `func` must point to a finalized generated function with the matching
/// Tail-CC entry signature. This portable fallback cannot pin `process`, so
/// callers that depend on the pinned register are unsupported on this arch.
#[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
pub unsafe fn call2(func: *const u8, _process: *mut Process, a0: u64, a1: u64) -> i64 {
    use std::mem::transmute;
    let f: extern "C" fn(u64, u64) -> i64 = unsafe { transmute(func) };
    f(a0, a1)
}
