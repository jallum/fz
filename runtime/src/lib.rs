//! fz-ul4.23.10 — runtime staticlib for fz code (JIT, interp, AOT).
//!
//! Owns the per-task substrate that every execution path shares:
//! AnyValueRef rep (`any_value`), per-task heap (`heap`),
//! Process struct + TLS (`process`), bit-level encoders (`bitstr`),
//! and the JIT/AOT extern "C" FFI surface (`ir_runtime`). AOT-compiled
//! binaries link against this crate as a staticlib; the fz binary
//! links against it as an rlib.

pub mod any_value;
pub mod aot_shim;
pub mod bitstr;
pub mod exec_ctx;
pub mod extern_binary;
pub mod extern_variadic;
pub mod heap;
pub mod ir_runtime;
pub mod park;
pub mod pinned_abi;
pub mod procbin;
pub mod process;
pub mod process_abi;
pub mod resource;
pub mod sched;
pub mod scheduler_hooks;
pub mod sync;
pub mod timer;

use crate::process::Process;
use any_value::debug::render_value;
use any_value::{AnyValue, AnyValueRef};
use std::process::abort;

// ---------------------------------------------------------------------------
// C-ABI builtins called from compiled fz code
// ---------------------------------------------------------------------------

pub(crate) fn emit_print_line(process: *mut Process, s: String) {
    println!("{}", s);
    // Beyond production stdout, forward the line to the running task's telemetry
    // sink as an observation channel. The sink + callback live on the task's
    // ExecCtx (per-context, not a thread-global); reached via the process the
    // print BIF carries (the value already in the pinned register).
    if !process.is_null() {
        let ctx = unsafe { &*process }.ctx;
        if !ctx.is_null() {
            let ctx = unsafe { &*ctx };
            if let Some(output) = ctx.output {
                output(ctx.tel, s.as_ptr(), s.len());
            }
        }
    }
}

/// Aborts with the fz value rendered to stderr.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_panic(process: *mut Process, msg_ref: u64) -> ! {
    let value = AnyValueRef::from_raw_word(msg_ref)
        .ok()
        .and_then(|value| AnyValue::from_ref(value).ok())
        .unwrap_or(AnyValue::null());
    eprintln!("fz panic: {}", render_value(process, value));
    abort();
}
