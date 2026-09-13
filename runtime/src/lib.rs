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
pub mod function_denotation;
pub mod heap;
pub mod ir_runtime;
pub mod module_name;
pub mod output;
pub mod park;
pub mod pinned_abi;
pub mod procbin;
pub mod process;
pub mod process_abi;
pub mod resource;
pub mod sched;
pub mod scheduler_hooks;
pub mod sync;
pub mod term;
pub mod timer;

use crate::process::Process;
use any_value::debug::render_value;
use any_value::{AnyValue, AnyValueRef};

// ---------------------------------------------------------------------------
// C-ABI builtins called from compiled fz code
// ---------------------------------------------------------------------------

pub(crate) fn emit_print_line(process: *mut Process, s: String) {
    if !process.is_null() {
        let ctx = unsafe { &*process }.ctx;
        if !ctx.is_null() {
            let ctx = unsafe { &*ctx };
            if let Some(output) = ctx.output {
                unsafe { output(ctx.output_context, s.as_ptr(), s.len()) };
            }
        }
    }
}

/// Render the borrowed panic value while its owning process and heap are live.
pub fn render_panic_message(process: *mut Process, msg_ref: u64) -> String {
    let value = AnyValueRef::from_raw_word(msg_ref)
        .ok()
        .and_then(|value| AnyValue::from_ref(value).ok())
        .unwrap_or(AnyValue::null());
    format!("fz panic: {}", render_value(process, value))
}

/// The fault hook for a process whose host has no error channel of its own:
/// render the panic to stderr and let the `never` contract stop the process.
pub const STDERR_FAULT_HOOK: crate::scheduler_hooks::FaultHook = stderr_fault_hook;

extern "C" fn stderr_fault_hook(process: *mut Process, _context: *mut (), value_ref_word: u64) {
    eprintln!("{}", render_panic_message(process, value_ref_word));
}

/// Report a process panic through the execution context. The physical export
/// returns so the interpreter can propagate its owned error without unwinding
/// across C; the source `never` contract supplies the non-continuation policy.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_panic(process: *mut Process, msg_ref: u64) {
    assert!(!process.is_null(), "fz_panic: no current process");
    let ctx = unsafe { (*process).ctx };
    assert!(!ctx.is_null(), "fz_panic: process has no execution context");
    let ctx = unsafe { &*ctx };
    (ctx.fault.expect("fz_panic: fault callback installed"))(process, ctx.scheduler, msg_ref);
}
