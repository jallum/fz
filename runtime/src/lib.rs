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

// ---------------------------------------------------------------------------
// C-ABI builtins called from compiled fz code
// ---------------------------------------------------------------------------

pub(crate) fn emit_print_line(s: String) {
    println!("{}", s);
    // Beyond production stdout, forward the line to the running task's telemetry
    // sink as an observation channel. The sink + callback live on the task's
    // ExecCtx (per-context, not a thread-global); reached via the installed
    // process during a quantum.
    if let Some(process) = crate::process::try_current_process() {
        let ctx = process.ctx;
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
pub extern "C" fn fz_panic(msg_ref: u64) -> ! {
    let value = any_value::AnyValueRef::from_raw_word(msg_ref)
        .ok()
        .and_then(|value| any_value::AnyValue::from_ref(value).ok())
        .unwrap_or(any_value::AnyValue::null());
    eprintln!("fz panic: {}", any_value::debug::render_value(value));
    std::process::abort();
}
