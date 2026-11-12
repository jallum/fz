//! Runtime staticlib for fz code (JIT, interp, AOT).
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
pub mod delivery;
pub mod exec_ctx;
pub mod extern_binary;
pub mod failure;
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
pub mod sched_core;
pub mod scheduler_hooks;
pub mod symbol_lookup;
pub mod sync;
pub mod telemetry;
pub mod term;
pub mod timer;

use crate::process::Process;

// ---------------------------------------------------------------------------
// C-ABI builtins called from compiled fz code
// ---------------------------------------------------------------------------

/// The one function behind every print: hands exactly `bytes` to the process's
/// output hook. The sink adds nothing, so a caller owns its newline.
pub(crate) fn write_output(process: *mut Process, bytes: &[u8]) {
    if !process.is_null() {
        let ctx = unsafe { &*process }.ctx;
        if !ctx.is_null() {
            let ctx = unsafe { &*ctx };
            if let Some(output) = ctx.output {
                unsafe { output(ctx.output_context, bytes.as_ptr(), bytes.len()) };
            }
        }
    }
}
