//! Runtime staticlib for fz code (JIT, interp, AOT).
//!
//! Owns the per-task substrate that every execution path shares:
//! AnyValueRef rep (`any_value`), per-task heap (`heap`),
//! Process struct + TLS (`process`), bit-level encoders (`bitstr`),
//! and the JIT/AOT extern "C" FFI surface (`ir_runtime`). AOT-compiled
//! binaries link against this crate as a staticlib; the fz binary
//! links against it as an rlib.

pub mod alloc_site;
pub mod any_value;
pub mod aot_shim;
pub mod bits;
pub mod bitstr;
pub mod clock;
pub mod construction_failure;
pub mod delivery;
pub mod escape;
pub mod exec_ctx;
pub mod extern_binary;
pub mod failure;
pub mod function_denotation;
pub mod handler_stack;
pub mod heap;
pub mod ir_runtime;
pub mod mailbox;
pub mod module_name;
pub mod off_heap;
pub mod output;
pub mod park;
pub mod pinned_abi;
pub mod process;
pub mod process_abi;
pub mod resource;
pub mod reuse_site;
pub mod sched;
pub mod sched_core;
pub mod scheduler_hooks;
pub mod site_table;
pub mod symbol_lookup;
pub mod sync;
pub mod telemetry;
pub mod term;
pub mod term_hash;
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

/// The one function behind every `IO.warn`: hands the message and its
/// location to the process's warning hook.
pub(crate) fn write_warning(
    process: *mut Process,
    message: *const u8,
    message_len: usize,
    file: *const u8,
    file_len: usize,
    line: u32,
) {
    if process.is_null() {
        return;
    }
    let ctx = unsafe { &*process }.ctx;
    if ctx.is_null() {
        return;
    }
    let ctx = unsafe { &*ctx };
    if let Some(warn) = ctx.warn {
        unsafe { warn(ctx.output_context, message, message_len, file, file_len, line) };
    }
}

/// The one function behind every macro-call expansion a macro body asks for:
/// hands the call and the context it stands in to the process's expansion
/// hook. A process with no hook has no compiler to ask.
pub(crate) fn request_expansion(process: *mut Process, ast: u64, context: i64) -> (u64, u64) {
    let no_compiler = (crate::output::Expansion::NO_COMPILER_CODE, 0);
    if process.is_null() {
        return no_compiler;
    }
    let ctx = unsafe { &*process }.ctx;
    if ctx.is_null() {
        return no_compiler;
    }
    let ctx = unsafe { &*ctx };
    let Some(expand) = ctx.expand else {
        return no_compiler;
    };
    let mut expanded = 0u64;
    let code = unsafe { expand(ctx.output_context, ast, context, &mut expanded) };
    (code, expanded)
}
