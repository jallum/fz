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
pub mod extern_binary;
pub mod extern_variadic;
pub mod heap;
pub mod ir_runtime;
pub mod park;
pub mod procbin;
pub mod process;
pub mod resource;
pub mod sched;
pub mod scheduler_hooks;
pub mod sync;
pub mod timer;
pub mod yield_flag;

// ---------------------------------------------------------------------------
// C-ABI builtins called from compiled fz code
// ---------------------------------------------------------------------------

// fz-ul4.27.7 (VR.5b): typed print helpers. The JIT routes Kernel.dbg
// to fz_print_i64 / fz_print_f64 when ir_planner narrows the arg, skipping the
// boxing round-trip through `fz_dbg_value`. Each helper also pushes to
// `TEST_CAPTURE` so cargo-test assertions work the same way regardless of
// which entry point the JIT picked.

pub(crate) fn emit_print_line(s: String) {
    println!("{}", s);
    crate::ir_runtime::TEST_CAPTURE.with(|c| c.borrow_mut().push(s));
}

pub(crate) fn format_f64_for_print(x: f64) -> String {
    if x.is_finite() && x.fract() == 0.0 {
        format!("{:.1}", x)
    } else {
        format!("{}", x)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_print_i64(n: i64) {
    emit_print_line(n.to_string());
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_print_f64(x: f64) {
    emit_print_line(format_f64_for_print(x));
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
