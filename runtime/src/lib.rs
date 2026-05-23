//! fz-ul4.23.10 — runtime staticlib for fz code (JIT, interp, AOT).
//!
//! Owns the per-task substrate that every execution path shares:
//! FzValue tagged-pointer rep (`fz_value`), per-task heap (`heap`),
//! Process struct + TLS (`process`), bit-level encoders (`bitstr`),
//! and the JIT/AOT extern "C" FFI surface (`ir_runtime`). AOT-compiled
//! binaries link against this crate as a staticlib; the fz binary
//! links against it as an rlib.

pub mod aot_shim;
pub mod bitstr;
pub mod extern_binary;
pub mod fz_value;
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

// fz-ul4.27.7 (VR.5b): typed print helpers. The JIT routes Prim::Builtin::Print
// to fz_print_i64 / fz_print_f64 when ir_typer narrows the arg, skipping the
// boxing round-trip through `fz_print_value`. Each helper also pushes to
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

/// Aborts with `msg` printed to stderr. `msg_ptr`/`msg_len` describe a UTF-8
/// byte slice; the compiler emits these from a string literal embedded in
/// the binary. Used for case no-match, integer overflow guards (.12.5), etc.
///
/// # Safety
/// `msg_ptr` must point to `msg_len` valid UTF-8 bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_panic(msg_ptr: *const u8, msg_len: usize) -> ! {
    let bytes = unsafe { std::slice::from_raw_parts(msg_ptr, msg_len) };
    let s = std::str::from_utf8(bytes).unwrap_or("<panic message: invalid utf-8>");
    eprintln!("fz panic: {}", s);
    std::process::abort();
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_assert(cond: u64) {
    let v = crate::fz_value::PackedValueWord(cond);
    if v.is_nil() || v.is_false() {
        eprintln!("fz assert failed");
        std::process::abort();
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_assert_eq(a: u64, b: u64) {
    if a != b {
        eprintln!("fz assert_eq failed: values are not equal");
        std::process::abort();
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_assert_neq(a: u64, b: u64) {
    if a == b {
        eprintln!("fz assert_neq failed: values are equal");
        std::process::abort();
    }
}
