//! fz-9ss — runtime helpers for the `binary` and `cstring` extern marshal
//! classes.
//!
//! Each helper takes tagged heap bits known to the *declaration* to be a
//! binary argument, validates them at runtime, and returns a `*const u8`
//! suitable for passing into a System V C function.
//!
//! Today both helpers do the same thing — return `bytes_ptr` — because every
//! binary's underlying buffer owns its trailing NUL via [[fz-wu9]] and there
//! are no SubBin slices yet (every slice allocates fresh). The split into two
//! symbols is deliberate so the *call sites* in interp/JIT/AOT commit to the
//! contract today. When SubBin lands, only these helper bodies change:
//!
//!   * `fz_binary_as_ptr` will still hand back the slice's pointer directly
//!     (the slice's pointer + len is C's problem).
//!   * `fz_binary_as_cstring` will additionally check whether the slice ends
//!     at the parent's buffer boundary; if not, allocate a fresh
//!     +1-NUL-padded buffer and copy.
//!
//! Both helpers raise an arg exception (abort with a message, matching the
//! existing `fz_panic` shape) when the value is not a byte-aligned binary.

use crate::any_value::{AnyValueRef, ValueKind, heap_object_word};
use crate::procbin::{bitstring_bit_len, bitstring_byte_ptr, is_bitstring_like};
use std::process::abort;

fn panic_arg(msg: &str) -> ! {
    eprintln!("fz panic: {}", msg);
    abort();
}

/// Validate that `v` is a byte-aligned binary heap value and return its
/// payload pointer. Aborts with an arg-exception message otherwise.
///
/// # Safety
/// `v` must be an any value ref for a binary-like value.
unsafe fn coerce_binary_ptr(v: u64) -> *const u8 {
    let p = match AnyValueRef::from_raw_word(v).ok().and_then(|value| match value.tag() {
        ValueKind::BITSTRING => value
            .bitstring_addr()
            .ok()
            .map(|addr| heap_object_word(addr, ValueKind::BITSTRING) as *mut u8),
        ValueKind::PROCBIN => value
            .procbin_addr()
            .ok()
            .map(|addr| heap_object_word(addr, ValueKind::PROCBIN) as *mut u8),
        _ => None,
    }) {
        Some(p) => p,
        _ => panic_arg("extern binary/cstring arg: expected a binary value"),
    };
    if !unsafe { is_bitstring_like(p) } {
        panic_arg("extern binary/cstring arg: expected a binary value");
    }
    if unsafe { bitstring_bit_len(p) } % 8 != 0 {
        panic_arg("extern binary/cstring arg: non-byte-aligned bitstring");
    }
    unsafe { bitstring_byte_ptr(p) }
}

/// `binary` marshal class: pointer to the bytes; no NUL guarantee.
///
/// # Safety
/// `v` must be tagged heap bits for a binary-like value.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_binary_as_ptr(v: u64) -> *const u8 {
    unsafe { coerce_binary_ptr(v) }
}

/// `cstring` marshal class: pointer to the bytes with a guaranteed
/// trailing NUL. Underwritten by the +1-NUL invariant from [[fz-wu9]].
///
/// # Safety
/// `v` must be tagged heap bits for a binary-like value.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_binary_as_cstring(v: u64) -> *const u8 {
    unsafe { coerce_binary_ptr(v) }
}

#[cfg(test)]
#[path = "extern_binary_test.rs"]
mod extern_binary_test;
