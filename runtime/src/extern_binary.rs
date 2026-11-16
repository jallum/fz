//! Runtime helpers for the `binary` and `c_string` extern marshal
//! classes.
//!
//! Each helper takes tagged heap bits known to the *declaration* to be a
//! binary argument, validates them at runtime, and returns a `*const u8`
//! suitable for passing into a System V C function.
//!
//! Today both helpers do the same thing — return `bytes_ptr` — because every
//! binary's underlying buffer owns its trailing NUL and there
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
//! Both helpers abort with an argument error when the value is not a
//! byte-aligned binary. They predate the process-aware `fz_panic` path and do
//! not participate in its execution-context fault channel.

use crate::any_value::{AnyValueRef, binview_addr_from_tagged};
use crate::bits::{BinView, bitstring_bit_len, bitstring_byte_ptr};
use crate::process::Process;
use std::process::abort;
use std::slice::from_raw_parts;

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
    let is_binary = AnyValueRef::from_raw_word(v).is_ok_and(|value| value.tag().is_binary_repr());
    if !is_binary {
        panic_arg("extern binary/c_string arg: expected a binary value");
    }
    if unsafe { bitstring_bit_len(v) } % 8 != 0 {
        panic_arg("extern binary/c_string arg: non-byte-aligned bitstring");
    }
    unsafe { bitstring_byte_ptr(v) }
}

/// `binary` marshal class: pointer to the bytes; no NUL guarantee.
///
/// # Safety
/// `v` must be tagged heap bits for a binary-like value.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_binary_as_ptr(v: u64) -> *const u8 {
    unsafe { coerce_binary_ptr(v) }
}

/// `c_string` marshal class: pointer to the bytes with a guaranteed
/// trailing NUL. A binary's buffer carries one invisible NUL after its last
/// byte, so a binary whose bytes end where its buffer ends is handed over as
/// it is. A view that ends earlier has no NUL after it and is copied into a
/// fresh binary on `process`'s heap, which does. Nothing roots that copy, and
/// nothing needs to: the collector runs only between quanta, and an extern
/// call cannot end one, so the copy outlives the call it is handed to.
///
/// # Safety
/// `process` must be the live current process and `v` tagged heap bits for a
/// binary-like value.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_binary_as_cstring(process: *mut Process, v: u64) -> *const u8 {
    let bytes = unsafe { coerce_binary_ptr(v) };
    let Some(addr) = binview_addr_from_tagged(v) else {
        return bytes;
    };
    let view = unsafe { BinView::from_raw(addr) };
    if view.ends_at_buffer_end() {
        return bytes;
    }
    let bytes = unsafe { from_raw_parts(bytes, view.bytes_len()) };
    let copy = unsafe { &mut *process }.heap.alloc_bitstring(bytes, view.bit_len());
    unsafe { bitstring_byte_ptr(copy.heap_object_word().expect("a copied binary is a heap object")) }
}

#[cfg(test)]
#[path = "extern_binary_test.rs"]
mod extern_binary_test;
