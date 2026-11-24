//! Runtime helpers for the `binary` and `c_string` extern marshal
//! classes.
//!
//! Each helper takes the tagged heap bits of an argument the *declaration*
//! types as a whole-byte binary, so the call has already proved it, and
//! returns a `*const u8` suitable for passing into a System V C function.
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

use crate::any_value::binview_addr_from_tagged;
use crate::bits::{Bin, BinView};
use crate::process::Process;
use std::slice::from_raw_parts;

/// `binary` marshal class: pointer to the bytes; no NUL guarantee.
///
/// # Safety
/// `v` must be tagged heap bits for a binary-like value.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_binary_as_ptr(v: u64) -> *const u8 {
    unsafe { Bin::of_binary(v) }.ptr()
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
    let bytes = unsafe { Bin::of_binary(v) }.ptr();
    let Some(addr) = binview_addr_from_tagged(v) else {
        return bytes;
    };
    let view = unsafe { BinView::from_raw(addr) };
    if view.ends_at_buffer_end() {
        return bytes;
    }
    let bytes = unsafe { from_raw_parts(bytes, view.bytes_len()) };
    let copy = unsafe { &mut *process }.alloc_bitstring(bytes, view.bit_len());
    unsafe { Bin::of_binary(copy.heap_object_word().expect("a copied binary is a heap object")) }.ptr()
}

#[cfg(test)]
#[path = "extern_binary_test.rs"]
mod extern_binary_test;
