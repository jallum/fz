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

use crate::any_value::AnyValueRef;
use crate::any_value::ValueKind;
use crate::procbin::{bitstring_bit_len, bitstring_byte_ptr, is_bitstring_like};

fn panic_arg(msg: &str) -> ! {
    eprintln!("fz panic: {}", msg);
    std::process::abort();
}

/// Validate that `v` is a byte-aligned binary heap value and return its
/// payload pointer. Aborts with an arg-exception message otherwise.
///
/// # Safety
/// `v` must be an any value ref for a binary-like value.
unsafe fn coerce_binary_ptr(v: u64) -> *const u8 {
    let p = match AnyValueRef::from_raw_word(v)
        .ok()
        .and_then(|value| match value.tag() {
            ValueKind::BITSTRING => value.bitstring_addr().ok().map(|addr| {
                crate::any_value::heap_object_word(addr, crate::any_value::ValueKind::BITSTRING)
                    as *mut u8
            }),
            ValueKind::PROCBIN => value.procbin_addr().ok().map(|addr| {
                crate::any_value::heap_object_word(addr, crate::any_value::ValueKind::PROCBIN)
                    as *mut u8
            }),
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
mod tests {
    use super::*;
    use crate::heap::{Heap, SIZE_TABLE, SchemaRegistry};
    use std::cell::RefCell;
    use std::rc::Rc;

    fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
        Rc::new(RefCell::new(SchemaRegistry::new()))
    }

    /// Heap-allocated inline Bitstring goes through as_ptr cleanly and the
    /// byte at `bytes_len` reads as 0 via the cstring helper.
    #[test]
    fn ptr_and_cstring_on_inline_bitstring() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let payload = b"/tmp/fz-fixture";
        let p = h.alloc_bitstring(payload, (payload.len() as u64) * 8);
        let v = AnyValueRef::from_heap_object(ValueKind::BITSTRING, p)
            .expect("bitstring ref")
            .raw_word();
        unsafe {
            let bp = fz_binary_as_ptr(v);
            assert!(!bp.is_null());
            let read = std::slice::from_raw_parts(bp, payload.len());
            assert_eq!(read, payload);

            let cs = fz_binary_as_cstring(v);
            assert!(!cs.is_null());
            assert_eq!(*cs.add(payload.len()), 0, "trailing NUL must be reachable");
        }
    }

    /// Above-threshold payload routes through ProcBin → SharedBin; both
    /// helpers still work and the NUL is reachable.
    #[test]
    #[serial_test::serial]
    fn ptr_and_cstring_on_procbin() {
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        // Large enough to cross SHARED_BIN_THRESHOLD_BYTES.
        let payload: Vec<u8> = (0..4096u32).map(|i| (i & 0xff) as u8).collect();
        let p = h.alloc_bitstring(&payload, (payload.len() as u64) * 8);
        let v = AnyValueRef::from_heap_object(ValueKind::PROCBIN, p)
            .expect("procbin ref")
            .raw_word();
        unsafe {
            let bp = fz_binary_as_ptr(v);
            let read = std::slice::from_raw_parts(bp, payload.len());
            assert_eq!(read, payload.as_slice());

            let cs = fz_binary_as_cstring(v);
            assert_eq!(*cs.add(payload.len()), 0);
        }
    }

    /// Non-binary AnyValues abort. We can't easily assert abort in a unit
    /// test (it would tear down the test process), so we drive these
    /// cases through a child process via `std::process::Command` only when
    /// requested — under normal `cargo test` we just verify that valid
    /// inputs work. The arg-exception path is exercised end-to-end by the
    /// integration fixture in [[fz-vw1]].
    ///
    /// However we can still confirm one negative shape statically: a raw
    /// integer payload is not a binary heap pointer, which causes
    /// `coerce_binary_ptr` to take the panic branch. We test by dispatching
    /// the call in a forked subprocess so the abort doesn't kill us.
    #[test]
    fn non_binary_aborts_in_subprocess() {
        use std::process::Command;
        // Re-invoke the same test binary with an env flag so a child
        // process performs the call and aborts.
        if std::env::var("FZ_EB_ABORT_NON_BIN").is_ok() {
            unsafe {
                let _ = fz_binary_as_ptr(42);
            }
            // Unreachable; coerce_binary_ptr should abort.
            std::process::exit(0);
        }
        let exe = std::env::current_exe().expect("current_exe");
        let out = Command::new(exe)
            .env("FZ_EB_ABORT_NON_BIN", "1")
            .args([
                "--exact",
                "extern_binary::tests::non_binary_aborts_in_subprocess",
            ])
            .output()
            .expect("spawn child");
        // The child should not exit cleanly — coerce_binary_ptr aborts.
        // cargo's libtest harness captures stderr unless --nocapture, so
        // we only assert the non-zero status here. The integration fixture
        // in [[fz-vw1]] exercises the arg-exception message end-to-end.
        assert!(
            !out.status.success(),
            "child must abort, got {:?}",
            out.status
        );
    }
}
