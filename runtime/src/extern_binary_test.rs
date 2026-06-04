use super::*;
use crate::heap::{Heap, SIZE_TABLE, SchemaRegistry};
use std::cell::RefCell;
use std::env::{current_exe, var};
use std::process::{Command, exit};
use std::rc::Rc;
use std::slice::from_raw_parts;

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
        let read = from_raw_parts(bp, payload.len());
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
        let read = from_raw_parts(bp, payload.len());
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
    // Re-invoke the same test binary with an env flag so a child
    // process performs the call and aborts.
    if var("FZ_EB_ABORT_NON_BIN").is_ok() {
        unsafe {
            let _ = fz_binary_as_ptr(42);
        }
        // Unreachable; coerce_binary_ptr should abort.
        exit(0);
    }
    let exe = current_exe().expect("current_exe");
    // Locate this test by its own module path so a module rename can't
    // silently desync the child's --exact filter. The stale "tests" path
    // left over from splitting tests into their own module matched no
    // tests, so the child ran nothing and exited 0 instead of aborting.
    let self_path = format!("{}::non_binary_aborts_in_subprocess", module_path!());
    // libtest's --exact names omit the crate; module_path! includes it.
    let filter = self_path.split_once("::").map_or(self_path.as_str(), |(_, rest)| rest);
    let out = Command::new(exe)
        .env("FZ_EB_ABORT_NON_BIN", "1")
        .args(["--exact", filter])
        .output()
        .expect("spawn child");
    // The child should not exit cleanly — coerce_binary_ptr aborts.
    // cargo's libtest harness captures stderr unless --nocapture, so
    // we only assert the non-zero status here. The integration fixture
    // in [[fz-vw1]] exercises the arg-exception message end-to-end.
    assert!(!out.status.success(), "child must abort, got {:?}", out.status);
}
