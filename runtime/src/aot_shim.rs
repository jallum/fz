//! Runtime entry point for AOT-compiled fz binaries (fz-siu.6.1).
//!
//! AOT codegen emits a C-callable `main` that drives the cps-in-clif
//! execution model:
//!
//!   1. `proc = fz_aot_setup(atom_blob, atom_blob_len, halt_cont_body_addr)`
//!   2. for each static closure target:
//!         `fz_aot_register_static_closure(proc, cl_sid, fn_id, code_addr)`
//!   3. `exit = fz_aot_run_main(proc, main_fp, main_entry_addr)`
//!   4. `return exit`
//!
//! `fz_main_entry`, `fz_halt_cont_body`, and the Tail-CC `fz_fn_<id>`
//! bodies are emitted as Local symbols in the same object — the C main
//! resolves them via `func_addr` and passes them by raw pointer. No
//! per-program dispatch / frame-size shim, no trampoline.
//!
//! Concurrency (spawn / send / receive) is wired in fz-siu.6.2 — the
//! non-concurrent §8 fixtures only need this skeleton.

use crate::heap::SchemaRegistry;
use crate::process::{Process, CURRENT_PROCESS};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

// ----- AOT scheduler state -----
//
// AOT_TASKS / AOT_SCHEMAS / AOT_NEXT_PID exist to support the spawn / send
// hooks reinstated in fz-siu.6.2. For .6.1 they are populated for the main
// process only; the hooks themselves are wired in the follow-up.

thread_local! {
    static AOT_NEXT_PID: std::cell::Cell<u32> = const { std::cell::Cell::new(2) };
    static AOT_TASKS: RefCell<HashMap<u32, Box<Process>>> =
        RefCell::new(HashMap::new());
    static AOT_SCHEMAS: RefCell<Option<Rc<RefCell<SchemaRegistry>>>> =
        const { RefCell::new(None) };
}

/// Decode an atom-name blob emitted by AOT codegen into a `Vec<String>`.
/// Format: NUL-terminated UTF-8 names, double-NUL terminator. Null
/// pointer / empty blob yields an empty Vec.
fn parse_atom_blob(blob: *const u8) -> Vec<String> {
    let mut out = Vec::new();
    if blob.is_null() {
        return out;
    }
    let mut cur = blob;
    loop {
        let mut len = 0usize;
        loop {
            let b = unsafe { *cur.add(len) };
            if b == 0 {
                break;
            }
            len += 1;
            if len > 1_000_000 {
                eprintln!("parse_atom_blob: name length exceeded sanity limit");
                std::process::abort();
            }
        }
        if len == 0 {
            break;
        }
        let bytes = unsafe { std::slice::from_raw_parts(cur, len) };
        match std::str::from_utf8(bytes) {
            Ok(s) => out.push(s.to_string()),
            Err(_) => out.push(String::new()),
        }
        cur = unsafe { cur.add(len + 1) };
    }
    out
}

/// AOT setup: create the main Process, install it as CURRENT_PROCESS,
/// initialize the halt-cont singleton, parse the atom blob. Returns the
/// process pointer for subsequent register/run calls. `atom_blob` may be
/// null (program has no atom literals); `atom_blob_len` is currently
/// advisory — parsing terminates on the double-NUL sentinel.
#[unsafe(no_mangle)]
pub extern "C" fn fz_aot_setup(
    atom_blob: *const u8,
    _atom_blob_len: u32,
    halt_cont_body_addr: *const u8,
) -> *mut Process {
    AOT_NEXT_PID.with(|c| c.set(2));
    AOT_TASKS.with(|c| c.borrow_mut().clear());

    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    AOT_SCHEMAS.with(|s| *s.borrow_mut() = Some(schemas.clone()));

    let mut proc_box = Box::new(Process::new(schemas));
    proc_box.pid = 1;
    proc_box.atom_names = parse_atom_blob(atom_blob);
    proc_box.init_halt_cont_singleton(halt_cont_body_addr);

    let proc_ptr = AOT_TASKS.with(|c| {
        let mut t = c.borrow_mut();
        t.insert(1, proc_box);
        t.get_mut(&1).map(|b| b.as_mut() as *mut Process).unwrap()
    });
    CURRENT_PROCESS.with(|c| c.set(proc_ptr));
    proc_ptr
}

/// Register one static closure target. AOT codegen emits one call per
/// `MakeClosure` with zero captures. `code_addr` is the body fn's
/// address (Cranelift `func_addr` of the fz_fn_<body_id>).
#[unsafe(no_mangle)]
pub extern "C" fn fz_aot_register_static_closure(
    proc: *mut Process,
    cl_sid: u32,
    fn_id: u32,
    code_addr: *const u8,
) {
    assert!(!proc.is_null(), "fz_aot_register_static_closure: null process");
    let process = unsafe { &mut *proc };
    process.init_static_closures(&[(cl_sid, fn_id, code_addr)]);
}

/// Run main via the SystemV→Tail-CC `fz_main_entry` shim and tear down
/// the AOT scheduler state. Returns 0 on clean completion (matches the
/// JIT/interp convention of treating halt_value as internal).
#[unsafe(no_mangle)]
pub extern "C" fn fz_aot_run_main(
    proc: *mut Process,
    main_fp: *const u8,
    main_entry_addr: *const u8,
) -> i32 {
    assert!(!proc.is_null(), "fz_aot_run_main: null process");
    assert!(!main_fp.is_null(), "fz_aot_run_main: null main_fp");
    assert!(!main_entry_addr.is_null(), "fz_aot_run_main: null main_entry_addr");

    // fz_main_entry is the SystemV→Tail-CC launch shim. It allocates the
    // halt-cont closure (via fz_get_halt_cont) and `call_indirect Tail`s
    // into main. Runs to halt synchronously; halt_value is set by
    // fz_halt_cont_body before return.
    type MainEntry = extern "C" fn(u64) -> i64;
    let f: MainEntry = unsafe { std::mem::transmute(main_entry_addr) };
    let _ = f(main_fp as u64);

    let _halt = unsafe { (*proc).halt_value };

    // Teardown.
    CURRENT_PROCESS.with(|c| c.set(std::ptr::null_mut()));
    AOT_TASKS.with(|c| c.borrow_mut().clear());
    AOT_SCHEMAS.with(|s| *s.borrow_mut() = None);
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_atom_blob_walks_until_double_nul() {
        let blob = b"ok\0err\0\0";
        let names = parse_atom_blob(blob.as_ptr());
        assert_eq!(names, vec!["ok".to_string(), "err".to_string()]);
    }

    #[test]
    fn parse_atom_blob_null_pointer_returns_empty() {
        let names = parse_atom_blob(std::ptr::null());
        assert!(names.is_empty());
    }
}
