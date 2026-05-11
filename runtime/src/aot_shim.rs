//! Runtime entry point for AOT-compiled fz binaries (fz-ul4.23.6.2).
//!
//! AOT codegen emits a per-program `main` (C-callable) that calls
//! `fz_aot_run` with three things:
//!
//!   1. `main_schema_id` — the IR FnId of fz's main fn, also used as the
//!      schema_id stamped into the entry frame header.
//!   2. `main_frame_size` — bytes to allocate for main's frame.
//!   3. `dispatch_fn` — a per-program fn that takes a schema_id and
//!      returns the address of the corresponding fz_fn_<N>. AOT codegen
//!      emits this as a switch over every fn id in the module.
//!
//! `fz_aot_run` sets up a Process, installs CURRENT_PROCESS, runs the
//! standard trampoline (same shape as JIT's `CompiledModule::run_internal`),
//! and returns the Process's `halt_value` so the C startup ends with the
//! right exit code.
//!
//! Single-task only at v1: no Runtime, no scheduler hooks. Concurrency
//! (spawn/send/receive) in AOT comes in fz-ul4.23.6.6.

use crate::fz_value::HeapHeader;
use crate::heap::SchemaRegistry;
use crate::ir_runtime::fz_alloc_frame;
use crate::process::{Process, CURRENT_PROCESS};

/// Per-program fn-pointer lookup. AOT codegen emits this as a switch
/// returning each fz_fn_<schema_id>'s address. Returning null is a
/// fatal AOT-build error (schema_id should always resolve).
pub type DispatchFn = extern "C" fn(schema_id: u32) -> *const u8;

/// AOT entry. Drives the same trampoline the JIT uses, but resolves fn
/// pointers via the caller-supplied switch (AOT-emitted) rather than the
/// JIT's in-memory HashMap.
///
/// Returns the Process's halt_value cast to i32 — suitable as the C
/// program's exit code. Callers can `std::process::exit(halt as i32)`
/// or just return from main.
#[unsafe(no_mangle)]
pub extern "C" fn fz_aot_run(
    main_schema_id: u32,
    main_frame_size: u32,
    dispatch: DispatchFn,
) -> i32 {
    let user_schemas =
        std::rc::Rc::new(std::cell::RefCell::new(SchemaRegistry::new()));
    let mut process = Process::new(user_schemas);
    let process_ptr: *mut Process = &mut process;
    let prev = CURRENT_PROCESS.with(|c| c.replace(process_ptr));

    // Allocate entry frame (mirrors run_internal in src/ir_codegen.rs).
    let frame = fz_alloc_frame(main_schema_id, main_frame_size);
    // Continuation pointer slot = null (entry fn). The frame layout is
    // [HeapHeader(16), cont_ptr(8), ...entry_params].
    unsafe {
        let cont_slot = frame.add(16) as *mut *mut u8;
        *cont_slot = std::ptr::null_mut();
    }

    let mut cur = frame;
    let mut iters: usize = 0;
    let cap: usize = 10_000_000;
    while !cur.is_null() {
        iters += 1;
        if iters > cap {
            eprintln!("fz_aot_run: trampoline exceeded {} iterations", cap);
            std::process::abort();
        }
        let header = cur as *const HeapHeader;
        let schema_id = unsafe { (*header).schema_id };
        let fn_ptr = dispatch(schema_id);
        if fn_ptr.is_null() {
            eprintln!("fz_aot_run: dispatch returned null for schema_id {}", schema_id);
            std::process::abort();
        }
        let f: extern "C" fn(*mut u8, *mut u8) -> *mut u8 =
            unsafe { std::mem::transmute(fn_ptr) };
        let ctx = CURRENT_PROCESS.with(|c| c.get()) as *mut u8;
        cur = f(cur, ctx);
        // fz-ul4.23.6.6 will land receive/yield handling. v1 single-task:
        // no YIELD_PTR check.
    }

    let halt = process.halt_value;
    CURRENT_PROCESS.with(|c| c.set(prev));
    halt as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    // Mock "program": one fz_fn that immediately halts by storing 7 in
    // the current Process's halt_value and returning null. Mirrors what
    // a real fz Term::Halt lowers to (via fz_halt FFI).
    extern "C" fn mock_main_fn(_frame: *mut u8, _ctx: *mut u8) -> *mut u8 {
        crate::process::current_process().halt_value = 7;
        std::ptr::null_mut()
    }

    extern "C" fn mock_dispatch(schema_id: u32) -> *const u8 {
        match schema_id {
            42 => mock_main_fn as *const u8,
            _ => std::ptr::null(),
        }
    }

    #[test]
    fn fz_aot_run_drives_trampoline_and_returns_halt_value() {
        let exit_code = fz_aot_run(
            /*main_schema_id=*/ 42,
            /*main_frame_size=*/ 24, // HeapHeader(16) + cont_ptr(8)
            mock_dispatch,
        );
        assert_eq!(exit_code, 7);
    }

    extern "C" fn mock_two_step_fn(frame: *mut u8, _ctx: *mut u8) -> *mut u8 {
        // First call: bump halt_value to 1, hand control back via a fresh
        // frame with a different schema_id. Second call: halt with 9.
        // (We reuse the frame across calls — the trampoline doesn't
        // dictate frame lifetimes; the program does.)
        let header = frame as *mut HeapHeader;
        let cur_id = unsafe { (*header).schema_id };
        if cur_id == 1 {
            unsafe { (*header).schema_id = 2 };
            frame
        } else {
            crate::process::current_process().halt_value = 9;
            std::ptr::null_mut()
        }
    }

    extern "C" fn mock_two_step_dispatch(_schema_id: u32) -> *const u8 {
        mock_two_step_fn as *const u8
    }

    #[test]
    fn fz_aot_run_dispatches_multiple_steps() {
        let exit_code = fz_aot_run(1, 24, mock_two_step_dispatch);
        assert_eq!(exit_code, 9);
    }
}
