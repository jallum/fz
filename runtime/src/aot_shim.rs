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
//! Concurrency (fz-ul4.23.6.6): an eager-synchronous scheduler mirrors
//! the interp's model from fz-ul4.23.5.8. Builtin::Spawn runs the child
//! task to completion synchronously before returning the pid. Term::Send
//! pushes into the receiver's mailbox via the AOT task registry. Doesn't
//! support patterns that need preempt-and-resume across receive points;
//! a real green-thread scheduler is a follow-up.

use crate::fz_value::{FzValue, HeapHeader};
use crate::heap::SchemaRegistry;
use crate::ir_runtime::fz_alloc_frame;
use crate::process::{Process, CURRENT_PROCESS};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

/// Per-program fn-pointer lookup. AOT codegen emits this as a switch
/// returning each fz_fn_<schema_id>'s address. Returning null is a
/// fatal AOT-build error (schema_id should always resolve).
pub type DispatchFn = extern "C" fn(schema_id: u32) -> *const u8;

/// Per-program frame-size lookup. AOT codegen emits this as a switch
/// returning the frame size (in bytes) for each fz_fn_<schema_id>.
/// Returning 0 is a fatal AOT-build error (every fn has a frame size).
pub type FrameSizeFn = extern "C" fn(schema_id: u32) -> u32;

// ----- AOT scheduler state (fz-ul4.23.6.6) -----
//
// Eager-sync model from fz-ul4.23.5.8 — spawn runs the child to
// completion before returning; send pushes into the receiver's mailbox;
// receive on an empty mailbox panics (no preempt-and-resume v1).
//
// The dispatch + frame-size fns are AOT-codegen-emitted per-program;
// the scheduler needs them at spawn time to drive the child's
// trampoline. Stashed in TLS by fz_aot_run.

thread_local! {
    static AOT_DISPATCH: Cell<Option<DispatchFn>> = const { Cell::new(None) };
    static AOT_FRAME_SIZE_FN: Cell<Option<FrameSizeFn>> = const { Cell::new(None) };
    static AOT_FN_COUNT: Cell<u32> = const { Cell::new(0) };
    static AOT_NEXT_PID: Cell<u32> = const { Cell::new(2) };
    static AOT_TASKS: RefCell<HashMap<u32, Box<Process>>> =
        RefCell::new(HashMap::new());
    static AOT_SCHEMAS: RefCell<Option<Rc<RefCell<SchemaRegistry>>>> =
        const { RefCell::new(None) };
}

extern "C" fn aot_spawn_hook(fn_id: u32) -> u32 {
    let pid = AOT_NEXT_PID.with(|c| {
        let p = c.get();
        c.set(p + 1);
        p
    });
    let dispatch = AOT_DISPATCH
        .with(|c| c.get())
        .expect("aot_spawn_hook: AOT_DISPATCH not set");
    let frame_size_fn = AOT_FRAME_SIZE_FN
        .with(|c| c.get())
        .expect("aot_spawn_hook: AOT_FRAME_SIZE_FN not set");
    let fn_count = AOT_FN_COUNT.with(|c| c.get());
    let schemas = AOT_SCHEMAS
        .with(|c| c.borrow().as_ref().cloned())
        .expect("aot_spawn_hook: AOT_SCHEMAS not set");

    let mut child = Box::new(Process::new(schemas));
    child.pid = pid;
    child.frame_sizes = (0..fn_count).map(|id| frame_size_fn(id)).collect();
    let child_ptr = AOT_TASKS.with(|c| {
        let mut t = c.borrow_mut();
        t.insert(pid, child);
        t.get_mut(&pid).map(|b| b.as_mut() as *mut Process).unwrap()
    });

    let entry_frame_size = frame_size_fn(fn_id);
    let prev = CURRENT_PROCESS.with(|c| c.replace(child_ptr));
    drive_trampoline(fn_id, entry_frame_size, dispatch);
    CURRENT_PROCESS.with(|c| c.set(prev));

    pid
}

extern "C" fn aot_send_hook(receiver_pid: u32, msg_bits: u64) {
    AOT_TASKS.with(|c| {
        let mut t = c.borrow_mut();
        match t.get_mut(&receiver_pid) {
            Some(task) => task.mailbox.push_back(FzValue(msg_bits)),
            None => {
                eprintln!("aot_send: no task with pid {}", receiver_pid);
                std::process::abort();
            }
        }
    });
}

/// Drive the JIT-shaped trampoline against the currently-installed
/// CURRENT_PROCESS, using the per-program dispatch fn to resolve
/// schema_id → fn_ptr. Returns when the running task halts
/// (next_frame becomes null).
fn drive_trampoline(entry_schema_id: u32, entry_frame_size: u32, dispatch: DispatchFn) {
    let frame = fz_alloc_frame(entry_schema_id, entry_frame_size);
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
            eprintln!("drive_trampoline: exceeded {} iterations", cap);
            std::process::abort();
        }
        let header = cur as *const HeapHeader;
        let schema_id = unsafe { (*header).schema_id };
        let fn_ptr = dispatch(schema_id);
        if fn_ptr.is_null() {
            eprintln!("drive_trampoline: dispatch returned null for schema_id {}", schema_id);
            std::process::abort();
        }
        let f: extern "C" fn(*mut u8, *mut u8) -> *mut u8 =
            unsafe { std::mem::transmute(fn_ptr) };
        let ctx = CURRENT_PROCESS.with(|c| c.get()) as *mut u8;
        cur = f(cur, ctx);
        // The eager-sync model doesn't yield: send runs before parent's
        // receive (because spawn ran the child synchronously), so the
        // parent's receive finds a message and continues. fz_receive_attempt
        // on empty would return YIELD_PTR (0x1) — we'd loop forever
        // dispatching that. Detect and abort.
        if cur as u64 == crate::scheduler_hooks::YIELD_PTR {
            eprintln!(
                "drive_trampoline: receive on empty mailbox in AOT \
                 (v1 has no preempt-and-resume; spawn must enqueue \
                 a message before any later receive)"
            );
            std::process::abort();
        }
    }
}

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
    frame_size: FrameSizeFn,
    fn_count: u32,
) -> i32 {
    // Stash codegen-emitted lookups in TLS so the scheduler hooks can
    // reach them without threading args through Cranelift's FFI surface.
    AOT_DISPATCH.with(|c| c.set(Some(dispatch)));
    AOT_FRAME_SIZE_FN.with(|c| c.set(Some(frame_size)));
    AOT_FN_COUNT.with(|c| c.set(fn_count));
    AOT_NEXT_PID.with(|c| c.set(2));
    AOT_TASKS.with(|c| c.borrow_mut().clear());

    // Shared SchemaRegistry across main + every spawned child, matching
    // the interp's model (heap pointers passed via messages reference
    // schemas that must resolve in both heaps).
    let user_schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    AOT_SCHEMAS.with(|s| *s.borrow_mut() = Some(user_schemas.clone()));

    // Install scheduler hooks so fz_spawn / fz_send (in this crate's
    // ir_runtime) dispatch back to the AOT eager-sync handlers.
    crate::scheduler_hooks::install_spawn_hook(aot_spawn_hook);
    crate::scheduler_hooks::install_send_hook(aot_send_hook);

    // Main process — register as pid 1.
    let mut main_process = Box::new(Process::new(user_schemas));
    main_process.pid = 1;
    main_process.frame_sizes = (0..fn_count).map(|id| frame_size(id)).collect();
    let main_ptr = AOT_TASKS.with(|c| {
        let mut t = c.borrow_mut();
        t.insert(1, main_process);
        t.get_mut(&1).map(|b| b.as_mut() as *mut Process).unwrap()
    });
    let prev = CURRENT_PROCESS.with(|c| c.replace(main_ptr));

    drive_trampoline(main_schema_id, main_frame_size, dispatch);

    // halt_value is the IR-level main return — we don't propagate it
    // as the C process exit code (JIT and interp drive the same way:
    // halt_value is internal, the wrapping process exits 0 on success).
    // A future fz convention may wire `Halt n` to a non-zero exit but
    // that's a separate ticket.
    let _halt = unsafe { (*main_ptr).halt_value };
    CURRENT_PROCESS.with(|c| c.set(prev));

    // Clean up scheduler state so a second fz_aot_run call (in tests or
    // future embedded scenarios) starts fresh.
    crate::scheduler_hooks::clear_spawn_hook();
    crate::scheduler_hooks::clear_send_hook();
    AOT_DISPATCH.with(|c| c.set(None));
    AOT_FRAME_SIZE_FN.with(|c| c.set(None));
    AOT_FN_COUNT.with(|c| c.set(0));
    AOT_TASKS.with(|c| c.borrow_mut().clear());
    AOT_SCHEMAS.with(|s| *s.borrow_mut() = None);

    0
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

    extern "C" fn mock_frame_size(_schema_id: u32) -> u32 {
        24 // HeapHeader(16) + cont_ptr(8)
    }

    #[test]
    fn fz_aot_run_drives_trampoline_to_completion() {
        let exit_code = fz_aot_run(
            /*main_schema_id=*/ 42,
            /*main_frame_size=*/ 24,
            mock_dispatch,
            mock_frame_size,
            /*fn_count=*/ 43,
        );
        // fz_aot_run returns 0 on clean completion; halt_value is
        // internal (matches JIT/interp's exit-code convention).
        assert_eq!(exit_code, 0);
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
        let exit_code = fz_aot_run(1, 24, mock_two_step_dispatch, mock_frame_size, 3);
        assert_eq!(exit_code, 0);
    }
}
