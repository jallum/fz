//! Runtime entry point for AOT-compiled fz binaries (fz-siu.6.1 / .6.2).
//!
//! AOT codegen emits a C-callable `main` that drives the cps-in-clif
//! execution model:
//!
//!   1. `proc = fz_aot_setup(atom_blob, atom_blob_len, halt_cont_body_addr,
//!                            spawn_entry_addr, resume_park_addr)`
//!   2. for each static closure target:
//!         `fz_aot_register_static_closure(proc, cl_sid, fn_id, code_addr)`
//!   3. `exit = fz_aot_run_main(proc, main_fp, main_entry_addr)`
//!   4. `return exit`
//!
//! `fz_main_entry`, `fz_halt_cont_body`, `fz_spawn_entry`, `fz_resume_park`,
//! and the Tail-CC `fz_fn_<id>` bodies are emitted as Local symbols in the
//! same object — the C main resolves each via `func_addr` and passes them
//! by raw pointer. No per-program dispatch / frame-size shim, no trampoline.
//!
//! Concurrency: a cooperative run-queue scheduler (fz-sched.1/2). Spawned
//! processes are enqueued and driven by `aot_run_queue_loop` in
//! `fz_aot_run_main`. `fz_receive_park` parks a process (sets state =
//! Blocked / Ready); `aot_send_hook` wakes Blocked receivers. This matches
//! the JIT's `run_until_idle` semantics.

use crate::fz_value::FzValue;
use crate::heap::SchemaRegistry;
use crate::process::{CURRENT_PROCESS, Process, ProcessState};
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

// ----- AOT scheduler state -----

thread_local! {
    static AOT_NEXT_PID: Cell<u32> = const { Cell::new(2) };
    static AOT_TASKS: RefCell<HashMap<u32, Box<Process>>> =
        RefCell::new(HashMap::new());
    static AOT_SCHEMAS: RefCell<Option<Rc<RefCell<SchemaRegistry>>>> =
        const { RefCell::new(None) };
    /// SystemV→Tail-CC shim addresses captured at setup.
    static AOT_SPAWN_ENTRY: Cell<*const u8> = const { Cell::new(std::ptr::null()) };
    static AOT_RESUME_PARK: Cell<*const u8> = const { Cell::new(std::ptr::null()) };
    /// fz-ul4.27.22.3 — three halt_cont_body addrs retained so spawned
    /// children can initialize their own halt_cont_singletons.
    static AOT_HALT_CONT_BODIES: Cell<[*const u8; 3]> =
        const { Cell::new([std::ptr::null(); 3]) };
    /// fz-sched.1 — cooperative run-queue. PIDs of processes ready to run.
    static AOT_RUN_QUEUE: RefCell<VecDeque<u32>> = RefCell::new(VecDeque::new());
    /// fz-sched.1 — fz_main_entry shim address and halt cont, stored so the
    /// run-queue loop can dispatch main's initial quantum.
    static AOT_MAIN_ENTRY: Cell<*const u8> = const { Cell::new(std::ptr::null()) };
    static AOT_HALT_CL: Cell<u64> = const { Cell::new(0) };
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
/// initialize the halt-cont singleton, register the spawn / resume shim
/// addresses, install scheduler hooks, parse the atom blob. Returns the
/// process pointer for subsequent register/run calls. `atom_blob` may be
/// null (program has no atom literals); `atom_blob_len` is currently
/// advisory — parsing terminates on the double-NUL sentinel.
#[unsafe(no_mangle)]
pub extern "C" fn fz_aot_setup(
    atom_blob: *const u8,
    _atom_blob_len: u32,
    halt_cont_body_tagged: *const u8,
    halt_cont_body_i64: *const u8,
    halt_cont_body_f64: *const u8,
    spawn_entry_addr: *const u8,
    resume_park_addr: *const u8,
) -> *mut Process {
    AOT_NEXT_PID.with(|c| c.set(2));
    AOT_TASKS.with(|c| c.borrow_mut().clear());
    AOT_RUN_QUEUE.with(|q| q.borrow_mut().clear());
    AOT_SPAWN_ENTRY.with(|c| c.set(spawn_entry_addr));
    AOT_RESUME_PARK.with(|c| c.set(resume_park_addr));
    AOT_MAIN_ENTRY.with(|c| c.set(std::ptr::null()));
    AOT_HALT_CL.with(|c| c.set(0));
    let body_addrs: [*const u8; 3] = [
        halt_cont_body_tagged,
        halt_cont_body_i64,
        halt_cont_body_f64,
    ];
    AOT_HALT_CONT_BODIES.with(|c| c.set(body_addrs));

    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    AOT_SCHEMAS.with(|s| *s.borrow_mut() = Some(schemas.clone()));

    let mut proc_box = Box::new(Process::new(schemas));
    proc_box.pid = 1;
    proc_box.atom_names = parse_atom_blob(atom_blob);
    proc_box.init_halt_cont_singletons(body_addrs);

    let proc_ptr = AOT_TASKS.with(|c| {
        let mut t = c.borrow_mut();
        t.insert(1, proc_box);
        t.get_mut(&1).map(|b| b.as_mut() as *mut Process).unwrap()
    });
    CURRENT_PROCESS.with(|c| c.set(proc_ptr));

    // Install scheduler hooks so fz_spawn / fz_send (in ir_runtime) dispatch
    // back to the AOT eager-sync handlers.
    crate::scheduler_hooks::install_spawn_hook(aot_spawn_hook);
    crate::scheduler_hooks::install_spawn_opt_hook(aot_spawn_opt_hook);
    crate::scheduler_hooks::install_send_hook(aot_send_hook);

    proc_ptr
}

/// Register one static closure target. AOT codegen emits one call per
/// `MakeClosure` with zero captures. `code_addr` is the body fn's
/// address (Cranelift `func_addr` of the fz_fn_<body_id>).
/// # Safety
/// `proc` must point at a valid `Process` produced by `fz_aot_setup`.
/// `code_addr` must point at a Cranelift-emitted closure-target body.
/// Called only from the AOT-emitted C `main`; clippy's
/// `not_unsafe_ptr_arg_deref` is silenced because the C ABI signature
/// is fixed by AOT codegen.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_aot_register_static_closure(
    proc: *mut Process,
    cl_sid: u32,
    fn_id: u32,
    code_addr: *const u8,
    halt_kind: u32,
) {
    assert!(
        !proc.is_null(),
        "fz_aot_register_static_closure: null process"
    );
    let process = unsafe { &mut *proc };
    process.init_static_closures(&[(cl_sid, fn_id, code_addr, halt_kind)]);
}

/// Spawn hook (fz-siu.6.2). Allocates a child Process, deep-copies the
/// closure into its heap, then dispatches `fz_spawn_entry` to run the
/// child synchronously to halt. The child may itself spawn / send /
/// receive; receive on an empty mailbox parks via fz_receive_park,
/// which under eager-sync means deadlock — aborted by fz_aot_run_main.
extern "C" fn aot_spawn_hook(closure_bits: u64) -> u32 {
    let pid = AOT_NEXT_PID.with(|c| {
        let p = c.get();
        c.set(p + 1);
        p
    });

    let parent_ptr = CURRENT_PROCESS.with(|c| c.get());
    assert!(!parent_ptr.is_null(), "aot_spawn_hook: no current process");
    let parent = unsafe { &*parent_ptr };
    let schemas = parent.heap.schemas_registry();
    let halt_cont_body_addrs = AOT_HALT_CONT_BODIES.with(|c| c.get());
    let static_closures = parent.static_closures.clone();

    let mut child = Box::new(Process::new(schemas));
    child.pid = pid;
    child.atom_names = parent.atom_names.clone();
    child.init_halt_cont_singletons(halt_cont_body_addrs);
    // Share parent's static-closure singleton pointers. Their backing
    // buffers (Box<[u64;3]>) live in `parent.static_closure_bufs` and
    // outlive every child under eager-sync.
    child.static_closures = static_closures;

    // Deep-copy the closure into the child's heap.
    let mut forwarding = HashMap::new();
    let copied = crate::heap::deep_copy_value(
        FzValue(closure_bits),
        &parent.heap,
        &mut child.heap,
        &mut forwarding,
    );
    let copied_ptr = copied
        .unbox_ptr()
        .expect("aot_spawn_hook: closure must be a heap ptr");

    let child_ptr = AOT_TASKS.with(|c| {
        let mut t = c.borrow_mut();
        t.insert(pid, child);
        t.get_mut(&pid).map(|b| b.as_mut() as *mut Process).unwrap()
    });

    // Dispatch via fz_spawn_entry under the child's CURRENT_PROCESS.
    let prev = CURRENT_PROCESS.with(|c| c.replace(child_ptr));
    let spawn_entry_addr = AOT_SPAWN_ENTRY.with(|c| c.get());
    assert!(
        !spawn_entry_addr.is_null(),
        "aot_spawn_hook: spawn_entry not set"
    );
    type SpawnEntry = extern "C" fn(u64) -> i64;
    let f: SpawnEntry = unsafe { std::mem::transmute(spawn_entry_addr) };
    let _ = f(copied_ptr as u64);

    // Drain any parked-then-Ready chain on the child (e.g., self-send +
    // receive). Mirrors fz_aot_run_main's loop below at the child scope.
    drain_parked_chain(child_ptr);

    CURRENT_PROCESS.with(|c| c.set(prev));
    pid
}

/// fz-siu.12: spawn_opt hook. v1 ignores min_heap_size; delegates to aot_spawn_hook.
extern "C" fn aot_spawn_opt_hook(closure_bits: u64, _min_heap_size: u32) -> u32 {
    aot_spawn_hook(closure_bits)
}

/// Send hook (fz-siu.6.2). Pushes a message into the receiver's mailbox.
/// Receiver pid must be registered in AOT_TASKS (parent is pid 1; spawn
/// allocates fresh pids).
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

/// Drains the parked-then-Ready chain on the given process: while it
/// has a parked_cont AND a waiting message, dispatch via fz_resume_park.
/// Each call may set parked_cont again (chained Receives); loop until
/// either parked_cont clears (halt) or the mailbox is empty (Blocked).
fn drain_parked_chain(proc: *mut Process) {
    let resume_park_addr = AOT_RESUME_PARK.with(|c| c.get());
    if resume_park_addr.is_null() {
        return;
    }
    type ResumePark = extern "C" fn(u64, u64) -> i64;
    let resume: ResumePark = unsafe { std::mem::transmute(resume_park_addr) };
    loop {
        let p = unsafe { &mut *proc };
        if p.parked_cont.is_null() {
            return;
        }
        let Some(msg) = p.mailbox.pop_front() else {
            eprintln!(
                "aot: process pid {} blocked on receive with empty mailbox \
                 (no preempt-and-resume in AOT eager-sync v1)",
                p.pid,
            );
            std::process::abort();
        };
        let cont = p.parked_cont;
        p.parked_cont = std::ptr::null_mut();
        let _ = resume(msg.0, cont as u64);
    }
}

/// Run main and all spawned processes via the cooperative run-queue, then
/// tear down AOT scheduler state. Returns 0 on clean completion.
/// # Safety
/// `proc`, `main_fp`, `main_entry_addr` must be valid pointers produced
/// by AOT codegen and `fz_aot_setup`. Called only from the AOT-emitted
/// C `main`; clippy's `not_unsafe_ptr_arg_deref` is silenced because
/// the C ABI signature is fixed.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_aot_run_main(
    proc: *mut Process,
    main_fp: *const u8,
    main_entry_addr: *const u8,
) -> i32 {
    assert!(!proc.is_null(), "fz_aot_run_main: null process");
    assert!(!main_fp.is_null(), "fz_aot_run_main: null main_fp");
    assert!(
        !main_entry_addr.is_null(),
        "fz_aot_run_main: null main_entry_addr"
    );

    // fz-ul4.27.22.3 — Tagged halt-cont for AOT main.
    let halt_cl = unsafe { (*proc).halt_cont_singletons[0] } as u64;

    // Store shim addr + halt_cl so the run-queue loop can dispatch main.
    AOT_MAIN_ENTRY.with(|c| c.set(main_entry_addr));
    AOT_HALT_CL.with(|c| c.set(halt_cl));

    // Seed the queue with main's initial dispatch.
    unsafe { (*proc).pending_main_entry = main_fp as *mut u8 };
    AOT_RUN_QUEUE.with(|q| q.borrow_mut().push_back(1));

    aot_run_queue_loop();

    // Teardown.
    crate::scheduler_hooks::clear_spawn_hook();
    crate::scheduler_hooks::clear_send_hook();
    AOT_SPAWN_ENTRY.with(|c| c.set(std::ptr::null()));
    AOT_RESUME_PARK.with(|c| c.set(std::ptr::null()));
    AOT_MAIN_ENTRY.with(|c| c.set(std::ptr::null()));
    AOT_HALT_CL.with(|c| c.set(0));
    AOT_HALT_CONT_BODIES.with(|c| c.set([std::ptr::null(); 3]));
    CURRENT_PROCESS.with(|c| c.set(std::ptr::null_mut()));
    AOT_TASKS.with(|c| c.borrow_mut().clear());
    AOT_RUN_QUEUE.with(|q| q.borrow_mut().clear());
    AOT_SCHEMAS.with(|s| *s.borrow_mut() = None);
    0
}

/// Cooperative run-queue loop. Drives all enqueued processes to completion
/// or Blocked state. Each iteration pops one pid, dispatches one quantum,
/// and re-enqueues if the process self-sent (state == Ready).
///
/// Dispatch priority (checked in order):
///   1. pending_main_entry — initial main dispatch via fz_main_entry shim
///   2. pending_closure_entry — initial spawn dispatch via fz_spawn_entry shim
///   3. parked_cont + message in mailbox — resume via fz_resume_park
fn aot_run_queue_loop() {
    let main_entry_addr = AOT_MAIN_ENTRY.with(|c| c.get());
    let spawn_entry_addr = AOT_SPAWN_ENTRY.with(|c| c.get());
    let resume_park_addr = AOT_RESUME_PARK.with(|c| c.get());
    let halt_cl = AOT_HALT_CL.with(|c| c.get());

    loop {
        let pid = match AOT_RUN_QUEUE.with(|q| q.borrow_mut().pop_front()) {
            Some(p) => p,
            None => break,
        };

        let proc_ptr = AOT_TASKS.with(|c| {
            c.borrow()
                .get(&pid)
                .map(|b| b.as_ref() as *const Process as *mut Process)
        })
        .unwrap_or_else(|| {
            eprintln!("aot_run_queue_loop: pid {} not in tasks", pid);
            std::process::abort();
        });

        let prev = CURRENT_PROCESS.with(|c| c.replace(proc_ptr));

        // Mark Running so a clean halt (no fz_receive_park call) is
        // distinguishable from Blocked/Ready after dispatch.
        unsafe { (*proc_ptr).state = ProcessState::Running };

        if !unsafe { (*proc_ptr).pending_main_entry }.is_null() {
            let main_fp = unsafe { (*proc_ptr).pending_main_entry };
            unsafe { (*proc_ptr).pending_main_entry = std::ptr::null_mut() };
            type MainEntry = extern "C" fn(u64, u64) -> i64;
            let f: MainEntry = unsafe { std::mem::transmute(main_entry_addr) };
            let _ = f(main_fp as u64, halt_cl);
        } else if !unsafe { (*proc_ptr).pending_closure_entry }.is_null() {
            let closure_ptr = unsafe { (*proc_ptr).pending_closure_entry };
            unsafe { (*proc_ptr).pending_closure_entry = std::ptr::null_mut() };
            type SpawnEntry = extern "C" fn(u64) -> i64;
            let f: SpawnEntry = unsafe { std::mem::transmute(spawn_entry_addr) };
            let _ = f(closure_ptr as u64);
        } else if !unsafe { (*proc_ptr).parked_cont }.is_null() {
            let msg = unsafe { (*proc_ptr).mailbox.pop_front() }.unwrap_or_else(|| {
                eprintln!(
                    "aot_run_queue_loop: pid {} enqueued with parked_cont but empty mailbox",
                    pid
                );
                std::process::abort();
            });
            let cont = unsafe { (*proc_ptr).parked_cont };
            unsafe { (*proc_ptr).parked_cont = std::ptr::null_mut() };
            type ResumePark = extern "C" fn(u64, u64) -> i64;
            let resume: ResumePark = unsafe { std::mem::transmute(resume_park_addr) };
            let _ = resume(msg.0, cont as u64);
        }

        // Post-quantum: re-enqueue on self-send; leave Blocked in registry.
        let state = unsafe { (*proc_ptr).state };
        if state == ProcessState::Ready {
            AOT_RUN_QUEUE.with(|q| q.borrow_mut().push_back(pid));
        }

        CURRENT_PROCESS.with(|c| c.set(prev));
    }
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
