//! Runtime entry point for AOT-compiled fz binaries (fz-siu.6.1 / .6.2).
//!
//! AOT codegen emits a C-callable `main` that drives the cps-in-clif
//! execution model:
//!
//!   1. `proc = fz_aot_setup(atom_blob, atom_blob_len, halt_cont_body_addr,
//!                            spawn_entry_addr, resume_park_addr)`
//!   2. for each static closure target:
//!      `fz_aot_register_static_closure(proc, cl_sid, fn_id, code_addr)`
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

use crate::fz_value::{FzValue, HeapHeader, HeapKind};
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
    static AOT_RUN_QUEUE: RefCell<VecDeque<u32>> = const { RefCell::new(VecDeque::new()) };
    /// fz-sched.1 — fz_main_entry shim address and halt cont, stored so the
    /// run-queue loop can dispatch main's initial quantum.
    static AOT_MAIN_ENTRY: Cell<*const u8> = const { Cell::new(std::ptr::null()) };
    static AOT_HALT_CL: Cell<u64> = const { Cell::new(0) };
    /// fz-02r.7 — mid-flight resume shim addresses (arg count 0..=8).
    /// Set by fz_aot_set_resume_shims; used by aot_run_queue_loop to resume
    /// a process that yielded at a back-edge after gc_mid_flight.
    static AOT_RESUME_SHIMS: Cell<[*const u8; 9]> =
        const { Cell::new([std::ptr::null(); 9]) };
    /// fz-swt.11 — dtor lookup table baked into the AOT binary at codegen
    /// time. Each entry is `(FnId of a zero-cap closure body, C-ABI fn ptr
    /// of the underlying extern)`. AOT codegen scans the IR module for
    /// closure-target bodies that are thin extern wrappers (the same
    /// shape `resolve_dtor_from_closure` recognises in interp/JIT) and
    /// emits one row per match into a data symbol with function-address
    /// relocations on the fn-ptr slot. `fz_aot_register_dtor_table`
    /// copies the rows into this thread-local table; the AOT
    /// `MakeResourceHook` (`aot_make_resource_hook`) reads the closure
    /// header's `_reserved` field (= fn_id) and does a linear lookup
    /// here, then calls `resource::resource_alloc` + `alloc_resource`
    /// against the current process's heap.
    static AOT_DTOR_TABLE: RefCell<Vec<(u32, *const u8)>> =
        const { RefCell::new(Vec::new()) };
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
    // fz-swt.11 — AOT MakeResourceHook. The dtor lookup table is populated
    // later via `fz_aot_register_dtor_table` (called from the AOT-emitted
    // C main between setup and run_main); the hook itself reads from it
    // each time `fz_make_resource` is called from emitted code.
    crate::scheduler_hooks::install_make_resource_hook(aot_make_resource_hook);

    proc_ptr
}

/// fz-swt.11 — populate the AOT dtor lookup table from a data symbol
/// emitted by AOT codegen. The data block is a packed array of `count`
/// 16-byte rows: `u32 fn_id, u32 _pad, u64 fn_ptr`. `fn_ptr` was
/// emitted as a function-address relocation by `desc.write_function_addr`
/// (see `define_aot_dtor_table` in `ir_codegen.rs`), so the linker
/// already filled in the absolute address of the underlying extern.
///
/// Idempotent: replaces the prior table contents. `table` may be null
/// when `count == 0` (program has no zero-cap closure-target wrappers).
///
/// # Safety
/// `table` must point to `count * 16` bytes of validly-relocated rows
/// when `count > 0`. Called only from the AOT-emitted C main.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_aot_register_dtor_table(table: *const u8, count: u32) {
    let mut rows: Vec<(u32, *const u8)> = Vec::with_capacity(count as usize);
    if count > 0 {
        assert!(
            !table.is_null(),
            "fz_aot_register_dtor_table: null table with count > 0"
        );
        for i in 0..count as usize {
            // Read unaligned: the data section's start is 8-byte aligned by
            // `set_align(8)` in codegen, and each 16-byte row is naturally
            // aligned, but stay defensive on aarch64.
            let base = unsafe { table.add(i * 16) };
            let fn_id = unsafe { std::ptr::read_unaligned(base as *const u32) };
            let fn_ptr = unsafe { std::ptr::read_unaligned(base.add(8) as *const *const u8) };
            rows.push((fn_id, fn_ptr));
        }
    }
    AOT_DTOR_TABLE.with(|c| *c.borrow_mut() = rows);
}

/// fz-swt.11 — AOT `MakeResourceHook` body. Reads the dtor closure's
/// `_reserved` field (set by `fz_alloc_closure` / `init_static_closures`
/// to the closure body's `FnId`), looks the fn_id up in the AOT dtor
/// table populated at startup, and allocates a fresh `Resource` on the
/// current process's heap.
extern "C" fn aot_make_resource_hook(payload: u64, dtor_closure_bits: u64) -> u64 {
    let closure = FzValue(dtor_closure_bits);
    let p = closure.unbox_ptr().unwrap_or_else(|| {
        eprintln!("fz_make_resource (AOT): dtor arg is not a heap value");
        std::process::abort();
    });
    let header: &HeapHeader = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Closure) {
        eprintln!("fz_make_resource (AOT): dtor arg is not a closure");
        std::process::abort();
    }
    let fn_id = header._reserved;
    let dtor_addr = AOT_DTOR_TABLE.with(|c| {
        c.borrow()
            .iter()
            .find_map(|(fid, addr)| if *fid == fn_id { Some(*addr) } else { None })
    });
    let dtor_addr = dtor_addr.unwrap_or_else(|| {
        eprintln!(
            "fz_make_resource (AOT): no dtor table entry for closure fn_id {} \
             — the closure body is not recognised as a thin extern wrapper",
            fn_id
        );
        std::process::abort();
    });
    // SAFETY: dtor_addr was emitted by AOT codegen as a function-address
    // relocation against an `extern "C"` symbol declared in the IR
    // module. ExternTy constraints guarantee a u64-wide scalar parameter.
    let dtor: unsafe extern "C" fn(u64) = unsafe { std::mem::transmute(dtor_addr) };
    let handle = crate::resource::ResourceHandle::new(payload, dtor);
    let proc_ptr = CURRENT_PROCESS.with(|c| c.get());
    assert!(
        !proc_ptr.is_null(),
        "fz_make_resource (AOT): no current process"
    );
    let heap = unsafe { &mut (*proc_ptr).heap };
    // fz-4mk — stash the dtor closure value alongside the extracted fn ptr
    // so phase 2 can dispatch the dtor as fz code at scheduler boundaries.
    let stub = crate::resource::alloc_resource(heap, handle, FzValue(dtor_closure_bits));
    FzValue::from_ptr(stub.as_raw()).0
}

/// fz-ul4.38 — register the program's tuple schemas with the AOT process,
/// in the order baked into the `fz_aot_tuple_arities` data symbol. Codegen
/// iterates arities in sorted order; this fn registers in that same order
/// so the schema ids match what was iconst'd into the emitted CLIF.
///
/// `arities` may be null (no tuples in program); `len` is the element
/// count (each element is a u32). When arities 1 and 3 are present, the
/// per-process bs reader caches are populated to bring AOT to parity with
/// JIT's CompiledModule wiring.
///
/// # Safety
/// `proc` must be a process produced by `fz_aot_setup`. `arities` must
/// point at `len` consecutive `u32`s when len > 0.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_aot_register_tuple_schemas(proc: *mut Process, arities: *const u32, len: u32) {
    assert!(
        !proc.is_null(),
        "fz_aot_register_tuple_schemas: null process"
    );
    if len == 0 {
        return;
    }
    assert!(
        !arities.is_null(),
        "fz_aot_register_tuple_schemas: null arities with len > 0"
    );
    let process = unsafe { &mut *proc };
    let registry = process.heap.schemas_registry();
    let mut reg = registry.borrow_mut();
    for i in 0..len {
        // Data section alignment isn't guaranteed on all platforms; read
        // unaligned so we don't trip the alignment check on aarch64-darwin.
        let arity = unsafe { std::ptr::read_unaligned(arities.add(i as usize)) };
        let id = reg.register(crate::heap::Schema::tuple_of_arity(arity as usize));
        match arity {
            1 => process.bs_tuple_arity1_schema = Some(id),
            3 => process.bs_tuple_arity3_schema = Some(id),
            _ => {}
        }
    }
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

/// Spawn hook (fz-sched.2). Allocates a child Process, deep-copies the
/// closure into its heap, sets pending_closure_entry, and enqueues the
/// child — returning immediately to the caller. The run-queue loop in
/// fz_aot_run_main drives the child when the parent yields or halts.
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

    // Store the entry point and enqueue — do not run now.
    child.pending_closure_entry = copied_ptr as *mut u8;
    child.state = ProcessState::Ready;

    AOT_TASKS.with(|c| c.borrow_mut().insert(pid, child));
    AOT_RUN_QUEUE.with(|q| q.borrow_mut().push_back(pid));

    pid
}

/// fz-siu.12: spawn_opt hook. v1 ignores min_heap_size; delegates to aot_spawn_hook.
extern "C" fn aot_spawn_opt_hook(closure_bits: u64, _min_heap_size: u32) -> u32 {
    aot_spawn_hook(closure_bits)
}

/// Send hook (fz-sched.2). Pushes a message into the receiver's mailbox.
/// If the receiver was Blocked on receive, flips it to Ready and enqueues
/// it — matching the JIT's send_via_current_runtime semantics.
extern "C" fn aot_send_hook(receiver_pid: u32, msg_bits: u64) {
    let wake = AOT_TASKS.with(|c| {
        let mut t = c.borrow_mut();
        match t.get_mut(&receiver_pid) {
            Some(task) => {
                task.mailbox.push_back(FzValue(msg_bits));
                if task.state == ProcessState::Blocked {
                    task.state = ProcessState::Ready;
                    true
                } else {
                    false
                }
            }
            None => {
                eprintln!("aot_send: no task with pid {}", receiver_pid);
                std::process::abort();
            }
        }
    });
    if wake {
        AOT_RUN_QUEUE.with(|q| q.borrow_mut().push_back(receiver_pid));
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
    crate::scheduler_hooks::clear_make_resource_hook();
    AOT_DTOR_TABLE.with(|c| c.borrow_mut().clear());
    AOT_SPAWN_ENTRY.with(|c| c.set(std::ptr::null()));
    AOT_RESUME_PARK.with(|c| c.set(std::ptr::null()));
    AOT_MAIN_ENTRY.with(|c| c.set(std::ptr::null()));
    AOT_HALT_CL.with(|c| c.set(0));
    AOT_HALT_CONT_BODIES.with(|c| c.set([std::ptr::null(); 3]));
    AOT_RESUME_SHIMS.with(|c| c.set([std::ptr::null(); 9]));
    CURRENT_PROCESS.with(|c| c.set(std::ptr::null_mut()));
    AOT_TASKS.with(|c| c.borrow_mut().clear());
    AOT_RUN_QUEUE.with(|q| q.borrow_mut().clear());
    AOT_SCHEMAS.with(|s| *s.borrow_mut() = None);
    0
}

/// fz-02r.7 — register the 9 mid-flight resume shim addresses (arg count
/// 0..=8). Called from the AOT-emitted C main after fz_aot_setup but before
/// fz_aot_run_main so the shims are available when back-edge yields fire.
/// `shims` must point to 9 consecutive *const u8 pointers.
///
/// # Safety
/// `shims` must point to 9 valid fn pointers (Local Cranelift symbols
/// emitted by compile_with_backend). Called only from AOT-generated C main.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_aot_set_resume_shims(shims: *const *const u8) {
    let mut arr = [std::ptr::null::<u8>(); 9];
    for (i, slot) in arr.iter_mut().enumerate() {
        *slot = unsafe { *shims.add(i) };
    }
    AOT_RESUME_SHIMS.with(|c| c.set(arr));
}

/// Cooperative run-queue loop. Drives all enqueued processes to completion
/// or Blocked state. Each iteration pops one pid, dispatches one quantum,
/// and re-enqueues if the process self-sent (state == Ready).
///
/// Dispatch priority (checked in order):
///   1. pending_main_entry — initial main dispatch via fz_main_entry shim
///   2. pending_closure_entry — initial spawn dispatch via fz_spawn_entry shim
///   3. parked_cont + message in mailbox — resume via fz_resume_park
///   4. mid_flight_fn_ptr != 0 — resume after mid-flight back-edge GC
fn aot_run_queue_loop() {
    let main_entry_addr = AOT_MAIN_ENTRY.with(|c| c.get());
    let spawn_entry_addr = AOT_SPAWN_ENTRY.with(|c| c.get());
    let resume_park_addr = AOT_RESUME_PARK.with(|c| c.get());
    let halt_cl = AOT_HALT_CL.with(|c| c.get());

    while let Some(pid) = AOT_RUN_QUEUE.with(|q| q.borrow_mut().pop_front()) {
        let proc_ptr = AOT_TASKS
            .with(|c| {
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
        } else if unsafe { (*proc_ptr).mid_flight_fn_ptr } != 0 {
            // fz-02r.7 — mid-flight back-edge yield resume. gc_mid_flight
            // was run by the scheduler before re-enqueue; mid_flight_roots
            // holds forwarded args. Call the matching resume shim which
            // reads N args from the slab and Tail-CC indirect-calls fn_ptr.
            let fn_ptr = unsafe { (*proc_ptr).mid_flight_fn_ptr };
            let n = unsafe { (*proc_ptr).mid_flight_root_count } as usize;
            unsafe { (*proc_ptr).mid_flight_fn_ptr = 0 };
            unsafe { (*proc_ptr).mid_flight_root_count = 0 };
            let shims = AOT_RESUME_SHIMS.with(|c| c.get());
            let shim = shims[n];
            if !shim.is_null() {
                type MidFlightResume = extern "C" fn(u64) -> i64;
                let f: MidFlightResume = unsafe { std::mem::transmute(shim) };
                let _ = f(fn_ptr);
            }
        }

        // Post-quantum state check.
        let state = unsafe { (*proc_ptr).state };
        let mid_flight = unsafe { (*proc_ptr).mid_flight_fn_ptr };
        if state == ProcessState::Running && mid_flight != 0 {
            // Mid-flight yield: GC the slab, clear flag, re-enqueue.
            let n = unsafe { (*proc_ptr).mid_flight_root_count as usize };
            let process = unsafe { &mut *proc_ptr };
            process
                .heap
                .gc_mid_flight(&mut process.mid_flight_roots[..n], &mut process.mailbox);
            process.quiet_quanta = 0;
            crate::yield_flag::FZ_SHOULD_YIELD.store(0, std::sync::atomic::Ordering::Relaxed);
            unsafe { (*proc_ptr).state = ProcessState::Ready };
            AOT_RUN_QUEUE.with(|q| q.borrow_mut().push_back(pid));
        } else if state == ProcessState::Ready {
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
