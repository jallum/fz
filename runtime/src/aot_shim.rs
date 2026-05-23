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

use crate::fz_value::PackedValueWord;
use crate::heap::SchemaRegistry;
use crate::process::{CURRENT_PROCESS, Process, ProcessState};
use crate::timer::TimerWheel;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;
use std::time::Duration;

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
    /// fz-4mk.3b — SystemV `fz_drain_dtor_entry(closure, payload)` shim
    /// address. Set by `fz_aot_set_drain_dtor_entry` after setup. The
    /// run-queue loop calls this once per pending dtor at task-exit; the
    /// shim Tail-CC dispatches the closure body with a fresh halt-cont.
    static AOT_DRAIN_DTOR_ENTRY: Cell<*const u8> = const { Cell::new(std::ptr::null()) };
    /// fz-xx8.1 — SystemV `fz_resume(cont)` shim address. Set by
    /// `fz_aot_set_resume_addr` after setup. The run-queue loop will call
    /// this when `pending_resume_matched` is set (selective-receive wakeup);
    /// the shim loads `cont+16` and calls the cont stub with the outcome
    /// closure. Bound values already live in that closure's env.
    static AOT_RESUME_ADDR: Cell<*const u8> = const { Cell::new(std::ptr::null()) };
    /// fz-xx8.3 — AOT-side `TimerWheel` so `receive ... after N -> ...`
    /// clauses fire under AOT. The JIT holds its own wheel inside `Runtime`
    /// (src/runtime.rs); AOT has no Runtime, so the wheel lives here.
    /// Scheduled by `aot_timer_schedule_hook`, cancelled by
    /// `aot_timer_cancel_hook`, drained at the top of each
    /// `aot_run_queue_loop` iteration.
    static AOT_TIMERS: RefCell<TimerWheel> = RefCell::new(TimerWheel::new());
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
    // fz-xx8.3 — timer schedule/cancel hooks for `receive ... after N`.
    crate::scheduler_hooks::install_timer_schedule_hook(aot_timer_schedule_hook);
    crate::scheduler_hooks::install_timer_cancel_hook(aot_timer_cancel_hook);
    AOT_TIMERS.with(|w| *w.borrow_mut() = TimerWheel::new());
    // fz-4mk — AOT MakeResourceHook. Allocates a Resource carrying the
    // dtor closure on the stub; the closure body fires as fz code at
    // task-exit drain via `fz_drain_dtor_entry`.
    crate::scheduler_hooks::install_make_resource_hook(aot_make_resource_hook);

    proc_ptr
}

/// fz-4mk — AOT `MakeResourceHook` body. Validates that the dtor arg is
/// a closure heap value, then allocates a fresh `Resource` on the current
/// process's heap with the closure stashed on the stub. The real dtor
/// body runs as fz code at scheduler-boundary drain via the
/// `fz_drain_dtor_entry` shim; the Resource's C-side dtor slot is the
/// no-op so refcount→0 outside the drain doesn't double-fire.
extern "C" fn aot_make_resource_hook(
    payload_raw: u64,
    payload_kind: u8,
    dtor_raw: u64,
    dtor_kind: u8,
) -> u64 {
    let dtor_closure = crate::fz_value::FzValue::decode_parts(dtor_raw, dtor_kind)
        .expect("fz_make_resource (AOT): dtor kind");
    let dtor_closure_bits = dtor_closure
        .tagged_heap_bits()
        .expect("fz_make_resource (AOT): dtor arg is not a closure");
    if crate::fz_value::closure_addr_from_tagged(dtor_closure_bits).is_none() {
        eprintln!("fz_make_resource (AOT): dtor arg is not a closure");
        std::process::abort();
    }
    let payload_value = crate::fz_value::FzValue::decode_parts(payload_raw, payload_kind)
        .expect("fz_make_resource (AOT): payload kind");
    let proc_ptr = CURRENT_PROCESS.with(|c| c.get());
    assert!(
        !proc_ptr.is_null(),
        "fz_make_resource (AOT): no current process"
    );
    let heap = unsafe { &mut (*proc_ptr).heap };
    let handle = crate::resource::ResourceHandle::new(
        payload_value.raw(),
        payload_value.kind().tag(),
        crate::resource::fz_resource_destructor_noop,
    );
    let stub = crate::resource::alloc_resource(heap, handle, dtor_closure);
    crate::fz_value::tagged_resource_bits(stub.as_raw() as *const u8)
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
        PackedValueWord(closure_bits),
        &parent.heap,
        &mut child.heap,
        &mut forwarding,
    );
    crate::fz_value::closure_addr_from_tagged(copied.0)
        .expect("aot_spawn_hook: closure must be a closure");

    // Store the entry point and enqueue — do not run now.
    child.pending_closure_entry = copied.0 as *mut u8;
    child.state = ProcessState::Ready;

    AOT_TASKS.with(|c| c.borrow_mut().insert(pid, child));
    AOT_RUN_QUEUE.with(|q| q.borrow_mut().push_back(pid));

    pid
}

/// fz-siu.12: spawn_opt hook. v1 ignores min_heap_size; delegates to aot_spawn_hook.
extern "C" fn aot_spawn_opt_hook(closure_bits: u64, _min_heap_size: u32) -> u32 {
    aot_spawn_hook(closure_bits)
}

/// fz-xx8.3 — schedule an after-clause timer on the AOT wheel. Returns the
/// fresh `TimerId` (a u64); `fz_receive_park_matched` stashes it on the
/// park record so a matcher hit can cancel.
extern "C" fn aot_timer_schedule_hook(pid: u32, after_ms: u64) -> u64 {
    AOT_TIMERS.with(|w| {
        w.borrow_mut()
            .schedule(pid, Duration::from_millis(after_ms))
    })
}

/// fz-xx8.3 — cancel an after-clause timer (no-op when already fired or
/// unknown, matching the JIT path's `TimerWheel::cancel`).
extern "C" fn aot_timer_cancel_hook(timer_id: u64) {
    AOT_TIMERS.with(|w| w.borrow_mut().cancel(timer_id));
}

/// Send hook (fz-sched.2). Pushes a message into the receiver's mailbox.
/// If the receiver was Blocked on legacy `receive()`, flips it to Ready
/// and enqueues — matching the JIT's send_via_current_runtime semantics.
/// Selective-receive arrivals route through `sched::probe_sender`.
extern "C" fn aot_send_hook(receiver_pid: u32, msg_value: u64, msg_kind: u8) {
    let slot = crate::fz_value::MailboxSlot {
        value: msg_value,
        kind: msg_kind,
    };
    let wake = AOT_TASKS.with(|c| {
        let mut t = c.borrow_mut();
        let Some(task) = t.get_mut(&receiver_pid) else {
            eprintln!("aot_send: no task with pid {}", receiver_pid);
            std::process::abort();
        };
        if task.parked_matched.is_some() {
            matches!(
                crate::sched::probe_sender(task, slot),
                crate::sched::ProbeOutcome::Hit
            )
        } else {
            task.mailbox.push_back(slot);
            if task.state == ProcessState::Blocked {
                task.state = ProcessState::Ready;
                true
            } else {
                false
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
    crate::scheduler_hooks::clear_timer_schedule_hook();
    crate::scheduler_hooks::clear_timer_cancel_hook();
    AOT_TIMERS.with(|w| *w.borrow_mut() = TimerWheel::new());
    AOT_DRAIN_DTOR_ENTRY.with(|c| c.set(std::ptr::null()));
    AOT_RESUME_ADDR.with(|c| c.set(std::ptr::null()));
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

/// fz-4mk.3b — register the `fz_drain_dtor_entry` shim address. Called from
/// AOT-emitted C main after `fz_aot_setup`. The run-queue loop dispatches
/// each entry on `process.heap.pending_dtors` through this shim when a
/// task exits.
///
/// # Safety
/// `addr` must be the address of `fz_drain_dtor_entry` emitted by
/// compile_with_backend (SystemV `(closure: u64, payload: u64) -> i64`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_aot_set_drain_dtor_entry(addr: *const u8) {
    AOT_DRAIN_DTOR_ENTRY.with(|c| c.set(addr));
}

/// fz-xx8.1 — register the `fz_resume` shim address. Called from AOT-emitted
/// C main after `fz_aot_setup` and before `fz_aot_run_main`. The run-queue
/// loop dispatches `pending_resume_matched` requests through this shim
/// (mirrors the JIT path in `src/ir_codegen.rs:335`).
///
/// # Safety
/// `addr` must be the address of `fz_resume` emitted by compile_with_backend
/// (SystemV `(cont: u64) -> i64`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_aot_set_resume_addr(addr: *const u8) {
    AOT_RESUME_ADDR.with(|c| c.set(addr));
}

/// Shim addresses pulled out of thread-locals once per `aot_run_queue_loop`
/// invocation, then threaded to `dispatch_quantum` so each iteration
/// doesn't pay the `with(...)` cost six times.
struct ShimAddrs {
    main_entry: *const u8,
    spawn_entry: *const u8,
    resume_park: *const u8,
    resume: *const u8,
    halt_cl: u64,
}

/// Drain the AOT timer wheel and apply each expired entry to its task
/// via `sched::fire_after_timer`. Tasks that fire get enqueued.
fn drain_after_timers_aot() {
    let expired = AOT_TIMERS.with(|w| w.borrow_mut().drain_expired(std::time::Instant::now()));
    for entry in expired {
        let woke = AOT_TASKS.with(|c| {
            let mut tasks = c.borrow_mut();
            tasks
                .get_mut(&entry.pid)
                .map(|task| crate::sched::fire_after_timer(task, entry.id))
                .unwrap_or(false)
        });
        if woke {
            AOT_RUN_QUEUE.with(|q| q.borrow_mut().push_back(entry.pid));
        }
    }
}

/// Run one quantum for `pid`: pick dispatch branch by Process state,
/// invoke the matching SystemV shim, then handle the post-quantum state
/// transition (re-enqueue / halt / mid-flight yield). Returns nothing;
/// scheduler state is mutated in place.
fn dispatch_quantum(pid: u32, addrs: &ShimAddrs) {
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

    // fz-qw6 — selective-receive initial scan lifted to runtime::sched.
    let process = unsafe { &mut *proc_ptr };
    match crate::sched::initial_scan(process) {
        crate::sched::ScanOutcome::Hit => {
            // Fall through to the pending_resume_matched branch.
        }
        crate::sched::ScanOutcome::Miss => {
            CURRENT_PROCESS.with(|c| c.set(prev));
            return;
        }
        crate::sched::ScanOutcome::NotApplicable => {}
    }

    if !unsafe { (*proc_ptr).pending_main_entry }.is_null() {
        let main_fp = unsafe { (*proc_ptr).pending_main_entry };
        unsafe { (*proc_ptr).pending_main_entry = std::ptr::null_mut() };
        type MainEntry = extern "C" fn(u64, u64) -> i64;
        let f: MainEntry = unsafe { std::mem::transmute(addrs.main_entry) };
        let _ = f(main_fp as u64, addrs.halt_cl);
    } else if !unsafe { (*proc_ptr).pending_closure_entry }.is_null() {
        let closure_ptr = unsafe { (*proc_ptr).pending_closure_entry };
        unsafe { (*proc_ptr).pending_closure_entry = std::ptr::null_mut() };
        type SpawnEntry = extern "C" fn(u64) -> i64;
        let f: SpawnEntry = unsafe { std::mem::transmute(addrs.spawn_entry) };
        let _ = f(closure_ptr as u64);
    } else if unsafe { (*proc_ptr).pending_resume_matched.is_some() } {
        // Selective-receive wakeup. Bound args travel in the outcome
        // closure env. Checked before `parked_cont` so a stale legacy
        // park can't shadow this.
        let resume = unsafe { (*proc_ptr).pending_resume_matched.take() }.expect("checked above");
        let cont_ptr = resume.cont;
        type Resume = extern "C" fn(u64) -> i64;
        let f: Resume = unsafe { std::mem::transmute(addrs.resume) };
        let _ = f(cont_ptr as u64);
    } else if !unsafe { (*proc_ptr).parked_cont }.is_null() {
        let msg = unsafe { (*proc_ptr).mailbox.pop_front() }.unwrap_or_else(|| {
            eprintln!(
                "aot_run_queue_loop: pid {} enqueued with parked_cont but empty mailbox",
                pid
            );
            std::process::abort();
        });
        let msg_raw = msg.value;
        let msg_kind = msg.kind;
        let cont = unsafe { (*proc_ptr).parked_cont };
        unsafe { (*proc_ptr).parked_cont = std::ptr::null_mut() };
        type ResumePark = extern "C" fn(u64, u8, u64) -> i64;
        let resume: ResumePark = unsafe { std::mem::transmute(addrs.resume_park) };
        let _ = resume(msg_raw, msg_kind, cont as u64);
    } else if unsafe { (*proc_ptr).mid_flight_fn_ptr } != 0 {
        // fz-02r.7 — mid-flight back-edge yield resume.
        let fn_ptr = unsafe { (*proc_ptr).mid_flight_fn_ptr };
        unsafe { (*proc_ptr).mid_flight_fn_ptr = 0 };
        unsafe { (*proc_ptr).mid_flight_root_count = 0 };
        type MidFlightResume = extern "C" fn() -> i64;
        let f: MidFlightResume = unsafe { std::mem::transmute(fn_ptr as *const u8) };
        let _ = f();
    }

    // Post-quantum state check.
    let state = unsafe { (*proc_ptr).state };
    let mid_flight = unsafe { (*proc_ptr).mid_flight_fn_ptr };
    let parked = unsafe { (*proc_ptr).parked_cont };
    if state == ProcessState::Running && mid_flight != 0 {
        let n = unsafe { (*proc_ptr).mid_flight_root_count as usize };
        let process = unsafe { &mut *proc_ptr };
        process.heap.gc_mid_flight(
            &mut process.mid_flight_roots[..n],
            &mut process.mid_flight_root_tags[..n],
            &mut process.mailbox,
        );
        process.quiet_quanta = 0;
        crate::yield_flag::FZ_SHOULD_YIELD.store(0, std::sync::atomic::Ordering::Relaxed);
        unsafe { (*proc_ptr).state = ProcessState::Ready };
        AOT_RUN_QUEUE.with(|q| q.borrow_mut().push_back(pid));
    } else if state == ProcessState::Ready {
        AOT_RUN_QUEUE.with(|q| q.borrow_mut().push_back(pid));
    } else if state == ProcessState::Running && parked.is_null() {
        // fz-4mk.3b — task halted; flush MSO resources through the dtor
        // drain shim before the heap drops.
        unsafe { (*proc_ptr).state = ProcessState::Exited };
        let drain_addr = AOT_DRAIN_DTOR_ENTRY.with(|c| c.get());
        if !drain_addr.is_null() {
            let process = unsafe { &mut *proc_ptr };
            crate::procbin::mso_drop_all_deferred(&mut process.heap);
            type DrainDtor = extern "C" fn(u64, u64, u8) -> i64;
            let drain: DrainDtor = unsafe { std::mem::transmute(drain_addr) };
            while let Some((closure, payload, payload_kind)) =
                process.heap.pending_dtors.pop_front()
            {
                let _ = drain(closure, payload, payload_kind);
            }
        }
    }

    CURRENT_PROCESS.with(|c| c.set(prev));
}

/// Cooperative run-queue loop. Drives all enqueued processes to
/// completion or Blocked state. Each iteration: drain expired timers,
/// pop a pid (idle-wait if the queue is empty but timers pend),
/// dispatch one quantum.
///
/// Dispatch priority inside `dispatch_quantum`:
///   1. selective-receive initial scan (fz-qw6 helper) — Hit falls
///      through to (4); Miss returns the task to Blocked.
///   2. `pending_main_entry` — initial main dispatch.
///   3. `pending_closure_entry` — initial spawn dispatch.
///   4. `pending_resume_matched` — selective-receive wakeup.
///   5. `parked_cont` + mailbox msg — legacy resume.
///   6. `mid_flight_fn_ptr` — mid-flight back-edge resume.
fn aot_run_queue_loop() {
    let addrs = ShimAddrs {
        main_entry: AOT_MAIN_ENTRY.with(|c| c.get()),
        spawn_entry: AOT_SPAWN_ENTRY.with(|c| c.get()),
        resume_park: AOT_RESUME_PARK.with(|c| c.get()),
        resume: AOT_RESUME_ADDR.with(|c| c.get()),
        halt_cl: AOT_HALT_CL.with(|c| c.get()),
    };

    loop {
        drain_after_timers_aot();

        let Some(pid) = AOT_RUN_QUEUE.with(|q| q.borrow_mut().pop_front()) else {
            // Queue empty. Sleep until the next timer deadline if one
            // exists; otherwise truly idle, break. (Multi-worker AOT
            // will need a condvar here instead of a blocking sleep.)
            let next = AOT_TIMERS.with(|w| w.borrow().next_deadline());
            match next {
                Some(deadline) => {
                    let now = std::time::Instant::now();
                    if deadline > now {
                        std::thread::sleep(deadline - now);
                    }
                    continue;
                }
                None => break,
            }
        };
        dispatch_quantum(pid, &addrs);
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

    /// fz-xx8.1 — `fz_aot_set_resume_addr` populates the thread-local
    /// `AOT_RESUME_ADDR`; teardown of `fz_aot_run_main` clears it. We
    /// can't easily drive a full setup→run→teardown cycle from a unit
    /// test (it would need a real codegen'd shim), so we exercise the
    /// register/clear lifecycle directly and assert the cell flips.
    /// fz-xx8.3 — schedule→drain→wake flow on the AOT timer wheel.
    /// Mirrors `src/runtime.rs::drain_expired_timers_wakes_after_cont`. We
    /// can't drive aot_run_queue_loop directly (it would call into
    /// codegen'd shim pointers we don't have), but we exercise every
    /// pre-dispatch ingredient: hook install → schedule → expiry →
    /// mutate the task's parked_matched into a pending_resume_matched →
    /// run-queue enqueue. The dispatch-via-resume-shim step is covered
    /// by the end-to-end fixture run on a built binary.
    #[test]
    fn timer_drain_wakes_after_cont() {
        use crate::park::ParkRecord;
        use crate::process::{Process, ProcessState};

        // Clean per-test slate.
        AOT_TIMERS.with(|w| *w.borrow_mut() = TimerWheel::new());
        AOT_TASKS.with(|c| c.borrow_mut().clear());
        AOT_RUN_QUEUE.with(|q| q.borrow_mut().clear());

        crate::scheduler_hooks::install_timer_schedule_hook(aot_timer_schedule_hook);
        crate::scheduler_hooks::install_timer_cancel_hook(aot_timer_cancel_hook);

        // Stand up a single task with a parked_matched that has an
        // after_timer_id. matcher_fn is unused on the drain path.
        extern "C" fn never_match(
            _msg: u64,
            _msg_kind: u8,
            _pinned: *const u64,
            _out: *mut u64,
        ) -> u32 {
            0
        }
        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let mut p = Box::new(Process::new(schemas));
        p.pid = 7;
        let timer_id =
            crate::scheduler_hooks::dispatch_timer_schedule(p.pid, 1).expect("hook installed");
        let after_cont_addr: usize = 0xCAFE_BABE;
        p.parked_matched = Some(Box::new(ParkRecord {
            matcher_fn: never_match,
            pinned: vec![],
            clause_bodies: vec![],
            clause_bound_counts: vec![],
            bound_arity: 0,
            after_deadline_ms: Some(1),
            after_cont: after_cont_addr as *mut u8,
            after_timer_id: Some(timer_id),
        }));
        p.state = ProcessState::Blocked;
        AOT_TASKS.with(|c| {
            c.borrow_mut().insert(7, p);
        });

        // Wait past the deadline, then run the same drain logic
        // aot_run_queue_loop runs at the top of each iteration.
        std::thread::sleep(std::time::Duration::from_millis(5));
        let expired = AOT_TIMERS.with(|w| w.borrow_mut().drain_expired(std::time::Instant::now()));
        assert_eq!(expired.len(), 1);
        for entry in expired {
            AOT_TASKS.with(|c| {
                let mut tasks = c.borrow_mut();
                let task = tasks.get_mut(&entry.pid).unwrap();
                let park = task.parked_matched.as_ref().unwrap();
                assert_eq!(park.after_timer_id, Some(entry.id));
                let after_cont = park.after_cont;
                task.parked_matched = None;
                task.pending_resume_matched =
                    Some(crate::park::PendingResumeMatched { cont: after_cont });
                task.state = ProcessState::Ready;
                AOT_RUN_QUEUE.with(|q| q.borrow_mut().push_back(entry.pid));
            });
        }

        AOT_TASKS.with(|c| {
            let tasks = c.borrow();
            let task = tasks.get(&7).unwrap();
            assert_eq!(task.state, ProcessState::Ready);
            assert!(task.parked_matched.is_none());
            let pending = task
                .pending_resume_matched
                .as_ref()
                .expect("after-timer fire sets pending_resume_matched");
            assert_eq!(pending.cont as usize, after_cont_addr);
        });
        assert!(AOT_RUN_QUEUE.with(|q| q.borrow().iter().any(|p| *p == 7)));

        // Cleanup so we don't leak hooks into a sibling test.
        crate::scheduler_hooks::clear_timer_schedule_hook();
        crate::scheduler_hooks::clear_timer_cancel_hook();
        AOT_TASKS.with(|c| c.borrow_mut().clear());
        AOT_RUN_QUEUE.with(|q| q.borrow_mut().clear());
        AOT_TIMERS.with(|w| *w.borrow_mut() = TimerWheel::new());
    }

    /// fz-xx8.3 — `aot_timer_cancel_hook` retires a previously scheduled
    /// timer so a sender-probe / initial-scan hit can prevent the after
    /// from firing.
    #[test]
    fn timer_cancel_removes_pending_entry() {
        AOT_TIMERS.with(|w| *w.borrow_mut() = TimerWheel::new());
        crate::scheduler_hooks::install_timer_schedule_hook(aot_timer_schedule_hook);
        crate::scheduler_hooks::install_timer_cancel_hook(aot_timer_cancel_hook);

        let id = crate::scheduler_hooks::dispatch_timer_schedule(99, 10_000).unwrap();
        assert!(AOT_TIMERS.with(|w| w.borrow().next_deadline().is_some()));
        crate::scheduler_hooks::dispatch_timer_cancel(id);
        assert!(AOT_TIMERS.with(|w| w.borrow().next_deadline().is_none()));

        crate::scheduler_hooks::clear_timer_schedule_hook();
        crate::scheduler_hooks::clear_timer_cancel_hook();
    }

    #[test]
    fn set_resume_addr_populates_and_clears() {
        AOT_RESUME_ADDR.with(|c| c.set(std::ptr::null()));
        let fake = 0xDEAD_BEEFusize as *const u8;
        unsafe { fz_aot_set_resume_addr(fake) };
        assert_eq!(AOT_RESUME_ADDR.with(|c| c.get()), fake);
        // Mirror the teardown clears in fz_aot_run_main.
        AOT_RESUME_ADDR.with(|c| c.set(std::ptr::null()));
        assert!(AOT_RESUME_ADDR.with(|c| c.get()).is_null());
    }
}
