//! Runtime entry point for AOT-compiled fz binaries (fz-siu.6.1 / .6.2).
//!
//! AOT codegen emits a C-callable `main` that drives the cps-in-clif
//! execution model:
//!
//!   1. `proc = fz_aot_setup(atom_blob, atom_blob_len, halt_cont_body_addr,
//!                            entry_thunk_addr)`
//!   2. for each static closure target:
//!      `fz_aot_register_static_closure(proc, cl_sid, fn_id, code_addr)`
//!   3. `exit = fz_aot_run_main(proc, main_fp, main_trampoline_addr)`
//!   4. `return exit`
//!
//! `fz_entry_thunk`, `fz_main_trampoline`, `fz_resume`, `fz_halt_cont_body`,
//! and the Tail-CC `fz_fn_<id>` bodies are emitted as Local symbols in the
//! same object — the C main resolves each via `func_addr` and passes them
//! by raw pointer. No per-program dispatch / frame-size shim, no trampoline.
//! Every task is resumed through the one `fz_resume` verb: a spawned task's
//! `runnable` is an entry thunk; main's wraps a synthetic `fz_main_trampoline`
//! inner closure.
//!
//! Concurrency: a cooperative run-queue scheduler (fz-sched.1/2). Spawned
//! processes are enqueued and driven by `aot_run_queue_loop` in
//! `fz_aot_run_main`. `fz_receive_park` parks a process (sets state =
//! Blocked / Ready); `aot_send_hook` wakes Blocked receivers. This matches
//! the JIT's `run_until_idle` semantics.

use crate::exec_ctx::ExecCtx;
use crate::heap::SchemaRegistry;
use crate::process::{Process, ProcessState};
use crate::timer::TimerWheel;
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;
use std::time::Duration;

// ----- AOT scheduler state -----

/// The whole scheduler state for one AOT run.
///
/// AOT has no binary `Runtime` to hang an `ExecCtx` off (the staticlib does
/// not link the codegen crate), so this struct *is* the AOT scheduler handle:
/// it owns the task table, run-queue, timer wheel, pid counter, and the
/// SystemV→Tail-CC shim addresses, and it carries the per-run `ExecCtx`
/// dispatch table inline. Its `ctx.scheduler` points back at the struct, so
/// the spawn/send/timer hooks re-narrow that erased handle to `&mut
/// AotScheduler` — exactly as the JIT hooks re-narrow `ExecCtx.scheduler` to
/// `*mut Runtime`. Per-run (heap-owned), not per-thread: two AOT runs can be
/// live on one worker without clobbering each other.
///
/// `fz_aot_setup` boxes one of these and leaks it (`Box::into_raw`); every
/// task's `Process.ctx` points at the inline `ctx` field, reachable from the
/// process pointer the AOT C-main threads through the entry sequence.
/// `fz_aot_run_main` reclaims and drops the box at teardown — one drop frees
/// the tasks, timers, and queue.
struct AotScheduler {
    /// Next pid to hand out. pid 1 is main; children start at 2.
    next_pid: u32,
    /// All live processes, keyed by pid. `Box` keeps each `Process` at a
    /// stable address across rehashes so raw `*mut Process` stay valid. The
    /// shared `SchemaRegistry` stays alive through these heaps' `Rc` clones —
    /// no separate scheduler-level anchor is needed.
    tasks: HashMap<u32, Box<Process>>,
    /// `fz_entry_thunk` body address captured at setup. Used to mint a fresh
    /// task's entry thunk (spawn / main) on its heap; the scheduler resumes
    /// every task through the one `fz_resume` verb.
    entry_thunk: *const u8,
    /// fz-ul4.27.22.3 — three halt_cont_body addrs retained so spawned
    /// children can initialize their own halt_cont_singletons.
    halt_cont_bodies: [*const u8; 3],
    /// fz-sched.1 — cooperative run-queue. PIDs of processes ready to run.
    run_queue: VecDeque<u32>,
    /// fz-4mk.3b — SystemV `fz_drain_dtor_entry(closure, payload)` shim
    /// address. Set by `fz_aot_set_drain_dtor_entry` after setup. The
    /// run-queue loop calls this once per pending dtor at task-exit; the
    /// shim Tail-CC dispatches the closure body with a fresh halt-cont.
    drain_dtor_entry: *const u8,
    /// fz-xx8.1 — SystemV `fz_resume(cont)` shim address. Set by
    /// `fz_aot_set_resume_addr` after setup. The run-queue loop calls this to
    /// resume the task's `runnable` closure (a fresh entry thunk or a
    /// continuation); the shim reads the closure code pointer through the
    /// runtime ABI and tail-calls it. Bound values already live in its env.
    resume_addr: *const u8,
    /// fz-xx8.3 — AOT-side `TimerWheel` so `receive ... after N -> ...`
    /// clauses fire under AOT. The JIT holds its own wheel inside `Runtime`
    /// (src/runtime.rs); AOT has no Runtime, so the wheel lives here.
    /// Scheduled by `aot_timer_schedule_hook`, cancelled by
    /// `aot_timer_cancel_hook`, drained at the top of each
    /// `aot_run_queue_loop` iteration.
    timers: TimerWheel,
    /// Per-run dispatch table. Its handles (Runtime/tel/module) stay null —
    /// AOT has none — and `scheduler` points back at this struct. Every AOT
    /// task points its `Process.ctx` here; the spawn/send/make_resource/timer
    /// BIFs dispatch through it.
    ctx: ExecCtx,
}

/// Re-narrow a task's erased scheduler handle (`Process.ctx.scheduler`) to
/// the owning `AotScheduler`.
///
/// # Safety
/// `proc` must be a live AOT process whose `ctx` was wired by `fz_aot_setup`
/// (directly or via `dispatch_quantum`'s re-stamp).
unsafe fn sched_of(proc: *mut Process) -> *mut AotScheduler {
    let ctx = unsafe { (*proc).ctx };
    debug_assert!(!ctx.is_null(), "aot process has no ctx");
    let scheduler = unsafe { (*ctx).scheduler };
    debug_assert!(!scheduler.is_null(), "aot ctx has no scheduler");
    scheduler as *mut AotScheduler
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

/// AOT setup: create the main Process, register it in the AOT task table,
/// initialize the halt-cont singleton, register the spawn-entry address,
/// install scheduler hooks, parse the atom blob. Returns the process pointer
/// for subsequent register/run calls. `atom_blob` may be null (program has no
/// atom literals); `atom_blob_len` is currently advisory — parsing terminates
/// on the double-NUL sentinel.
#[unsafe(no_mangle)]
pub extern "C" fn fz_aot_setup(
    atom_blob: *const u8,
    _atom_blob_len: u32,
    halt_cont_body_tagged: *const u8,
    halt_cont_body_i64: *const u8,
    halt_cont_body_f64: *const u8,
    entry_thunk_addr: *const u8,
) -> *mut Process {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));

    // The AOT run's node-global atom table, seeded from the program's atom
    // blob and shared (Rc) by every spawned process.
    let node = Rc::new(crate::process::Node::new(
        parse_atom_blob(atom_blob),
        Vec::new(),
    ));
    let proc_box = Box::new(Process::from_consts(
        node,
        schemas,
        &crate::process::CompiledModuleConsts::empty(),
        1,
        crate::process::DEFAULT_REDUCTIONS_PER_QUANTUM,
    ));

    // Box and leak the scheduler so it outlives this call's stack frame and
    // stays reachable from `proc.ctx.scheduler` through the AOT C-main entry
    // sequence. `fz_aot_run_main` reclaims and drops it at teardown.
    //
    // fz-4mk — the MakeResourceHook allocates a Resource carrying the dtor
    // closure on the stub; the closure body fires as fz code at task-exit
    // drain via `fz_drain_dtor_entry`.
    // fz-xx8.3 — timer schedule/cancel hooks for `receive ... after N`.
    let mut tasks = HashMap::new();
    tasks.insert(1u32, proc_box);
    let sched = Box::into_raw(Box::new(AotScheduler {
        next_pid: 2,
        tasks,
        entry_thunk: entry_thunk_addr,
        halt_cont_bodies: [
            halt_cont_body_tagged,
            halt_cont_body_i64,
            halt_cont_body_f64,
        ],
        run_queue: VecDeque::new(),
        drain_dtor_entry: std::ptr::null(),
        resume_addr: std::ptr::null(),
        timers: TimerWheel::new(),
        ctx: ExecCtx {
            spawn: Some(aot_spawn_hook),
            spawn_opt: Some(aot_spawn_opt_hook),
            send: Some(aot_send_hook),
            make_resource: Some(aot_make_resource_hook),
            timer_schedule: Some(aot_timer_schedule_hook),
            timer_cancel: Some(aot_timer_cancel_hook),
            ..ExecCtx::empty()
        },
    }));

    // Wire the self-referential handles: ctx.scheduler points back at the
    // scheduler (the erased handle the hooks re-narrow); the root task's
    // ctx points at the inline dispatch table. Spawned children are stamped
    // at dispatch. Both targets are stable — the box never moves.
    unsafe {
        (*sched).ctx.scheduler = sched as *mut ();
        let proc_ptr = (*sched)
            .tasks
            .get_mut(&1)
            .map(|b| b.as_mut() as *mut Process)
            .unwrap();
        (*proc_ptr).ctx = &mut (*sched).ctx;
        proc_ptr
    }
}

/// fz-4mk — AOT `MakeResourceHook` body. Validates that the dtor arg is
/// a closure heap value, then allocates a fresh `Resource` on the current
/// process's heap with the closure stashed on the stub. The real dtor
/// body runs as fz code at scheduler-boundary drain via the
/// `fz_drain_dtor_entry` shim; the Resource's C-side dtor slot is the
/// no-op so refcount→0 outside the drain doesn't double-fire.
extern "C" fn aot_make_resource_hook(
    process: *mut Process,
    _module: *const (),
    payload_raw: u64,
    dtor_ref: u64,
) -> u64 {
    let dtor_ref = crate::any_value::AnyValueRef::from_raw_word(dtor_ref)
        .expect("fz_make_resource (AOT): dtor ref");
    let dtor_closure =
        crate::any_value::AnyValue::from_ref(dtor_ref).expect("fz_make_resource (AOT): dtor value");
    let dtor_closure_bits = dtor_closure
        .heap_object_word()
        .expect("fz_make_resource (AOT): dtor arg is not a closure");
    if crate::any_value::closure_addr_from_tagged(dtor_closure_bits).is_none() {
        eprintln!("fz_make_resource (AOT): dtor arg is not a closure");
        std::process::abort();
    }
    assert!(
        !process.is_null(),
        "fz_make_resource (AOT): no current process"
    );
    let heap = unsafe { &mut (*process).heap };
    let handle = crate::resource::ResourceHandle::new(
        payload_raw,
        crate::resource::fz_resource_destructor_noop,
    );
    let stub = crate::resource::alloc_resource(heap, handle, dtor_closure);
    crate::any_value::AnyValueRef::from_heap_object(
        crate::any_value::ValueKind::RESOURCE,
        stub.as_raw() as *const u8,
    )
    .expect("resource ref")
    .raw_word()
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
    // Read the shim addrs off the scheduler before taking the &mut Process —
    // `sched_of` reads `proc.ctx`, which must not alias the live &mut below.
    let halt_cont_bodies = unsafe { (*sched_of(proc)).halt_cont_bodies };
    let process = unsafe { &mut *proc };
    if len > 0 {
        assert!(
            !arities.is_null(),
            "fz_aot_register_tuple_schemas: null arities with len > 0"
        );
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
    process.init_halt_cont_singletons(halt_cont_bodies);
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
extern "C" fn aot_spawn_hook(sender: *mut Process, scheduler: *mut (), closure_bits: u64) -> u32 {
    assert!(!sender.is_null(), "aot_spawn_hook: no sender process");
    // Touch the scheduler only through short raw-pointer scopes: `sender`
    // lives inside `sched.tasks`, so a long-lived `&mut *sched` would alias
    // the `&*parent` view below.
    let sched = scheduler as *mut AotScheduler;
    let pid = unsafe {
        let p = (*sched).next_pid;
        (*sched).next_pid = p + 1;
        p
    };
    let halt_cont_body_addrs = unsafe { (*sched).halt_cont_bodies };
    let entry_thunk_addr = unsafe { (*sched).entry_thunk };

    let parent = unsafe { &*sender };
    let schemas = parent.heap.schemas_registry();
    let static_closures = parent.static_closures.clone();
    // Child shares the parent's node (the same atom table) by Rc clone — a
    // pointer copy, not a table copy.
    let node = std::rc::Rc::clone(&parent.node);

    let consts = crate::process::CompiledModuleConsts {
        halt_cont_body_addrs,
        ..crate::process::CompiledModuleConsts::empty()
    };
    let mut child = Box::new(Process::from_consts(
        node,
        schemas,
        &consts,
        pid,
        crate::process::DEFAULT_REDUCTIONS_PER_QUANTUM,
    ));
    // Inherit the parent's already-built static-closure singletons by copying
    // the pointers (they alias the parent's process-lifetime buffers).
    child.static_closures = static_closures;

    // Deep-copy the closure into the child's heap.
    let mut forwarding = HashMap::new();
    let closure_ref = crate::any_value::AnyValueRef::from_raw_word(closure_bits)
        .expect("aot_spawn_hook: closure ref");
    let copied = crate::heap::deep_copy_any_value_ref(
        closure_ref,
        &parent.heap,
        &mut child.heap,
        &mut forwarding,
    );
    let copied_addr = copied
        .closure_addr()
        .expect("aot_spawn_hook: copied closure must be a closure");

    // Wrap the copied closure in an entry thunk queued as `runnable`; the
    // run-queue loop resumes it via `fz_resume`. `parent`/`sender` are no
    // longer read past this point, so mutating `sched.tasks` is safe.
    let thunk = crate::sched::mint_entry_thunk(&mut child.heap, entry_thunk_addr, copied_addr);
    child.set_runnable_closure(thunk);
    // Scaffolding is prepared before the child runs; reset so its alloc
    // telemetry measures only the child's execution.
    child.heap.reset_alloc_stats();
    child.state = ProcessState::Ready;

    unsafe {
        (*sched).tasks.insert(pid, child);
        (*sched).run_queue.push_back(pid);
    }

    pid
}

/// fz-siu.12: spawn_opt hook. v1 ignores min_heap_size; delegates to aot_spawn_hook.
extern "C" fn aot_spawn_opt_hook(
    sender: *mut Process,
    scheduler: *mut (),
    closure_bits: u64,
    _min_heap_size: u32,
) -> u32 {
    aot_spawn_hook(sender, scheduler, closure_bits)
}

fn deep_copy_send_ref_for_aot(
    sender: &Process,
    receiver: &mut Process,
    msg: crate::any_value::AnyValueRef,
) -> crate::any_value::AnyValueRef {
    let mut forwarding = HashMap::new();
    crate::heap::deep_copy_any_value_ref(msg, &sender.heap, &mut receiver.heap, &mut forwarding)
}

fn deep_copy_self_send_ref_for_aot(
    sender: &mut Process,
    msg: crate::any_value::AnyValueRef,
) -> crate::any_value::AnyValueRef {
    let mut forwarding = HashMap::new();
    let heap_ptr: *mut crate::heap::Heap = &mut sender.heap as *mut _;
    let src_heap: &crate::heap::Heap = unsafe { &*heap_ptr };
    let dst_heap: &mut crate::heap::Heap = unsafe { &mut *heap_ptr };
    crate::heap::deep_copy_any_value_ref(msg, src_heap, dst_heap, &mut forwarding)
}

/// fz-xx8.3 — schedule an after-clause timer on the AOT wheel. Returns the
/// fresh `TimerId` (a u64); `fz_receive_park_matched` stashes it on the
/// park record so a matcher hit can cancel.
extern "C" fn aot_timer_schedule_hook(scheduler: *mut (), pid: u32, after_ms: u64) -> u64 {
    let sched = unsafe { &mut *(scheduler as *mut AotScheduler) };
    sched.timers.schedule(pid, Duration::from_millis(after_ms))
}

/// fz-xx8.3 — cancel an after-clause timer (no-op when already fired or
/// unknown, matching the JIT path's `TimerWheel::cancel`).
extern "C" fn aot_timer_cancel_hook(scheduler: *mut (), timer_id: u64) {
    let sched = unsafe { &mut *(scheduler as *mut AotScheduler) };
    sched.timers.cancel(timer_id);
}

/// Send hook (fz-sched.2). Pushes a message into the receiver's mailbox.
/// If the receiver was Blocked on non-selective `receive()`, flips it to Ready
/// and enqueues — matching the JIT's send_via_current_runtime semantics.
/// Selective-receive arrivals route through `sched::probe_sender`.
extern "C" fn aot_send_hook(
    sender_ptr: *mut Process,
    scheduler: *mut (),
    receiver_pid: u32,
    msg_ref_word: u64,
) {
    let msg =
        crate::any_value::AnyValueRef::from_raw_word(msg_ref_word).expect("aot_send message ref");
    assert!(!sender_ptr.is_null(), "aot_send_hook: no sender process");
    let sched = scheduler as *mut AotScheduler;
    let wake = {
        let tasks = unsafe { &mut (*sched).tasks };
        let Some(task) = tasks.get_mut(&receiver_pid) else {
            eprintln!("aot_send: no task with pid {}", receiver_pid);
            std::process::abort();
        };
        let msg = if task.pid == unsafe { (*sender_ptr).pid } {
            deep_copy_self_send_ref_for_aot(task, msg)
        } else {
            let sender = unsafe { &*sender_ptr };
            deep_copy_send_ref_for_aot(sender, task, msg)
        };
        if task.wait.is_some() {
            matches!(
                crate::sched::probe_sender(task, msg),
                crate::sched::ProbeOutcome::Hit
            )
        } else {
            task.mailbox.push_back(msg);
            if task.state == ProcessState::Blocked {
                task.state = ProcessState::Ready;
                true
            } else {
                false
            }
        }
    };
    if wake {
        unsafe { (*sched).run_queue.push_back(receiver_pid) };
    }
}

/// Run main and all spawned processes via the cooperative run-queue, then
/// tear down AOT scheduler state. Returns 0 on clean completion.
/// # Safety
/// `proc`, `main_fp`, `main_trampoline_addr` must be valid pointers produced
/// by AOT codegen and `fz_aot_setup`. Called only from the AOT-emitted
/// C `main`; clippy's `not_unsafe_ptr_arg_deref` is silenced because
/// the C ABI signature is fixed.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_aot_run_main(
    proc: *mut Process,
    main_fp: *const u8,
    main_trampoline_addr: *const u8,
) -> i32 {
    assert!(!proc.is_null(), "fz_aot_run_main: null process");
    assert!(!main_fp.is_null(), "fz_aot_run_main: null main_fp");
    assert!(
        !main_trampoline_addr.is_null(),
        "fz_aot_run_main: null main_trampoline_addr"
    );

    let sched = unsafe { sched_of(proc) };
    let entry_thunk_addr = unsafe { (*sched).entry_thunk };

    // Make main a closure: a synthetic inner closure carrying the raw `(cont)`
    // main fp (via `fz_main_trampoline`), wrapped in an entry thunk queued as
    // `runnable`. AOT main has always used the strict (kind 0) halt-cont. The
    // scheduler resumes it through the one `fz_resume` verb, like any task.
    let process = unsafe { &mut *proc };
    let inner = crate::sched::mint_main_inner(
        &mut process.heap,
        main_trampoline_addr,
        main_fp,
        /* halt_kind = strict */ 0,
    );
    let thunk = crate::sched::mint_entry_thunk(&mut process.heap, entry_thunk_addr, inner);
    process.set_runnable_closure(thunk);
    // Scaffolding is prepared before main runs; reset so alloc telemetry
    // measures only main's execution.
    process.heap.reset_alloc_stats();
    unsafe {
        (*sched).run_queue.push_back(1);
    }

    aot_run_queue_loop(sched);

    // Teardown: reclaim the leaked scheduler box. Its drop frees the task
    // table (and every process heap), the timer wheel, and the run-queue in
    // one shot — replacing the per-thread-local clears the old code ran here.
    drop(unsafe { Box::from_raw(sched) });
    0
}

/// fz-4mk.3b — register the `fz_drain_dtor_entry` shim address. Called from
/// AOT-emitted C main after `fz_aot_setup`. The run-queue loop dispatches
/// each entry on `process.heap.pending_dtors` through this shim when a
/// task exits.
///
/// # Safety
/// `proc` must be a process produced by `fz_aot_setup`. `addr` must be the
/// address of `fz_drain_dtor_entry` emitted by compile_with_backend (SystemV
/// `(closure: u64, payload: u64) -> i64`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_aot_set_drain_dtor_entry(proc: *mut Process, addr: *const u8) {
    unsafe { (*sched_of(proc)).drain_dtor_entry = addr };
}

/// fz-xx8.1 — register the `fz_resume` shim address. Called from AOT-emitted
/// C main after `fz_aot_setup` and before `fz_aot_run_main`. The run-queue
/// loop resumes each task's `runnable` closure through this shim
/// (mirrors the JIT path in `src/ir_codegen.rs:335`).
///
/// # Safety
/// `proc` must be a process produced by `fz_aot_setup`. `addr` must be the
/// address of `fz_resume` emitted by compile_with_backend (SystemV
/// `(cont: u64) -> i64`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_aot_set_resume_addr(proc: *mut Process, addr: *const u8) {
    unsafe { (*sched_of(proc)).resume_addr = addr };
}

/// Shim addresses snapshotted off the scheduler once per `aot_run_queue_loop`
/// invocation, then threaded to `dispatch_quantum` so each iteration reads
/// them by value rather than re-deref the scheduler.
struct ShimAddrs {
    resume: *const u8,
}

fn closure_ref_word(closure: *mut u8) -> u64 {
    crate::any_value::AnyValueRef::from_heap_object(
        crate::any_value::ValueKind::CLOSURE,
        closure as *const u8,
    )
    .expect("scheduler closure ref")
    .raw_word()
}

/// Drain the AOT timer wheel and apply each expired entry to its task
/// via `sched::fire_after_timer`. Tasks that fire get enqueued.
fn drain_after_timers_aot(sched: *mut AotScheduler) {
    let expired = unsafe { (*sched).timers.drain_expired(std::time::Instant::now()) };
    for entry in expired {
        let woke = unsafe {
            (*sched)
                .tasks
                .get_mut(&entry.pid)
                .map(|task| crate::sched::fire_after_timer(task, entry.id))
                .unwrap_or(false)
        };
        if woke {
            unsafe { (*sched).run_queue.push_back(entry.pid) };
        }
    }
}

/// Run one quantum for `pid`: pick dispatch branch by Process state,
/// invoke the matching SystemV shim, then handle the post-quantum state
/// transition (re-enqueue / halt / mid-flight yield). Returns nothing;
/// scheduler state is mutated in place.
fn dispatch_quantum(sched: *mut AotScheduler, pid: u32, addrs: &ShimAddrs) {
    let proc_ptr = unsafe {
        (*sched)
            .tasks
            .get(&pid)
            .map(|b| b.as_ref() as *const Process as *mut Process)
    }
    .unwrap_or_else(|| {
        eprintln!("aot_run_queue_loop: pid {} not in tasks", pid);
        std::process::abort();
    });

    // Mark Running so a clean halt (no fz_receive_park call) is
    // distinguishable from Blocked/Ready after dispatch.
    unsafe {
        (*proc_ptr).state = ProcessState::Running;
        (*proc_ptr).reset_reduction_budget();
        (*proc_ptr).ctx = &mut (*sched).ctx;
        (*proc_ptr).heap.set_owner(proc_ptr);
        debug_assert!(!(*proc_ptr).ctx.is_null(), "aot ctx installed");
    };

    // fz-qw6 — selective-receive initial scan lifted to runtime::sched.
    let process = unsafe { &mut *proc_ptr };
    match crate::sched::initial_scan(process) {
        crate::sched::ScanOutcome::Hit => {
            // Fall through to the resume below.
        }
        crate::sched::ScanOutcome::Miss => {
            return;
        }
        crate::sched::ScanOutcome::NotApplicable => {}
    }

    fn run_scheduler_closure(resume_addr: *const u8, process: *mut Process, closure: *mut u8) {
        let _ =
            unsafe { crate::pinned_abi::call1(resume_addr, process, closure_ref_word(closure)) };
    }

    // One re-entry verb: resume the task's `runnable` closure (a fresh entry
    // thunk for a spawned task / main, or a continuation for a receive or
    // mid-flight wakeup). Bound args travel in the closure env.
    if let Some(closure) = unsafe { (*proc_ptr).take_runnable_closure() } {
        run_scheduler_closure(addrs.resume, proc_ptr, closure);
    }
    // Post-quantum state check.
    let state = unsafe { (*proc_ptr).state };
    let has_runnable = unsafe { (*proc_ptr).runnable.is_some() };
    if state == ProcessState::Running && has_runnable {
        let process = unsafe { &mut *proc_ptr };
        if process.needs_boundary_gc() {
            let mut root = process.runnable_ptr();
            process
                .heap
                .gc_process_roots(&mut root, &mut process.mailbox);
            process.set_runnable_closure(root);
            process.quiet_quanta = 0;
        } else {
            process.quiet_quanta = process.quiet_quanta.saturating_add(1);
        }
        process.clear_yield_reasons();
        unsafe {
            (*proc_ptr).state = ProcessState::Ready;
            (*sched).run_queue.push_back(pid);
        }
    } else if state == ProcessState::Ready {
        unsafe { (*sched).run_queue.push_back(pid) };
    } else if state == ProcessState::Running && unsafe { (*proc_ptr).wait.is_none() } {
        // fz-4mk.3b — task halted; flush MSO resources through the dtor
        // drain shim before the heap drops.
        unsafe { (*proc_ptr).state = ProcessState::Exited };
        let drain_addr = unsafe { (*sched).drain_dtor_entry };
        if !drain_addr.is_null() {
            let process = unsafe { &mut *proc_ptr };
            crate::procbin::mso_drop_all_deferred(&mut process.heap);
            while let Some((closure, payload_ref)) = process.heap.pending_dtors.pop_front() {
                let _ =
                    unsafe { crate::pinned_abi::call2(drain_addr, proc_ptr, closure, payload_ref) };
            }
        }
    }
}

/// Cooperative run-queue loop. Drives all enqueued processes to
/// completion or Blocked state. Each iteration: drain expired timers,
/// pop a pid (idle-wait if the queue is empty but timers pend),
/// dispatch one quantum.
///
/// Dispatch inside `dispatch_quantum`:
///   1. selective-receive initial scan (fz-qw6 helper) — Hit moves the
///      outcome into `runnable`; Miss returns the task to Blocked.
///   2. resume `runnable` through `fz_resume` — the one re-entry verb,
///      whether it holds a fresh-task entry thunk or a continuation.
fn aot_run_queue_loop(sched: *mut AotScheduler) {
    let addrs = unsafe {
        ShimAddrs {
            resume: (*sched).resume_addr,
        }
    };

    loop {
        drain_after_timers_aot(sched);

        let Some(pid) = (unsafe { (*sched).run_queue.pop_front() }) else {
            // Queue empty. Sleep until the next timer deadline if one
            // exists; otherwise truly idle, break. (Multi-worker AOT
            // will need a condvar here instead of a blocking sleep.)
            let next = unsafe { (*sched).timers.next_deadline() };
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
        dispatch_quantum(sched, pid, &addrs);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A bare scheduler for unit tests. The caller pushes tasks into
    /// `tasks` and passes `sched_handle(&mut sched)` as the erased scheduler
    /// handle the hooks re-narrow — the same handle `ExecCtx.scheduler`
    /// carries in production.
    fn test_scheduler() -> AotScheduler {
        AotScheduler {
            next_pid: 2,
            tasks: HashMap::new(),
            entry_thunk: std::ptr::null(),
            halt_cont_bodies: [std::ptr::null(); 3],
            run_queue: VecDeque::new(),
            drain_dtor_entry: std::ptr::null(),
            resume_addr: std::ptr::null(),
            timers: TimerWheel::new(),
            ctx: ExecCtx::empty(),
        }
    }

    fn sched_handle(sched: &mut AotScheduler) -> *mut () {
        sched as *mut AotScheduler as *mut ()
    }

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

    #[test]
    fn aot_send_deep_copies_message_into_receiver_heap() {
        use crate::any_value::AnyValueRef;

        let mut sched = test_scheduler();

        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let mut sender = Box::new(Process::new(schemas.clone()));
        sender.pid = 1;
        let msg = sender
            .heap
            .alloc_list_cons_int(42, AnyValueRef::empty_list())
            .expect("sender list ref");
        let sender_addr = msg.list_addr().expect("sender list addr");

        let mut receiver = Box::new(Process::new(schemas));
        receiver.pid = 2;
        receiver.state = ProcessState::Blocked;

        sched.tasks.insert(1, sender);
        sched.tasks.insert(2, receiver);
        let sender_ptr = sched
            .tasks
            .get_mut(&1)
            .map(|p| p.as_mut() as *mut Process)
            .expect("sender task");

        aot_send_hook(sender_ptr, sched_handle(&mut sched), 2, msg.raw_word());

        let sender = sched.tasks.get(&1).expect("sender");
        let receiver = sched.tasks.get(&2).expect("receiver");
        let copied = receiver.mailbox.front().expect("receiver mailbox");
        let copied_addr = copied.list_addr().expect("copied list addr");
        assert_ne!(copied_addr, sender_addr);
        assert!(sender.heap.contains_heap_addr(sender_addr));
        assert!(receiver.heap.contains_heap_addr(copied_addr));
    }

    /// fz-xx8.3 — schedule→drain→wake flow on the AOT timer wheel.
    /// Mirrors `src/runtime.rs::drain_expired_timers_wakes_after_cont`. We
    /// can't drive aot_run_queue_loop directly (it would call into
    /// codegen'd shim pointers we don't have), but we exercise every
    /// pre-dispatch ingredient: schedule → expiry → mutate the task's
    /// wait into a runnable_closure → run-queue enqueue. The
    /// dispatch-via-resume-shim step is covered by the end-to-end fixture
    /// run on a built binary.
    #[test]
    fn timer_drain_wakes_after_cont() {
        use crate::park::ParkRecord;
        use crate::process::{Process, ProcessState};

        let mut sched = test_scheduler();

        // Stand up a single task with a wait that has an
        // after_timer_id. matcher_fn is unused on the drain path.
        extern "C" fn never_match(
            _process: *mut Process,
            _msg: u64,
            _pinned: *const crate::any_value::AnyValueRef,
            _out: *mut crate::any_value::AnyValueRef,
        ) -> u32 {
            0
        }
        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let mut p = Box::new(Process::new(schemas));
        p.pid = 7;
        let timer_id = aot_timer_schedule_hook(sched_handle(&mut sched), p.pid, 1);
        let after_cont_addr: usize = 0xCAFE_BABE;
        p.wait = Some(Box::new(ParkRecord {
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
        sched.tasks.insert(7, p);

        // Wait past the deadline, then run the same drain logic
        // aot_run_queue_loop runs at the top of each iteration.
        std::thread::sleep(std::time::Duration::from_millis(5));
        let expired = sched.timers.drain_expired(std::time::Instant::now());
        assert_eq!(expired.len(), 1);
        for entry in expired {
            {
                let task = sched.tasks.get_mut(&entry.pid).unwrap();
                let park = task.wait.as_ref().unwrap();
                assert_eq!(park.after_timer_id, Some(entry.id));
                let after_cont = park.after_cont;
                task.wait = None;
                task.set_runnable_closure(after_cont);
                task.state = ProcessState::Ready;
            }
            sched.run_queue.push_back(entry.pid);
        }

        let task = sched.tasks.get(&7).unwrap();
        assert_eq!(task.state, ProcessState::Ready);
        assert!(task.wait.is_none());
        assert_eq!(task.runnable_ptr() as usize, after_cont_addr);
        assert!(sched.run_queue.iter().any(|p| *p == 7));
    }

    /// fz-xx8.3 — `aot_timer_cancel_hook` retires a previously scheduled
    /// timer so a sender-probe / initial-scan hit can prevent the after
    /// from firing.
    #[test]
    fn timer_cancel_removes_pending_entry() {
        let mut sched = test_scheduler();

        let id = aot_timer_schedule_hook(sched_handle(&mut sched), 99, 10_000);
        assert!(sched.timers.next_deadline().is_some());
        aot_timer_cancel_hook(sched_handle(&mut sched), id);
        assert!(sched.timers.next_deadline().is_none());
    }

    /// fz-xx8.1 — `fz_aot_set_resume_addr` records the shim address on the
    /// scheduler reached through `proc.ctx.scheduler`. We can't drive a full
    /// setup→run→teardown cycle from a unit test (it needs a real codegen'd
    /// shim), so we wire one process at the scheduler and assert the setter
    /// lands the address on it.
    #[test]
    fn set_resume_addr_records_on_scheduler() {
        let mut sched = test_scheduler();
        let sched_ptr: *mut AotScheduler = &mut sched;
        sched.ctx.scheduler = sched_ptr as *mut ();

        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let mut p = Box::new(Process::new(schemas));
        p.pid = 1;
        p.ctx = &mut sched.ctx;

        let fake = 0xDEAD_BEEFusize as *const u8;
        unsafe { fz_aot_set_resume_addr(p.as_mut(), fake) };
        assert_eq!(sched.resume_addr, fake);
    }
}
