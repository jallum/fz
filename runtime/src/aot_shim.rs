//! Runtime entry point for AOT-compiled fz binaries (fz-siu.6.1 / .6.2).
//!
//! AOT codegen emits a C-callable `main` that drives the cps-in-clif
//! execution model:
//!
//!   1. `proc = fz_aot_setup(atom_blob, atom_blob_len, halt_cont_body_addr,
//!                            entry_thunk_addr)`
//!   2. for each static closure target:
//!      `fz_aot_register_static_closure(proc, cl_sid, fn_id, code_addr)`
//!   3. `exit = fz_aot_run_main(proc, main_fp, main_trampoline_addr, main_halt_kind)`
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
//! `fz_aot_run_main`. `fz_receive_park_matched` parks a process (sets state =
//! Blocked / Ready); `aot_send_hook` wakes blocked receivers through the
//! selective-receive probe path. This matches the JIT's `run_until_idle`
//! semantics.

use crate::any_value::{AnyValue, AnyValueRef, ValueKind, closure_addr_from_tagged};
use crate::exec_ctx::ExecCtx;
use crate::heap::{Heap, Schema, SchemaRegistry, deep_copy_any_value_ref};
use crate::pinned_abi::{call1, call2};
use crate::procbin::mso_drop_all_deferred;
use crate::process::{CompiledModuleConsts, DEFAULT_REDUCTIONS_PER_QUANTUM, Node, Process, ProcessState};
use crate::resource::{ResourceHandle, alloc_resource, fz_resource_destructor_noop};
use crate::sched::{
    ProbeOutcome, ScanOutcome, fire_after_timer, initial_scan, mint_entry_thunk, mint_main_inner, probe_sender,
};
use crate::timer::TimerWheel;
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::process::abort;
use std::ptr::{null, read_unaligned};
use std::rc::Rc;
use std::slice::from_raw_parts;
use std::str::from_utf8;
use std::thread::sleep;
use std::time::{Duration, Instant};

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
    /// fz-ul4.27.22.3 — four halt_cont_body addrs retained so spawned
    /// children can initialize their own halt_cont_singletons.
    halt_cont_bodies: [*const u8; 4],
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
                abort();
            }
        }
        if len == 0 {
            break;
        }
        let bytes = unsafe { from_raw_parts(cur, len) };
        match from_utf8(bytes) {
            Ok(s) => out.push(s.to_string()),
            Err(_) => out.push(String::new()),
        }
        cur = unsafe { cur.add(len + 1) };
    }
    out
}

fn parse_named_schema_blob(blob: *const u8, len: u32) -> Vec<(String, Vec<String>)> {
    if blob.is_null() || len == 0 {
        return Vec::new();
    }
    let bytes = unsafe { from_raw_parts(blob, len as usize) };
    let mut pos = 0usize;
    fn read_u32(bytes: &[u8], pos: &mut usize) -> u32 {
        let end = *pos + 4;
        if end > bytes.len() {
            eprintln!("parse_named_schema_blob: truncated u32");
            abort();
        }
        let mut raw = [0u8; 4];
        raw.copy_from_slice(&bytes[*pos..end]);
        *pos = end;
        u32::from_ne_bytes(raw)
    }
    fn read_string(bytes: &[u8], pos: &mut usize) -> String {
        let len = read_u32(bytes, pos) as usize;
        let end = *pos + len;
        if end > bytes.len() {
            eprintln!("parse_named_schema_blob: truncated string");
            abort();
        }
        let s = from_utf8(&bytes[*pos..end])
            .unwrap_or_else(|_| {
                eprintln!("parse_named_schema_blob: invalid utf-8");
                abort();
            })
            .to_string();
        *pos = end;
        s
    }

    let schema_count = read_u32(bytes, &mut pos);
    let mut out = Vec::with_capacity(schema_count as usize);
    for _ in 0..schema_count {
        let name = read_string(bytes, &mut pos);
        let field_count = read_u32(bytes, &mut pos);
        let mut fields = Vec::with_capacity(field_count as usize);
        for _ in 0..field_count {
            fields.push(read_string(bytes, &mut pos));
        }
        out.push((name, fields));
    }
    if pos != bytes.len() {
        eprintln!("parse_named_schema_blob: trailing bytes");
        abort();
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
    halt_cont_body_atom: *const u8,
    entry_thunk_addr: *const u8,
) -> *mut Process {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));

    // The AOT run's node-global atom table, seeded from the program's atom
    // blob and shared (Rc) by every spawned process.
    let node = Rc::new(Node::new(parse_atom_blob(atom_blob), Vec::new()));
    let proc_box = Box::new(Process::from_consts(
        node,
        schemas,
        &CompiledModuleConsts::empty(),
        1,
        DEFAULT_REDUCTIONS_PER_QUANTUM,
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
            halt_cont_body_atom,
        ],
        run_queue: VecDeque::new(),
        drain_dtor_entry: null(),
        resume_addr: null(),
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
        let proc_ptr = (*sched).tasks.get_mut(&1).map(|b| b.as_mut() as *mut Process).unwrap();
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
    let dtor_ref = AnyValueRef::from_raw_word(dtor_ref).expect("fz_make_resource (AOT): dtor ref");
    let dtor_closure = AnyValue::from_ref(dtor_ref).expect("fz_make_resource (AOT): dtor value");
    let dtor_closure_bits = dtor_closure
        .heap_object_word()
        .expect("fz_make_resource (AOT): dtor arg is not a closure");
    if closure_addr_from_tagged(dtor_closure_bits).is_none() {
        eprintln!("fz_make_resource (AOT): dtor arg is not a closure");
        abort();
    }
    assert!(!process.is_null(), "fz_make_resource (AOT): no current process");
    let heap = unsafe { &mut (*process).heap };
    let handle = ResourceHandle::new(payload_raw, fz_resource_destructor_noop);
    let stub = alloc_resource(heap, handle, dtor_closure);
    AnyValueRef::from_heap_object(ValueKind::RESOURCE, stub.as_raw() as *const u8)
        .expect("resource ref")
        .raw_word()
}

/// fz-ul4.38 — register the program's tuple schemas with the AOT process,
/// in the order baked into the `fz_aot_tuple_arities` data symbol. Codegen
/// first registers `ClosureEnv0`, then iterates arities in sorted order; this
/// fn registers in that same order so the schema ids match what was iconst'd
/// into the emitted CLIF.
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
    assert!(!proc.is_null(), "fz_aot_register_tuple_schemas: null process");
    // Read the shim addrs off the scheduler before taking the &mut Process —
    // `sched_of` reads `proc.ctx`, which must not alias the live &mut below.
    let halt_cont_bodies = unsafe { (*sched_of(proc)).halt_cont_bodies };
    let process = unsafe { &mut *proc };
    process.heap.closure_schema_id(0);
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
            let arity = unsafe { read_unaligned(arities.add(i as usize)) };
            let id = reg.register(Schema::tuple_of_arity(arity as usize));
            match arity {
                1 => process.bs_tuple_arity1_schema = Some(id),
                3 => process.bs_tuple_arity3_schema = Some(id),
                _ => {}
            }
        }
    }
    process.init_halt_cont_singletons(halt_cont_bodies);
}

/// Register named source `defstruct` schemas with the AOT process in the
/// deterministic order codegen used when baking schema ids into CLIF.
///
/// # Safety
/// `proc` must be a process produced by `fz_aot_setup`. `blob` must point at
/// `len` bytes emitted by AOT codegen when len > 0.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_aot_register_named_schemas(proc: *mut Process, blob: *const u8, len: u32) {
    assert!(!proc.is_null(), "fz_aot_register_named_schemas: null process");
    let process = unsafe { &mut *proc };
    let registry = process.heap.schemas_registry();
    let mut reg = registry.borrow_mut();
    for (name, fields) in parse_named_schema_blob(blob, len) {
        reg.register(Schema::named_struct(name, fields));
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
    assert!(!proc.is_null(), "fz_aot_register_static_closure: null process");
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
    let node = Rc::clone(&parent.node);

    let consts = CompiledModuleConsts {
        halt_cont_body_addrs,
        ..CompiledModuleConsts::empty()
    };
    let mut child = Box::new(Process::from_consts(
        node,
        schemas,
        &consts,
        pid,
        DEFAULT_REDUCTIONS_PER_QUANTUM,
    ));
    // Inherit the parent's already-built static-closure singletons by copying
    // the pointers (they alias the parent's process-lifetime buffers).
    child.static_closures = static_closures;

    // Deep-copy the closure into the child's heap.
    let mut forwarding = HashMap::new();
    let closure_ref = AnyValueRef::from_raw_word(closure_bits).expect("aot_spawn_hook: closure ref");
    let copied = deep_copy_any_value_ref(closure_ref, &parent.heap, &mut child.heap, &mut forwarding);
    let copied_addr = copied
        .closure_addr()
        .expect("aot_spawn_hook: copied closure must be a closure");

    // Wrap the copied closure in an entry thunk queued as `runnable`; the
    // run-queue loop resumes it via `fz_resume`. `parent`/`sender` are no
    // longer read past this point, so mutating `sched.tasks` is safe.
    let thunk = mint_entry_thunk(&mut child.heap, entry_thunk_addr, copied_addr);
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

fn deep_copy_send_ref_for_aot(sender: &Process, receiver: &mut Process, msg: AnyValueRef) -> AnyValueRef {
    let mut forwarding = HashMap::new();
    deep_copy_any_value_ref(msg, &sender.heap, &mut receiver.heap, &mut forwarding)
}

fn deep_copy_self_send_ref_for_aot(sender: &mut Process, msg: AnyValueRef) -> AnyValueRef {
    let mut forwarding = HashMap::new();
    let heap_ptr: *mut Heap = &mut sender.heap as *mut _;
    let src_heap: &Heap = unsafe { &*heap_ptr };
    let dst_heap: &mut Heap = unsafe { &mut *heap_ptr };
    deep_copy_any_value_ref(msg, src_heap, dst_heap, &mut forwarding)
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
/// Selective-receive arrivals route through `sched::probe_sender`, which
/// flips a matched blocked receiver to Ready and enqueues it.
extern "C" fn aot_send_hook(sender_ptr: *mut Process, scheduler: *mut (), receiver_pid: u32, msg_ref_word: u64) {
    let msg = AnyValueRef::from_raw_word(msg_ref_word).expect("aot_send message ref");
    assert!(!sender_ptr.is_null(), "aot_send_hook: no sender process");
    let sched = scheduler as *mut AotScheduler;
    let wake = {
        let tasks = unsafe { &mut (*sched).tasks };
        let Some(task) = tasks.get_mut(&receiver_pid) else {
            eprintln!("aot_send: no task with pid {}", receiver_pid);
            abort();
        };
        let msg = if task.pid == unsafe { (*sender_ptr).pid } {
            deep_copy_self_send_ref_for_aot(task, msg)
        } else {
            let sender = unsafe { &*sender_ptr };
            deep_copy_send_ref_for_aot(sender, task, msg)
        };
        if task.wait.is_some() {
            matches!(probe_sender(task, msg), ProbeOutcome::Hit)
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
/// by AOT codegen and `fz_aot_setup`; `main_halt_kind` must match the entry
/// fn's computed halt seam kind. Called only from the AOT-emitted
/// C `main`; clippy's `not_unsafe_ptr_arg_deref` is silenced because
/// the C ABI signature is fixed.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_aot_run_main(
    proc: *mut Process,
    main_fp: *const u8,
    main_trampoline_addr: *const u8,
    main_halt_kind: u32,
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
    // `runnable`. The scheduler resumes it through the one `fz_resume` verb,
    // like any task; the inner closure carries the entry fn's halt_kind so the
    // thunk picks the matching halt continuation body.
    let process = unsafe { &mut *proc };
    let inner = mint_main_inner(&mut process.heap, main_trampoline_addr, main_fp, main_halt_kind as u16);
    let thunk = mint_entry_thunk(&mut process.heap, entry_thunk_addr, inner);
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
    AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure as *const u8)
        .expect("scheduler closure ref")
        .raw_word()
}

/// Drain the AOT timer wheel and apply each expired entry to its task
/// via `sched::fire_after_timer`. Tasks that fire get enqueued.
fn drain_after_timers_aot(sched: *mut AotScheduler) {
    let expired = unsafe { (*sched).timers.drain_expired(Instant::now()) };
    for entry in expired {
        let woke = unsafe {
            (*sched)
                .tasks
                .get_mut(&entry.pid)
                .map(|task| fire_after_timer(task, entry.id))
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
        abort();
    });

    // Mark Running so a clean halt (no selective-receive park call) is
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
    match initial_scan(process) {
        ScanOutcome::Hit => {
            // Fall through to the resume below.
        }
        ScanOutcome::Miss => {
            return;
        }
        ScanOutcome::NotApplicable => {}
    }

    fn run_scheduler_closure(resume_addr: *const u8, process: *mut Process, closure: *mut u8) {
        let _ = unsafe { call1(resume_addr, process, closure_ref_word(closure)) };
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
            process.heap.gc_process_roots(&mut root, &mut process.mailbox);
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
            mso_drop_all_deferred(&mut process.heap);
            while let Some((closure, payload_ref)) = process.heap.pending_dtors.pop_front() {
                let _ = unsafe { call2(drain_addr, proc_ptr, closure, payload_ref) };
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
                    let now = Instant::now();
                    if deadline > now {
                        sleep(deadline - now);
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
#[path = "aot_shim_test.rs"]
mod aot_shim_test;
