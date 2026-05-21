//! fz-ul4.23.5.2 — IR interpreter on FzValue, heap, and runtime substrate.
//!
//! Walks a `fz_ir::Module` directly, just like the legacy ir_interp.rs, but
//! uses the SAME value representation, heap, and runtime FFI as the JIT.
//! Spawn/send/receive call into the same runtime.rs scheduler. Print
//! renders through `fz_runtime::ir_runtime::fz_print_value`. Heap allocations
//! go through the current Process's Heap.
//!
//! Scope at .5.2: minimal for fixtures/add1/input.fz —
//!   Const::{Int, Atom, Nil, True, False}
//!   BinOp::Add  (Int + Int)
//!   Term::{Call, Return, Halt}
//!
//! Subsequent atoms expand the surface fixture by fixture:
//!   .5.3 scalars + print + other arith
//!   .5.4 closures + higher-order
//!   .5.5 pattern dispatch
//!   .5.6 modules
//!   .5.7 tail recursion (TCO)
//!   .5.8 spawn/send/receive

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use crate::types::AtomTypeTest;
use crate::types_seam::Types;

use crate::fz_ir::{BinOp, Const, ExternId, ExternTy, FnId, Module, Prim, Stmt, Term, Var};
use fz_runtime::fz_value::FzValue;
use fz_runtime::process::Process;

// ===== Interp-internal scheduler (fz-ul4.23.5.8 / fz-sched.3) =====
//
// The interp owns its own task registry separate from runtime.rs::Runtime
// (which is wired into the JIT trampoline). They share the Process type,
// the FzValue rep, and the heap — so messages and mailboxes are byte-
// compatible between paths.
//
// Scheduling model (fz-sched.3): cooperative run-queue, BEAM-correct.
// Builtin::Spawn enqueues the child and returns immediately; the parent
// continues its own quantum. Term::Receive parks the task (InterpStep::Blocked)
// if the mailbox is empty; the scheduler records the resume state and moves on.
// interp_send flips a Blocked receiver to Ready, prepends the message to its
// resume args, and re-enqueues it. run_main drives the loop until the queue
// is empty.
//
// Limitation: Blocked propagates as an error through non-tail call sites
// (Term::Call / Term::CallClosure). In practice all fixture receive sites are
// in tail position inside spawned fns, so this doesn't matter yet.

use std::collections::VecDeque;

/// Returned by run_fn to signal either completion or a receive-park.
enum InterpStep {
    Done(FzValue),
    /// Task parked on receive. `resume_fn(msg, cap_vals...)` is called when
    /// the message arrives. `after` is a chain of (fn_id, caps) continuations
    /// to call in order with each successive return value — built up when
    /// Blocked propagates through Term::Call frames.
    Blocked(FnId, Vec<FzValue>, Vec<(FnId, Vec<FzValue>)>),
    /// fz-yxs/fz-2v3 — task parked on a selective `receive do … end`. The
    /// park record snapshots every clause's pattern + body / guard FnId
    /// plus the pinned ^name and capture FzValues from the receive site
    /// so that `interp_send` can probe new messages without recreating
    /// any of that state.
    BlockedMatched(ParkRecord, Vec<(FnId, Vec<FzValue>)>),
}

/// fz-yxs/fz-2v3 — interp park record for a selective receive.
/// `after` is consumed inline at park time (the `after 0` case fires
/// before we park; non-zero/`:infinity` is treated as "no timer" in the
/// interp since there's no wall clock — the real timer wiring lands
/// for JIT/AOT in B2 via F2). So this struct only stores what the
/// sender-side probe needs.
#[derive(Clone)]
struct ParkRecord {
    clauses: Vec<MatchedClause>,
    pinned: HashMap<String, FzValue>,
    captures: Vec<FzValue>,
}

#[derive(Clone)]
struct MatchedClause {
    pattern: crate::ast::Pattern,
    bound_names: Vec<String>,
    guard: Option<FnId>,
    body: FnId,
}

/// Per-task resume state: fn to call, captures (no message), and after-chain.
type ResumeEntry = (FnId, Vec<FzValue>, Vec<(FnId, Vec<FzValue>)>);

thread_local! {
    static INTERP_TASKS: RefCell<HashMap<u32, Box<Process>>> =
        RefCell::new(HashMap::new());
    static INTERP_NEXT_PID: Cell<u32> = const { Cell::new(2) };
    static INTERP_SCHEMAS: RefCell<Option<std::rc::Rc<std::cell::RefCell<fz_runtime::heap::SchemaRegistry>>>> =
        const { RefCell::new(None) };
    /// fz-ul4.35 — per-run map from tuple arity to heap schema id.
    /// Populated lazily by Prim::MakeTuple via interp_tuple_schema_id; cleared
    /// at run_main / run_test_fn entry so each run starts fresh.
    static INTERP_TUPLE_SCHEMA_IDS: RefCell<HashMap<usize, u32>> =
        RefCell::new(HashMap::new());
    /// FIFO run-queue of pids ready to execute.
    static INTERP_RUN_QUEUE: RefCell<VecDeque<u32>> = const { RefCell::new(VecDeque::new()) };
    /// Per-task resume state: (resume_fn, cap_vals, after_chain).
    /// cap_vals holds captures only (no message); interp_send prepends the
    /// message. after_chain is the sequence of (fn_id, caps) continuations to
    /// invoke in order after resume_fn returns, passing each return value on.
    static INTERP_RESUME: RefCell<HashMap<u32, ResumeEntry>> =
        RefCell::new(HashMap::new());
    /// fz-yxs/fz-2v3 — selective-receive park records. Keyed by pid so
    /// that `interp_send` can probe an arriving message against the
    /// receiver's parked matcher without unwinding the scheduler.
    static INTERP_PARKED: RefCell<HashMap<u32, InterpParked>> =
        RefCell::new(HashMap::new());
}

/// fz-yxs/fz-2v3 — value type for `INTERP_PARKED`. Factored out so
/// the TLS entry doesn't trip clippy's "very complex type" lint.
type InterpParked = (ParkRecord, Vec<(FnId, Vec<FzValue>)>);

/// fz-ul4.35 — get-or-register a heap schema for a tuple of `arity`,
/// matching the JIT codegen layout in src/ir_codegen.rs (Tuple{N}, N*8
/// payload bytes, N FzValue fields at offsets 0, 8, 16, ...).
fn interp_tuple_schema_id(arity: usize) -> u32 {
    INTERP_TUPLE_SCHEMA_IDS.with(|m| {
        if let Some(&id) = m.borrow().get(&arity) {
            return id;
        }
        use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
        let s = Schema {
            name: format!("Tuple{}", arity),
            size: (arity * 8) as u32,
            fields: (0..arity)
                .map(|i| FieldDescriptor {
                    offset: (i * 8) as u32,
                    kind: FieldKind::FzValue,
                })
                .collect(),
        };
        let registry = fz_runtime::process::current_process()
            .heap
            .schemas_registry();
        let id = registry.borrow_mut().register(s);
        m.borrow_mut().insert(arity, id);
        id
    })
}

/// fz-yxs/fz-2v3 — match an FzValue against a pattern AST. Returns
/// Some(bindings) on a successful match; None otherwise. `pinned`
/// supplies the resolved value for every `^name` reference in the
/// pattern. Bindings are accumulated in source-traversal order to
/// align with `ReceiveClause::bound_names`.
///
/// Equality semantics for pinned values: bit-equality on the
/// `FzValue.0` u64. Correct for ints / atoms / refs and any other
/// inline-tagged value. Structural equality for boxed payloads
/// (deep tuples, lists, maps) is not yet implemented — none of the
/// fixtures need it, and the matcher's purity restriction already
/// rules out anything that would allocate.
fn try_match_pattern(
    module: &Module,
    pat: &crate::ast::Pattern,
    val: FzValue,
    pinned: &HashMap<String, FzValue>,
    out: &mut Vec<(String, FzValue)>,
) -> bool {
    use crate::ast::Pattern;
    use fz_runtime::fz_value::Tag;
    match pat {
        Pattern::Wildcard => true,
        Pattern::Var(name) => {
            out.push((name.clone(), val));
            true
        }
        Pattern::As(name, inner) => {
            out.push((name.clone(), val));
            try_match_pattern(module, &inner.node, val, pinned, out)
        }
        Pattern::Pinned(name) => match pinned.get(name) {
            Some(want) => want.0 == val.0,
            None => false,
        },
        Pattern::Int(n) => val.tag() == Tag::Int && val.unbox_int() == Some(*n),
        Pattern::Float(_) => false, // floats live on the heap; not used by current fixtures
        Pattern::Str(_) => false,
        Pattern::Atom(name) => {
            if val.tag() != Tag::Atom {
                return false;
            }
            let id = match val.unbox_atom() {
                Some(id) => id,
                None => return false,
            };
            module
                .atom_names
                .iter()
                .position(|n| n == name)
                .is_some_and(|pos| pos as u32 == id)
        }
        Pattern::Bool(true) => val.is_true(),
        Pattern::Bool(false) => val.is_false(),
        Pattern::Nil => val.is_nil(),
        Pattern::Tuple(elems) => {
            let Some(p) = val.unbox_ptr() else {
                return false;
            };
            let header = unsafe { &*p };
            use fz_runtime::fz_value::HeapKind;
            if HeapKind::from_u16(header.kind) != Some(HeapKind::Struct) {
                return false;
            }
            if header.schema_id != interp_tuple_schema_id(elems.len()) {
                return false;
            }
            for (i, e) in elems.iter().enumerate() {
                let off = 16 + i * 8;
                let field: FzValue =
                    unsafe { std::ptr::read((p as *const u8).add(off) as *const FzValue) };
                if !try_match_pattern(module, &e.node, field, pinned, out) {
                    return false;
                }
            }
            true
        }
        Pattern::List(_, _) | Pattern::Map(_) | Pattern::Bitstring(_) => false,
    }
}

/// fz-yxs/fz-2v3 — try matching the message against each clause's
/// pattern + guard in order; first match wins. Returns the matched
/// clause index plus the bindings list (in source order, aligned with
/// `MatchedClause::bound_names`) on success.
fn try_match_clauses<T: Types<Ty = crate::types_seam::Ty>>(
    t: &mut T,
    module: &Module,
    clauses: &[MatchedClause],
    msg: FzValue,
    pinned: &HashMap<String, FzValue>,
    captures: &[FzValue],
) -> Result<Option<(usize, Vec<FzValue>)>, String> {
    for (i, c) in clauses.iter().enumerate() {
        let mut binds: Vec<(String, FzValue)> = Vec::new();
        if !try_match_pattern(module, &c.pattern, msg, pinned, &mut binds) {
            continue;
        }
        // Align with declared bound_names order. The matcher walked the
        // pattern in source order too, so this should always succeed —
        // but the explicit reorder protects against any future drift.
        let mut bound_vals: Vec<FzValue> = Vec::with_capacity(c.bound_names.len());
        for name in &c.bound_names {
            let Some((_, v)) = binds.iter().rev().find(|(n, _)| n == name) else {
                return Err(format!(
                    "try_match_clauses: bound name `{}` missing from pattern walk",
                    name
                ));
            };
            bound_vals.push(*v);
        }
        if let Some(g_fid) = c.guard {
            let mut g_args = bound_vals.clone();
            g_args.extend_from_slice(captures);
            let g_step = run_fn(t, module, g_fid, g_args)?;
            let g_val = match g_step {
                InterpStep::Done(v) => v,
                InterpStep::Blocked(..) | InterpStep::BlockedMatched(..) => {
                    return Err("receive guard parked on receive — guards must be pure".into());
                }
            };
            if g_val.is_false() || g_val.is_nil() {
                continue;
            }
        }
        return Ok(Some((i, bound_vals)));
    }
    Ok(None)
}

fn interp_register_task(pid: u32, process: Box<Process>) -> *mut Process {
    INTERP_TASKS.with(|t| {
        let mut tasks = t.borrow_mut();
        tasks.insert(pid, process);
        tasks
            .get_mut(&pid)
            .map(|b| b.as_mut() as *mut Process)
            .unwrap()
    })
}

fn interp_next_pid() -> u32 {
    INTERP_NEXT_PID.with(|n| {
        let p = n.get();
        n.set(p + 1);
        p
    })
}

fn interp_send<T: Types<Ty = crate::types_seam::Ty>>(
    t: &mut T,
    module: &Module,
    receiver_pid: u32,
    msg: FzValue,
) -> Result<(), String> {
    use fz_runtime::process::ProcessState;
    // fz-yxs/fz-2v3 — sender-side probe for selective receive. If the
    // receiver is parked on a Term::ReceiveMatched, run the parked
    // matcher inline against the new message; on a hit, set up the
    // matched clause's body as the receiver's next resume and wake it
    // without touching the mailbox.
    let parked = INTERP_PARKED.with(|p| p.borrow_mut().remove(&receiver_pid));
    if let Some((park, after_chain)) = parked {
        let hit = try_match_clauses(t, module, &park.clauses, msg, &park.pinned, &park.captures)?;
        match hit {
            Some((idx, bound_vals)) => {
                let body = park.clauses[idx].body;
                let mut args = bound_vals;
                args.extend(park.captures.iter().copied());
                INTERP_RESUME.with(|r| {
                    r.borrow_mut()
                        .insert(receiver_pid, (body, args, after_chain));
                });
                INTERP_TASKS.with(|t| {
                    if let Some(task) = t.borrow_mut().get_mut(&receiver_pid) {
                        task.state = ProcessState::Ready;
                    }
                });
                INTERP_RUN_QUEUE.with(|q| q.borrow_mut().push_back(receiver_pid));
                return Ok(());
            }
            None => {
                // Miss: park stays in place; message lands in mailbox.
                INTERP_PARKED.with(|p| {
                    p.borrow_mut().insert(receiver_pid, (park, after_chain));
                });
                INTERP_TASKS.with(|t| {
                    let mut tasks = t.borrow_mut();
                    if let Some(task) = tasks.get_mut(&receiver_pid) {
                        task.mailbox.push_back(msg);
                    } else {
                        eprintln!("send: no task with pid {}", receiver_pid);
                    }
                });
                return Ok(());
            }
        }
    }

    let was_blocked = INTERP_TASKS.with(|t| {
        let mut tasks = t.borrow_mut();
        match tasks.get_mut(&receiver_pid) {
            Some(task) => {
                if task.state == ProcessState::Blocked {
                    task.state = ProcessState::Ready;
                    true
                } else {
                    task.mailbox.push_back(msg);
                    false
                }
            }
            None => {
                eprintln!("send: no task with pid {}", receiver_pid);
                false
            }
        }
    });
    if was_blocked {
        // Blocked task has cap_vals in INTERP_RESUME; prepend message to form
        // the complete args for the next run_fn call, then re-enqueue.
        INTERP_RESUME.with(|r| {
            let mut resume = r.borrow_mut();
            if let Some(entry) = resume.get_mut(&receiver_pid) {
                entry.1.insert(0, msg); // prepend msg before cap_vals
            }
        });
        INTERP_RUN_QUEUE.with(|q| q.borrow_mut().push_back(receiver_pid));
    }
    Ok(())
}

fn interp_reset_state() {
    INTERP_TASKS.with(|t| t.borrow_mut().clear());
    INTERP_NEXT_PID.with(|n| n.set(2));
    INTERP_RUN_QUEUE.with(|q| q.borrow_mut().clear());
    INTERP_RESUME.with(|r| r.borrow_mut().clear());
    INTERP_PARKED.with(|p| p.borrow_mut().clear());
    INTERP_TUPLE_SCHEMA_IDS.with(|m| m.borrow_mut().clear());
}

/// Run `module`'s `main` fn through the interpreter.
///
/// Drives a cooperative run-queue loop: main starts at pid=1, spawned tasks
/// are enqueued and run one quantum at a time in FIFO order. Tasks that block
/// on receive park until a send wakes them. Loop exits when the queue is empty.
pub fn run_main(module: &Module) -> Result<i64, String> {
    use fz_runtime::process::ProcessState;
    let main_id = module.fn_by_name("main").ok_or("no `main/0` fn found")?.id;
    interp_reset_state();
    let user_schemas = std::rc::Rc::new(std::cell::RefCell::new(
        fz_runtime::heap::SchemaRegistry::new(),
    ));
    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = Some(user_schemas.clone()));
    let mut main_process = Box::new(Process::new(user_schemas));
    main_process.pid = 1;
    main_process.atom_names = module.atom_names.clone();
    main_process.state = ProcessState::Ready;
    interp_register_task(1, main_process);
    INTERP_RESUME.with(|r| r.borrow_mut().insert(1, (main_id, vec![], vec![])));
    INTERP_RUN_QUEUE.with(|q| q.borrow_mut().push_back(1));
    let mut t = crate::types_seam::ConcreteTypes;

    let mut halt_val = 0i64;
    'sched: while let Some(pid) = INTERP_RUN_QUEUE.with(|q| q.borrow_mut().pop_front()) {
        let (fn_id, args, mut after) = INTERP_RESUME
            .with(|r| r.borrow_mut().remove(&pid))
            .expect("pid in run_queue with no resume entry");
        let proc_ptr = INTERP_TASKS
            .with(|t| {
                t.borrow()
                    .get(&pid)
                    .map(|b| b.as_ref() as *const _ as *mut Process)
            })
            .expect("pid in run_queue with no process entry");
        unsafe { (*proc_ptr).state = ProcessState::Running };
        let prev = fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(proc_ptr));
        let mut step = run_fn(&mut t, module, fn_id, args);
        // Process the after-chain: each Done value is threaded into the next fn.
        loop {
            match step {
                Ok(InterpStep::Done(val)) => {
                    if let Some((next_fn, next_caps)) = after.first().cloned() {
                        after.remove(0);
                        let mut next_args = vec![val];
                        next_args.extend(next_caps);
                        step = run_fn(&mut t, module, next_fn, next_args);
                        // loop continues
                    } else {
                        // fz-4mk — shutdown drain: walk the MSO chain to
                        // enqueue every still-live resource's dtor, then
                        // dispatch each as a real fz call while the process
                        // is still alive (CURRENT_PROCESS is `proc_ptr`,
                        // heap is intact, scheduler can drive callbacks
                        // into externs the dtor body invokes).
                        unsafe {
                            fz_runtime::procbin::mso_drop_all_deferred(&mut (*proc_ptr).heap);
                        }
                        if let Err(e) = drain_pending_dtors_interp(&mut t, module) {
                            eprintln!("fz-4mk: dtor drain failed: {}", e);
                        }
                        fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                        INTERP_TASKS.with(|t| {
                            if let Some(p) = t.borrow_mut().get_mut(&pid) {
                                p.state = ProcessState::Exited;
                            }
                        });
                        if pid == 1 {
                            halt_val = value_to_halt(val);
                        }
                        continue 'sched;
                    }
                }
                Ok(InterpStep::Blocked(resume_fn, cap_vals, mut new_after)) => {
                    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                    new_after.extend(after);
                    INTERP_TASKS.with(|t| {
                        if let Some(p) = t.borrow_mut().get_mut(&pid) {
                            p.state = ProcessState::Blocked;
                        }
                    });
                    INTERP_RESUME
                        .with(|r| r.borrow_mut().insert(pid, (resume_fn, cap_vals, new_after)));
                    continue 'sched;
                }
                // fz-yxs/fz-2v3 — park record + after-chain stashed under
                // INTERP_PARKED so the next interp_send can probe the
                // matcher against the arriving message without unwinding.
                Ok(InterpStep::BlockedMatched(park, mut new_after)) => {
                    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                    new_after.extend(after);
                    INTERP_TASKS.with(|t| {
                        if let Some(p) = t.borrow_mut().get_mut(&pid) {
                            p.state = ProcessState::Blocked;
                        }
                    });
                    INTERP_PARKED.with(|p| {
                        p.borrow_mut().insert(pid, (park, new_after));
                    });
                    continue 'sched;
                }
                Err(e) => {
                    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = None);
                    return Err(e);
                }
            }
        }
    }

    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = None);
    Ok(halt_val)
}

/// Run a single test fn (no args) through the interp on a fresh Process.
/// Used by `fz test` (src/test_runner.rs). Each test gets its own heap +
/// mailbox so state can't leak between tests in the same module.
///
/// Returns Ok(()) if the test completes without an assertion failure;
/// returns Err(msg) on any interp/runtime/assertion error.
pub fn run_test_fn(module: &Module, fn_id: FnId) -> Result<(), String> {
    interp_reset_state();
    let user_schemas = std::rc::Rc::new(std::cell::RefCell::new(
        fz_runtime::heap::SchemaRegistry::new(),
    ));
    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = Some(user_schemas.clone()));
    let mut task = Box::new(Process::new(user_schemas));
    task.pid = 1;
    task.atom_names = module.atom_names.clone();
    let task_ptr = interp_register_task(1, task);
    let prev = fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(task_ptr));
    let mut t = crate::types_seam::ConcreteTypes;
    let result = run_fn(&mut t, module, fn_id, Vec::new());
    // fz-4mk — shutdown drain mirrors run_main's exit path: enqueue every
    // surviving resource's dtor and dispatch each as a real fz call while
    // CURRENT_PROCESS is still pointing at the test task's heap.
    unsafe {
        fz_runtime::procbin::mso_drop_all_deferred(&mut (*task_ptr).heap);
    }
    if let Err(e) = drain_pending_dtors_interp(&mut t, module) {
        eprintln!("fz-4mk: dtor drain failed in test fn: {}", e);
    }
    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = None);
    match result {
        Ok(InterpStep::Done(_)) => Ok(()),
        Ok(InterpStep::Blocked(..)) | Ok(InterpStep::BlockedMatched(..)) => {
            Err("test fn blocked on receive with empty mailbox".to_string())
        }
        Err(e) => Err(e),
    }
}

/// Spawn a new task: enqueue it and return its pid immediately.
/// The child runs in a later scheduler quantum, not in the parent's.
fn interp_spawn(module: &Module, fn_id: FnId, args: Vec<FzValue>) -> Result<u32, String> {
    use fz_runtime::process::ProcessState;
    let pid = interp_next_pid();
    let user_schemas = INTERP_SCHEMAS
        .with(|s| s.borrow().as_ref().cloned())
        .ok_or("interp_spawn: no INTERP_SCHEMAS installed (call run_main first)")?;
    let mut child = Box::new(Process::new(user_schemas));
    child.pid = pid;
    child.atom_names = module.atom_names.clone();
    child.state = ProcessState::Ready;
    interp_register_task(pid, child);
    INTERP_RESUME.with(|r| r.borrow_mut().insert(pid, (fn_id, args, vec![])));
    INTERP_RUN_QUEUE.with(|q| q.borrow_mut().push_back(pid));
    Ok(pid)
}

fn value_to_halt(v: FzValue) -> i64 {
    use fz_runtime::fz_value::Tag;
    match v.tag() {
        Tag::Int => v.unbox_int().unwrap(),
        // fz-yan.1 — see ir_runtime::fz_halt for the same shape.
        // nil/true/false flow through this atom arm now.
        Tag::Atom => v.unbox_atom().unwrap() as i64,
        Tag::Ptr | Tag::Reserved => v.0 as i64,
    }
}

/// Run an fz fn. Tail calls reuse this stack frame (O(1) Rust stack).
/// Returns Done(val) on Halt/Return or Blocked(fn_id, cap_vals) when a
/// Term::Receive fires on an empty mailbox.
fn run_fn<T: Types<Ty = crate::types_seam::Ty>>(
    t: &mut T,
    module: &Module,
    mut fn_id: FnId,
    mut args: Vec<FzValue>,
) -> Result<InterpStep, String> {
    'tail: loop {
        let fn_ir = module.fn_by_id(fn_id);
        let mut env: HashMap<Var, FzValue> = HashMap::new();
        let entry = fn_ir.block(fn_ir.entry);
        if entry.params.len() != args.len() {
            return Err(format!(
                "fn {} expected {} args, got {}",
                fn_ir.name,
                entry.params.len(),
                args.len()
            ));
        }
        for (p, v) in entry.params.iter().zip(args.iter()) {
            env.insert(*p, *v);
        }
        let mut cur = fn_ir.entry;
        loop {
            let blk = fn_ir.block(cur);
            for Stmt::Let(v, prim) in &blk.stmts {
                let val = eval_prim(t, module, prim, &env)?;
                env.insert(*v, val);
            }
            match &blk.terminator {
                Term::Goto(b, gargs) => {
                    let vals: Vec<FzValue> = gargs
                        .iter()
                        .map(|v| env_get(&env, *v))
                        .collect::<Result<_, _>>()?;
                    let next = fn_ir.block(*b);
                    for (p, val) in next.params.iter().zip(vals) {
                        env.insert(*p, val);
                    }
                    cur = *b;
                }
                Term::If {
                    cond,
                    then_b,
                    else_b,
                    ..
                } => {
                    let cv = env_get(&env, *cond)?;
                    cur = if is_truthy(cv) { *then_b } else { *else_b };
                }
                Term::Call {
                    ident: _,
                    callee,
                    args: call_args,
                    continuation,
                } => {
                    let arg_vals = collect(&env, call_args)?;
                    let outer_cap_vals = collect(&env, &continuation.captured)?;
                    match run_fn(t, module, *callee, arg_vals)? {
                        InterpStep::Done(val) => {
                            let mut cont_args = vec![val];
                            cont_args.extend(outer_cap_vals);
                            fn_id = continuation.fn_id;
                            args = cont_args;
                            continue 'tail;
                        }
                        InterpStep::Blocked(rf, cv, mut inner_after) => {
                            // Append our continuation to the chain so the
                            // scheduler calls it after the blocked task resumes.
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::Blocked(rf, cv, inner_after));
                        }
                        InterpStep::BlockedMatched(park, mut inner_after) => {
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::BlockedMatched(park, inner_after));
                        }
                    }
                }
                Term::TailCall {
                    ident: _,
                    callee,
                    args: call_args,
                    is_back_edge,
                } => {
                    let mut arg_vals = collect(&env, call_args)?;
                    // fz-02r.6 — interpreter back-edge cooperative GC.
                    // Check FZ_SHOULD_YIELD at annotated back-edges; if set,
                    // forward live args through gc_mid_flight and clear the
                    // flag. The interpreter runs synchronously so no yield or
                    // re-enqueue is needed — just GC in place and continue.
                    if *is_back_edge {
                        use std::sync::atomic::Ordering;
                        if fz_runtime::yield_flag::FZ_SHOULD_YIELD.load(Ordering::Relaxed) != 0 {
                            let p = fz_runtime::process::current_process();
                            p.heap.gc_mid_flight(&mut arg_vals, &mut p.mailbox);
                            p.quiet_quanta = 0;
                            fz_runtime::yield_flag::FZ_SHOULD_YIELD.store(0, Ordering::Relaxed);
                        } else {
                            let p = fz_runtime::process::current_process();
                            p.quiet_quanta = p.quiet_quanta.saturating_add(1);
                        }
                    }
                    fn_id = *callee;
                    args = arg_vals;
                    continue 'tail;
                }
                Term::CallClosure {
                    ident: _,
                    closure,
                    args: call_args,
                    continuation,
                } => {
                    let cl = env_get(&env, *closure)?;
                    let (lam_fn, mut clos_args) = unpack_closure(cl)?;
                    clos_args.extend(collect(&env, call_args)?);
                    let outer_cap_vals = collect(&env, &continuation.captured)?;
                    match run_fn(t, module, lam_fn, clos_args)? {
                        InterpStep::Done(val) => {
                            let mut cont_args = vec![val];
                            cont_args.extend(outer_cap_vals);
                            fn_id = continuation.fn_id;
                            args = cont_args;
                            continue 'tail;
                        }
                        InterpStep::Blocked(rf, cv, mut inner_after) => {
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::Blocked(rf, cv, inner_after));
                        }
                        InterpStep::BlockedMatched(park, mut inner_after) => {
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::BlockedMatched(park, inner_after));
                        }
                    }
                }
                Term::TailCallClosure {
                    ident: _,
                    closure,
                    args: call_args,
                } => {
                    let cl = env_get(&env, *closure)?;
                    let (lam_fn, mut clos_args) = unpack_closure(cl)?;
                    clos_args.extend(collect(&env, call_args)?);
                    fn_id = lam_fn;
                    args = clos_args;
                    continue 'tail;
                }
                Term::Return(v) => return Ok(InterpStep::Done(env_get(&env, *v)?)),
                Term::Halt(v) => return Ok(InterpStep::Done(env_get(&env, *v)?)),
                Term::Receive {
                    continuation,
                    ident: _,
                } => {
                    let cap_vals = collect(&env, &continuation.captured)?;
                    match fz_runtime::process::current_process().mailbox.pop_front() {
                        Some(msg) => {
                            let mut cont_args = vec![msg];
                            cont_args.extend(cap_vals);
                            fn_id = continuation.fn_id;
                            args = cont_args;
                            continue 'tail;
                        }
                        None => {
                            return Ok(InterpStep::Blocked(continuation.fn_id, cap_vals, vec![]));
                        }
                    }
                }
                // fz-yxs/fz-2v3 — selective receive. Walk the mailbox
                // head-to-tail trying each clause in order; first match
                // wins. On miss, return BlockedMatched so the scheduler
                // can stash a park record for `interp_send`'s sender-side
                // probe to consult on the next arrival.
                Term::ReceiveMatched {
                    clauses,
                    after,
                    pinned,
                    captures,
                    ..
                } => {
                    let pinned_map: HashMap<String, FzValue> = pinned
                        .iter()
                        .map(|(name, var)| env_get(&env, *var).map(|v| (name.clone(), v)))
                        .collect::<Result<_, _>>()?;
                    let capture_vals: Vec<FzValue> = collect(&env, captures)?;

                    let matched_clauses: Vec<MatchedClause> = clauses
                        .iter()
                        .map(|c| MatchedClause {
                            pattern: c.pattern.node.clone(),
                            bound_names: c.bound_names.clone(),
                            guard: c.guard,
                            body: c.body,
                        })
                        .collect();

                    // Initial mailbox scan.
                    let mailbox_len = fz_runtime::process::current_process().mailbox.len();
                    let mut hit: Option<(usize, usize, Vec<FzValue>)> = None;
                    for mb_idx in 0..mailbox_len {
                        let msg = fz_runtime::process::current_process().mailbox[mb_idx];
                        if let Some((clause_idx, binds)) = try_match_clauses(
                            t,
                            module,
                            &matched_clauses,
                            msg,
                            &pinned_map,
                            &capture_vals,
                        )? {
                            hit = Some((mb_idx, clause_idx, binds));
                            break;
                        }
                    }

                    if let Some((mb_idx, clause_idx, bound_vals)) = hit {
                        fz_runtime::process::current_process()
                            .mailbox
                            .remove(mb_idx);
                        let body = matched_clauses[clause_idx].body;
                        let mut new_args = bound_vals;
                        new_args.extend(capture_vals);
                        fn_id = body;
                        args = new_args;
                        continue 'tail;
                    }

                    // Miss — `after 0` (timeout literal 0) fires the after
                    // body inline; any other after value (including
                    // `:infinity`) parks without a timer since the interp
                    // has no wall clock.
                    if let Some(a) = after {
                        let timeout_val = env_get(&env, a.timeout)?;
                        if timeout_val.tag() == fz_runtime::fz_value::Tag::Int
                            && timeout_val.unbox_int() == Some(0)
                        {
                            fn_id = a.body;
                            args = capture_vals;
                            continue 'tail;
                        }
                    }

                    let park = ParkRecord {
                        clauses: matched_clauses,
                        pinned: pinned_map,
                        captures: capture_vals,
                    };
                    return Ok(InterpStep::BlockedMatched(park, vec![]));
                }
            }
        }
    }
}

fn collect(env: &HashMap<Var, FzValue>, vars: &[Var]) -> Result<Vec<FzValue>, String> {
    vars.iter().map(|v| env_get(env, *v)).collect()
}

fn env_get(env: &HashMap<Var, FzValue>, v: Var) -> Result<FzValue, String> {
    env.get(&v)
        .copied()
        .ok_or_else(|| format!("unbound Var({})", v.0))
}

fn is_truthy(v: FzValue) -> bool {
    !(v.is_false() || v.is_nil())
}

fn eval_prim<T: Types<Ty = crate::types_seam::Ty>>(
    t: &mut T,
    module: &Module,
    prim: &Prim,
    env: &HashMap<Var, FzValue>,
) -> Result<FzValue, String> {
    Ok(match prim {
        Prim::Const(c) => const_to_fz(c),
        Prim::BinOp(op, a, b) => {
            let av = env_get(env, *a)?;
            let bv = env_get(env, *b)?;
            eval_binop(*op, av, bv)?
        }
        Prim::Extern(eid, args) => {
            let arg_vals = collect(env, args)?;
            call_extern(t, module, *eid, &arg_vals)?
        }
        Prim::MakeBitstring(fields) => {
            // fz-cty.7 — mirror src/ir_codegen.rs Prim::MakeBitstring: drive the
            // same runtime BitWriter through the same extern "C" calls the JIT
            // and AOT paths use, so all three paths funnel through the shared
            // bitstring substrate.
            use crate::ast::BitType as AstBitType;
            use crate::fz_ir::BitSizeIr;
            fn encode_bit_type(t: AstBitType) -> u32 {
                match t {
                    AstBitType::Integer => 0,
                    AstBitType::Float => 1,
                    AstBitType::Binary => 2,
                    AstBitType::Bits => 3,
                    AstBitType::Utf8 => 4,
                    AstBitType::Utf16 => 5,
                    AstBitType::Utf32 => 6,
                }
            }
            fn encode_endian(e: crate::ast::Endian) -> u32 {
                use crate::ast::Endian;
                match e {
                    Endian::Big => 0,
                    Endian::Little => 1,
                    Endian::Native => 2,
                }
            }
            fn default_unit_for(ty: AstBitType) -> u32 {
                match ty {
                    AstBitType::Integer | AstBitType::Float | AstBitType::Bits => 1,
                    AstBitType::Binary => 8,
                    AstBitType::Utf8 | AstBitType::Utf16 | AstBitType::Utf32 => 1,
                }
            }
            fz_runtime::ir_runtime::fz_bs_begin();
            for f in fields {
                let value_v = env_get(env, f.value)?;
                let ty_tag = encode_bit_type(f.ty);
                let unit = f.unit.unwrap_or(default_unit_for(f.ty));
                let endian_tag = encode_endian(f.endian);
                let signed = f.signed as u32;
                let (size_present, size_value) = match &f.size {
                    None => (0u32, 0u32),
                    Some(BitSizeIr::Literal(n)) => (1, *n),
                    Some(BitSizeIr::Var(v)) => {
                        let raw = env_get(env, *v)?;
                        let n = raw
                            .unbox_int()
                            .ok_or_else(|| "bit size var must be an integer".to_string())?;
                        (1, n as u32)
                    }
                };
                fz_runtime::ir_runtime::fz_bs_write_field(
                    value_v.0,
                    ty_tag,
                    size_present,
                    size_value,
                    unit,
                    endian_tag,
                    signed,
                );
            }
            FzValue(fz_runtime::ir_runtime::fz_bs_finalize())
        }
        Prim::ConstBitstring(bytes, bit_len) => {
            // fz-cty.8 — bytes are owned by the Module (and live as long as
            // the interp run), so it's safe to alloc straight from them via
            // the shared runtime FFI; identical to the JIT/AOT lowering.
            FzValue(fz_runtime::ir_runtime::fz_alloc_bitstring_const(
                bytes.as_ptr() as u64,
                bytes.len() as u64,
                *bit_len,
            ))
        }
        Prim::MakeClosure(_, fn_id, captured) => {
            // fz-ul4.29.5: new closure layout — header (16) + stub_fp (8) +
            // captures. The interp has no compiled stub for the closure;
            // it dispatches via the body fn id stored in header._reserved
            // (callee_fn_id). stub_fp is left null and never read by the
            // interp's CallClosure / TailCallClosure / spawn paths.
            let cap_vals: Vec<FzValue> = collect(env, captured)?;
            let p = fz_runtime::process::current_process().heap.alloc_closure(
                fn_id.0,
                cap_vals.len(),
                0,
            );
            unsafe {
                std::ptr::write((p as *mut u8).add(16) as *mut u64, 0); // stub_fp = null
                let cursor = (p as *mut u8).add(24) as *mut FzValue;
                for (i, cv) in cap_vals.iter().enumerate() {
                    std::ptr::write(cursor.add(i), *cv);
                }
            }
            FzValue(p as u64)
        }
        Prim::MakeTuple(elems) => {
            // fz-ul4.35 — mirror src/ir_codegen.rs MakeTuple: alloc a heap
            // Struct with `arity` FzValue slots and write each captured
            // value at offset 16 + i*8 (after the 16-byte HeapHeader).
            // Schemas are registered lazily on first use of each arity; the
            // map is per-run (run_main / run_test_fn clear it), so schema
            // ids are stable across spawned tasks that share the registry.
            let arity = elems.len();
            let schema_id = interp_tuple_schema_id(arity);
            let p = fz_runtime::process::current_process()
                .heap
                .alloc_struct(schema_id);
            for (i, v) in elems.iter().enumerate() {
                let val = env_get(env, *v)?;
                unsafe {
                    let dst = (p as *mut u8).add(16 + i * 8) as *mut FzValue;
                    std::ptr::write(dst, val);
                }
            }
            FzValue(p as u64)
        }
        Prim::TupleField(c, idx) => {
            let cv = env_get(env, *c)?;
            let p = cv
                .unbox_ptr()
                .ok_or_else(|| "TupleField: subject is not a heap pointer".to_string())?;
            let off = 16 + (*idx as usize) * 8;
            unsafe {
                let src = (p as *const u8).add(off) as *const FzValue;
                std::ptr::read(src)
            }
        }
        Prim::TypeTest(v, descr) => {
            use crate::types::BasicBits;
            use fz_runtime::fz_value::{HeapKind, Tag};
            let descr = descr.as_ref().descr();
            let val = env_get(env, *v)?;
            let tag = val.tag();
            // Hoist heap inspection — many Component arms need (header, kind).
            let heap = val.unbox_ptr().map(|ptr| {
                let header = unsafe { &*ptr };
                (header, HeapKind::from_u16(header.kind))
            });
            let mut matched = false;
            if descr.type_test_has_ints() {
                matched |= tag == Tag::Int;
            }
            match descr.type_test_atoms() {
                AtomTypeTest::None => {}
                AtomTypeTest::Any => {
                    matched |= tag == Tag::Atom;
                }
                AtomTypeTest::Cofinite => {
                    return Err(
                        "TypeTest: cofinite atom literal sets not yet supported in interpreter"
                            .into(),
                    );
                }
                AtomTypeTest::Finite(names) => {
                    // fz-yan.2 — atoms axis subsumes BasicBits::NIL / ::BOOL.
                    if tag == Tag::Atom {
                        let id = val.unbox_atom().expect("atom-tagged");
                        for name in &names {
                            if let Some(pos) = module.atom_names.iter().position(|n| n == name)
                                && pos as u32 == id
                            {
                                matched = true;
                                break;
                            }
                        }
                    }
                }
            }
            if descr.type_test_has_floats() {
                if let Some((_, Some(HeapKind::Float))) = heap {
                    matched = true;
                }
            }
            let basic = descr.type_test_basic_bits();
            if let Some((_, Some(hk))) = heap {
                if basic.contains_all(BasicBits::VEC_I64) && hk == HeapKind::VecI64 {
                    matched = true;
                }
                if basic.contains_all(BasicBits::VEC_F64) && hk == HeapKind::VecF64 {
                    matched = true;
                }
                if basic.contains_all(BasicBits::VEC_U8) && hk == HeapKind::VecU8 {
                    matched = true;
                }
                if basic.contains_all(BasicBits::VEC_BIT) && hk == HeapKind::VecBit {
                    matched = true;
                }
            }
            // fz-ul4.36 — match if value is HeapKind::Struct with matching
            // schema_id. Negated tuple clauses unsupported.
            assert!(
                !descr.type_test_tuple_has_negations(),
                "TypeTest: negated tuple clauses not yet supported"
            );
            if let Some((header, Some(HeapKind::Struct))) = heap {
                let actual_schema = header.schema_id;
                for arity in descr.type_test_tuple_arities() {
                    let want_schema = interp_tuple_schema_id(arity);
                    if actual_schema == want_schema {
                        matched = true;
                        break;
                    }
                }
            }
            if matched {
                FzValue::TRUE
            } else {
                FzValue::FALSE
            }
        }
        // fz-fyq.5 — list primitives. Same runtime helpers and memory
        // layout as ir_codegen's JIT/AOT paths use (cons cells: header
        // at 0..16, head at 16, tail at 24); the empty list is the
        // single bit pattern `FzValue::EMPTY_LIST`. Until this lands,
        // every interp run of a program containing a list literal
        // exited 75 "Deferred" and the fixture matrix silently skipped
        // it.
        Prim::ListCons(h, t) => {
            let hv = env_get(env, *h)?;
            let tv = env_get(env, *t)?;
            FzValue(fz_runtime::ir_runtime::fz_alloc_list_cons(hv.0, tv.0))
        }
        Prim::ListHead(c) => {
            let cv = env_get(env, *c)?;
            let p = cv
                .unbox_ptr()
                .ok_or_else(|| "ListHead: subject is not a heap pointer".to_string())?;
            FzValue(unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) })
        }
        Prim::ListTail(c) => {
            let cv = env_get(env, *c)?;
            let p = cv
                .unbox_ptr()
                .ok_or_else(|| "ListTail: subject is not a heap pointer".to_string())?;
            FzValue(unsafe { std::ptr::read((p as *const u8).add(24) as *const u64) })
        }
        Prim::IsEmptyList(c) => {
            let cv = env_get(env, *c)?;
            if cv.is_empty_list() {
                FzValue::TRUE
            } else {
                FzValue::FALSE
            }
        }
        Prim::MapGet(m, k) => {
            // fz-swt.8 — route through the same runtime helper the JIT
            // and AOT use. That helper recognises `HeapKind::Resource`
            // stubs and returns the payload (the `.value` accessor on
            // resource handles); generic map subjects fall through to
            // the regular linear-scan path.
            let mv = env_get(env, *m)?;
            let kv = env_get(env, *k)?;
            FzValue(fz_runtime::ir_runtime::fz_map_get(mv.0, kv.0))
        }
        Prim::MakeList(elems, tail) => {
            // Mirror ir_codegen: fold cons from right, starting with
            // `tail` (defaulted to the empty list).
            let mut acc = match tail {
                Some(t) => env_get(env, *t)?,
                None => FzValue::EMPTY_LIST,
            };
            for e in elems.iter().rev() {
                let ev = env_get(env, *e)?;
                acc = FzValue(fz_runtime::ir_runtime::fz_alloc_list_cons(ev.0, acc.0));
            }
            acc
        }
        // fz-axu.23 (M2) — lower_program_full erases Prim::Brand
        // before the interp sees the module. Surface a stray Brand
        // instead of silently aliasing.
        Prim::Brand(_, _) => unreachable!(
            "Prim::Brand reached interp — erasure should run inside lower_program_full"
        ),
        _ => {
            return Err(format!(
                "interp .5.2: prim {:?} not yet supported (lands in fz-ul4.23.5.3+)",
                std::mem::discriminant(prim)
            ));
        }
    })
}

/// Read an interp-side closure value. fz-ul4.29.5 layout:
///   header (16) + stub_fp (8) + captured: [FzValue; n] (offset 24+)
///   header._reserved = callee FnId; header.flags = captured count.
/// fz-4mk — interpreter-leg drain of `Heap::pending_dtors`. Pops each
/// `(closure_bits, payload)` enqueued by `mso_sweep`/`mso_drop_all`,
/// unpacks the closure to its body FnId + captures, and runs the body
/// as a fully fz-side call via `run_fn`. The dtor's return value is
/// discarded. Errors from the dtor body propagate to the caller; the
/// run-loop logs and continues.
///
/// Pre-conditions: `CURRENT_PROCESS` is set to the heap owning the
/// queue. Closures in the queue point into that heap.
fn drain_pending_dtors_interp<T: Types<Ty = crate::types_seam::Ty>>(
    t: &mut T,
    module: &Module,
) -> Result<(), String> {
    loop {
        let entry = {
            let p = fz_runtime::process::current_process();
            p.heap.pending_dtors.pop_front()
        };
        let Some((closure_bits, payload)) = entry else {
            break;
        };
        let closure = FzValue(closure_bits);
        let (fn_id, captured) = match unpack_closure(closure) {
            Ok(x) => x,
            Err(e) => {
                eprintln!("fz-4mk drain: bad dtor closure (skipping): {}", e);
                continue;
            }
        };
        let mut args = captured;
        args.push(FzValue(payload));
        match run_fn(t, module, fn_id, args)? {
            InterpStep::Done(_) => {}
            InterpStep::Blocked(_, _, _) | InterpStep::BlockedMatched(_, _) => {
                return Err("fz-4mk drain: dtor blocked on receive (unsupported in v1)".into());
            }
        }
    }
    Ok(())
}

fn unpack_closure(v: FzValue) -> Result<(FnId, Vec<FzValue>), String> {
    use fz_runtime::fz_value::HeapKind;
    let p = v.unbox_ptr().ok_or_else(|| {
        format!(
            "call_closure on non-ptr value: {}",
            fz_runtime::fz_value::debug::render(v.0)
        )
    })?;
    let header = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Closure) {
        return Err("call_closure on non-closure heap value".into());
    }
    let fn_id = FnId(header._reserved);
    let cap_count = header.flags as usize;
    let payload = unsafe { (p as *const u8).add(24) as *const u64 };
    let captured: Vec<FzValue> = (0..cap_count)
        .map(|i| FzValue(unsafe { std::ptr::read(payload.add(i)) }))
        .collect();
    Ok((fn_id, captured))
}

fn const_to_fz(c: &Const) -> FzValue {
    match c {
        Const::Int(n) => FzValue::from_int(*n),
        Const::Atom(id) => FzValue::from_atom_id(*id),
        Const::Nil => FzValue::NIL,
        Const::True => FzValue::TRUE,
        Const::False => FzValue::FALSE,
        Const::Float(f) => FzValue(fz_runtime::ir_runtime::fz_alloc_float(f.to_bits())),
    }
}

fn eval_binop(op: BinOp, a: FzValue, b: FzValue) -> Result<FzValue, String> {
    // Arithmetic: both-Int fast path matches the JIT's inline lowering;
    // mixed or boxed-float operands promote both to f64 and box. fz-ul4.27.9
    // dropped the per-op fz_arith_* helpers; promotion goes through the
    // shared fz_promote_f64 conversion, same as the JIT slow path.
    use fz_runtime::ir_runtime::{box_float, cmp_to_fz, fz_promote_f64};
    macro_rules! int_arith {
        ($op:tt) => {
            match (a.unbox_int(), b.unbox_int()) {
                (Some(x), Some(y)) => Ok(FzValue::from_int(x $op y)),
                _ => Ok(FzValue(box_float(fz_promote_f64(a.0) $op fz_promote_f64(b.0)))),
            }
        };
    }
    macro_rules! float_cmp {
        ($op:tt) => { Ok(FzValue(cmp_to_fz(fz_promote_f64(a.0) $op fz_promote_f64(b.0)))) };
    }
    match op {
        BinOp::Add => int_arith!(+),
        BinOp::Sub => int_arith!(-),
        BinOp::Mul => int_arith!(*),
        BinOp::Div => int_arith!(/),
        BinOp::Mod => int_arith!(%),
        BinOp::Eq => Ok(FzValue(fz_runtime::ir_runtime::fz_value_eq(a.0, b.0))),
        BinOp::Neq => {
            let eq = FzValue(fz_runtime::ir_runtime::fz_value_eq(a.0, b.0));
            Ok(if eq.is_true() {
                FzValue::FALSE
            } else {
                FzValue::TRUE
            })
        }
        BinOp::Lt => float_cmp!(<),
        BinOp::Le => float_cmp!(<=),
        BinOp::Gt => float_cmp!(>),
        BinOp::Ge => float_cmp!(>=),
        BinOp::And => Ok(if !is_truthy(a) { a } else { b }),
        BinOp::Or => Ok(if is_truthy(a) { a } else { b }),
    }
}

/// fz-4mk — shared work behind both the interp `fz_make_resource` BIF and
/// the JIT/AOT `MakeResourceHook` thunk: validate the dtor closure, then
/// allocate the off-heap `Resource` + on-heap stub on the current process
/// heap. The dtor body fires as real fz code at scheduler-boundary drain
/// via `fz_drain_dtor_entry` (JIT/AOT) or `run_fn` (interp); the
/// Resource's C-side dtor slot is the no-op so refcount→0 paths that
/// bypass the drain don't double-fire.
pub(crate) fn make_resource_in_current_process(
    _module: &Module,
    payload: u64,
    dtor_closure: FzValue,
) -> Result<FzValue, String> {
    use fz_runtime::fz_value::HeapKind;
    let p = dtor_closure
        .unbox_ptr()
        .ok_or_else(|| "make_resource: dtor arg is not a heap value".to_string())?;
    let header = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Closure) {
        return Err("make_resource: dtor arg is not a closure".into());
    }
    let handle = fz_runtime::resource::ResourceHandle::new(
        payload,
        fz_runtime::resource::fz_resource_destructor_noop,
    );
    let heap = &mut fz_runtime::process::current_process().heap;
    let stub = fz_runtime::resource::alloc_resource(heap, handle, dtor_closure);
    Ok(FzValue::from_ptr(stub.as_raw()))
}

fn call_extern<T: Types<Ty = crate::types_seam::Ty>>(
    t: &mut T,
    module: &Module,
    eid: ExternId,
    args: &[FzValue],
) -> Result<FzValue, String> {
    let decl = module.extern_by_id(eid);
    // Assert fns use std::process::abort on failure — fatal for the JIT/AOT
    // path, but unusable in the interpreter where failures must return Err.
    // Handle them inline with the same logic as run_builtin::Assert*.
    match decl.symbol.as_str() {
        "fz_assert" => {
            if args.len() != 1 {
                return Err(format!("fz_assert/1 got {} args", args.len()));
            }
            return if is_truthy(args[0]) {
                Ok(FzValue::NIL)
            } else {
                Err("assertion failed".into())
            };
        }
        "fz_assert_eq" => {
            if args.len() != 2 {
                return Err(format!("fz_assert_eq/2 got {} args", args.len()));
            }
            let eq = FzValue(fz_runtime::ir_runtime::fz_value_eq(args[0].0, args[1].0));
            return if eq.is_true() {
                Ok(FzValue::NIL)
            } else {
                Err(format!(
                    "assertion failed: assert_eq({}, {})",
                    fz_runtime::fz_value::debug::render(args[0].0),
                    fz_runtime::fz_value::debug::render(args[1].0),
                ))
            };
        }
        "fz_assert_neq" => {
            if args.len() != 2 {
                return Err(format!("fz_assert_neq/2 got {} args", args.len()));
            }
            let eq = FzValue(fz_runtime::ir_runtime::fz_value_eq(args[0].0, args[1].0));
            return if eq.is_false() {
                Ok(FzValue::NIL)
            } else {
                Err(format!(
                    "assertion failed: assert_neq({}, {})",
                    fz_runtime::fz_value::debug::render(args[0].0),
                    fz_runtime::fz_value::debug::render(args[1].0),
                ))
            };
        }
        // Spawn/send/self need the interpreter's own scheduler — the C
        // implementations require a Runtime spawn hook which is only
        // installed on the JIT/AOT path.
        "fz_spawn" | "fz_spawn_opt" => {
            if args.is_empty() {
                return Err(format!("{}/1+ got 0 args", &decl.symbol));
            }
            // args[0] is the thunk closure (wrapping the user's closure);
            // args[1] (fz_spawn_opt) is a min_heap_size hint — ignored here.
            let (fn_id, captured) = unpack_closure(args[0])?;
            let pid = interp_spawn(module, fn_id, captured)?;
            return Ok(FzValue::from_int(pid as i64));
        }
        "fz_self" => {
            return Ok(FzValue::from_int(
                fz_runtime::process::current_process().pid as i64,
            ));
        }
        "fz_make_ref" => {
            // fz-ht5 — route through the runtime FFI so interp and JIT
            // share the same counter; otherwise an interp run followed
            // by a JIT run in the same process could collide.
            let bits = fz_runtime::ir_runtime::fz_make_ref();
            return Ok(FzValue(bits));
        }
        "fz_send" => {
            if args.len() != 2 {
                return Err(format!("fz_send/2 got {} args", args.len()));
            }
            let receiver = args[0]
                .unbox_int()
                .ok_or_else(|| "send/2: pid must be Int".to_string())?
                as u32;
            interp_send(t, module, receiver, args[1])?;
            return Ok(args[1]);
        }
        "fz_make_resource" => {
            // fz-swt.7 / fz-swt.10 — interp BIF: routes through the same
            // shared helper used by the runtime's `MakeResourceHook` for
            // the JIT/AOT legs, so dtor-resolution semantics are uniform
            // across paths.
            if args.len() != 2 {
                return Err(format!("fz_make_resource/2 got {} args", args.len()));
            }
            return make_resource_in_current_process(module, args[0].0, args[1]);
        }
        _ => {}
    }
    let fp = resolve_symbol(&decl.symbol)?;
    let raw_args: Vec<u64> = args
        .iter()
        .zip(decl.params.iter())
        .map(|(v, ty)| match ty {
            ExternTy::I64 => v.unbox_int().unwrap_or(0) as u64,
            // fz-8up — Binary/CString call into the runtime helpers from
            // [[fz-9ss]] and pass the returned pointer as the C arg.
            ExternTy::Binary => {
                (unsafe { fz_runtime::extern_binary::fz_binary_as_ptr(v.0) }) as u64
            }
            ExternTy::CString => {
                (unsafe { fz_runtime::extern_binary::fz_binary_as_cstring(v.0) }) as u64
            }
            _ => v.0,
        })
        .collect();
    let returns_value = !matches!(decl.ret, ExternTy::Unit | ExternTy::Never);
    let ret = if returns_value {
        unsafe { dispatch_fn_returning(fp, &raw_args) }
    } else {
        unsafe { dispatch_fn_void(fp, &raw_args) };
        0
    };
    // fz-rb8 — `:: integer` returns a raw signed 64-bit value from C;
    // auto-box to FzValue::Int. Other return classes treat the bits as
    // an already-tagged FzValue.
    let boxed = match decl.ret {
        ExternTy::I64 => FzValue::from_int(ret as i64).0,
        _ => ret,
    };
    Ok(FzValue(boxed))
}

/// Return the function pointer for a named C symbol.
///
/// Checks the built-in native table first (all symbols declared in runtime.fz
/// are registered here so that the interpreter finds them even when the runtime
/// is statically linked and dlsym(RTLD_DEFAULT) cannot reach the symbols).
/// Falls back to dlsym for any name not in the table.
fn resolve_symbol(name: &str) -> Result<*const (), String> {
    // Native table: every symbol declared in runtime.fz. These Rust functions
    // are linked into the binary; using their address directly avoids relying
    // on dlsym visibility, which is unreliable for statically-linked rlibs.
    #[cfg(test)]
    if let Some(fp) = tests_support::lookup_test_symbol(name) {
        return Ok(fp);
    }
    let native: Option<*const ()> = match name {
        "fz_print_i64" => Some(fz_runtime::fz_print_i64 as *const ()),
        "fz_print_value" => Some(fz_runtime::ir_runtime::fz_print_value as *const ()),
        "fz_assert" => Some(fz_runtime::fz_assert as *const ()),
        "fz_assert_eq" => Some(fz_runtime::fz_assert_eq as *const ()),
        "fz_assert_neq" => Some(fz_runtime::fz_assert_neq as *const ()),
        "fz_vec_get" => Some(fz_runtime::ir_runtime::fz_vec_get as *const ()),
        "fz_spawn" => Some(fz_runtime::ir_runtime::fz_spawn as *const ()),
        "fz_spawn_opt" => Some(fz_runtime::ir_runtime::fz_spawn_opt as *const ()),
        "fz_self" => Some(fz_runtime::ir_runtime::fz_self as *const ()),
        "fz_make_ref" => Some(fz_runtime::ir_runtime::fz_make_ref as *const ()),
        "fz_send" => Some(fz_runtime::ir_runtime::fz_send as *const ()),
        // fz-swt.11 — fixture/test dtor exported from the runtime crate.
        // Bound here so interp-leg invocations of fixtures using this
        // symbol (e.g. when `fz interp` is run by hand on the AOT-only
        // fixture) reach the same Rust fn the AOT-linked binary uses.
        "fz_resource_test_print_dtor" => {
            Some(fz_runtime::resource::fz_resource_test_print_dtor as *const ())
        }
        // fz-swt.13 — tmpfile helper for file fixtures. Same rationale as
        // the print-dtor binding above: keep the interp leg of the fixture
        // matrix self-contained, no dlsym dependence.
        "fz_test_open_tmpfile" => Some(fz_runtime::resource::fz_test_open_tmpfile as *const ()),
        // fz-axu.14 (R1) — utf8 runtime support. Bound here so the
        // interp leg of the matrix can resolve them without relying on
        // dlsym; statically-linked rlibs don't expose these via
        // RTLD_DEFAULT on Linux.
        "fz_bitstring_valid_utf8" => {
            Some(fz_runtime::ir_runtime::fz_bitstring_valid_utf8 as *const ())
        }
        "fz_brand_bitstring_as_utf8" => {
            Some(fz_runtime::ir_runtime::fz_brand_bitstring_as_utf8 as *const ())
        }
        _ => None,
    };
    if let Some(fp) = native {
        return Ok(fp);
    }
    // Fallback: dlsym for user-declared externs not in the native table.
    use std::ffi::CString;
    let cname = CString::new(name).map_err(|e| format!("bad symbol name: {}", e))?;
    #[cfg(unix)]
    let ptr = unsafe { libc::dlsym(libc::RTLD_DEFAULT, cname.as_ptr()) };
    #[cfg(not(unix))]
    let ptr: *mut std::ffi::c_void = std::ptr::null_mut();
    if ptr.is_null() {
        return Err(format!("dlsym: symbol `{}` not found", name));
    }
    Ok(ptr as *const ())
}

unsafe fn dispatch_fn_returning(fp: *const (), args: &[u64]) -> u64 {
    match args.len() {
        0 => unsafe {
            let f: unsafe extern "C" fn() -> u64 = std::mem::transmute(fp);
            f()
        },
        1 => unsafe {
            let f: unsafe extern "C" fn(u64) -> u64 = std::mem::transmute(fp);
            f(args[0])
        },
        2 => unsafe {
            let f: unsafe extern "C" fn(u64, u64) -> u64 = std::mem::transmute(fp);
            f(args[0], args[1])
        },
        3 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64) -> u64 = std::mem::transmute(fp);
            f(args[0], args[1], args[2])
        },
        4 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64, u64) -> u64 = std::mem::transmute(fp);
            f(args[0], args[1], args[2], args[3])
        },
        n => panic!("extern arity {} not supported (max 4)", n),
    }
}

unsafe fn dispatch_fn_void(fp: *const (), args: &[u64]) {
    match args.len() {
        0 => unsafe {
            let f: unsafe extern "C" fn() = std::mem::transmute(fp);
            f()
        },
        1 => unsafe {
            let f: unsafe extern "C" fn(u64) = std::mem::transmute(fp);
            f(args[0])
        },
        2 => unsafe {
            let f: unsafe extern "C" fn(u64, u64) = std::mem::transmute(fp);
            f(args[0], args[1])
        },
        3 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64) = std::mem::transmute(fp);
            f(args[0], args[1], args[2])
        },
        4 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64, u64) = std::mem::transmute(fp);
            f(args[0], args[1], args[2], args[3])
        },
        n => panic!("extern arity {} not supported (max 4)", n),
    }
}

// ===== Test-only symbol registry (fz-swt.7) ================================

/// fz-swt.10 — expose the test counter dtor's raw address so JIT-leg
/// fixture tests can register it with the `JITBuilder`. Lives in this
/// module to share the `DTOR_FIRED` / `DTOR_LAST_PAYLOAD` statics with
/// the interp-leg tests below.
#[cfg(test)]
pub(crate) fn tests_support_test_dtor_addr() -> *const u8 {
    tests_support::_resource_test_dtor as *const u8
}

/// fz-swt.10 — accessors for the test dtor counters, used by both the
/// interp-leg tests in this file and the JIT-leg tests in
/// `ir_codegen_tests.rs`.
#[cfg(test)]
pub(crate) fn tests_support_dtor_reset() {
    use std::sync::atomic::Ordering;
    tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
    tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);
}

#[cfg(test)]
pub(crate) fn tests_support_dtor_fired() -> usize {
    tests_support::DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed)
}

#[cfg(test)]
pub(crate) fn tests_support_dtor_last_payload() -> u64 {
    tests_support::DTOR_LAST_PAYLOAD.load(std::sync::atomic::Ordering::Relaxed)
}

/// fz-swt.10 — shared lock so JIT-leg and interp-leg resource tests
/// don't race on the static `DTOR_*` counters.
#[cfg(test)]
pub(crate) fn tests_support_lock() -> &'static std::sync::Mutex<()> {
    static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    &LOCK
}

#[cfg(test)]
mod tests_support {
    use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

    pub static DTOR_FIRED: AtomicUsize = AtomicUsize::new(0);
    pub static DTOR_LAST_PAYLOAD: AtomicU64 = AtomicU64::new(0);

    /// Counter-bumping dtor. Used by the fz-side test as the
    /// `&_resource_test_dtor/1` wrapped extern: bumps a global counter
    /// and records the payload it received. Verifies that the BIF stored
    /// the right C-ABI fn ptr and that MSO sweep invoked it on the right
    /// payload.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn _resource_test_dtor(payload: u64) {
        DTOR_FIRED.fetch_add(1, Ordering::Relaxed);
        DTOR_LAST_PAYLOAD.store(payload, Ordering::Relaxed);
    }

    pub fn lookup_test_symbol(name: &str) -> Option<*const ()> {
        match name {
            "_resource_test_dtor" => Some(_resource_test_dtor as *const ()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod resource_bif_tests {
    use super::*;
    use crate::test_runner;
    use std::sync::atomic::Ordering;

    /// fz-swt.7 acceptance — interp BIF round-trip.
    ///
    /// User-level fz source declares a wrapper around a C extern and uses
    /// `make_resource(payload, &wrapper/1)`. The interp BIF walks the
    /// closure's IR body, resolves the extern symbol to the C fn pointer
    /// in `tests_support`, allocates an off-heap Resource, and returns a
    /// `HeapKind::Resource` stub. The process heap is dropped at test
    /// scope exit; MSO sweep invokes the dtor on the payload exactly once.
    #[test]
    fn make_resource_bif_round_trip() {
        let _g = super::tests_support_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
        tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn test_make_resource() do
  r = make_resource(42, &dwrap/1)
  assert(true)
end
"#;
        test_runner::run_str(src).expect("test_runner run_str succeeded");

        // Force the interp's task registry to drop. Process drop drops
        // its Heap, which fires `mso_drop_all` and invokes our dtor.
        super::interp_reset_state();

        assert_eq!(
            tests_support::DTOR_FIRED.load(Ordering::Relaxed),
            1,
            "dtor must fire exactly once after process heap drop"
        );
        // fz-4mk — the dtor body runs as ordinary fz code through
        // dispatched closure; the extern's `:: integer` marshal class
        // unboxes the payload before the C fn sees it. So the C dtor
        // receives the *unboxed* int 42, not the tagged FzValue bits.
        assert_eq!(
            tests_support::DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
            42,
            "dtor (called via fz dispatch + extern unboxing) receives the unboxed int payload"
        );
    }

    /// fz-swt.9 acceptance — aliasing inside a single process.
    ///
    /// `r2 = r1` copies the FzValue tag bits; both names refer to the
    /// same on-heap stub which holds a single refcount edge to the
    /// off-heap Resource. The dtor must fire **exactly once** when the
    /// process heap drops — not zero times (we'd be leaking the
    /// payload), and not twice (we'd be double-freeing).
    #[test]
    fn aliasing_in_one_process_fires_dtor_once() {
        let _g = super::tests_support_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
        tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn test_alias_once() do
  r1 = make_resource(7, &dwrap/1)
  r2 = r1
  r3 = r2
  # Three names, one off-heap Resource. Until heap drop, refcount is 1.
  assert(true)
end
"#;
        test_runner::run_str(src).expect("test_runner run_str succeeded");
        super::interp_reset_state();

        assert_eq!(
            tests_support::DTOR_FIRED.load(Ordering::Relaxed),
            1,
            "aliasing three bindings must still produce exactly one dtor call",
        );
        // fz-4mk — dtor dispatches as fz code, extern unboxes (see
        // make_resource_bif_round_trip).
        assert_eq!(
            tests_support::DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
            7,
            "dtor receives the unboxed int payload",
        );
    }

    /// fz-swt.9 acceptance — two *distinct* `make_resource` calls each
    /// fire their dtor exactly once. Confirms we're counting allocations,
    /// not bindings, and that the MSO sweep walks the chain correctly
    /// when it contains more than one Resource stub.
    #[test]
    fn two_distinct_resources_each_fire_once() {
        let _g = super::tests_support_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
        tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn test_two_resources() do
  a = make_resource(11, &dwrap/1)
  b = make_resource(22, &dwrap/1)
  assert(true)
end
"#;
        test_runner::run_str(src).expect("test_runner run_str succeeded");
        super::interp_reset_state();

        assert_eq!(
            tests_support::DTOR_FIRED.load(Ordering::Relaxed),
            2,
            "two distinct make_resource calls must each fire their dtor once",
        );
    }

    /// fz-swt.8 acceptance — `.value` round-trip through the interp.
    ///
    /// `get/1` lives in module `R` (the declaring module of the opaque
    /// alias `t`) and returns `h.value`. The test invokes it from a
    /// `test_*` fn — also in `R` — to satisfy the opaque-visibility
    /// gate. The handle is constructed via `make_resource(99, ...)`;
    /// after `.value` the interp must read back the raw `99` payload.
    #[test]
    fn value_accessor_round_trip_in_interp() {
        let _g = super::tests_support_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
        tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

        // Note: test fns must live at top level (the test_runner only
        // discovers `test_*` fns by their FINAL segment). We therefore
        // keep the dtor wrapper, the resource ctor wrapper, the
        // accessor and the assertion at top-level too, and rely on
        // the opaque alias being a top-level (unqualified) tag — its
        // visibility gate trivially passes (no owner module). This
        // exercises the runtime read path (`fz_map_get` recognising
        // `HeapKind::Resource`) end-to-end; the visibility gate is
        // covered by the typer-side unit tests above.
        // Declaring module `R` wraps the opaque alias + accessor; the
        // dtor wrapper and the `test_*` entry stay at top level (the
        // test_runner only discovers `test_*` fns by their FINAL
        // segment, and item-macros inside a `defmodule` body produce
        // bare-named fns per fz-ul4.16.5). `get_value` lives inside
        // `R`, where the visibility gate accepts the `.value` access.
        // `test_value_round_trip` calls `R.get_value` from top level
        // — visibility is irrelevant on the call site, only on the
        // `.value` syntax itself.
        let src = r#"
defmodule R do
  @type t :: opaque resource(integer)

  fn get_value(h), do: h.value
end

extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)

fn test_value_round_trip() do
  r = make_resource(99, &dwrap/1)
  assert_eq(R.get_value(r), 99)
end
"#;
        crate::test_runner::run_str(src).expect("test_runner run_str succeeded");
        // Clean up; verify the dtor fired exactly once with payload 99
        // (FzValue bits) once the process heap drops.
        super::interp_reset_state();
        assert_eq!(
            tests_support::DTOR_FIRED.load(Ordering::Relaxed),
            1,
            "dtor fires once on heap drop",
        );
        // fz-4mk — see make_resource_bif_round_trip; dtor sees unboxed.
        assert_eq!(
            tests_support::DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
            99,
            "dtor receives the unboxed int payload",
        );
    }
}

// ----- fz-yxs/fz-2v3 — selective receive interp tests -----

#[cfg(test)]
mod receive_tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn lower_src(src: &str) -> Module {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        crate::ir_lower::lower_program(&mut crate::types_seam::ConcreteTypes, &prog).expect("lower")
    }

    fn run_and_capture(src: &str) -> Result<String, String> {
        let m = lower_src(src);
        let _ = fz_runtime::ir_runtime::test_capture_take();
        run_main(&m)?;
        Ok(fz_runtime::ir_runtime::test_capture_take().join("\n"))
    }

    /// Initial-scan hit: the message is already in the mailbox at the
    /// point the receive runs (self-send then receive).
    #[test]
    fn initial_scan_pinned_match() {
        let src = r#"
            fn main() do
              ref = make_ref()
              send(self(), {:reply, ref, :ok})
              v = receive do
                {:reply, ^ref, val} -> val
              end
              print(v)
            end
        "#;
        let out = run_and_capture(src).expect("interp run");
        assert!(out.contains(":ok"), "expected :ok, got: {}", out);
    }

    /// Sender-side probe hit: receiver parks, then a sender delivers a
    /// matching message; the sender-side probe wakes the receiver with
    /// the matched body.
    #[test]
    fn sender_side_probe_match() {
        let src = r#"
            fn child(parent) do
              send(parent, {:reply, :tag, 99})
            end
            fn main() do
              me = self()
              spawn(fn () -> child(me))
              v = receive do
                {:reply, :tag, val} -> val
              end
              print(v)
            end
        "#;
        let out = run_and_capture(src).expect("interp run");
        assert!(out.contains("99"), "expected 99, got: {}", out);
    }

    /// `after 0` fires the after body when nothing in the mailbox matches.
    #[test]
    fn after_zero_fires_immediately_on_empty_mailbox() {
        let src = r#"
            fn main() do
              v = receive do
                {:never, _} -> :hit
              after 0 -> :timed_out
              end
              print(v)
            end
        "#;
        let out = run_and_capture(src).expect("interp run");
        assert!(
            out.contains(":timed_out"),
            "expected :timed_out, got: {}",
            out
        );
    }

    /// Receiver-side scan finds a message left in the mailbox by an
    /// earlier `receive` that skipped it.
    #[test]
    fn receiver_scan_finds_earlier_skipped_message() {
        let src = r#"
            fn main() do
              me = self()
              send(me, {:a, 1})
              send(me, {:b, 2})
              vb = receive do
                {:b, x} -> x
              end
              va = receive do
                {:a, x} -> x
              end
              print({va, vb})
            end
        "#;
        let out = run_and_capture(src).expect("interp run");
        assert!(out.contains("{1, 2}"), "expected {{1, 2}}, got: {}", out);
    }

    /// fixtures/receive_selective_refs/input.fz — the design proof point
    /// for fz-recv: sender-side miss, sender-side hit, and receiver-side
    /// scan hit in a single trace. See docs/receive-matched-stress-test.html.
    #[test]
    fn fixture_receive_selective_refs() {
        let src = std::fs::read_to_string("fixtures/receive_selective_refs/input.fz")
            .expect("read fixture");
        let out = run_and_capture(&src).expect("interp run");
        assert!(
            out.contains("{:k_a, :k_b}"),
            "expected {{:k_a, :k_b}}, got: {}",
            out
        );
    }
}
