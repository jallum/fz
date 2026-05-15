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
//!   Prim::Builtin(Print, ...)
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

use crate::fz_ir::{BinOp, BuiltinKind, Const, FnId, Module, Prim, Stmt, Term, Var};
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
}

thread_local! {
    static INTERP_TASKS: RefCell<HashMap<u32, Box<Process>>> =
        RefCell::new(HashMap::new());
    static INTERP_NEXT_PID: Cell<u32> = const { Cell::new(2) };
    static INTERP_SCHEMAS: RefCell<Option<std::rc::Rc<std::cell::RefCell<fz_runtime::heap::SchemaRegistry>>>> =
        const { RefCell::new(None) };
    /// FIFO run-queue of pids ready to execute.
    static INTERP_RUN_QUEUE: RefCell<VecDeque<u32>> = RefCell::new(VecDeque::new());
    /// Per-task resume state: (resume_fn, cap_vals, after_chain).
    /// cap_vals holds captures only (no message); interp_send prepends the
    /// message. after_chain is the sequence of (fn_id, caps) continuations to
    /// invoke in order after resume_fn returns, passing each return value on.
    static INTERP_RESUME: RefCell<HashMap<u32, (FnId, Vec<FzValue>, Vec<(FnId, Vec<FzValue>)>)>> =
        RefCell::new(HashMap::new());
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

fn interp_send(receiver_pid: u32, msg: FzValue) -> Result<(), String> {
    use fz_runtime::process::ProcessState;
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

    let mut halt_val = 0i64;
    'sched: loop {
        let pid = match INTERP_RUN_QUEUE.with(|q| q.borrow_mut().pop_front()) {
            Some(p) => p,
            None => break,
        };
        let (fn_id, args, mut after) = INTERP_RESUME
            .with(|r| r.borrow_mut().remove(&pid))
            .expect("pid in run_queue with no resume entry");
        let proc_ptr = INTERP_TASKS
            .with(|t| t.borrow().get(&pid).map(|b| b.as_ref() as *const _ as *mut Process))
            .expect("pid in run_queue with no process entry");
        unsafe { (*proc_ptr).state = ProcessState::Running };
        let prev = fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(proc_ptr));
        let mut step = run_fn(module, fn_id, args);
        // Process the after-chain: each Done value is threaded into the next fn.
        loop {
            match step {
                Ok(InterpStep::Done(val)) => {
                    if let Some((next_fn, next_caps)) = after.first().cloned() {
                        after.remove(0);
                        let mut next_args = vec![val];
                        next_args.extend(next_caps);
                        step = run_fn(module, next_fn, next_args);
                        // loop continues
                    } else {
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
    let result = run_fn(module, fn_id, Vec::new());
    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = None);
    match result {
        Ok(InterpStep::Done(_)) => Ok(()),
        Ok(InterpStep::Blocked(..)) => Err("test fn blocked on receive with empty mailbox".to_string()),
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
        Tag::Atom => v.unbox_atom().unwrap() as i64,
        Tag::Special => {
            // Tag::Special has three inhabitants: true → 1, false → 0,
            // nil → 0. The else branch asserts the only remaining
            // possibility; a new Special variant landing here would
            // surface in debug builds.
            if v.is_true() {
                1
            } else if v.is_false() {
                0
            } else {
                debug_assert!(v.is_nil(), "value_to_halt: unrecognized Tag::Special bits");
                0
            }
        }
        Tag::Ptr | Tag::Reserved => v.0 as i64,
    }
}

/// Run an fz fn. Tail calls reuse this stack frame (O(1) Rust stack).
/// Returns Done(val) on Halt/Return or Blocked(fn_id, cap_vals) when a
/// Term::Receive fires on an empty mailbox.
fn run_fn(module: &Module, mut fn_id: FnId, mut args: Vec<FzValue>) -> Result<InterpStep, String> {
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
                let val = eval_prim(module, prim, &env)?;
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
                Term::If(c, t, e) => {
                    let cv = env_get(&env, *c)?;
                    cur = if is_truthy(cv) { *t } else { *e };
                }
                Term::Call {
                    callee,
                    args: call_args,
                    continuation,
                } => {
                    let arg_vals = collect(&env, call_args)?;
                    let outer_cap_vals = collect(&env, &continuation.captured)?;
                    match run_fn(module, *callee, arg_vals)? {
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
                    }
                }
                Term::TailCall {
                    callee,
                    args: call_args,
                } => {
                    let arg_vals = collect(&env, call_args)?;
                    fn_id = *callee;
                    args = arg_vals;
                    continue 'tail;
                }
                Term::CallClosure {
                    closure,
                    args: call_args,
                    continuation,
                } => {
                    let cl = env_get(&env, *closure)?;
                    let (lam_fn, mut clos_args) = unpack_closure(cl)?;
                    clos_args.extend(collect(&env, call_args)?);
                    let outer_cap_vals = collect(&env, &continuation.captured)?;
                    match run_fn(module, lam_fn, clos_args)? {
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
                    }
                }
                Term::TailCallClosure {
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
                Term::Receive { continuation } => {
                    let cap_vals = collect(&env, &continuation.captured)?;
                    match fz_runtime::process::current_process().mailbox.pop_front() {
                        Some(msg) => {
                            let mut cont_args = vec![msg];
                            cont_args.extend(cap_vals);
                            fn_id = continuation.fn_id;
                            args = cont_args;
                            continue 'tail;
                        }
                        None => return Ok(InterpStep::Blocked(continuation.fn_id, cap_vals, vec![])),
                    }
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

fn eval_prim(module: &Module, prim: &Prim, env: &HashMap<Var, FzValue>) -> Result<FzValue, String> {
    Ok(match prim {
        Prim::Const(c) => const_to_fz(c),
        Prim::BinOp(op, a, b) => {
            let av = env_get(env, *a)?;
            let bv = env_get(env, *b)?;
            eval_binop(*op, av, bv)?
        }
        Prim::Builtin(bid, args) => {
            let arg_vals = collect(env, args)?;
            run_builtin(module, *bid, &arg_vals)?
        }
        Prim::MakeClosure(fn_id, captured) => {
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
        // Str: no first-class heap kind yet (.11.x lowers strings to
        // Bitstring at the AST level). Should never reach the interp as a
        // raw Const::Str; if it does, surface honestly.
        Const::Str(_) => FzValue::NIL,
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

fn run_builtin(
    module: &Module,
    bid: crate::fz_ir::BuiltinId,
    args: &[FzValue],
) -> Result<FzValue, String> {
    let Some(kind) = BuiltinKind::from_id(bid) else {
        return Err(format!("interp: unknown builtin id {}", bid.0));
    };
    match kind {
        BuiltinKind::Print => {
            if args.len() != 1 {
                return Err(format!("print/1 got {} args", args.len()));
            }
            fz_runtime::ir_runtime::fz_print_value(args[0].0);
            Ok(FzValue::NIL)
        }
        BuiltinKind::Assert => {
            if args.len() != 1 {
                return Err(format!("assert/1 got {} args", args.len()));
            }
            if is_truthy(args[0]) {
                Ok(FzValue::NIL)
            } else {
                Err("assertion failed".into())
            }
        }
        BuiltinKind::AssertEq => {
            if args.len() != 2 {
                return Err(format!("assert_eq/2 got {} args", args.len()));
            }
            let eq = FzValue(fz_runtime::ir_runtime::fz_value_eq(args[0].0, args[1].0));
            if eq.is_true() {
                Ok(FzValue::NIL)
            } else {
                Err(format!(
                    "assertion failed: assert_eq({}, {})",
                    fz_runtime::fz_value::debug::render(args[0].0),
                    fz_runtime::fz_value::debug::render(args[1].0),
                ))
            }
        }
        BuiltinKind::AssertNeq => {
            if args.len() != 2 {
                return Err(format!("assert_neq/2 got {} args", args.len()));
            }
            let eq = FzValue(fz_runtime::ir_runtime::fz_value_eq(args[0].0, args[1].0));
            if eq.is_false() {
                Ok(FzValue::NIL)
            } else {
                Err(format!(
                    "assertion failed: assert_neq({}, {})",
                    fz_runtime::fz_value::debug::render(args[0].0),
                    fz_runtime::fz_value::debug::render(args[1].0),
                ))
            }
        }
        BuiltinKind::Spawn => {
            // fz-ul4.29.5: lifted zero-captures restriction. Spawn deep-
            // copies the closure (captures included) into the new task's
            // heap; the body fn is invoked with the captures as its entry
            // params (a spawned closure has zero call args, so the entry
            // params are exactly the captures).
            // fz-siu.12: spawn/2 accepts a min_heap_size hint (ignored by
            // the interp — single shared heap, no per-process sizing).
            if args.len() != 1 && args.len() != 2 {
                return Err(format!("spawn/1 or spawn/2 got {} args", args.len()));
            }
            let (fn_id, captured) = unpack_closure(args[0])?;
            // Deep-copy the captured values into the child's heap is
            // implicit: interp runs every task on the same heap (single
            // shared SchemaRegistry, single Process model under the test
            // harness). For correctness of cross-heap semantics under
            // multi-task interp execution see .19's design — v1 interp
            // uses a single heap, so captures are already there.
            let pid = interp_spawn(module, fn_id, captured)?;
            Ok(FzValue::from_int(pid as i64))
        }
        BuiltinKind::SelfPid => Ok(FzValue::from_int(
            fz_runtime::process::current_process().pid as i64,
        )),
        BuiltinKind::Send => {
            if args.len() != 2 {
                return Err(format!("send/2 got {} args", args.len()));
            }
            let receiver = args[0]
                .unbox_int()
                .ok_or_else(|| "send/2: pid must be Int".to_string())?
                as u32;
            interp_send(receiver, args[1])?;
            Ok(args[1])
        }
        BuiltinKind::VecGet => {
            if args.len() != 2 {
                return Err(format!("vec_get/2 got {} args", args.len()));
            }
            Ok(FzValue(fz_runtime::ir_runtime::fz_vec_get(
                args[0].0, args[1].0,
            )))
        }
    }
}
