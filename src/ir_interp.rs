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
}

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
        Ok(InterpStep::Blocked(..)) => {
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
        Prim::Extern(eid, args) => {
            let arg_vals = collect(env, args)?;
            call_extern(module, *eid, &arg_vals)?
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
            use crate::types::{BasicBits, Component};
            use fz_runtime::fz_value::{HeapKind, Tag};
            let val = env_get(env, *v)?;
            let tag = val.tag();
            // Hoist heap inspection — many Component arms need (header, kind).
            let heap = val.unbox_ptr().map(|ptr| {
                let header = unsafe { &*ptr };
                (header, HeapKind::from_u16(header.kind))
            });
            let mut matched = false;
            for component in descr.components() {
                match component {
                    Component::Ints(_) => {
                        matched |= tag == Tag::Int;
                    }
                    Component::Atoms(view) => {
                        // fz-yan.2 — atoms axis subsumes BasicBits::NIL / ::BOOL.
                        if view.is_any() {
                            matched |= tag == Tag::Atom;
                        } else if view.cofinite() {
                            return Err(
                                "TypeTest: cofinite atom literal sets not yet supported in interpreter"
                                    .into(),
                            );
                        } else if tag == Tag::Atom {
                            let id = val.unbox_atom().expect("atom-tagged");
                            for name in view.finite().expect("finite (non-cofinite)") {
                                if let Some(pos) = module.atom_names.iter().position(|n| n == name)
                                    && pos as u32 == id
                                {
                                    matched = true;
                                    break;
                                }
                            }
                        }
                    }
                    Component::Floats(_) => {
                        if let Some((_, Some(HeapKind::Float))) = heap {
                            matched = true;
                        }
                    }
                    Component::Basic(bits) => {
                        if let Some((_, Some(hk))) = heap {
                            if bits.contains_all(BasicBits::VEC_I64) && hk == HeapKind::VecI64 {
                                matched = true;
                            }
                            if bits.contains_all(BasicBits::VEC_F64) && hk == HeapKind::VecF64 {
                                matched = true;
                            }
                            if bits.contains_all(BasicBits::VEC_U8) && hk == HeapKind::VecU8 {
                                matched = true;
                            }
                            if bits.contains_all(BasicBits::VEC_BIT) && hk == HeapKind::VecBit {
                                matched = true;
                            }
                        }
                    }
                    Component::Tuples(view) => {
                        // fz-ul4.36 — match if value is HeapKind::Struct with
                        // matching schema_id. Negated tuple clauses unsupported.
                        assert!(
                            !view.has_negations(),
                            "TypeTest: negated tuple clauses not yet supported"
                        );
                        if let Some((header, Some(HeapKind::Struct))) = heap {
                            let actual_schema = header.schema_id;
                            for arity in view.arities() {
                                let want_schema = interp_tuple_schema_id(arity);
                                if actual_schema == want_schema {
                                    matched = true;
                                    break;
                                }
                            }
                        }
                    }
                    // Unhandled axes — silent no-match. The pre-Component
                    // implementation ignored these too. Compiler-enforced
                    // exhaustiveness means any future axis addition surfaces
                    // this gap explicitly rather than silently mis-typing.
                    Component::Strs(_)
                    | Component::Opaques(_)
                    | Component::Vars(_)
                    | Component::Lists(_)
                    | Component::Funcs(_)
                    | Component::Maps(_) => {}
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

/// fz-swt.7 / fz-swt.10 — given a closure FzValue produced by
/// `&name/arity`, resolve the C-ABI fn pointer to install as the
/// resource's dtor.
///
/// Both interp and JIT/AOT closures store the wrapper fn's `FnId` in the
/// `_reserved` field of the on-heap `HeapKind::Closure` header. The
/// closure's `+16` slot holds different things depending on the leg
/// (interp: null; JIT/AOT: the body's func_addr in closure-target sig,
/// which is NOT a C-ABI `fn(u64)` and cannot be called directly), so we
/// uniformly ignore `+16` and resolve the dtor by walking the wrapper
/// fn's IR to find its underlying `Prim::Extern(eid, _)` call. That
/// extern's symbol is then resolved through the same machinery
/// `call_extern` uses below.
///
/// Pattern recognised: any block in the fn body that contains
/// `Let(_, Prim::Extern(eid, _))` — i.e., the canonical
/// `fn wrap(x), do: some_extern(x)` shape (and any single-extern
/// wrapper whose CPS lowering produces an Extern stmt anywhere). Richer
/// dtor wrappers (multiple externs, branching) require evaluating the
/// closure body, which is out of scope for v0; the contract is "fz-side
/// dtor must be a thin wrapper around a single C extern."
pub(crate) fn resolve_dtor_from_closure(
    module: &Module,
    closure: FzValue,
) -> Result<unsafe extern "C" fn(u64), String> {
    use fz_runtime::fz_value::HeapKind;
    let p = closure
        .unbox_ptr()
        .ok_or_else(|| "make_resource: dtor arg is not a heap value".to_string())?;
    let header = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Closure) {
        return Err("make_resource: dtor arg is not a closure".into());
    }
    let fn_id = crate::fz_ir::FnId(header._reserved);
    let fnir = module.fn_by_id(fn_id);
    let eid = fnir.blocks.iter().find_map(|b| {
        b.stmts.iter().find_map(|s| match s {
            Stmt::Let(_, Prim::Extern(eid, _)) => Some(*eid),
            _ => None,
        })
    });
    let eid = eid.ok_or_else(|| {
        format!(
            "make_resource: dtor closure for `{}` has no Prim::Extern in body",
            fnir.name
        )
    })?;
    let decl = module.extern_by_id(eid);
    let fp = resolve_symbol(&decl.symbol)?;
    // SAFETY: resolved fn pointer for a C-ABI extern declared in the
    // module; ExternTy constraints guarantee u64-wide scalar params.
    let f: unsafe extern "C" fn(u64) = unsafe { std::mem::transmute(fp) };
    Ok(f)
}

/// fz-swt.10 — shared work behind both the interp `fz_make_resource` BIF
/// and the JIT/AOT `MakeResourceHook` thunk: resolve the dtor, allocate
/// an off-heap `Resource` + on-heap stub on the current process heap,
/// return the FzValue bits of the stub.
pub(crate) fn make_resource_in_current_process(
    module: &Module,
    payload: u64,
    dtor_closure: FzValue,
) -> Result<FzValue, String> {
    let dtor = resolve_dtor_from_closure(module, dtor_closure)?;
    let handle = fz_runtime::resource::ResourceHandle::new(payload, dtor);
    let heap = &mut fz_runtime::process::current_process().heap;
    let stub = fz_runtime::resource::alloc_resource(heap, handle);
    Ok(FzValue::from_ptr(stub.as_raw()))
}

fn call_extern(module: &Module, eid: ExternId, args: &[FzValue]) -> Result<FzValue, String> {
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
        "fz_send" => {
            if args.len() != 2 {
                return Err(format!("fz_send/2 got {} args", args.len()));
            }
            let receiver = args[0]
                .unbox_int()
                .ok_or_else(|| "send/2: pid must be Int".to_string())?
                as u32;
            interp_send(receiver, args[1])?;
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
        "fz_send" => Some(fz_runtime::ir_runtime::fz_send as *const ()),
        // fz-swt.11 — fixture/test dtor exported from the runtime crate.
        // Bound here so interp-leg invocations of fixtures using this
        // symbol (e.g. when `fz interp` is run by hand on the AOT-only
        // fixture) reach the same Rust fn the AOT-linked binary uses.
        "fz_resource_test_print_dtor" => {
            Some(fz_runtime::resource::fz_resource_test_print_dtor as *const ())
        }
        // fz-swt.13 — File-module test helpers. Same rationale as the
        // print-dtor binding above: keep the interp leg of the fixture
        // matrix self-contained, no dlsym dependence.
        "fz_test_open_tmpfile" => Some(fz_runtime::resource::fz_test_open_tmpfile as *const ()),
        "fz_test_close_fd" => Some(fz_runtime::resource::fz_test_close_fd as *const ()),
        // fz-vw1 — libc shims for the extern-binary integration fixture.
        "fz_test_open_writeonly" => Some(fz_runtime::libc_io::fz_test_open_writeonly as *const ()),
        "fz_test_write_close" => Some(fz_runtime::libc_io::fz_test_write_close as *const ()),
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
        // The dtor receives the raw FzValue bits of the payload we stored
        // (the BIF stores args[0].0 verbatim). For Int 42, FzValue.0 is
        // `42 << 4 | INT_TAG` (Int tag = 0), i.e. 672.
        // FzValue Int encoding: (n << 3) | TAG_INT (=1). For n=42 → 337.
        assert_eq!(
            tests_support::DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
            fz_runtime::fz_value::FzValue::from_int(42).0,
            "dtor receives the stored FzValue.0 bits of payload 42",
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
        assert_eq!(
            tests_support::DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
            fz_runtime::fz_value::FzValue::from_int(7).0,
            "dtor receives the stored FzValue.0 bits of payload 7",
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
        assert_eq!(
            tests_support::DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
            fz_runtime::fz_value::FzValue::from_int(99).0,
            "dtor receives the stored FzValue.0 bits of payload 99",
        );
    }
}
