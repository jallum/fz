//! fz-ul4.23.5.2 — IR interpreter on FzValue, heap, and runtime substrate.
//!
//! Walks a `fz_ir::Module` directly, just like the legacy ir_interp.rs, but
//! uses the SAME value representation, heap, and runtime FFI as the JIT.
//! Spawn/send/receive call into the same runtime.rs scheduler. Print
//! renders through `crate::ir_runtime::fz_print_value`. Heap allocations
//! go through the current Process's Heap.
//!
//! Scope at .5.2: minimal for fixtures/add1.fz —
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

use std::collections::HashMap;
use std::cell::{Cell, RefCell};

use crate::fz_ir::{BinOp, BuiltinKind, Const, FnId, Module, Prim, Stmt, Term, Var};
use crate::fz_value::FzValue;
use crate::process::Process;

// ===== Interp-internal scheduler (fz-ul4.23.5.8) =====
//
// The interp owns its own task registry separate from runtime.rs::Runtime
// (which is wired into the JIT trampoline). They share the Process type,
// the FzValue rep, and the heap — so messages and mailboxes are byte-
// compatible between paths.
//
// Scheduling model: eager-synchronous. Builtin::Spawn runs the spawned
// task to completion before returning (i.e. spawned tasks are
// synchronous from the parent's perspective). Term::Receive pops from
// the current task's mailbox; if empty, it errors — there is no
// preemption / suspend-and-resume in the interp v1 since fz-IR doesn't
// run on stackable continuations here.
//
// This matches concurrency_ping_pong.fz's semantics (parent spawns child
// → child eagerly runs send(1, 42) → returns; parent's receive pops 42)
// but does NOT match richer concurrency patterns where the child holds
// internal state across receive points. fz-ul4.23.5.8.1 (follow-up)
// tracks the proper green-thread scheduler.

thread_local! {
    static INTERP_TASKS: RefCell<HashMap<u32, Box<Process>>> =
        RefCell::new(HashMap::new());
    static INTERP_NEXT_PID: Cell<u32> = const { Cell::new(2) };
    static INTERP_SCHEMAS: RefCell<Option<std::rc::Rc<std::cell::RefCell<crate::heap::SchemaRegistry>>>> =
        const { RefCell::new(None) };
}

fn interp_register_task(pid: u32, process: Box<Process>) -> *mut Process {
    INTERP_TASKS.with(|t| {
        let mut tasks = t.borrow_mut();
        tasks.insert(pid, process);
        tasks.get_mut(&pid).map(|b| b.as_mut() as *mut Process).unwrap()
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
    INTERP_TASKS.with(|t| {
        let mut tasks = t.borrow_mut();
        match tasks.get_mut(&receiver_pid) {
            Some(task) => {
                task.mailbox.push_back(msg);
                Ok(())
            }
            None => Err(format!("send: no task with pid {}", receiver_pid)),
        }
    })
}

fn interp_reset_state() {
    INTERP_TASKS.with(|t| t.borrow_mut().clear());
    INTERP_NEXT_PID.with(|n| n.set(2));
}

/// Run `module`'s `main` fn through the interpreter.
///
/// Creates a fresh Process, installs it in CURRENT_PROCESS for the duration
/// of the run (so runtime FFI fns like fz_print_value see a valid Process),
/// drives main to completion, returns the Process's `halt_value`.
pub fn run_main(module: &Module) -> Result<i64, String> {
    let main_id = module
        .fn_by_name("main")
        .ok_or("no `main/0` fn found")?
        .id;
    interp_reset_state();
    let user_schemas =
        std::rc::Rc::new(std::cell::RefCell::new(crate::heap::SchemaRegistry::new()));
    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = Some(user_schemas.clone()));
    let mut main_process = Box::new(Process::new(user_schemas));
    main_process.pid = 1;
    let main_ptr = interp_register_task(1, main_process);
    let prev = crate::process::CURRENT_PROCESS.with(|c| c.replace(main_ptr));
    let result = run_fn(module, main_id, Vec::new());
    crate::process::CURRENT_PROCESS.with(|c| c.set(prev));
    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = None);
    let r = result?;
    Ok(value_to_halt(r))
}

/// Spawn a new task at `fn_id`, run it to completion synchronously, and
/// return its pid. Matches the JIT's pid allocation convention (main=1,
/// children get sequential pids starting at 2).
fn interp_spawn(module: &Module, fn_id: FnId) -> Result<u32, String> {
    let pid = interp_next_pid();
    let user_schemas = INTERP_SCHEMAS
        .with(|s| s.borrow().as_ref().cloned())
        .ok_or("interp_spawn: no INTERP_SCHEMAS installed (call run_main first)")?;
    let mut child = Box::new(Process::new(user_schemas));
    child.pid = pid;
    let child_ptr = interp_register_task(pid, child);
    let prev = crate::process::CURRENT_PROCESS.with(|c| c.replace(child_ptr));
    let result = run_fn(module, fn_id, Vec::new());
    crate::process::CURRENT_PROCESS.with(|c| c.set(prev));
    result?;
    Ok(pid)
}

fn value_to_halt(v: FzValue) -> i64 {
    use crate::fz_value::Tag;
    match v.tag() {
        Tag::Int => v.unbox_int().unwrap(),
        Tag::Atom => v.unbox_atom().unwrap() as i64,
        Tag::Special => {
            if v.is_true() {
                1
            } else if v.is_false() {
                0
            } else {
                0
            }
        }
        Tag::Ptr | Tag::Reserved => v.0 as i64,
    }
}

/// Run an fz fn to completion. Tail calls reuse this stack frame (no Rust
/// recursion) so deeply tail-recursive programs run in O(1) Rust stack —
/// `tail_recursion.fz`'s 100k-deep count exits cleanly.
///
/// Non-tail calls (Term::Call, Term::CallClosure) still recurse into a
/// fresh `run_fn`; that's correct for the language's semantics (the
/// continuation runs AFTER the callee returns), and it's bounded by the
/// program's actual call depth which is typically small.
fn run_fn(module: &Module, mut fn_id: FnId, mut args: Vec<FzValue>) -> Result<FzValue, String> {
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
                    let result = run_fn(module, *callee, arg_vals)?;
                    let cap_vals = collect(&env, &continuation.captured)?;
                    let mut cont_args = vec![result];
                    cont_args.extend(cap_vals);
                    // The continuation invocation is itself a tail
                    // position — reuse this stack frame.
                    fn_id = continuation.fn_id;
                    args = cont_args;
                    continue 'tail;
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
                    let result = run_fn(module, lam_fn, clos_args)?;
                    let cap_vals = collect(&env, &continuation.captured)?;
                    let mut cont_args = vec![result];
                    cont_args.extend(cap_vals);
                    fn_id = continuation.fn_id;
                    args = cont_args;
                    continue 'tail;
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
                Term::Return(v) => return env_get(&env, *v),
                Term::Halt(v) => return env_get(&env, *v),
                Term::Receive { continuation } => {
                    let msg = crate::process::current_process()
                        .mailbox
                        .pop_front()
                        .ok_or_else(|| {
                            "interp: receive on empty mailbox (no preemption in v1 scheduler)"
                                .to_string()
                        })?;
                    let cap_vals = collect(&env, &continuation.captured)?;
                    let mut cont_args = vec![msg];
                    cont_args.extend(cap_vals);
                    fn_id = continuation.fn_id;
                    args = cont_args;
                    continue 'tail;
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

fn eval_prim(
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
        Prim::Builtin(bid, args) => {
            let arg_vals = collect(env, args)?;
            run_builtin(module, *bid, &arg_vals)?
        }
        Prim::MakeClosure(fn_id, captured) => {
            let cap_vals: Vec<FzValue> = collect(env, captured)?;
            let p = crate::process::current_process()
                .heap
                .alloc_closure(fn_id.0, &cap_vals);
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

/// Read an interp-side closure value: the heap object's `schema_id` field
/// is repurposed (per the JIT layout, fz-ul4.11.32) to hold the IR FnId of
/// the lambda body, and `flags` holds the captured count. Returns the
/// callee fn id plus a Vec of captured FzValues read from the payload.
fn unpack_closure(v: FzValue) -> Result<(FnId, Vec<FzValue>), String> {
    use crate::fz_value::HeapKind;
    let p = v.unbox_ptr().ok_or_else(|| {
        format!(
            "call_closure on non-ptr value: {}",
            crate::fz_value::debug::render(v.0)
        )
    })?;
    let header = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Closure) {
        return Err("call_closure on non-closure heap value".into());
    }
    let fn_id = FnId(header.schema_id);
    let cap_count = header.flags as usize;
    let payload = unsafe { (p as *const u8).add(16) as *const u64 };
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
        Const::Float(f) => FzValue(crate::ir_runtime::fz_alloc_float(f.to_bits())),
        // Str: no first-class heap kind yet (.11.x lowers strings to
        // Bitstring at the AST level). Should never reach the interp as a
        // raw Const::Str; if it does, surface honestly.
        Const::Str(_) => FzValue::NIL,
    }
}

fn eval_binop(op: BinOp, a: FzValue, b: FzValue) -> Result<FzValue, String> {
    // Arithmetic: both-Int fast path matches the JIT's inline lowering;
    // mixed or boxed-float operands fall back to the shared FFI helper so
    // promotion semantics stay identical across paths.
    macro_rules! int_arith {
        ($op:tt, $ffi:path) => {
            match (a.unbox_int(), b.unbox_int()) {
                (Some(x), Some(y)) => Ok(FzValue::from_int(x $op y)),
                _ => Ok(FzValue($ffi(a.0, b.0))),
            }
        };
    }
    match op {
        BinOp::Add => int_arith!(+, crate::ir_runtime::fz_arith_add),
        BinOp::Sub => int_arith!(-, crate::ir_runtime::fz_arith_sub),
        BinOp::Mul => int_arith!(*, crate::ir_runtime::fz_arith_mul),
        BinOp::Div => int_arith!(/, crate::ir_runtime::fz_arith_div),
        BinOp::Mod => int_arith!(%, crate::ir_runtime::fz_arith_mod),
        BinOp::Eq => Ok(FzValue(crate::ir_runtime::fz_value_eq(a.0, b.0))),
        BinOp::Neq => {
            let eq = FzValue(crate::ir_runtime::fz_value_eq(a.0, b.0));
            Ok(if eq.is_true() { FzValue::FALSE } else { FzValue::TRUE })
        }
        BinOp::Lt => Ok(FzValue(crate::ir_runtime::fz_cmp_lt(a.0, b.0))),
        BinOp::Le => Ok(FzValue(crate::ir_runtime::fz_cmp_le(a.0, b.0))),
        BinOp::Gt => Ok(FzValue(crate::ir_runtime::fz_cmp_gt(a.0, b.0))),
        BinOp::Ge => Ok(FzValue(crate::ir_runtime::fz_cmp_ge(a.0, b.0))),
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
            crate::ir_runtime::fz_print_value(args[0].0);
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
            let eq = FzValue(crate::ir_runtime::fz_value_eq(args[0].0, args[1].0));
            if eq.is_true() {
                Ok(FzValue::NIL)
            } else {
                Err(format!(
                    "assertion failed: assert_eq({}, {})",
                    crate::fz_value::debug::render(args[0].0),
                    crate::fz_value::debug::render(args[1].0),
                ))
            }
        }
        BuiltinKind::AssertNeq => {
            if args.len() != 2 {
                return Err(format!("assert_neq/2 got {} args", args.len()));
            }
            let eq = FzValue(crate::ir_runtime::fz_value_eq(args[0].0, args[1].0));
            if eq.is_false() {
                Ok(FzValue::NIL)
            } else {
                Err(format!(
                    "assertion failed: assert_neq({}, {})",
                    crate::fz_value::debug::render(args[0].0),
                    crate::fz_value::debug::render(args[1].0),
                ))
            }
        }
        BuiltinKind::Spawn => {
            if args.len() != 1 {
                return Err(format!("spawn/1 got {} args", args.len()));
            }
            let (fn_id, captured) = unpack_closure(args[0])?;
            if !captured.is_empty() {
                return Err(format!(
                    "interp spawn/1: closure with {} captures not yet supported \
                     (v1 restriction matches the JIT, see fz-ul4.19.2)",
                    captured.len()
                ));
            }
            let pid = interp_spawn(module, fn_id)?;
            Ok(FzValue::from_int(pid as i64))
        }
        BuiltinKind::SelfPid => {
            Ok(FzValue::from_int(
                crate::process::current_process().pid as i64,
            ))
        }
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
            Ok(FzValue(crate::ir_runtime::fz_vec_get(args[0].0, args[1].0)))
        }
    }
}
