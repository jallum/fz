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

use crate::fz_ir::{BinOp, BuiltinKind, Const, FnId, Module, Prim, Stmt, Term, Var};
use crate::fz_value::FzValue;
use crate::process::Process;

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
    let user_schemas =
        std::rc::Rc::new(std::cell::RefCell::new(crate::heap::SchemaRegistry::new()));
    let mut process = Process::new(user_schemas);
    let ptr: *mut Process = &mut process;
    let prev = crate::process::CURRENT_PROCESS.with(|c| c.replace(ptr));
    let result = run_fn(module, main_id, Vec::new());
    crate::process::CURRENT_PROCESS.with(|c| c.set(prev));
    let r = result?;
    // For `main`, the returned FzValue's int (or boxed-float bits) becomes
    // the halt value, mirroring fz_halt's per-tag logic.
    Ok(value_to_halt(r))
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

fn run_fn(module: &Module, fn_id: FnId, args: Vec<FzValue>) -> Result<FzValue, String> {
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
    for (p, v) in entry.params.iter().zip(args) {
        env.insert(*p, v);
    }
    let mut cur = fn_ir.entry;
    loop {
        let blk = fn_ir.block(cur);
        for Stmt::Let(v, prim) in &blk.stmts {
            let val = eval_prim(module, prim, &env)?;
            env.insert(*v, val);
        }
        match &blk.terminator {
            Term::Goto(b, args) => {
                let vals: Vec<FzValue> = args
                    .iter()
                    .map(|v| env_get(&env, *v))
                    .collect::<Result<_, _>>()?;
                let next = module.fn_by_id(fn_id).block(*b);
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
                args,
                continuation,
            } => {
                let arg_vals = collect(&env, args)?;
                let result = run_fn(module, *callee, arg_vals)?;
                let cap_vals = collect(&env, &continuation.captured)?;
                let mut cont_args = vec![result];
                cont_args.extend(cap_vals);
                return run_fn(module, continuation.fn_id, cont_args);
            }
            Term::TailCall { callee, args } => {
                let arg_vals = collect(&env, args)?;
                return run_fn(module, *callee, arg_vals);
            }
            Term::Return(v) => return env_get(&env, *v),
            Term::Halt(v) => return env_get(&env, *v),
            Term::CallClosure { .. }
            | Term::TailCallClosure { .. } => {
                return Err(
                    "interp .5.2: closure invocation not yet supported (fz-ul4.23.5.4)".into(),
                );
            }
            Term::Receive { .. } => {
                return Err(
                    "interp .5.2: receive not yet supported (fz-ul4.23.5.8)".into(),
                );
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
        _ => {
            return Err(format!(
                "interp .5.2: prim {:?} not yet supported (lands in fz-ul4.23.5.3+)",
                std::mem::discriminant(prim)
            ));
        }
    })
}

fn const_to_fz(c: &Const) -> FzValue {
    match c {
        Const::Int(n) => FzValue::from_int(*n),
        Const::Atom(id) => FzValue::from_atom_id(*id),
        Const::Nil => FzValue::NIL,
        Const::True => FzValue::TRUE,
        Const::False => FzValue::FALSE,
        Const::Float(_) | Const::Str(_) => FzValue::NIL, // .5.3 wires properly
    }
}

fn eval_binop(op: BinOp, a: FzValue, b: FzValue) -> Result<FzValue, String> {
    match op {
        BinOp::Add => {
            // Both Int fast path (matches the JIT's inline path). Mixed-
            // or boxed-float operands fall back to fz_arith_add to share
            // semantics with the JIT exactly.
            match (a.unbox_int(), b.unbox_int()) {
                (Some(x), Some(y)) => Ok(FzValue::from_int(x + y)),
                _ => Ok(FzValue(crate::ir_runtime::fz_arith_add(a.0, b.0))),
            }
        }
        _ => Err(format!(
            "interp .5.2: BinOp::{:?} not yet supported (lands in fz-ul4.23.5.3+)",
            op
        )),
    }
}

fn run_builtin(
    _module: &Module,
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
        _ => Err(format!(
            "interp .5.2: builtin {:?} not yet supported (lands in later .5.x)",
            kind
        )),
    }
}
