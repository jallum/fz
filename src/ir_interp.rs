//! fz-IR tree-walking interpreter (debug oracle).
//!
//! Validates fz-IR end-to-end without dragging Cranelift in. Walks the IR
//! directly using the existing crate::value::Value as its runtime
//! representation, so test assertions compare apples to apples.
//!
//! Trampoline-style: the top-level driver loops on Term::Goto / Term::If
//! within a fn; on Term::Call it recursively runs the callee and then the
//! continuation; Term::TailCall and Term::Return short-circuit out.

#![allow(dead_code)]

use crate::fz_ir::{
    BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp, Var,
};
use crate::value::{FzMap, Value};
use std::collections::HashMap;
use std::rc::Rc;

pub struct InterpCtx<'a> {
    pub module: &'a Module,
    /// id N -> name. Empty -> use synthetic "atom_N" names.
    pub atoms: &'a [String],
    /// id N -> name. Empty -> synthetic "builtin_N".
    pub builtins: &'a [String],
}

pub fn run_fn(module: &Module, fn_id: FnId, args: Vec<Value>) -> Result<Value, String> {
    run_fn_with(module, fn_id, args, &[], &[])
}

pub fn run_fn_with(
    module: &Module,
    fn_id: FnId,
    args: Vec<Value>,
    atoms: &[String],
    builtins: &[String],
) -> Result<Value, String> {
    let ctx = InterpCtx { module, atoms, builtins };
    run(&ctx, fn_id, args)
}

fn atom_name(ctx: &InterpCtx, id: u32) -> Rc<str> {
    if (id as usize) < ctx.atoms.len() {
        Rc::from(ctx.atoms[id as usize].as_str())
    } else {
        Rc::from(format!("atom_{}", id).as_str())
    }
}

fn builtin_name(ctx: &InterpCtx, id: u32) -> String {
    if (id as usize) < ctx.builtins.len() {
        ctx.builtins[id as usize].clone()
    } else {
        format!("builtin_{}", id)
    }
}

fn run(ctx: &InterpCtx, fn_id: FnId, args: Vec<Value>) -> Result<Value, String> {
    let fn_ir = ctx.module.fn_by_id(fn_id);
    let mut env: HashMap<Var, Value> = HashMap::new();
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
        for stmt in &blk.stmts {
            let Stmt::Let(v, prim) = stmt;
            let val = eval_prim(ctx, prim, &env)?;
            env.insert(*v, val);
        }
        match &blk.terminator {
            Term::Goto(b, args) => {
                let new_vals: Vec<Value> = args
                    .iter()
                    .map(|v| {
                        env.get(v)
                            .cloned()
                            .ok_or_else(|| format!("unbound var {} in Goto args", v.0))
                    })
                    .collect::<Result<_, _>>()?;
                let next_blk = fn_ir.block(*b);
                if next_blk.params.len() != new_vals.len() {
                    return Err(format!(
                        "Goto target {} expected {} params, got {}",
                        b.0,
                        next_blk.params.len(),
                        new_vals.len()
                    ));
                }
                for (p, val) in next_blk.params.iter().zip(new_vals) {
                    env.insert(*p, val);
                }
                cur = *b;
            }
            Term::If(c, t, e) => {
                let cv = env
                    .get(c)
                    .ok_or_else(|| format!("unbound condition var {}", c.0))?;
                let truthy = is_truthy(cv);
                let next = if truthy { *t } else { *e };
                let next_blk = fn_ir.block(next);
                if !next_blk.params.is_empty() {
                    return Err(format!(
                        "If branch target {} unexpectedly has {} params",
                        next.0,
                        next_blk.params.len()
                    ));
                }
                cur = next;
            }
            Term::Call { callee, args, continuation } => {
                let arg_vals = collect_vals(&env, args)?;
                let result = run(ctx, *callee, arg_vals)?;
                let cap_vals = collect_vals(&env, &continuation.captured)?;
                let mut cont_args = vec![result];
                cont_args.extend(cap_vals);
                return run(ctx, continuation.fn_id, cont_args);
            }
            Term::TailCall { callee, args } => {
                let arg_vals = collect_vals(&env, args)?;
                return run(ctx, *callee, arg_vals);
            }
            Term::Return(v) => {
                return env
                    .get(v)
                    .cloned()
                    .ok_or_else(|| format!("unbound return var {}", v.0));
            }
            Term::Halt(v) => {
                return env
                    .get(v)
                    .cloned()
                    .ok_or_else(|| format!("unbound halt var {}", v.0));
            }
        }
    }
}

fn collect_vals(env: &HashMap<Var, Value>, vars: &[Var]) -> Result<Vec<Value>, String> {
    vars.iter()
        .map(|v| env.get(v).cloned().ok_or_else(|| format!("unbound var {}", v.0)))
        .collect()
}

fn is_truthy(v: &Value) -> bool {
    match v {
        Value::Bool(b) => *b,
        Value::Nil => false,
        _ => true,
    }
}

fn eval_prim(
    ctx: &InterpCtx,
    prim: &Prim,
    env: &HashMap<Var, Value>,
) -> Result<Value, String> {
    Ok(match prim {
        Prim::Const(c) => match c {
            Const::Int(n) => Value::Int(*n),
            Const::Float(x) => Value::Float(*x),
            Const::Str(s) => Value::Str(Rc::from(s.as_str())),
            Const::Atom(id) => Value::Atom(atom_name(ctx, *id)),
            Const::Nil => Value::Nil,
            Const::True => Value::Bool(true),
            Const::False => Value::Bool(false),
        },
        Prim::BinOp(op, a, b) => {
            let av = env_get(env, *a)?;
            let bv = env_get(env, *b)?;
            eval_binop(*op, &av, &bv)?
        }
        Prim::UnOp(op, x) => {
            let xv = env_get(env, *x)?;
            match (op, &xv) {
                (UnOp::Neg, Value::Int(n)) => Value::Int(-n),
                (UnOp::Neg, Value::Float(f)) => Value::Float(-f),
                (UnOp::Not, Value::Bool(b)) => Value::Bool(!b),
                _ => return Err(format!("bad UnOp {:?} on {:?}", op, kind(&xv))),
            }
        }
        Prim::AllocStruct(_, _) => {
            return Err("AllocStruct: lowering to user-struct alloc lands in .11.7+".into());
        }
        Prim::Builtin(bid, args) => {
            let arg_vals: Vec<Value> = args
                .iter()
                .map(|v| env_get(env, *v))
                .collect::<Result<_, _>>()?;
            let name = builtin_name(ctx, bid.0);
            run_builtin(&name, &arg_vals)?
        }
        Prim::ListCons(h, t) => {
            let hv = env_get(env, *h)?;
            let tv = env_get(env, *t)?;
            list_cons(hv, tv)?
        }
        Prim::ListHead(l) => {
            let lv = env_get(env, *l)?;
            list_head(&lv)?
        }
        Prim::ListTail(l) => {
            let lv = env_get(env, *l)?;
            list_tail(&lv)?
        }
        Prim::ListIsNil(l) => {
            let lv = env_get(env, *l)?;
            Value::Bool(matches!(lv, Value::Nil) || matches!(&lv, Value::List(xs) if xs.is_empty()))
        }
        Prim::MakeTuple(args) => {
            let vs: Vec<Value> = args
                .iter()
                .map(|v| env_get(env, *v))
                .collect::<Result<_, _>>()?;
            Value::Tuple(Rc::new(vs))
        }
        Prim::TupleField(v, i) => {
            let tv = env_get(env, *v)?;
            match tv {
                Value::Tuple(xs) => xs
                    .get(*i as usize)
                    .cloned()
                    .ok_or_else(|| format!("tuple_field {} out of range", i))?,
                other => return Err(format!("tuple_field on non-tuple {:?}", kind(&other))),
            }
        }
        Prim::MakeList(els, tail) => {
            let mut vs: Vec<Value> = els
                .iter()
                .map(|v| env_get(env, *v))
                .collect::<Result<_, _>>()?;
            match tail {
                Some(t) => {
                    let tv = env_get(env, *t)?;
                    let tail_vs = match tv {
                        Value::Nil => vec![],
                        Value::List(xs) => (*xs).clone(),
                        other => {
                            return Err(format!(
                                "list tail must be List or Nil, got {:?}",
                                kind(&other)
                            ));
                        }
                    };
                    vs.extend(tail_vs);
                    Value::List(Rc::new(vs))
                }
                None => Value::List(Rc::new(vs)),
            }
        }
        Prim::MakeClosure(_, _) => {
            // First-class closures require a Value::IrClosure variant; deferred.
            return Err("MakeClosure: IR-level closure value not yet wired".into());
        }
    })
}

fn env_get(env: &HashMap<Var, Value>, v: Var) -> Result<Value, String> {
    env.get(&v).cloned().ok_or_else(|| format!("unbound var {}", v.0))
}

fn list_cons(h: Value, t: Value) -> Result<Value, String> {
    let mut xs = match t {
        Value::Nil => Vec::new(),
        Value::List(xs) => (*xs).clone(),
        other => return Err(format!("cons tail must be List/Nil, got {:?}", kind(&other))),
    };
    xs.insert(0, h);
    Ok(Value::List(Rc::new(xs)))
}

fn list_head(v: &Value) -> Result<Value, String> {
    match v {
        Value::List(xs) if !xs.is_empty() => Ok(xs[0].clone()),
        _ => Err("head of empty/non-list".into()),
    }
}

fn list_tail(v: &Value) -> Result<Value, String> {
    match v {
        Value::List(xs) if !xs.is_empty() => {
            let rest: Vec<Value> = xs[1..].to_vec();
            if rest.is_empty() {
                Ok(Value::Nil)
            } else {
                Ok(Value::List(Rc::new(rest)))
            }
        }
        _ => Err("tail of empty/non-list".into()),
    }
}

fn eval_binop(op: BinOp, a: &Value, b: &Value) -> Result<Value, String> {
    use Value::*;
    Ok(match (op, a, b) {
        (BinOp::Add, Int(x), Int(y)) => Int(x + y),
        (BinOp::Sub, Int(x), Int(y)) => Int(x - y),
        (BinOp::Mul, Int(x), Int(y)) => Int(x * y),
        (BinOp::Div, Int(x), Int(y)) => {
            if *y == 0 {
                return Err("division by zero".into());
            }
            Int(x / y)
        }
        (BinOp::Mod, Int(x), Int(y)) => {
            if *y == 0 {
                return Err("mod by zero".into());
            }
            Int(x % y)
        }
        (BinOp::Add, Float(x), Float(y)) => Float(x + y),
        (BinOp::Sub, Float(x), Float(y)) => Float(x - y),
        (BinOp::Mul, Float(x), Float(y)) => Float(x * y),
        (BinOp::Div, Float(x), Float(y)) => Float(x / y),
        (BinOp::Eq, x, y) => Bool(value_eq(x, y)),
        (BinOp::Neq, x, y) => Bool(!value_eq(x, y)),
        (BinOp::Lt, Int(x), Int(y)) => Bool(x < y),
        (BinOp::Le, Int(x), Int(y)) => Bool(x <= y),
        (BinOp::Gt, Int(x), Int(y)) => Bool(x > y),
        (BinOp::Ge, Int(x), Int(y)) => Bool(x >= y),
        (BinOp::Lt, Float(x), Float(y)) => Bool(x < y),
        (BinOp::Le, Float(x), Float(y)) => Bool(x <= y),
        (BinOp::Gt, Float(x), Float(y)) => Bool(x > y),
        (BinOp::Ge, Float(x), Float(y)) => Bool(x >= y),
        (BinOp::And, Bool(x), Bool(y)) => Bool(*x && *y),
        (BinOp::Or, Bool(x), Bool(y)) => Bool(*x || *y),
        _ => return Err(format!("bad BinOp {:?} on ({:?}, {:?})", op, kind(a), kind(b))),
    })
}

fn value_eq(a: &Value, b: &Value) -> bool {
    use Value::*;
    match (a, b) {
        (Int(x), Int(y)) => x == y,
        (Float(x), Float(y)) => x == y,
        (Bool(x), Bool(y)) => x == y,
        (Nil, Nil) => true,
        (Atom(x), Atom(y)) => &**x == &**y,
        (Str(x), Str(y)) => &**x == &**y,
        (List(x), List(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| value_eq(a, b))
        }
        (Tuple(x), Tuple(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| value_eq(a, b))
        }
        _ => false,
    }
}

fn run_builtin(name: &str, args: &[Value]) -> Result<Value, String> {
    match name {
        "print" => {
            // No-op for tests; real print would write to stdout.
            Ok(Value::Nil)
        }
        "assert" => {
            if args.len() != 1 {
                return Err("assert/1 expected 1 arg".into());
            }
            if is_truthy(&args[0]) {
                Ok(Value::Atom(Rc::from("ok")))
            } else {
                Err("assert failed".into())
            }
        }
        "assert_eq" => {
            if args.len() != 2 {
                return Err("assert_eq/2 expected 2 args".into());
            }
            if value_eq(&args[0], &args[1]) {
                Ok(Value::Atom(Rc::from("ok")))
            } else {
                Err(format!("assert_eq failed: {:?} != {:?}", kind(&args[0]), kind(&args[1])))
            }
        }
        "assert_neq" => {
            if args.len() != 2 {
                return Err("assert_neq/2 expected 2 args".into());
            }
            if !value_eq(&args[0], &args[1]) {
                Ok(Value::Atom(Rc::from("ok")))
            } else {
                Err("assert_neq failed".into())
            }
        }
        other => Err(format!("unknown builtin {}", other)),
    }
}

fn kind(v: &Value) -> &'static str {
    match v {
        Value::Int(_) => "Int",
        Value::Float(_) => "Float",
        Value::Bool(_) => "Bool",
        Value::Nil => "Nil",
        Value::Atom(_) => "Atom",
        Value::Str(_) => "Str",
        Value::List(_) => "List",
        Value::Tuple(_) => "Tuple",
        Value::Vec(_) => "Vec",
        Value::BitStr(_) => "BitStr",
        Value::Map(_) => "Map",
        Value::Closure(_) => "Closure",
        Value::Builtin(_) => "Builtin",
        Value::Jit(_) => "Jit",
        Value::JitPoly(_) => "JitPoly",
    }
}

// Silence unused-import warning when FzMap isn't referenced by any test.
#[allow(dead_code)]
fn _unused_fzmap_import(_: &FzMap) {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinOp as ABinOp, Expr, FnClause, FnDef, Item, Pattern, Program, UnOp as AUnOp};
    use crate::ir_lower::{lower_program, AtomTable, BuiltinTable};
    use std::rc::Rc;

    fn fn_def(name: &str, clauses: Vec<FnClause>) -> Rc<Item> {
        Rc::new(Item::Fn(FnDef {
            name: name.into(),
            clauses,
            is_macro: false,
            doc: None,
        }))
    }

    fn cl(params: Vec<Pattern>, body: Expr) -> FnClause {
        FnClause { params, guard: None, body }
    }

    /// Lower a program and return (module, atom_names, builtin_names) ready
    /// for the IR interp. The atom table after lowering has every interned
    /// atom; the builtin table is the v1 stable set seeded by the lowerer.
    fn lower_for_interp(items: Vec<Rc<Item>>) -> (Module, Vec<String>, Vec<String>) {
        let prog = Program { items };
        let module = lower_program(&prog).expect("lower failed");
        // Re-derive atoms by re-lowering with a peek at the table.
        // (The crate exposes AtomTable but lower_program consumes it; for
        // tests we just need the names that may appear at runtime, which
        // are the standard halt atoms plus any test-specific atoms.)
        // Easiest path: synthesize from a fresh AtomTable used during
        // lowering — we can't access the consumed one, so we run a parallel
        // intern to reconstruct. For these tests we don't observe atoms at
        // runtime, so we leave the names empty and rely on synthetic.
        let _ = AtomTable::default();
        let builtins = vec![
            "print".to_string(),
            "assert".to_string(),
            "assert_eq".to_string(),
            "assert_neq".to_string(),
        ];
        let _ = BuiltinTable::new();
        (module, Vec::new(), builtins)
    }

    fn run_named(items: Vec<Rc<Item>>, name: &str, args: Vec<Value>) -> Result<Value, String> {
        let (module, atoms, builtins) = lower_for_interp(items);
        let f = module.fn_by_name(name).expect("fn not found");
        run_fn_with(&module, f.id, args, &atoms, &builtins)
    }

    #[test]
    fn interp_const_int() {
        let f = fn_def("f", vec![cl(vec![], Expr::Int(42))]);
        let r = run_named(vec![f], "f", vec![]).unwrap();
        assert!(matches!(r, Value::Int(42)));
    }

    #[test]
    fn interp_identity() {
        let f = fn_def(
            "id",
            vec![cl(vec![Pattern::Var("x".into())], Expr::Var("x".into()))],
        );
        let r = run_named(vec![f], "id", vec![Value::Int(7)]).unwrap();
        assert!(matches!(r, Value::Int(7)));
    }

    #[test]
    fn interp_binop_add() {
        let f = fn_def(
            "add1",
            vec![cl(
                vec![Pattern::Var("x".into())],
                Expr::BinOp(
                    ABinOp::Add,
                    Box::new(Expr::Var("x".into())),
                    Box::new(Expr::Int(1)),
                ),
            )],
        );
        let r = run_named(vec![f], "add1", vec![Value::Int(41)]).unwrap();
        assert!(matches!(r, Value::Int(42)));
    }

    #[test]
    fn interp_unop_neg() {
        let f = fn_def(
            "n",
            vec![cl(
                vec![Pattern::Var("x".into())],
                Expr::UnOp(AUnOp::Neg, Box::new(Expr::Var("x".into()))),
            )],
        );
        let r = run_named(vec![f], "n", vec![Value::Int(5)]).unwrap();
        assert!(matches!(r, Value::Int(-5)));
    }

    #[test]
    fn interp_if_then() {
        // fn pos(x), do: if x > 0, do: 1, else: -1
        let f = fn_def(
            "pos",
            vec![cl(
                vec![Pattern::Var("x".into())],
                Expr::If(
                    Box::new(Expr::BinOp(
                        ABinOp::Gt,
                        Box::new(Expr::Var("x".into())),
                        Box::new(Expr::Int(0)),
                    )),
                    Box::new(Expr::Int(1)),
                    Some(Box::new(Expr::UnOp(AUnOp::Neg, Box::new(Expr::Int(1))))),
                ),
            )],
        );
        let r = run_named(vec![f.clone()], "pos", vec![Value::Int(5)]).unwrap();
        assert!(matches!(r, Value::Int(1)));
        let r = run_named(vec![f], "pos", vec![Value::Int(-3)]).unwrap();
        assert!(matches!(r, Value::Int(-1)));
    }

    #[test]
    fn interp_block_returns_last() {
        let f = fn_def(
            "b",
            vec![cl(
                vec![],
                Expr::Block(vec![Expr::Int(1), Expr::Int(2), Expr::Int(3)]),
            )],
        );
        let r = run_named(vec![f], "b", vec![]).unwrap();
        assert!(matches!(r, Value::Int(3)));
    }

    #[test]
    fn interp_tuple_construction_and_field_projection() {
        // fn first({a, b}), do: a
        let f = fn_def(
            "first",
            vec![cl(
                vec![Pattern::Tuple(vec![
                    Pattern::Var("a".into()),
                    Pattern::Var("b".into()),
                ])],
                Expr::Var("a".into()),
            )],
        );
        let t = Value::Tuple(Rc::new(vec![Value::Int(10), Value::Int(20)]));
        let r = run_named(vec![f], "first", vec![t]).unwrap();
        assert!(matches!(r, Value::Int(10)));
    }

    #[test]
    fn interp_list_construction() {
        let f = fn_def(
            "l",
            vec![cl(
                vec![],
                Expr::List(vec![Expr::Int(1), Expr::Int(2), Expr::Int(3)], None),
            )],
        );
        let r = run_named(vec![f], "l", vec![]).unwrap();
        match r {
            Value::List(xs) => {
                let xs = (*xs).clone();
                assert_eq!(xs.len(), 3);
                assert!(matches!(xs[0], Value::Int(1)));
                assert!(matches!(xs[2], Value::Int(3)));
            }
            other => panic!("expected list, got {:?}", super::kind(&other)),
        }
    }

    #[test]
    fn interp_list_head_tail_pattern() {
        // fn first_of([h | _]), do: h
        let f = fn_def(
            "first_of",
            vec![cl(
                vec![Pattern::List(
                    vec![Pattern::Var("h".into())],
                    Some(Box::new(Pattern::Wildcard)),
                )],
                Expr::Var("h".into()),
            )],
        );
        let lst = Value::List(Rc::new(vec![Value::Int(7), Value::Int(8)]));
        let r = run_named(vec![f], "first_of", vec![lst]).unwrap();
        assert!(matches!(r, Value::Int(7)));
    }

    #[test]
    fn interp_multi_clause_factorial() {
        // fn fact(0), do: 1
        // fn fact(n), do: n * fact(n - 1)
        let f = fn_def(
            "fact",
            vec![
                cl(vec![Pattern::Int(0)], Expr::Int(1)),
                cl(
                    vec![Pattern::Var("n".into())],
                    Expr::BinOp(
                        ABinOp::Mul,
                        Box::new(Expr::Var("n".into())),
                        Box::new(Expr::Call(
                            Box::new(Expr::Var("fact".into())),
                            vec![Expr::BinOp(
                                ABinOp::Sub,
                                Box::new(Expr::Var("n".into())),
                                Box::new(Expr::Int(1)),
                            )],
                        )),
                    ),
                ),
            ],
        );
        let r = run_named(vec![f], "fact", vec![Value::Int(5)]).unwrap();
        assert!(matches!(r, Value::Int(120)), "got {:?}", super::kind(&r));
    }

    #[test]
    fn interp_tail_call() {
        // fn caller(x), do: callee(x)
        // fn callee(y), do: y + 1
        let caller = fn_def(
            "caller",
            vec![cl(
                vec![Pattern::Var("x".into())],
                Expr::Call(
                    Box::new(Expr::Var("callee".into())),
                    vec![Expr::Var("x".into())],
                ),
            )],
        );
        let callee = fn_def(
            "callee",
            vec![cl(
                vec![Pattern::Var("y".into())],
                Expr::BinOp(
                    ABinOp::Add,
                    Box::new(Expr::Var("y".into())),
                    Box::new(Expr::Int(1)),
                ),
            )],
        );
        let r = run_named(vec![caller, callee], "caller", vec![Value::Int(41)]).unwrap();
        assert!(matches!(r, Value::Int(42)));
    }

    #[test]
    fn interp_cps_split_call_in_binop() {
        // fn caller(x), do: callee(x) + 10
        // fn callee(y), do: y * 2
        let caller = fn_def(
            "caller",
            vec![cl(
                vec![Pattern::Var("x".into())],
                Expr::BinOp(
                    ABinOp::Add,
                    Box::new(Expr::Call(
                        Box::new(Expr::Var("callee".into())),
                        vec![Expr::Var("x".into())],
                    )),
                    Box::new(Expr::Int(10)),
                ),
            )],
        );
        let callee = fn_def(
            "callee",
            vec![cl(
                vec![Pattern::Var("y".into())],
                Expr::BinOp(
                    ABinOp::Mul,
                    Box::new(Expr::Var("y".into())),
                    Box::new(Expr::Int(2)),
                ),
            )],
        );
        let r = run_named(vec![caller, callee], "caller", vec![Value::Int(5)]).unwrap();
        // callee(5) = 10; + 10 = 20.
        assert!(matches!(r, Value::Int(20)), "got {:?}", super::kind(&r));
    }

    #[test]
    fn interp_recursive_count_down() {
        // fn count(0), do: 0
        // fn count(n), do: count(n - 1)
        let f = fn_def(
            "count",
            vec![
                cl(vec![Pattern::Int(0)], Expr::Int(0)),
                cl(
                    vec![Pattern::Var("n".into())],
                    Expr::Call(
                        Box::new(Expr::Var("count".into())),
                        vec![Expr::BinOp(
                            ABinOp::Sub,
                            Box::new(Expr::Var("n".into())),
                            Box::new(Expr::Int(1)),
                        )],
                    ),
                ),
            ],
        );
        let r = run_named(vec![f], "count", vec![Value::Int(50)]).unwrap();
        assert!(matches!(r, Value::Int(0)));
    }

    #[test]
    fn interp_fib() {
        // fn fib(0), do: 0
        // fn fib(1), do: 1
        // fn fib(n), do: fib(n - 1) + fib(n - 2)
        let f = fn_def(
            "fib",
            vec![
                cl(vec![Pattern::Int(0)], Expr::Int(0)),
                cl(vec![Pattern::Int(1)], Expr::Int(1)),
                cl(
                    vec![Pattern::Var("n".into())],
                    Expr::BinOp(
                        ABinOp::Add,
                        Box::new(Expr::Call(
                            Box::new(Expr::Var("fib".into())),
                            vec![Expr::BinOp(
                                ABinOp::Sub,
                                Box::new(Expr::Var("n".into())),
                                Box::new(Expr::Int(1)),
                            )],
                        )),
                        Box::new(Expr::Call(
                            Box::new(Expr::Var("fib".into())),
                            vec![Expr::BinOp(
                                ABinOp::Sub,
                                Box::new(Expr::Var("n".into())),
                                Box::new(Expr::Int(2)),
                            )],
                        )),
                    ),
                ),
            ],
        );
        let r = run_named(vec![f], "fib", vec![Value::Int(10)]).unwrap();
        assert!(matches!(r, Value::Int(55)), "got {:?}", super::kind(&r));
    }

    #[test]
    fn interp_pattern_match_falls_through() {
        // fn classify(0), do: :zero
        // fn classify(_), do: :other
        let f = fn_def(
            "classify",
            vec![
                cl(vec![Pattern::Int(0)], Expr::Atom("zero".into())),
                cl(vec![Pattern::Wildcard], Expr::Atom("other".into())),
            ],
        );
        // Atom ids are interned in lowering order: function_clause first
        // (the multi-clause fail-block atom), then "zero", then "other".
        let r0 = run_named(vec![f.clone()], "classify", vec![Value::Int(0)]).unwrap();
        let r5 = run_named(vec![f], "classify", vec![Value::Int(5)]).unwrap();
        match (&r0, &r5) {
            (Value::Atom(a), Value::Atom(b)) => {
                assert_ne!(&**a, &**b, "two clauses should return distinct atoms");
                assert_eq!(&**a, "atom_1");
                assert_eq!(&**b, "atom_2");
            }
            _ => panic!("expected atoms, got {:?} / {:?}", super::kind(&r0), super::kind(&r5)),
        }
    }

    #[test]
    fn interp_builtin_assert_eq_passes() {
        // fn t(), do: assert_eq(1 + 1, 2)
        let f = fn_def(
            "t",
            vec![cl(
                vec![],
                Expr::Call(
                    Box::new(Expr::Var("assert_eq".into())),
                    vec![
                        Expr::BinOp(
                            ABinOp::Add,
                            Box::new(Expr::Int(1)),
                            Box::new(Expr::Int(1)),
                        ),
                        Expr::Int(2),
                    ],
                ),
            )],
        );
        let r = run_named(vec![f], "t", vec![]).unwrap();
        match r {
            Value::Atom(s) => assert_eq!(&*s, "ok"),
            other => panic!("got {:?}", super::kind(&other)),
        }
    }

    #[test]
    fn interp_builtin_assert_eq_fails() {
        let f = fn_def(
            "t",
            vec![cl(
                vec![],
                Expr::Call(
                    Box::new(Expr::Var("assert_eq".into())),
                    vec![Expr::Int(1), Expr::Int(2)],
                ),
            )],
        );
        let err = run_named(vec![f], "t", vec![]).unwrap_err();
        assert!(err.contains("assert_eq failed"));
    }
}
