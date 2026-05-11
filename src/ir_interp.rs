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

use crate::ast::{BitType, Endian, VecKind};
use crate::bitstr::{
    apply_endian_for_read, decode_utf16, decode_utf32, decode_utf8, encode_utf16, encode_utf32,
    encode_utf8, sign_extend, BitReader, BitWriter,
};
use crate::fz_ir::{
    BinOp, BitFieldIr, BitSizeIr, Const, FnId, Module, Prim, Stmt, Term, UnOp, Var,
};
use crate::value::{BitVec, FzMap, FzVec, IrClosure, Value};
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
            Term::CallClosure { closure, args, continuation } => {
                let cv = env_get(&env, *closure)?;
                let (lam_fn, captured) = match cv {
                    Value::IrClosure(c) => (FnId(c.fn_id), c.captured.clone()),
                    other => return Err(format!("call_closure on non-closure {:?}", kind(&other))),
                };
                let mut call_args = captured;
                call_args.extend(collect_vals(&env, args)?);
                let result = run(ctx, lam_fn, call_args)?;
                let cap_vals = collect_vals(&env, &continuation.captured)?;
                let mut cont_args = vec![result];
                cont_args.extend(cap_vals);
                return run(ctx, continuation.fn_id, cont_args);
            }
            Term::TailCallClosure { closure, args } => {
                let cv = env_get(&env, *closure)?;
                let (lam_fn, captured) = match cv {
                    Value::IrClosure(c) => (FnId(c.fn_id), c.captured.clone()),
                    other => return Err(format!(
                        "tail_call_closure on non-closure {:?}",
                        kind(&other)
                    )),
                };
                let mut call_args = captured;
                call_args.extend(collect_vals(&env, args)?);
                return run(ctx, lam_fn, call_args);
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
        Prim::MakeClosure(fn_id, captured_vars) => {
            let captured: Vec<Value> = captured_vars
                .iter()
                .map(|v| env_get(env, *v))
                .collect::<Result<_, _>>()?;
            Value::IrClosure(Rc::new(IrClosure { fn_id: fn_id.0, captured }))
        }
        Prim::MakeMap(entries) => {
            let mut m = FzMap::new();
            for (k, v) in entries {
                let kv = env_get(env, *k)?;
                let vv = env_get(env, *v)?;
                m = m.put(kv, vv);
            }
            Value::Map(Rc::new(m))
        }
        Prim::MapUpdate(base, entries) => {
            let bv = env_get(env, *base)?;
            let mut m = match bv {
                Value::Map(m) => (*m).clone(),
                other => return Err(format!("map_update on non-map {:?}", kind(&other))),
            };
            for (k, v) in entries {
                let kv = env_get(env, *k)?;
                let vv = env_get(env, *v)?;
                if !m.has(&kv) {
                    return Err(format!("map_update: key not present"));
                }
                m = m.put(kv, vv);
            }
            Value::Map(Rc::new(m))
        }
        Prim::MapGet(m, k) => {
            let mv = env_get(env, *m)?;
            let kv = env_get(env, *k)?;
            match mv {
                Value::Map(m) => m.get(&kv).cloned().unwrap_or(Value::Nil),
                other => return Err(format!("map_get on non-map {:?}", kind(&other))),
            }
        }
        Prim::MakeVec(kind_ir, els) => {
            use crate::ast::VecKind;
            use crate::fz_ir::VecKindIr;
            let vs: Vec<Value> = els.iter().map(|v| env_get(env, *v)).collect::<Result<_, _>>()?;
            // ir_interp builds via ast::VecKind sigil; collapse the per-element
            // bifurcation back to the AST-level shape.
            let ast_kind = match kind_ir {
                VecKindIr::I64 | VecKindIr::F64 => VecKind::Numeric,
                VecKindIr::U8 => VecKind::Bytes,
                VecKindIr::Bit => VecKind::Bits,
            };
            build_vec(ast_kind, vs)?
        }
        Prim::MakeBitstring(fields) => build_bitstring(env, fields)?,
        Prim::BitReaderInit(v) => {
            let sv = env_get(env, *v)?;
            reader_init(&sv)?
        }
        Prim::BitReadField { reader, ty, size, endian, signed, unit, is_last } => {
            let r = env_get(env, *reader)?;
            let size_resolved = match resolve_size_ir(env, size)? {
                Some(s) => Some(s),
                None => default_size_for(*ty),
            };
            read_field(&r, *ty, size_resolved, resolved_unit_for(*ty, *unit), *endian, *signed, *is_last)
        }
        Prim::BitReaderDone(r) => {
            let rv = env_get(env, *r)?;
            Value::Bool(reader_pos(&rv)? == reader_bit_len(&rv)?)
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
        Value::IrClosure(_) => "IrClosure",
    }
}

// Silence unused-import warning when FzMap isn't referenced by any test.
#[allow(dead_code)]
fn _unused_fzmap_import(_: &FzMap) {}

// ----------------------------------------------------------------------
// Vec / Bitstring helpers
// ----------------------------------------------------------------------

fn build_vec(kind: VecKind, vs: Vec<Value>) -> Result<Value, String> {
    match kind {
        VecKind::Numeric => {
            let all_int = vs.iter().all(|v| matches!(v, Value::Int(_)));
            let any_float = vs.iter().any(|v| matches!(v, Value::Float(_)));
            if any_float {
                let xs: Vec<f64> = vs
                    .iter()
                    .map(|v| match v {
                        Value::Float(x) => Ok(*x),
                        Value::Int(n) => Ok(*n as f64),
                        other => Err(format!("vec(numeric): expected number, got {:?}", kind_v(other))),
                    })
                    .collect::<Result<_, _>>()?;
                Ok(Value::Vec(FzVec::F64(Rc::new(xs))))
            } else if all_int {
                let xs: Vec<i64> = vs.iter().map(|v| if let Value::Int(n) = v { *n } else { 0 }).collect();
                Ok(Value::Vec(FzVec::I64(Rc::new(xs))))
            } else {
                Err("vec(numeric): expected ints or floats".into())
            }
        }
        VecKind::Bytes => {
            let xs: Vec<u8> = vs
                .iter()
                .map(|v| match v {
                    Value::Int(n) if *n >= 0 && *n <= 255 => Ok(*n as u8),
                    other => Err(format!("vec(bytes): expected 0..=255, got {:?}", kind_v(other))),
                })
                .collect::<Result<_, _>>()?;
            Ok(Value::Vec(FzVec::U8(Rc::new(xs))))
        }
        VecKind::Bits => {
            let xs: Vec<u8> = vs
                .iter()
                .map(|v| match v {
                    Value::Int(n) if *n == 0 || *n == 1 => Ok(*n as u8),
                    other => Err(format!("vec(bits): expected 0 or 1, got {:?}", kind_v(other))),
                })
                .collect::<Result<_, _>>()?;
            Ok(Value::Vec(FzVec::Bit(Rc::new(BitVec::from_bits(&xs)))))
        }
    }
}

fn kind_v(v: &Value) -> &'static str { kind(v) }

fn resolve_size_ir(env: &HashMap<Var, Value>, size: &Option<BitSizeIr>) -> Result<Option<u32>, String> {
    match size {
        Some(BitSizeIr::Literal(n)) => Ok(Some(*n)),
        Some(BitSizeIr::Var(v)) => match env_get(env, *v)? {
            Value::Int(n) if n >= 0 => Ok(Some(n as u32)),
            other => Err(format!("bit size must be non-negative int, got {:?}", kind(&other))),
        },
        None => Ok(None),
    }
}

fn default_size_for(ty: BitType) -> Option<u32> {
    match ty {
        BitType::Integer => Some(8),
        BitType::Float => Some(64),
        BitType::Binary | BitType::Bits => None,
        BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => None,
    }
}

fn resolved_unit_for(ty: BitType, unit: Option<u32>) -> u32 {
    if let Some(u) = unit { return u; }
    match ty {
        BitType::Integer | BitType::Float | BitType::Bits => 1,
        BitType::Binary => 8,
        BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => 1,
    }
}

fn build_bitstring(env: &HashMap<Var, Value>, fields: &[BitFieldIr]) -> Result<Value, String> {
    let mut writer = BitWriter::new();
    for f in fields {
        let unit = resolved_unit_for(f.ty, f.unit);
        let size = match resolve_size_ir(env, &f.size)? {
            Some(s) => Some(s),
            None => default_size_for(f.ty),
        };
        let val = env_get(env, f.value)?;
        encode_field_ir(&val, f.ty, size, unit, f.endian, f.signed, &mut writer)?;
    }
    Ok(writer.finalize())
}

fn encode_field_ir(
    value: &Value,
    ty: BitType,
    size: Option<u32>,
    unit: u32,
    endian: Endian,
    _signed: bool,
    writer: &mut BitWriter,
) -> Result<(), String> {
    match ty {
        BitType::Integer => {
            let n = match value {
                Value::Int(n) => *n,
                _ => return Err("integer bit field expects int".into()),
            };
            let total = size.unwrap_or(8) * unit;
            if total > 64 { return Err(format!("integer field too wide: {}", total)); }
            let masked = if total < 64 { (n as u64) & ((1u64 << total) - 1) } else { n as u64 };
            let bswap = crate::bitstr::apply_endian_for_write(masked, total, endian);
            writer.write_bits(bswap, total as usize);
            Ok(())
        }
        BitType::Float => {
            let f = match value {
                Value::Float(f) => *f,
                Value::Int(n) => *n as f64,
                _ => return Err("float bit field expects number".into()),
            };
            let total = size.unwrap_or(64) * unit;
            let bits = match total {
                32 => (f as f32).to_bits() as u64,
                64 => f.to_bits(),
                _ => return Err(format!("float field size must be 32 or 64, got {}", total)),
            };
            let bswap = crate::bitstr::apply_endian_for_write(bits, total, endian);
            writer.write_bits(bswap, total as usize);
            Ok(())
        }
        BitType::Binary => {
            let bytes = match value {
                Value::Vec(FzVec::U8(b)) => b.clone(),
                _ => return Err("binary bit field expects byte-vector".into()),
            };
            let total_bits = match size {
                None => bytes.len() * 8,
                Some(n) => (n * unit) as usize,
            };
            if total_bits > bytes.len() * 8 {
                return Err(format!("binary field exceeds available bits"));
            }
            if total_bits % 8 == 0 && writer.bit_len % 8 == 0 {
                writer.bytes.extend_from_slice(&bytes[..total_bits / 8]);
                writer.bit_len += total_bits;
            } else {
                let mut r = BitReader { bytes: &bytes, bit_len: bytes.len() * 8, pos: 0 };
                for _ in 0..total_bits {
                    writer.append_bit(r.read_bit().unwrap());
                }
            }
            Ok(())
        }
        BitType::Bits => {
            let (bytes, bit_len): (Vec<u8>, usize) = match value {
                Value::Vec(FzVec::U8(b)) => ((**b).clone(), b.len() * 8),
                Value::BitStr(bs) => (bs.bytes.clone(), bs.bit_len),
                _ => return Err("bits field expects bitstring".into()),
            };
            let total_bits = match size {
                None => bit_len,
                Some(n) => (n * unit) as usize,
            };
            if total_bits > bit_len { return Err("bits field exceeds available".into()); }
            let mut r = BitReader { bytes: &bytes, bit_len, pos: 0 };
            for _ in 0..total_bits {
                writer.append_bit(r.read_bit().unwrap());
            }
            Ok(())
        }
        BitType::Utf8 => {
            let cp = codepoint_v(value)?;
            let bytes = encode_utf8(cp).ok_or_else(|| format!("invalid codepoint: {}", cp))?;
            writer.write_bytes(&bytes);
            Ok(())
        }
        BitType::Utf16 => {
            let cp = codepoint_v(value)?;
            let bytes = encode_utf16(cp, endian).ok_or_else(|| format!("invalid codepoint: {}", cp))?;
            writer.write_bytes(&bytes);
            Ok(())
        }
        BitType::Utf32 => {
            let cp = codepoint_v(value)?;
            let bytes = encode_utf32(cp, endian).ok_or_else(|| format!("invalid codepoint: {}", cp))?;
            writer.write_bytes(&bytes);
            Ok(())
        }
    }
}

fn codepoint_v(v: &Value) -> Result<u32, String> {
    match v {
        Value::Int(n) if *n >= 0 && *n <= 0x10ffff => Ok(*n as u32),
        _ => Err("expected codepoint".into()),
    }
}

// Reader is modelled as a Tuple([Vec(U8), Int(bit_len), Int(pos)]). Persistent —
// each read produces a new reader value with the position advanced.

fn reader_init(v: &Value) -> Result<Value, String> {
    let (bytes, bit_len): (Rc<Vec<u8>>, usize) = match v {
        Value::Vec(FzVec::U8(b)) => (b.clone(), b.len() * 8),
        Value::BitStr(bs) => (Rc::new(bs.bytes.clone()), bs.bit_len),
        other => return Err(format!("bit_reader_init on non-bitstring {:?}", kind(other))),
    };
    Ok(Value::Tuple(Rc::new(vec![
        Value::Vec(FzVec::U8(bytes)),
        Value::Int(bit_len as i64),
        Value::Int(0),
    ])))
}

fn reader_parts(v: &Value) -> Result<(Rc<Vec<u8>>, usize, usize), String> {
    let xs = match v {
        Value::Tuple(xs) => xs,
        other => return Err(format!("expected reader, got {:?}", kind(other))),
    };
    if xs.len() != 3 {
        return Err("reader tuple has wrong shape".into());
    }
    let bytes = match &xs[0] {
        Value::Vec(FzVec::U8(b)) => b.clone(),
        _ => return Err("reader bytes slot wrong".into()),
    };
    let bit_len = match &xs[1] { Value::Int(n) => *n as usize, _ => return Err("reader bit_len".into()) };
    let pos = match &xs[2] { Value::Int(n) => *n as usize, _ => return Err("reader pos".into()) };
    Ok((bytes, bit_len, pos))
}

fn reader_pos(v: &Value) -> Result<usize, String> { reader_parts(v).map(|(_, _, p)| p) }
fn reader_bit_len(v: &Value) -> Result<usize, String> { reader_parts(v).map(|(_, b, _)| b) }

fn make_reader(bytes: Rc<Vec<u8>>, bit_len: usize, pos: usize) -> Value {
    Value::Tuple(Rc::new(vec![
        Value::Vec(FzVec::U8(bytes)),
        Value::Int(bit_len as i64),
        Value::Int(pos as i64),
    ]))
}

/// Read one field from the reader, returning Tuple([ok, extracted, new_reader])
/// on success or Tuple([false]) on failure.
fn read_field(
    reader_val: &Value,
    ty: BitType,
    size: Option<u32>,
    unit: u32,
    endian: Endian,
    signed: bool,
    is_last: bool,
) -> Value {
    let (bytes, bit_len, pos) = match reader_parts(reader_val) {
        Ok(p) => p,
        Err(_) => return Value::Tuple(Rc::new(vec![Value::Bool(false)])),
    };
    let mut r = BitReader { bytes: &bytes, bit_len, pos };
    let extracted: Value = match ty {
        BitType::Integer => {
            let total = size.unwrap_or(8) * unit;
            if total > 64 { return Value::Tuple(Rc::new(vec![Value::Bool(false)])); }
            let raw = match r.read_bits(total as usize) {
                Some(v) => v,
                None => return Value::Tuple(Rc::new(vec![Value::Bool(false)])),
            };
            let raw = apply_endian_for_read(raw, total, endian);
            let n = if signed { sign_extend(raw, total) } else { raw as i64 };
            Value::Int(n)
        }
        BitType::Float => {
            let total = size.unwrap_or(64) * unit;
            let raw = match r.read_bits(total as usize) {
                Some(v) => v,
                None => return Value::Tuple(Rc::new(vec![Value::Bool(false)])),
            };
            let raw = apply_endian_for_read(raw, total, endian);
            let fv = match total {
                32 => f32::from_bits(raw as u32) as f64,
                64 => f64::from_bits(raw),
                _ => return Value::Tuple(Rc::new(vec![Value::Bool(false)])),
            };
            Value::Float(fv)
        }
        BitType::Binary => {
            let n_bits = match size {
                None => {
                    if !is_last { return Value::Tuple(Rc::new(vec![Value::Bool(false)])); }
                    r.remaining()
                }
                Some(n) => (n * unit) as usize,
            };
            if n_bits % 8 != 0 { return Value::Tuple(Rc::new(vec![Value::Bool(false)])); }
            match r.take_bits(n_bits) {
                Some(v) => v,
                None => return Value::Tuple(Rc::new(vec![Value::Bool(false)])),
            }
        }
        BitType::Bits => {
            let n_bits = match size {
                None => {
                    if !is_last { return Value::Tuple(Rc::new(vec![Value::Bool(false)])); }
                    r.remaining()
                }
                Some(n) => (n * unit) as usize,
            };
            match r.take_bits(n_bits) {
                Some(v) => v,
                None => return Value::Tuple(Rc::new(vec![Value::Bool(false)])),
            }
        }
        BitType::Utf8 => match decode_utf8(&mut r) {
            Some(c) => Value::Int(c as i64),
            None => return Value::Tuple(Rc::new(vec![Value::Bool(false)])),
        },
        BitType::Utf16 => match decode_utf16(&mut r, endian) {
            Some(c) => Value::Int(c as i64),
            None => return Value::Tuple(Rc::new(vec![Value::Bool(false)])),
        },
        BitType::Utf32 => match decode_utf32(&mut r, endian) {
            Some(c) => Value::Int(c as i64),
            None => return Value::Tuple(Rc::new(vec![Value::Bool(false)])),
        },
    };
    let new_pos = r.pos;
    let new_reader = make_reader(bytes, bit_len, new_pos);
    Value::Tuple(Rc::new(vec![Value::Bool(true), extracted, new_reader]))
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use std::rc::Rc;

    fn lower_for_interp(src: &str) -> (Module, Vec<String>, Vec<String>) {
        use crate::ir_lower::lower_program_full;
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let (module, atoms, _builtins) = lower_program_full(&prog).expect("lower failed");
        let builtins = vec![
            "print".to_string(),
            "assert".to_string(),
            "assert_eq".to_string(),
            "assert_neq".to_string(),
        ];
        (module, atoms.names(), builtins)
    }

    fn run_named(src: &str, name: &str, args: Vec<Value>) -> Result<Value, String> {
        let (module, atoms, builtins) = lower_for_interp(src);
        let f = module.fn_by_name(name).expect("fn not found");
        run_fn_with(&module, f.id, args, &atoms, &builtins)
    }

    #[test]
    fn interp_const_int() {
        let r = run_named("fn f(), do: 42", "f", vec![]).unwrap();
        assert!(matches!(r, Value::Int(42)));
    }

    #[test]
    fn interp_identity() {
        let r = run_named("fn id(x), do: x", "id", vec![Value::Int(7)]).unwrap();
        assert!(matches!(r, Value::Int(7)));
    }

    #[test]
    fn interp_binop_add() {
        let r = run_named("fn add1(x), do: x + 1", "add1", vec![Value::Int(41)]).unwrap();
        assert!(matches!(r, Value::Int(42)));
    }

    #[test]
    fn interp_unop_neg() {
        let r = run_named("fn n(x), do: -x", "n", vec![Value::Int(5)]).unwrap();
        assert!(matches!(r, Value::Int(-5)));
    }

    #[test]
    fn interp_if_then() {
        let src = "fn pos(x), do: if x > 0, do: 1, else: -1";
        let r = run_named(src, "pos", vec![Value::Int(5)]).unwrap();
        assert!(matches!(r, Value::Int(1)));
        let r = run_named(src, "pos", vec![Value::Int(-3)]).unwrap();
        assert!(matches!(r, Value::Int(-1)));
    }

    #[test]
    fn interp_block_returns_last() {
        let r = run_named("fn b() do\n  1\n  2\n  3\nend", "b", vec![]).unwrap();
        assert!(matches!(r, Value::Int(3)));
    }

    #[test]
    fn interp_tuple_construction_and_field_projection() {
        let t = Value::Tuple(Rc::new(vec![Value::Int(10), Value::Int(20)]));
        let r = run_named("fn first({a, b}), do: a", "first", vec![t]).unwrap();
        assert!(matches!(r, Value::Int(10)));
    }

    #[test]
    fn interp_list_construction() {
        let r = run_named("fn l(), do: [1, 2, 3]", "l", vec![]).unwrap();
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
        let lst = Value::List(Rc::new(vec![Value::Int(7), Value::Int(8)]));
        let r = run_named("fn first_of([h | _]), do: h", "first_of", vec![lst]).unwrap();
        assert!(matches!(r, Value::Int(7)));
    }

    #[test]
    fn interp_multi_clause_factorial() {
        let src = "fn fact(0), do: 1\nfn fact(n), do: n * fact(n - 1)";
        let r = run_named(src, "fact", vec![Value::Int(5)]).unwrap();
        assert!(matches!(r, Value::Int(120)), "got {:?}", super::kind(&r));
    }

    #[test]
    fn interp_tail_call() {
        let src = "fn caller(x), do: callee(x)\nfn callee(y), do: y + 1";
        let r = run_named(src, "caller", vec![Value::Int(41)]).unwrap();
        assert!(matches!(r, Value::Int(42)));
    }

    #[test]
    fn interp_cps_split_call_in_binop() {
        let src = "fn caller(x), do: callee(x) + 10\nfn callee(y), do: y * 2";
        let r = run_named(src, "caller", vec![Value::Int(5)]).unwrap();
        // callee(5) = 10; + 10 = 20.
        assert!(matches!(r, Value::Int(20)), "got {:?}", super::kind(&r));
    }

    #[test]
    fn interp_recursive_count_down() {
        let src = "fn count(0), do: 0\nfn count(n), do: count(n - 1)";
        let r = run_named(src, "count", vec![Value::Int(50)]).unwrap();
        assert!(matches!(r, Value::Int(0)));
    }

    #[test]
    fn interp_fib() {
        let src = r#"
fn fib(0), do: 0
fn fib(1), do: 1
fn fib(n), do: fib(n - 1) + fib(n - 2)
"#;
        let r = run_named(src, "fib", vec![Value::Int(10)]).unwrap();
        assert!(matches!(r, Value::Int(55)), "got {:?}", super::kind(&r));
    }

    #[test]
    fn interp_pattern_match_falls_through() {
        let src = "fn classify(0), do: :zero\nfn classify(_), do: :other";
        let r0 = run_named(src, "classify", vec![Value::Int(0)]).unwrap();
        let r5 = run_named(src, "classify", vec![Value::Int(5)]).unwrap();
        match (&r0, &r5) {
            (Value::Atom(a), Value::Atom(b)) => {
                assert_ne!(&**a, &**b, "two clauses should return distinct atoms");
                assert_eq!(&**a, "zero");
                assert_eq!(&**b, "other");
            }
            _ => panic!("expected atoms, got {:?} / {:?}", super::kind(&r0), super::kind(&r5)),
        }
    }

    #[test]
    fn interp_builtin_assert_eq_passes() {
        let r = run_named("fn t(), do: assert_eq(1 + 1, 2)", "t", vec![]).unwrap();
        match r {
            Value::Atom(s) => assert_eq!(&*s, "ok"),
            other => panic!("got {:?}", super::kind(&other)),
        }
    }

    #[test]
    fn interp_closure_construction() {
        let r = run_named("fn mk(), do: fn(y) -> y + 1", "mk", vec![]).unwrap();
        match r {
            Value::IrClosure(c) => assert!(c.captured.is_empty()),
            other => panic!("expected IrClosure, got {:?}", super::kind(&other)),
        }
    }

    #[test]
    fn interp_closure_captures_and_invokes() {
        let src = r#"
fn mk(x), do: fn(y) -> x + y
fn use_it(x, y) do
  f = mk(x)
  f(y)
end
"#;
        let r = run_named(src, "use_it", vec![Value::Int(10), Value::Int(32)]).unwrap();
        assert!(matches!(r, Value::Int(42)), "got {:?}", super::kind(&r));
    }

    // ----- fz-ul4.11.17 coverage: VecLit / Map / MapUpdate / Index / Case / Cond / With / Bitstring -----

    #[test]
    fn interp_vec_numeric_int() {
        let r = run_named("fn v(), do: ~v[1, 2, 3]", "v", vec![]).unwrap();
        match r {
            Value::Vec(super::FzVec::I64(xs)) => assert_eq!(&*xs, &[1, 2, 3]),
            other => panic!("got {:?}", super::kind(&other)),
        }
    }

    #[test]
    fn interp_vec_bytes() {
        let r = run_named("fn v(), do: ~b[255, 0]", "v", vec![]).unwrap();
        match r {
            Value::Vec(super::FzVec::U8(xs)) => assert_eq!(&*xs, &[255, 0]),
            other => panic!("got {:?}", super::kind(&other)),
        }
    }

    #[test]
    fn interp_vec_bits() {
        let r = run_named("fn v(), do: ~bits[1, 0, 1]", "v", vec![]).unwrap();
        match r {
            Value::Vec(super::FzVec::Bit(b)) => {
                assert_eq!(b.len, 3);
                assert_eq!(b.get(0), 1);
                assert_eq!(b.get(1), 0);
                assert_eq!(b.get(2), 1);
            }
            other => panic!("got {:?}", super::kind(&other)),
        }
    }

    #[test]
    fn interp_map_construction_and_lookup() {
        let r = run_named("fn m(), do: %{k: 7}[:k]", "m", vec![]).unwrap();
        assert!(matches!(r, Value::Int(7)));
    }

    #[test]
    fn interp_index_returns_nil_when_absent() {
        let r = run_named("fn m(), do: %{k: 7}[:missing]", "m", vec![]).unwrap();
        assert!(matches!(r, Value::Nil));
    }

    #[test]
    fn interp_map_update() {
        let r = run_named("fn u(), do: %{%{k: 1} | k: 2}[:k]", "u", vec![]).unwrap();
        assert!(matches!(r, Value::Int(2)));
    }

    #[test]
    fn interp_map_pattern_extracts_value() {
        let mut entries = FzMap::new();
        entries = entries.put(Value::Atom(Rc::from("name")), Value::Int(42));
        let r = run_named("fn first(%{name: n}), do: n", "first", vec![Value::Map(Rc::new(entries))]).unwrap();
        assert!(matches!(r, Value::Int(42)));
    }

    #[test]
    fn interp_case_dispatch() {
        let src = r#"
fn c(x) do
  case x do
    0 -> :zero
    _ -> :other
  end
end
"#;
        let r0 = run_named(src, "c", vec![Value::Int(0)]).unwrap();
        let r5 = run_named(src, "c", vec![Value::Int(5)]).unwrap();
        match (&r0, &r5) {
            (Value::Atom(a), Value::Atom(b)) => {
                assert_eq!(&**a, "zero");
                assert_eq!(&**b, "other");
            }
            _ => panic!("expected atoms"),
        }
    }

    #[test]
    fn interp_cond_first_truthy_wins() {
        let src = r#"
fn c(x) do
  cond do
    x > 0 -> :pos
    true -> :nonpos
  end
end
"#;
        let r = run_named(src, "c", vec![Value::Int(10)]).unwrap();
        if let Value::Atom(a) = r { assert_eq!(&*a, "pos"); } else { panic!(); }
        let r = run_named(src, "c", vec![Value::Int(-1)]).unwrap();
        if let Value::Atom(a) = r { assert_eq!(&*a, "nonpos"); } else { panic!(); }
    }

    #[test]
    fn interp_with_success_threads_bindings() {
        let r = run_named("fn w() do\n  with {:ok, a} <- {:ok, 41}, do: a + 1\nend", "w", vec![]).unwrap();
        assert!(matches!(r, Value::Int(42)));
    }

    #[test]
    fn interp_with_else_handles_failure() {
        let src = r#"
fn w() do
  with {:ok, _} <- {:error, :boom} do
    :unreached
  else
    {:error, m} -> {:handled, m}
  end
end
"#;
        let r = run_named(src, "w", vec![]).unwrap();
        match r {
            Value::Tuple(xs) => {
                assert_eq!(xs.len(), 2);
                if let Value::Atom(a) = &xs[0] { assert_eq!(&**a, "handled"); } else { panic!(); }
                if let Value::Atom(a) = &xs[1] { assert_eq!(&**a, "boom"); } else { panic!(); }
            }
            other => panic!("got {:?}", super::kind(&other)),
        }
    }

    #[test]
    fn interp_bitstring_round_trip_simple() {
        let r = run_named("fn b(), do: <<0xA5>>", "b", vec![]).unwrap();
        match r {
            Value::Vec(super::FzVec::U8(b)) => assert_eq!(&*b, &[0xA5]),
            other => panic!("got {:?}", super::kind(&other)),
        }
    }

    #[test]
    fn interp_bitstring_pattern_extracts_int() {
        let bs = Value::Vec(super::FzVec::U8(Rc::new(vec![10, 32])));
        let r = run_named("fn parse(<<a, b>>), do: a + b", "parse", vec![bs]).unwrap();
        assert!(matches!(r, Value::Int(42)));
    }

    #[test]
    fn interp_bitstring_pattern_with_size_var() {
        // <<3, "abc">> = [3, 'a', 'b', 'c']
        let bs = Value::Vec(super::FzVec::U8(Rc::new(vec![3, b'a', b'b', b'c'])));
        let r = run_named(
            "fn parse(<<n, payload::binary-size(n)>>), do: payload",
            "parse",
            vec![bs],
        ).unwrap();
        match r {
            Value::Vec(super::FzVec::U8(b)) => assert_eq!(&*b, &[b'a', b'b', b'c']),
            other => panic!("got {:?}", super::kind(&other)),
        }
    }

    #[test]
    fn interp_builtin_assert_eq_fails() {
        let err = run_named("fn t(), do: assert_eq(1, 2)", "t", vec![]).unwrap_err();
        assert!(err.contains("assert_eq failed"));
    }
}
