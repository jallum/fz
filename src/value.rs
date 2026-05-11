use crate::ast::{FnClause, Pattern};
use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

#[derive(Clone)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Atom(Rc<str>),
    Str(Rc<str>),
    Nil,
    List(Rc<Vec<Value>>),
    Tuple(Rc<Vec<Value>>),
    Vec(FzVec),
    /// Non-byte-aligned bitstring. Byte-aligned bitstrings produced by `<<...>>`
    /// expressions promote to `Value::Vec(FzVec::U8(...))` instead.
    /// Bits are packed MSB-first within each byte (network/big-endian layout).
    BitStr(Rc<BitString>),
    /// Insertion-ordered map. Linear lookup is fine at the sizes maps are used
    /// for in v0; we'll swap to a hashed representation when profiles say so.
    Map(Rc<FzMap>),
    /// User-defined function: ordered clauses + captured environment.
    /// Multi-clause dispatch happens at call time.
    Closure(Rc<Closure>),
    /// Built-in (host) function.
    Builtin(Rc<Builtin>),
    /// IR-level closure: a Lambda lowered through fz-IR. Carries the IR FnId
    /// (raw u32) of the lambda body and the captured environment slots. Only
    /// used by the fz-IR interpreter (.11.5); the AST interp and JIT path
    /// continue to use Value::Closure.
    IrClosure(Rc<IrClosure>),
}

#[derive(Clone)]
pub struct IrClosure {
    pub fn_id: u32,
    pub captured: Vec<Value>,
}

#[derive(Clone)]
pub struct FzMap {
    /// Insertion-ordered. Equality and `get` walk linearly using `value_eq`.
    pub entries: Vec<(Value, Value)>,
}

impl FzMap {
    pub fn new() -> Self { Self { entries: Vec::new() } }
    pub fn get(&self, key: &Value) -> Option<&Value> {
        self.entries.iter().find(|(k, _)| value_eq(k, key)).map(|(_, v)| v)
    }
    pub fn put(&self, key: Value, val: Value) -> Self {
        let mut entries = self.entries.clone();
        if let Some(slot) = entries.iter_mut().find(|(k, _)| value_eq(k, &key)) {
            slot.1 = val;
        } else {
            entries.push((key, val));
        }
        FzMap { entries }
    }
    pub fn has(&self, key: &Value) -> bool { self.get(key).is_some() }
}

#[derive(Clone)]
pub struct BitString {
    pub bytes: Vec<u8>,    // MSB-first packed
    pub bit_len: usize,
}

/// Monotyped contiguous storage. The point of this type: SIMD-friendly,
/// O(1) indexed, and homogeneous so codegen can specialize element ops.
#[derive(Clone)]
pub enum FzVec {
    I64(Rc<Vec<i64>>),
    F64(Rc<Vec<f64>>),
    U8(Rc<Vec<u8>>),
    Bit(Rc<BitVec>),
}

#[derive(Clone)]
pub struct BitVec {
    pub words: Vec<u64>,
    pub len: usize,
}

impl BitVec {
    pub fn from_bits(bits: &[u8]) -> Self {
        let n = bits.len();
        let mut words = vec![0u64; (n + 63) / 64];
        for (i, b) in bits.iter().enumerate() {
            if *b != 0 { words[i / 64] |= 1u64 << (i % 64); }
        }
        BitVec { words, len: n }
    }
    pub fn get(&self, i: usize) -> u8 {
        ((self.words[i / 64] >> (i % 64)) & 1) as u8
    }
}

impl FzVec {
    pub fn len(&self) -> usize {
        match self {
            FzVec::I64(v) => v.len(),
            FzVec::F64(v) => v.len(),
            FzVec::U8(v)  => v.len(),
            FzVec::Bit(v) => v.len,
        }
    }
    pub fn get(&self, i: usize) -> Option<Value> {
        Some(match self {
            FzVec::I64(v) => Value::Int(*v.get(i)?),
            FzVec::F64(v) => Value::Float(*v.get(i)?),
            FzVec::U8(v)  => Value::Int(*v.get(i)? as i64),
            FzVec::Bit(v) => if i < v.len { Value::Int(v.get(i) as i64) } else { return None; },
        })
    }
}

pub struct Closure {
    pub name: Option<String>,
    pub clauses: Vec<FnClause>,
    pub env: Env,
}

pub struct Builtin {
    pub name: &'static str,
    pub arity: usize,
    pub func: BuiltinFn,
}

/// Builtins receive a callback to apply higher-order functions back into the interpreter.
/// This avoids needing the interpreter as a thread-local while still letting `vec_map`
/// etc. invoke user closures.
pub type BuiltinFn = fn(&[Value], &dyn Fn(&Value, Vec<Value>) -> Result<Value, String>) -> Result<Value, String>;

/// Environments are linked frames; lookups walk the chain.
/// Cheap to clone (Rc), cheap to extend (push a new frame).
#[derive(Clone)]
pub struct Env(Rc<EnvNode>);

enum EnvNode {
    Empty,
    Frame { bindings: RefCell<Vec<(String, Value)>>, parent: Env },
}

impl Env {
    pub fn empty() -> Self { Env(Rc::new(EnvNode::Empty)) }

    pub fn child(&self) -> Self {
        Env(Rc::new(EnvNode::Frame {
            bindings: RefCell::new(Vec::new()),
            parent: self.clone(),
        }))
    }

    pub fn bind(&self, name: &str, v: Value) {
        match &*self.0 {
            EnvNode::Empty => panic!("cannot bind into empty env"),
            EnvNode::Frame { bindings, .. } => bindings.borrow_mut().push((name.to_string(), v)),
        }
    }

    pub fn lookup(&self, name: &str) -> Option<Value> {
        let mut cur = self.clone();
        loop {
            let next = match &*cur.0 {
                EnvNode::Empty => return None,
                EnvNode::Frame { bindings, parent } => {
                    if let Some((_, v)) = bindings.borrow().iter().rev().find(|(n, _)| n == name) {
                        return Some(v.clone());
                    }
                    parent.clone()
                }
            };
            cur = next;
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self) }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Float(x) => {
                if x.fract() == 0.0 && x.is_finite() { write!(f, "{:.1}", x) }
                else { write!(f, "{}", x) }
            }
            Value::Bool(b) => write!(f, "{}", b),
            Value::Atom(a) => write!(f, ":{}", a),
            Value::Str(s) => write!(f, "{:?}", s),
            Value::Nil => write!(f, "nil"),
            Value::List(xs) => {
                write!(f, "[")?;
                for (i, v) in xs.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Value::Tuple(xs) => {
                write!(f, "{{")?;
                for (i, v) in xs.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", v)?;
                }
                write!(f, "}}")
            }
            Value::Vec(v) => {
                write!(f, "~{}[", match v {
                    FzVec::I64(_) | FzVec::F64(_) => "v",
                    FzVec::U8(_)  => "b",
                    FzVec::Bit(_) => "bits",
                })?;
                let n = v.len();
                for i in 0..n {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", v.get(i).unwrap())?;
                }
                write!(f, "]")
            }
            Value::Map(m) => {
                write!(f, "%{{")?;
                for (i, (k, v)) in m.entries.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    match k {
                        Value::Atom(a) => write!(f, "{}: {}", a, v)?,
                        _ => write!(f, "{} => {}", k, v)?,
                    }
                }
                write!(f, "}}")
            }
            Value::BitStr(bs) => {
                // Show as "<< b1, b2, ... :: N-bit total >>" — printable but
                // not a valid surface form (we don't have a non-aligned literal).
                write!(f, "<<")?;
                for (i, b) in bs.bytes.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", b)?;
                }
                write!(f, " :: {} bits>>", bs.bit_len)
            }
            Value::Closure(c) => write!(f, "#fn<{}/{}>",
                c.name.as_deref().unwrap_or("anon"),
                c.clauses.first().map(|cl| cl.params.len()).unwrap_or(0)),
            Value::Builtin(b) => write!(f, "#builtin<{}/{}>", b.name, b.arity),
            Value::IrClosure(c) => {
                write!(f, "#ir_closure<fn{}/cap{}>", c.fn_id, c.captured.len())
            }
        }
    }
}

/// A pattern usable as a map key must reduce to a concrete value (atom, int,
/// str, etc.). Variables and structural patterns are rejected — Elixir has the
/// same restriction.
fn pattern_to_value(p: &Pattern) -> Option<Value> {
    Some(match p {
        Pattern::Atom(a) => Value::Atom(Rc::from(a.as_str())),
        Pattern::Int(n) => Value::Int(*n),
        Pattern::Float(f) => Value::Float(*f),
        Pattern::Str(s) => Value::Str(Rc::from(s.as_str())),
        Pattern::Bool(b) => Value::Bool(*b),
        Pattern::Nil => Value::Nil,
        _ => return None,
    })
}

/// Structural equality on values. NaN floats compare unequal (IEEE).
pub fn value_eq(a: &Value, b: &Value) -> bool {
    use Value::*;
    match (a, b) {
        (Int(x), Int(y)) => x == y,
        (Float(x), Float(y)) => x == y,
        (Bool(x), Bool(y)) => x == y,
        (Atom(x), Atom(y)) => x.as_ref() == y.as_ref(),
        (Str(x), Str(y))   => x.as_ref() == y.as_ref(),
        (Nil, Nil) => true,
        (List(x), List(y)) => x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| value_eq(a, b)),
        (Tuple(x), Tuple(y)) => x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| value_eq(a, b)),
        (Map(x), Map(y)) => {
            x.entries.len() == y.entries.len()
                && x.entries.iter().all(|(k, v)| matches!(y.get(k), Some(yv) if value_eq(v, yv)))
        }
        _ => false,
    }
}

/// Try to bind `pat` against `v`, pushing matched names into `env`.
/// Returns true on success (env may have been mutated even on partial fail —
/// callers must use a fresh frame).
pub fn match_pattern(pat: &Pattern, v: &Value, env: &Env) -> bool {
    match (pat, v) {
        (Pattern::Wildcard, _) => true,
        (Pattern::Var(n), v) => { env.bind(n, v.clone()); true }
        (Pattern::Int(a), Value::Int(b)) => a == b,
        (Pattern::Float(a), Value::Float(b)) => a == b,
        (Pattern::Str(a), Value::Str(b)) => a.as_str() == b.as_ref(),
        (Pattern::Atom(a), Value::Atom(b)) => a.as_str() == b.as_ref(),
        (Pattern::Bool(a), Value::Bool(b)) => a == b,
        (Pattern::Nil, Value::Nil) => true,
        (Pattern::Tuple(ps), Value::Tuple(xs)) => {
            ps.len() == xs.len() && ps.iter().zip(xs.iter()).all(|(p, v)| match_pattern(&p.node, v, env))
        }
        (Pattern::List(heads, tail), Value::List(xs)) => {
            if let Some(tail_pat) = tail {
                if xs.len() < heads.len() { return false; }
                for (p, v) in heads.iter().zip(xs.iter()) {
                    if !match_pattern(&p.node, v, env) { return false; }
                }
                let rest: Vec<Value> = xs[heads.len()..].to_vec();
                match_pattern(&tail_pat.node, &Value::List(Rc::new(rest)), env)
            } else {
                if heads.len() != xs.len() { return false; }
                heads.iter().zip(xs.iter()).all(|(p, v)| match_pattern(&p.node, v, env))
            }
        }
        (Pattern::As(name, inner), v) => {
            env.bind(name, v.clone());
            match_pattern(&inner.node, v, env)
        }
        (Pattern::Bitstring(fields), v) => {
            crate::bitstr::match_bitstring(fields, v, env)
        }
        (Pattern::Map(pairs), Value::Map(m)) => {
            for (kp, vp) in pairs {
                let key = match pattern_to_value(&kp.node) {
                    Some(k) => k,
                    None => return false,
                };
                let Some(actual) = m.get(&key) else { return false };
                if !match_pattern(&vp.node, actual, env) { return false; }
            }
            true
        }
        _ => false,
    }
}
