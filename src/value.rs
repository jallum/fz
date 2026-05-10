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
    /// User-defined function: ordered clauses + captured environment.
    /// Multi-clause dispatch happens at call time.
    Closure(Rc<Closure>),
    /// Built-in (host) function.
    Builtin(Rc<Builtin>),
}

#[derive(Clone)]
pub struct BitString {
    pub bytes: Vec<u8>,    // MSB-first packed
    pub bit_len: usize,
}

impl BitString {
    pub fn empty() -> Self { Self { bytes: Vec::new(), bit_len: 0 } }
    pub fn from_bytes(b: Vec<u8>) -> Self {
        let n = b.len();
        Self { bytes: b, bit_len: n * 8 }
    }
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
    pub fn kind_str(&self) -> &'static str {
        match self {
            FzVec::I64(_) => "i64",
            FzVec::F64(_) => "f64",
            FzVec::U8(_)  => "u8",
            FzVec::Bit(_) => "bit",
        }
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
        }
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
            ps.len() == xs.len() && ps.iter().zip(xs.iter()).all(|(p, v)| match_pattern(p, v, env))
        }
        (Pattern::List(heads, tail), Value::List(xs)) => {
            if let Some(tail_pat) = tail {
                if xs.len() < heads.len() { return false; }
                for (p, v) in heads.iter().zip(xs.iter()) {
                    if !match_pattern(p, v, env) { return false; }
                }
                let rest: Vec<Value> = xs[heads.len()..].to_vec();
                match_pattern(tail_pat, &Value::List(Rc::new(rest)), env)
            } else {
                if heads.len() != xs.len() { return false; }
                heads.iter().zip(xs.iter()).all(|(p, v)| match_pattern(p, v, env))
            }
        }
        (Pattern::As(name, inner), v) => {
            env.bind(name, v.clone());
            match_pattern(inner, v, env)
        }
        (Pattern::Bitstring(fields), v) => {
            crate::bitstr::match_bitstring(fields, v, env)
        }
        _ => false,
    }
}
