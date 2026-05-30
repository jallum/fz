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
    /// fz-axu.26 (M5) — byte-backed. Mirrors `Expr::Binary`/`Pattern::Binary`,
    /// which carry raw bytes since L2. Print decodes lossily; equality
    /// compares slices.
    Binary(Rc<[u8]>),
    /// Opaque reference produced by REPL/eval `make_ref/0`.
    Ref(u64),
    Nil,
    List(Rc<Vec<Value>>),
    Tuple(Rc<Vec<Value>>),
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
}

#[derive(Clone)]
pub struct FzMap {
    /// Insertion-ordered. Equality and `get` walk linearly using `value_eq`.
    pub entries: Vec<(Value, Value)>,
}

impl FzMap {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }
    pub fn get(&self, key: &Value) -> Option<&Value> {
        self.entries
            .iter()
            .find(|(k, _)| value_eq(k, key))
            .map(|(_, v)| v)
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
}

#[derive(Clone)]
pub struct BitString {
    pub bytes: Vec<u8>, // MSB-first packed
    pub bit_len: usize,
}

pub struct Closure {
    pub name: Option<String>,
    pub clauses: Vec<FnClause>,
    pub env: Env,
    /// `@doc "..."` attached to this fn at definition. `None` for
    /// lambdas and undocumented top-level fns. Surfaces in REPL `?name`.
    pub doc: Option<String>,
    /// fz-ul4.31.6 — pre-formatted `@spec` for REPL `?name`. `None`
    /// when no `@spec` was declared or when resolution of the spec body
    /// against the module's `@type` env failed at load time (validation
    /// would surface that as a `spec/violation` diagnostic).
    pub spec_text: Option<String>,
}

pub struct Builtin {
    pub name: &'static str,
    pub arity: usize,
    pub func: BuiltinFn,
}

/// Builtins receive a callback to apply higher-order functions back into the interpreter.
/// This avoids needing the interpreter as a thread-local while still letting `vec_map`
/// etc. invoke user closures.
pub type BuiltinFn =
    fn(&[Value], &dyn Fn(&Value, Vec<Value>) -> Result<Value, String>) -> Result<Value, String>;

/// Environments are linked frames; lookups walk the chain.
/// Cheap to clone (Rc), cheap to extend (push a new frame).
#[derive(Clone)]
pub struct Env(Rc<EnvNode>);

enum EnvNode {
    Empty,
    Frame {
        bindings: RefCell<Vec<(String, Value)>>,
        parent: Env,
    },
}

impl Env {
    pub fn empty() -> Self {
        Env(Rc::new(EnvNode::Empty))
    }

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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Float(x) => {
                if x.fract() == 0.0 && x.is_finite() {
                    write!(f, "{:.1}", x)
                } else {
                    write!(f, "{}", x)
                }
            }
            Value::Bool(b) => write!(f, "{}", b),
            Value::Atom(a) => write!(f, ":{}", a),
            Value::Binary(bytes) => {
                if is_printable_utf8(bytes) {
                    let s = std::str::from_utf8(bytes).expect("checked by is_printable_utf8");
                    write!(f, "{:?}", s)
                } else {
                    write!(f, "<<")?;
                    for (i, b) in bytes.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", b)?;
                    }
                    write!(f, ">>")
                }
            }
            Value::Ref(id) => write!(f, "#Ref<{}>", id),
            Value::Nil => write!(f, "nil"),
            Value::List(xs) => {
                write!(f, "[")?;
                for (i, v) in xs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Value::Tuple(xs) => {
                write!(f, "{{")?;
                for (i, v) in xs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "}}")
            }
            Value::Map(m) => {
                write!(f, "%{{")?;
                for (i, (k, v)) in m.entries.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
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
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", b)?;
                }
                write!(f, " :: {} bits>>", bs.bit_len)
            }
            Value::Closure(c) => write!(
                f,
                "#fn<{}/{}>",
                c.name.as_deref().unwrap_or("anon"),
                c.clauses.first().map(|cl| cl.params.len()).unwrap_or(0)
            ),
            Value::Builtin(b) => write!(f, "#builtin<{}/{}>", b.name, b.arity),
        }
    }
}

fn is_printable_utf8(bytes: &[u8]) -> bool {
    std::str::from_utf8(bytes)
        .map(|s| s.chars().all(|c| !c.is_control()))
        .unwrap_or(false)
}

/// A pattern usable as a map key must reduce to a concrete value (atom, int,
/// str, etc.). Variables and structural patterns are rejected — Elixir has the
/// same restriction.
fn pattern_to_value(p: &Pattern) -> Option<Value> {
    Some(match p {
        Pattern::Atom(a) => Value::Atom(Rc::from(a.as_str())),
        Pattern::Int(n) => Value::Int(*n),
        Pattern::Float(f) => Value::Float(*f),
        Pattern::Binary(bytes) => Value::Binary(Rc::from(bytes.as_slice())),
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
        (Binary(x), Binary(y)) => x.as_ref() == y.as_ref(),
        (Ref(x), Ref(y)) => x == y,
        (Nil, Nil) => true,
        (List(x), List(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| value_eq(a, b))
        }
        (Tuple(x), Tuple(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| value_eq(a, b))
        }
        (Map(x), Map(y)) => {
            x.entries.len() == y.entries.len()
                && x.entries
                    .iter()
                    .all(|(k, v)| matches!(y.get(k), Some(yv) if value_eq(v, yv)))
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
        (Pattern::Var(n), v) => {
            env.bind(n, v.clone());
            true
        }
        (Pattern::Int(a), Value::Int(b)) => a == b,
        (Pattern::Float(a), Value::Float(b)) => a == b,
        (Pattern::Binary(a), Value::Binary(b)) => a.as_slice() == b.as_ref(),
        (Pattern::Atom(a), Value::Atom(b)) => a.as_str() == b.as_ref(),
        (Pattern::Bool(a), Value::Bool(b)) => a == b,
        (Pattern::Nil, Value::Nil) => true,
        (Pattern::Tuple(ps), Value::Tuple(xs)) => {
            ps.len() == xs.len()
                && ps
                    .iter()
                    .zip(xs.iter())
                    .all(|(p, v)| match_pattern(&p.node, v, env))
        }
        (Pattern::List(heads, tail), Value::List(xs)) => {
            if let Some(tail_pat) = tail {
                if xs.len() < heads.len() {
                    return false;
                }
                for (p, v) in heads.iter().zip(xs.iter()) {
                    if !match_pattern(&p.node, v, env) {
                        return false;
                    }
                }
                let rest: Vec<Value> = xs[heads.len()..].to_vec();
                match_pattern(&tail_pat.node, &Value::List(Rc::new(rest)), env)
            } else {
                if heads.len() != xs.len() {
                    return false;
                }
                heads
                    .iter()
                    .zip(xs.iter())
                    .all(|(p, v)| match_pattern(&p.node, v, env))
            }
        }
        (Pattern::As(name, inner), v) => {
            env.bind(name, v.clone());
            match_pattern(&inner.node, v, env)
        }
        (Pattern::Bitstring(fields), v) => crate::exec::bitstr::match_bitstring(fields, v, env),
        (Pattern::Map(pairs), Value::Map(m)) => {
            for (kp, vp) in pairs {
                let key = match pattern_to_value(&kp.node) {
                    Some(k) => k,
                    None => return false,
                };
                let Some(actual) = m.get(&key) else {
                    return false;
                };
                if !match_pattern(&vp.node, actual, env) {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binary_display_keeps_textual_utf8_quoted() {
        let value = Value::Binary(Rc::from(&b"hello"[..]));
        assert_eq!(format!("{}", value), "\"hello\"");
    }

    #[test]
    fn binary_display_uses_byte_list_for_control_bytes() {
        let value = Value::Binary(Rc::from(&[1_u8, 2, 65][..]));
        assert_eq!(format!("{}", value), "<<1, 2, 65>>");
    }
}
