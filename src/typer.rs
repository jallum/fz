//! Pure helpers over `ast::Pattern` / `ast::Expr` that feed the set-theoretic
//! algebra in `crate::types`. The AST-walking inference driver lived here until
//! fz-ul4.11.24.1 — it was retired ahead of the IR-shaped reintegration arc
//! (fz-ul4.11.24.2-.7). What survives is the shape-level glue: pattern → Descr,
//! pattern bindings, projection helpers, map-key conversion, list/map field
//! lookup, the widening operator for fixed-point termination, and the AST
//! self-call predicate. None of these reach into pipeline state.
//!
//! Design choices preserved from the original driver, in case they need
//! revisiting when the IR-shaped driver lands:
//!
//! - **Pattern types are over-approximated** when a scrutinee is a union of
//!   tuple/list shapes (`pattern_bindings` falls back to `any` for a variable
//!   bound under a union scrutinee). Single-shape scrutinees give precise
//!   per-component types.
//!
//! - **Widening at K=3** is the termination guard for fixed-point inference
//!   over recursive functions — singleton-type lattices have infinite
//!   ascending chains, so growing literal-set axes (ints/floats/strs) widen
//!   to their tops once iteration depth crosses the threshold. The `widen`
//!   function applies it; callers decide when.

use crate::ast::*;
use crate::types::*;

// ----------------------------------------------------------------------
// AST walking helpers
// ----------------------------------------------------------------------

/// True if `e` syntactically contains a call to `name` (as `name(...)`).
/// Used by the inference driver to decide whether a clause needs the
/// self-narrowed snapshot pass.
pub fn expr_calls_self(e: &Expr, name: &str) -> bool {
    match e {
        Expr::Call(callee, args) => {
            if let Expr::Var(n) = &**callee {
                if n == name { return true; }
            }
            expr_calls_self(callee, name) || args.iter().any(|a| expr_calls_self(a, name))
        }
        Expr::BinOp(_, l, r) => expr_calls_self(l, name) || expr_calls_self(r, name),
        Expr::UnOp(_, x) => expr_calls_self(x, name),
        Expr::If(c, t, els) => expr_calls_self(c, name)
            || expr_calls_self(t, name)
            || els.as_deref().is_some_and(|e| expr_calls_self(e, name)),
        Expr::Case(s, cls) => expr_calls_self(s, name)
            || cls.iter().any(|c| expr_calls_self(&c.body, name)
                || c.guard.as_ref().is_some_and(|g| expr_calls_self(g, name))),
        Expr::Cond(arms) => arms.iter().any(|(c, b)| expr_calls_self(c, name) || expr_calls_self(b, name)),
        Expr::With(bindings, body, els) => {
            bindings.iter().any(|b| match b {
                WithBinding::Match(_, e) | WithBinding::Bare(e) => expr_calls_self(e, name),
            }) || expr_calls_self(body, name)
                || els.iter().any(|c| expr_calls_self(&c.body, name))
        }
        Expr::Match(_, rhs) => expr_calls_self(rhs, name),
        Expr::Block(es) => es.iter().any(|e| expr_calls_self(e, name)),
        Expr::Lambda(_, body) => expr_calls_self(body, name),
        Expr::List(es, tail) => es.iter().any(|e| expr_calls_self(e, name))
            || tail.as_deref().is_some_and(|e| expr_calls_self(e, name)),
        Expr::Tuple(es) => es.iter().any(|e| expr_calls_self(e, name)),
        Expr::VecLit(_, es) => es.iter().any(|e| expr_calls_self(e, name)),
        Expr::Bitstring(fields) => fields.iter().any(|f| expr_calls_self(&f.value, name)),
        Expr::Map(pairs) => pairs.iter().any(|(k, v)| expr_calls_self(k, name) || expr_calls_self(v, name)),
        Expr::MapUpdate(b, pairs) => expr_calls_self(b, name)
            || pairs.iter().any(|(k, v)| expr_calls_self(k, name) || expr_calls_self(v, name)),
        Expr::Index(t, k) => expr_calls_self(t, name) || expr_calls_self(k, name),
        Expr::Dot(e, _) => expr_calls_self(e, name),
        _ => false,
    }
}

// ----------------------------------------------------------------------
// Patterns
// ----------------------------------------------------------------------

pub fn pattern_type(p: &Pattern) -> Descr {
    match p {
        Pattern::Wildcard => Descr::any(),
        Pattern::Var(_) => Descr::any(),
        Pattern::Int(n) => Descr::int_lit(*n),
        Pattern::Float(f) => Descr::float_lit(*f),
        Pattern::Str(s) => Descr::str_lit(s.clone()),
        Pattern::Atom(a) => Descr::atom_lit(a.clone()),
        Pattern::Bool(_) => Descr::bool_t(),
        Pattern::Nil => Descr::nil(),
        Pattern::Tuple(ps) => Descr::tuple_of(ps.iter().map(pattern_type).collect::<Vec<_>>()),
        Pattern::List(heads, _tail) => {
            let elem = if heads.is_empty() {
                Descr::any()
            } else {
                heads.iter().fold(Descr::none(), |acc, p| acc.union(&pattern_type(p)))
            };
            Descr::list_of(elem)
        }
        Pattern::As(_, inner) => pattern_type(inner),
        Pattern::Map(pairs) => {
            let mut fields = std::collections::BTreeMap::new();
            for (kp, vp) in pairs {
                if let Some(mk) = pattern_to_map_key(kp) {
                    fields.insert(mk, pattern_type(vp));
                }
            }
            if fields.is_empty() { Descr::map_top() } else { Descr::map_of(fields) }
        }
        Pattern::Bitstring(_) => Descr::vec_u8().union(&Descr::vec_bit()),
    }
}

pub fn pattern_bindings(p: &Pattern, scrut: &Descr) -> Vec<(String, Descr)> {
    let mut out = Vec::new();
    extract(p, scrut, &mut out);
    out
}

fn extract(p: &Pattern, scrut: &Descr, out: &mut Vec<(String, Descr)>) {
    match p {
        Pattern::Var(n) => out.push((n.clone(), scrut.clone())),
        Pattern::As(n, inner) => {
            out.push((n.clone(), scrut.clone()));
            extract(inner, scrut, out);
        }
        Pattern::Tuple(ps) => {
            let comps = tuple_projections(scrut, ps.len());
            for (i, p) in ps.iter().enumerate() {
                extract(p, &comps[i], out);
            }
        }
        Pattern::List(heads, tail) => {
            let elem = list_element_type(scrut);
            for h in heads { extract(h, &elem, out); }
            if let Some(t) = tail { extract(t, scrut, out); }
        }
        Pattern::Bitstring(fields) => {
            for f in fields {
                let scrut_for_field = match f.spec.ty {
                    BitType::Integer | BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => Descr::int(),
                    BitType::Float => Descr::float(),
                    BitType::Binary => Descr::vec_u8(),
                    BitType::Bits => Descr::vec_u8().union(&Descr::vec_bit()),
                };
                extract(&f.value, &scrut_for_field, out);
            }
        }
        Pattern::Map(pairs) => {
            for (kp, vp) in pairs {
                let val_t = if let Some(mk) = pattern_to_map_key(kp) {
                    map_field_lookup(scrut, &mk).unwrap_or_else(Descr::any)
                } else {
                    Descr::any()
                };
                extract(vp, &val_t, out);
            }
        }
        _ => {} // literals, wildcard, etc., bind nothing.
    }
}

/// Project the i-th component of any positive tuple shape in `scrut` of the
/// given arity, unioning across multiple shapes. Falls back to `any` when
/// no matching tuple shape is present.
pub fn tuple_projections(scrut: &Descr, arity: usize) -> Vec<Descr> {
    let mut comps = vec![Descr::none(); arity];
    let mut found = false;
    for clause in &scrut.tuples {
        for sig in &clause.pos {
            if sig.elems.len() == arity {
                for i in 0..arity { comps[i] = comps[i].union(&sig.elems[i]); }
                found = true;
            }
        }
    }
    if !found { return vec![Descr::any(); arity]; }
    comps
}

// ----------------------------------------------------------------------
// Map helpers
// ----------------------------------------------------------------------

pub fn expr_to_map_key(e: &Expr) -> Option<MapKey> {
    Some(match e {
        Expr::Atom(a) => MapKey::Atom(a.clone()),
        Expr::Int(n) => MapKey::Int(*n),
        Expr::Str(s) => MapKey::Str(s.clone()),
        Expr::Bool(b) => MapKey::Bool(*b),
        Expr::Nil => MapKey::Nil,
        _ => return None,
    })
}

pub fn pattern_to_map_key(p: &Pattern) -> Option<MapKey> {
    Some(match p {
        Pattern::Atom(a) => MapKey::Atom(a.clone()),
        Pattern::Int(n) => MapKey::Int(*n),
        Pattern::Str(s) => MapKey::Str(s.clone()),
        Pattern::Bool(b) => MapKey::Bool(*b),
        Pattern::Nil => MapKey::Nil,
        _ => return None,
    })
}

/// Look up the value type for `key` across all positive map shapes in `d`.
/// Returns `None` if `d` has no map shapes (call site decides the fallback).
pub fn map_field_lookup(d: &Descr, key: &MapKey) -> Option<Descr> {
    let mut found = false;
    let mut acc = Descr::none();
    for clause in &d.maps {
        for sig in &clause.pos {
            found = true;
            // Open shape: if key is required, contribute its type; otherwise
            // the key may or may not be present so contribute `any | nil`.
            if let Some(t) = sig.fields.get(key) {
                acc = acc.union(t);
            } else {
                acc = acc.union(&Descr::any()).union(&Descr::nil());
            }
        }
        if clause.pos.is_empty() {
            // Top map clause — any map, any key value.
            acc = acc.union(&Descr::any()).union(&Descr::nil());
            found = true;
        }
    }
    if !found { None } else { Some(acc) }
}

/// Refine `d` by setting field `key` to value type `vt` in every positive map
/// shape. Used by map update typing.
pub fn refine_map_field(d: &Descr, key: &MapKey, vt: &Descr) -> Descr {
    let mut out = d.clone();
    for clause in &mut out.maps {
        for sig in &mut clause.pos {
            sig.fields.insert(key.clone(), vt.clone());
        }
        if clause.pos.is_empty() {
            // Top map: can't refine without manufacturing a shape; skip.
        }
    }
    out
}

/// Element type of a list-typed descriptor. Falls back to `any`.
pub fn list_element_type(scrut: &Descr) -> Descr {
    let mut elem = Descr::none();
    let mut found = false;
    for clause in &scrut.lists {
        for sig in &clause.pos {
            elem = elem.union(&sig.elem);
            found = true;
        }
    }
    if !found { Descr::any() } else { elem }
}

// ----------------------------------------------------------------------
// Widening (for fixed-point termination)
// ----------------------------------------------------------------------

/// Widen any growing literal-set axes to their tops. Recursively applied to
/// structural element types so arrow returns / list elements / tuple
/// components also widen.
pub fn widen(d: &Descr) -> Descr {
    let mut out = d.clone();
    if !out.ints.is_none() && !out.ints.is_any() { out.ints = IntSet::any(); }
    if !out.floats.is_none() && !out.floats.is_any() { out.floats = FloatSet::any(); }
    if !out.strs.is_none() && !out.strs.is_any() { out.strs = StrSet::any(); }
    out.tuples = out.tuples.into_iter().map(widen_tuple).collect();
    out.lists  = out.lists.into_iter().map(widen_list).collect();
    out.funcs  = out.funcs.into_iter().map(widen_func).collect();
    out.maps   = out.maps.into_iter().map(widen_map).collect();
    out
}
fn widen_map_sig(s: MapSig) -> MapSig {
    MapSig { fields: s.fields.into_iter().map(|(k, v)| (k, widen(&v))).collect() }
}
fn widen_map(c: Conj<MapSig>) -> Conj<MapSig> {
    Conj { pos: c.pos.into_iter().map(widen_map_sig).collect(),
           neg: c.neg.into_iter().map(widen_map_sig).collect() }
}
fn widen_tuple(c: Conj<TupleSig>) -> Conj<TupleSig> {
    Conj {
        pos: c.pos.into_iter().map(|s| TupleSig { elems: s.elems.iter().map(widen).collect() }).collect(),
        neg: c.neg.into_iter().map(|s| TupleSig { elems: s.elems.iter().map(widen).collect() }).collect(),
    }
}
fn widen_list(c: Conj<ListSig>) -> Conj<ListSig> {
    Conj {
        pos: c.pos.into_iter().map(|s| ListSig { elem: Box::new(widen(&s.elem)) }).collect(),
        neg: c.neg.into_iter().map(|s| ListSig { elem: Box::new(widen(&s.elem)) }).collect(),
    }
}
fn widen_func(c: Conj<ArrowSig>) -> Conj<ArrowSig> {
    let widen_sig = |s: ArrowSig| ArrowSig {
        args: s.args.iter().map(widen).collect(),
        ret: Box::new(widen(&s.ret)),
    };
    Conj { pos: c.pos.into_iter().map(widen_sig).collect(),
           neg: c.neg.into_iter().map(widen_sig).collect() }
}
