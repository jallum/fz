//! Set-theoretic shape helpers consumed by `ir_typer`. The AST-walking
//! inference driver was retired by fz-ul4.11.24.1; the AST-shaped pattern /
//! expression orphans were pruned by fz-ul4.11.25.2. What survives:
//!
//! - tuple / list projection helpers (used by IR pattern narrowing)
//! - map field lookup / refinement
//! - widening operator for fixed-point termination (used by
//!   `ir_typer::specialize_return` per fz-ul4.11.24.7).

use crate::types::*;

// ----------------------------------------------------------------------
// Tuple / list projection helpers
// ----------------------------------------------------------------------

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

/// Look up the value type for `key` across all positive map shapes in `d`.
/// Returns `None` if `d` has no map shapes (call site decides the fallback).
pub fn map_field_lookup(d: &Descr, key: &MapKey) -> Option<Descr> {
    let mut found = false;
    let mut acc = Descr::none();
    for clause in &d.maps {
        for sig in &clause.pos {
            found = true;
            if let Some(t) = sig.fields.get(key) {
                acc = acc.union(t);
            } else {
                acc = acc.union(&Descr::any()).union(&Descr::nil());
            }
        }
        if clause.pos.is_empty() {
            acc = acc.union(&Descr::any()).union(&Descr::nil());
            found = true;
        }
    }
    if !found { None } else { Some(acc) }
}

pub fn refine_map_field(d: &Descr, key: &MapKey, vt: &Descr) -> Descr {
    let mut out = d.clone();
    for clause in &mut out.maps {
        for sig in &mut clause.pos {
            sig.fields.insert(key.clone(), vt.clone());
        }
    }
    out
}

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
