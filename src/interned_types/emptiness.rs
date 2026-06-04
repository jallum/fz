//! Per-axis emptiness algorithms for the interned descriptor kernel.

use std::collections::{BTreeMap, HashSet};

use crate::types::MapKey;

use super::conj::Conj;
use super::descr::Descr;
use super::sigs::{ArrowSig, ClosureLit, ListSig, MapSig, ResourceSig, TupleSig};
use super::TyCtx;

#[derive(Default)]
pub(crate) struct Memo {
    pub(super) in_flight: HashSet<Descr>,
}

pub(crate) fn tuple_clause_empty(cx: TyCtx<'_>, c: &Conj<TupleSig>, memo: &mut Memo) -> bool {
    if c.pos.is_empty() {
        return false;
    }
    let arity = c.pos[0].elems.len();
    if c.pos.iter().any(|p| p.elems.len() != arity) {
        return true;
    }
    let mut t: Vec<Descr> = c.pos[0].elems.iter().map(|ty| cx.descr(ty).clone()).collect();
    for p in &c.pos[1..] {
        for (i, e) in p.elems.iter().enumerate() {
            t[i] = t[i].intersect(cx.descr(e));
        }
    }
    let negs: Vec<Vec<Descr>> = c
        .neg
        .iter()
        .filter(|n| n.elems.len() == arity)
        .map(|n| n.elems.iter().map(|ty| cx.descr(ty).clone()).collect())
        .collect();
    phi_tuple(cx, &t, &negs, memo)
}

fn phi_tuple(cx: TyCtx<'_>, t: &[Descr], n: &[Vec<Descr>], memo: &mut Memo) -> bool {
    if n.is_empty() {
        return t.iter().any(|d| d.is_empty_memo(cx, memo));
    }
    let head = &n[0];
    let rest = &n[1..];
    for i in 0..t.len() {
        let mut t_split = t.to_vec();
        for j in 0..i {
            t_split[j] = t_split[j].intersect(&head[j]);
        }
        t_split[i] = t_split[i].diff(&head[i]);
        if !phi_tuple(cx, &t_split, rest, memo) {
            return false;
        }
    }
    true
}

pub(crate) fn list_clause_empty(cx: TyCtx<'_>, c: &Conj<ListSig>, memo: &mut Memo) -> bool {
    let (empty, t) = if c.pos.is_empty() {
        (true, Some(Descr::any()))
    } else {
        let mut empty = true;
        let mut t: Option<Descr> = None;
        for p in &c.pos {
            empty &= p.empty;
            t = match (t, p.elem) {
                (None, None) => None,
                (None, Some(elem)) => Some(cx.descr(&elem).clone()),
                (Some(prev), None) => Some(prev),
                (Some(prev), Some(elem)) => {
                    let next = prev.intersect(cx.descr(&elem));
                    if next.is_empty_memo(cx, memo) {
                        None
                    } else {
                        Some(next)
                    }
                }
            };
        }
        (empty, t)
    };
    if !empty && t.is_none() {
        return true;
    }
    if c.neg.is_empty() {
        return false;
    }
    let empty_covered = !empty || c.neg.iter().any(|n| n.empty);
    let non_empty_covered = match t {
        None => true,
        Some(ref t) => c.neg.iter().any(|n| {
            n.elem
                .is_some_and(|elem| t.diff(cx.descr(&elem)).is_empty_memo(cx, memo))
        }),
    };
    empty_covered && non_empty_covered
}

pub(crate) fn resource_clause_empty(cx: TyCtx<'_>, c: &Conj<ResourceSig>, memo: &mut Memo) -> bool {
    let payload = if c.pos.is_empty() {
        Descr::any()
    } else {
        let mut payload = cx.descr(&c.pos[0].payload).clone();
        for p in &c.pos[1..] {
            payload = payload.intersect(cx.descr(&p.payload));
        }
        if payload.is_empty_memo(cx, memo) {
            return true;
        }
        payload
    };
    if c.neg.is_empty() {
        return false;
    }
    c.neg
        .iter()
        .any(|n| payload.diff(cx.descr(&n.payload)).is_empty_memo(cx, memo))
}

fn arrow_input(sig: &ArrowSig) -> Descr {
    Descr::tuple_of(sig.args.clone())
}

pub(crate) fn func_clause_empty(cx: TyCtx<'_>, c: &Conj<ArrowSig>, memo: &mut Memo) -> bool {
    let p = &c.pos;
    let n = &c.neg;

    let pos_lits: Vec<&ClosureLit> = p.iter().filter_map(|s| s.lit.as_ref()).collect();
    for i in 0..pos_lits.len() {
        for j in (i + 1)..pos_lits.len() {
            if pos_lits[i].fn_id != pos_lits[j].fn_id || pos_lits[i].captures.len() != pos_lits[j].captures.len() {
                return true;
            }
            for (a, b) in pos_lits[i].captures.iter().zip(&pos_lits[j].captures) {
                if cx.descr(a).intersect(cx.descr(b)).is_empty_memo(cx, memo) {
                    return true;
                }
            }
        }
    }

    'next_neg_lit: for negj in n {
        let Some(neg_lit) = &negj.lit else {
            continue;
        };
        let mut found_matching_pos = false;
        for posi in p {
            let Some(pos_lit) = &posi.lit else {
                continue;
            };
            if pos_lit.fn_id != neg_lit.fn_id || pos_lit.captures.len() != neg_lit.captures.len() {
                continue;
            }
            found_matching_pos = true;
            let all_subset = pos_lit
                .captures
                .iter()
                .zip(&neg_lit.captures)
                .all(|(pc, nc)| cx.descr(nc).diff(cx.descr(pc)).is_empty_memo(cx, memo));
            if all_subset {
                return true;
            }
        }
        if found_matching_pos {
            continue 'next_neg_lit;
        }
    }

    let filtered_negs: Vec<ArrowSig> = n.iter().filter(|negj| negj.lit.is_none()).cloned().collect();
    let n = &filtered_negs;
    if n.is_empty() {
        return false;
    }
    let n_pos = p.len();
    'next_neg: for negj in n {
        let s = arrow_input(negj);
        let v = cx.descr(&negj.ret).clone();
        for mask in 0u32..(1u32 << n_pos) {
            let mut union_in = Descr::none();
            let mut inter_out = Descr::any();
            for (i, pi) in p.iter().enumerate().take(n_pos) {
                if (mask >> i) & 1 == 1 {
                    union_in = union_in.union(cx, &arrow_input(pi));
                } else {
                    inter_out = inter_out.intersect(cx.descr(&pi.ret));
                }
            }
            if s.diff(&union_in).is_empty_memo(cx, memo) {
                continue;
            }
            if inter_out.diff(&v).is_empty_memo(cx, memo) {
                continue;
            }
            continue 'next_neg;
        }
        return true;
    }
    false
}

pub(crate) fn map_clause_empty(cx: TyCtx<'_>, c: &Conj<MapSig>, memo: &mut Memo) -> bool {
    if c.pos.is_empty() {
        return false;
    }
    let mut merged: BTreeMap<MapKey, Descr> = c.pos[0]
        .fields
        .iter()
        .map(|(k, v)| (k.clone(), cx.descr(v).clone()))
        .collect();
    for p in &c.pos[1..] {
        for (k, v) in &p.fields {
            merged
                .entry(k.clone())
                .and_modify(|e| *e = e.intersect(cx.descr(v)))
                .or_insert_with(|| cx.descr(v).clone());
        }
    }
    if merged.values().any(|v| v.is_empty_memo(cx, memo)) {
        return true;
    }
    for n in &c.neg {
        let n_keys_subset = n.fields.keys().all(|k| merged.contains_key(k));
        if !n_keys_subset {
            continue;
        }
        let value_refines = n.fields.iter().all(|(k, nv)| {
            merged
                .get(k)
                .map(|pv| pv.diff(cx.descr(nv)).is_empty_memo(cx, memo))
                .unwrap_or(false)
        });
        if value_refines {
            return true;
        }
    }
    false
}
