//! Per-axis emptiness algorithms for DNF clauses.

use std::collections::{BTreeMap, HashSet};

use crate::types::MapKey;

use super::conj::Conj;
use super::descr::Descr;
use super::sigs::{ArrowSig, ClosureLit, ListSig, MapSig, ResourceSig, TupleSig};
use super::ty_descr;

#[derive(Default)]
pub(crate) struct Memo {
    pub(super) in_flight: HashSet<Descr>,
}

// ----------------------------------------------------------------------
// Tuple emptiness — Φ algorithm
// ----------------------------------------------------------------------
//
// A clause `⋀ pos ∧ ⋀ ¬neg` over n-tuples is empty iff it describes the
// empty set. We split on arity:
//
//   * Empty positives: the clause matches "any tuple of any arity not in
//     ⋃neg". Tuple arity is unbounded in fz, so a finite set of negatives
//     can never cover all arities — hence this is always non-empty.
//
//   * Non-empty positives: every positive must agree on arity (else the
//     positive intersection is empty). With shared arity n, intersect
//     positives componentwise to get a "rectangle" (t1, ..., tn). Filter
//     negatives down to those of arity n (others can't intersect this
//     rectangle, so they're vacuously satisfied). Run Φ.
//
// Φ(t, N): is the rectangle t covered by the union of negative rectangles
// in N? Pick a negative s, split t by "first index where the value falls
// outside s_i":
//
//   slab_i = (t_1 ∩ s_1, ..., t_{i-1} ∩ s_{i-1}, t_i \ s_i, t_{i+1}, ..., t_n)
//
// Each slab must be covered by N \ {s}. Base case: an empty rectangle
// (some component empty) is trivially covered.

pub(crate) fn tuple_clause_empty(c: &Conj<TupleSig>, memo: &mut Memo) -> bool {
    if c.pos.is_empty() {
        // Tuple universe is unbounded in arity; a finite set of negative
        // tuple shapes can never cover it.
        return false;
    }
    let arity = c.pos[0].elems.len();
    if c.pos.iter().any(|p| p.elems.len() != arity) {
        // Distinct arities in positives → intersection is empty.
        return true;
    }
    // Componentwise intersection of positives.
    let mut t: Vec<Descr> = c.pos[0].elems.clone();
    for p in &c.pos[1..] {
        for (i, e) in p.elems.iter().enumerate() {
            t[i] = t[i].intersect(e);
        }
    }
    // Negatives at this arity contribute; other arities don't intersect the
    // rectangle and are vacuously satisfied.
    let negs: Vec<Vec<Descr>> = c
        .neg
        .iter()
        .filter(|n| n.elems.len() == arity)
        .map(|n| n.elems.clone())
        .collect();
    phi_tuple(&t, &negs, memo)
}

pub(crate) fn phi_tuple(t: &[Descr], n: &[Vec<Descr>], memo: &mut Memo) -> bool {
    if n.is_empty() {
        return t.iter().any(|d| d.is_empty_memo(memo));
    }
    let head = &n[0];
    let rest = &n[1..];
    for i in 0..t.len() {
        let mut t_split = t.to_vec();
        for j in 0..i {
            t_split[j] = t_split[j].intersect(&head[j]);
        }
        t_split[i] = t_split[i].diff(&head[i]);
        if !phi_tuple(&t_split, rest, memo) {
            return false;
        }
    }
    true
}

// ----------------------------------------------------------------------
// List emptiness — homogeneous-list rule
// ----------------------------------------------------------------------
//
// Every `list(T)` contains nil, so the positive part is always inhabited.
// A clause `pos ∧ ⋀ ¬neg` is empty iff `list(t) ⊆ ⋃ list(N_j)` where
// `t` is the intersection of positive element types.
//
// Standard rule: `list(t) ⊆ ⋃ list(N_j)` iff there's a single j with
// `t ⊆ N_j` — because lists are homogeneous, every value of a single
// list must use the same N_j. The empty list trivially fits any list type.
//
// `is_subtype` here recurses through `is_empty`, which is what makes the
// memo necessary for recursive list types.

pub(crate) fn list_clause_empty(c: &Conj<ListSig>, memo: &mut Memo) -> bool {
    let (empty, t) = if c.pos.is_empty() {
        (true, Some(Descr::any())) // implicit positive: list(any)
    } else {
        let mut empty = true;
        let mut t: Option<Descr> = None;
        for p in &c.pos {
            empty &= p.empty;
            t = match (t, &p.elem) {
                (None, None) => None,
                (None, Some(elem)) => Some(elem.as_ref().clone()),
                (Some(prev), None) => Some(prev),
                (Some(prev), Some(elem)) => {
                    let next = prev.intersect(elem);
                    if next.is_empty_memo(memo) { None } else { Some(next) }
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
    let neg_covers_empty = |n: &ListSig| n.empty;
    let neg_covers_non_empty =
        |n: &ListSig, t: &Descr, memo: &mut Memo| n.elem.as_ref().is_some_and(|elem| t.diff(elem).is_empty_memo(memo));
    let empty_covered = !empty || c.neg.iter().any(neg_covers_empty);
    let non_empty_covered = match t {
        None => true,
        Some(ref t) => c.neg.iter().any(|n| neg_covers_non_empty(n, t, memo)),
    };
    empty_covered && non_empty_covered
}

pub(crate) fn resource_clause_empty(c: &Conj<ResourceSig>, memo: &mut Memo) -> bool {
    let payload = if c.pos.is_empty() {
        Descr::any()
    } else {
        let mut payload = (*c.pos[0].payload).clone();
        for p in &c.pos[1..] {
            payload = payload.intersect(&p.payload);
        }
        if payload.is_empty_memo(memo) {
            return true;
        }
        payload
    };
    if c.neg.is_empty() {
        return false;
    }
    c.neg.iter().any(|n| payload.diff(&n.payload).is_empty_memo(memo))
}

// ----------------------------------------------------------------------
// Arrow emptiness — contravariant subsumption
// ----------------------------------------------------------------------
//
// Standard semantic-subtyping result for arrows:
//   ⋀_i (t_i → u_i)  ⊆  (s → v)
//   iff  for every P' ⊆ P:  s ⊆ ⋃_{i ∈ P'} t_i  OR  ⋂_{i ∉ P'} u_i ⊆ v
//
// A clause is empty iff some negative `(s, v)` is subsumed by the
// positives — meaning every function satisfying the positives is forced
// into `(s → v)`, contradicting `¬(s → v)`. We try each negative; if any
// passes the for-all-subsets test, the clause is empty.
//
// For multi-arg arrows, the "input domain" is the n-tuple of args.

fn arrow_input(sig: &ArrowSig) -> Descr {
    Descr::tuple_of(sig.args.clone())
}

pub(crate) fn func_clause_empty(c: &Conj<ArrowSig>, memo: &mut Memo) -> bool {
    let p = &c.pos;
    let n = &c.neg;

    // fz-ul4.27.22.8 — closure-literal aware pre-checks.
    //
    // (a) Two positive lits in the same clause with disagreeing FnId (or
    //     different arity) describe disjoint singletons — their ∧ is
    //     bottom. Captures must intersect elementwise; any empty
    //     intersection drives the clause to bottom.
    {
        let pos_lits: Vec<&ClosureLit> = p.iter().filter_map(|s| s.lit.as_ref()).collect();
        for i in 0..pos_lits.len() {
            for j in (i + 1)..pos_lits.len() {
                if pos_lits[i].fn_id != pos_lits[j].fn_id {
                    return true;
                }
                if pos_lits[i].captures.len() != pos_lits[j].captures.len() {
                    return true;
                }
                for (a, b) in pos_lits[i].captures.iter().zip(&pos_lits[j].captures) {
                    if ty_descr(a).intersect(ty_descr(b)).is_empty_memo(memo) {
                        return true;
                    }
                }
            }
        }
    }

    // (b) Lit-aware negative subsumption. If a neg sig has a lit tag:
    //       - it constrains the clause only via pos sigs with matching
    //         FnId (other-FnId pos sigs don't overlap the neg's singleton
    //         set, so the negation is automatically satisfied there);
    //       - the neg is subsumed iff some matching-FnId pos sig has
    //         captures elementwise ⊇ the neg's captures.
    //     If a matching pos sig subsumes the neg → clause is bottom.
    //     If no matching pos sig exists → this neg cannot empty the
    //     clause via lit reasoning; defer to the structural check on
    //     the lit-free part below.
    'next_neg_lit: for negj in n {
        let Some(neg_lit) = &negj.lit else {
            continue;
        };
        let mut found_matching_pos = false;
        for posi in p {
            let Some(pos_lit) = &posi.lit else {
                continue;
            };
            if pos_lit.fn_id != neg_lit.fn_id {
                continue;
            }
            if pos_lit.captures.len() != neg_lit.captures.len() {
                continue;
            }
            found_matching_pos = true;
            // pos captures must elementwise ⊇ neg captures (i.e., neg
            // ⊆ pos in capture space). diff(neg, pos) empty per axis.
            let all_subset = pos_lit
                .captures
                .iter()
                .zip(&neg_lit.captures)
                .all(|(pc, nc)| ty_descr(nc).diff(ty_descr(pc)).is_empty_memo(memo));
            if all_subset {
                return true;
            }
        }
        if found_matching_pos {
            // We had a matching-FnId pos but it didn't fully subsume —
            // the neg cuts a hole the pos sigs don't cover. Clause is
            // not bottom via this neg. Continue to next neg.
            continue 'next_neg_lit;
        }
        // No matching-FnId pos — neg is irrelevant for lit reasoning;
        // structural check below would falsely subsume on `any`
        // placeholders. Skip negj from the structural check by
        // recording its index... simplest: short-circuit here, since
        // a lit-tagged neg unrelated to any pos lit cannot make the
        // clause empty (it negates a set disjoint from the pos).
        // Falling through to the structural check would incorrectly
        // consider this neg's any-args / any-ret coverage. So we
        // simply continue and do NOT consult negj in the structural
        // loop. To enforce that, filter negs before the loop.
    }

    // Lit-tagged negs are fully handled by the pre-pass above. If we got
    // here without returning, none of them subsumes via lit reasoning;
    // drop them all from the structural check so any-args / any-ret
    // placeholders on lit clauses can't falsely subsume.
    let filtered_negs: Vec<ArrowSig> = n.iter().filter(|negj| negj.lit.is_none()).cloned().collect();
    let n = &filtered_negs;

    if n.is_empty() {
        // ⋀ positives is non-empty: at least one function (e.g., the constant
        // function) satisfies any consistent set of positive arrows.
        return false;
    }
    let n_pos = p.len();
    if n_pos > 24 {
        // 2^n subsets becomes painful; we don't expect this in practice.
        // Fall through and let it run; users can split clauses if needed.
    }
    'next_neg: for negj in n {
        let s = arrow_input(negj);
        let v = (*negj.ret).clone();
        for mask in 0u32..(1u32 << n_pos) {
            let mut union_in = Descr::none();
            let mut inter_out = Descr::any();
            for (i, pi) in p.iter().enumerate().take(n_pos) {
                if (mask >> i) & 1 == 1 {
                    union_in = union_in.union(&arrow_input(pi));
                } else {
                    inter_out = inter_out.intersect(&pi.ret);
                }
            }
            // Either inputs of P' cover s, OR outputs of P\P' refine v.
            if s.diff(&union_in).is_empty_memo(memo) {
                continue;
            }
            if inter_out.diff(&v).is_empty_memo(memo) {
                continue;
            }
            // Neither side held — this subset breaks subsumption for negj.
            continue 'next_neg;
        }
        // Every subset passed → negj is subsumed → clause is empty.
        return true;
    }
    false
}

// ----------------------------------------------------------------------
// Map emptiness — open-shape rule
// ----------------------------------------------------------------------
//
// An open-shape map type `MapSig{F: T}` represents the set of all maps
// containing AT LEAST the listed keys with values of the listed types
// (more keys with arbitrary values are allowed).
//
// A clause `⋀ pos ∧ ⋀ ¬neg`:
//
//   * Empty positives: any map. Negatives covering "any map" requires the
//     union of negs to span the full map universe — impossible for any
//     finite collection of open shapes (extra keys give wiggle room).
//
//   * Non-empty positives: merge into a single open shape `P` (union of
//     required keys; intersect overlapping value types). `P` is empty if
//     any required field has empty value type. Negative `Nj` subsumes `P`
//     iff `Nj.fields ⊆ P.fields` (open subtype) AND for each shared key,
//     `P.value(k) ⊆ Nj.value(k)`. Clause is empty iff some negative
//     subsumes the merged positive.
//
//   * This is sound for the open-shape fragment we use; negatives that
//     reference "this exact key set" semantics aren't expressible here
//     (we'd need closed shapes for that).

pub(crate) fn map_clause_empty(c: &Conj<MapSig>, memo: &mut Memo) -> bool {
    if c.pos.is_empty() {
        // Any-map universe ⊄ finite union of open shapes (extras always escape).
        return false;
    }
    // Merge positives.
    let mut merged: BTreeMap<MapKey, Descr> = c.pos[0].fields.clone();
    for p in &c.pos[1..] {
        for (k, v) in &p.fields {
            merged
                .entry(k.clone())
                .and_modify(|e| *e = e.intersect(v))
                .or_insert_with(|| v.clone());
        }
    }
    // Empty if any required field is empty.
    if merged.values().any(|v| v.is_empty_memo(memo)) {
        return true;
    }
    // Negative subsumption.
    for n in &c.neg {
        let n_keys_subset = n.fields.keys().all(|k| merged.contains_key(k));
        if !n_keys_subset {
            continue;
        }
        let value_refines = n
            .fields
            .iter()
            .all(|(k, nv)| merged.get(k).map(|pv| pv.diff(nv).is_empty_memo(memo)).unwrap_or(false));
        if value_refines {
            return true;
        }
    }
    false
}
