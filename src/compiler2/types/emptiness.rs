//! Per-axis emptiness algorithms for the interned descriptor kernel.

use crate::fz_ir::FnId;
use std::collections::{BTreeMap, HashSet};

use super::conj::Conj;
use super::descr::Descr;
use super::sigs::{ArrowSig, ClosureLit, ListSig, MapSig, ResourceSig, TupleSig};
use super::{MapKey, Ty, TyCtx};

/// Coinductive assumption set for one top-level emptiness query. Emptiness
/// over recursive descriptors is a greatest fixpoint: a query that re-enters a
/// descriptor already `in_flight` assumes it empty, and the assumption is
/// discharged if the whole cycle checks out.
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

/// Is the product `∏t` minus the union of the products `∏n` empty?
///
/// Exact, and stated over DESCRIPTORS rather than interned coordinates, so a
/// caller can decide `∏t ⊆ ⋃∏n` for rectangles it built but never interned.
/// Every entry of `n` must have the same arity as `t`; a mismatched arity
/// subtracts nothing and belongs to the caller's filter.
pub(super) fn phi_tuple(cx: TyCtx<'_>, t: &[Descr], n: &[Vec<Descr>], memo: &mut Memo) -> bool {
    // One empty coordinate empties the whole product — no negation needed.
    // Checking at entry prunes every recursive branch whose diff/intersect
    // zeroed a coordinate; without this the recursion only discovers the
    // emptiness at the leaves, after fanning out arity^|negs| branches.
    if t.iter().any(|d| d.is_empty_memo(cx, memo)) {
        return true;
    }
    let Some((head, rest)) = n.split_first() else {
        return false;
    };
    // A negation disjoint from the product on any coordinate subtracts
    // nothing: drop it instead of splitting on it.
    if head
        .iter()
        .zip(t)
        .any(|(h, ti)| ti.intersect(h).is_empty_memo(cx, memo))
    {
        return phi_tuple(cx, t, rest, memo);
    }
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

/// The positive fold's evidence about the NONEMPTY fragment of a list-clause
/// intersection ("unknown is not none"): before any sig is folded the
/// fragment is unconstrained — a distinct state from proven-empty. An
/// exact-empty sig (`elem: None`) admits no nonempty lists, so it forces
/// `Empty`, and `Empty` absorbs everything folded after it.
enum ElemEvidence {
    Unconstrained,
    Empty,
    Inhabited(Box<Descr>),
}

impl ElemEvidence {
    /// Fold one positive sig's element constraint into the cell. `Empty` is
    /// absorbing; every other transition is a plain set intersection, so
    /// inhabited evidence degrades to `Empty` only on genuine set facts (an
    /// exact-empty sig, or an intersection that empties).
    fn meet(self, cx: TyCtx<'_>, sig_elem: Option<Ty>, memo: &mut Memo) -> Self {
        let Some(elem) = sig_elem else {
            return Self::Empty;
        };
        let next = match self {
            Self::Empty => return Self::Empty,
            Self::Unconstrained => cx.descr(&elem).clone(),
            Self::Inhabited(prev) => prev.intersect(cx.descr(&elem)),
        };
        if next.is_empty_memo(cx, memo) {
            Self::Empty
        } else {
            Self::Inhabited(Box::new(next))
        }
    }

    /// The fragment's element descriptor, `None` meaning ONLY "proven empty".
    fn fragment(self) -> Option<Descr> {
        match self {
            Self::Unconstrained => Some(Descr::any()),
            Self::Empty => None,
            Self::Inhabited(d) => Some(*d),
        }
    }
}

pub(crate) fn list_clause_empty(cx: TyCtx<'_>, c: &Conj<ListSig>, memo: &mut Memo) -> bool {
    let mut empty = true;
    let mut evidence = ElemEvidence::Unconstrained;
    for p in &c.pos {
        empty &= p.empty;
        evidence = evidence.meet(cx, p.elem, memo);
    }
    let t = evidence.fragment();
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

/// Whether two closure literals can name ONE value: the same brand, or either
/// one anonymous — an anonymous literal is every brand at once.
fn closure_brands_meet(a: Option<FnId>, b: Option<FnId>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a == b,
        _ => true,
    }
}

/// Whether every brand `pos` names, `neg` names too. An anonymous `neg`
/// subtracts every brand; a branded `neg` subtracts only its own, and never
/// covers an anonymous `pos`, which names every other brand as well.
fn closure_brand_inside(pos: Option<FnId>, neg: Option<FnId>) -> bool {
    match (pos, neg) {
        (_, None) => true,
        (Some(pos), Some(neg)) => pos == neg,
        (None, Some(_)) => false,
    }
}

pub(crate) fn func_clause_empty(cx: TyCtx<'_>, c: &Conj<ArrowSig>, memo: &mut Memo) -> bool {
    let p = &c.pos;
    let n = &c.neg;

    let pos_lits: Vec<&ClosureLit> = p.iter().filter_map(|s| s.lit.as_ref()).collect();
    // A closure holds exactly one value per capture slot, so a literal whose
    // capture TYPE is empty denotes nothing -- however it got that way. An
    // anonymous literal is every brand at once, so it MERGES with a branded
    // one instead of staying distinct from it, and the merged literal's
    // capture is the two captures' intersection; one brand at two capture
    // types merges the same way. Asking each literal about its own captures
    // covers both, where the pairwise loop below can only see pairs that
    // survived the merge.
    if pos_lits
        .iter()
        .any(|lit| lit.captures.iter().any(|c| cx.descr(c).is_empty_memo(cx, memo)))
    {
        return true;
    }
    for i in 0..pos_lits.len() {
        for j in (i + 1)..pos_lits.len() {
            if !closure_brands_meet(pos_lits[i].fn_id, pos_lits[j].fn_id)
                || pos_lits[i].captures.len() != pos_lits[j].captures.len()
            {
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
            if !closure_brand_inside(pos_lit.fn_id, neg_lit.fn_id) || pos_lit.captures.len() != neg_lit.captures.len() {
                continue;
            }
            found_matching_pos = true;
            // The clause is empty only when the positive capture space is
            // fully covered by the negated capture space: P \ N = empty iff
            // P ⊆ N.
            let pos_subset_of_neg = pos_lit
                .captures
                .iter()
                .zip(&neg_lit.captures)
                .all(|(pc, nc)| cx.descr(pc).diff(cx.descr(nc)).is_empty_memo(cx, memo));
            if pos_subset_of_neg {
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
