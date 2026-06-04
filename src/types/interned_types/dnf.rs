//! DNF operations: union, intersection, negation, subsumption dedup, and
//! the list-axis empty/nonempty normalization pass.

use super::conj::Conj;
use super::sigs::ListSig;

pub(crate) fn dnf_union<T: Clone + PartialEq>(a: &[Conj<T>], b: &[Conj<T>]) -> Vec<Conj<T>> {
    // fz-sj6.1 — ∨ is idempotent. Dedup exact-duplicate clauses at
    // union to keep the DNF in a canonical-enough form for diagnostic
    // output and downstream consumers. Without this, repeated unions
    // of equal Descrs pile up clauses (`/tmp/sum.fz` showed 15 copies
    // of `list(1|2|3|4|5)` from recursive narrowing).
    //
    // Soundness: `A ∨ A = A` is unconditionally true. We compare
    // clauses via derived PartialEq (structural equality through
    // `Conj.pos / .neg`).
    //
    // We do NOT merge same-shape clauses (`list(A) ∨ list(B) →
    // list(A∨B)`) — that's unsound for heterogeneous lists
    // (`[1, 2.0]` lives in `list(int∨float)` but not `list(int) ∨
    // list(float)`). Subsumption-based dedup (`A ⊆ B ⇒ A ∨ B = B`,
    // fz-et8) runs as a post-pass at `Descr::union`.
    let mut out: Vec<Conj<T>> = Vec::with_capacity(a.len() + b.len());
    for c in a {
        if !out.contains(c) {
            out.push(c.clone());
        }
    }
    for c in b {
        if !out.contains(c) {
            out.push(c.clone());
        }
    }
    out
}

pub(crate) fn normalize_empty_nonempty_list_unions(clauses: Vec<Conj<ListSig>>) -> Vec<Conj<ListSig>> {
    let has_empty_list = clauses
        .iter()
        .any(|c| c.neg.is_empty() && c.pos.len() == 1 && c.pos[0].is_exact_empty());
    if !has_empty_list {
        return clauses;
    }

    let mut widened_any_non_empty = false;
    let mut out = Vec::with_capacity(clauses.len());
    for mut c in clauses {
        if c.neg.is_empty() && c.pos.len() == 1 {
            let sig = &mut c.pos[0];
            if sig.is_exact_empty() {
                continue;
            }
            if sig.is_exact_non_empty() {
                sig.allow_empty();
                widened_any_non_empty = true;
            }
        }
        if !out.contains(&c) {
            out.push(c);
        }
    }

    if widened_any_non_empty {
        out
    } else {
        let empty = Conj::pos_of(ListSig::empty());
        if !out.contains(&empty) {
            out.push(empty);
        }
        out
    }
}

pub(crate) fn dnf_intersect<T: Clone + PartialEq>(a: &[Conj<T>], b: &[Conj<T>]) -> Vec<Conj<T>> {
    let mut out = Vec::with_capacity(a.len() * b.len());
    for c1 in a {
        for c2 in b {
            out.push(merge_clauses(c1, c2));
        }
    }
    out
}

/// ¬(⋁ Cᵢ) = ⋀ ¬Cᵢ. Each ¬Cᵢ is a DNF (disjunction of single-literal
/// clauses); we intersect them all together.
pub(crate) fn dnf_neg<T: Clone + PartialEq>(d: &[Conj<T>]) -> Vec<Conj<T>> {
    let mut acc: Vec<Conj<T>> = vec![Conj::top()]; // start with "true"
    for c in d {
        let neg_c = neg_clause(c);
        acc = dnf_intersect(&acc, &neg_c);
    }
    acc
}

pub(crate) fn merge_clauses<T: Clone + PartialEq>(a: &Conj<T>, b: &Conj<T>) -> Conj<T> {
    let mut pos = a.pos.clone();
    for new_sig in &b.pos {
        if !pos.contains(new_sig) {
            pos.push(new_sig.clone());
        }
    }
    let mut neg = a.neg.clone();
    for x in &b.neg {
        if !neg.contains(x) {
            neg.push(x.clone());
        }
    }
    Conj { pos, neg }
}

/// ¬(⋀ pos ∧ ⋀ ¬neg) = ⋁ (¬p) ∨ ⋁ n  — one single-literal clause per element.
pub(crate) fn neg_clause<T: Clone>(c: &Conj<T>) -> Vec<Conj<T>> {
    let mut out: Vec<Conj<T>> = Vec::with_capacity(c.pos.len() + c.neg.len());
    for p in &c.pos {
        out.push(Conj {
            pos: vec![],
            neg: vec![p.clone()],
        });
    }
    for n in &c.neg {
        out.push(Conj {
            pos: vec![n.clone()],
            neg: vec![],
        });
    }
    out
}

pub(crate) fn is_dnf_top<T>(d: &[Conj<T>]) -> bool {
    d.len() == 1 && d[0].pos.is_empty() && d[0].neg.is_empty()
}
