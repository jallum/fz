//! DNF operations: union, intersection, negation, the tuple-clause
//! subsumption predicate, and the list-axis empty/nonempty normalization pass.

use super::Ty;
use super::conj::Conj;
use super::sigs::{ListSig, TupleSig};

pub(crate) fn dnf_union<T: Clone + PartialEq>(a: &[Conj<T>], b: &[Conj<T>]) -> Vec<Conj<T>> {
    // ∨ is idempotent. Dedup exact-duplicate clauses at
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
    // list(float)`). Subsumption-based absorption (`A ⊆ B ⇒ A ∨ B = B`)
    // is semantic, so it lives above the descriptor kernel: `Types::intern`
    // canonicalizes the tuples axis at the persistence boundary.
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
    dnf_intersect_with(a, b, |c1, c2| Some(merge_clauses(c1, c2)))
}

/// The one clause-product skeleton behind both intersections: the structural
/// kernel (`Descr::intersect`, via [`dnf_intersect`]) concatenates clause
/// literals, while the semantic path (`Types::intersect`) collapses same-shape
/// positives through `MergeSig` and reports provably-empty merges as `None`.
///
/// The product is kept hygienic as it is built:
/// merges that prove the clause empty are skipped (`merge` returns `None`),
/// clauses containing a literal both positively and negatively are empty
/// (`P ∧ ¬P = ∅`, sound structurally without any semantic query), and
/// duplicate clauses collapse (`A ∨ A = A`, mirroring `dnf_union`).
/// Without this, iterated intersections snowball, and one `dnf_neg` over
/// the result distributes into millions of clauses (00277 built 2^21).
pub(crate) fn dnf_intersect_with<T: Clone + PartialEq>(
    a: &[Conj<T>],
    b: &[Conj<T>],
    mut merge: impl FnMut(&Conj<T>, &Conj<T>) -> Option<Conj<T>>,
) -> Vec<Conj<T>> {
    let mut out = Vec::with_capacity(a.len().max(b.len()));
    for c1 in a {
        for c2 in b {
            let Some(merged) = merge(c1, c2) else {
                continue;
            };
            if merged.pos.iter().any(|p| merged.neg.contains(p)) {
                continue;
            }
            if !out.contains(&merged) {
                out.push(merged);
            }
        }
    }
    out
}

/// `A ⊆ B` for two tuple clauses, by sufficient conditions only (`false`
/// means "not proven", never "proven not"). Used for absorption at the
/// persistence boundary (`A ⊆ B ⇒ A ∨ B = B`):
///
/// - structurally, a clause with a superset of the other's literals denotes a
///   subset (`⋀` of more constraints), covering exact duplicates and the
///   saturated `Conj::top()` absorbing everything;
/// - for plain single-positive clauses, products of non-empty sets compare
///   coordinatewise: `∏Aᵢ ⊆ ∏Bᵢ ⟺ ∀i. Aᵢ ⊆ Bᵢ` — exact, given interned
///   clauses never carry an empty coordinate.
///
/// `is_subtype` is injected so callers can route through the memoized
/// comparison cache.
pub(crate) fn tuple_clause_subsumed(
    a: &Conj<TupleSig>,
    b: &Conj<TupleSig>,
    mut is_subtype: impl FnMut(&Ty, &Ty) -> bool,
) -> bool {
    if b.pos.iter().all(|p| a.pos.contains(p)) && b.neg.iter().all(|n| a.neg.contains(n)) {
        return true;
    }
    match (a.pos.as_slice(), a.neg.as_slice(), b.pos.as_slice(), b.neg.as_slice()) {
        ([pa], [], [pb], []) => {
            pa.elems.len() == pb.elems.len() && pa.elems.iter().zip(pb.elems.iter()).all(|(x, y)| is_subtype(x, y))
        }
        _ => false,
    }
}

/// ¬(⋁ Cᵢ) = ⋀ ¬Cᵢ. Each ¬Cᵢ is a DNF (disjunction of single-literal
/// clauses); we intersect them all together. Duplicate clauses contribute
/// duplicate factors (`¬A ∧ ¬A = ¬A`) and are skipped — the product is
/// exponential in the factor count, so idempotence is applied to the input,
/// not just the output.
pub(crate) fn dnf_neg<T: Clone + PartialEq>(d: &[Conj<T>]) -> Vec<Conj<T>> {
    let mut acc: Vec<Conj<T>> = vec![Conj::top()]; // start with "true"
    let mut seen: Vec<&Conj<T>> = Vec::with_capacity(d.len());
    for c in d {
        if seen.contains(&c) {
            continue;
        }
        seen.push(c);
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
