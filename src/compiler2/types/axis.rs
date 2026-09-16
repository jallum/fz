//! The rewrites that make one DNF axis a function of the set it denotes.
//!
//! An axis denotes the UNION of its clauses, so a clause that denotes nothing
//! is that union's identity and is dropped (`A ∨ ∅ = A`). The rewrite produces
//! a semantically EQUAL descriptor, so emptiness and subtyping answers are
//! unchanged; only the clause list shrinks.
//!
//! `Types::intern` is the authority: it applies this at the persistence
//! boundary, so an interned descriptor arrives already swept and identity is
//! assigned to the swept form. [`TyCanon`](super::canon) is the second caller,
//! for the descriptors it builds ITSELF — tuple-coordinate widening and a list
//! clause's intersected element fragment are `Descr` values that never reach
//! the interner, and an intersection can empty a clause there just as it can
//! anywhere else. One function, so the boundary and the rendering cannot drift
//! apart.

use super::Ty;
use super::TyCtx;
use super::conj::Conj;
use super::descr::Descr;
use super::emptiness;
use super::sigs::TupleSig;

/// `A ∨ ∅ = A` on every axis.
///
/// `is_empty_ty` is injected so a caller holding a memo answers coordinate
/// emptiness through it; without one the same algorithm runs uncached. It is
/// consulted only on the plain single-positive tuple product — overwhelmingly
/// the common shape, and the one where a coordinate decides the clause on its
/// own.
pub(super) fn drop_empty_clauses(cx: TyCtx<'_>, d: &mut Descr, is_empty_ty: &dyn Fn(&Ty) -> bool) {
    d.tuples.retain(|clause| !tuple_clause_empty(cx, clause, is_empty_ty));
    retain_inhabited(cx, &mut d.lists, emptiness::list_clause_empty);
    retain_inhabited(cx, &mut d.resources, emptiness::resource_clause_empty);
    retain_inhabited(cx, &mut d.funcs, emptiness::func_clause_empty);
    retain_inhabited(cx, &mut d.maps, emptiness::map_clause_empty);
}

fn tuple_clause_empty(cx: TyCtx<'_>, c: &Conj<TupleSig>, is_empty_ty: &dyn Fn(&Ty) -> bool) -> bool {
    if let ([p], []) = (c.pos.as_slice(), c.neg.as_slice()) {
        return p.elems.iter().any(is_empty_ty);
    }
    emptiness::tuple_clause_empty(cx, c, &mut emptiness::Memo::default())
}

fn retain_inhabited<T>(
    cx: TyCtx<'_>,
    clauses: &mut Vec<Conj<T>>,
    clause_empty: fn(TyCtx<'_>, &Conj<T>, &mut emptiness::Memo) -> bool,
) {
    clauses.retain(|clause| !clause_empty(cx, clause, &mut emptiness::Memo::default()));
}
