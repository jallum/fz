//! Structural signatures: `TupleSig`, `ListSig`, `ArrowSig`, `MapSig`,
//! the `ClosureLit` tag, and the `MergeSig` trait + per-sig impls.

use std::collections::BTreeMap;

use crate::fz_ir::FnId;

use super::{CallableValueKind, MapKey, Sigma, Ty, TyCtx, Types};

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct TupleSig {
    pub elems: Vec<Ty>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct ListSig {
    pub empty: bool,
    pub elem: Option<Ty>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct ResourceSig {
    pub payload: Ty,
}

impl ListSig {
    pub(super) fn empty() -> Self {
        Self {
            empty: true,
            elem: None,
        }
    }

    pub(super) fn possibly_empty(cx: &TyCtx<'_>, elem: Ty) -> Self {
        if cx.descr(&elem).is_empty(*cx) {
            Self::empty()
        } else {
            Self {
                empty: true,
                elem: Some(elem),
            }
        }
    }

    pub(super) fn non_empty(cx: &TyCtx<'_>, elem: Ty) -> Option<Self> {
        if cx.descr(&elem).is_empty(*cx) {
            None
        } else {
            Some(Self {
                empty: false,
                elem: Some(elem),
            })
        }
    }

    pub(super) fn is_exact_empty(&self) -> bool {
        self.empty && self.elem.is_none()
    }

    pub(super) fn is_exact_non_empty(&self) -> bool {
        !self.empty && self.elem.is_some()
    }

    pub(super) fn allow_empty(&mut self) {
        self.empty = true;
    }
}

/// fz-ul4.27.22.8 — closure-literal tag attached to an arrow clause.
/// When `ArrowSig::lit = Some(ClosureLit { kind, fn_id, captures })`, the
/// clause represents one specific callable value rather than only the
/// saturated arrow `(args)→ret`.
///
/// `kind = FnRef` means the value is a thin function reference with no
/// environment payload. `captures` must be empty in that case.
///
/// `kind = Closure` means the value is an env-carrying closure produced by
/// `MakeClosure(fn_id, vars_typed_as_captures)`. Captures are stored as a
/// vector aligned with the first N entry params of `fn_id`'s body.
///
/// The arrow's `args` field carries the apparent post-capture arity for
/// downstream contract-aware arrow matching.
///
/// Two `ClosureLit`s are equal iff `kind`, `fn_id`, and elementwise
/// `captures` match. Lit-bearing clauses do not collapse with lit-free clauses
/// under union — callable singletons are stricter than plain arrows, and the
/// union keeps both to preserve singleton precision downstream.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct ClosureLit {
    pub kind: CallableValueKind,
    pub fn_id: FnId,
    pub captures: Vec<Ty>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct ArrowSig {
    pub args: Vec<Ty>,
    pub ret: Ty,
    /// `None` for ordinary arrows; `Some` for closure literals (fz-ul4.27.22.8).
    pub lit: Option<ClosureLit>,
}

/// Open-shape map type: "any map containing AT LEAST these literal keys with
/// values of the corresponding types." Keys are concrete singleton values
/// (atoms, ints, strs); arbitrary-keyed maps fall back to `map_top`.
///
/// Subtyping (open record): `s <: t` iff every field in `t` is in `s` with
/// subtype value. More required keys = smaller set.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct MapSig {
    pub fields: BTreeMap<MapKey, Ty>,
}

/// The outcome of intersecting two same-axis positive sigs inside one clause.
pub(crate) enum PosMeet<T> {
    /// The pair collapsed to one narrower sig (`A ∩ B` on this axis).
    Merged(T),
    /// The pair is provably disjoint, so the WHOLE clause (which conjoins
    /// both) is `∅` and must not persist.
    Empty,
    /// The pair cannot be collapsed or refuted structurally; the clause keeps
    /// both sigs as separate positive conjuncts.
    Distinct,
}

/// Same-shape positive clauses in an intersection should collapse to one
/// narrower clause. This keeps semantic meets stable instead of piling up
/// conjunctive structure on every repeated refinement, and lets a merge that
/// proves emptiness drop the clause instead of persisting garbage (fz-go4.24).
pub(crate) trait MergeSig: Clone + PartialEq {
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self>;
}

impl MergeSig for ListSig {
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self> {
        let elem = match (a.elem, b.elem) {
            (Some(a), Some(b)) => {
                let elem = types.intersect(a, b);
                if types.is_empty(&elem) { None } else { Some(elem) }
            }
            _ => None,
        };
        let empty = a.empty && b.empty;
        // A non-empty list needs a head in the element intersection; with no
        // element left and `[]` excluded, the merged sig denotes `∅`.
        if !empty && elem.is_none() {
            return PosMeet::Empty;
        }
        PosMeet::Merged(ListSig { empty, elem })
    }
}

impl MergeSig for ResourceSig {
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self> {
        // `res(A) ∩ res(B) = res(A ∩ B)`, and `res(∅) = ∅` (a resource always
        // carries a payload; `Descr::resource_of` refuses an empty one).
        let payload = types.intersect(a.payload, b.payload);
        if types.is_empty(&payload) {
            PosMeet::Empty
        } else {
            PosMeet::Merged(ResourceSig { payload })
        }
    }
}

impl MergeSig for TupleSig {
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self> {
        // Tuples of different arity are disjoint products: `A₁×…×Aₙ ∩
        // B₁×…×Bₘ = ∅` for `n ≠ m` (a tuple value has exactly one arity —
        // the same rule `emptiness::tuple_clause_empty` decides by).
        if a.elems.len() != b.elems.len() {
            return PosMeet::Empty;
        }
        // `∏Aᵢ ∩ ∏Bᵢ = ∏(Aᵢ ∩ Bᵢ)`; a product with an empty factor is `∅`.
        let elems: Vec<Ty> = a
            .elems
            .iter()
            .zip(b.elems.iter())
            .map(|(x, y)| types.intersect(*x, *y))
            .collect();
        if elems.iter().any(|e| types.is_empty(e)) {
            return PosMeet::Empty;
        }
        PosMeet::Merged(TupleSig { elems })
    }
}

impl MergeSig for ArrowSig {
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self> {
        // An unmergeable arrow pair stays Distinct, never Empty: a conjunction
        // of arrows is an overload, which is inhabited in general.
        if a.args.len() != b.args.len() {
            return PosMeet::Distinct;
        }
        match (&a.lit, &b.lit) {
            (Some(la), Some(lb)) => {
                if la.fn_id != lb.fn_id || la.kind != lb.kind || la.captures.len() != lb.captures.len() {
                    return PosMeet::Distinct;
                }
                PosMeet::Merged(ArrowSig {
                    args: a
                        .args
                        .iter()
                        .zip(b.args.iter())
                        .map(|(x, y)| types.union(*x, *y))
                        .collect(),
                    ret: types.intersect(a.ret, b.ret),
                    lit: Some(ClosureLit {
                        kind: la.kind,
                        fn_id: la.fn_id,
                        captures: la
                            .captures
                            .iter()
                            .zip(lb.captures.iter())
                            .map(|(x, y)| types.intersect(*x, *y))
                            .collect(),
                    }),
                })
            }
            (Some(_), None) => PosMeet::Merged(specialize_lit_arrow(types, a, b)),
            (None, Some(_)) => PosMeet::Merged(specialize_lit_arrow(types, b, a)),
            (None, None) => PosMeet::Merged(ArrowSig {
                args: a
                    .args
                    .iter()
                    .zip(b.args.iter())
                    .map(|(x, y)| types.union(*x, *y))
                    .collect(),
                ret: types.intersect(a.ret, b.ret),
                lit: None,
            }),
        }
    }
}

fn specialize_lit_arrow(types: &mut Types, lit: &ArrowSig, surface: &ArrowSig) -> ArrowSig {
    let mut sigma = Sigma::new();
    for (pattern, witness) in lit.args.iter().zip(surface.args.iter()) {
        types.collect_instantiation_subst(pattern, witness, &mut sigma);
    }
    types.collect_instantiation_subst(&lit.ret, &surface.ret, &mut sigma);
    ArrowSig {
        args: lit.args.iter().map(|arg| types.instantiate(arg, &sigma)).collect(),
        ret: types.instantiate(&lit.ret, &sigma),
        lit: lit.lit.clone(),
    }
}

impl MergeSig for MapSig {
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self> {
        let mut fields = a.fields.clone();
        for (key, value) in &b.fields {
            fields
                .entry(key.clone())
                .and_modify(|current| *current = types.intersect(*current, *value))
                .or_insert(*value);
        }
        PosMeet::Merged(MapSig { fields })
    }
}
