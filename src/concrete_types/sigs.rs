//! Structural signatures: `TupleSig`, `ListSig`, `ArrowSig`, `MapSig`,
//! the `ClosureLit` tag, and the `MergeSig` trait + per-sig impls.

use std::collections::BTreeMap;

use crate::fz_ir::FnId;
use crate::types::{CallableValueKind, MapKey, Ty};

use super::descr::Descr;
use super::{ty_descr, ty_from_descr};

#[derive(Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) struct TupleSig {
    pub elems: Vec<Descr>,
}

#[derive(Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) struct ListSig {
    pub empty: bool,
    pub elem: Option<Box<Descr>>,
}

#[derive(Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) struct ResourceSig {
    pub payload: Box<Descr>,
}

impl ListSig {
    pub(super) fn empty() -> Self {
        Self {
            empty: true,
            elem: None,
        }
    }

    pub(super) fn possibly_empty(elem: Descr) -> Self {
        if elem.is_empty() {
            Self::empty()
        } else {
            Self {
                empty: true,
                elem: Some(Box::new(elem)),
            }
        }
    }

    pub(super) fn non_empty(elem: Descr) -> Option<Self> {
        if elem.is_empty() {
            None
        } else {
            Some(Self {
                empty: false,
                elem: Some(Box::new(elem)),
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
/// The arrow's `args` field carries the apparent post-capture arity (vector of
/// `Descr::any()` until 22.9's `resolve_closure_return` refines per spec
/// lookup).
///
/// Two `ClosureLit`s are equal iff `kind`, `fn_id`, and elementwise
/// `captures` match. Lit-bearing clauses do not collapse with lit-free clauses
/// under union — callable singletons are stricter than plain arrows, and the
/// union keeps both to preserve singleton precision downstream.
#[derive(Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) struct ClosureLit {
    pub kind: CallableValueKind,
    pub fn_id: FnId,
    pub captures: Vec<Ty>,
}

#[derive(Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) struct ArrowSig {
    pub args: Vec<Descr>,
    pub ret: Box<Descr>,
    /// `None` for ordinary arrows; `Some` for closure literals (fz-ul4.27.22.8).
    pub lit: Option<ClosureLit>,
}

/// Open-shape map type: "any map containing AT LEAST these literal keys with
/// values of the corresponding types." Keys are concrete singleton values
/// (atoms, ints, strs); arbitrary-keyed maps fall back to `map_top`.
///
/// Subtyping (open record): `s <: t` iff every field in `t` is in `s` with
/// subtype value. More required keys = smaller set.
#[derive(Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) struct MapSig {
    /// Serialized as a sequence of `(MapKey, Descr)` entries: `MapKey` is an
    /// enum, and serde_json rejects non-string map keys, so the map cannot
    /// round-trip as a JSON object.
    #[serde(with = "map_sig_fields")]
    pub fields: BTreeMap<MapKey, Descr>,
}

/// (De)serialize `BTreeMap<MapKey, Descr>` as a `Vec<(MapKey, Descr)>` so the
/// enum key survives serde_json (which forbids non-string object keys).
mod map_sig_fields {
    use super::{Descr, MapKey};
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::BTreeMap;

    pub fn serialize<S: Serializer>(fields: &BTreeMap<MapKey, Descr>, s: S) -> Result<S::Ok, S::Error> {
        fields.iter().collect::<Vec<_>>().serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<BTreeMap<MapKey, Descr>, D::Error> {
        Ok(Vec::<(MapKey, Descr)>::deserialize(d)?.into_iter().collect())
    }
}

/// fz-jvo — sig types that support semantic merging at the
/// intersection point. When two positive sigs of compatible shape
/// occur in the same Conj clause (e.g. `list(A) & list(B)` produced
/// by branch narrowing), they should collapse to a single sig with
/// elements intersected (`list(A ∩ B)`) — both for representation
/// minimality and so that downstream consumers (list_element_type,
/// tuple_projections, ...) don't see structurally-multi-sig clauses
/// they then have to reason about specially.
///
/// `intersect_pos` returns `Some(merged)` when two sigs can be
/// merged via intersection; `None` when they're incompatible (e.g.
/// tuples of different arities) and must remain as separate pos
/// sigs.
pub(crate) trait MergeSig: Clone + PartialEq {
    fn intersect_pos(a: &Self, b: &Self) -> Option<Self>;
}

impl MergeSig for ListSig {
    fn intersect_pos(a: &Self, b: &Self) -> Option<Self> {
        let elem = match (&a.elem, &b.elem) {
            (Some(a), Some(b)) => {
                let elem = a.intersect(b);
                if elem.is_empty() { None } else { Some(Box::new(elem)) }
            }
            _ => None,
        };
        Some(ListSig {
            empty: a.empty && b.empty,
            elem,
        })
    }
}

impl MergeSig for ResourceSig {
    fn intersect_pos(a: &Self, b: &Self) -> Option<Self> {
        let payload = a.payload.intersect(&b.payload);
        if payload.is_empty() {
            None
        } else {
            Some(ResourceSig {
                payload: Box::new(payload),
            })
        }
    }
}
impl MergeSig for TupleSig {
    fn intersect_pos(a: &Self, b: &Self) -> Option<Self> {
        if a.elems.len() != b.elems.len() {
            return None;
        }
        let elems = a
            .elems
            .iter()
            .zip(b.elems.iter())
            .map(|(x, y)| x.intersect(y))
            .collect();
        Some(TupleSig { elems })
    }
}

impl MergeSig for ArrowSig {
    fn intersect_pos(a: &Self, b: &Self) -> Option<Self> {
        if a.args.len() != b.args.len() {
            return None;
        }
        // fz-ul4.27.22.8 — closure-literal lit handling at ∧:
        //   lit(F,K) ∧ lit(F,K')  → lit(F, K∩K' elementwise) — same closure,
        //                          captures must satisfy both → narrow.
        //   lit(F,K) ∧ lit(F',K') with F≠F' → no function is both; return
        //                          None so the caller keeps them as separate
        //                          pos sigs (clause becomes empty under
        //                          func_clause_empty's structural check
        //                          when extended; safe representation today).
        //   lit(F,K) ∧ plain_arrow → lit(F,K) wins (singleton ⊆ arrow), but
        //                          take args/ret from the plain arrow side
        //                          if narrower.
        //   plain ∧ plain → existing behavior, lit stays None.
        let lit = match (&a.lit, &b.lit) {
            (Some(la), Some(lb)) => {
                if la.fn_id != lb.fn_id {
                    return None;
                }
                if la.kind != lb.kind {
                    return None;
                }
                if la.captures.len() != lb.captures.len() {
                    return None;
                }
                let caps: Vec<Ty> = la
                    .captures
                    .iter()
                    .zip(lb.captures.iter())
                    .map(|(x, y)| ty_from_descr(ty_descr(x).intersect(ty_descr(y))))
                    .collect();
                Some(ClosureLit {
                    kind: la.kind,
                    fn_id: la.fn_id,
                    captures: caps,
                })
            }
            (Some(la), None) => Some(la.clone()),
            (None, Some(lb)) => Some(lb.clone()),
            (None, None) => None,
        };
        // Arrow contravariant on args (union to widen accepted input),
        // covariant on return (intersect to narrow accepted output).
        let args = a.args.iter().zip(b.args.iter()).map(|(x, y)| x.union(y)).collect();
        let ret = a.ret.intersect(&b.ret);
        Some(ArrowSig {
            args,
            ret: Box::new(ret),
            lit,
        })
    }
}

impl MergeSig for MapSig {
    fn intersect_pos(a: &Self, b: &Self) -> Option<Self> {
        // Map intersection: shared keys' values get intersected;
        // keys present in only one side stay as-is (both maps must
        // have at least that field, possibly with a more permissive
        // type on the missing side).
        let mut fields = a.fields.clone();
        for (k, v) in &b.fields {
            fields
                .entry(k.clone())
                .and_modify(|prev| *prev = prev.intersect(v))
                .or_insert_with(|| v.clone());
        }
        Some(MapSig { fields })
    }
}
