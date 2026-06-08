//! Structural signatures: `TupleSig`, `ListSig`, `ArrowSig`, `MapSig`,
//! the `ClosureLit` tag, and the `MergeSig` trait + per-sig impls.

use std::collections::BTreeMap;

use crate::fz_ir::FnId;

use super::{CallableValueKind, MapKey, Ty, TyCtx};

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
/// The arrow's `args` field carries the apparent post-capture arity (vector of
/// `Descr::any()` until 22.9's `resolve_closure_return` refines per spec
/// lookup).
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
