//! Component view API (fz-68x).
//!
//! The consumer-facing surface for code that needs to *destructure* a
//! `Descr` axis-by-axis (interp TypeTest, codegen repr selection, planner
//! projections, reducer literal extraction). Today the consumers reach
//! into the public axis fields directly; this is the API they migrate
//! to in fz-68x.{3..7}, after which the axis fields seal (fz-68x.8).
//!
//! The boundary lets the internal representation evolve — Elixir's
//! `Module.Types.Descr` is migrating DNF → BDD with hash-consing, and
//! fz can follow without rippling through every consumer.
//!
//! `Descr::components()` yields only *present* components, mirroring
//! Elixir's sparse-map representation. Consumers `match` on the
//! `Component` variant; the compiler enforces exhaustiveness, which
//! turns the three-path-parity promise of `docs/descr-cleanup.md`
//! into a load-bearing invariant rather than an aspiration.

// API-in-waiting: the Component types and most View methods are
// unused until fz-68x.{3..7} migrate consumers. Allow dead_code only
// on this section; do not propagate the allow upward.

use crate::types::{MapKey, TypeVarId};

use super::bits::{BasicBits, F64Bits};
use super::conj::Conj;
use super::descr::Descr;
use super::lit_set::{AtomSet, FloatSet, IntSet, LiteralSet, VarSet};
use super::sigs::{ArrowSig, ClosureLit, ListSig, MapSig, ResourceSig, TupleSig};

/// The kinds of value-sets a `Descr` admits, one per axis. Yielded by
/// `Descr::components()`. Only present (non-empty) axes appear.
#[allow(dead_code)]
#[derive(Clone, Copy)]
pub(crate) enum Component<'a> {
    Basic(BasicBits),
    Atoms(AtomView<'a>),
    Ints(IntView<'a>),
    Floats(FloatView<'a>),
    Opaques(OpaqueView<'a>),
    Brands(BrandView<'a>),
    Vars(VarView<'a>),
    Tuples(TupleView<'a>),
    Lists(ListView<'a>),
    Resources(ResourceView<'a>),
    Funcs(FuncView<'a>),
    Maps(MapView<'a>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AtomTypeTest {
    None,
    Any,
    Finite(Vec<String>),
    Cofinite,
}

// ---- literal-set views ----

#[derive(Clone, Copy)]
pub(crate) struct AtomView<'a> {
    pub(super) inner: &'a AtomSet,
}

impl<'a> AtomView<'a> {
    pub(crate) fn is_any(&self) -> bool {
        self.inner.is_any()
    }
    pub(crate) fn cofinite(&self) -> bool {
        self.inner.cofinite
    }
    /// Iterator over finite members; `None` if the set is cofinite ("any
    /// atom except these"). Callers that handle cofinite check
    /// `cofinite()` first.
    pub(crate) fn finite(&self) -> Option<impl Iterator<Item = &'a str> + 'a> {
        if self.inner.cofinite {
            None
        } else {
            Some(self.inner.set.iter().map(String::as_str))
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct IntView<'a> {
    pub(super) inner: &'a IntSet,
}

impl<'a> IntView<'a> {
    /// Returns the single integer if this view is exactly `{n}`; `None`
    /// otherwise (any, cofinite, multi-element, or empty).
    pub(crate) fn singleton(&self) -> Option<i64> {
        if !self.inner.cofinite && self.inner.set.len() == 1 {
            self.inner.set.iter().next().copied()
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct FloatView<'a> {
    pub(super) inner: &'a FloatSet,
}

impl<'a> FloatView<'a> {
    /// Returns the single F64Bits if this view is exactly `{b}`; `None`
    /// otherwise. Bit-level precision — callers wanting `f64` call `.get()`.
    pub(crate) fn singleton(&self) -> Option<F64Bits> {
        if !self.inner.cofinite && self.inner.set.len() == 1 {
            self.inner.set.iter().next().copied()
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
#[allow(dead_code)]
pub(crate) struct OpaqueView<'a> {
    pub(super) inner: &'a LiteralSet<String>,
}

impl<'a> OpaqueView<'a> {
    /// fz-swt.6 — if this view names exactly one opaque type (the common
    /// case for an opaque-alias value), return its qualified tag.
    /// Returns `None` for cofinite sets (`Descr::any()`'s opaques axis is
    /// "every opaque", not a substitutable pattern) and for empty / many-
    /// tag sets. Consumers pair this with
    /// `crate::type_expr::opaque_owner_module` to discover the declaring
    /// module for visibility gating.
    #[allow(dead_code)] // exercised via Descr::as_opaque_singleton in tests; .8 wires it into typing.
    pub(crate) fn singleton(&self) -> Option<&'a str> {
        if !self.inner.cofinite && self.inner.set.len() == 1 {
            self.inner.set.iter().next().map(String::as_str)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
#[allow(dead_code)]
pub(crate) struct BrandView<'a> {
    pub(super) inner: &'a LiteralSet<String>,
}

impl<'a> BrandView<'a> {
    /// fz-axu.2 (K1) — if this view names exactly one brand tag (the
    /// common case for a freshly minted brand value), return its
    /// qualified name. Returns `None` for cofinite sets and for empty
    /// or many-tag sets. Consumers (K4 visibility gating, K5 erasure)
    /// pair this with brand_inners to resolve the underlying Descr.
    #[allow(dead_code)] // K3 wires this into brand-mint typing.
    pub(crate) fn singleton(&self) -> Option<&'a str> {
        if !self.inner.cofinite && self.inner.set.len() == 1 {
            self.inner.set.iter().next().map(String::as_str)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct VarView<'a> {
    pub(super) inner: &'a VarSet,
}

impl<'a> VarView<'a> {
    /// Named finite var ids; None if cofinite (e.g. `Descr::any()`'s vars
    /// axis is "every var" — not a substitutable pattern).
    pub(crate) fn finite(&self) -> Option<impl Iterator<Item = TypeVarId> + 'a> {
        if self.inner.cofinite {
            None
        } else {
            Some(self.inner.set.iter().copied())
        }
    }
    /// Count of named finite var ids; None if cofinite. Used by the
    /// most-specific-wins ordering in spec dispatch.
    pub(crate) fn finite_len(&self) -> Option<usize> {
        if self.inner.cofinite {
            None
        } else {
            Some(self.inner.set.len())
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct ResourceView<'a> {
    pub(super) inner: &'a [Conj<ResourceSig>],
}

impl<'a> ResourceView<'a> {
    pub(crate) fn payload_type(&self) -> Descr {
        let mut acc = Descr::none();
        for conj in self.inner {
            if !conj.neg.is_empty() {
                return Descr::any();
            }
            if conj.pos.is_empty() {
                return Descr::any();
            }
            let mut payload: Option<Descr> = None;
            for sig in &conj.pos {
                payload = Some(match payload {
                    Some(prev) => prev.intersect(&sig.payload),
                    None => (*sig.payload).clone(),
                });
            }
            acc = acc.union(&payload.unwrap_or_else(Descr::any));
        }
        acc
    }
}

// ---- structural views ----
//
// Each wraps a `&[Conj<Sig>]` slice but exposes only View methods. The
// DNF / clause representation is private to types.rs; consumers ask
// "what arities does this admit?", "project element i of arity-n
// tuples", "what's the joined element type?", etc.

#[derive(Clone, Copy)]
pub(crate) struct TupleView<'a> {
    pub(super) inner: &'a [Conj<TupleSig>],
}

impl<'a> TupleView<'a> {
    /// True iff this view admits every tuple (single `Conj::top()` clause).
    /// True iff any clause contains a negation. Consumers that don't yet
    /// support DNF with negations check this to preserve invariants.
    pub(crate) fn has_negations(&self) -> bool {
        self.inner.iter().any(|c| !c.neg.is_empty())
    }
    /// Distinct arities admitted by any positive clause. Empty iterator
    /// if the only clauses are negations-of-top.
    pub(crate) fn arities(&self) -> impl Iterator<Item = usize> {
        let mut seen = std::collections::BTreeSet::new();
        for conj in self.inner {
            for sig in &conj.pos {
                seen.insert(sig.elems.len());
            }
        }
        seen.into_iter()
    }
    /// Project the full element-Descr vector at the given arity, following
    /// Castagna DNF semantics (fz-dhd): positive sigs within a Conj are
    /// intersected per-position; results union across Conjs. Returns None
    /// if no Conj has the requested arity. The returned length equals `arity`.
    pub(crate) fn project_all(&self, arity: usize) -> Option<Vec<Descr>> {
        let mut comps = vec![Descr::none(); arity];
        let mut found = false;
        for conj in self.inner {
            let mut clause_comps: Option<Vec<Descr>> = None;
            for sig in &conj.pos {
                if sig.elems.len() != arity {
                    continue;
                }
                clause_comps = Some(match clause_comps {
                    None => sig.elems.clone(),
                    Some(prev) => prev
                        .iter()
                        .zip(sig.elems.iter())
                        .map(|(p, s)| p.intersect(s))
                        .collect(),
                });
            }
            if let Some(cs) = clause_comps {
                for i in 0..arity {
                    comps[i] = comps[i].union(&cs[i]);
                }
                found = true;
            }
        }
        if found { Some(comps) } else { None }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct ListView<'a> {
    pub(super) inner: &'a [Conj<ListSig>],
}

impl<'a> ListView<'a> {
    /// Element type across all positive list clauses, following fz-dhd
    /// DNF semantics: sigs within a Conj are intersected; results union
    /// across Conjs. For `list(int) & list(any)` (one Conj, two sigs),
    /// the element is `int ∩ any = int`, not `int ∪ any = any`. Exact empty
    /// lists contribute no element evidence, so their projection is bottom.
    pub(crate) fn element_type(&self) -> Descr {
        let mut elem = Descr::none();
        let mut found = false;
        for conj in self.inner {
            let mut clause_elem: Option<Descr> = None;
            for sig in &conj.pos {
                let Some(sig_elem) = &sig.elem else {
                    continue;
                };
                clause_elem = Some(match clause_elem {
                    None => sig_elem.as_ref().clone(),
                    Some(prev) => prev.intersect(sig_elem),
                });
            }
            if let Some(e) = clause_elem {
                elem = elem.union(&e);
                found = true;
            }
        }
        if found { elem } else { Descr::none() }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct FuncView<'a> {
    pub(super) inner: &'a [Conj<ArrowSig>],
}

impl<'a> FuncView<'a> {
    /// True iff any clause carries negations. Consumers that don't yet
    /// support DNF with negations check this to preserve invariants
    /// (ir_planner closure dispatch falls back to `any` when this is true).
    pub(crate) fn has_negations(&self) -> bool {
        self.inner.iter().any(|c| !c.neg.is_empty())
    }
    /// True iff every clause has at least one positive arrow signature.
    /// When false, some clause is purely negative (e.g. `not arrow(...)`),
    /// which ir_planner treats as "give up; fall through to `any`."
    pub(crate) fn all_clauses_have_pos(&self) -> bool {
        self.inner.iter().all(|c| !c.pos.is_empty())
    }
    /// Arrows admitted by positive clauses. Each arrow exposes args/ret
    /// via `ArrowView`. Negations are not yielded — consumers reasoning
    /// about full DNF use the algebra (intersect/diff), not this view.
    pub(crate) fn arrows(&self) -> impl Iterator<Item = ArrowView<'a>> {
        self.inner
            .iter()
            .flat_map(|conj| conj.pos.iter().map(|sig| ArrowView { inner: sig }))
    }
    /// Arrows from clauses that have NO negations. Used by sites that
    /// want to enumerate dispatch targets safely: a clause `arrow1 ∧
    /// ¬arrow2` is too complex to flatten without losing the negation,
    /// so the consumer skips it entirely.
    #[allow(dead_code)]
    pub(crate) fn arrows_from_pure_clauses(&self) -> impl Iterator<Item = ArrowView<'a>> {
        self.inner
            .iter()
            .filter(|c| c.neg.is_empty())
            .flat_map(|conj| conj.pos.iter().map(|sig| ArrowView { inner: sig }))
    }
    /// Distinct arities admitted by positive clauses.
    #[allow(dead_code)]
    pub(crate) fn arities(&self) -> impl Iterator<Item = usize> {
        let mut seen = std::collections::BTreeSet::new();
        for conj in self.inner {
            for sig in &conj.pos {
                seen.insert(sig.args.len());
            }
        }
        seen.into_iter()
    }
}

#[derive(Clone, Copy)]
pub(crate) struct ArrowView<'a> {
    inner: &'a ArrowSig,
}

impl<'a> ArrowView<'a> {
    pub(crate) fn args(&self) -> &'a [Descr] {
        &self.inner.args
    }
    pub(crate) fn ret(&self) -> &'a Descr {
        &self.inner.ret
    }
    pub(crate) fn closure_lit(&self) -> Option<&'a ClosureLit> {
        self.inner.lit.as_ref()
    }
}

#[derive(Clone, Copy)]
pub(crate) struct MapView<'a> {
    pub(super) inner: &'a [Conj<MapSig>],
}

impl<'a> MapView<'a> {
    /// Look up the value type for `key` across all positive map clauses,
    /// following Castagna open-map semantics (fz-dhd): pos sigs within a
    /// Conj are intersected (a missing field in a sig contributes
    /// `any | nil` because open maps don't constrain unmentioned keys);
    /// results union across Conjs. A Conj with `pos.is_empty()` (e.g. a
    /// pure negation of map-top) contributes `any | nil`. Returns None
    /// if the view has no clauses.
    pub(crate) fn lookup(&self, key: &MapKey) -> Option<Descr> {
        if self.inner.is_empty() {
            return None;
        }
        let mut found = false;
        let mut acc = Descr::none();
        for conj in self.inner {
            if conj.pos.is_empty() {
                acc = acc.union(&Descr::any()).union(&Descr::nil());
                found = true;
                continue;
            }
            let mut clause_v: Option<Descr> = None;
            for sig in &conj.pos {
                let sig_v = match sig.fields.get(key) {
                    Some(t) => t.clone(),
                    None => Descr::any().union(&Descr::nil()),
                };
                clause_v = Some(match clause_v {
                    None => sig_v,
                    Some(prev) => prev.intersect(&sig_v),
                });
            }
            if let Some(v) = clause_v {
                acc = acc.union(&v);
                found = true;
            }
        }
        if found { Some(acc) } else { None }
    }
}
