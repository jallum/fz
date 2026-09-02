//! Canonical clause order: a total order on DNF clauses, so a descriptor's
//! clause list is a function of what it SAYS and not of how it was built.
//!
//! A DNF axis denotes a SET of clauses but is stored as a `Vec`, and every
//! producer appends: `dnf_union` concatenates its two arguments, and
//! `dnf_intersect_with` walks the clause product in arrival order. So `A ∨ B`
//! and `B ∨ A` reach the persistence boundary as two different vectors, hash to
//! two different `Descr`s, and are handed two different `Ty`s for one set of
//! values. That is not cosmetic. A `Ty` IS the identity of a specialization —
//! `ActivationKey::from_inputs` keys on one — so a callee gets one body per
//! ARRIVAL ORDER of the joins that reached it, and the addresser numbers tuple
//! alternatives by clause position (`AddrStep::Variant(k)`), so the variable
//! names inside a canonical arrow move with the scheduler too.
//!
//! Sorting every axis at intern removes that degree of freedom: the clause list
//! becomes a function of the clause MULTISET, so same-denotation unions carved
//! the same way intern to ONE `Ty`.
//!
//! The order has a second consumer, reached through `Types::cmp_ty`: the
//! artifact's final-packaging sorts (fz-kdt.101). They used to compare raw `Ty`
//! ids, which is interning order, so a re-ordered pull renumbered
//! `entry x<N>` / `construction=w<N>` on artifacts that said the same thing.
//! The two residuals below bound what that buys: schedule-independence WITHIN
//! one compile, which is what those sorts need.
//!
//! # What the order is
//!
//! Lexicographic over the raw stored structure, in the spirit of the canonical
//! rendering in [`super::canon`] but not identical to it: the closure literal
//! leads an arrow here while canon renders it last, and canon normalizes
//! before rendering while this walks the descriptor as stored. Compared in
//! place rather than materialized as text, so a comparison stops at the first
//! difference and nothing is allocated or cached. Two `Ty`s are compared by their descriptors,
//! recursively; the recursion terminates because a descriptor can only name
//! `Ty`s that were interned before it, so every step moves to strictly smaller
//! ids.
//!
//! # Why it is injective
//!
//! `cmp_ty(a, b)` is `Equal` exactly when `a == b`: the interner is keyed by
//! `Descr`, so distinct ids have structurally distinct descriptors, and the
//! comparison below reads every structural field. Injectivity is what makes the
//! sort canonical — if two DIFFERENT clauses could tie, the sort would leave
//! them in arrival order and hand the schedule its dependence right back.
//!
//! # Version stability, and the one residual
//!
//! A closure literal orders by its owner's stable LABEL (`Module.name/arity`),
//! never by its raw `FnId`, which is a mint-order index that shifts whenever the
//! source gains or loses a function. Named functions therefore order stably
//! across unrelated edits in OTHER files; a lambda's label embeds its byte
//! span, so an edit above it in the SAME file still relabels it -- the
//! stability bought here is cross-file and within-compile, not universal. Structural address vars likewise order by
//! their `AddrStep` path rather than by the id interned for it.
//!
//! The residual: a FREE type var (bit 31 clear — a closure-surface var, a
//! resolver encounter var, a typedef param) has no structural name, so a tie
//! broken by two free vars is broken by mint order, which is schedule-dependent.
//! It is narrow — it decides an order only between two clauses that agree on
//! everything up to a pair of free var ids — but it is real, and it is the one
//! place this module cannot promise confluence.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Arc;

use crate::finite_set::FiniteSet;
use crate::fz_ir::FnId;

use super::addressed::address_path;
use super::conj::Conj;
use super::descr::Descr;
use super::sigs::{ArrowSig, ClosureLit, ListSig, MapSig, ResourceSig, TupleSig};
use super::{Ty, TyCtx, TypeVarId};

/// The stable label of every callable a closure literal can name, keyed by the
/// `FnId` the literal carries. `World` fills this in as it mints function ids;
/// a `Types` built standalone (unit tests) leaves it empty and falls back to id
/// order, which is deterministic within one instance but not across versions.
pub(super) type CallableLabels = HashMap<FnId, Arc<str>>;

/// A signature that knows its own place in the canonical order. One impl per
/// DNF axis, so the clause and axis walks below are written once.
trait OrderedSig: Sized {
    fn cmp_sig(order: &ClauseOrder<'_>, a: &Self, b: &Self) -> Ordering;
}

pub(super) struct ClauseOrder<'a> {
    cx: TyCtx<'a>,
    labels: &'a CallableLabels,
}

impl<'a> ClauseOrder<'a> {
    pub(super) fn new(cx: TyCtx<'a>, labels: &'a CallableLabels) -> Self {
        Self { cx, labels }
    }

    /// Put every DNF axis of `d` in canonical order.
    pub(super) fn sort_axes(&self, d: &mut Descr) {
        self.sort_axis(&mut d.tuples);
        self.sort_axis(&mut d.lists);
        self.sort_axis(&mut d.resources);
        self.sort_axis(&mut d.funcs);
        self.sort_axis(&mut d.maps);
    }

    fn sort_axis<T: OrderedSig>(&self, clauses: &mut [Conj<T>]) {
        if clauses.len() < 2 {
            return;
        }
        clauses.sort_by(|a, b| self.cmp_conj(a, b));
    }

    // ------------------------------------------------------------------
    // Types
    // ------------------------------------------------------------------

    pub(super) fn cmp_ty(&self, a: Ty, b: Ty) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        self.cmp_descr(self.cx.descr(&a), self.cx.descr(&b))
    }

    fn cmp_descr(&self, a: &Descr, b: &Descr) -> Ordering {
        a.basic
            .cmp(&b.basic)
            .then_with(|| a.atoms.cmp(&b.atoms))
            .then_with(|| a.opaques.cmp(&b.opaques))
            .then_with(|| a.brands.cmp(&b.brands))
            .then_with(|| self.cmp_vars(&a.vars, &b.vars))
            .then_with(|| self.cmp_axis(&a.tuples, &b.tuples))
            .then_with(|| self.cmp_axis(&a.lists, &b.lists))
            .then_with(|| self.cmp_axis(&a.resources, &b.resources))
            .then_with(|| self.cmp_axis(&a.funcs, &b.funcs))
            .then_with(|| self.cmp_axis(&a.maps, &b.maps))
    }

    pub(super) fn cmp_tys(&self, a: &[Ty], b: &[Ty]) -> Ordering {
        lex(a, b, |x, y| self.cmp_ty(*x, *y))
    }

    // ------------------------------------------------------------------
    // Clauses
    // ------------------------------------------------------------------

    /// A clause compares by its POSITIVE factors, then its negative ones — and
    /// within each, in STORED order.
    ///
    /// Sorting the factors first would be the wrong move: two clauses that hold
    /// the same factors in different orders are not equal under the `PartialEq`
    /// that `dedupe_exact_clauses` and the interner index use, so making them
    /// TIE here would hand the survivor back to arrival order. Intra-clause
    /// factor order is a second non-canonical dimension (`Conj::pos` grows in
    /// `dnf_intersect_with` arrival order); this module does not touch it, and
    /// two factor-permuted clauses simply stay distinct.
    fn cmp_conj<T: OrderedSig>(&self, a: &Conj<T>, b: &Conj<T>) -> Ordering {
        lex(&a.pos, &b.pos, |x, y| T::cmp_sig(self, x, y))
            .then_with(|| lex(&a.neg, &b.neg, |x, y| T::cmp_sig(self, x, y)))
    }

    fn cmp_axis<T: OrderedSig>(&self, a: &[Conj<T>], b: &[Conj<T>]) -> Ordering {
        lex(a, b, |x, y| self.cmp_conj(x, y))
    }

    // ------------------------------------------------------------------
    // Signatures
    // ------------------------------------------------------------------

    fn cmp_list_sig(&self, a: &ListSig, b: &ListSig) -> Ordering {
        a.empty.cmp(&b.empty).then_with(|| match (a.elem, b.elem) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(x), Some(y)) => self.cmp_ty(x, y),
        })
    }

    /// The closure literal leads, so a union of many callables over one surface
    /// lands grouped by callable rather than interleaved by arrow shape.
    fn cmp_arrow_sig(&self, a: &ArrowSig, b: &ArrowSig) -> Ordering {
        self.cmp_lit(a.lit.as_ref(), b.lit.as_ref())
            .then_with(|| self.cmp_tys(&a.args, &b.args))
            .then_with(|| self.cmp_ty(a.ret, b.ret))
    }

    fn cmp_lit(&self, a: Option<&ClosureLit>, b: Option<&ClosureLit>) -> Ordering {
        match (a, b) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(x), Some(y)) => match (x.fn_id, y.fn_id) {
                (None, None) => Ordering::Equal,
                (None, Some(_)) => Ordering::Less,
                (Some(_), None) => Ordering::Greater,
                (Some(a), Some(b)) => self.cmp_callable(a, b),
            }
            .then_with(|| x.kind.cmp(&y.kind))
            .then_with(|| self.cmp_tys(&x.captures, &y.captures)),
        }
    }

    /// Two callables order by their stable labels. `function_label` is
    /// injective, so the trailing id comparison should be unreachable for
    /// distinct labelled callables; it is there because the order must stay
    /// TOTAL even if that ever stopped being true, and it is what an unlabelled
    /// `Types` (unit tests) falls back to.
    fn cmp_callable(&self, a: FnId, b: FnId) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        match (self.labels.get(&a), self.labels.get(&b)) {
            (Some(x), Some(y)) => x.cmp(y).then_with(|| a.0.cmp(&b.0)),
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (None, None) => a.0.cmp(&b.0),
        }
    }

    fn cmp_map_sig(&self, a: &MapSig, b: &MapSig) -> Ordering {
        a.fields.len().cmp(&b.fields.len()).then_with(|| {
            first_difference(
                a.fields
                    .iter()
                    .zip(b.fields.iter())
                    .map(|((ka, va), (kb, vb))| ka.cmp(kb).then_with(|| self.cmp_ty(*va, *vb))),
            )
        })
    }

    // ------------------------------------------------------------------
    // Variables
    // ------------------------------------------------------------------

    fn cmp_vars(&self, a: &FiniteSet<TypeVarId>, b: &FiniteSet<TypeVarId>) -> Ordering {
        a.cofinite
            .cmp(&b.cofinite)
            .then_with(|| a.values.len().cmp(&b.values.len()))
            .then_with(|| first_difference(a.values.iter().zip(b.values.iter()).map(|(x, y)| self.cmp_var(*x, *y))))
    }

    /// A structural address orders by its PATH (`[Param(1), Field(0)]`), which
    /// the program's shape decides; the id interned for that path is first-use
    /// order and would not survive a schedule flip. A free var has no such name
    /// — that is the residual this module documents at the top.
    fn cmp_var(&self, a: TypeVarId, b: TypeVarId) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        match (address_path(self.cx.addresses, a), address_path(self.cx.addresses, b)) {
            (Some(x), Some(y)) => x.cmp(y),
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (None, None) => a.0.cmp(&b.0),
        }
    }
}

impl OrderedSig for TupleSig {
    fn cmp_sig(order: &ClauseOrder<'_>, a: &Self, b: &Self) -> Ordering {
        order.cmp_tys(&a.elems, &b.elems)
    }
}

impl OrderedSig for ListSig {
    fn cmp_sig(order: &ClauseOrder<'_>, a: &Self, b: &Self) -> Ordering {
        order.cmp_list_sig(a, b)
    }
}

impl OrderedSig for ResourceSig {
    fn cmp_sig(order: &ClauseOrder<'_>, a: &Self, b: &Self) -> Ordering {
        order.cmp_ty(a.payload, b.payload)
    }
}

impl OrderedSig for ArrowSig {
    fn cmp_sig(order: &ClauseOrder<'_>, a: &Self, b: &Self) -> Ordering {
        order.cmp_arrow_sig(a, b)
    }
}

impl OrderedSig for MapSig {
    fn cmp_sig(order: &ClauseOrder<'_>, a: &Self, b: &Self) -> Ordering {
        order.cmp_map_sig(a, b)
    }
}

/// Shorter first, then elementwise. Length leads because it settles most pairs
/// without touching an element at all.
fn lex<T>(a: &[T], b: &[T], mut cmp: impl FnMut(&T, &T) -> Ordering) -> Ordering {
    a.len()
        .cmp(&b.len())
        .then_with(|| first_difference(a.iter().zip(b.iter()).map(|(x, y)| cmp(x, y))))
}

/// The first non-`Equal` verdict, or `Equal` if there is none. The iterator is
/// lazy, so the walk stops at the first difference.
fn first_difference(verdicts: impl Iterator<Item = Ordering>) -> Ordering {
    verdicts.into_iter().find(|o| o.is_ne()).unwrap_or(Ordering::Equal)
}
