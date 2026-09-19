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
//! `Conj::pos` and `Conj::neg` grow the same way inside the clause product, so
//! `A ∧ B` and `B ∧ A` split one overload in two.
//!
//! Sorting every axis at intern removes both degrees of freedom: a clause
//! becomes a function of its factor set and an axis a function of its clause
//! set, so same-denotation unions carved the same way intern to ONE `Ty`.
//!
//! This storage order is private to descriptor canonicalization. Production
//! activation and artifact order instead use `Types::cmp_activation_ty`, whose
//! field precedence is the established activation order. The test-only
//! `Types::cmp_ty` accessor exists solely to prove those two relations remain
//! distinct.
//!
//! # What the order is
//!
//! Lexicographic over the raw stored structure, in the spirit of the canonical
//! rendering in [`super::canon`] but not identical to it: the closure literal
//! leads an arrow here while canon renders it last, and canon normalizes
//! before rendering while this walks the descriptor as stored. Compared in
//! place rather than materialized as text, so a comparison stops at the first
//! difference and nothing is allocated. Two `Ty`s are compared by their
//! descriptors, recursively. The pair memo records each normalized pair while
//! it is being compared; re-entering that pair finds no further structural
//! difference, and a completed pair reuses its verdict. Thus the walk
//! terminates for regular trees as well as acyclic ones. `Types` memoizes
//! repeated activation-order verdicts; storage canonicalization remains a
//! direct walk.
//!
//! # Why it is injective
//!
//! `cmp_ty(a, b)` is `Equal` exactly when `a == b`: the interner is keyed by
//! `Descr`, so distinct acyclic ids have structurally distinct descriptors, and
//! the comparison below reads every structural field. Distinct cyclic ids can
//! have the same finite unfolding, so a completed structural tie falls back to
//! the root identity order as well. Injectivity is what makes the sort
//! canonical — if two DIFFERENT clauses could tie, the sort would leave them in
//! arrival order and hand the schedule its dependence right back.
//!
//! # Why storage order reads nothing outside the descriptor
//!
//! The storage relation is a function of the descriptor's own bytes, the ids it
//! names, and its completed-tie identity order, and of nothing mutable. That
//! is what lets the interner trust its index: a descriptor already in the index
//! was normalized once, and because nothing the normal form depends on can
//! change afterwards, the id it was given then is still the id it would be
//! given now. So a hit is answered without normalizing at all.
//!
//! The one place that could have broken it is the closure literal. A callable
//! can be interned before its owner exists, and `Types::define_callable_origin`
//! registers the typed origin later; ordering two literals by their registered
//! origins would make the stored clause order — and with it the descriptor's
//! normal form — move the moment a registration landed, so one denotation
//! would take one id before the registration and another after. Storage
//! therefore orders two literals by `FnId` alone. `for_activation` keeps the
//! origin order, and it can: it runs only over activation surfaces, where
//! every literal's origin is registered and asserted to be.
//!
//! [`OrderPurpose`] is what holds that apart: the registration map lives in
//! the `Activation` variant, so the storage relation has no origins in hand
//! and could not read one if a future comparison wanted to.
//!
//! What that costs is stated plainly: the stored order of a funcs axis is the
//! order its callables were minted in, not their source order. Nothing reads
//! it as source order — canon sorts its own rendered clause texts, activation
//! keys go through `cmp_activation_ty`, and every other reader folds or maps
//! the axis rather than selecting by position.
//!
//! # Version stability, and the one residual
//!
//! Structural address vars order by their `AddrStep` path rather than by the
//! id interned for it, so a schedule flip cannot move them.
//!
//! The residual: a FREE type var (bit 31 clear — a closure-surface var, a
//! resolver encounter var, a typedef param) has no structural name, so a tie
//! broken by two free vars is broken by mint order, which is schedule-dependent.
//! A closure literal's `FnId` is now a second such tie-break. Both are narrow
//! — they decide an order only between clauses that agree on everything up to
//! a pair of ids — but they are real, and they are where this module cannot
//! promise confluence across arenas.

use std::cell::{Cell, RefCell};
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

/// The shared typed origin of every callable a closure literal can name, keyed
/// by the `FnId` the literal carries. `World` registers it when minting ids.
/// Only the activation relation reads it; storage order deliberately does not.
pub(super) type CallableOrigins = HashMap<FnId, Arc<fz_runtime::function_denotation::FunctionDenotation>>;

/// A signature that knows its own place in the canonical order. One impl per
/// DNF axis, so the clause and axis walks below are written once.
trait OrderedSig: Sized {
    fn cmp_sig(order: &ClauseOrder<'_>, a: &Self, b: &Self) -> Ordering;
}

pub(super) struct ClauseOrder<'a> {
    cx: TyCtx<'a>,
    purpose: OrderPurpose<'a>,
    comparison_active: Cell<bool>,
    pairs: RefCell<HashMap<(Ty, Ty), PairComparison>>,
}

#[derive(Clone, Copy)]
enum PairComparison {
    InFlight,
    Complete(Ordering),
}

/// Which of the two relations this comparator is, and — for the activation
/// one — the registration state it is allowed to read. Storage carries no
/// origins at all, so the relation the interner's index depends on cannot
/// reach registration state even by accident.
#[derive(Clone, Copy)]
enum OrderPurpose<'a> {
    Storage,
    Activation(&'a CallableOrigins),
}

impl<'a> ClauseOrder<'a> {
    pub(super) fn new(cx: TyCtx<'a>) -> Self {
        Self {
            cx,
            purpose: OrderPurpose::Storage,
            comparison_active: Cell::new(false),
            pairs: RefCell::default(),
        }
    }

    /// The activation-facing relation leads with callable construction. Direct
    /// call surfaces are ordered separately as `ActivationSignature`s, so a
    /// literal's owner identity must not be recovered from its value type's
    /// template variables.
    pub(super) fn for_activation(cx: TyCtx<'a>, origins: &'a CallableOrigins) -> Self {
        Self {
            cx,
            purpose: OrderPurpose::Activation(origins),
            comparison_active: Cell::new(false),
            pairs: RefCell::default(),
        }
    }

    /// Put every DNF axis of `d` in canonical order, factors first.
    ///
    /// Factors have to lead: a clause compares by its stored factor lists, so
    /// the clause sort is a function of the clause SET only once each clause is
    /// a function of its own factor set.
    pub(super) fn sort_axes(&self, d: &mut Descr) {
        self.sort_axis(&mut d.tuples);
        self.sort_axis(&mut d.lists);
        self.sort_axis(&mut d.resources);
        self.sort_axis(&mut d.funcs);
        self.sort_axis(&mut d.maps);
    }

    fn sort_axis<T: OrderedSig + PartialEq>(&self, clauses: &mut [Conj<T>]) {
        for clause in clauses.iter_mut() {
            self.sort_factors(&mut clause.pos);
            self.sort_factors(&mut clause.neg);
        }
        if clauses.len() < 2 {
            return;
        }
        clauses.sort_by(|a, b| self.cmp_conj(a, b));
    }

    /// One side of one clause, in canonical order with duplicates collapsed
    /// (`A ∧ A = A`, `¬A ∧ ¬A = ¬A`). The order is injective — it reads every
    /// field of a signature — so equal factors land adjacent and `dedup`
    /// removes exactly the repeats.
    fn sort_factors<T: OrderedSig + PartialEq>(&self, factors: &mut Vec<T>) {
        if factors.len() < 2 {
            return;
        }
        factors.sort_by(|a, b| T::cmp_sig(self, a, b));
        factors.dedup();
    }

    // ------------------------------------------------------------------
    // Types
    // ------------------------------------------------------------------

    pub(super) fn cmp_ty(&self, a: Ty, b: Ty) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        if self.comparison_active.get() {
            return self.cmp_ty_structural(a, b);
        }

        self.pairs.borrow_mut().clear();
        self.comparison_active.set(true);
        let structural = self.cmp_ty_structural(a, b);
        self.comparison_active.set(false);
        if structural == Ordering::Equal {
            a.cmp(&b)
        } else {
            structural
        }
    }

    fn cmp_ty_structural(&self, a: Ty, b: Ty) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        let (low, high, reversed) = if a < b { (a, b, false) } else { (b, a, true) };
        let normalized = self.cmp_ty_structural_normalized(low, high);
        if reversed { normalized.reverse() } else { normalized }
    }

    fn cmp_ty_structural_normalized(&self, low: Ty, high: Ty) -> Ordering {
        if let Some(comparison) = self.pairs.borrow().get(&(low, high)).copied() {
            return match comparison {
                PairComparison::InFlight => Ordering::Equal,
                PairComparison::Complete(order) => order,
            };
        }

        self.pairs.borrow_mut().insert((low, high), PairComparison::InFlight);
        let order = self.cmp_descr(self.cx.descr(&low), self.cx.descr(&high));
        self.pairs
            .borrow_mut()
            .insert((low, high), PairComparison::Complete(order));
        order
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
        match self.purpose {
            OrderPurpose::Storage => lex(a, b, |x, y| self.cmp_ty(*x, *y)),
            OrderPurpose::Activation(_) => lex_elements_first(a, b, |x, y| self.cmp_ty(*x, *y)),
        }
    }

    // ------------------------------------------------------------------
    // Clauses
    // ------------------------------------------------------------------

    /// A clause compares by its POSITIVE factors, then its negative ones. Both
    /// lists are in canonical order by the time this runs, so the verdict is a
    /// function of the two clauses' factor sets.
    fn cmp_conj<T: OrderedSig>(&self, a: &Conj<T>, b: &Conj<T>) -> Ordering {
        lex(&a.pos, &b.pos, |x, y| T::cmp_sig(self, x, y))
            .then_with(|| lex(&a.neg, &b.neg, |x, y| T::cmp_sig(self, x, y)))
    }

    fn cmp_axis<T: OrderedSig>(&self, a: &[Conj<T>], b: &[Conj<T>]) -> Ordering {
        match self.purpose {
            OrderPurpose::Storage => lex(a, b, |x, y| self.cmp_conj(x, y)),
            OrderPurpose::Activation(_) => lex_elements_then_longer(a, b, |x, y| self.cmp_conj(x, y)),
        }
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
        match self.purpose {
            OrderPurpose::Storage => self
                .cmp_lit(a.lit.as_ref(), b.lit.as_ref())
                .then_with(|| self.cmp_tys(&a.args, &b.args))
                .then_with(|| self.cmp_ty(a.ret, b.ret)),
            OrderPurpose::Activation(_) => self
                .cmp_lit(a.lit.as_ref(), b.lit.as_ref())
                .then_with(|| self.cmp_tys(&a.args, &b.args))
                .then_with(|| self.cmp_ty(a.ret, b.ret)),
        }
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

    /// Activation identities order only by their registered typed origins.
    /// Storage canonicalization orders by the id alone, which is the only
    /// reading available to it: registration happens AFTER a literal can be
    /// interned, so reading an origin here would make a stored clause order —
    /// and with it a descriptor's normal form — change under the arena. The
    /// storage relation holds no origins to read, so that is settled by the
    /// type rather than by this match.
    fn cmp_callable(&self, a: FnId, b: FnId) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        let OrderPurpose::Activation(origins) = self.purpose else {
            return a.0.cmp(&b.0);
        };
        let a_origin = origins.get(&a).expect("activation callable has a registered origin");
        let b_origin = origins.get(&b).expect("activation callable has a registered origin");
        let order = a_origin.semantic_cmp(b_origin);
        assert_ne!(
            order,
            Ordering::Equal,
            "distinct activation callables must have distinct typed origins"
        );
        order
    }

    fn cmp_map_sig(&self, a: &MapSig, b: &MapSig) -> Ordering {
        a.tag
            .cmp(&b.tag)
            .then_with(|| a.fields.len().cmp(&b.fields.len()))
            .then_with(|| {
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

/// Ordinary lexicographic order: compare shared elements first and use arity
/// only when one slice is an exact prefix of the other. Activation surfaces
/// historically expose arguments in this order; storage clauses use `lex`
/// above because canonicalization intentionally groups arities first.
fn lex_elements_first<T>(a: &[T], b: &[T], mut cmp: impl FnMut(&T, &T) -> Ordering) -> Ordering {
    first_difference(a.iter().zip(b.iter()).map(|(x, y)| cmp(x, y))).then_with(|| a.len().cmp(&b.len()))
}

/// Lexicographic over the shared elements, and where one slice is an exact
/// prefix of the other the LONGER one sorts first.
///
/// This is the tie-break `cmp_activation_tys` falls through to, and through
/// `canonically_order_separated_neighbours` it is what picks the seat of a pair
/// of dispatch arms no value can reach both of. That seat is a determinism
/// choice and decides nothing else -- neither where a value lands, which
/// separation already settled, nor how many questions it answers, which
/// `dispatch_columns` settles by asking the separating input first. Flipping
/// the direction below moves no surface-membership census row.
fn lex_elements_then_longer<T>(a: &[T], b: &[T], mut cmp: impl FnMut(&T, &T) -> Ordering) -> Ordering {
    first_difference(a.iter().zip(b.iter()).map(|(x, y)| cmp(x, y))).then_with(|| b.len().cmp(&a.len()))
}

/// The first non-`Equal` verdict, or `Equal` if there is none. The iterator is
/// lazy, so the walk stops at the first difference.
fn first_difference(verdicts: impl Iterator<Item = Ordering>) -> Ordering {
    verdicts.into_iter().find(|o| o.is_ne()).unwrap_or(Ordering::Equal)
}
