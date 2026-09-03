//! Interned set-theoretic type implementation.
//!
//! Its `Descr` is private here, and every structural child is a `Ty` allocated
//! by the owning `Types` instance.

mod addressed;
mod arrow_match;
mod bits;
mod canon;
mod closure_surface_var;
mod conj;
mod descr;
mod dnf;
mod emptiness;
mod format;
mod order;
mod sigs;

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use crate::finite_set::FiniteSet;
use crate::fz_ir::FnId;
use crate::runtime_type_predicate::{
    CallableShape, CallableShapes, ListShape, ListShapes, RuntimeTypePredicate, TupleShapes,
};

use super::keying::DispatchDemand;
use super::protocol::{ProtocolDomainObligation, is_protocol_domain_tag};
use crate::type_expr::opaque_owner_module;
use crate::types::{
    ClosureTypes as SharedClosureTypes, RenderTypes as SharedRenderTypes, Types as SharedTypes,
    VisibilityTypes as SharedVisibilityTypes,
};
use bits::BasicBits;

pub use crate::types::{
    CallableClause, CallableValueKind, ClosureLitInfo, ClosureTarget, MapKey, Nominals, OpaqueVisibilityError, Sigma,
    TypeVarId,
};

pub use arrow_match::ArrowMatch;

pub(crate) use canon::TyCanon;

use addressed::AddrStep;
#[cfg(test)]
pub(crate) use closure_surface_var::{ClosureSurfacePos, decode_closure_surface_var};
use closure_surface_var::{closure_ret_var_id, closure_var_id};
use conj::Conj;
use descr::Descr;
use dnf::{dnf_intersect_with, tuple_clause_subsumed};
use sigs::{ArrowSig, ClosureLit, ListSig, MergeSig, PosMeet, ResourceSig, TupleSig};

/// One closure-literal arrow as [`Types::lit_arrow_shapes`] reports it:
/// `(brand, captures, args, ret)`, the brand `None` for an anonymous literal.
pub(crate) type LitArrowShape = (Option<FnId>, Vec<Ty>, Vec<Ty>, Ty);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Ty(u32);

impl Ty {
    /// The raw interned handle, valid only within the `Types` instance that
    /// minted it (see `ModuleId`/`FunctionId`/`RootId::as_u32`). Telemetry
    /// projections render this instead of `Types::display` — display is
    /// measured non-injective and would conflate distinct types that happen
    /// to render the same.
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Default)]
pub struct Types {
    interner: TypeInterner,
    comparisons: RefCell<ComparisonCache>,
    /// Memoized `value_lane_repr`: the transport-lane representative of a type.
    /// A derived fact about each type, computed once rather than on every lane.
    value_lane_reprs: HashMap<Ty, Ty>,
    /// Interned structural addresses (`a0`, `a1_0`, `r0`, ...). Keyed by the
    /// address path so the same address always yields the same `TypeVarId`,
    /// making the addressed arrow canonical by construction. See `addressed`.
    address_vars: HashMap<Vec<addressed::AddrStep>, TypeVarId>,
    /// The reverse of `address_vars`: the path behind each address id, indexed
    /// by the id's dense slot (its tag bit masked off). Lets display render an
    /// address structurally (`a1_0`, `r0`) instead of as a bare `αN`.
    address_paths: Vec<Vec<addressed::AddrStep>>,
    /// The stable label of every callable a closure literal can name. A raw
    /// `FnId` is a mint-order index, so it cannot decide canonical clause order
    /// (`order`); the owner names each callable as it mints the id.
    callable_labels: order::CallableLabels,
    /// Correlated-input row sets widened to their column-wise join since the
    /// last drain, because they crossed `ACTIVATION_INPUT_ROW_BUDGET`
    /// (fz-0xp). `World::take_activation_input_collapses` is the drain and
    /// `ExecutionContext::complete_job` the reporter.
    ///
    /// The tally lives on the type store because that is the only handle the
    /// collapse site has: it fires inside
    /// `ActivationInputAlternatives`' monotone join, whose
    /// `JoinContribution::Ctx` is `Types` — an associated TYPE that no
    /// borrowed sink can ride without a GAT on every implementor — and
    /// measurement says the join is where every collapse in the corpus
    /// actually happens (`push_row`, the one path that could return a count to
    /// its caller, produced none of the 28/30 the lenses recorded before
    /// fz-kdt.106). Owning it here makes the ledger per-`World` by
    /// construction, so an undrained collapse dies with the `World` that
    /// produced it instead of leaking into the next reader. Threading a
    /// first-class sink through the join stays fz-0xp's.
    activation_input_collapses: u64,
}

#[derive(Default)]
struct TypeInterner {
    arena: Vec<Descr>,
    index: HashMap<Descr, Ty>,
}

#[derive(Default)]
struct ComparisonCache {
    values: HashMap<ComparisonKey, bool>,
    semantic_order: HashMap<SemanticOrderKey, std::cmp::Ordering>,
    semantic_order_checked: HashSet<Ty>,
    hits: usize,
    misses: usize,
    #[cfg(test)]
    semantic_order_hits: usize,
    #[cfg(test)]
    semantic_order_misses: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ComparisonKey {
    Empty(Ty),
    Subtype(Ty, Ty),
    Disjoint(Ty, Ty),
    Equivalent(Ty, Ty),
    /// `Types::row_column_dominates`. NOT symmetric: the two positions mean
    /// different things, so this key is never built through `symmetric_key`.
    RowColumnDominates(Ty, Ty),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum SemanticOrderOperation {
    ActivationArrow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct SemanticOrderKey {
    operation: SemanticOrderOperation,
    low: Ty,
    high: Ty,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ComparisonCacheStats {
    pub entries: usize,
    pub hits: usize,
    pub misses: usize,
    pub semantic_order_entries: usize,
    pub semantic_order_hits: usize,
    pub semantic_order_misses: usize,
}

#[derive(Clone, Copy)]
pub(super) struct TyCtx<'a> {
    arena: &'a [Descr],
    /// The address reverse table (path per address id), so display can render a
    /// structural address as `a1_0`/`r0`. Empty for the interner-internal ctx,
    /// which only resolves descriptors and never renders.
    addresses: &'a [Vec<addressed::AddrStep>],
}

impl<'a> TyCtx<'a> {
    fn descr(&self, t: &Ty) -> &'a Descr {
        self.arena
            .get(t.0 as usize)
            .unwrap_or_else(|| panic!("unknown interned type id {}", t.0))
    }

    /// Render one type variable: a structural address (`a0`, `a1_0`, `r0`) when
    /// its id carries the address tag, else a free var `αN` (fz-hwn.27.13).
    fn render_var(&self, id: TypeVarId) -> String {
        match addressed::address_path(self.addresses, id) {
            Some(path) => addressed::format_address(path),
            None => id.to_string(),
        }
    }
}

impl TypeInterner {
    fn intern(&mut self, d: Descr) -> Ty {
        if let Some(ty) = self.index.get(&d) {
            return *ty;
        }
        #[cfg(debug_assertions)]
        self.debug_assert_dnf_axes_hygienic(&d);
        let raw = self.arena.len();
        assert!(u32::try_from(raw).is_ok(), "type interner exhausted ids");
        let ty = Ty(raw as u32);
        self.arena.push(d.clone());
        self.index.insert(d, ty);
        ty
    }

    fn ctx(&self) -> TyCtx<'_> {
        TyCtx {
            arena: &self.arena,
            addresses: &[],
        }
    }

    fn descr(&self, t: &Ty) -> &Descr {
        self.ctx().descr(t)
    }

    /// The interned-DNF invariant: a descriptor entering the arena never
    /// carries a duplicate clause on any axis, nor a provably-empty or
    /// subsumed tuple clause. `Types::intern` establishes it by canonicalizing
    /// the axes; this sweep verifies it for every intern in debug builds, so
    /// any construction route leaking garbage clauses fails loudly instead of
    /// accumulating.
    #[cfg(debug_assertions)]
    fn debug_assert_dnf_axes_hygienic(&self, d: &Descr) {
        let cx = self.ctx();
        for (i, c) in d.tuples.iter().enumerate() {
            let mut memo = emptiness::Memo::default();
            debug_assert!(
                !emptiness::tuple_clause_empty(cx, c, &mut memo),
                "interned descr carries a provably-empty tuple clause"
            );
            for (j, other) in d.tuples.iter().enumerate() {
                debug_assert!(
                    i == j || !tuple_clause_subsumed(c, other, |x, y| { cx.descr(x).is_subtype(cx, cx.descr(y)) }),
                    "interned descr carries a subsumed (or duplicate) tuple clause"
                );
            }
        }
        debug_assert_no_exact_duplicates(&d.lists, "lists");
        debug_assert_no_exact_duplicates(&d.resources, "resources");
        debug_assert_no_exact_duplicates(&d.funcs, "funcs");
        debug_assert_no_exact_duplicates(&d.maps, "maps");
    }
}

/// `A ∨ A = A` on the four axes that carry no absorption pass of their own.
///
/// The tuples axis gets the stronger emptiness+subsumption treatment; the rest
/// get idempotence, which is the rule the ACTIVATION KEY depends on. A key is
/// built by erasing what the key language cannot address — closure brands
/// above all — and erasure runs IN PLACE, so a union that legitimately kept one
/// clause per brand becomes `A ∨ A` the moment the brands go. Without this
/// collapse `funcs = [A, A]` interns as a different `Ty` than `funcs = [A]`,
/// the key stops being a join homomorphism, and a callsite reached down two
/// rows publishes an edge naming neither activation its walk actually read
/// (fz-kdt.80).
///
/// First occurrence wins, so the canonical order the `order` pass just imposed
/// survives this filter — which is the whole reason the two compose. The
/// comparator here stays `PartialEq`, deliberately: it is the very equality the
/// interner index is keyed on, so collapsing exactly these pairs is what makes
/// `A ∨ A` and `A` reach one `Ty`. Anything coarser would fold clauses the index
/// still tells apart.
fn dedupe_exact_clauses<T: PartialEq>(clauses: &mut Vec<Conj<T>>) {
    if clauses.len() < 2 {
        return;
    }
    let mut kept = 0;
    for i in 0..clauses.len() {
        if clauses[..kept].contains(&clauses[i]) {
            continue;
        }
        clauses.swap(kept, i);
        kept += 1;
    }
    clauses.truncate(kept);
}

#[cfg(debug_assertions)]
fn debug_assert_no_exact_duplicates<T: PartialEq>(clauses: &[Conj<T>], axis: &str) {
    for (i, c) in clauses.iter().enumerate() {
        debug_assert!(
            !clauses[..i].contains(c),
            "interned descr carries a duplicate clause on the {axis} axis"
        );
    }
}

impl Types {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record one correlated-input row set widened past
    /// `ACTIVATION_INPUT_ROW_BUDGET`. See `activation_input_collapses`.
    pub(crate) fn note_activation_input_collapse(&mut self) {
        self.activation_input_collapses += 1;
    }

    /// Take the collapses recorded since the last drain. Ask
    /// [`World::take_activation_input_collapses`] — the drain is the `World`'s
    /// to offer, and this is where the count is kept.
    pub(crate) fn take_activation_input_collapses(&mut self) -> u64 {
        std::mem::take(&mut self.activation_input_collapses)
    }

    pub fn repeat(&mut self, ty: Ty, n: usize) -> Vec<Ty> {
        vec![ty; n]
    }

    pub fn bool_lit(&mut self, value: bool) -> Ty {
        self.atom_lit(if value { "true" } else { "false" })
    }

    pub fn cpointer(&mut self) -> Ty {
        self.opaque_of("cpointer")
    }

    pub fn differs_only_nominally(&self, a: &Ty, b: &Ty) -> bool {
        self.is_disjoint(a, b) && !self.is_value_disjoint(a, b)
    }

    pub fn key_is_strictly_more_specific(&self, lhs: &[Ty], rhs: &[Ty]) -> bool {
        lhs.len() == rhs.len()
            && lhs
                .iter()
                .zip(rhs.iter())
                .fold((true, false), |(all_le, any_strict), (l, r)| {
                    (all_le && self.is_subtype(l, r), any_strict || !self.is_subtype(r, l))
                })
                == (true, true)
    }

    pub fn as_map_key(&self, a: &Ty) -> Option<MapKey> {
        self.as_int_singleton(a)
            .map(MapKey::Int)
            .or_else(|| self.as_atom_singleton(a).map(MapKey::Atom))
    }

    /// The persistence boundary, in three passes that each leave the next one's
    /// precondition intact.
    ///
    /// ORDER first (fz-kdt.105): every axis goes into canonical clause order, so
    /// a descriptor's clause list is a function of its clause set rather than of
    /// the arrival order that built it. It has to lead, because the absorption
    /// below picks the survivor of a mutually-subsuming pair by ARRIVAL — sort
    /// afterwards and the schedule would still be choosing which clause lives.
    ///
    /// ABSORPTION and IDEMPOTENCE follow, and both are order-preserving filters
    /// (`canonicalize_tuple_axis` keeps survivors in input order;
    /// `dedupe_exact_clauses` keeps the first occurrence), so what reaches the
    /// interner index is still sorted.
    ///
    /// One pass suffices because the composition is idempotent: re-interning an
    /// already-interned descriptor sorts an already-sorted list to itself, finds
    /// no empty or subsumed tuple clause left to drop and no exact duplicate
    /// left to collapse, and so hashes to the descriptor already in the index.
    fn intern(&mut self, mut d: Descr) -> Ty {
        self.order_clauses(&mut d);
        self.canonicalize_tuple_axis(&mut d);
        dedupe_exact_clauses(&mut d.lists);
        dedupe_exact_clauses(&mut d.resources);
        dedupe_exact_clauses(&mut d.funcs);
        dedupe_exact_clauses(&mut d.maps);
        self.interner.intern(d)
    }

    fn order_clauses(&self, d: &mut Descr) {
        self.clause_order().sort_axes(d);
    }

    fn clause_order(&self) -> order::ClauseOrder<'_> {
        order::ClauseOrder::new(self.ctx(), &self.callable_labels)
    }

    fn activation_order(&self) -> order::ClauseOrder<'_> {
        order::ClauseOrder::for_activation(self.ctx(), &self.callable_labels)
    }

    /// Test evidence for the storage-canonical relation. Production consumers
    /// use the operation-specific activation relation below; storage order is
    /// otherwise private to DNF canonicalization.
    #[cfg(test)]
    pub(crate) fn cmp_ty(&self, a: Ty, b: Ty) -> std::cmp::Ordering {
        self.clause_order().cmp_ty(a, b)
    }

    /// Total typed order for activation-bearing identities. Unlike storage
    /// clause order, callable arrows compare arguments and return before their
    /// literal identity, preserving the established observable precedence
    /// without rendering either type. The interned descriptors and callable
    /// labels are immutable, so one normalized pair has one verdict for this
    /// `Types`/`World` lifetime and the reverse direction reuses its inverse.
    pub(crate) fn cmp_activation_ty(&self, a: Ty, b: Ty) -> std::cmp::Ordering {
        self.assert_semantic_order_labels_registered(a);
        self.assert_semantic_order_labels_registered(b);
        if a == b {
            return std::cmp::Ordering::Equal;
        }
        let (low, high, reversed) = if a < b { (a, b, false) } else { (b, a, true) };
        let key = SemanticOrderKey {
            operation: SemanticOrderOperation::ActivationArrow,
            low,
            high,
        };
        let normalized = if let Some(order) = self.comparisons.borrow_mut().semantic_order_hit(key) {
            order
        } else {
            let order = self.activation_order().cmp_ty(low, high);
            self.comparisons.borrow_mut().semantic_order_miss(key, order);
            order
        };
        if reversed { normalized.reverse() } else { normalized }
    }

    /// Lexicographic [`Types::cmp_activation_ty`], with length breaking prefix ties.
    pub(crate) fn cmp_activation_tys(&self, a: &[Ty], b: &[Ty]) -> std::cmp::Ordering {
        for (left, right) in a.iter().zip(b) {
            let order = self.cmp_activation_ty(*left, *right);
            if order != std::cmp::Ordering::Equal {
                return order;
            }
        }
        a.len().cmp(&b.len())
    }

    fn assert_semantic_order_labels_registered(&self, root: Ty) {
        if self.comparisons.borrow().semantic_order_checked.contains(&root) {
            return;
        }
        let seen = self.activation_reachable(root, |ty| {
            let d = self.descr(&ty);
            for sig in d.funcs.iter().flat_map(|conj| conj.pos.iter().chain(conj.neg.iter())) {
                if let Some(lit) = &sig.lit
                    && let Some(fn_id) = lit.fn_id
                {
                    assert!(
                        self.callable_labels.contains_key(&fn_id),
                        "activation arrow names unregistered callable {}",
                        fn_id.0
                    );
                }
            }
        });
        self.comparisons.borrow_mut().semantic_order_checked.extend(seen);
    }

    fn activation_reachable(&self, root: Ty, mut visit: impl FnMut(Ty)) -> HashSet<Ty> {
        let mut pending = vec![root];
        let mut seen = HashSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            visit(ty);
            let d = self.descr(&ty);
            for sig in d.tuples.iter().flat_map(|conj| conj.pos.iter().chain(conj.neg.iter())) {
                pending.extend(sig.elems.iter().copied());
            }
            for sig in d.lists.iter().flat_map(|conj| conj.pos.iter().chain(conj.neg.iter())) {
                pending.extend(sig.elem);
            }
            for sig in d
                .resources
                .iter()
                .flat_map(|conj| conj.pos.iter().chain(conj.neg.iter()))
            {
                pending.push(sig.payload);
            }
            for sig in d.funcs.iter().flat_map(|conj| conj.pos.iter().chain(conj.neg.iter())) {
                pending.extend(sig.args.iter().copied());
                pending.push(sig.ret);
                if let Some(lit) = &sig.lit {
                    pending.extend(lit.captures.iter().copied());
                }
            }
            for sig in d.maps.iter().flat_map(|conj| conj.pos.iter().chain(conj.neg.iter())) {
                pending.extend(sig.fields.values().copied());
            }
        }
        seen
    }

    /// The persistence boundary keeps the tuples axis of every
    /// interned descriptor canonical: provably-empty clauses are dropped
    /// (`A ∨ ∅ = A`) and subsumed clauses are absorbed (`A ⊆ B ⇒ A ∨ B = B`,
    /// restoring the fz-et8 absorption lost in the compiler2 port). Both drop
    /// rules preserve the denoted set exactly, so emptiness and subtyping
    /// answers are unchanged — only the clause list shrinks. Running once at
    /// intern covers every construction route (union, intersect, difference,
    /// substitution) with one pass, and keeps garbage from accumulating across
    /// fixpoint iterations or doubling `dnf_neg` factors downstream.
    fn canonicalize_tuple_axis(&self, d: &mut Descr) {
        if d.tuples.is_empty() {
            return;
        }
        let clauses = std::mem::take(&mut d.tuples);
        let mut out: Vec<Conj<TupleSig>> = Vec::with_capacity(clauses.len());
        for c in clauses {
            if self.tuple_clause_provably_empty(&c) {
                continue;
            }
            let cached_subtype = |x: &Ty, y: &Ty| self.is_subtype(x, y);
            if out.iter().any(|kept| tuple_clause_subsumed(&c, kept, cached_subtype)) {
                continue;
            }
            out.retain(|kept| !tuple_clause_subsumed(kept, &c, cached_subtype));
            out.push(c);
        }
        d.tuples = out;
    }

    fn tuple_clause_provably_empty(&self, c: &Conj<TupleSig>) -> bool {
        // Plain single-positive clauses (the overwhelmingly common shape) are
        // empty iff a coordinate is — decidable through the memoized
        // comparison cache without cloning descriptors.
        if let ([p], []) = (c.pos.as_slice(), c.neg.as_slice()) {
            return p.elems.iter().any(|e| self.is_empty(e));
        }
        let mut memo = emptiness::Memo::default();
        emptiness::tuple_clause_empty(self.ctx(), c, &mut memo)
    }

    fn ctx(&self) -> TyCtx<'_> {
        TyCtx {
            arena: &self.interner.arena,
            addresses: &self.address_paths,
        }
    }

    fn descr(&self, t: &Ty) -> &Descr {
        self.interner.descr(t)
    }

    fn cached_comparison(&self, key: ComparisonKey, compute: impl FnOnce(&Self) -> bool) -> bool {
        if let Some(result) = self.comparisons.borrow_mut().hit(key) {
            return result;
        }
        let result = compute(self);
        self.comparisons.borrow_mut().miss(key, result);
        result
    }

    fn symmetric_key(kind: fn(Ty, Ty) -> ComparisonKey, a: Ty, b: Ty) -> ComparisonKey {
        if a <= b { kind(a, b) } else { kind(b, a) }
    }

    /// The transport-lane representative of `ty`. A `Value` lane is one boxed
    /// reference word, so a list's empty/non-empty refinement and element type
    /// do not change its representation: every list-shaped type shares one lane
    /// (the precise type still lives in `value_types` for codegen). Returning
    /// one canonical lane is what lets a clause whose return is a narrower list
    /// (`[int]`) than the function's joined return (`[int] | []`) deliver into
    /// the same lane, so destination-passing folds instead of re-materializing.
    /// Memoized — a derived fact about the type, not recomputed per lane.
    pub fn value_lane_repr(&mut self, ty: Ty) -> Ty {
        if let Some(&cached) = self.value_lane_reprs.get(&ty) {
            return cached;
        }
        let any = self.any();
        let list_top = self.list(any);
        let repr = if !self.is_empty(&ty) && self.is_subtype(&ty, &list_top) {
            list_top
        } else if self.descr(&ty).is_pure_callable() {
            // A callable value is one word — a code pointer or a closure ref —
            // regardless of its signature, identity, or captures. Collapse every
            // callable to one lane, exactly as lists collapse to `list(any)`, so
            // two representations of the same callable (e.g. an opaque join of
            // same-signature functions, addressed vs not) never split across
            // lanes (fz-hwn.27.12). The contract stays out-of-band in boundaries.
            self.intern(Descr::fun_top())
        } else {
            ty
        };
        self.value_lane_reprs.insert(ty, repr);
        repr
    }

    /// Every type the arena holds, in mint order.
    ///
    /// Comparison-only: the canon faithfulness ratchet sweeps the whole
    /// interned population, and needs the census rather than any particular id.
    #[cfg(test)]
    pub(crate) fn interned_tys(&self) -> Vec<Ty> {
        (0..self.interner.arena.len() as u32).map(Ty).collect()
    }

    #[cfg(test)]
    pub(crate) fn activation_order_evidence_for_test(&self, left: Ty, right: Ty) -> String {
        format!(
            "left={left:?} right={right:?}; left_descr={:?}; right_descr={:?}; \
             activation=({:?}, {:?}); storage=({:?}, {:?}); address_paths={:?}; callable_labels={:?}",
            self.descr(&left),
            self.descr(&right),
            self.cmp_activation_ty(left, right),
            self.cmp_activation_ty(right, left),
            self.cmp_ty(left, right),
            self.cmp_ty(right, left),
            self.address_paths,
            self.callable_labels,
        )
    }

    #[cfg(test)]
    pub(crate) fn activation_reachable_tys(&self, root: Ty) -> HashSet<Ty> {
        self.activation_reachable(root, |_| {})
    }

    /// The two identity inventories demand-formula evaluation must leave
    /// untouched: interned type descriptors and interned structural addresses.
    #[cfg(test)]
    pub(crate) fn identity_inventory(&self) -> (usize, usize) {
        (self.interner.arena.len(), self.address_paths.len())
    }

    #[cfg(test)]
    pub(crate) fn comparison_cache_stats(&self) -> ComparisonCacheStats {
        let cache = self.comparisons.borrow();
        ComparisonCacheStats {
            entries: cache.values.len(),
            hits: cache.hits,
            misses: cache.misses,
            semantic_order_entries: cache.semantic_order.len(),
            semantic_order_hits: cache.semantic_order_hits,
            semantic_order_misses: cache.semantic_order_misses,
        }
    }
}

impl ComparisonCache {
    fn hit(&mut self, key: ComparisonKey) -> Option<bool> {
        let result = self.values.get(&key).copied();
        if result.is_some() {
            self.hits += 1;
        }
        result
    }

    fn miss(&mut self, key: ComparisonKey, result: bool) {
        self.misses += 1;
        self.values.insert(key, result);
    }

    fn semantic_order_hit(&mut self, key: SemanticOrderKey) -> Option<std::cmp::Ordering> {
        let result = self.semantic_order.get(&key).copied();
        #[cfg(test)]
        if result.is_some() {
            self.semantic_order_hits += 1;
        }
        result
    }

    fn semantic_order_miss(&mut self, key: SemanticOrderKey, result: std::cmp::Ordering) {
        #[cfg(test)]
        {
            self.semantic_order_misses += 1;
        }
        self.semantic_order.insert(key, result);
    }
}

impl Types {
    pub(crate) fn close_bounds(&mut self, bounds: &HashMap<TypeVarId, Ty>, seed: &Sigma<Ty>) -> Sigma<Ty> {
        let mut closed = seed.clone();
        let mut vars = bounds.keys().copied().collect::<Vec<_>>();
        vars.sort();
        for _ in 0..bounds.len() {
            let mut changed = false;
            for var in &vars {
                if seed.contains_key(var) {
                    continue;
                }
                let bound = bounds[var];
                let next = self.instantiate(&bound, &closed);
                if self.has_vars(&next) {
                    continue;
                }
                if closed.get(var) != Some(&next) {
                    closed.insert(*var, next);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        closed
    }

    pub fn any(&mut self) -> Ty {
        self.intern(Descr::any())
    }

    pub fn none(&mut self) -> Ty {
        self.intern(Descr::none())
    }

    pub fn nil(&mut self) -> Ty {
        self.intern(Descr::nil())
    }

    pub fn bool(&mut self) -> Ty {
        self.intern(Descr::bool_t())
    }

    pub fn int(&mut self) -> Ty {
        self.intern(Descr::int())
    }

    /// Numeric literals are VALUES, not types: the lattice deliberately
    /// cannot express a numeric singleton (Elixir's descr draws the same
    /// line). A literal in type position means its kind.
    pub fn int_lit(&mut self, _n: i64) -> Ty {
        self.int()
    }

    pub fn float(&mut self) -> Ty {
        self.intern(Descr::float())
    }

    /// See `int_lit`: a float literal in type position means `float()`.
    pub fn float_lit(&mut self, _f: f64) -> Ty {
        self.float()
    }

    pub fn atom(&mut self) -> Ty {
        self.intern(Descr::atom_top())
    }

    pub fn atom_lit(&mut self, name: &str) -> Ty {
        self.intern(Descr::atom_lit(name))
    }

    pub fn type_var(&mut self, id: TypeVarId) -> Ty {
        self.intern(Descr::var(id))
    }

    pub fn resource(&mut self, payload: Ty) -> Ty {
        self.intern(Descr::resource_of(self.ctx(), payload))
    }

    pub fn arrow(&mut self, args: &[Ty], ret: Ty) -> Ty {
        self.intern(Descr::arrow(args.iter().copied(), ret))
    }

    /// Project the parameter (input) side of an arrow type immutably. This is
    /// the read path for `ActivationKey::inputs`: the key stores its canonical
    /// inputs as the params of an interned arrow, and consumers recover them
    /// here without needing `&mut` on the interner.
    pub fn arrow_params(&self, arrow: &Ty) -> Vec<Ty> {
        self.descr(arrow)
            .pure_arrow()
            .map(|sig| sig.args.clone())
            .unwrap_or_default()
    }

    /// Arity of an arrow's parameter side without cloning — the read path for
    /// `ActivationKey::input_len` at the many call sites that need only the
    /// input count.
    pub fn arrow_arity(&self, arrow: &Ty) -> usize {
        self.descr(arrow).pure_arrow().map_or(0, |sig| sig.args.len())
    }

    /// Project the result side of an arrow immutably. `None` when `arrow` is not
    /// a pure arrow. Pairs with `arrow_params` to decompose an interned arrow back
    /// into its (params, result) — the read path for `ResolvedSpec` after the
    /// resolver addresses a spec scope whole (fz-hwn.27.14).
    pub fn arrow_result(&self, arrow: &Ty) -> Option<Ty> {
        self.descr(arrow).pure_arrow().map(|sig| sig.ret)
    }

    pub fn tuple(&mut self, elems: &[Ty]) -> Ty {
        self.intern(Descr::tuple_of(elems.iter().copied()))
    }

    pub fn empty_list(&mut self) -> Ty {
        self.intern(Descr::empty_list())
    }

    pub fn list(&mut self, elem: Ty) -> Ty {
        self.intern(Descr::list_of(self.ctx(), elem))
    }

    pub fn non_empty_list(&mut self, elem: Ty) -> Ty {
        self.intern(Descr::non_empty_list_of(self.ctx(), elem))
    }

    pub fn map(&mut self, fields: &[(MapKey, Ty)]) -> Ty {
        self.intern(Descr::map_of(fields.iter().cloned()))
    }

    pub fn str_t(&mut self) -> Ty {
        self.intern(Descr::str_t())
    }

    pub fn map_top(&mut self) -> Ty {
        self.intern(Descr::map_top())
    }

    pub fn mint_brand(&mut self, inner: Ty, name: &str) -> Ty {
        let mut d = self.descr(&inner).clone();
        d.brands = FiniteSet::lit(name.to_string());
        self.intern(d)
    }

    pub fn opaque_of(&mut self, name: &str) -> Ty {
        self.intern(Descr::opaque_of(name))
    }

    pub fn brand_of(&mut self, name: &str) -> Ty {
        self.intern(Descr::brand_of(name))
    }

    pub fn list_element_type(&mut self, a: &Ty) -> Ty {
        let d = {
            let cx = self.ctx();
            list_element_type(cx, cx.descr(a))
        };
        self.intern(d)
    }

    pub fn has_list_shape(&self, a: &Ty) -> bool {
        !self.descr(a).lists.is_empty()
    }

    pub fn resource_payload_type(&mut self, a: &Ty) -> Option<Ty> {
        let d = {
            let cx = self.ctx();
            resource_payload_type(cx, cx.descr(a))?
        };
        Some(self.intern(d))
    }

    pub fn mint_owned_resource_aliases(&mut self, a: Ty, owner: &str, opaque_inners: &HashMap<String, Ty>) -> Ty {
        let candidates = opaque_inners
            .iter()
            .filter_map(|(tag, inner)| {
                let tag_owner = opaque_owner_module(tag)?;
                (tag_owner == owner).then(|| (tag.clone(), self.descr(inner).clone()))
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return a;
        }
        let d = mint_owned_resource_aliases_descr(self.ctx(), self.descr(&a), &candidates);
        self.intern(d)
    }

    pub fn tuple_projections(&mut self, a: &Ty, arity: usize) -> Vec<Ty> {
        let ds = {
            let cx = self.ctx();
            tuple_projections(cx, cx.descr(a), arity)
        };
        ds.into_iter().map(|d| self.intern(d)).collect()
    }

    pub fn tuple_field_type(&mut self, a: &Ty, index: usize) -> Ty {
        let d = {
            let cx = self.ctx();
            tuple_field_type(cx, cx.descr(a), index)
        };
        self.intern(d)
    }

    pub fn max_tuple_arity(&self, a: &Ty) -> usize {
        self.descr(a).max_tuple_arity()
    }

    pub fn refine_map_field(&mut self, a: &Ty, key: &MapKey, v: &Ty) -> Ty {
        let d = self.descr(a).refine_map_field(key, *v);
        self.intern(d)
    }

    pub fn map_field_lookup(&mut self, a: &Ty, key: &MapKey) -> Option<Ty> {
        let d = {
            let cx = self.ctx();
            map_field_lookup(cx, cx.descr(a), key)?
        };
        Some(self.intern(d))
    }

    pub fn map_known_keys(&self, a: &Ty) -> Vec<MapKey> {
        map_known_keys(self.descr(a))
    }

    /// Identity since numeric literal types left the lattice: there is
    /// nothing to widen. Kept for the shared `Types` trait until the old
    /// pipeline (which still carries literal types) retires.
    pub fn widen_for_recursive_spec_key(&mut self, a: &Ty) -> Ty {
        *a
    }

    pub fn refine_widen(&mut self, a: &Ty, b: &Ty) -> Ty {
        refine_widen(self, *a, *b)
    }

    pub fn convergence_class(&mut self, a: &Ty) -> Ty {
        let descr = self.descr(a).clone();
        if descr.as_pure_list(self.ctx()).is_some() {
            let any = self.any();
            self.list(any)
        } else if let Some(tuple) = descr.pure_tuple() {
            let elems = tuple
                .elems
                .iter()
                .map(|elem| self.convergence_class(elem))
                .collect::<Vec<_>>();
            self.tuple(&elems)
        } else if let Some(resource) = descr.pure_resource() {
            let payload = self.convergence_class(&resource.payload);
            self.resource(payload)
        } else if descr.is_pure_callable() {
            self.intern(Descr::fun_top())
        } else if let Some(map) = descr.pure_map() {
            let fields = map
                .fields
                .iter()
                .map(|(key, value)| (key.clone(), self.convergence_class(value)))
                .collect::<Vec<_>>();
            self.map(&fields)
        } else {
            *a
        }
    }

    /// The ADDRESSED convergence class of `ty` at structural address `path`: the
    /// same family collapse as [`convergence_class`], but a pure list's element
    /// and a pure callable become a RESOLVABLE address var at their structural
    /// address (`P_e`, `P`) rather than the `any`/`fun_top` fallback
    /// (fz-f98.14.10.2). Breadth is still one address per position, so the
    /// interner folds same-shape arrows to one key exactly as `list(any)` did and
    /// fz-y6w termination holds. Depth is capped: past `ADDRESS_COLLAPSE_DEPTH`
    /// nested addressing steps the element tops out at `any` (the earned depth ⊤)
    /// so a self-nesting list can never grow the address path without bound.
    fn convergence_class_at(&mut self, a: &Ty, path: &[AddrStep]) -> Ty {
        const ADDRESS_COLLAPSE_DEPTH: usize = 8;
        let descr = self.descr(a).clone();
        if descr.is_pure_list_family() {
            if path.len() >= ADDRESS_COLLAPSE_DEPTH {
                let any = self.any();
                return self.list(any);
            }
            let mut child = path.to_vec();
            child.push(AddrStep::Elem);
            let elem = self.address_var(&child);
            self.list(elem)
        } else if descr.is_pure_callable() {
            // A clause-less `fun_top` is the unresolvable fallback; the address
            // var keeps the slot resolvable (`has_vars` true) so the indirect
            // reducer still narrows at its call.
            self.address_var(path)
        } else if let Some(tuple) = descr.pure_tuple() {
            let elems = tuple
                .elems
                .iter()
                .enumerate()
                .map(|(j, elem)| {
                    let mut child = path.to_vec();
                    child.push(AddrStep::Field(j as u16));
                    self.convergence_class_at(elem, &child)
                })
                .collect::<Vec<_>>();
            self.tuple(&elems)
        } else if let Some(resource) = descr.pure_resource() {
            let payload = resource.payload;
            let mut child = path.to_vec();
            child.push(AddrStep::Payload);
            let payload = self.convergence_class_at(&payload, &child);
            self.resource(payload)
        } else if let Some(map) = descr.pure_map() {
            let fields = map
                .fields
                .iter()
                .enumerate()
                .map(|(j, (key, value))| {
                    let mut child = path.to_vec();
                    child.push(AddrStep::MapField(j as u16));
                    (key.clone(), self.convergence_class_at(value, &child))
                })
                .collect::<Vec<_>>();
            self.map(&fields)
        } else {
            *a
        }
    }

    /// Derive a recursive activation's dispatch KEY from its precise evidence
    /// arrow by widening every non-dispatch subtree to its convergence class, so
    /// the recursive ascent settles (fz-y6w bounded specialization:
    /// `list(int)` and `list(any)` share one recursive key). Dispatch demand is
    /// type-shaped: a tuple tag can remain precise while its payload collapses.
    ///
    /// This is ONE whole-arrow operation on the interned arrow (fz-hwn.27.7) — it
    /// replaces a per-input `convergence_class` pre-pass run before the inputs
    /// were addressed. The two agree because `convergence_class` only collapses
    /// pure lists (`list(τ) -> list(any)`), which is invariant under the
    /// variable-addressing `from_inputs` applies. The arrow remains the PRECISE
    /// evidence surface (carried by `ActivationInputs`); the collapse is a derived
    /// dispatch key, and key != evidence is intentional.
    pub(crate) fn convergence_collapse(&mut self, arrow: Ty, mask: &[DispatchDemand]) -> Ty {
        let Some(sig) = self.descr(&arrow).pure_arrow() else {
            return arrow;
        };
        let params = sig.args.clone();
        let ret = sig.ret;
        let collapsed = params
            .iter()
            .enumerate()
            .map(|(slot, param)| {
                let demand = mask.get(slot).unwrap_or(&DispatchDemand::Whole);
                let path = [AddrStep::Param(slot as u16)];
                self.convergence_collapse_ty(*param, demand, &path, true)
            })
            .collect::<Vec<_>>();
        self.arrow(&collapsed, ret)
    }

    /// The transported-callable key collapse (fz-6gb, fz-kdt.127): erase
    /// closure BRANDS from the arrow's non-dispatch slots, leaving everything
    /// else -- data types, callable surfaces, CAPTURE TYPES, dispatch-relevant
    /// slots -- exactly as the evidence stated it. Two closures of the same
    /// shape then key one activation of a function that only carries them,
    /// while a slot the function dispatches on keeps brand identity, and two
    /// capture types through one slot stay two keys because the body a key
    /// names grounds its callees' capture lanes. Unlike
    /// [`convergence_collapse`], no slot becomes an address var: this erasure
    /// is value-language throughout, so nothing key-shaped can leak into
    /// evidence.
    pub(crate) fn erase_transported_closure_identities(&mut self, arrow: Ty, mask: &[DispatchDemand]) -> Ty {
        let Some(sig) = self.descr(&arrow).pure_arrow() else {
            return arrow;
        };
        let params = sig.args.clone();
        let ret = sig.ret;
        let erased = params
            .iter()
            .enumerate()
            .map(|(slot, param)| match mask.get(slot).unwrap_or(&DispatchDemand::Whole) {
                DispatchDemand::Ignore => self.erase_closure_identity(param),
                _ => *param,
            })
            .collect::<Vec<_>>();
        self.arrow(&erased, ret)
    }

    pub(crate) fn convergence_collapse_evidence_inputs(&mut self, inputs: &[Ty], mask: &[DispatchDemand]) -> Vec<Ty> {
        inputs
            .iter()
            .enumerate()
            .map(|(slot, input)| {
                let demand = mask.get(slot).unwrap_or(&DispatchDemand::Whole);
                let path = [AddrStep::Param(slot as u16)];
                self.convergence_collapse_ty(*input, demand, &path, false)
            })
            .collect()
    }

    fn convergence_collapse_ty(
        &mut self,
        ty: Ty,
        demand: &DispatchDemand,
        path: &[AddrStep],
        collapse_concrete_ignored: bool,
    ) -> Ty {
        match demand {
            DispatchDemand::Ignore => {
                // KEY path (`collapse_concrete_ignored`) collapses an ignored slot
                // to its ADDRESSED convergence class: a pure list becomes
                // `list(<P_e var>)` and a pure callable an addressed surface var,
                // so the slot stays RESOLVABLE at its structural address instead of
                // bottoming out at `any`/`fun_top` (fz-f98.14.10.2). Breadth is
                // still var-bounded (one address per position) so fz-y6w
                // termination holds; depth is capped in `convergence_class_at`.
                // The EVIDENCE path keeps a var-bearing pure callable verbatim and
                // collapses every other var-bearing type to its (path-blind) class.
                if collapse_concrete_ignored {
                    self.convergence_class_at(&ty, path)
                } else if self.has_vars(&ty) && !self.descr(&ty).is_pure_callable() {
                    self.convergence_class(&ty)
                } else {
                    ty
                }
            }
            DispatchDemand::Whole => ty,
            DispatchDemand::TupleFields(fields) => {
                self.convergence_collapse_tuple_fields(ty, fields, path, collapse_concrete_ignored)
            }
            DispatchDemand::ListShape(elem_demand) => {
                self.convergence_collapse_list_shape(ty, elem_demand, path, collapse_concrete_ignored)
            }
        }
    }

    fn convergence_collapse_tuple_fields(
        &mut self,
        ty: Ty,
        fields: &BTreeMap<u32, DispatchDemand>,
        path: &[AddrStep],
        collapse_concrete_ignored: bool,
    ) -> Ty {
        let mut d = self.descr(&ty).clone();
        if d.tuples.is_empty() {
            return self.convergence_collapse_ignored_leaf(&ty, path, collapse_concrete_ignored);
        }
        // Discriminate tuple alternatives by their `Variant(k)` step exactly as
        // the canonical addresser does (`address_remap_children`): when a slot is
        // a union of more than one tuple alternative, each alternative's fields
        // address under `Variant(k)` so the collapsed arrow is CANONICALLY
        // addressed and round-trips through `from_inputs` by construction
        // (fz-hwn.27 — `address_inputs` is the single source of truth). Without
        // this the mint emits `a_..._j` where re-addressing emits `a_..._uk_j`,
        // so `executable_key_for_transport_position` reconstructs a distinct key
        // (fz-go4.18.3.2.1).
        let tuple_alternatives = d
            .tuples
            .iter()
            .map(|conj| conj.pos.len() + conj.neg.len())
            .sum::<usize>();
        let discriminate_tuple_alternatives = tuple_alternatives > 1;
        let mut tuple_alternative = 0_u16;
        for conj in &mut d.tuples {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                let alternative = tuple_alternative;
                tuple_alternative = tuple_alternative.saturating_add(1);
                for (index, elem) in sig.elems.iter_mut().enumerate() {
                    let demand = fields.get(&(index as u32)).unwrap_or(&DispatchDemand::Ignore);
                    let mut child = path.to_vec();
                    if discriminate_tuple_alternatives {
                        child.push(AddrStep::Variant(alternative));
                    }
                    child.push(AddrStep::Field(index as u16));
                    *elem = self.convergence_collapse_ty(*elem, demand, &child, collapse_concrete_ignored);
                }
            }
        }
        self.intern(d)
    }

    fn convergence_collapse_list_shape(
        &mut self,
        ty: Ty,
        elem_demand: &DispatchDemand,
        path: &[AddrStep],
        collapse_concrete_ignored: bool,
    ) -> Ty {
        let mut d = self.descr(&ty).clone();
        if d.lists.is_empty() {
            return self.convergence_collapse_ignored_leaf(&ty, path, collapse_concrete_ignored);
        }
        let mut child = path.to_vec();
        child.push(AddrStep::Elem);
        if collapse_concrete_ignored {
            let elem_descr = list_element_type(self.ctx(), &d);
            let elem = self.intern(elem_descr);
            let elem = self.convergence_collapse_ty(elem, elem_demand, &child, collapse_concrete_ignored);
            return self.list(elem);
        }
        for conj in &mut d.lists {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                if let Some(elem) = sig.elem {
                    sig.elem = Some(self.convergence_collapse_ty(elem, elem_demand, &child, collapse_concrete_ignored));
                }
            }
        }
        self.intern(d)
    }

    /// The collapse for an ignored slot that did not match the demanded shape:
    /// KEY path uses the addressed class (stays resolvable); EVIDENCE path the
    /// path-blind class (its earned ⊤).
    fn convergence_collapse_ignored_leaf(&mut self, ty: &Ty, path: &[AddrStep], collapse_concrete_ignored: bool) -> Ty {
        if collapse_concrete_ignored {
            self.convergence_class_at(ty, path)
        } else {
            self.convergence_class(ty)
        }
    }

    pub fn union(&mut self, a: Ty, b: Ty) -> Ty {
        let d = {
            let cx = self.ctx();
            cx.descr(&a).union(cx, cx.descr(&b))
        };
        self.intern(d)
    }

    pub fn intersect(&mut self, a: Ty, b: Ty) -> Ty {
        if a == b {
            return a;
        }
        if self.is_subtype(&a, &b) {
            return a;
        }
        if self.is_subtype(&b, &a) {
            return b;
        }
        let left = self.descr(&a).clone();
        let right = self.descr(&b).clone();
        let d = intersect_descr(self, &left, &right);
        self.intern(d)
    }

    #[cfg(test)]
    pub fn complement(&mut self, a: Ty) -> Ty {
        let d = self.descr(&a).neg();
        self.intern(d)
    }

    pub fn difference(&mut self, a: Ty, b: Ty) -> Ty {
        let d = self.descr(&a).diff(self.descr(&b));
        self.intern(d)
    }

    pub(crate) fn projection_alternatives(&mut self, ty: Ty) -> Vec<Ty> {
        let Some(alternatives) = self.descr(&ty).projection_alternatives() else {
            return vec![ty];
        };
        alternatives
            .into_iter()
            .map(|alternative| self.intern(alternative))
            .collect()
    }

    pub fn is_empty(&self, a: &Ty) -> bool {
        self.cached_comparison(ComparisonKey::Empty(*a), |types| {
            let cx = types.ctx();
            types.descr(a).is_empty(cx)
        })
    }

    #[cfg(test)]
    pub fn is_top(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_equiv(cx, &Descr::any())
    }

    pub fn is_subtype(&self, a: &Ty, b: &Ty) -> bool {
        if a == b {
            return true;
        }
        self.cached_comparison(ComparisonKey::Subtype(*a, *b), |types| {
            let cx = types.ctx();
            types.descr(a).is_subtype(cx, types.descr(b))
        })
    }

    pub fn is_disjoint(&self, a: &Ty, b: &Ty) -> bool {
        if a == b {
            return self.is_empty(a);
        }
        let key = Self::symmetric_key(ComparisonKey::Disjoint, *a, *b);
        self.cached_comparison(key, |types| {
            let cx = types.ctx();
            types.descr(a).intersect(types.descr(b)).is_empty(cx)
        })
    }

    pub fn is_value_disjoint(&self, a: &Ty, b: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).value_disjoint(cx, self.descr(b))
    }

    pub fn key_var_count(&self, key: &[Ty]) -> usize {
        key.iter().map(|t| self.descr(t).vars.finite_len().unwrap_or(0)).sum()
    }

    pub fn key_subsumes_with(&self, query: &Ty, key: &Ty, sigma: &mut Sigma<Ty>) -> bool {
        let qd = self.descr(query);
        let kd = self.descr(key);
        if kd.looks_full() {
            return true;
        }
        if let Some(alphas) = pure_var_ids(kd) {
            for alpha in alphas {
                match sigma.get(&alpha) {
                    None => {
                        sigma.insert(alpha, *query);
                    }
                    Some(existing) => {
                        let cx = self.ctx();
                        if !self.descr(existing).is_equiv(cx, qd) {
                            return false;
                        }
                    }
                }
            }
            return true;
        }
        let cx = self.ctx();
        qd.is_subtype(cx, kd)
    }

    /// True when the polymorphic argument list `template` subsumes `candidate`
    /// under one consistent variable substitution — i.e. `candidate` is an
    /// instantiation of `template`. A single substitution is threaded across
    /// every position, so a template variable that recurs (e.g. `[α, α]`) is
    /// instantiated only by argument lists whose corresponding positions are
    /// type-equivalent. This is the authoritative surface-subsumption fact;
    /// callers must not approximate it by checking each position in isolation,
    /// which would treat the two `α`s as independent and accept `[binary, int]`.
    pub fn key_list_subsumes(&self, candidate: &[Ty], template: &[Ty]) -> bool {
        if candidate.len() != template.len() {
            return false;
        }
        let mut sigma = Sigma::default();
        candidate
            .iter()
            .zip(template.iter())
            .all(|(query, key)| self.key_subsumes_with(query, key, &mut sigma))
    }

    /// True when any argument in `key` carries a (possibly nested) type variable.
    /// A ground argument list names a real runtime dispatch shape; a list with
    /// variables is an inference template, not a runtime fact.
    pub fn key_has_vars(&self, key: &[Ty]) -> bool {
        key.iter().any(|ty| self.has_vars(ty))
    }

    /// True when this type is a *value template* — a position whose runtime value
    /// has no concrete representation: a bare type variable, or a tuple one of
    /// whose fields is a bare type variable. Narrower than `has_vars`: a callable
    /// `(a)->a` or a `list(a)` is a representable value (a pointer / a list), so
    /// inner variables do not make the value itself a template. The cheap, sound,
    /// syntactic approximation of meaningful-variable groundness — the
    /// calculator's authority on "can this be a runtime value" (fz-hwn.23).
    pub fn is_value_template(&self, ty: &Ty) -> bool {
        let d = self.descr(ty);
        if pure_var_ids(d).is_some() {
            return true;
        }
        match d.pure_tuple() {
            Some(tuple) => tuple.elems.iter().any(|elem| pure_var_ids(self.descr(elem)).is_some()),
            None => false,
        }
    }

    /// True when any input position of `key` is a value template — the key names
    /// an activation that cannot become a runtime/backend executable because an
    /// argument would carry an unrepresentable bare-variable value.
    pub fn key_is_value_template(&self, key: &[Ty]) -> bool {
        key.iter().any(|ty| self.is_value_template(ty))
    }

    pub fn is_equivalent(&self, a: &Ty, b: &Ty) -> bool {
        if a == b {
            return true;
        }
        let key = Self::symmetric_key(ComparisonKey::Equivalent, *a, *b);
        self.cached_comparison(key, |types| types.is_subtype(a, b) && types.is_subtype(b, a))
    }

    pub fn kinds_overlap(&self, a: &Ty, b: &Ty) -> bool {
        self.descr(a).kinds_overlap(self.descr(b))
    }

    pub fn opaque_singleton(&self, a: &Ty) -> Option<String> {
        self.descr(a).as_opaque_singleton().map(String::from)
    }

    /// Classifies the resolved protocol-domain markers carried by a contract.
    ///
    /// The obligation identity is the resolved protocol-domain opaque marker
    /// tag (`protocol::<Name>.t`) wrapped as [`ProtocolDomainObligation`].
    /// This walks explicit positive markers in the hard `Ty` surface plus the
    /// contract-bound sidecar; negative descriptor clauses and cofinite
    /// complements describe excluded values, not obligations. It deliberately
    /// does not read source references or protocol implementation registries.
    pub(crate) fn protocol_domain_obligations(
        &self,
        roots: impl IntoIterator<Item = Ty>,
        bounds: &HashMap<TypeVarId, Ty>,
    ) -> BTreeSet<ProtocolDomainObligation> {
        let mut obligations = BTreeSet::new();
        let mut seen = HashSet::new();
        for root in roots {
            self.collect_protocol_domain_obligations(root, &mut seen, &mut obligations);
        }
        for bound in bounds.values().copied() {
            self.collect_protocol_domain_obligations(bound, &mut seen, &mut obligations);
        }
        obligations
    }

    fn collect_protocol_domain_obligations(
        &self,
        ty: Ty,
        seen: &mut HashSet<Ty>,
        obligations: &mut BTreeSet<ProtocolDomainObligation>,
    ) {
        if !seen.insert(ty) {
            return;
        }
        let descr = self.descr(&ty);
        if let Some(tags) = descr.opaques.finite_elems() {
            obligations.extend(tags.filter_map(|tag| {
                is_protocol_domain_tag(&tag).then(|| ProtocolDomainObligation::from_marker_tag(tag))
            }));
        }
        for conj in &descr.tuples {
            for sig in &conj.pos {
                for elem in &sig.elems {
                    self.collect_protocol_domain_obligations(*elem, seen, obligations);
                }
            }
        }
        for conj in &descr.lists {
            for sig in &conj.pos {
                if let Some(elem) = sig.elem {
                    self.collect_protocol_domain_obligations(elem, seen, obligations);
                }
            }
        }
        for conj in &descr.resources {
            for sig in &conj.pos {
                self.collect_protocol_domain_obligations(sig.payload, seen, obligations);
            }
        }
        for conj in &descr.funcs {
            for sig in &conj.pos {
                for arg in &sig.args {
                    self.collect_protocol_domain_obligations(*arg, seen, obligations);
                }
                self.collect_protocol_domain_obligations(sig.ret, seen, obligations);
                if let Some(lit) = &sig.lit {
                    for capture in &lit.captures {
                        self.collect_protocol_domain_obligations(*capture, seen, obligations);
                    }
                }
            }
        }
        for conj in &descr.maps {
            for sig in &conj.pos {
                for field in sig.fields.values() {
                    self.collect_protocol_domain_obligations(*field, seen, obligations);
                }
            }
        }
    }

    #[cfg(test)]
    pub fn brand_singleton(&self, a: &Ty) -> Option<String> {
        self.descr(a).as_brand_singleton().map(String::from)
    }

    pub fn is_singleton_lit(&self, a: &Ty) -> bool {
        self.descr(a).is_singleton_literal()
    }

    /// Always `None`: the lattice holds no numeric singletons. Constants
    /// ride the lowering as values (`LoweredMapKey`, dispatch consts).
    pub fn as_int_singleton(&self, _a: &Ty) -> Option<i64> {
        None
    }

    /// See `as_int_singleton`.
    pub fn as_float_singleton(&self, _a: &Ty) -> Option<f64> {
        None
    }

    pub fn as_atom_singleton(&self, a: &Ty) -> Option<String> {
        self.descr(a).as_atom_singleton().map(String::from)
    }

    pub(crate) fn runtime_type_predicate(&self, a: &Ty) -> RuntimeTypePredicate {
        let descr = self.descr(a);
        if runtime_type_predicate_requires_any(descr) {
            return RuntimeTypePredicate::any();
        }
        let named_structs = runtime_type_predicate_named_structs(descr);
        RuntimeTypePredicate {
            // Numbers are presence bits: the predicate is a kind check,
            // never a value-membership set, from this pipeline. `ints` and
            // `floats` are therefore always `FiniteSet::any()` (INT/FLOAT
            // present) or `FiniteSet::none()` (absent) here — never a
            // finite set of literal values. If a future numeric-singleton
            // axis is restored to the type lattice (the IntSet/FloatSet
            // finite-or-cofinite axes deleted when literals widened to
            // presence bits, recoverable from history), this is the site
            // that would populate `ints.values`/`floats.values` from it;
            // `emit_i64_membership`/`emit_u64_membership` in native
            // codegen already implement the per-value membership check
            // and are reused live today for atom membership, so they need
            // no change to pick up real numeric value sets.
            ints: if descr.basic.contains_all(BasicBits::INT) {
                FiniteSet::any()
            } else {
                FiniteSet::none()
            },
            floats: if descr.basic.contains_all(BasicBits::FLOAT) {
                FiniteSet::any()
            } else {
                FiniteSet::none()
            },
            atoms: descr.atoms.clone(),
            lists: self.runtime_type_predicate_lists(descr),
            tuples: self.runtime_type_predicate_tuples(descr),
            named_structs: named_structs.clone(),
            allow_other_structs: false,
            maps: !descr.maps.is_empty() && named_structs.is_none(),
            binaries: descr.basic.contains_all(BasicBits::BINARY),
            callables: self.runtime_type_predicate_callables(descr),
            resources: !descr.resources.is_empty(),
        }
    }

    /// The list axis a runtime test can put to a value.
    ///
    /// One head question per list CLAUSE that admits a cons cell, because a
    /// clause is the unit the lattice keeps correlated -- the same reason
    /// [`Self::runtime_type_predicate_tuples`] keeps one shape per clause.
    ///
    /// A clause is head-projectable only when it is exactly one positive
    /// signature with nothing subtracted, and that signature names an element
    /// type. Several positive signatures are an INTERSECTION of list types and
    /// negations are a DIFFERENCE; neither is one element type, and inventing
    /// one would claim a precision the emitted test could not honour. Those
    /// degrade the whole axis to the shape-only reading, which is what every
    /// clause answered before fz-kdt.107 step 3.
    ///
    /// A shape set with no `NonEmpty` puts no head question at all: `[]` is a
    /// single value and there is no cons cell to read.
    fn runtime_type_predicate_lists(&self, descr: &Descr) -> ListShapes {
        let shapes = runtime_type_predicate_list_shapes(descr);
        if !shapes.contains(&ListShape::NonEmpty) {
            return ListShapes::exact(shapes, Vec::new());
        }
        let mut heads = Vec::with_capacity(descr.lists.len());
        for clause in &descr.lists {
            if clause.pos.len() != 1 || !clause.neg.is_empty() {
                return ListShapes::shape_only(shapes);
            }
            let Some(elem) = clause.pos[0].elem else {
                // `[]` exactly: the clause admits no cons cell, so it puts no
                // head question and the other clauses' heads still stand.
                continue;
            };
            heads.push(self.runtime_type_predicate(&elem));
        }
        if heads.is_empty() {
            // Every clause admits a cons cell that no element type describes,
            // so there is nothing to ask it. "Any cons cell" is the shape-only
            // reading, and calling it exact would let it claim to CONTAIN
            // sharper axes it does not.
            return ListShapes::shape_only(shapes);
        }
        ListShapes::exact(shapes, heads)
    }

    /// The tuple axis a runtime test can put to a value.
    ///
    /// One shape per tuple CLAUSE, each carrying its positions' own
    /// predicates, because a clause is the unit the lattice keeps correlated:
    /// `{:cont, int} | {:halt, atom}` is two clauses, and joining them
    /// position-wise would admit `{:cont, atom}`, which neither names
    /// (fz-kdt.126).
    ///
    /// A clause is shapeable only when it is exactly one positive signature
    /// with nothing subtracted. Several positive signatures are an
    /// INTERSECTION of tuple types and negations are a DIFFERENCE; neither is
    /// a list of positions, and inventing one would claim a precision the
    /// emitted test could not honour. Those degrade the whole axis to the
    /// arity-only reading, which is what every clause answered before
    /// fz-kdt.119.
    fn runtime_type_predicate_tuples(&self, descr: &Descr) -> TupleShapes {
        let mut shapes = Vec::with_capacity(descr.tuples.len());
        for clause in &descr.tuples {
            if clause.pos.len() != 1 || !clause.neg.is_empty() {
                return TupleShapes::arity_only(runtime_type_predicate_tuple_arities(descr));
            }
            shapes.push(
                clause.pos[0]
                    .elems
                    .iter()
                    .map(|elem| self.runtime_type_predicate(elem))
                    .collect::<Vec<_>>(),
            );
        }
        TupleShapes::exact(shapes)
    }

    /// The callable axis a runtime test can put to a value.
    ///
    /// One shape per closure-literal CLAUSE, each carrying its captures' own
    /// predicates, because a clause is the unit the lattice keeps correlated
    /// -- the same reason [`Self::runtime_type_predicate_tuples`] keeps one
    /// shape per clause. A construction wrapper stamps exactly one such shape
    /// onto every value it mints (fz-kdt.127), which is what makes the capture
    /// positions answerable without ever loading a capture.
    ///
    /// A clause is shapeable only when it pins exactly one literal. Several
    /// literals at once are an INTERSECTION, which is not one shape; that
    /// degrades the whole axis to the target-only reading, which is what every
    /// clause answered before fz-kdt.127 and is a sound over-approximation of
    /// it. `callable_identity_targets` has already refused the clauses that
    /// name no literal, subtract one, or name an ANONYMOUS one.
    fn runtime_type_predicate_callables(&self, descr: &Descr) -> CallableShapes {
        let Some(targets) = callable_identity_targets(&descr.funcs) else {
            return CallableShapes::any();
        };
        let mut shapes = Vec::with_capacity(descr.funcs.len());
        for clause in &descr.funcs {
            let mut lits = clause.pos.iter().filter_map(|sig| sig.lit.as_ref());
            let (Some(lit), None) = (lits.next(), lits.next()) else {
                return CallableShapes::target_only(FiniteSet::finite(targets.into_iter().map(ClosureTarget::from)));
            };
            shapes.push(CallableShape {
                target: ClosureTarget::from(
                    lit.fn_id
                        .expect("callable_identity_targets refused every anonymous literal"),
                ),
                captures: lit
                    .captures
                    .iter()
                    .map(|capture| self.runtime_type_predicate(capture))
                    .collect(),
            });
        }
        CallableShapes::exact(shapes)
    }

    pub(crate) fn atom_literals(&self, a: &Ty) -> Vec<String> {
        self.descr(a).atom_literals().unwrap_or_default()
    }

    pub fn arrow_join_return(&mut self, a: &Ty) -> Ty {
        let d = {
            let cx = self.ctx();
            arrow_join_return(cx, cx.descr(a))
        };
        self.intern(d)
    }

    #[cfg(test)]
    pub fn tuple_lit_elems(&self, a: &Ty) -> Option<Vec<Ty>> {
        tuple_lit_elems(self.ctx(), self.descr(a))
    }

    pub fn is_integer(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::int())
    }

    pub fn is_floating(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::float())
    }

    pub fn is_nil(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::nil())
    }

    #[cfg(test)]
    pub fn is_bool(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::bool_t())
    }

    pub fn is_atom_type(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::atom_top())
    }

    pub fn has_vars(&self, a: &Ty) -> bool {
        has_vars(self.ctx(), self.descr(a))
    }

    /// Every free type-var id reachable from `a`, structural children
    /// included. The identity of the vars, not merely their presence: two
    /// types that mention DIFFERENT vars describe different families however
    /// their denotations compare.
    pub fn free_var_ids(&self, a: &Ty) -> BTreeSet<TypeVarId> {
        let mut ids = BTreeSet::new();
        collect_free_vars(self.ctx(), self.descr(a), &mut ids);
        ids
    }

    /// Every closure-literal arrow reachable from `a`, as
    /// `(fn_id, captures, args, ret)`, sorted and deduped. The brand is `None`
    /// for an anonymous literal, which is one shape like any other: two rows
    /// whose literals differ only in brand are NOT the same shape.
    ///
    /// `args` and `ret` are in here because subtyping leaves them out:
    /// `emptiness::func_clause_empty` decides a negative closure-literal
    /// arrow's `P \ N` from `fn_id` and `captures` alone. This is the
    /// signature evidence that judgement discards.
    ///
    /// The walk is STRUCTURAL, mirroring [`free_var_ids`](Self::free_var_ids):
    /// the same blind spot reaches a lambda wrapped in a tuple, a list, a
    /// resource payload, a map field or another arrow's signature exactly as it
    /// reaches a bare one, so the evidence has to be collected from the same
    /// places. A top-level-only walk would let `{:tag, fn}` rows that differ
    /// only in the nested arrow's signature absorb each other.
    pub fn lit_arrow_shapes(&self, a: &Ty) -> Vec<LitArrowShape> {
        let mut shapes = Vec::new();
        let mut seen = HashSet::new();
        collect_lit_arrow_shapes(self.ctx(), a, &mut seen, &mut shapes);
        shapes.sort();
        shapes.dedup();
        shapes
    }

    /// Does `dom` cover everything `sub` says, at one column of a correlated
    /// input row? (fz-kdt.106)
    ///
    /// A row set is an ANTICHAIN of alternatives, but a caller's ascent
    /// deposits a CHAIN: `conclude_preserving_frontier` joins every superseded
    /// conclusion's row in and nothing takes it out again, so the row set
    /// accumulates the history of one widening column. A covered rung carries
    /// no evidence its dominator does not, and eight of them cross
    /// `ACTIVATION_INPUT_ROW_BUDGET` and collapse the whole set columnwise --
    /// which is how the schedule ends up deciding what gets specialized.
    ///
    /// The relation is deliberately NARROWER than `is_subtype`, on two counts
    /// that are each load-bearing:
    ///
    /// - **Equal free-var sets.** A free var is absorbing under subtyping, so
    ///   a value-TEMPLATE column would swallow its own ground instances. Those
    ///   are two different activations of one body -- the erased shared
    ///   specialization and its representable sibling -- and dropping the
    ///   template misroutes every element family that was keyed through it.
    /// - **Closure-literal shape containment.** `func_clause_empty` (see
    ///   `emptiness.rs`) decides `P \ N` for a negative arrow carrying a
    ///   `ClosureLit` from `fn_id` and `captures` alone -- `args` and `ret`
    ///   are never read -- so subtyping calls a ground reducer arrow and a
    ///   var-carrying template arrow over ONE lambda equivalent. Requiring
    ///   `sub`'s literal shapes to appear verbatim among `dom`'s puts the
    ///   signature back into the judgement. Containment, not equality: a
    ///   ladder's closure column grows by ADDING literals, and those rungs
    ///   must still absorb.
    ///
    /// WHAT IS BY CONSTRUCTION, AND WHAT IS ONLY MEASURED. Two properties
    /// matter to the antichain that uses this, and they have different
    /// standing:
    ///
    /// - TRANSITIVITY is by construction. The relation is a conjunction of
    ///   three transitive relations (set equality on free-var ids, containment
    ///   on literal shapes, `is_subtype`) plus a reflexive `sub == dom`
    ///   short-circuit, and a conjunction of transitive relations is
    ///   transitive.
    /// - ANTISYMMETRY -- and so the confluence of absorption, which is what
    ///   makes the surviving set independent of insertion order -- is
    ///   EMPIRICAL. Nothing here forbids a mutually-dominating pair of
    ///   DISTINCT types: `is_subtype` is not antisymmetric on closure-literal
    ///   columns, and equal free-var sets plus equal shape sets do not force
    ///   equal types. What is known is that the corpus contains no such pair
    ///   (measured count 0 over 577 fixtures), which is a fact about today's
    ///   inputs, not a theorem.
    ///
    /// TERMINATION has the same empirical standing. Absorption is inflationary
    /// in denotation -- a dominated row adds nothing to the union, and a
    /// dominator that lands only grows it -- which is the fixpoint argument,
    /// but that argument leans on the relation implying denotational
    /// containment, and `is_subtype` is not denotational on closure-literal
    /// columns. Every fixture in the corpus settles;
    /// `ACTIVATION_INPUT_ROW_BUDGET` remains the backstop that makes
    /// termination a theorem regardless.
    ///
    /// Memoized on its own NON-symmetric key: `sub` and `dom` are not
    /// interchangeable, so this may never route through `symmetric_key`.
    pub fn row_column_dominates(&self, sub: &Ty, dom: &Ty) -> bool {
        if sub == dom {
            return true;
        }
        self.cached_comparison(ComparisonKey::RowColumnDominates(*sub, *dom), |types| {
            if types.free_var_ids(sub) != types.free_var_ids(dom) {
                return false;
            }
            let dom_shapes = types.lit_arrow_shapes(dom);
            if !types
                .lit_arrow_shapes(sub)
                .iter()
                .all(|shape| dom_shapes.contains(shape))
            {
                return false;
            }
            types.is_subtype(sub, dom)
        })
    }

    /// The row-level lift of [`Types::row_column_dominates`]: same arity, and
    /// every column of `sub` dominated by the column beside it in `dom`.
    ///
    /// Not memoized -- the columns underneath it are, and a row pair is a
    /// larger, sparser key than the column pairs it decomposes into.
    pub fn row_dominates(&self, sub: &[Ty], dom: &[Ty]) -> bool {
        sub.len() == dom.len()
            && sub
                .iter()
                .zip(dom)
                .all(|(sub, dom)| self.row_column_dominates(sub, dom))
    }

    pub fn runtime_envelope(&mut self, ty: Ty) -> Ty {
        let descr = runtime_envelope(self, ty, RuntimeEnvelopePolarity::Positive, CallableReading::AsTyped);
        self.intern(descr)
    }

    /// What a runtime test can see of `ty`.
    ///
    /// On the callable axis that is the value's CONSTRUCTION: a closure
    /// value's heap word at `+8` names the construction it was minted from,
    /// and a construction is a function together with the capture types it
    /// closed over, because a construction wrapper is one function at one
    /// capture layout. So the literal `fn_id`s and their captures survive
    /// here, each capture enveloped by this same reading, and the arrow the
    /// literal was typed at is erased -- no value carries it (fz-kdt.125,
    /// fz-kdt.127).
    ///
    /// AT EVERY DEPTH (fz-kdt.119). A tuple position holding a closure is read
    /// by the same one comparison as a top-level one, so `{:tag, #66(int)}`
    /// and `{:tag, #66(float)}` are two observables here exactly as `#66(int)`
    /// and `#66(float)` are, and `{:tag, #66}` and `{:tag, #68}` are two.
    /// Widening a nested callable to `fun_top` instead would reproduce
    /// fz-kdt.125's defect one tuple deep, and leave a depth-0/depth-1 seam
    /// nothing in the runtime justifies.
    pub(crate) fn runtime_type_test_envelope(&mut self, ty: Ty) -> Ty {
        let descr = runtime_envelope(self, ty, RuntimeEnvelopePolarity::Positive, CallableReading::Identity);
        self.intern(descr)
    }

    pub fn instantiate(&mut self, a: &Ty, sigma: &Sigma<Ty>) -> Ty {
        let d = instantiate(self, *a, sigma);
        self.intern(d)
    }

    pub fn collect_instantiation_subst(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) {
        collect_subst_into(self, *pattern, *witness, sigma);
    }

    pub fn grounded_callable_args(&mut self, template_args: &[Ty], surface_inputs: &[Ty]) -> Vec<Ty> {
        let mut sigma = Sigma::new();
        for (pattern, witness) in template_args.iter().zip(surface_inputs.iter()) {
            self.collect_instantiation_subst(pattern, witness, &mut sigma);
        }
        template_args.iter().map(|arg| self.instantiate(arg, &sigma)).collect()
    }
}

impl Types {
    /// Record the stable, version-independent name of one callable.
    ///
    /// A closure literal carries an `FnId`, which is a mint-order index: it
    /// shifts whenever the source gains or loses a function, so it cannot be
    /// what decides canonical clause order (see `order`). The owner knows the
    /// `Module.name/arity` behind the id and names it here as the id is minted,
    /// which is before any literal can reference it.
    pub(crate) fn name_callable(&mut self, target: ClosureTarget, label: impl Into<Arc<str>>) {
        let target = target.into();
        let label = label.into();
        if let Some(existing) = self.callable_labels.get(&target) {
            assert_eq!(existing, &label, "callable labels are immutable once registered");
        } else {
            assert!(
                self.callable_labels.values().all(|existing| existing != &label),
                "distinct callable identities require distinct stable labels"
            );
            self.callable_labels.insert(target, label);
        }
    }

    /// Every callable a closure literal in the arena names, that the owner
    /// never named. Empty in production — the gate that says so is
    /// `canon_test`'s `every_closure_literal_names_a_labelled_callable`.
    #[cfg(test)]
    pub(crate) fn unnamed_callables(&self) -> BTreeSet<u32> {
        self.interner
            .arena
            .iter()
            .flat_map(|d| d.funcs.iter())
            .flat_map(|c| c.pos.iter().chain(c.neg.iter()))
            .filter_map(|sig| sig.lit.as_ref())
            .filter_map(|lit| lit.fn_id)
            .filter(|fn_id| !self.callable_labels.contains_key(fn_id))
            .map(|fn_id| fn_id.0)
            .collect()
    }

    pub fn fn_ref_lit(&mut self, target: ClosureTarget, n_args: usize) -> Ty {
        let fn_id = target.into();
        let args: Vec<Ty> = (0..n_args)
            .map(|pos| self.intern(Descr::var(closure_var_id(fn_id, pos))))
            .collect();
        let ret = self.intern(Descr::var(closure_ret_var_id(fn_id)));
        self.intern(Descr {
            funcs: vec![Conj::pos_of(ArrowSig {
                args,
                ret,
                lit: Some(ClosureLit {
                    kind: CallableValueKind::FnRef,
                    fn_id: Some(fn_id),
                    captures: Vec::new(),
                }),
            })],
            ..Descr::none()
        })
    }

    pub fn closure_lit(&mut self, target: ClosureTarget, captures: Vec<Ty>, n_args: usize) -> Ty {
        let fn_id = target.into();
        let args: Vec<Ty> = (0..n_args)
            .map(|pos| self.intern(Descr::var(closure_var_id(fn_id, pos))))
            .collect();
        let ret = self.intern(Descr::var(closure_ret_var_id(fn_id)));
        self.intern(Descr {
            funcs: vec![Conj::pos_of(ArrowSig {
                args,
                ret,
                lit: Some(ClosureLit {
                    kind: CallableValueKind::Closure,
                    fn_id: Some(fn_id),
                    captures,
                }),
            })],
            ..Descr::none()
        })
    }

    pub fn closure_lit_parts(&self, a: &Ty) -> Option<ClosureLitInfo<Ty>> {
        let lit = self.descr(a).as_closure_lit()?;
        Some(ClosureLitInfo {
            target: lit.fn_id?.into(),
            captures: lit.captures.clone(),
            kind: lit.kind,
        })
    }

    pub fn callable_clauses(&mut self, a: &Ty) -> Option<Vec<CallableClause<Ty>>> {
        callable_clauses(self.ctx(), self.descr(a))
    }

    pub fn callable_value_clauses(&mut self, a: &Ty) -> Option<Vec<CallableClause<Ty>>> {
        let clauses = self.callable_clauses(a)?;
        let surface_clauses = clauses
            .iter()
            .filter(|clause| clause.closure.is_none())
            .cloned()
            .collect::<Vec<_>>();
        if surface_clauses.is_empty() {
            return Some(clauses);
        }

        let mut resolved = Vec::new();
        for clause in clauses {
            if clause.closure.is_none() {
                continue;
            }
            let mut specialized = false;
            for surface in surface_clauses
                .iter()
                .filter(|surface| surface.args.len() == clause.args.len())
            {
                specialized = true;
                let resolved_clause = specialize_callable_clause(self, &clause, surface);
                if !resolved.contains(&resolved_clause) {
                    resolved.push(resolved_clause);
                }
            }
            if !specialized && !resolved.contains(&clause) {
                resolved.push(clause);
            }
        }

        if resolved.is_empty() {
            Some(surface_clauses)
        } else {
            Some(resolved)
        }
    }

    pub fn erase_closure_identity(&mut self, a: &Ty) -> Ty {
        let d = erase_closure_identity(self, *a);
        self.intern(d)
    }
}

impl Types {
    pub fn check_opaque_visibility(&self, a: &Ty, using_module: &str) -> Result<(), OpaqueVisibilityError> {
        let Some(tag) = self.descr(a).as_opaque_singleton() else {
            return Ok(());
        };
        let Some(owner) = opaque_owner_module(tag) else {
            return Ok(());
        };
        if owner == using_module {
            Ok(())
        } else {
            Err(OpaqueVisibilityError {
                opaque: tag.to_string(),
                owner_module: owner.to_string(),
                using_module: using_module.to_string(),
            })
        }
    }
}

impl Types {
    pub fn display(&self, a: &Ty) -> String {
        format::display(self.ctx(), self.descr(a))
    }

    pub fn display_for_diag(&self, a: &Ty) -> String {
        format::display_for_diag(self.ctx(), self.descr(a))
    }
}

impl SharedTypes for Types {
    type Ty = Ty;

    fn any(&mut self) -> Self::Ty {
        Types::any(self)
    }

    fn none(&mut self) -> Self::Ty {
        Types::none(self)
    }

    fn nil(&mut self) -> Self::Ty {
        Types::nil(self)
    }

    fn bool(&mut self) -> Self::Ty {
        Types::bool(self)
    }

    fn int(&mut self) -> Self::Ty {
        Types::int(self)
    }

    fn int_lit(&mut self, n: i64) -> Self::Ty {
        Types::int_lit(self, n)
    }

    fn float(&mut self) -> Self::Ty {
        Types::float(self)
    }

    fn float_lit(&mut self, f: f64) -> Self::Ty {
        Types::float_lit(self, f)
    }

    fn atom(&mut self) -> Self::Ty {
        Types::atom(self)
    }

    fn atom_lit(&mut self, name: &str) -> Self::Ty {
        Types::atom_lit(self, name)
    }

    fn type_var(&mut self, id: TypeVarId) -> Self::Ty {
        Types::type_var(self, id)
    }

    fn resource(&mut self, payload: Self::Ty) -> Self::Ty {
        Types::resource(self, payload)
    }

    fn arrow(&mut self, args: &[Self::Ty], ret: Self::Ty) -> Self::Ty {
        Types::arrow(self, args, ret)
    }

    fn tuple(&mut self, elems: &[Self::Ty]) -> Self::Ty {
        Types::tuple(self, elems)
    }

    fn empty_list(&mut self) -> Self::Ty {
        Types::empty_list(self)
    }

    fn list(&mut self, elem: Self::Ty) -> Self::Ty {
        Types::list(self, elem)
    }

    fn non_empty_list(&mut self, elem: Self::Ty) -> Self::Ty {
        Types::non_empty_list(self, elem)
    }

    fn map(&mut self, fields: &[(MapKey, Self::Ty)]) -> Self::Ty {
        Types::map(self, fields)
    }

    fn str_t(&mut self) -> Self::Ty {
        Types::str_t(self)
    }

    fn map_top(&mut self) -> Self::Ty {
        Types::map_top(self)
    }

    fn mint_brand(&mut self, inner: Self::Ty, name: &str) -> Self::Ty {
        Types::mint_brand(self, inner, name)
    }

    fn opaque_of(&mut self, name: &str) -> Self::Ty {
        Types::opaque_of(self, name)
    }

    fn brand_of(&mut self, name: &str) -> Self::Ty {
        Types::brand_of(self, name)
    }

    fn list_element_type(&mut self, a: &Self::Ty) -> Self::Ty {
        Types::list_element_type(self, a)
    }

    fn has_list_shape(&self, a: &Self::Ty) -> bool {
        Types::has_list_shape(self, a)
    }

    fn resource_payload_type(&mut self, a: &Self::Ty) -> Option<Self::Ty> {
        Types::resource_payload_type(self, a)
    }

    fn mint_owned_resource_aliases(
        &mut self,
        a: Self::Ty,
        owner: &str,
        opaque_inners: &HashMap<String, Self::Ty>,
    ) -> Self::Ty {
        Types::mint_owned_resource_aliases(self, a, owner, opaque_inners)
    }

    fn tuple_projections(&mut self, a: &Self::Ty, arity: usize) -> Vec<Self::Ty> {
        Types::tuple_projections(self, a, arity)
    }

    fn tuple_field_type(&mut self, a: &Self::Ty, index: usize) -> Self::Ty {
        Types::tuple_field_type(self, a, index)
    }

    fn max_tuple_arity(&self, a: &Self::Ty) -> usize {
        Types::max_tuple_arity(self, a)
    }

    fn refine_map_field(&mut self, a: &Self::Ty, key: &MapKey, v: &Self::Ty) -> Self::Ty {
        Types::refine_map_field(self, a, key, v)
    }

    fn map_field_lookup(&mut self, a: &Self::Ty, key: &MapKey) -> Option<Self::Ty> {
        Types::map_field_lookup(self, a, key)
    }

    fn map_known_keys(&self, a: &Self::Ty) -> Vec<MapKey> {
        Types::map_known_keys(self, a)
    }

    fn widen_for_recursive_spec_key(&mut self, a: &Self::Ty) -> Self::Ty {
        Types::widen_for_recursive_spec_key(self, a)
    }

    fn refine_widen(&mut self, a: &Self::Ty, b: &Self::Ty) -> Self::Ty {
        Types::refine_widen(self, a, b)
    }

    fn convergence_class(&mut self, a: &Self::Ty) -> Self::Ty {
        Types::convergence_class(self, a)
    }

    fn union(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty {
        Types::union(self, a, b)
    }

    fn intersect(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty {
        Types::intersect(self, a, b)
    }

    #[cfg(test)]
    fn complement(&mut self, a: Self::Ty) -> Self::Ty {
        Types::complement(self, a)
    }

    fn difference(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty {
        Types::difference(self, a, b)
    }

    fn is_empty(&self, a: &Self::Ty) -> bool {
        Types::is_empty(self, a)
    }

    #[cfg(test)]
    fn is_top(&self, a: &Self::Ty) -> bool {
        Types::is_top(self, a)
    }

    fn is_subtype(&self, a: &Self::Ty, b: &Self::Ty) -> bool {
        Types::is_subtype(self, a, b)
    }

    fn is_disjoint(&self, a: &Self::Ty, b: &Self::Ty) -> bool {
        Types::is_disjoint(self, a, b)
    }

    fn is_value_disjoint(&self, a: &Self::Ty, b: &Self::Ty, _nominals: Nominals<'_, Self::Ty>) -> bool {
        Types::is_value_disjoint(self, a, b)
    }

    fn key_var_count(&self, key: &[Self::Ty]) -> usize {
        Types::key_var_count(self, key)
    }

    fn key_subsumes_with(&self, query: &Self::Ty, key: &Self::Ty, sigma: &mut Sigma<Self::Ty>) -> bool {
        Types::key_subsumes_with(self, query, key, sigma)
    }

    fn kinds_overlap(&self, a: &Self::Ty, b: &Self::Ty) -> bool {
        Types::kinds_overlap(self, a, b)
    }

    fn opaque_singleton(&self, a: &Self::Ty) -> Option<String> {
        Types::opaque_singleton(self, a)
    }

    #[cfg(test)]
    fn brand_singleton(&self, a: &Self::Ty) -> Option<String> {
        Types::brand_singleton(self, a)
    }

    fn is_singleton_lit(&self, a: &Self::Ty) -> bool {
        Types::is_singleton_lit(self, a)
    }

    fn as_int_singleton(&self, a: &Self::Ty) -> Option<i64> {
        Types::as_int_singleton(self, a)
    }

    fn as_float_singleton(&self, a: &Self::Ty) -> Option<f64> {
        Types::as_float_singleton(self, a)
    }

    fn as_atom_singleton(&self, a: &Self::Ty) -> Option<String> {
        Types::as_atom_singleton(self, a)
    }

    fn arrow_join_return(&mut self, a: &Self::Ty) -> Self::Ty {
        Types::arrow_join_return(self, a)
    }

    fn arrow_params(&self, a: &Self::Ty) -> Vec<Self::Ty> {
        Types::arrow_params(self, a)
    }

    #[cfg(test)]
    fn tuple_lit_elems(&self, a: &Self::Ty) -> Option<Vec<Self::Ty>> {
        Types::tuple_lit_elems(self, a)
    }

    fn instantiate(&mut self, a: &Self::Ty, sigma: &Sigma<Self::Ty>) -> Self::Ty {
        Types::instantiate(self, a, sigma)
    }

    fn collect_instantiation_subst(&mut self, pattern: &Self::Ty, witness: &Self::Ty, sigma: &mut Sigma<Self::Ty>) {
        Types::collect_instantiation_subst(self, pattern, witness, sigma)
    }

    fn is_integer(&self, a: &Self::Ty) -> bool {
        Types::is_integer(self, a)
    }

    fn is_floating(&self, a: &Self::Ty) -> bool {
        Types::is_floating(self, a)
    }

    fn is_nil(&self, a: &Self::Ty) -> bool {
        Types::is_nil(self, a)
    }

    #[cfg(test)]
    fn is_bool(&self, a: &Self::Ty) -> bool {
        Types::is_bool(self, a)
    }

    #[cfg(test)]
    fn is_atom_type(&self, a: &Self::Ty) -> bool {
        Types::is_atom_type(self, a)
    }

    fn has_vars(&self, a: &Self::Ty) -> bool {
        Types::has_vars(self, a)
    }
}

impl SharedClosureTypes for Types {
    fn fn_ref_lit(&mut self, target: ClosureTarget, n_args: usize) -> Self::Ty {
        Types::fn_ref_lit(self, target, n_args)
    }

    fn closure_lit(&mut self, target: ClosureTarget, captures: Vec<Self::Ty>, n_args: usize) -> Self::Ty {
        Types::closure_lit(self, target, captures, n_args)
    }

    fn closure_lit_parts(&self, a: &Self::Ty) -> Option<ClosureLitInfo<Self::Ty>> {
        Types::closure_lit_parts(self, a)
    }

    fn callable_clauses(&mut self, a: &Self::Ty) -> Option<Vec<CallableClause<Self::Ty>>> {
        Types::callable_clauses(self, a)
    }

    fn erase_closure_identity(&mut self, a: &Self::Ty) -> Self::Ty {
        Types::erase_closure_identity(self, a)
    }
}

impl SharedVisibilityTypes for Types {
    fn check_opaque_visibility(&self, a: &Self::Ty, using_module: &str) -> Result<(), OpaqueVisibilityError> {
        Types::check_opaque_visibility(self, a, using_module)
    }
}

impl SharedRenderTypes for Types {
    fn display(&self, a: &Self::Ty) -> String {
        Types::display(self, a)
    }

    fn display_for_diag(&self, a: &Self::Ty) -> String {
        Types::display_for_diag(self, a)
    }
}

fn pure_var_ids(d: &Descr) -> Option<Vec<TypeVarId>> {
    let finite: Vec<TypeVarId> = d.vars.finite_elems()?.collect();
    let only_vars = d.basic.is_empty()
        && d.atoms.is_none()
        && d.opaques.is_none()
        && d.brands.is_none()
        && d.tuples.is_empty()
        && d.lists.is_empty()
        && d.resources.is_empty()
        && d.funcs.is_empty()
        && d.maps.is_empty();
    (only_vars && !finite.is_empty()).then_some(finite)
}

fn intersect_descr(types: &mut Types, a: &Descr, b: &Descr) -> Descr {
    Descr {
        basic: a.basic.intersect(b.basic),
        atoms: a.atoms.intersect(&b.atoms),
        opaques: a.opaques.intersect(&b.opaques),
        brands: a.brands.intersect(&b.brands),
        vars: a.vars.intersect(&b.vars),
        tuples: intersect_dnf(types, &a.tuples, &b.tuples),
        lists: intersect_dnf(types, &a.lists, &b.lists),
        resources: intersect_dnf(types, &a.resources, &b.resources),
        funcs: intersect_dnf(types, &a.funcs, &b.funcs),
        maps: intersect_dnf(types, &a.maps, &b.maps),
    }
}

fn intersect_dnf<T: MergeSig>(types: &mut Types, a: &[Conj<T>], b: &[Conj<T>]) -> Vec<Conj<T>> {
    dnf_intersect_with(a, b, |c1, c2| intersect_clauses(types, c1, c2))
}

/// `None` means the merged clause is empty by construction (a positive-sig
/// pair proved disjoint): `∅` contributes nothing to a DNF and must not
/// persist — every garbage clause doubles a `dnf_neg` factor.
fn intersect_clauses<T: MergeSig>(types: &mut Types, a: &Conj<T>, b: &Conj<T>) -> Option<Conj<T>> {
    let mut pos = a.pos.clone();
    for new_sig in &b.pos {
        let mut merged = false;
        for slot in pos.iter_mut() {
            match T::intersect_pos(types, slot, new_sig) {
                PosMeet::Merged(narrowed) => {
                    *slot = narrowed;
                    merged = true;
                    break;
                }
                PosMeet::Empty => return None,
                PosMeet::Distinct => {}
            }
        }
        if !merged && !pos.contains(new_sig) {
            pos.push(new_sig.clone());
        }
    }
    let mut neg = a.neg.clone();
    for sig in &b.neg {
        if !neg.contains(sig) {
            neg.push(sig.clone());
        }
    }
    Some(Conj { pos, neg })
}

fn list_element_type(cx: TyCtx<'_>, d: &Descr) -> Descr {
    if d.lists.is_empty() {
        return Descr::any();
    }
    let mut elem = Descr::none();
    for conj in &d.lists {
        // A positive sig with no elem is the exact empty list: the whole
        // conjunction is a subset of it and has no head to project.
        if conj.pos.iter().any(|sig| sig.elem.is_none()) {
            continue;
        }
        let mut clause_elem: Option<Descr> = None;
        for sig in &conj.pos {
            let sig_elem = cx.descr(&sig.elem.expect("empty-list sigs were skipped above"));
            clause_elem = Some(match clause_elem {
                None => sig_elem.clone(),
                Some(prev) => prev.intersect(sig_elem),
            });
        }
        // No positive constraint at all (`Conj::top()`, as in `any`'s list
        // fragment) leaves the element unconstrained: `any`, never `none`.
        elem = elem.union(cx, &clause_elem.unwrap_or_else(Descr::any));
    }
    elem
}

fn resource_payload_type(cx: TyCtx<'_>, d: &Descr) -> Option<Descr> {
    if d.resources.is_empty() {
        return None;
    }
    let mut acc = Descr::none();
    for conj in &d.resources {
        if !conj.neg.is_empty() || conj.pos.is_empty() {
            return Some(Descr::any());
        }
        let mut payload: Option<Descr> = None;
        for sig in &conj.pos {
            let sig_payload = cx.descr(&sig.payload);
            payload = Some(match payload {
                Some(prev) => prev.intersect(sig_payload),
                None => sig_payload.clone(),
            });
        }
        acc = acc.union(cx, &payload.unwrap_or_else(Descr::any));
    }
    Some(acc)
}

fn tuple_projections(cx: TyCtx<'_>, d: &Descr, arity: usize) -> Vec<Descr> {
    let mut comps = vec![Descr::none(); arity];
    let mut found = false;
    for conj in &d.tuples {
        let mut clause_comps: Option<Vec<Descr>> = None;
        for sig in &conj.pos {
            if sig.elems.len() != arity {
                continue;
            }
            clause_comps = Some(match clause_comps {
                None => sig.elems.iter().map(|t| cx.descr(t).clone()).collect(),
                Some(prev) => prev
                    .iter()
                    .zip(sig.elems.iter())
                    .map(|(p, s)| p.intersect(cx.descr(s)))
                    .collect(),
            });
        }
        if let Some(cs) = clause_comps {
            for i in 0..arity {
                comps[i] = comps[i].union(cx, &cs[i]);
            }
            found = true;
        }
    }
    if found { comps } else { vec![Descr::any(); arity] }
}

fn tuple_field_type(cx: TyCtx<'_>, d: &Descr, index: usize) -> Descr {
    let mut out = Descr::none();
    let mut found = false;
    for conj in &d.tuples {
        if conj.pos.is_empty() {
            return Descr::any();
        }

        let mut arity = None;
        let mut clause_fields: Option<Vec<Descr>> = None;
        let mut feasible = true;
        for sig in &conj.pos {
            if index >= sig.elems.len() || arity.is_some_and(|arity| arity != sig.elems.len()) {
                feasible = false;
                break;
            }
            arity = Some(sig.elems.len());
            clause_fields = Some(match clause_fields {
                None => sig.elems.iter().map(|t| cx.descr(t).clone()).collect(),
                Some(prev) => prev
                    .iter()
                    .zip(sig.elems.iter())
                    .map(|(p, s)| p.intersect(cx.descr(s)))
                    .collect(),
            });
        }
        let Some(fields) = clause_fields else {
            continue;
        };
        if !feasible || fields.iter().any(|field| field.is_empty(cx)) {
            continue;
        }
        out = out.union(cx, &fields[index]);
        found = true;
    }
    if found { out } else { Descr::none() }
}

fn map_field_lookup(cx: TyCtx<'_>, d: &Descr, key: &MapKey) -> Option<Descr> {
    if d.maps.is_empty() {
        return None;
    }
    let mut found = false;
    let mut acc = Descr::none();
    for conj in &d.maps {
        if conj.pos.is_empty() {
            acc = acc.union(cx, &Descr::any()).union(cx, &Descr::nil());
            found = true;
            continue;
        }
        let mut clause_v: Option<Descr> = None;
        for sig in &conj.pos {
            let sig_v = match sig.fields.get(key) {
                Some(t) => cx.descr(t).clone(),
                None => Descr::any().union(cx, &Descr::nil()),
            };
            clause_v = Some(match clause_v {
                None => sig_v,
                Some(prev) => prev.intersect(&sig_v),
            });
        }
        if let Some(v) = clause_v {
            acc = acc.union(cx, &v);
            found = true;
        }
    }
    if found { Some(acc) } else { None }
}

fn map_known_keys(d: &Descr) -> Vec<MapKey> {
    let mut keys = BTreeSet::new();
    for conj in &d.maps {
        for sig in &conj.pos {
            keys.extend(sig.fields.keys().cloned());
        }
    }
    keys.into_iter().collect()
}

fn callable_clauses(cx: TyCtx<'_>, d: &Descr) -> Option<Vec<CallableClause<Ty>>> {
    if d.funcs.is_empty() || d.funcs.iter().any(|c| !c.neg.is_empty() || c.pos.is_empty()) {
        return None;
    }
    Some(
        d.funcs
            .iter()
            .flat_map(|conj| conj.pos.iter())
            .map(|arrow| CallableClause {
                args: arrow.args.clone(),
                ret: arrow.ret,
                closure: arrow.lit.as_ref().and_then(|lit| {
                    lit.fn_id.map(|fn_id| ClosureLitInfo {
                        target: fn_id.into(),
                        captures: lit.captures.clone(),
                        kind: lit.kind,
                    })
                }),
            })
            .filter(|clause| clause.args.iter().all(|arg| !cx.descr(arg).is_empty(cx)))
            .collect(),
    )
}

fn runtime_type_predicate_requires_any(descr: &Descr) -> bool {
    const STRUCT_PREFIX: &str = "impl-target::";
    descr.opaques.cofinite
        || descr.opaques.values.iter().any(|tag| !tag.starts_with(STRUCT_PREFIX))
        || descr.brands.cofinite
        || descr.vars.cofinite
        || !descr.vars.values.is_empty()
}

fn runtime_type_predicate_list_shapes(descr: &Descr) -> FiniteSet<ListShape> {
    let mut out = FiniteSet::none();
    for clause in &descr.lists {
        let mut allowed = FiniteSet::finite([ListShape::Empty, ListShape::NonEmpty]);
        for sig in &clause.pos {
            let sig_allowed = if sig.is_exact_empty() {
                FiniteSet::lit(ListShape::Empty)
            } else if sig.is_exact_non_empty() {
                FiniteSet::lit(ListShape::NonEmpty)
            } else {
                FiniteSet::finite([ListShape::Empty, ListShape::NonEmpty])
            };
            allowed = allowed.intersect(&sig_allowed);
        }
        for sig in &clause.neg {
            if sig.is_exact_empty() {
                allowed = runtime_type_predicate_remove(&allowed, &ListShape::Empty);
            } else if sig.is_exact_non_empty() {
                allowed = runtime_type_predicate_remove(&allowed, &ListShape::NonEmpty);
            }
        }
        out = out.union(&allowed);
    }
    out
}

fn runtime_type_predicate_tuple_arities(descr: &Descr) -> FiniteSet<usize> {
    let mut out = FiniteSet::none();
    for clause in &descr.tuples {
        let mut allowed = if clause.pos.is_empty() {
            FiniteSet::any()
        } else {
            let arities = clause.pos.iter().map(|sig| sig.elems.len()).collect::<BTreeSet<_>>();
            if arities.len() != 1 {
                continue;
            }
            FiniteSet::lit(*arities.iter().next().expect("one tuple arity"))
        };
        for sig in &clause.neg {
            allowed = runtime_type_predicate_remove(&allowed, &sig.elems.len());
        }
        out = out.union(&allowed);
    }
    out
}

/// Every callable a function axis admits, named the way the runtime tells them
/// apart: by the code each was minted from. `None` when the axis admits
/// callables this side cannot enumerate.
///
/// A clause that pins no closure literal admits any callable at all, and one
/// such clause makes the whole union unrestricted; so does a clause that
/// SUBTRACTS a literal, whose remainder is not enumerable from this side. A
/// clause that pins several literals at once is an intersection, which every
/// one of them contains, so naming them all over-approximates it — and
/// over-approximation is the direction a dispatch test must err in, exactly as
/// the list-shape and tuple-arity axes do.
///
/// An ANONYMOUS literal (fz-kdt.127) names no code at all, so it is that same
/// unrestricted answer -- and this is the ONE place that decides it, for the
/// predicate projection and for the envelope alike. It never actually arrives.
/// An anonymous literal is minted in exactly one place,
/// [`Types::erase_transported_closure_identities`], which puts it in the
/// `arrow` of the ACTIVATION KEY of a non-recursive body that consumes no
/// callable identity, and only in the slots the dispatch mask marks
/// `DispatchDemand::Ignore`; a runtime test is asked of a VALUE's type -- a
/// callsite's `CallTargetSummary::surface_inputs`, a lane's carrier -- never of
/// a key. THAT is what makes an erased forwarder key and the construction axis
/// compose: the keying rule holds the two apart, not any projection here. The
/// `debug_assert!` is the gate on the rule; the `?` behind it keeps the sound
/// unrestricted answer if the rule is ever broken.
fn callable_identity_targets(funcs: &[Conj<ArrowSig>]) -> Option<BTreeSet<FnId>> {
    let mut targets = BTreeSet::new();
    for clause in funcs {
        let lits = clause
            .pos
            .iter()
            .filter_map(|sig| sig.lit.as_ref())
            .map(|lit| {
                debug_assert!(
                    lit.fn_id.is_some(),
                    "an anonymous literal reached a runtime test: it can only have come from an \
                     activation key, and a key is never what a test is asked of (fz-kdt.127)"
                );
                lit.fn_id
            })
            .collect::<Option<Vec<_>>>()?;
        if lits.is_empty() || !clause.neg.is_empty() {
            return None;
        }
        targets.extend(lits);
    }
    Some(targets)
}

fn runtime_type_predicate_named_structs(descr: &Descr) -> FiniteSet<String> {
    const STRUCT_PREFIX: &str = "impl-target::";
    FiniteSet::finite(
        descr
            .opaques
            .values
            .iter()
            .filter_map(|tag| tag.strip_prefix(STRUCT_PREFIX).map(str::to_string)),
    )
}

fn runtime_type_predicate_remove<T>(set: &FiniteSet<T>, value: &T) -> FiniteSet<T>
where
    T: Ord + Clone,
{
    if set.cofinite {
        let mut excluded = set.values.clone();
        excluded.insert(value.clone());
        FiniteSet::cofinite(excluded)
    } else {
        FiniteSet::finite(set.values.iter().filter(|candidate| *candidate != value).cloned())
    }
}

fn specialize_callable_clause(
    types: &mut Types,
    clause: &CallableClause<Ty>,
    surface: &CallableClause<Ty>,
) -> CallableClause<Ty> {
    let mut sigma = Sigma::new();
    for (pattern, witness) in clause.args.iter().zip(surface.args.iter()) {
        types.collect_instantiation_subst(pattern, witness, &mut sigma);
    }
    types.collect_instantiation_subst(&clause.ret, &surface.ret, &mut sigma);
    CallableClause {
        args: clause.args.iter().map(|arg| types.instantiate(arg, &sigma)).collect(),
        ret: types.instantiate(&clause.ret, &sigma),
        closure: clause.closure.clone(),
    }
}

/// Collect every type-var id `d` mentions, mirroring `has_vars`' recursion:
/// the same axes, the same structural children, including a closure literal's
/// captures.
fn collect_free_vars(cx: TyCtx<'_>, d: &Descr, ids: &mut BTreeSet<TypeVarId>) {
    ids.extend(d.vars.values.iter().copied());
    for c in &d.tuples {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            for t in &sig.elems {
                collect_free_vars(cx, cx.descr(t), ids);
            }
        }
    }
    for c in &d.lists {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            if let Some(t) = sig.elem {
                collect_free_vars(cx, cx.descr(&t), ids);
            }
        }
    }
    for c in &d.resources {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            collect_free_vars(cx, cx.descr(&sig.payload), ids);
        }
    }
    for c in &d.funcs {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            for t in &sig.args {
                collect_free_vars(cx, cx.descr(t), ids);
            }
            collect_free_vars(cx, cx.descr(&sig.ret), ids);
            if let Some(lit) = sig.lit.as_ref() {
                for t in &lit.captures {
                    collect_free_vars(cx, cx.descr(t), ids);
                }
            }
        }
    }
    for c in &d.maps {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            for t in sig.fields.values() {
                collect_free_vars(cx, cx.descr(t), ids);
            }
        }
    }
}

/// Collect every closure-literal arrow reachable from `t`, mirroring
/// `collect_free_vars`' recursion: the same axes, the same structural
/// children, plus a literal's own captures.
///
/// `seen` is a cycle guard, not a memo -- an interned type may be its own
/// descendant (a recursive list element, a closure captured in its own
/// capture vector), and revisiting one adds nothing the first visit did not.
fn collect_lit_arrow_shapes(cx: TyCtx<'_>, t: &Ty, seen: &mut HashSet<Ty>, shapes: &mut Vec<LitArrowShape>) {
    if !seen.insert(*t) {
        return;
    }
    let d = cx.descr(t);
    for c in &d.tuples {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            for e in &sig.elems {
                collect_lit_arrow_shapes(cx, e, seen, shapes);
            }
        }
    }
    for c in &d.lists {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            if let Some(e) = sig.elem {
                collect_lit_arrow_shapes(cx, &e, seen, shapes);
            }
        }
    }
    for c in &d.resources {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            collect_lit_arrow_shapes(cx, &sig.payload, seen, shapes);
        }
    }
    for c in &d.funcs {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            if let Some(lit) = sig.lit.as_ref() {
                shapes.push((lit.fn_id, lit.captures.clone(), sig.args.clone(), sig.ret));
                for capture in &lit.captures {
                    collect_lit_arrow_shapes(cx, capture, seen, shapes);
                }
            }
            for arg in &sig.args {
                collect_lit_arrow_shapes(cx, arg, seen, shapes);
            }
            collect_lit_arrow_shapes(cx, &sig.ret, seen, shapes);
        }
    }
    for c in &d.maps {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            for field in sig.fields.values() {
                collect_lit_arrow_shapes(cx, field, seen, shapes);
            }
        }
    }
}

fn has_vars(cx: TyCtx<'_>, d: &Descr) -> bool {
    if !d.vars.values.is_empty() {
        return true;
    }
    d.tuples.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| sig.elems.iter().any(|t| has_vars(cx, cx.descr(t))))
    }) || d.lists.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| sig.elem.is_some_and(|t| has_vars(cx, cx.descr(&t))))
    }) || d.resources.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| has_vars(cx, cx.descr(&sig.payload)))
    }) || d.funcs.iter().any(|c| {
        c.pos.iter().chain(c.neg.iter()).any(|sig| {
            sig.args.iter().any(|t| has_vars(cx, cx.descr(t)))
                || has_vars(cx, cx.descr(&sig.ret))
                || sig
                    .lit
                    .as_ref()
                    .is_some_and(|lit| lit.captures.iter().any(|t| has_vars(cx, cx.descr(t))))
        })
    }) || d.maps.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| sig.fields.values().any(|t| has_vars(cx, cx.descr(t))))
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RuntimeEnvelopePolarity {
    Positive,
    Negative,
}

impl RuntimeEnvelopePolarity {
    fn flipped(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

/// Whether the envelope keeps a callable's typing or reduces it to the one
/// thing a runtime value tells about itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CallableReading {
    /// Leave the function axis as the lattice typed it.
    AsTyped,
    /// Reduce it to the CONSTRUCTION -- the literal's identity together with
    /// its capture types, each capture reduced by this same reading -- and drop
    /// the arrow, at every depth.
    Identity,
}

fn runtime_envelope(types: &mut Types, ty: Ty, polarity: RuntimeEnvelopePolarity, callables: CallableReading) -> Descr {
    let mut descr = types.descr(&ty).clone();
    if !descr.vars.values.is_empty() {
        match (polarity, descr.vars.cofinite) {
            (RuntimeEnvelopePolarity::Positive, _) => return Descr::any(),
            (RuntimeEnvelopePolarity::Negative, true) => return Descr::none(),
            (RuntimeEnvelopePolarity::Negative, false) => descr.vars = FiniteSet::none(),
        }
    }
    // Only in a positive position: a construction clause drops the arrow and
    // widens each capture by this same reading, so it names at least the
    // callables the clause it replaces named -- the direction a test must err
    // in, and the opposite of the direction a subtracted region may.
    if callables == CallableReading::Identity
        && polarity == RuntimeEnvelopePolarity::Positive
        && !descr.funcs.is_empty()
    {
        descr.funcs = callable_identity_clauses(types, &descr.funcs);
    }
    descr.tuples = descr
        .tuples
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, callables, runtime_tuple_sig))
        .collect();
    descr.lists = descr
        .lists
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, callables, runtime_list_sig))
        .collect();
    descr.resources = descr
        .resources
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, callables, runtime_resource_sig))
        .collect();
    descr.maps = descr
        .maps
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, callables, runtime_map_sig))
        .collect();
    descr
}

/// The function axis reduced to the one question the runtime can ask of a
/// callable value: which CONSTRUCTION is it?
///
/// One literal per literal and one clause per clause, carrying the identity
/// and the captures -- each capture itself reduced to what a test can see of
/// it, at every depth -- and nothing else: the arrow the literal was typed at
/// is gone, because no value carries it. Where it can name no literal at all
/// the axis widens to `fun_top` rather than claim a precision the test could
/// not honour.
///
/// The CLAUSE SHAPE survives untouched, and that is the point: how a clause
/// projects is decided in exactly one place,
/// [`Types::runtime_type_predicate_callables`], and this function hands it the
/// same clause it would have seen unenveloped. A clause pinning several
/// literals at once is an intersection and is not one construction, so that
/// one place degrades it to the target-only reading -- every capture layout of
/// those targets -- on both roads. Splitting it here into several literals over
/// NO captures would instead reach that place as EXACT zero-capture shapes,
/// which `CallableShape::inside` refuses every capturing construction of, on a
/// capture-count mismatch: under-admission, the one direction a runtime test
/// may never err in.
fn callable_identity_clauses(types: &mut Types, funcs: &[Conj<ArrowSig>]) -> Vec<Conj<ArrowSig>> {
    if callable_identity_targets(funcs).is_none() {
        return Descr::fun_top().funcs;
    }
    let ret = types.any();
    let mut clauses = Vec::with_capacity(funcs.len());
    for clause in funcs {
        let mut pos = Vec::with_capacity(clause.pos.len());
        for lit in clause.pos.iter().filter_map(|sig| sig.lit.as_ref()) {
            let captures = lit
                .captures
                .iter()
                .map(|capture| {
                    runtime_envelope_ty(
                        types,
                        *capture,
                        RuntimeEnvelopePolarity::Positive,
                        CallableReading::Identity,
                    )
                })
                .collect();
            pos.push(ArrowSig {
                args: Vec::new(),
                ret,
                lit: Some(ClosureLit {
                    kind: CallableValueKind::Closure,
                    fn_id: lit.fn_id,
                    captures,
                }),
            });
        }
        clauses.push(Conj { pos, neg: Vec::new() });
    }
    clauses
}

fn runtime_envelope_ty(types: &mut Types, ty: Ty, polarity: RuntimeEnvelopePolarity, callables: CallableReading) -> Ty {
    let descr = runtime_envelope(types, ty, polarity, callables);
    types.intern(descr)
}

fn runtime_structural_conj<T>(
    types: &mut Types,
    conj: Conj<T>,
    polarity: RuntimeEnvelopePolarity,
    callables: CallableReading,
    transform: fn(&mut Types, T, RuntimeEnvelopePolarity, CallableReading) -> Option<T>,
) -> Option<Conj<T>> {
    let mut pos = Vec::with_capacity(conj.pos.len());
    for sig in conj.pos {
        pos.push(transform(types, sig, polarity, callables)?);
    }
    let neg = conj
        .neg
        .into_iter()
        .filter_map(|sig| transform(types, sig, polarity.flipped(), callables))
        .collect();
    Some(Conj { pos, neg })
}

fn runtime_tuple_sig(
    types: &mut Types,
    sig: TupleSig,
    polarity: RuntimeEnvelopePolarity,
    callables: CallableReading,
) -> Option<TupleSig> {
    let elems = sig
        .elems
        .into_iter()
        .map(|ty| runtime_envelope_ty(types, ty, polarity, callables))
        .collect::<Vec<_>>();
    (!elems.iter().any(|ty| types.is_empty(ty))).then_some(TupleSig { elems })
}

fn runtime_list_sig(
    types: &mut Types,
    sig: ListSig,
    polarity: RuntimeEnvelopePolarity,
    callables: CallableReading,
) -> Option<ListSig> {
    let elem = sig.elem.map(|ty| runtime_envelope_ty(types, ty, polarity, callables));
    match elem {
        Some(elem) if types.is_empty(&elem) && !sig.empty => None,
        Some(elem) if types.is_empty(&elem) => Some(ListSig::empty()),
        _ => Some(ListSig { empty: sig.empty, elem }),
    }
}

fn runtime_resource_sig(
    types: &mut Types,
    sig: ResourceSig,
    polarity: RuntimeEnvelopePolarity,
    callables: CallableReading,
) -> Option<ResourceSig> {
    let payload = runtime_envelope_ty(types, sig.payload, polarity, callables);
    (!types.is_empty(&payload)).then_some(ResourceSig { payload })
}

fn runtime_map_sig(
    types: &mut Types,
    sig: sigs::MapSig,
    polarity: RuntimeEnvelopePolarity,
    callables: CallableReading,
) -> Option<sigs::MapSig> {
    let fields = sig
        .fields
        .into_iter()
        .map(|(key, ty)| (key, runtime_envelope_ty(types, ty, polarity, callables)))
        .collect::<BTreeMap<_, _>>();
    (!fields.values().any(|ty| types.is_empty(ty))).then_some(sigs::MapSig { fields })
}

fn arrow_join_return(cx: TyCtx<'_>, d: &Descr) -> Descr {
    if d.funcs.is_empty() {
        return Descr::any();
    }
    let mut acc = Descr::none();
    for c in &d.funcs {
        if !c.neg.is_empty() || c.pos.is_empty() {
            return Descr::any();
        }
        for sig in &c.pos {
            acc = acc.union(cx, cx.descr(&sig.ret));
        }
    }
    acc
}

#[cfg(test)]
fn tuple_lit_elems(cx: TyCtx<'_>, d: &Descr) -> Option<Vec<Ty>> {
    let elems = d.as_tuple_singleton()?;
    elems.iter().all(|t| is_literal(cx, t)).then(|| elems.to_vec())
}

#[cfg(test)]
fn is_literal(cx: TyCtx<'_>, a: &Ty) -> bool {
    let d = cx.descr(a);
    d.is_singleton_literal()
        || d.is_equiv(cx, &Descr::nil())
        || tuple_lit_elems(cx, d).is_some()
        || d.as_closure_lit()
            .is_some_and(|lit| lit.captures.iter().all(|capture| is_literal(cx, capture)))
}

// More recursive transforms live in this module so they can thread the owning
// interner explicitly without exposing the private descriptor representation.
/// Erase every closure literal's BRAND and keep its capture TYPES, at every
/// depth (fz-6gb, fz-kdt.127).
///
/// A forwarder key must not fork on WHICH lambda travelled through it -- that
/// is freight, and forking on it drags a private copy of every library
/// function the lambda reaches. It must fork on what that lambda CLOSED OVER:
/// a body keyed at one capture type grounds its callees' capture lanes to that
/// type, so two capture types arriving through one key leave a choice no
/// static key can pin and only a runtime test could answer. Keeping the
/// capture types answers it by the key instead.
///
/// The captures are erased by this same rule, so brands nested inside a
/// captured closure go too and same-typed literals still share one body. A
/// literal with no captures has nothing left to say once its brand is gone, so
/// it erases to the bare arrow it always did.
fn erase_closure_identity(t: &mut Types, a: Ty) -> Descr {
    let base = t.descr(&a).clone();
    let mut erased = map_recursive_inputs(t, base, erase_closure_identity);
    for conj in &mut erased.funcs {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            let Some(lit) = sig.lit.take() else {
                continue;
            };
            if lit.captures.is_empty() {
                continue;
            }
            let captures = lit
                .captures
                .iter()
                .map(|capture| {
                    let capture = erase_closure_identity(t, *capture);
                    t.intern(capture)
                })
                .collect();
            sig.lit = Some(ClosureLit {
                kind: lit.kind,
                fn_id: None,
                captures,
            });
        }
    }
    erased
}

/// Returns an interned `Ty`: every result is canonically interned in `Types`,
/// so a widened type is never an un-interned `Descr` that a caller might compare
/// or store without canonicalization.
fn refine_widen(t: &mut Types, a: Ty, b: Ty) -> Ty {
    let lhs = t.descr(&a).clone();
    let rhs = t.descr(&b).clone();
    if let (Some(l), Some(r)) = (lhs.pure_tuple().cloned(), rhs.pure_tuple().cloned())
        && l.elems.len() == r.elems.len()
    {
        let elems: Vec<Ty> = l
            .elems
            .iter()
            .zip(r.elems.iter())
            .map(|(l, r)| refine_widen(t, *l, *r))
            .collect();
        return t.intern(Descr::tuple_of(elems));
    }
    if let (Some(l), Some(r)) = (lhs.as_pure_list(t.ctx()).cloned(), rhs.as_pure_list(t.ctx()).cloned()) {
        let elem = match (l.elem, r.elem) {
            (Some(l), Some(r)) => Some(refine_widen(t, l, r)),
            (Some(l), None) => Some(l),
            (None, Some(r)) => Some(r),
            (None, None) => None,
        };
        let d = match elem {
            Some(elem) => Descr::list_sig(ListSig {
                empty: l.empty || r.empty,
                elem: Some(elem),
            }),
            None => Descr::empty_list(),
        };
        return t.intern(d);
    }
    if let (Some(l), Some(r)) = (lhs.pure_resource().cloned(), rhs.pure_resource().cloned()) {
        let payload = refine_widen(t, l.payload, r.payload);
        let d = Descr::resource_of(t.ctx(), payload);
        return t.intern(d);
    }
    if let (Some(l), Some(r)) = (lhs.pure_arrow().cloned(), rhs.pure_arrow().cloned())
        && l.args.len() == r.args.len()
    {
        // Pairwise arrow-merging is only a valid economy when both clauses
        // describe the same callable value (or neither carries one).
        // Mismatched identities fall through to the union so closure
        // callsites downstream can still resolve every target.
        let merged_lit = match (&l.lit, &r.lit) {
            (None, None) => Some(None),
            (Some(lhs_lit), Some(rhs_lit))
                if lhs_lit.kind == rhs_lit.kind
                    && lhs_lit.fn_id == rhs_lit.fn_id
                    && lhs_lit.captures.len() == rhs_lit.captures.len() =>
            {
                let captures = lhs_lit
                    .captures
                    .clone()
                    .into_iter()
                    .zip(rhs_lit.captures.clone())
                    .map(|(lhs_capture, rhs_capture)| refine_widen(t, lhs_capture, rhs_capture))
                    .collect();
                Some(Some(ClosureLit {
                    kind: lhs_lit.kind,
                    fn_id: lhs_lit.fn_id,
                    captures,
                }))
            }
            _ => None,
        };
        if let Some(lit) = merged_lit {
            let args: Vec<Ty> = l.args.iter().zip(r.args.iter()).map(|(l, r)| t.union(*l, *r)).collect();
            let ret = refine_widen(t, l.ret, r.ret);
            return t.intern(Descr {
                funcs: vec![Conj::pos_of(ArrowSig { args, ret, lit })],
                ..Descr::none()
            });
        }
    }
    if let (Some(l), Some(r)) = (lhs.pure_map().cloned(), rhs.pure_map().cloned()) {
        let mut fields = l.fields;
        for (key, rv) in &r.fields {
            if let Some(lv) = fields.get_mut(key) {
                *lv = refine_widen(t, *lv, *rv);
            } else {
                fields.insert(key.clone(), *rv);
            }
        }
        return t.intern(Descr::map_of(fields));
    }

    t.union(a, b)
}

fn instantiate(t: &mut Types, a: Ty, sigma: &Sigma<Ty>) -> Descr {
    let d = t.descr(&a).clone();
    if !has_vars(t.ctx(), &d) {
        return d;
    }
    let mut substituted = Descr::none();
    let mut base = d.clone();
    if !base.vars.cofinite {
        let mut new_set = BTreeSet::new();
        for id in &d.vars.values {
            match sigma.get(id) {
                Some(replacement) => {
                    substituted = substituted.union(t.ctx(), t.descr(replacement));
                }
                None => {
                    new_set.insert(*id);
                }
            }
        }
        base.vars = FiniteSet::finite(new_set);
    }
    let walked = map_recursive_inputs_with(t, base, &mut |t, nested| {
        let d = instantiate(t, nested, sigma);
        t.intern(d)
    });
    walked.union(t.ctx(), &substituted)
}

fn collect_subst_into(t: &mut Types, pattern: Ty, witness: Ty, sigma: &mut Sigma<Ty>) {
    let pat = t.descr(&pattern).clone();
    let wit = t.descr(&witness).clone();
    if let Some(ids) = pure_var_ids(&pat) {
        for id in ids {
            sigma.entry(id).or_insert(witness);
        }
        return;
    }
    if let (Some(ps), Some(ws)) = (pat.pure_tuple(), wit.pure_tuple())
        && ps.elems.len() == ws.elems.len()
    {
        for (p, w) in ps.elems.iter().zip(ws.elems.iter()) {
            collect_subst_into(t, *p, *w, sigma);
        }
    }
    if let (Some(ps), Some(ws)) = (pat.as_pure_list(t.ctx()), wit.as_pure_list(t.ctx()))
        && let (Some(p), Some(w)) = (ps.elem, ws.elem)
    {
        collect_subst_into(t, p, w, sigma);
    }
    if let (Some(ps), Some(ws)) = (pat.pure_resource(), wit.pure_resource()) {
        collect_subst_into(t, ps.payload, ws.payload, sigma);
    }
    if let (Some(ps), Some(ws)) = (pat.pure_arrow(), wit.pure_arrow())
        && ps.args.len() == ws.args.len()
    {
        for (p, w) in ps.args.iter().zip(ws.args.iter()) {
            collect_subst_into(t, *p, *w, sigma);
        }
        collect_subst_into(t, ps.ret, ws.ret, sigma);
    }
    if let (Some(ps), Some(ws)) = (pat.pure_map(), wit.pure_map()) {
        for (key, p) in &ps.fields {
            if let Some(w) = ws.fields.get(key) {
                collect_subst_into(t, *p, *w, sigma);
            }
        }
    }
}

fn map_recursive_inputs(t: &mut Types, d: Descr, f: fn(&mut Types, Ty) -> Descr) -> Descr {
    map_recursive_inputs_with(t, d, &mut |t, nested| {
        let d = f(t, nested);
        t.intern(d)
    })
}

fn map_recursive_inputs_with(t: &mut Types, mut d: Descr, f: &mut impl FnMut(&mut Types, Ty) -> Ty) -> Descr {
    for conj in &mut d.tuples {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            sig.elems = sig.elems.iter().map(|ty| f(t, *ty)).collect();
        }
    }
    for conj in &mut d.lists {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            sig.elem = sig.elem.map(|ty| f(t, ty));
        }
    }
    for conj in &mut d.resources {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            sig.payload = f(t, sig.payload);
        }
    }
    for conj in &mut d.funcs {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            sig.args = sig.args.iter().map(|ty| f(t, *ty)).collect();
            sig.ret = f(t, sig.ret);
        }
    }
    for conj in &mut d.maps {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            sig.fields = sig.fields.iter().map(|(k, v)| (k.clone(), f(t, *v))).collect();
        }
    }
    d
}

fn mint_owned_resource_aliases_descr(cx: TyCtx<'_>, d: &Descr, candidates: &[(String, Descr)]) -> Descr {
    for (tag, inner) in candidates {
        if resource_payload_type(cx, d).is_some_and(|payload| payload.is_equiv(cx, inner)) {
            return Descr::opaque_of(tag);
        }
    }
    d.clone()
}

#[cfg(test)]
mod types_test;
