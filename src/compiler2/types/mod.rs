//! Interned set-theoretic type implementation.
//!
//! Its `Descr` is private here, and every structural child is a `Ty` allocated
//! by the owning `Types` instance.

mod addressed;
mod arrow_match;
mod axis;
mod bits;
mod canon;
mod closure_surface_var;
mod conj;
mod descr;
mod dnf;
mod emptiness;
mod format;
mod order;
#[cfg(test)]
mod regular;
mod render_bindings;
mod sigs;

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use crate::dispatch_matrix::demand::DispatchDemand;
use crate::finite_set::FiniteSet;
use crate::fz_ir::FnId;
use crate::runtime_type_predicate::{
    CallableShape, CallableShapes, ListShape, ListShapes, RuntimeTypePredicate, TupleShapes,
};

use super::identity::ActivationSignature;
use super::protocol::{ProtocolDomainObligation, is_protocol_domain_tag};
use crate::type_expr::opaque_owner_module;
use crate::types::{
    ClosureTypes as SharedClosureTypes, RenderTypes as SharedRenderTypes, Types as SharedTypes,
    VisibilityTypes as SharedVisibilityTypes,
};
use bits::BasicBits;

pub use crate::types::{
    BuiltinOpaque, CallableClause, CallableValueKind, ClosureLitInfo, ClosureTarget, MapKey, OpaqueVisibilityError,
    Sigma, TypeVarId,
};

pub use arrow_match::ArrowMatch;

pub(crate) use canon::TyCanon;

use crate::modules::identity::ModuleName;
use addressed::AddrStep;
#[cfg(test)]
pub(crate) use closure_surface_var::{ClosureSurfacePos, decode_closure_surface_var};
use closure_surface_var::{closure_ret_var_id, closure_var_id};
use conj::Conj;
use descr::OpaqueTag;
use descr::{Descr, DescrOf};
use dnf::dnf_intersect_with;
#[cfg(test)]
use regular::ComponentRef;
use sigs::{ArrowSig, ClosureLit, ListSig, MapTag, MergeSig, PosMeet, ResourceSig, StructTag, TupleSig, TupleSigOf};
#[cfg(test)]
use sigs::{ArrowSigOf, ClosureLitOf, ListSigOf};

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

pub struct Types {
    interner: TypeInterner,
    /// The ids of every fixed core type, interned when the store is built.
    ///
    /// These descriptors have no operand and are already normal forms, so
    /// their ids are stable for the life of the store. Holding them makes each
    /// fixed constructor a handle read: no descriptor is rebuilt, hashed, or
    /// searched merely to rediscover a core type the arena already owns.
    core: CoreTypes,
    comparisons: RefCell<ComparisonCache>,
    binary_type_operations: BinaryTypeOperationResults,
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
    callable_origins: order::CallableOrigins,
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

/// The operand-free types every [`Types`] world knows from birth.
///
/// This is not an alternate interner. Each field is the one `Ty` the ordinary
/// interner assigned to its already-normal descriptor at world construction.
/// Keeping these handles is the direct, zero-work route for fixed constructors;
/// operand-dependent constructors remain at the sole [`Types::intern`] boundary.
struct CoreTypes {
    any: Ty,
    none: Ty,
    nil: Ty,
    bool_t: Ty,
    int: Ty,
    float: Ty,
    atom: Ty,
    empty_list: Ty,
    str_t: Ty,
    map_top: Ty,
    pid: Ty,
    reference: Ty,
    c_pointer: Ty,
}

impl Default for Types {
    fn default() -> Self {
        Self::with_constants()
    }
}

#[derive(Default)]
struct TypeInterner {
    arena: Vec<Descr>,
    index: HashMap<InternKey, Ty>,
    #[cfg(test)]
    work: InterningWork,
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, expect(clippy::large_enum_variant))]
enum InternKey {
    Direct(Descr),
    #[cfg(test)]
    Regular(Box<regular::RegularKey>),
}

pub(super) trait TupleCoordinateOps<R: Clone> {
    fn is_subtype(&self, positive: &R, negative: &R) -> bool;
    fn has_vars(&self, reference: &R) -> bool;
    fn difference(&mut self, positive: R, negative: R) -> Option<R>;
}

pub(super) trait CallableSurfaceOps<R: Clone> {
    fn named_arg(&mut self, fn_id: FnId, position: usize) -> R;
    fn named_ret(&mut self, fn_id: FnId) -> R;
    fn any(&mut self) -> R;
}

impl TupleCoordinateOps<Ty> for Types {
    fn is_subtype(&self, positive: &Ty, negative: &Ty) -> bool {
        Types::is_subtype(self, positive, negative)
    }

    fn has_vars(&self, reference: &Ty) -> bool {
        Types::has_vars(self, reference)
    }

    fn difference(&mut self, positive: Ty, negative: Ty) -> Option<Ty> {
        Some(Types::difference(self, positive, negative))
    }
}

impl CallableSurfaceOps<Ty> for Types {
    fn named_arg(&mut self, fn_id: FnId, position: usize) -> Ty {
        self.type_var(closure_var_id(fn_id, position))
    }

    fn named_ret(&mut self, fn_id: FnId) -> Ty {
        self.type_var(closure_ret_var_id(fn_id))
    }

    fn any(&mut self) -> Ty {
        Types::any(self)
    }
}

pub(super) fn normalize_tuple_coordinate_difference_with<R: Clone>(
    ops: &mut impl TupleCoordinateOps<R>,
    clause: Conj<TupleSigOf<R>>,
) -> Conj<TupleSigOf<R>> {
    let ([positive], [negative]) = (clause.pos.as_slice(), clause.neg.as_slice()) else {
        return clause;
    };
    if positive.elems.len() != negative.elems.len()
        || positive
            .elems
            .iter()
            .chain(&negative.elems)
            .any(|reference| ops.has_vars(reference))
    {
        return clause;
    }
    let differing = positive
        .elems
        .iter()
        .zip(&negative.elems)
        .enumerate()
        .filter_map(|(index, (positive, negative))| (!ops.is_subtype(positive, negative)).then_some(index))
        .collect::<Vec<_>>();
    let [index] = differing.as_slice() else {
        return clause;
    };
    let Some(difference) = ops.difference(positive.elems[*index].clone(), negative.elems[*index].clone()) else {
        return clause;
    };
    let mut elems = positive.elems.clone();
    elems[*index] = difference;
    Conj::pos_of(TupleSigOf { elems })
}

fn normalize_literal_callable_surfaces_with<R: Clone>(ops: &mut impl CallableSurfaceOps<R>, d: &mut DescrOf<R>) {
    for sig in d
        .funcs
        .iter_mut()
        .flat_map(|clause| clause.pos.iter_mut().chain(&mut clause.neg))
    {
        let Some(lit) = &sig.lit else {
            continue;
        };
        let arity = sig.args.len();
        match lit.fn_id {
            Some(fn_id) => {
                sig.args = (0..arity).map(|position| ops.named_arg(fn_id, position)).collect();
                sig.ret = ops.named_ret(fn_id);
            }
            None => {
                let any = ops.any();
                sig.args = vec![any.clone(); arity];
                sig.ret = any;
            }
        }
    }
}

/// Test-only accounting for the sole type persistence boundary.
///
/// A no-op type operation must return its existing [`Ty`] before it reaches
/// this boundary. The counters deliberately measure boundary work, rather than
/// wall time, so the contract holds across machines and build profiles.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct InterningWorkStats {
    pub identity_shortcuts: usize,
    pub raw_index_probes: usize,
    pub normalizations: usize,
    pub canonical_index_probes: usize,
    pub inserted: usize,
}

#[cfg(test)]
#[derive(Default)]
struct InterningWork {
    identity_shortcuts: usize,
    raw_index_probes: usize,
    normalizations: usize,
    canonical_index_probes: usize,
    inserted: usize,
}

#[derive(Default)]
struct ComparisonCache {
    outcomes: HashMap<ComparisonKey, ComparisonOutcome>,
    #[cfg(test)]
    hits: usize,
    #[cfg(test)]
    misses: usize,
    #[cfg(test)]
    semantic_order_hits: usize,
    #[cfg(test)]
    semantic_order_misses: usize,
}

/// Results of pure binary operations over immutable type handles.
///
/// A result enters only after the ordinary operation has produced an interned
/// `Ty`. The table is therefore not an alternate descriptor index or
/// normalization authority: its keys are two `u32` handles and an operation
/// tag, and its values are identities the interner already owns.
#[derive(Default)]
struct BinaryTypeOperationResults {
    results: HashMap<BinaryTypeOperation, Ty>,
    #[cfg(test)]
    work: BinaryTypeOperationStats,
}

/// The operand order belongs to the operation's current exact result unless
/// the operation explicitly normalizes it at the call site. In particular,
/// `difference` is directional, and `intersect` currently preserves its
/// directional survivor where distinct ids are mutually subtype.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum BinaryTypeOperation {
    Union(Ty, Ty),
    Intersect(Ty, Ty),
    Difference(Ty, Ty),
    RefineWiden(Ty, Ty),
}

/// Test-only work accounting for the immutable binary-operation result table.
///
/// The production table stores only canonical answers. These counts make its
/// reuse observable without charging telemetry or wall-clock noise to a test.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct BinaryTypeOperationStats {
    pub union: BinaryTypeOperationCount,
    pub intersect: BinaryTypeOperationCount,
    pub difference: BinaryTypeOperationCount,
    pub refine_widen: BinaryTypeOperationCount,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct BinaryTypeOperationCount {
    pub hits: usize,
    pub misses: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ComparisonKey {
    Subtype(Ty, Ty),
    Disjoint(Ty, Ty),
    ValueDisjoint(Ty, Ty),
    Equivalent(Ty, Ty),
    /// `Types::row_column_dominates`. NOT symmetric: the two positions mean
    /// different things, so this key is never built through `symmetric_key`.
    RowColumnDominates(Ty, Ty),
    ActivationArrowOrder(Ty, Ty),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ComparisonOutcome {
    Predicate(bool),
    Order(std::cmp::Ordering),
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
        match self.arena.get(t.0 as usize) {
            Some(descr) => descr,
            None => panic!("unknown interned type id {}", t.0),
        }
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
    #[inline]
    fn identity_shortcut(&mut self) {
        #[cfg(test)]
        {
            self.work.identity_shortcuts += 1;
        }
    }

    fn intern(&mut self, d: Descr) -> Ty {
        #[cfg(test)]
        {
            self.work.canonical_index_probes += 1;
        }
        if let Some(ty) = self.index.get(&InternKey::Direct(d.clone())) {
            return *ty;
        }
        #[cfg(debug_assertions)]
        self.debug_assert_dnf_axes_hygienic(&d);
        let raw = self.arena.len();
        assert!(u32::try_from(raw).is_ok(), "type interner exhausted ids");
        let ty = Ty(raw as u32);
        self.arena.push(d.clone());
        self.index.insert(InternKey::Direct(d), ty);
        #[cfg(test)]
        {
            self.work.inserted += 1;
        }
        ty
    }

    /// The id already given to this exact descriptor, if it has one.
    ///
    /// A descriptor the index holds was normalized on its way in, and
    /// normalization is a pure function of the descriptor — every step reads
    /// the descriptor's own bytes, the immutable descriptors of the ids it
    /// names, and the stable identity that resolves a completed structural tie
    /// (`super::order` states the one rule that makes this true of clause
    /// order). So the normal form it was given then is the normal form it would
    /// be given now, and the id can be returned without re-deriving it.
    fn lookup(&mut self, d: &Descr) -> Option<Ty> {
        #[cfg(test)]
        {
            self.work.raw_index_probes += 1;
        }
        self.index.get(&InternKey::Direct(d.clone())).copied()
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.arena.len()
    }

    #[cfg(test)]
    fn lookup_regular(&self, key: &regular::RegularKey) -> Option<Ty> {
        self.index.get(&InternKey::Regular(Box::new(key.clone()))).copied()
    }

    #[cfg(test)]
    fn intern_regular(&mut self, keys: Vec<regular::RegularKey>, descriptors: Vec<Descr>) -> Vec<Ty> {
        assert_eq!(keys.len(), descriptors.len(), "regular keys and descriptors must align");
        assert!(
            keys.iter().all(|key| self.lookup_regular(key).is_none()),
            "regular component insertion raced an existing identity"
        );
        let first = self.arena.len();
        let last = first
            .checked_add(descriptors.len())
            .expect("type interner exhausted ids");
        assert!(
            u32::try_from(last.saturating_sub(1)).is_ok(),
            "type interner exhausted ids"
        );
        let tys = (first..last).map(|raw| Ty(raw as u32)).collect::<Vec<_>>();

        for (ty, descriptor) in tys.iter().copied().zip(descriptors.iter()) {
            assert!(
                !self.index.contains_key(&InternKey::Direct(descriptor.clone())),
                "regular component body was already interned directly"
            );
            self.arena.push(descriptor.clone());
            self.index.insert(InternKey::Direct(descriptor.clone()), ty);
        }
        for (key, ty) in keys.into_iter().zip(tys.iter().copied()) {
            assert!(self.index.insert(InternKey::Regular(Box::new(key)), ty).is_none());
        }
        #[cfg(test)]
        {
            self.work.inserted += tys.len();
        }
        tys
    }

    fn normalized(&mut self) {
        #[cfg(test)]
        {
            self.work.normalizations += 1;
        }
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

    /// The debug half of the interned-DNF invariant: a descriptor that reaches
    /// the index carries no provably-empty clause, no missed absorption on a
    /// literal-free axis, and no exact duplicate on a literal-bearing callable
    /// axis. This runs on an index MISS, so it costs one sweep per distinct
    /// descriptor.
    #[cfg(debug_assertions)]
    fn debug_assert_dnf_axes_hygienic(&self, d: &Descr) {
        let cx = self.ctx();
        debug_assert_no_empty_clauses(cx, &d.tuples, emptiness::tuple_clause_empty, "tuples");
        debug_assert_no_empty_clauses(cx, &d.lists, emptiness::list_clause_empty, "lists");
        debug_assert_no_empty_clauses(cx, &d.resources, emptiness::resource_clause_empty, "resources");
        debug_assert_no_empty_clauses(cx, &d.funcs, emptiness::func_clause_empty, "funcs");
        debug_assert_no_empty_clauses(cx, &d.maps, emptiness::map_clause_empty, "maps");
        debug_assert_absorbed(cx, &d.tuples, "tuple", &axis::TUPLES);
        debug_assert_absorbed(cx, &d.lists, "list", &axis::LISTS);
        debug_assert_absorbed(cx, &d.resources, "resource", &axis::RESOURCES);
        debug_assert_absorbed(cx, &d.maps, "map", &axis::MAPS);
        if callable_axis_is_literal_free(&d.funcs) {
            debug_assert_absorbed(cx, &d.funcs, "callable", &axis::FUNCS);
        }
        debug_assert_lists_merged(&d.lists);
        debug_assert_no_exact_duplicates(&d.funcs, "funcs");
    }
}

/// The list axis reaches the index already merged: `[]` and a clause of
/// non-empty lists are ONE clause by then. Stated as a fixpoint of the merge
/// itself, which is what makes it a statement about the clause SET and holds
/// for the clauses the boundary left alone as well.
#[cfg(debug_assertions)]
fn debug_assert_lists_merged(clauses: &[Conj<ListSig>]) {
    let mut merged = clauses.to_vec();
    axis::merge_empty_list_clause(&mut merged);
    debug_assert!(
        merged == clauses,
        "interned list axis still has an empty-list clause to merge"
    );
}

fn callable_axis_is_literal_free(clauses: &[Conj<ArrowSig>]) -> bool {
    clauses
        .iter()
        .flat_map(|clause| clause.pos.iter().chain(&clause.neg))
        .all(|sig| sig.lit.is_none())
}

/// `A ∨ A = A` on a literal-bearing callable axis.
///
/// Literal-free clauses get the stronger coverage rule. Erasure runs in place,
/// so a union that legitimately kept one clause per closure brand can become
/// `A ∨ A` when the brands go. Without this collapse `funcs = [A, A]` interns
/// as a different `Ty` than `funcs = [A]`, and the key stops being a join
/// homomorphism.
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
fn debug_assert_no_empty_clauses<T>(
    cx: TyCtx<'_>,
    clauses: &[Conj<T>],
    clause_empty: fn(TyCtx<'_>, &Conj<T>, &mut emptiness::Memo) -> bool,
    axis: &str,
) {
    for c in clauses {
        debug_assert!(
            !clause_empty(cx, c, &mut emptiness::Memo::default()),
            "interned descr carries a provably-empty clause on the {axis} axis"
        );
    }
}

#[cfg(debug_assertions)]
fn debug_assert_absorbed<T: Clone + PartialEq + 'static>(
    cx: TyCtx<'_>,
    clauses: &[Conj<T>],
    name: &str,
    view: &axis::AxisView<T>,
) {
    if clauses.is_empty() || dnf::is_dnf_top(clauses) {
        return;
    }
    debug_assert!(
        !clauses.iter().any(Conj::is_top),
        "interned descr carries a contentless clause beside others on the {name} axis"
    );
    // Runs on an index MISS only, so it asks both relations directly rather
    // than through the caches the boundary itself goes through.
    let subtype = &|narrower: &Ty, wider: &Ty| cx.descr(narrower).is_subtype(cx, cx.descr(wider));
    let covers = &|wider: &Descr, narrower: &Descr| narrower.is_subtype(cx, wider);
    // An axis its clauses cover is written as the ONE spelling of its top, the
    // contentless clause, which the early return above has already let through.
    // Reaching here saturated means the boundary left a second spelling.
    debug_assert!(
        !axis::axis_is_top(cx, clauses, covers, view),
        "interned descr carries a saturated {name} axis the boundary did not collapse"
    );
    let keep = vec![true; clauses.len()];
    for index in 0..clauses.len() {
        debug_assert!(
            !axis::clause_is_covered(cx, subtype, covers, clauses, &keep, index, view),
            "interned descr carries a covered clause on the {name} axis"
        );
    }
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

    /// Every type the store is born knowing: its operand-free core inventory.
    ///
    /// They go in through the interner directly because each descriptor is
    /// already the normal form `Types::intern` would hand back. `any` has one
    /// contentless clause on every axis; `none` has none. Every other entry has
    /// no operand and exactly one descriptor. None of these descriptors has an
    /// empty clause or ordering left to resolve.
    fn with_constants() -> Self {
        let mut interner = TypeInterner::default();
        let core = CoreTypes {
            any: interner.intern(Descr::any()),
            none: interner.intern(Descr::none()),
            nil: interner.intern(Descr::nil()),
            bool_t: interner.intern(Descr::bool_t()),
            int: interner.intern(Descr::int()),
            float: interner.intern(Descr::float()),
            atom: interner.intern(Descr::atom_top()),
            empty_list: interner.intern(Descr::empty_list()),
            str_t: interner.intern(Descr::str_t()),
            map_top: interner.intern(Descr::map_top()),
            pid: interner.intern(Descr::builtin_opaque(BuiltinOpaque::Pid)),
            reference: interner.intern(Descr::builtin_opaque(BuiltinOpaque::Ref)),
            c_pointer: interner.intern(Descr::builtin_opaque(BuiltinOpaque::CPointer)),
        };
        Self {
            interner,
            core,
            comparisons: RefCell::default(),
            binary_type_operations: BinaryTypeOperationResults::default(),
            value_lane_reprs: HashMap::new(),
            address_vars: HashMap::new(),
            address_paths: Vec::new(),
            callable_origins: order::CallableOrigins::new(),
            activation_input_collapses: 0,
        }
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

    pub fn c_pointer(&mut self) -> Ty {
        self.builtin_opaque(BuiltinOpaque::CPointer)
    }

    pub fn pid(&mut self) -> Ty {
        self.builtin_opaque(BuiltinOpaque::Pid)
    }

    pub fn reference(&mut self) -> Ty {
        self.builtin_opaque(BuiltinOpaque::Ref)
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

    /// The persistence boundary, in passes that each leave the next one's
    /// precondition intact.
    ///
    /// THE INDEX ANSWERS FIRST. An interned descriptor's normal form is a pure
    /// function of the descriptor: every pass below reads the descriptor's own
    /// bytes, the immutable descriptors of the ids it names, and the stable
    /// identity that resolves a completed structural tie. Storage clause order
    /// reads nothing mutable outside them either (`order`'s module doc carries
    /// that rule and why the callable axis is where it had to be won).
    /// A descriptor the index already holds is therefore its own normal form,
    /// and the id it was given is the id the whole pass below would arrive at,
    /// so the lookup returns it and the derivation is skipped. That is the
    /// common case by a wide margin — the overwhelming majority of intern calls
    /// re-present a descriptor the arena already has.
    ///
    /// TUPLE NORMALIZATION first, the one rule that reaches a different
    /// CARVING of one type. A ground tuple difference whose cover differs in
    /// exactly one coordinate is still one rectangle, and the axis's plain
    /// rectangles are then fused and widened to the one union of products both
    /// carvings reach: `{A,C} ∨ {B,C}` is `{A∨B, C}`, so
    /// `{[int], :false} ∨ {[int], :true}` and `{[int], :false | :true}` are one
    /// descriptor before identity is assigned. Fusion mints the coordinate it
    /// merges on, through this same boundary; the recursion terminates because
    /// a coordinate names only types interned before it.
    ///
    /// LIST NORMALIZATION comes next, and is the same idea on the list axis. A
    /// list clause says only two things -- does it hold `[]`, and which
    /// non-empty lists does it keep -- so every spelling of one denotation is
    /// rewritten to the one that states them directly: `list(T) ∧ ¬[]` is
    /// `non_empty_list(T)`, a subtraction that removes nothing is not a
    /// constraint, and an axis holding an exact `[]` beside a clause of
    /// non-empty lists is that clause widened. The merge reads the finished
    /// clause SET, never the order the union arrived in, which is what the
    /// union-path normalizer it replaces could not do.
    ///
    /// ORDER follows (fz-kdt.105): every axis goes into canonical clause order, so
    /// a descriptor's clause list is a function of its clause set rather than of
    /// the arrival order that built it. It has to lead the absorption, which
    /// picks the survivor of a mutually-subsuming pair by ARRIVAL — sort
    /// afterwards and the schedule would still be choosing which clause lives.
    ///
    /// The EMPTY-CLAUSE DROP follows, on all five axes: a clause that denotes
    /// nothing is the union identity of its axis, so it goes before anything
    /// reads the clause list. Sweeping every axis is also what keeps the
    /// bottom collapse below cheap: an axis with no empty clause left is empty
    /// exactly when it holds no clause at all, so the collapse's question stops
    /// at the first surviving clause.
    ///
    /// ABSORPTION follows, one rule for every axis whose clauses describe
    /// nothing but the set they denote: a clause the union of its surviving
    /// siblings already covers is dropped, and an axis its clauses between
    /// them cover collapses to that axis's one top spelling, the clause with no
    /// factors. Literal-bearing callable clauses retain their construction
    /// layout and get exact duplicate removal after their surfaces normalize.
    ///
    /// The BOTTOM COLLAPSE closes the pass. The empty set is reachable by many
    /// descriptor shapes — an empty brand slot, empty kind axes under a slot
    /// still at top, a tuple with an empty coordinate — and they all denote
    /// the one set, so they all take the one `none` identity.
    ///
    /// It asks `looks_empty()`, not the recursive emptiness algorithm, and the
    /// empty-clause drop above is what makes that exact: a swept axis holds no
    /// clause that denotes nothing, so "every clause is empty" and "the axis
    /// holds no clause" are the same question. Reading the descriptor
    /// structurally also means the check never descends through interned
    /// children, so it can neither mint the id it is about to reject nor
    /// inherit the recursion's coinductive assumption about a cycle.
    ///
    /// One pass suffices because the composition is idempotent: re-interning an
    /// already-interned descriptor finds its tuple axis already at the carving
    /// fixpoint, sorts an already-sorted list to itself, finds
    /// no empty or subsumed clause left to drop on any axis, no exact duplicate
    /// left to collapse, and answers `none` for `none`, so it hashes to the
    /// descriptor already in the index. Idempotence is also what makes the
    /// lookup above an optimization rather than a second rule: running the pass
    /// on an indexed descriptor would return it unchanged.
    fn intern(&mut self, mut d: Descr) -> Ty {
        if let Some(ty) = self.interner.lookup(&d) {
            return ty;
        }
        self.interner.normalized();
        self.normalize_tuple_axis(&mut d);
        self.normalize_list_clauses(&mut d);
        self.normalize_literal_callable_surfaces(&mut d);
        self.order_clauses(&mut d);
        self.drop_empty_clauses(&mut d);
        self.absorb_covered_clauses(&mut d);
        dedupe_exact_clauses(&mut d.funcs);
        if d.looks_empty() {
            d = Descr::none();
        }
        self.interner.intern(d)
    }

    #[cfg(test)]
    fn intern_regular_component(
        &mut self,
        count: usize,
        build: impl FnOnce(&[ComponentRef]) -> Vec<DescrOf<ComponentRef>>,
    ) -> Vec<Ty> {
        regular::intern(self, count, build)
    }

    /// Return an input whose operation has proved unchanged before any
    /// descriptor is built. This is deliberately not an interner lookup: the
    /// caller already owns the canonical identity.
    #[inline]
    fn unchanged(&mut self, ty: Ty) -> Ty {
        self.interner.identity_shortcut();
        ty
    }

    /// The list axis rewritten to the one normal form in [`axis`], clause by
    /// clause and then across the set.
    fn normalize_list_clauses(&mut self, d: &mut Descr) {
        let clauses = std::mem::take(&mut d.lists);
        d.lists = clauses.into_iter().map(|c| self.list_normal_form(c)).collect();
        axis::merge_empty_list_clause(&mut d.lists);
    }

    /// Direct callable observations are activation coordinates, not value
    /// identity. A named literal has one reproducible owner template; an
    /// anonymous literal keeps only its arity.
    fn normalize_literal_callable_surfaces(&mut self, d: &mut Descr) {
        normalize_literal_callable_surfaces_with(self, d)
    }

    /// One list clause rewritten to what it denotes.
    ///
    /// A clause that denotes nothing is left exactly as it is: the
    /// empty-clause drop below removes it, and rewriting what is about to go
    /// is work for nobody.
    fn list_normal_form(&mut self, c: Conj<ListSig>) -> Conj<ListSig> {
        // A clause that constrains nothing is the axis top, and `is_dnf_top`
        // reads it structurally, so it keeps its empty conjunction.
        if c.is_top() {
            return c;
        }
        // One positive sig over an inhabited element already states both
        // facts, and so does a lone `[]`. The element is interned, so the
        // bottom collapse has already given it the one empty shape and reading
        // the descriptor answers exactly, without a query.
        if let ([sig], []) = (c.pos.as_slice(), c.neg.as_slice())
            && sig.elem.is_none_or(|elem| !self.descr(&elem).looks_empty())
        {
            return c;
        }
        if Self::needs_element_arithmetic(&c) && self.clause_has_vars(&c) {
            return c;
        }
        let denotation = {
            let cx = self.ctx();
            emptiness::list_denotation(cx, &c, &mut emptiness::Memo::default())
        };
        match denotation {
            None => c,
            Some(denotation) => axis::list_clause_of(denotation, &mut |d| self.intern(d)),
        }
    }

    /// Whether reading a list clause's denotation has to MEET or SUBTRACT
    /// element types rather than only read the `[]` flags.
    ///
    /// That arithmetic is what a type variable makes unsafe to bake in. The
    /// kernel reads a variable as an atom disjoint from everything else, so
    /// `list(α) ∧ list(int)` has no non-empty fragment and `non_empty_list(α)
    /// ∧ ¬non_empty_list(int)` subtracts nothing -- both true of the clause as
    /// it stands, neither true once `α` is substituted. The `[]` bookkeeping
    /// carries no such risk: it reads flags the substitution never touches.
    fn needs_element_arithmetic(c: &Conj<ListSig>) -> bool {
        c.pos.len() > 1 || c.neg.iter().any(|n| n.elem.is_some())
    }

    fn clause_has_vars(&self, c: &Conj<ListSig>) -> bool {
        c.pos
            .iter()
            .chain(&c.neg)
            .filter_map(|sig| sig.elem)
            .any(|elem| self.has_vars(&elem))
    }

    fn order_clauses(&self, d: &mut Descr) {
        self.clause_order().sort_axes(d);
    }

    fn clause_order(&self) -> order::ClauseOrder<'_> {
        order::ClauseOrder::new(self.ctx())
    }

    fn activation_order(&self) -> order::ClauseOrder<'_> {
        order::ClauseOrder::for_activation(self.ctx(), &self.callable_origins)
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
    /// origins are immutable, so one normalized pair has one verdict for this
    /// `Types`/`World` lifetime and the reverse direction reuses its inverse.
    pub(crate) fn cmp_activation_ty(&self, a: Ty, b: Ty) -> std::cmp::Ordering {
        if a == b {
            return std::cmp::Ordering::Equal;
        }
        let (low, high, reversed) = if a < b { (a, b, false) } else { (b, a, true) };
        let key = ComparisonKey::ActivationArrowOrder(low, high);
        let normalized = if let Some(outcome) = self.comparisons.borrow_mut().hit(key) {
            outcome.order()
        } else {
            self.assert_activation_origins_registered(low);
            self.assert_activation_origins_registered(high);
            let order = self.activation_order().cmp_ty(low, high);
            self.comparisons.borrow_mut().miss(key, ComparisonOutcome::Order(order));
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

    /// Total typed order for the coordinate record that specializes one body.
    ///
    /// An activation is not an arrow value: its inputs and pending result are
    /// planner-owned coordinates. Keep their ordering beside the existing
    /// typed `Ty` order rather than re-packing them onto the callable axis.
    pub(crate) fn cmp_activation_signature(
        &self,
        left: &ActivationSignature,
        right: &ActivationSignature,
    ) -> std::cmp::Ordering {
        self.cmp_activation_tys(&left.inputs, &right.inputs)
            .then_with(|| self.cmp_activation_ty(left.result, right.result))
    }

    /// Total typed order for the direct callable observations attached to an
    /// activation key.  `BTreeSet`'s raw `Ty` order is only a storage detail;
    /// sorting each set through the owning interner keeps emitted-product order
    /// semantic and stable across allocation histories.
    pub(crate) fn cmp_activation_callable_surfaces(
        &self,
        left: &[BTreeSet<ActivationSignature>],
        right: &[BTreeSet<ActivationSignature>],
    ) -> std::cmp::Ordering {
        for (left_slot, right_slot) in left.iter().zip(right) {
            let mut left_surfaces = left_slot.iter().collect::<Vec<_>>();
            let mut right_surfaces = right_slot.iter().collect::<Vec<_>>();
            left_surfaces.sort_by(|a, b| self.cmp_activation_signature(a, b));
            right_surfaces.sort_by(|a, b| self.cmp_activation_signature(a, b));
            for (left_surface, right_surface) in left_surfaces.iter().zip(&right_surfaces) {
                let order = self.cmp_activation_signature(left_surface, right_surface);
                if order != std::cmp::Ordering::Equal {
                    return order;
                }
            }
            let order = left_surfaces.len().cmp(&right_surfaces.len());
            if order != std::cmp::Ordering::Equal {
                return order;
            }
        }
        left.len().cmp(&right.len())
    }

    fn assert_activation_origins_registered(&self, root: Ty) {
        self.activation_reachable(root, |ty| {
            let d = self.descr(&ty);
            for sig in d.funcs.iter().flat_map(|conj| conj.pos.iter().chain(conj.neg.iter())) {
                if let Some(lit) = &sig.lit
                    && let Some(fn_id) = lit.fn_id
                {
                    assert!(
                        self.callable_origins.contains_key(&fn_id),
                        "activation arrow names unregistered callable {}",
                        fn_id.0
                    );
                }
            }
        });
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

    /// `A ∨ ∅ = A` on every axis, by the shared rule in [`axis`]. Running it at
    /// intern covers every construction route (union, intersect, difference,
    /// substitution) with one pass, and keeps garbage from accumulating across
    /// fixpoint iterations or doubling `dnf_neg` factors downstream. Tuple
    /// coordinates are asked through the memoized `Types::is_empty`.
    fn drop_empty_clauses(&self, d: &mut Descr) {
        axis::drop_empty_clauses(self.ctx(), d, &|ty| self.is_empty(ty));
    }

    /// Every literal-free axis is absorbed by the shared rule in [`axis`].
    ///
    /// A closure literal retains its capture layout until the value reaches
    /// the transport projection; the layout is evidence about construction,
    /// not an alternative spelling of a bare callable value.
    fn absorb_covered_clauses(&self, d: &mut Descr) {
        self.absorb_one_axis(&mut d.tuples, &axis::TUPLES);
        self.absorb_one_axis(&mut d.lists, &axis::LISTS);
        self.absorb_one_axis(&mut d.resources, &axis::RESOURCES);
        self.absorb_one_axis(&mut d.maps, &axis::MAPS);
        if callable_axis_is_literal_free(&d.funcs) {
            self.absorb_one_axis(&mut d.funcs, &axis::FUNCS);
        }
    }

    fn absorb_one_axis<T: Clone + 'static>(&self, clauses: &mut Vec<Conj<T>>, view: &axis::AxisView<T>) {
        let cx = self.ctx();
        let subtype = &|narrower: &Ty, wider: &Ty| self.is_subtype(narrower, wider);
        let covers = &|wider: &Descr, narrower: &Descr| narrower.is_subtype(cx, wider);
        axis::absorb_axis(cx, clauses, subtype, covers, view);
    }

    /// The tuple axis's own normal form, in two steps.
    ///
    /// First each clause alone: a ground difference whose cover differs in
    /// exactly one coordinate is still one rectangle, so it is rewritten to
    /// one — which also turns a clause that was carrying a negative into a
    /// plain rectangle the step below can carve.
    ///
    /// Then the axis as a whole: its plain rectangles go through
    /// [`axis::fuse_tuple_rects`], which fuses and widens until one union of
    /// products has one carving. Clauses that are not plain rectangles keep
    /// their form; the clause sort below puts the axis back in canonical order
    /// either way.
    ///
    /// Carving works on descriptors and the coordinates it builds are interned
    /// here, so a coordinate is a `Ty` by the time the descriptor reaches the
    /// index. That recursion terminates for the same reason the rest of the
    /// boundary does: a coordinate names only types interned before it.
    fn normalize_tuple_axis(&mut self, d: &mut Descr) {
        let clauses = std::mem::take(&mut d.tuples);
        let mut complex = Vec::with_capacity(clauses.len());
        let mut rects: Vec<axis::Rect> = Vec::with_capacity(clauses.len());
        for clause in clauses {
            let clause = self.normalize_tuple_coordinate_difference(clause);
            match (clause.pos.as_slice(), clause.neg.as_slice()) {
                ([sig], []) => rects.push(sig.elems.iter().map(|ty| axis::Coord::Interned(*ty)).collect()),
                _ => complex.push(clause),
            }
        }
        let rects = axis::fuse_tuple_rects(self.ctx(), rects);
        d.tuples = complex;
        for rect in rects {
            let elems = rect
                .into_iter()
                .map(|coord| match coord {
                    axis::Coord::Interned(ty) => ty,
                    axis::Coord::Built(descr) => self.intern(*descr),
                })
                .collect();
            d.tuples.push(Conj::pos_of(TupleSig { elems }));
        }
    }

    /// `P₀ × … × Pₖ × … × Pₙ \ N₀ × … × Nₖ × … × Nₙ` is one rectangle
    /// whenever every coordinate except `k` is contained in its cover:
    ///
    /// `P₀ × … × (Pₖ \ Nₖ) × … × Pₙ`.
    ///
    /// The descriptor kernel represents the left form as one positive and one
    /// negative tuple signature. It is semantically exact but structurally
    /// distinct from the right form, so it must collapse before `Ty` identity
    /// is assigned. More than one differing coordinate needs a union of
    /// rectangles and deliberately stays in its existing DNF form.
    fn normalize_tuple_coordinate_difference(&mut self, clause: Conj<TupleSig>) -> Conj<TupleSig> {
        normalize_tuple_coordinate_difference_with(self, clause)
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
        if let Some(outcome) = self.comparisons.borrow_mut().hit(key) {
            return outcome.predicate();
        }
        let result = compute(self);
        self.comparisons
            .borrow_mut()
            .miss(key, ComparisonOutcome::Predicate(result));
        result
    }

    fn binary_type_operation(&mut self, key: BinaryTypeOperation, compute: impl FnOnce(&mut Self) -> Ty) -> Ty {
        if let Some(result) = self.binary_type_operations.lookup(key) {
            return result;
        }
        let result = compute(self);
        self.binary_type_operations.remember(key, result);
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
        self.interner
            .arena
            .iter()
            .enumerate()
            .map(|(index, _)| Ty(index as u32))
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn activation_order_evidence_for_test(&self, left: Ty, right: Ty) -> String {
        format!(
            "left={left:?} right={right:?}; left_descr={:?}; right_descr={:?}; \
             activation=({:?}, {:?}); storage=({:?}, {:?}); address_paths={:?}; callable_origins={:?}",
            self.descr(&left),
            self.descr(&right),
            self.cmp_activation_ty(left, right),
            self.cmp_activation_ty(right, left),
            self.cmp_ty(left, right),
            self.cmp_ty(right, left),
            self.address_paths,
            self.callable_origins,
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
    pub(crate) fn interning_work_stats(&self) -> InterningWorkStats {
        let work = &self.interner.work;
        InterningWorkStats {
            identity_shortcuts: work.identity_shortcuts,
            raw_index_probes: work.raw_index_probes,
            normalizations: work.normalizations,
            canonical_index_probes: work.canonical_index_probes,
            inserted: work.inserted,
        }
    }

    #[cfg(test)]
    pub(crate) fn binary_type_operation_stats(&self) -> BinaryTypeOperationStats {
        self.binary_type_operations.work
    }

    #[cfg(test)]
    pub(crate) fn comparison_cache_stats(&self) -> ComparisonCacheStats {
        let cache = self.comparisons.borrow();
        ComparisonCacheStats {
            entries: cache.outcomes.len(),
            hits: cache.hits,
            misses: cache.misses,
            semantic_order_entries: cache
                .outcomes
                .keys()
                .filter(|key| matches!(key, ComparisonKey::ActivationArrowOrder(_, _)))
                .count(),
            semantic_order_hits: cache.semantic_order_hits,
            semantic_order_misses: cache.semantic_order_misses,
        }
    }
}

impl BinaryTypeOperationResults {
    fn lookup(&mut self, key: BinaryTypeOperation) -> Option<Ty> {
        let result = self.results.get(&key).copied();
        #[cfg(test)]
        if result.is_some() {
            self.work.count_for(key).hits += 1;
        }
        result
    }

    fn remember(&mut self, key: BinaryTypeOperation, result: Ty) {
        assert!(
            self.results.insert(key, result).is_none(),
            "an acyclic type operation must not re-enter the same operand pair"
        );
        #[cfg(test)]
        {
            self.work.count_for(key).misses += 1;
        }
    }
}

#[cfg(test)]
impl BinaryTypeOperationStats {
    fn count_for(&mut self, operation: BinaryTypeOperation) -> &mut BinaryTypeOperationCount {
        match operation {
            BinaryTypeOperation::Union(_, _) => &mut self.union,
            BinaryTypeOperation::Intersect(_, _) => &mut self.intersect,
            BinaryTypeOperation::Difference(_, _) => &mut self.difference,
            BinaryTypeOperation::RefineWiden(_, _) => &mut self.refine_widen,
        }
    }
}

impl ComparisonCache {
    fn hit(&mut self, key: ComparisonKey) -> Option<ComparisonOutcome> {
        let result = self.outcomes.get(&key).copied();
        #[cfg(test)]
        if result.is_some() {
            if matches!(key, ComparisonKey::ActivationArrowOrder(_, _)) {
                self.semantic_order_hits += 1;
            } else {
                self.hits += 1;
            }
        }
        result
    }

    fn miss(&mut self, key: ComparisonKey, outcome: ComparisonOutcome) {
        #[cfg(test)]
        {
            if matches!(key, ComparisonKey::ActivationArrowOrder(_, _)) {
                self.semantic_order_misses += 1;
            } else {
                self.misses += 1;
            }
        }
        assert!(self.outcomes.insert(key, outcome).is_none());
    }
}

impl ComparisonOutcome {
    fn predicate(self) -> bool {
        match self {
            Self::Predicate(result) => result,
            Self::Order(_) => unreachable!("a comparison operation has one outcome type"),
        }
    }

    fn order(self) -> std::cmp::Ordering {
        match self {
            Self::Order(result) => result,
            Self::Predicate(_) => unreachable!("a comparison operation has one outcome type"),
        }
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
        self.core.any
    }

    pub fn none(&mut self) -> Ty {
        self.core.none
    }

    pub fn nil(&mut self) -> Ty {
        self.core.nil
    }

    pub fn bool(&mut self) -> Ty {
        self.core.bool_t
    }

    pub fn int(&mut self) -> Ty {
        self.core.int
    }

    /// Numeric literals are VALUES, not types: the lattice deliberately
    /// cannot express a numeric singleton (Elixir's descr draws the same
    /// line). A literal in type position means its kind.
    pub fn int_lit(&mut self, _n: i64) -> Ty {
        self.int()
    }

    pub fn float(&mut self) -> Ty {
        self.core.float
    }

    /// See `int_lit`: a float literal in type position means `float()`.
    pub fn float_lit(&mut self, _f: f64) -> Ty {
        self.float()
    }

    pub fn atom(&mut self) -> Ty {
        self.core.atom
    }

    pub fn atom_lit(&mut self, name: &str) -> Ty {
        self.intern(Descr::atom_lit(name))
    }

    pub fn type_var(&mut self, id: TypeVarId) -> Ty {
        self.intern(Descr::var(id))
    }

    pub fn resource(&mut self, payload: Ty) -> Ty {
        if payload == self.core.none {
            return self.core.none;
        }
        self.intern(Descr::resource_of(payload))
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
        let mut fields = Vec::with_capacity(elems.len());
        for &elem in elems {
            if elem == self.core.none {
                return self.core.none;
            }
            fields.push(elem);
        }
        self.intern(Descr::tuple_of(fields))
    }

    pub fn empty_list(&mut self) -> Ty {
        self.core.empty_list
    }

    pub fn list(&mut self, elem: Ty) -> Ty {
        if elem == self.core.none {
            return self.core.empty_list;
        }
        self.intern(Descr::list_of(elem))
    }

    pub fn non_empty_list(&mut self, elem: Ty) -> Ty {
        if elem == self.core.none {
            return self.core.none;
        }
        self.intern(Descr::non_empty_list_of(elem))
    }

    pub fn map(&mut self, fields: &[(MapKey, Ty)]) -> Ty {
        let Some(final_fields) = self.final_required_fields(fields) else {
            return self.core.none;
        };
        self.intern(Descr::map_of(final_fields))
    }

    pub fn str_t(&mut self) -> Ty {
        self.core.str_t
    }

    pub fn map_top(&mut self) -> Ty {
        self.core.map_top
    }

    pub fn mint_brand(&mut self, inner: Ty, name: &str) -> Ty {
        let mut d = self.descr(&inner).clone();
        d.brands = FiniteSet::lit(name.to_string());
        self.intern(d)
    }

    pub fn opaque_of(&mut self, name: &str) -> Ty {
        self.intern(Descr::opaque_of(name))
    }

    pub fn builtin_opaque(&mut self, builtin: BuiltinOpaque) -> Ty {
        match builtin {
            BuiltinOpaque::Pid => self.core.pid,
            BuiltinOpaque::Ref => self.core.reference,
            BuiltinOpaque::CPointer => self.core.c_pointer,
        }
    }

    pub(crate) fn nominal_protocol_target(&mut self, name: ModuleName) -> Ty {
        self.intern(Descr {
            opaques: FiniteSet::lit(OpaqueTag::ProtocolTarget(name)),
            ..Descr::unbranded()
        })
    }

    pub(crate) fn struct_map(
        &mut self,
        module: super::identity::ModuleId,
        name: ModuleName,
        fields: &[(MapKey, Ty)],
    ) -> Ty {
        let Some(final_fields) = self.final_required_fields(fields) else {
            return self.core.none;
        };
        self.intern(Descr::struct_map(StructTag { module, name }, final_fields))
    }

    fn final_required_fields(&self, fields: &[(MapKey, Ty)]) -> Option<BTreeMap<MapKey, Ty>> {
        let none = self.core.none;
        let mut final_fields = BTreeMap::new();
        let mut empty_required_fields = 0;
        for (key, value) in fields {
            if final_fields.insert(key.clone(), *value) == Some(none) {
                empty_required_fields -= 1;
            }
            if *value == none {
                empty_required_fields += 1;
            }
        }
        (empty_required_fields == 0).then_some(final_fields)
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

    pub(crate) fn exclusive_tuple_root_arity(&self, a: &Ty) -> Option<usize> {
        let descr = self.descr(a);
        if !has_only_tuple_runtime_roots(descr) {
            return None;
        }
        let arities = tuple_root_arities(descr);
        let mut arities = arities.finite_elems()?;
        let arity = arities.next()?;
        arities.next().is_none().then_some(arity)
    }

    pub fn refine_map_field(&mut self, a: &Ty, key: &MapKey, v: &Ty) -> Ty {
        let Some(d) = self.descr(a).refine_map_field(key, *v) else {
            return self.unchanged(*a);
        };
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

    pub fn refine_widen(&mut self, a: &Ty, b: &Ty) -> Ty {
        if a == b {
            return self.unchanged(*a);
        }
        self.binary_type_operation(BinaryTypeOperation::RefineWiden(*a, *b), |types| {
            refine_widen_uncached(types, *a, *b)
        })
    }

    pub fn convergence_class(&mut self, a: &Ty) -> Ty {
        let descr = self.descr(a).clone();
        let any = self.any();
        if descr.as_pure_list(any).is_some() {
            self.list(any)
        } else if let Some(tuple) = descr.pure_tuple() {
            let elems = tuple
                .elems
                .iter()
                .map(|elem| self.convergence_class(elem))
                .collect::<Vec<_>>();
            self.tuple(&elems)
        } else if let Some(resource) = descr.pure_resource(any) {
            let payload = self.convergence_class(&resource.payload);
            self.resource(payload)
        } else if descr.is_pure_callable() {
            self.intern(Descr::fun_top())
        } else if let Some(record) = descr.pure_record() {
            let fields = record
                .fields
                .iter()
                .map(|(key, value)| (key.clone(), self.convergence_class(value)))
                .collect::<Vec<_>>();
            self.intern(Descr::record(record.tag.clone(), fields))
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
    /// fz-y6w termination holds. Depth is capped for LIST families: past
    /// `ADDRESS_COLLAPSE_DEPTH` nested addressing steps the element tops out at
    /// `any` (the earned depth ⊤) so a self-nesting list can never grow the
    /// address path without bound. The cap is checked inside the
    /// `is_pure_list_family` branch alone; the tuple, resource and map branches
    /// recurse on the type that arrives, so their depth is bounded by that type
    /// rather than by this function.
    ///
    /// `keep_elements` says DEMAND reached this position (fz-kdt.183): the value
    /// here is one some body on the forwarding chain asks about, so its own
    /// structure decides which callee activation -- and therefore which return
    /// -- this key names, and a ground element is the key's meaning rather than
    /// freight. It is set only under a demanded list's element; every other
    /// caller passes `false` and gets the freight collapse unchanged.
    fn convergence_class_at(&mut self, a: &Ty, path: &[AddrStep], keep_elements: bool) -> Ty {
        const ADDRESS_COLLAPSE_DEPTH: usize = 8;
        let descr = self.descr(a).clone();
        if descr.is_pure_list_family() {
            if path.len() >= ADDRESS_COLLAPSE_DEPTH {
                let any = self.any();
                return self.list(any);
            }
            let mut child = path.to_vec();
            child.push(AddrStep::Elem);
            let elem = if keep_elements {
                let elem_descr = list_element_type(self.ctx(), &descr);
                let elem = self.intern(elem_descr);
                self.convergence_class_at(&elem, &child, true)
            } else {
                self.address_var(&child)
            };
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
                    self.convergence_class_at(elem, &child, keep_elements)
                })
                .collect::<Vec<_>>();
            self.tuple(&elems)
        } else if let Some(resource) = descr.pure_resource(self.any()) {
            let payload = resource.payload;
            let mut child = path.to_vec();
            child.push(AddrStep::Payload);
            let payload = self.convergence_class_at(&payload, &child, keep_elements);
            self.resource(payload)
        } else if let Some(record) = descr.pure_record() {
            let fields = record
                .fields
                .iter()
                .enumerate()
                .map(|(j, (key, value))| {
                    let mut child = path.to_vec();
                    child.push(AddrStep::MapField(j as u16));
                    (key.clone(), self.convergence_class_at(value, &child, keep_elements))
                })
                .collect::<Vec<_>>();
            self.intern(Descr::record(record.tag.clone(), fields))
        } else if keep_elements && self.has_vars(a) {
            // A kept leaf that still carries a free variable is replaced by the
            // canonical address var for its position, never kept verbatim: the
            // collapsed arrow must be canonically ADDRESSED so re-addressing it
            // through `address_inputs` is the identity (fz-hwn.27,
            // fz-go4.18.3.2.1). Ground leaves are the key's meaning and survive.
            self.address_var(path)
        } else {
            *a
        }
    }

    /// Derive a recursive activation's KEY inputs from precise evidence by
    /// widening every UNDEMANDED subtree to its convergence class, so the
    /// recursive ascent settles (fz-y6w bounded specialization). The mask is
    /// `InputDemand::forwarded_dispatch`: what this body asks about a slot,
    /// joined with what every callee it forwards the slot to asks (fz-kdt.183).
    /// Demand is type-shaped: a tuple tag can remain precise while its payload
    /// collapses.
    ///
    /// `list(int)` and `list(any)` share one recursive key only where the list
    /// is FREIGHT -- nothing on the forwarding chain reads it. A list some body
    /// downstream splits into head and tail keeps its element, because the
    /// element decides which callee activation is reached and therefore what
    /// this activation publishes as its return. A `Whole` slot has no collapse
    /// at all, and forwarding can hand a `Whole` up from a callee that tests a
    /// literal; fz-y6w's termination argument does not cover a slot with no
    /// collapse.
    ///
    /// This is one coordinate-record operation applied after
    /// whole-scope addressing. `convergence_class` only collapses pure lists
    /// (`list(τ) -> list(any)`), so it is invariant under that addressing. The
    /// precise evidence remains in `ActivationInputs`; this returns the derived
    /// dispatch coordinates, and key != evidence is intentional.
    pub(crate) fn convergence_collapse_inputs(
        &mut self,
        inputs: &[Ty],
        mask: &[DispatchDemand],
        returned: &[DispatchDemand],
    ) -> Box<[Ty]> {
        inputs
            .iter()
            .enumerate()
            .map(|(slot, param)| {
                let demand = mask.get(slot).unwrap_or(&DispatchDemand::Whole);
                let result = returned.get(slot).unwrap_or(&DispatchDemand::Ignore);
                let path = [AddrStep::Param(slot as u16)];
                self.convergence_collapse_ty(*param, demand, result, &path, true)
            })
            .collect()
    }

    /// The transported-callable key collapse (fz-6gb, fz-kdt.127): erase
    /// closure BRANDS from non-dispatch input coordinates, leaving everything
    /// else -- data types, callable surfaces, CAPTURE TYPES, dispatch-relevant
    /// slots -- exactly as the evidence stated it. Two closures of the same
    /// shape then key one activation of a function that only carries them,
    /// while a slot the function dispatches on keeps brand identity, and two
    /// capture types through one slot stay two keys because the body a key
    /// names grounds its callees' capture lanes. Unlike
    /// [`convergence_collapse_inputs`], no slot becomes an address var: this erasure
    /// is value-language throughout, so nothing key-shaped can leak into
    /// evidence.
    ///
    /// The mask is `InputDemand::local_dispatch`, never the forwarded half: the
    /// question is "does a clause of THIS body test this slot", and a body that
    /// merely hands a callable to a callee that tests it still cannot tell two
    /// same-shape lambdas apart itself (fz-kdt.183).
    ///
    /// Keeping the capture tuple is the conservative context-free rule
    /// (fz-kdt.169). Whole-tuple or arity-only erasure would also merge one
    /// lambda closed over one `int` with that lambda closed over one `float`;
    /// preserving dispatch-free static grounding while erasing more therefore
    /// requires a flow-sensitive non-observability proof.
    pub(crate) fn erase_transported_closure_identity_inputs(
        &mut self,
        inputs: &[Ty],
        mask: &[DispatchDemand],
    ) -> Box<[Ty]> {
        inputs
            .iter()
            .enumerate()
            .map(|(slot, param)| match mask.get(slot).unwrap_or(&DispatchDemand::Whole) {
                DispatchDemand::Ignore => self.erase_transported_closure_identity_for_key(param),
                _ => *param,
            })
            .collect()
    }

    pub(crate) fn convergence_collapse_evidence_inputs(&mut self, inputs: &[Ty], mask: &[DispatchDemand]) -> Vec<Ty> {
        inputs
            .iter()
            .enumerate()
            .map(|(slot, input)| {
                let demand = mask.get(slot).unwrap_or(&DispatchDemand::Whole);
                let path = [AddrStep::Param(slot as u16)];
                // EVIDENCE reads the dispatch axis alone. The `returned` axis
                // asks the key to KEEP a position, and evidence already keeps
                // every ground position verbatim (the `Ignore` arm widens only
                // what carries variables), so there is nothing for it to say
                // here (fz-kdt.199).
                self.convergence_collapse_ty(*input, demand, &DispatchDemand::Ignore, &path, false)
            })
            .collect()
    }

    fn convergence_collapse_ty(
        &mut self,
        ty: Ty,
        demand: &DispatchDemand,
        returned: &DispatchDemand,
        path: &[AddrStep],
        collapse_concrete_ignored: bool,
    ) -> Ty {
        // The two axes ask for two collapses and the DISPATCH axis wins where
        // they meet: `Whole` there means a question reads the value itself, so
        // the key keeps it verbatim, which is at least as precise as the class
        // the `returned` axis would keep (fz-kdt.199).
        if !matches!(demand, DispatchDemand::Whole)
            && let Some(collapsed) = self.convergence_collapse_returned(ty, demand, returned, path)
        {
            return collapsed;
        }
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
                    self.convergence_class_at(&ty, path, false)
                } else if self.has_vars(&ty) && !self.descr(&ty).is_pure_callable() {
                    self.convergence_class(&ty)
                } else {
                    ty
                }
            }
            DispatchDemand::Whole => ty,
            DispatchDemand::TupleFields(fields) => self.convergence_collapse_tuple_fields(
                ty,
                fields,
                returned_fields(returned),
                path,
                collapse_concrete_ignored,
            ),
            DispatchDemand::ListShape(elem_demand) => self.convergence_collapse_list_shape(
                ty,
                elem_demand,
                returned_element(returned),
                path,
                collapse_concrete_ignored,
            ),
        }
    }

    /// The `returned` axis's own answer at one position, or `None` when the
    /// dispatch axis is the only one that has anything to say here.
    ///
    /// `Whole` on this axis means "the activation's published return IS this
    /// value", and the key keeps its ADDRESSED CONVERGENCE CLASS: list families
    /// normalise to `list(elem)` with the element kept at every depth and
    /// capped at `ADDRESS_COLLAPSE_DEPTH`, and closure brands still erase to
    /// their addressed surface -- the same bounded collapse fz-kdt.183 gives a
    /// demanded list, one axis over. It is deliberately NOT `Whole`'s verbatim
    /// keep, which has no collapse at all and no fz-y6w termination argument
    /// (fz-kdt.200). The cap is a LIST-family cap:
    /// [`Types::convergence_class_at`] checks it only in its
    /// `is_pure_list_family` branch, so a tuple, map or resource nest at a
    /// returned position recurses on the type that arrives with no depth bound
    /// of its own.
    ///
    /// Where the two axes descend into DIFFERENT kinds at one position -- a
    /// union of a tuple and a list, one axis reading each -- the class keeps
    /// both, which is the same bounded answer and never the verbatim type.
    fn convergence_collapse_returned(
        &mut self,
        ty: Ty,
        demand: &DispatchDemand,
        returned: &DispatchDemand,
        path: &[AddrStep],
    ) -> Option<Ty> {
        match (demand, returned) {
            (_, DispatchDemand::Ignore) => None,
            (_, DispatchDemand::Whole)
            | (DispatchDemand::TupleFields(_), DispatchDemand::ListShape(_))
            | (DispatchDemand::ListShape(_), DispatchDemand::TupleFields(_)) => {
                Some(self.convergence_class_at(&ty, path, true))
            }
            (DispatchDemand::Ignore, DispatchDemand::TupleFields(fields)) => {
                Some(self.convergence_collapse_tuple_fields(ty, &BTreeMap::new(), Some(fields), path, true))
            }
            (DispatchDemand::Ignore, DispatchDemand::ListShape(elem)) => {
                Some(self.convergence_collapse_list_shape(ty, &DispatchDemand::Ignore, Some(elem), path, true))
            }
            (DispatchDemand::TupleFields(_) | DispatchDemand::ListShape(_) | DispatchDemand::Whole, _) => None,
        }
    }

    fn convergence_collapse_tuple_fields(
        &mut self,
        ty: Ty,
        fields: &BTreeMap<u32, DispatchDemand>,
        returned_fields: Option<&BTreeMap<u32, DispatchDemand>>,
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
                    let returned = returned_fields
                        .and_then(|returned| returned.get(&(index as u32)))
                        .unwrap_or(&DispatchDemand::Ignore);
                    let mut child = path.to_vec();
                    if discriminate_tuple_alternatives {
                        child.push(AddrStep::Variant(alternative));
                    }
                    child.push(AddrStep::Field(index as u16));
                    *elem = self.convergence_collapse_ty(*elem, demand, returned, &child, collapse_concrete_ignored);
                }
            }
        }
        self.intern(d)
    }

    fn convergence_collapse_list_shape(
        &mut self,
        ty: Ty,
        elem_demand: &DispatchDemand,
        returned_elem: Option<&DispatchDemand>,
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
            // Demand reached this list's SHAPE, so the element is meaning, not
            // freight -- at every depth, because nothing here can say how far
            // down the forwarding chain that reads it looks (fz-kdt.183). An
            // element the demand names further (`ListShape(Whole)`, a tuple
            // field) is still collapsed by that demand; an element it stops at
            // is KEPT.
            let returned_elem = returned_elem.unwrap_or(&DispatchDemand::Ignore);
            let elem =
                if matches!(elem_demand, DispatchDemand::Ignore) && matches!(returned_elem, DispatchDemand::Ignore) {
                    self.convergence_class_at(&elem, &child, true)
                } else {
                    self.convergence_collapse_ty(elem, elem_demand, returned_elem, &child, collapse_concrete_ignored)
                };
            return self.list(elem);
        }
        for conj in &mut d.lists {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                if let Some(elem) = sig.elem {
                    sig.elem = Some(self.convergence_collapse_ty(
                        elem,
                        elem_demand,
                        returned_elem.unwrap_or(&DispatchDemand::Ignore),
                        &child,
                        collapse_concrete_ignored,
                    ));
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
            self.convergence_class_at(ty, path, false)
        } else {
            self.convergence_class(ty)
        }
    }

    pub fn union(&mut self, a: Ty, b: Ty) -> Ty {
        if a == b {
            return self.unchanged(a);
        }
        if a == self.core.none {
            return b;
        }
        if b == self.core.none {
            return a;
        }
        let key = if a <= b {
            BinaryTypeOperation::Union(a, b)
        } else {
            BinaryTypeOperation::Union(b, a)
        };
        self.binary_type_operation(key, |types| {
            let d = {
                let cx = types.ctx();
                cx.descr(&a).union(cx, cx.descr(&b))
            };
            types.intern(d)
        })
    }

    pub fn intersect(&mut self, a: Ty, b: Ty) -> Ty {
        if a == b {
            return a;
        }
        if a == self.core.none || b == self.core.none {
            return self.core.none;
        }
        self.binary_type_operation(BinaryTypeOperation::Intersect(a, b), |types| {
            if types.is_subtype(&a, &b) {
                return a;
            }
            if types.is_subtype(&b, &a) {
                return b;
            }
            let left = types.descr(&a).clone();
            let right = types.descr(&b).clone();
            let d = intersect_descr(types, &left, &right);
            types.intern(d)
        })
    }

    pub fn difference(&mut self, a: Ty, b: Ty) -> Ty {
        if a == b {
            return self.none();
        }
        if a == self.core.none {
            return self.core.none;
        }
        if b == self.core.none {
            return a;
        }
        self.binary_type_operation(BinaryTypeOperation::Difference(a, b), |types| {
            let d = types.descr(&a).diff(types.descr(&b));
            types.intern(d)
        })
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
        *a == self.core.none
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
        let key = Self::symmetric_key(ComparisonKey::ValueDisjoint, *a, *b);
        self.cached_comparison(key, |types| {
            let cx = types.ctx();
            types.descr(a).value_disjoint(cx, types.descr(b))
        })
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

    pub fn opaque_singleton(&self, a: &Ty) -> Option<String> {
        self.descr(a).as_opaque_singleton().map(String::from)
    }

    pub fn builtin_opaque_singleton(&self, a: &Ty) -> Option<BuiltinOpaque> {
        self.descr(a).as_builtin_opaque_singleton()
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

    /// Struct schemas named by these retained type surfaces.
    ///
    /// Struct record tags use `ModuleId` as their sole semantic identity, so
    /// this walk stays typed and local to the supplied types. It never renders
    /// a `Ty`, consults source reference graphs, or inventories World modules.
    pub(crate) fn struct_modules(&self, roots: impl IntoIterator<Item = Ty>) -> BTreeSet<super::identity::ModuleId> {
        let mut modules = BTreeSet::new();
        let mut seen = HashSet::new();
        for root in roots {
            self.collect_struct_modules(root, &mut seen, &mut modules);
        }
        modules
    }

    fn collect_struct_modules(
        &self,
        ty: Ty,
        seen: &mut HashSet<Ty>,
        modules: &mut BTreeSet<super::identity::ModuleId>,
    ) {
        if !seen.insert(ty) {
            return;
        }
        let descr = self.descr(&ty);
        for conj in &descr.tuples {
            for sig in conj.pos.iter().chain(&conj.neg) {
                for elem in &sig.elems {
                    self.collect_struct_modules(*elem, seen, modules);
                }
            }
        }
        for conj in &descr.lists {
            for sig in conj.pos.iter().chain(&conj.neg) {
                if let Some(elem) = sig.elem {
                    self.collect_struct_modules(elem, seen, modules);
                }
            }
        }
        for conj in &descr.resources {
            for sig in conj.pos.iter().chain(&conj.neg) {
                self.collect_struct_modules(sig.payload, seen, modules);
            }
        }
        for conj in &descr.funcs {
            for sig in conj.pos.iter().chain(&conj.neg) {
                for arg in &sig.args {
                    self.collect_struct_modules(*arg, seen, modules);
                }
                self.collect_struct_modules(sig.ret, seen, modules);
                if let Some(lit) = &sig.lit {
                    for capture in &lit.captures {
                        self.collect_struct_modules(*capture, seen, modules);
                    }
                }
            }
        }
        for conj in &descr.maps {
            for sig in conj.pos.iter().chain(&conj.neg) {
                if let MapTag::Struct(tag) = &sig.tag {
                    modules.insert(tag.module);
                }
                for field in sig.fields.values() {
                    self.collect_struct_modules(*field, seen, modules);
                }
            }
        }
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
                let OpaqueTag::Named(tag) = tag else {
                    return None;
                };
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
        let widen_non_structs = runtime_type_predicate_widens_non_structs(descr);
        let (plain_maps, tagged_structs) = runtime_type_predicate_map_tags(descr);
        let named_structs = runtime_type_predicate_named_structs(descr, tagged_structs);
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
            ints: if widen_non_structs || descr.basic.contains_all(BasicBits::INT) {
                FiniteSet::any()
            } else {
                FiniteSet::none()
            },
            floats: if widen_non_structs || descr.basic.contains_all(BasicBits::FLOAT) {
                FiniteSet::any()
            } else {
                FiniteSet::none()
            },
            atoms: if widen_non_structs {
                FiniteSet::any()
            } else {
                descr.atoms.clone()
            },
            lists: if widen_non_structs {
                ListShapes::any()
            } else {
                self.runtime_type_predicate_lists(descr)
            },
            tuples: if widen_non_structs {
                TupleShapes::any()
            } else {
                self.runtime_type_predicate_tuples(descr)
            },
            named_structs: named_structs.clone(),
            allow_other_structs: named_structs.cofinite,
            maps: widen_non_structs || plain_maps,
            binaries: widen_non_structs || descr.basic.contains_all(BasicBits::BINARY),
            callables: if widen_non_structs {
                CallableShapes::any()
            } else {
                self.runtime_type_predicate_callables(descr)
            },
            resources: widen_non_structs || !descr.resources.is_empty(),
        }
    }

    /// The list axis a runtime test can put to a value.
    ///
    /// One head question per list CLAUSE that admits a cons cell, because a
    /// clause is the unit the lattice keeps correlated -- the same reason
    /// [`Self::runtime_type_predicate_tuples`] keeps one shape per clause.
    ///
    /// A clause is head-projectable when it is the axis TOP, which admits every
    /// head, or when it is exactly one positive signature with nothing
    /// subtracted and that signature names an element type. Several positive
    /// signatures are an INTERSECTION of list types and negations are a
    /// DIFFERENCE; neither is one element type, and inventing one would claim
    /// a precision the emitted test could not honour. Those
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
            if clause.is_top() {
                // The axis top is written as the clause with no factors
                // (`types::axis`), so this clause is `[any]` and its head
                // question is the one every value passes.
                heads.push(RuntimeTypePredicate::any());
                continue;
            }
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
                return TupleShapes::arity_only(tuple_root_arities(descr));
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
    /// An interned callable clause pins exactly one literal. Equal-target
    /// literals merge at the type boundary; different targets make the clause
    /// empty and the boundary drops it. `callable_identity_literal` refuses
    /// clauses that name no literal, subtract one, or name an anonymous
    /// literal.
    fn runtime_type_predicate_callables(&self, descr: &Descr) -> CallableShapes {
        let mut shapes = Vec::with_capacity(descr.funcs.len());
        for clause in &descr.funcs {
            let Some(lit) = callable_identity_literal(clause) else {
                return CallableShapes::any();
            };
            shapes.push(CallableShape {
                target: ClosureTarget::from(
                    lit.fn_id
                        .expect("callable_identity_literal accepted an anonymous literal"),
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
        let mut seen = HashSet::new();
        has_vars_ty(self.ctx(), *a, &mut seen)
    }

    /// Every free type-var id reachable from `a`, structural children
    /// included. The identity of the vars, not merely their presence: two
    /// types that mention DIFFERENT vars describe different families however
    /// their denotations compare.
    pub fn free_var_ids(&self, a: &Ty) -> BTreeSet<TypeVarId> {
        let mut ids = BTreeSet::new();
        let mut seen = HashSet::new();
        collect_free_vars(self.ctx(), *a, &mut seen, &mut ids);
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
        let descr = runtime_envelope(
            self,
            ty,
            RuntimeEnvelopePolarity::Positive,
            RuntimeEnvelopePurpose::Projection,
        );
        self.intern(descr)
    }

    /// The static surface from which a runtime test and its projections are
    /// built.
    ///
    /// A plain map keeps recursively enveloped fields because pattern planning
    /// projects and binds those fields statically, even though the emitted
    /// `RuntimeTypePredicate::maps` question itself observes only map kind. A
    /// named struct instead keeps its schema tag and clears positive fields:
    /// its runtime question observes schema identity, while its field/storage
    /// views come from the settled schema and lowered struct operation.
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
        let descr = runtime_envelope(
            self,
            ty,
            RuntimeEnvelopePolarity::Positive,
            RuntimeEnvelopePurpose::Predicate,
        );
        self.intern(descr)
    }

    pub fn instantiate(&mut self, a: &Ty, sigma: &Sigma<Ty>) -> Ty {
        if sigma.is_empty() || !self.has_vars(a) {
            return self.unchanged(*a);
        }
        let d = instantiate(self, *a, sigma);
        self.intern(d)
    }

    /// UNIFY `pattern` against `witness`: the two describe the SAME thing, so
    /// every aligned position binds and no polarity applies. This is template
    /// instantiation (a callable clause specialized by a concrete surface), not
    /// constraint solving -- see [`Types::collect_constraint_subst`] for that.
    pub fn collect_instantiation_subst(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) {
        collect_subst_into(self, *pattern, *witness, BindingSide::Unify, BindingSide::Unify, sigma);
    }

    /// SOLVE the constraint `witness ⊆ σ(pattern)`, collecting the bindings on
    /// ONE side of it. `side` is the direction of the constraint at the root
    /// (`Lower` for a parameter matched against an argument); `target` selects
    /// which positions record -- `Lower` for the join a variable must contain,
    /// `Upper` for the meet it may not exceed. The direction reverses under an
    /// arrow's PARAMETERS, so a variable reached through an odd number of
    /// parameter descents is an upper bound and one reached through an even
    /// number is a lower bound (fz-kdt.184).
    pub(crate) fn collect_constraint_subst(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        side: BindingSide,
        target: BindingSide,
        sigma: &mut Sigma<Ty>,
    ) {
        collect_subst_into(self, *pattern, *witness, side, target, sigma);
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
    /// Share the function interner's typed origin before a literal can name it.
    /// The ID denotes equality in this World; its origin supplies semantic order.
    pub(crate) fn define_callable_origin(&mut self, target: ClosureTarget, origin: Arc<super::identity::FunctionRef>) {
        let origin = Arc::clone(&origin.denotation);
        let target = target.into();
        if let Some(existing) = self.callable_origins.get(&target) {
            assert_eq!(existing, &origin, "callable origins are immutable once registered");
        } else {
            self.callable_origins.insert(target, origin);
        }
    }

    pub(crate) fn callable_source_origin(
        &self,
        function: super::identity::FunctionId,
    ) -> Arc<fz_runtime::function_denotation::FunctionDenotation> {
        Arc::clone(
            self.callable_origins
                .get(&crate::fz_ir::FnId(function.as_u32()))
                .expect("registered source function"),
        )
    }

    #[cfg(test)]
    pub(crate) fn define_test_callable(&mut self, target: ClosureTarget, name: &str, arity: usize) {
        self.define_callable_origin(
            target,
            Arc::new(super::identity::FunctionRef {
                module: super::identity::ModuleId::GLOBAL,
                denotation: Arc::new(super::identity::FunctionDenotation {
                    origin: super::identity::FunctionOrigin::Named {
                        module: None,
                        name: name.to_string(),
                    },
                    arity,
                }),
            }),
        );
    }

    /// Every callable literal whose owner never registered an origin.
    /// Empty in production — the gate that says so is
    /// `canon_test`'s `every_closure_literal_has_a_registered_origin`.
    #[cfg(test)]
    pub(crate) fn unregistered_callables(&self) -> BTreeSet<u32> {
        self.interner
            .arena
            .iter()
            .flat_map(|d| d.funcs.iter())
            .flat_map(|c| c.pos.iter().chain(c.neg.iter()))
            .filter_map(|sig| sig.lit.as_ref())
            .filter_map(|lit| lit.fn_id)
            .filter(|fn_id| !self.callable_origins.contains_key(fn_id))
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
            ..Descr::unbranded()
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
            ..Descr::unbranded()
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

    /// The callable-surface variables owned by one literal before any caller
    /// observes it. This is planner evidence, not part of the literal's value
    /// denotation; semantic rows carry the returned coordinate record when a
    /// literal needs a surface.
    pub(crate) fn callable_literal_signature(&self, a: &Ty) -> Option<ActivationSignature> {
        let sig = self.descr(a).pure_arrow()?;
        sig.lit.as_ref()?;
        Some(ActivationSignature {
            inputs: sig.args.clone().into_boxed_slice(),
            result: sig.ret,
        })
    }

    /// Read an arrow coordinate record without treating it as a callable
    /// value. Contracts use this to attach their matched callback surface to
    /// an activation input rather than intersecting it into a closure `Ty`.
    pub(crate) fn callable_signature(&self, a: &Ty) -> Option<ActivationSignature> {
        let sig = self.descr(a).pure_arrow()?;
        Some(ActivationSignature {
            inputs: sig.args.clone().into_boxed_slice(),
            result: sig.ret,
        })
    }

    pub fn callable_clauses(&mut self, a: &Ty) -> Option<Vec<CallableClause<Ty>>> {
        callable_clauses(self.ctx(), self.descr(a))
    }

    pub fn callable_value_clauses(&mut self, a: &Ty) -> Option<Vec<CallableClause<Ty>>> {
        // Call observations are carried beside the value by `ActivationInput`.
        // This compatibility accessor therefore has no literal-specialization
        // arm: every named closure has precisely the callable clauses its
        // denotation owns.
        self.callable_clauses(a)
    }

    pub fn erase_closure_identity(&mut self, a: &Ty) -> Ty {
        let d = erase_closure_identity(self, *a);
        self.intern(d)
    }

    /// Key erasure keeps a joined family of one closure target intact: a
    /// runtime-selected capture layout still needs its construction word to
    /// discriminate the member. A one-literal forwarding input instead drops
    /// its target/surface identity and keeps only its capture denotation.
    fn erase_transported_closure_identity_for_key(&mut self, a: &Ty) -> Ty {
        let d = erase_transported_closure_identity_for_key(self, *a);
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
        format::display(self.ctx(), *a)
    }

    pub fn display_for_diag(&self, a: &Ty) -> String {
        format::display_for_diag(self.ctx(), *a)
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

    fn builtin_opaque(&mut self, builtin: BuiltinOpaque) -> Self::Ty {
        Types::builtin_opaque(self, builtin)
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

    fn is_value_disjoint(&self, a: &Self::Ty, b: &Self::Ty) -> bool {
        Types::is_value_disjoint(self, a, b)
    }

    fn key_var_count(&self, key: &[Self::Ty]) -> usize {
        Types::key_var_count(self, key)
    }

    fn key_subsumes_with(&self, query: &Self::Ty, key: &Self::Ty, sigma: &mut Sigma<Self::Ty>) -> bool {
        Types::key_subsumes_with(self, query, key, sigma)
    }

    fn opaque_singleton(&self, a: &Self::Ty) -> Option<String> {
        Types::opaque_singleton(self, a)
    }

    fn builtin_opaque_singleton(&self, a: &Self::Ty) -> Option<BuiltinOpaque> {
        Types::builtin_opaque_singleton(self, a)
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
        && d.brands.is_any()
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

/// The `returned` axis's per-field demand where it descends into a tuple, and
/// nothing where it does not (fz-kdt.199).
fn returned_fields(returned: &DispatchDemand) -> Option<&BTreeMap<u32, DispatchDemand>> {
    match returned {
        DispatchDemand::TupleFields(fields) => Some(fields),
        _ => None,
    }
}

/// The `returned` axis's element demand where it descends into a list, and
/// nothing where it does not (fz-kdt.199).
fn returned_element(returned: &DispatchDemand) -> Option<&DispatchDemand> {
    match returned {
        DispatchDemand::ListShape(elem) => Some(elem),
        _ => None,
    }
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

fn runtime_type_predicate_widens_non_structs(descr: &Descr) -> bool {
    descr.opaques.cofinite
        || descr
            .opaques
            .values
            .iter()
            .any(|tag| matches!(tag, OpaqueTag::Builtin(_) | OpaqueTag::Named(_)))
        || descr.vars.cofinite
        || !descr.vars.values.is_empty()
}

fn runtime_type_predicate_map_tags(descr: &Descr) -> (bool, FiniteSet<ModuleName>) {
    let mut plain = false;
    let mut structs = FiniteSet::none();
    for clause in &descr.maps {
        let positive = clause.pos.first().map(|sig| &sig.tag);
        if clause.pos.iter().skip(1).any(|sig| Some(&sig.tag) != positive) {
            continue;
        }
        let (mut clause_plain, mut clause_structs) = match positive {
            None => (true, FiniteSet::any()),
            Some(MapTag::Plain) => (true, FiniteSet::none()),
            Some(MapTag::Struct(tag)) => (false, FiniteSet::lit(tag.name.clone())),
        };
        for negative in &clause.neg {
            // The runtime observes a record's family, not its fields. A shaped
            // subtraction removes only part of that family, so rejecting the
            // whole tag would under-admit. Runtime envelopes clear observable
            // positive shapes first; their exact family negatives arrive here
            // fieldless and can be subtracted.
            if !negative.fields.is_empty() {
                continue;
            }
            match &negative.tag {
                MapTag::Plain => clause_plain = false,
                MapTag::Struct(tag) => clause_structs = runtime_type_predicate_remove(&clause_structs, &tag.name),
            }
        }
        plain |= clause_plain;
        structs = structs.union(&clause_structs);
    }
    (plain, structs)
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
            } else if negative_swallows_the_fragment(clause, sig) {
                allowed = runtime_type_predicate_remove(&allowed, &ListShape::NonEmpty);
            }
        }
        out = out.union(&allowed);
    }
    out
}

/// Whether a negative takes the clause's WHOLE non-empty fragment away.
///
/// A negative over a smaller element removes only part of it:
/// `non_empty_list(int | :a) & not(non_empty_list(int))` still holds
/// `[1, :a]`. The list normal form leaves no negative that swallows the
/// fragment behind — a clause one swallowed is `[]` or nothing by the time it
/// is stored — so the case left is a clause the boundary left alone, where the
/// negative names the positive's own element.
fn negative_swallows_the_fragment(clause: &Conj<ListSig>, negative: &ListSig) -> bool {
    matches!(clause.pos.as_slice(), [positive] if positive.elem.is_some() && positive.elem == negative.elem)
}

fn tuple_root_arities(descr: &Descr) -> FiniteSet<usize> {
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

fn has_only_tuple_runtime_roots(descr: &Descr) -> bool {
    let (maps, named_structs) = runtime_type_predicate_map_tags(descr);
    !runtime_type_predicate_widens_non_structs(descr)
        && descr.basic.is_empty()
        && descr.atoms.is_none()
        && descr.opaques.is_none()
        && runtime_type_predicate_list_shapes(descr).is_none()
        && descr.resources.is_empty()
        && descr.funcs.is_empty()
        && !maps
        && named_structs.is_none()
}

/// Every callable a function axis admits, named the way the runtime tells them
/// apart: by the code each was minted from. `None` when the axis admits
/// callables this side cannot enumerate.
///
/// A clause that pins no closure literal admits any callable at all, and one
/// such clause makes the whole union unrestricted; so does a clause that
/// SUBTRACTS a literal, whose remainder is not enumerable from this side.
/// A canonical clause has exactly one literal: same-identity literals merged
/// at the type boundary, while distinct identities made the clause empty and
/// were dropped. If that invariant breaks, the exact reader below fails rather
/// than making a runtime predicate for a state the type interner forbids.
///
/// An ANONYMOUS literal (fz-kdt.127) names no code at all, so it is that same
/// unrestricted answer -- and this is the ONE place that decides it, for the
/// predicate projection and for the envelope alike. It never actually arrives.
/// An anonymous literal is minted in exactly one place,
/// [`Types::erase_transported_closure_identity_inputs`], which puts it in the
/// ACTIVATION KEY of a non-recursive body that consumes no callable identity,
/// and only in the slots the dispatch mask marks
/// `DispatchDemand::Ignore`; a runtime test is asked of a VALUE's type -- a
/// callsite's `CallTargetSummary::surface_inputs`, a lane's carrier -- never of
/// a key. THAT is what makes an erased forwarder key and the construction axis
/// compose: the keying rule holds the two apart, not any projection here. The
/// `debug_assert!` is the gate on the rule; the `?` behind it keeps the sound
/// unrestricted answer if the rule is ever broken.
fn callable_identity_targets(funcs: &[Conj<ArrowSig>]) -> Option<BTreeSet<FnId>> {
    let mut targets = BTreeSet::new();
    for clause in funcs {
        targets.insert(
            callable_identity_literal(clause)?
                .fn_id
                .expect("callable_identity_literal accepted an anonymous literal"),
        );
    }
    Some(targets)
}

/// The one runtime-observable literal of an interned callable clause.
///
/// An anonymous literal is valid only in a non-runtime activation key, so it
/// asks the caller to take the unrestricted predicate path. Several literals
/// mean the interner invariant was violated and must never be recovered into a
/// lossy runtime test.
fn callable_identity_literal(clause: &Conj<ArrowSig>) -> Option<&ClosureLit> {
    if !clause.neg.is_empty() {
        return None;
    }
    let mut literals = clause.pos.iter().filter_map(|sig| sig.lit.as_ref());
    let literal = literals.next()?;
    debug_assert!(
        literal.fn_id.is_some(),
        "an anonymous literal reached a runtime test: it can only have come from an \
         activation key, and a key is never what a test is asked of (fz-kdt.127)"
    );
    literal.fn_id?;
    assert!(
        literals.next().is_none(),
        "Types::intern retained a callable clause with several literal identities"
    );
    Some(literal)
}

fn runtime_type_predicate_named_structs(descr: &Descr, structs: FiniteSet<ModuleName>) -> FiniteSet<ModuleName> {
    let nominal = if descr.opaques.cofinite {
        FiniteSet::none()
    } else {
        FiniteSet::finite(descr.opaques.values.iter().filter_map(|tag| match tag {
            OpaqueTag::ProtocolTarget(module) => Some(module.clone()),
            OpaqueTag::Builtin(_) | OpaqueTag::Named(_) => None,
        }))
    };
    nominal.union(&structs)
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

/// Collect every type-var id `d` mentions, mirroring `has_vars`' recursion:
/// the same axes, the same structural children, including a closure literal's
/// captures.
fn collect_free_vars(cx: TyCtx<'_>, ty: Ty, seen: &mut HashSet<Ty>, ids: &mut BTreeSet<TypeVarId>) {
    if !seen.insert(ty) {
        return;
    }
    let d = cx.descr(&ty);
    ids.extend(d.vars.values.iter().copied());
    for c in &d.tuples {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            for t in &sig.elems {
                collect_free_vars(cx, *t, seen, ids);
            }
        }
    }
    for c in &d.lists {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            if let Some(t) = sig.elem {
                collect_free_vars(cx, t, seen, ids);
            }
        }
    }
    for c in &d.resources {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            collect_free_vars(cx, sig.payload, seen, ids);
        }
    }
    for c in &d.funcs {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            for t in &sig.args {
                collect_free_vars(cx, *t, seen, ids);
            }
            collect_free_vars(cx, sig.ret, seen, ids);
            if let Some(lit) = sig.lit.as_ref() {
                for t in &lit.captures {
                    collect_free_vars(cx, *t, seen, ids);
                }
            }
        }
    }
    for c in &d.maps {
        for sig in c.pos.iter().chain(c.neg.iter()) {
            for t in sig.fields.values() {
                collect_free_vars(cx, *t, seen, ids);
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
    let mut seen = HashSet::new();
    has_vars_descr(cx, d, &mut seen)
}

fn has_vars_ty(cx: TyCtx<'_>, ty: Ty, seen: &mut HashSet<Ty>) -> bool {
    seen.insert(ty) && has_vars_descr(cx, cx.descr(&ty), seen)
}

fn has_vars_descr(cx: TyCtx<'_>, d: &Descr, seen: &mut HashSet<Ty>) -> bool {
    if !d.vars.values.is_empty() {
        return true;
    }
    d.tuples.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| sig.elems.iter().any(|t| has_vars_ty(cx, *t, seen)))
    }) || d.lists.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| sig.elem.is_some_and(|t| has_vars_ty(cx, t, seen)))
    }) || d.resources.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| has_vars_ty(cx, sig.payload, seen))
    }) || d.funcs.iter().any(|c| {
        c.pos.iter().chain(c.neg.iter()).any(|sig| {
            sig.args.iter().any(|t| has_vars_ty(cx, *t, seen))
                || has_vars_ty(cx, sig.ret, seen)
                || sig
                    .lit
                    .as_ref()
                    .is_some_and(|lit| lit.captures.iter().any(|t| has_vars_ty(cx, *t, seen)))
        })
    }) || d.maps.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| sig.fields.values().any(|t| has_vars_ty(cx, *t, seen)))
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

/// The semantic evidence needed by a projection, or the observable surface
/// from which a runtime type predicate is built.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RuntimeEnvelopePurpose {
    /// Preserve callable typing and recursively projectable record fields.
    Projection,
    /// Observe callable construction and struct identity, erasing arrows and
    /// positive struct fields that a type predicate cannot inspect.
    Predicate,
}

fn runtime_envelope(
    types: &mut Types,
    ty: Ty,
    polarity: RuntimeEnvelopePolarity,
    purpose: RuntimeEnvelopePurpose,
) -> Descr {
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
    if purpose == RuntimeEnvelopePurpose::Predicate
        && polarity == RuntimeEnvelopePolarity::Positive
        && !descr.funcs.is_empty()
    {
        descr.funcs = callable_identity_clauses(types, &descr.funcs);
    }
    descr.tuples = descr
        .tuples
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, purpose, runtime_tuple_sig))
        .collect();
    descr.lists = descr
        .lists
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, purpose, runtime_list_sig))
        .collect();
    descr.resources = descr
        .resources
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, purpose, runtime_resource_sig))
        .collect();
    descr.maps = descr
        .maps
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, purpose, runtime_map_sig))
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
/// same interned one-literal clause it would have seen unenveloped. The
/// persistence boundary rejects the impossible several-literal intersection,
/// so this path never invents a coarse fallback or a capture layout.
fn callable_identity_clauses(types: &mut Types, funcs: &[Conj<ArrowSig>]) -> Vec<Conj<ArrowSig>> {
    if callable_identity_targets(funcs).is_none() {
        return Descr::fun_top().funcs;
    }
    let ret = types.any();
    let mut clauses = Vec::with_capacity(funcs.len());
    for clause in funcs {
        let mut pos = Vec::with_capacity(clause.pos.len());
        for lit in clause.pos.iter().filter_map(|sig| sig.lit.as_ref()) {
            let captures: Vec<Ty> = lit
                .captures
                .iter()
                .map(|capture| {
                    runtime_envelope_ty(
                        types,
                        *capture,
                        RuntimeEnvelopePolarity::Positive,
                        RuntimeEnvelopePurpose::Predicate,
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

fn runtime_envelope_ty(
    types: &mut Types,
    ty: Ty,
    polarity: RuntimeEnvelopePolarity,
    purpose: RuntimeEnvelopePurpose,
) -> Ty {
    let descr = runtime_envelope(types, ty, polarity, purpose);
    types.intern(descr)
}

fn runtime_structural_conj<T>(
    types: &mut Types,
    conj: Conj<T>,
    polarity: RuntimeEnvelopePolarity,
    purpose: RuntimeEnvelopePurpose,
    transform: fn(&mut Types, T, RuntimeEnvelopePolarity, RuntimeEnvelopePurpose) -> Option<T>,
) -> Option<Conj<T>> {
    let mut pos = Vec::with_capacity(conj.pos.len());
    for sig in conj.pos {
        pos.push(transform(types, sig, polarity, purpose)?);
    }
    let neg = conj
        .neg
        .into_iter()
        .filter_map(|sig| transform(types, sig, polarity.flipped(), purpose))
        .collect();
    Some(Conj { pos, neg })
}

fn runtime_tuple_sig(
    types: &mut Types,
    sig: TupleSig,
    polarity: RuntimeEnvelopePolarity,
    purpose: RuntimeEnvelopePurpose,
) -> Option<TupleSig> {
    let elems = sig
        .elems
        .into_iter()
        .map(|ty| runtime_envelope_ty(types, ty, polarity, purpose))
        .collect::<Vec<_>>();
    (!elems.iter().any(|ty| types.is_empty(ty))).then_some(TupleSig { elems })
}

fn runtime_list_sig(
    types: &mut Types,
    sig: ListSig,
    polarity: RuntimeEnvelopePolarity,
    purpose: RuntimeEnvelopePurpose,
) -> Option<ListSig> {
    let elem = sig.elem.map(|ty| runtime_envelope_ty(types, ty, polarity, purpose));
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
    purpose: RuntimeEnvelopePurpose,
) -> Option<ResourceSig> {
    let payload = runtime_envelope_ty(types, sig.payload, polarity, purpose);
    (!types.is_empty(&payload)).then_some(ResourceSig { payload })
}

fn runtime_map_sig(
    types: &mut Types,
    sig: sigs::MapSig,
    polarity: RuntimeEnvelopePolarity,
    purpose: RuntimeEnvelopePurpose,
) -> Option<sigs::MapSig> {
    match (purpose, &sig.tag, polarity) {
        // A struct question observes the schema tag; its field layout is owned
        // by the settled schema and lowered operation, not the question.
        (RuntimeEnvelopePurpose::Predicate, MapTag::Struct(_), RuntimeEnvelopePolarity::Positive) => {
            Some(sigs::MapSig {
                tag: sig.tag,
                fields: BTreeMap::new(),
            })
        }
        // A shaped struct negative cannot be tested exactly. Dropping it
        // widens in the safe direction; a fieldless negative names the whole
        // family.
        (RuntimeEnvelopePurpose::Predicate, MapTag::Struct(_), RuntimeEnvelopePolarity::Negative)
            if sig.fields.is_empty() =>
        {
            Some(sig)
        }
        (RuntimeEnvelopePurpose::Predicate, MapTag::Struct(_), RuntimeEnvelopePolarity::Negative) => None,
        // Semantic projection retains both record families' field evidence.
        // Plain maps also retain it in the runtime test surface.
        _ => {
            let fields = sig
                .fields
                .into_iter()
                .map(|(key, ty)| (key, runtime_envelope_ty(types, ty, polarity, purpose)))
                .collect::<BTreeMap<_, _>>();
            (!fields.values().any(|ty| types.is_empty(ty))).then_some(sigs::MapSig { tag: sig.tag, fields })
        }
    }
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
/// captured closure go too and same-typed literals still share one body. The
/// literal's argument/result fields are planner observations, so erasure also
/// replaces them with the literal-free callable form; direct activation rows
/// retain the observations needed to plan a call.
fn erase_closure_identity(t: &mut Types, a: Ty) -> Descr {
    let base = t.descr(&a).clone();
    let mut erased = map_recursive_inputs(t, base, erase_closure_identity);
    let any = t.any();
    for conj in &mut erased.funcs {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            let Some(lit) = sig.lit.take() else {
                continue;
            };
            sig.args = vec![any; sig.args.len()];
            sig.ret = any;
            if lit.captures.is_empty() {
                continue;
            }
            let captures: Vec<Ty> = lit
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

/// The activation-key form of closure erasure.  A joined value with several
/// capture layouts of the SAME closure target cannot be selected statically;
/// its literal target remains the runtime construction discriminator.  A
/// single arrival, on the other hand, transports only freight through a body
/// that does not inspect it, so its target and call surface must not fork that
/// body's key.
fn erase_transported_closure_identity_for_key(t: &mut Types, a: Ty) -> Descr {
    let base = t.descr(&a).clone();
    let mut erased = map_recursive_inputs(t, base, erase_transported_closure_identity_for_key);
    let literal_targets = erased
        .funcs
        .iter()
        .flat_map(|conj| conj.pos.iter().chain(conj.neg.iter()))
        .filter_map(|sig| sig.lit.as_ref().and_then(|lit| lit.fn_id))
        .collect::<BTreeSet<_>>();
    let literal_count = erased
        .funcs
        .iter()
        .flat_map(|conj| conj.pos.iter().chain(conj.neg.iter()))
        .filter(|sig| sig.lit.as_ref().is_some_and(|lit| lit.fn_id.is_some()))
        .count();
    if literal_targets.len() == 1 && literal_count > 1 {
        return erased;
    }

    let any = t.any();
    for conj in &mut erased.funcs {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            let Some(lit) = sig.lit.take() else {
                continue;
            };
            sig.args = vec![any; sig.args.len()];
            sig.ret = any;
            let captures: Vec<Ty> = lit
                .captures
                .iter()
                .map(|capture| {
                    let capture = erase_transported_closure_identity_for_key(t, *capture);
                    t.intern(capture)
                })
                .collect();
            if !captures.is_empty() {
                sig.lit = Some(ClosureLit {
                    kind: lit.kind,
                    fn_id: None,
                    captures,
                });
            }
        }
    }
    erased
}

/// Returns an interned `Ty`: every result is canonically interned in `Types`,
/// so a widened type is never an un-interned `Descr` that a caller might compare
/// or store without canonicalization.
fn refine_widen_uncached(t: &mut Types, a: Ty, b: Ty) -> Ty {
    let lhs = t.descr(&a).clone();
    let rhs = t.descr(&b).clone();
    if let (Some(l), Some(r)) = (lhs.pure_tuple().cloned(), rhs.pure_tuple().cloned())
        && l.elems.len() == r.elems.len()
    {
        let elems: Vec<Ty> = l
            .elems
            .iter()
            .zip(r.elems.iter())
            .map(|(l, r)| t.refine_widen(l, r))
            .collect();
        return t.intern(Descr::tuple_of(elems));
    }
    let any = t.any();
    if let (Some(l), Some(r)) = (lhs.as_pure_list(any), rhs.as_pure_list(any)) {
        let elem = match (l.elem, r.elem) {
            (Some(l), Some(r)) => Some(t.refine_widen(&l, &r)),
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
    if let (Some(l), Some(r)) = (lhs.pure_resource(any), rhs.pure_resource(any)) {
        let payload = t.refine_widen(&l.payload, &r.payload);
        return t.resource(payload);
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
                    .map(|(lhs_capture, rhs_capture)| t.refine_widen(&lhs_capture, &rhs_capture))
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
            let ret = t.refine_widen(&l.ret, &r.ret);
            return t.intern(Descr {
                funcs: vec![Conj::pos_of(ArrowSig { args, ret, lit })],
                ..Descr::unbranded()
            });
        }
    }
    if let (Some(l), Some(r)) = (lhs.pure_record().cloned(), rhs.pure_record().cloned())
        && l.tag == r.tag
    {
        let mut fields = l.fields;
        for (key, rv) in &r.fields {
            if let Some(lv) = fields.get_mut(key) {
                *lv = t.refine_widen(lv, rv);
            } else {
                fields.insert(key.clone(), *rv);
            }
        }
        return t.intern(Descr::record(l.tag, fields));
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

/// Which side of a subtyping constraint the position being walked binds for.
///
/// Passing argument `W` where parameter pattern `P` is declared asserts
/// `W ⊆ σ(P)`. Every covariant slot preserves that direction; an arrow's
/// PARAMETERS reverse it, because `(w) -> r ⊆ (σp) -> σr` needs `σp ⊆ w`. So a
/// variable under an arrow parameter is bounded from ABOVE, and an upper bound
/// is not evidence about any value -- it never instantiates anything. `Unify`
/// is the third case: the two sides describe the same thing rather than
/// standing in a constraint, so every position binds and no flip applies
/// (fz-kdt.184).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum BindingSide {
    Unify,
    Lower,
    Upper,
}

impl BindingSide {
    pub(crate) fn flipped(self) -> Self {
        match self {
            Self::Unify => Self::Unify,
            Self::Lower => Self::Upper,
            Self::Upper => Self::Lower,
        }
    }
}

fn collect_subst_into(
    t: &mut Types,
    pattern: Ty,
    witness: Ty,
    side: BindingSide,
    target: BindingSide,
    sigma: &mut Sigma<Ty>,
) {
    let mut seen = HashSet::new();
    collect_subst_into_with(t, pattern, witness, side, target, sigma, &mut seen);
}

fn collect_subst_into_with(
    t: &mut Types,
    pattern: Ty,
    witness: Ty,
    side: BindingSide,
    target: BindingSide,
    sigma: &mut Sigma<Ty>,
    seen: &mut HashSet<(Ty, Ty, BindingSide, BindingSide)>,
) {
    if !seen.insert((pattern, witness, side, target)) {
        return;
    }
    let pat = t.descr(&pattern).clone();
    let wit = t.descr(&witness).clone();
    if let Some(ids) = pure_var_ids(&pat) {
        if side == target {
            for id in ids {
                sigma.entry(id).or_insert(witness);
            }
        }
        return;
    }
    if let (Some(ps), Some(ws)) = (pat.pure_tuple(), wit.pure_tuple())
        && ps.elems.len() == ws.elems.len()
    {
        for (p, w) in ps.elems.iter().zip(ws.elems.iter()) {
            collect_subst_into_with(t, *p, *w, side, target, sigma, seen);
        }
    }
    let any = t.any();
    if let (Some(ps), Some(ws)) = (pat.as_pure_list(any), wit.as_pure_list(any))
        && let (Some(p), Some(w)) = (ps.elem, ws.elem)
    {
        collect_subst_into_with(t, p, w, side, target, sigma, seen);
    }
    if let (Some(ps), Some(ws)) = (pat.pure_resource(any), wit.pure_resource(any)) {
        collect_subst_into_with(t, ps.payload, ws.payload, side, target, sigma, seen);
    }
    if let (Some(ps), Some(ws)) = (pat.pure_arrow(), wit.pure_arrow())
        && ps.args.len() == ws.args.len()
    {
        for (p, w) in ps.args.iter().zip(ws.args.iter()) {
            collect_subst_into_with(t, *p, *w, side.flipped(), target, sigma, seen);
        }
        collect_subst_into_with(t, ps.ret, ws.ret, side, target, sigma, seen);
    }
    if let (Some(ps), Some(ws)) = (pat.pure_record(), wit.pure_record())
        && ps.tag == ws.tag
    {
        for (key, p) in &ps.fields {
            if let Some(w) = ws.fields.get(key) {
                collect_subst_into_with(t, *p, *w, side, target, sigma, seen);
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
            sig.fields = sig
                .fields
                .iter()
                .map(|(key, value)| (key.clone(), f(t, *value)))
                .collect();
        }
    }
    d
}

fn mint_owned_resource_aliases_descr(cx: TyCtx<'_>, d: &Descr, candidates: &[(String, Descr)]) -> Descr {
    for (tag, inner) in candidates {
        if resource_payload_type(cx, d).is_some_and(|payload| payload.is_equiv(cx, inner)) {
            return Descr::opaque_of(tag.clone());
        }
    }
    d.clone()
}

#[cfg(test)]
mod types_test;
