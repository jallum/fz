//! Compiler2's root-scoped semantic facts.
//!
//! This module stores activation-local summaries and closed-root frontiers that
//! the work graph owns: observed input shapes, reachable callsites, settled
//! return types, and the semantic closure each root has reached.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::hash::Hash;

use super::body::{CallSiteId, ControlEntryId, ValueId};
use super::identity::{ActivationKey, ExecutableKey, FunctionId, RootId};
use super::types::{Ty, Types};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallSiteKey {
    pub activation: ActivationKey,
    pub callsite: CallSiteId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SelectedCallee {
    Function(FunctionId),
    ProviderBoundary(FunctionId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallTargetSummary {
    pub callee: SelectedCallee,
    /// The semantic call surface this callsite can send to the callee.
    ///
    /// This is not the same thing as the bounded recursive activation key.
    /// Materialization follows `activation`; diagnostics, fixture contracts,
    /// and semantic closure reasoning describe the externally visible surface.
    pub surface_inputs: Vec<Ty>,
    /// The exact bounded activation this target demanded, when the callee is
    /// compiler-owned. Provider boundaries do not name a compiler2 activation.
    pub activation: Option<ActivationKey>,
    /// `None` means the callee has produced no return evidence yet — an
    /// honest snapshot mid-ascent. Settledness guarantees resolution before
    /// consumers read; at the fixpoint a still-`None` return *is* the empty
    /// type (a callee that provably never returns), see `settled_return`.
    pub return_ty: Option<Ty>,
}

impl CallTargetSummary {
    /// The Kleene reading of a settled summary: evidence absent at the
    /// fixpoint means no value ever flows — the empty type. Only valid
    /// behind the settled gate (seal/materialization).
    pub fn settled_return(&self, types: &mut Types) -> Ty {
        self.return_ty.unwrap_or_else(|| types.none())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallSiteSummary {
    pub targets: Vec<CallTargetSummary>,
    pub return_ty: Option<Ty>,
}

impl CallSiteSummary {
    /// See [`CallTargetSummary::settled_return`].
    pub fn settled_return(&self, types: &mut Types) -> Ty {
        self.return_ty.unwrap_or_else(|| types.none())
    }
}

/// One exact callable surface observed semantically at a call boundary.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallableSurface {
    pub inputs: Vec<Ty>,
}

impl CallableSurface {
    pub fn new(inputs: Vec<Ty>) -> Self {
        Self { inputs }
    }

    pub(crate) fn alpha_normalize(&mut self, types: &mut Types) {
        self.inputs = self
            .inputs
            .iter()
            .copied()
            .map(|ty| types.alpha_normalize_vars(&ty))
            .collect();
    }
}

/// Runtime demand specific to callable values, kept separate from generic
/// whole-value demand so semantic flow derivation can publish one exact
/// callable-flow fact per local producer.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CallableDemand {
    pub resolved: BTreeSet<CallableSurface>,
    pub opaque: bool,
    pub escape: bool,
}

impl CallableDemand {
    pub fn resolved(inputs: Vec<Ty>) -> Self {
        let mut resolved = BTreeSet::new();
        resolved.insert(CallableSurface::new(inputs));
        Self {
            resolved,
            opaque: false,
            escape: false,
        }
    }

    pub fn opaque() -> Self {
        Self {
            resolved: BTreeSet::new(),
            opaque: true,
            escape: false,
        }
    }

    pub fn escaped() -> Self {
        Self {
            resolved: BTreeSet::new(),
            opaque: false,
            escape: true,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.resolved.is_empty() && !self.opaque && !self.escape
    }

    /// Whether the callable crosses a boundary that cannot carry a grounded
    /// call contract — it escapes first-class, or reaches an unknown callee.
    /// These are the cases a consumer must lower as a boxed first-class
    /// callable rather than a grounded direct surface.
    pub fn is_first_class(&self) -> bool {
        self.opaque || self.escape
    }

    pub fn join(&self, other: &Self) -> Self {
        let mut joined = self.clone();
        joined.join_assign(other);
        joined
    }

    pub fn join_assign(&mut self, other: &Self) {
        self.resolved.extend(other.resolved.iter().cloned());
        self.opaque |= other.opaque;
        self.escape |= other.escape;
    }

    pub(crate) fn alpha_normalize(&mut self, types: &mut Types) {
        let mut normalized = BTreeSet::new();
        for mut surface in self.resolved.clone() {
            surface.alpha_normalize(types);
            normalized.insert(surface);
        }
        self.resolved = normalized;
    }
}

/// AXIS 1 — how much of a value's *data representation* a consumer needs.
///
/// A pure join-semilattice: `Ignore` is bottom, `Whole` is the absorbing top,
/// and a same-arity `TupleFields` joins pointwise while a mismatched arity joins
/// up to `Whole`. Coarsening here is always correctness-safe — it only means
/// "materialize the whole box." Each field is a full [`RuntimeDemand`], so a
/// tuple of callables keeps each field's callable obligations.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum ShapeDemand {
    #[default]
    Ignore,
    Whole,
    TupleFields(Vec<RuntimeDemand>),
}

impl ShapeDemand {
    pub fn is_ignore(&self) -> bool {
        matches!(self, Self::Ignore)
    }

    fn normalized(self) -> Self {
        match self {
            Self::TupleFields(fields) => {
                let normalized = fields.into_iter().map(RuntimeDemand::normalized).collect::<Vec<_>>();
                if normalized.iter().all(RuntimeDemand::is_ignore) {
                    Self::Ignore
                } else {
                    Self::TupleFields(normalized)
                }
            }
            other => other,
        }
    }

    fn join(self, other: Self) -> Self {
        match (self.normalized(), other.normalized()) {
            (Self::Ignore, other) | (other, Self::Ignore) => other,
            (Self::Whole, _) | (_, Self::Whole) => Self::Whole,
            (Self::TupleFields(left), Self::TupleFields(right)) => {
                if left.len() != right.len() {
                    return Self::Whole;
                }
                Self::TupleFields(
                    left.into_iter()
                        .zip(right)
                        .map(|(left, right)| left.join(&right))
                        .collect(),
                )
                .normalized()
            }
        }
    }

    pub(crate) fn alpha_normalize(&mut self, types: &mut Types) {
        if let Self::TupleFields(fields) = self {
            for field in fields {
                field.alpha_normalize(types);
            }
        }
        *self = std::mem::take(self).normalized();
    }
}

/// The runtime demand on one semantic value: the **product** of an independent
/// data-shape axis and a callable-usage axis.
///
/// The two axes never share a representation, so coarsening the shape to `Whole`
/// cannot erase callable obligations, and accumulating callable obligations
/// cannot disturb the shape. This is what makes the join monotone — there is no
/// arm where one axis collapses the other, so callable surfaces, `opaque`, and
/// `escape` only ever grow. (Previously a `Value ⊔ Callable` join collapsed the
/// callable axis to a representation-agnostic top, which then had to be
/// non-monotonically *re-grounded* from the value's type at boundaries.)
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct RuntimeDemand {
    pub shape: ShapeDemand,
    pub callable: CallableDemand,
}

impl RuntimeDemand {
    /// The bottom demand: no data shape needed, never used as a callable.
    pub fn ignore() -> Self {
        Self::default()
    }

    /// The whole data representation, with no callable obligation. A callable
    /// value reaching a `whole` consumer escapes first-class — but that escape
    /// is recorded explicitly on the callable axis at the boundary (see
    /// `CallableDemand::escaped`), never inferred from `shape` being `Whole`.
    pub fn whole() -> Self {
        Self {
            shape: ShapeDemand::Whole,
            callable: CallableDemand::default(),
        }
    }

    pub fn tuple_fields(fields: Vec<RuntimeDemand>) -> Self {
        Self {
            shape: ShapeDemand::TupleFields(fields).normalized(),
            callable: CallableDemand::default(),
        }
    }

    pub fn callable(demand: CallableDemand) -> Self {
        Self {
            shape: ShapeDemand::Ignore,
            callable: demand,
        }
    }

    pub fn is_ignore(&self) -> bool {
        self.shape.is_ignore() && self.callable.is_empty()
    }

    /// Whether this demand carries a callable obligation — its callable axis is
    /// non-empty. The callable axis is populated only for values used as
    /// callables, so consumers that lower a callable lane branch on this and
    /// read `self.callable`, otherwise they read `self.shape`.
    pub fn is_callable(&self) -> bool {
        !self.callable.is_empty()
    }

    pub fn join(&self, other: &Self) -> Self {
        Self {
            shape: self.shape.clone().join(other.shape.clone()),
            callable: self.callable.join(&other.callable),
        }
    }

    pub fn join_assign(&mut self, other: &Self) {
        *self = self.join(other);
    }

    fn normalized(mut self) -> Self {
        self.shape = self.shape.normalized();
        self
    }

    pub(crate) fn alpha_normalize(&mut self, types: &mut Types) {
        self.shape.alpha_normalize(types);
        self.callable.alpha_normalize(types);
    }
}

/// Upstream callable-flow evidence for one local callable producer.
///
/// Transport may project these facts, but it must not rediscover them from
/// callable type or lowered callsites.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableFlowFact {
    pub function: FunctionId,
    pub captures: Box<[ValueId]>,
    pub direct_surfaces: BTreeSet<CallableSurface>,
    pub first_class_surfaces: BTreeSet<CallableSurface>,
    pub direct_edges: Vec<CallableFlowEdge>,
    pub first_class_edges: Vec<CallableFlowEdge>,
    pub opaque: bool,
    pub escape: bool,
    pub resolutions: Vec<ExecutableKey>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableFlowEdge {
    pub surface: CallableSurface,
    pub resolution: ExecutableKey,
}

impl CallableFlowFact {
    pub(crate) fn alpha_normalize(&mut self, types: &mut Types) {
        self.direct_surfaces = alpha_normalized_surfaces(types, &self.direct_surfaces);
        self.first_class_surfaces = alpha_normalized_surfaces(types, &self.first_class_surfaces);
        for edge in self.direct_edges.iter_mut().chain(self.first_class_edges.iter_mut()) {
            edge.surface.alpha_normalize(types);
            edge.resolution.activation.input = edge
                .resolution
                .activation
                .input
                .iter()
                .copied()
                .map(|ty| types.alpha_normalize_vars(&ty))
                .collect();
        }
        for resolution in &mut self.resolutions {
            resolution.activation.input = resolution
                .activation
                .input
                .iter()
                .copied()
                .map(|ty| types.alpha_normalize_vars(&ty))
                .collect();
        }
    }
}

fn alpha_normalized_surfaces(types: &mut Types, surfaces: &BTreeSet<CallableSurface>) -> BTreeSet<CallableSurface> {
    let mut normalized = BTreeSet::new();
    for mut surface in surfaces.clone() {
        surface.alpha_normalize(types);
        normalized.insert(surface);
    }
    normalized
}

/// The full runtime-demand projection for one analyzed executable.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ExecutableRuntimeDemand {
    pub return_demand: RuntimeDemand,
    pub input_demands: Vec<RuntimeDemand>,
    pub value_demands: HashMap<ValueId, RuntimeDemand>,
    pub entry_capture_demands: HashMap<ControlEntryId, Vec<RuntimeDemand>>,
    pub call_arg_demands: HashMap<CallSiteId, Vec<RuntimeDemand>>,
    pub callable_flows: HashMap<ValueId, CallableFlowFact>,
}

impl ExecutableRuntimeDemand {
    pub(crate) fn alpha_normalize(&mut self, types: &mut Types) {
        self.return_demand.alpha_normalize(types);
        for demand in &mut self.input_demands {
            demand.alpha_normalize(types);
        }
        for demand in self.value_demands.values_mut() {
            demand.alpha_normalize(types);
        }
        for demands in self.entry_capture_demands.values_mut() {
            for demand in demands {
                demand.alpha_normalize(types);
            }
        }
        for demands in self.call_arg_demands.values_mut() {
            for demand in demands {
                demand.alpha_normalize(types);
            }
        }
        for flow in self.callable_flows.values_mut() {
            flow.alpha_normalize(types);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActivationAnalysis {
    pub reachable_clauses: Vec<u32>,
    pub reachable_entries: Vec<ControlEntryId>,
    pub callsites: Vec<CallSiteId>,
    pub latent_executables: Vec<ExecutableKey>,
    pub value_types: HashMap<ValueId, Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticClosure {
    pub entry: ExecutableKey,
    pub activations: HashSet<ActivationKey>,
    pub executables: HashSet<ExecutableKey>,
    pub runtime_demands: HashMap<ExecutableKey, ExecutableRuntimeDemand>,
}

#[derive(Debug, Clone)]
pub struct ActivationSlot {
    return_ty: Option<Ty>,
    /// Strict ascents of the return evidence since the last rebase. Past
    /// `RETURN_WIDENING_BUDGET` the join widens; past twice that it tops out.
    ascents: u32,
    analysis: Option<ActivationAnalysis>,
}

/// The BUDGET of strict ascents one activation's return may take per epoch
/// (between rebases) before the join starts widening. This is deliberately a
/// total, not a consecutive-ascent delay: resetting on a quiet round would
/// let spurious wakes interleave with a genuinely divergent chain and starve
/// the widening forever — the per-epoch total makes termination a theorem.
/// Honest programs converge in a few rungs; only programs whose precise
/// ascent provably never lands pay the precision loss. The corpus sweep
/// (`compiler2_corpus_never_engages_return_widening_*`) pins the measured
/// maximum at ≤ 4 strict ascents across every fixture; the budget sits at
/// 2× that headroom.
pub const RETURN_WIDENING_BUDGET: u32 = 8;

/// The outcome of installing one round's return evidence.
#[derive(Debug, Clone, Copy)]
pub struct ReturnDefine {
    pub changed: bool,
    pub ascents: u32,
    pub widened: bool,
}

#[derive(Debug, Default)]
pub struct ActivationMap {
    slots: HashMap<ActivationKey, ActivationSlot>,
}

/// A value that composes by monotone join within a context. The contribution
/// store joins every publisher's entry for one key into a single aggregate;
/// `Ctx` carries whatever the join needs — the type store for input vectors,
/// nothing for runtime demand.
pub trait JoinContribution: Clone + PartialEq {
    type Ctx;
    /// The empty aggregate: the join of zero contributors (lattice bottom).
    fn bottom() -> Self;
    /// Monotone join: `self ⊔= other`.
    fn join_assign(&mut self, other: &Self, ctx: &mut Self::Ctx);
}

/// One key's per-publisher contributions and their joined aggregate.
#[derive(Debug, Clone)]
struct ContributionSlot<P, V> {
    contributors: HashMap<P, V>,
    joined: V,
}

/// A multi-publisher contribution store: each key's value is the join over
/// every publisher's contribution. `ActivationInputMap` and `ReturnDemandMap`
/// are its two instances, differing only in (key, value, join context).
///
/// The store does NOT own a per-publisher output-key index. The scheduler's
/// work graph already tracks every job's published facts under the identical
/// accumulate-on-extend / replace-on-conclude rule, so it is the single source
/// of truth for a publisher's frontier; `conclude` takes that frontier as
/// `previous_output_keys`.
pub struct ContributionMap<K, P, V> {
    slots: HashMap<K, ContributionSlot<P, V>>,
}

impl<K, P, V> Default for ContributionMap<K, P, V> {
    fn default() -> Self {
        Self { slots: HashMap::new() }
    }
}

/// A conclusion/extension's effect: the publisher's new output-key frontier and
/// the keys whose joined aggregate moved.
#[derive(Debug)]
pub struct ContributionReplace<K> {
    pub output_keys: HashSet<K>,
    pub changed_keys: HashSet<K>,
}

impl<K> Default for ContributionReplace<K> {
    fn default() -> Self {
        Self {
            output_keys: HashSet::new(),
            changed_keys: HashSet::new(),
        }
    }
}

/// The activation-input contribution store: per-publisher body input evidence,
/// joined pointwise by `refine_widen` over the shared type store.
pub type ActivationInputMap<P> = ContributionMap<ActivationKey, P, Vec<Ty>>;

/// The return-demand contribution store: per-caller `ReturnDemand(E)` evidence,
/// joined by the demand lattice's least upper bound.
pub type ReturnDemandMap<P> = ContributionMap<ExecutableKey, P, RuntimeDemand>;

/// One publisher's entry for a key in a conclusion's `next` map.
enum SlotEntry<V> {
    Upsert(V),
    Withdraw,
}

#[derive(Debug, Default)]
pub struct CallSiteMap {
    slots: HashMap<CallSiteKey, CallSiteSummary>,
}

#[derive(Debug, Clone)]
pub struct SemanticClosureSlot {
    closure: SemanticClosure,
}

#[derive(Debug, Default)]
pub struct SemanticClosureMap {
    slots: Vec<Option<SemanticClosureSlot>>,
}

impl ActivationMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&self, key: &ActivationKey) -> Option<&ActivationSlot> {
        self.slots.get(key)
    }

    /// Install one round's return evidence — the single join point of the
    /// fixpoint. `None` is the ascent's bottom: no evidence adds nothing and
    /// never erases standing evidence. `Some` evidence JOINS by union (which
    /// preserves closure identities; `refine_widen` does not and is not
    /// idempotent), so within an epoch the stored value only ascends —
    /// descent is unrepresentable. A `rebased` publisher REPLACES instead:
    /// the only narrowing path, taken when its ground shifted.
    ///
    /// The ladder must end: past `RETURN_WIDENING_BUDGET` strict ascents the
    /// join widens the growing spine (`convergence_class`); past twice the
    /// budget it tops out at `any`. Termination is then a theorem for every
    /// program, not a property of lucky inputs.
    pub fn define_return(
        &mut self,
        types: &mut Types,
        key: &ActivationKey,
        evidence: Option<Ty>,
        rebased: bool,
    ) -> ReturnDefine {
        let slot = self.slots.entry(key.clone()).or_insert_with(ActivationSlot::new);
        if rebased {
            let changed = slot.return_ty != evidence;
            slot.return_ty = evidence;
            slot.ascents = 0;
            return ReturnDefine {
                changed,
                ascents: 0,
                widened: false,
            };
        }
        let Some(next) = evidence else {
            return ReturnDefine {
                changed: false,
                ascents: slot.ascents,
                widened: false,
            };
        };
        let joined = match slot.return_ty {
            None => next,
            Some(current) if current == next => {
                return ReturnDefine {
                    changed: false,
                    ascents: slot.ascents,
                    widened: false,
                };
            }
            Some(current) => types.union(current, next),
        };
        if Some(joined) == slot.return_ty {
            return ReturnDefine {
                changed: false,
                ascents: slot.ascents,
                widened: false,
            };
        }
        slot.ascents += 1;
        let stored = if slot.ascents > 2 * RETURN_WIDENING_BUDGET {
            types.any()
        } else if slot.ascents > RETURN_WIDENING_BUDGET {
            types.convergence_class(&joined)
        } else {
            joined
        };
        // `widened` reports what actually happened to the stored value, not
        // that the budget threshold was crossed: past the threshold the
        // operator is often the identity (the spine already collapsed).
        let widened = stored != joined;
        let changed = Some(stored) != slot.return_ty;
        slot.return_ty = Some(stored);
        ReturnDefine {
            changed,
            ascents: slot.ascents,
            widened,
        }
    }

    pub fn define_analysis(&mut self, key: &ActivationKey, analysis: ActivationAnalysis) -> bool {
        let slot = self.slots.entry(key.clone()).or_insert_with(ActivationSlot::new);
        let changed = slot.analysis.as_ref() != Some(&analysis);
        if changed {
            slot.analysis = Some(analysis);
        }
        changed
    }
}

impl<K, P, V> ContributionMap<K, P, V>
where
    K: Clone + Eq + Hash,
    P: Clone + Eq + Hash,
    V: JoinContribution,
{
    pub fn new() -> Self {
        Self::default()
    }

    /// The joined aggregate for a key, or `None` before any publisher
    /// contributes. Read a bottom-defaulting value with
    /// `get(key).cloned().unwrap_or_else(V::bottom)`.
    pub fn get(&self, key: &K) -> Option<&V> {
        self.slots.get(key).map(|slot| &slot.joined)
    }

    /// The concluding-completion arm: the publisher's contribution key set is
    /// replaced — dropping a key withdraws that contribution, the only path by
    /// which a sole publisher retracts — while entry values JOIN with the
    /// publisher's prior entry unless its ground shifted (`rebased`), the only
    /// path by which contributed values may narrow. `previous_output_keys` is
    /// the publisher's prior frontier, owned by the work graph.
    pub fn conclude(
        &mut self,
        ctx: &mut V::Ctx,
        publisher: P,
        previous_output_keys: HashSet<K>,
        next: HashMap<K, V>,
        rebased: bool,
    ) -> ContributionReplace<K> {
        let next_output_keys = next.keys().cloned().collect::<HashSet<_>>();
        let touched = previous_output_keys
            .iter()
            .cloned()
            .chain(next_output_keys.iter().cloned())
            .collect::<HashSet<_>>();
        let mut changed_keys = HashSet::new();
        for key in touched {
            let entry = match next.get(&key) {
                Some(value) => SlotEntry::Upsert(value.clone()),
                None => SlotEntry::Withdraw,
            };
            if self.apply(ctx, &key, &publisher, entry, !rebased) {
                changed_keys.insert(key);
            }
        }
        ContributionReplace {
            output_keys: next_output_keys,
            changed_keys,
        }
    }

    /// The waiting-completion arm: listed keys gain (or widen) this publisher's
    /// entry; unlisted keys it previously contributed stand untouched. A blocked
    /// publisher recants nothing.
    pub fn extend(&mut self, ctx: &mut V::Ctx, publisher: P, next: HashMap<K, V>) -> ContributionReplace<K> {
        if next.is_empty() {
            return ContributionReplace::default();
        }
        let next_output_keys = next.keys().cloned().collect::<HashSet<_>>();
        let mut changed_keys = HashSet::new();
        for (key, value) in next {
            if self.apply(ctx, &key, &publisher, SlotEntry::Upsert(value), true) {
                changed_keys.insert(key);
            }
        }
        ContributionReplace {
            output_keys: next_output_keys,
            changed_keys,
        }
    }

    /// Apply one publisher's entry (or withdrawal) to one key and report whether
    /// the joined aggregate moved. An emptied slot is dropped, and its move to
    /// bottom is reported so a multi-publisher retraction is observed; a sole
    /// publisher's retraction is reported too, though the fact table neutralizes
    /// it through the vanished publisher set.
    fn apply(&mut self, ctx: &mut V::Ctx, key: &K, publisher: &P, entry: SlotEntry<V>, join: bool) -> bool {
        let mut slot = self.slots.remove(key).unwrap_or_else(|| ContributionSlot {
            contributors: HashMap::new(),
            joined: V::bottom(),
        });
        let old_joined = (!slot.contributors.is_empty()).then(|| slot.joined.clone());
        match entry {
            SlotEntry::Upsert(value) => {
                upsert_contribution(ctx, &mut slot.contributors, publisher, value, join);
            }
            SlotEntry::Withdraw => {
                slot.contributors.remove(publisher);
            }
        }
        let joined = join_contributions(ctx, slot.contributors.values());
        let moved = old_joined.as_ref() != Some(&joined);
        if !slot.contributors.is_empty() {
            slot.joined = joined;
            self.slots.insert(key.clone(), slot);
        }
        moved
    }
}

impl ActivationSlot {
    fn new() -> Self {
        Self {
            return_ty: None,
            ascents: 0,
            analysis: None,
        }
    }

    pub fn return_ty(&self) -> Option<&Ty> {
        self.return_ty.as_ref()
    }

    pub fn analysis(&self) -> Option<&ActivationAnalysis> {
        self.analysis.as_ref()
    }
}

impl CallSiteMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, key: CallSiteKey, summary: CallSiteSummary) -> bool {
        let changed = self.slots.get(&key) != Some(&summary);
        self.slots.insert(key, summary);
        changed
    }

    pub fn get(&self, key: &CallSiteKey) -> Option<&CallSiteSummary> {
        self.slots.get(key)
    }
}

impl CallSiteSummary {
    pub fn arity(&self) -> usize {
        self.targets
            .first()
            .map(|target| target.surface_inputs.len())
            .unwrap_or(0)
    }

    pub fn single_target(&self) -> Option<&CallTargetSummary> {
        (self.targets.len() == 1).then_some(&self.targets[0])
    }
}

impl SemanticClosureMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, root: RootId, closure: SemanticClosure) -> bool {
        self.ensure(root);
        let slot = &mut self.slots[root.as_u32() as usize];
        let changed = !matches!(slot, Some(existing) if existing.closure == closure);
        *slot = Some(SemanticClosureSlot { closure });
        changed
    }

    pub fn get(&self, root: RootId) -> Option<&SemanticClosure> {
        self.slots
            .get(root.as_u32() as usize)
            .and_then(|slot| slot.as_ref().map(|slot| &slot.closure))
    }
    fn ensure(&mut self, root: RootId) {
        let needed = root.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || None);
        }
    }
}

/// Install one publisher's contribution into a key's contributor table. `join`
/// widens the publisher's prior entry (the within-epoch ascent); without it the
/// entry replaces (the rebase path).
fn upsert_contribution<P, V>(ctx: &mut V::Ctx, contributors: &mut HashMap<P, V>, publisher: &P, value: V, join: bool)
where
    P: Clone + Eq + Hash,
    V: JoinContribution,
{
    match contributors.entry(publisher.clone()) {
        std::collections::hash_map::Entry::Vacant(entry) => {
            entry.insert(value);
        }
        std::collections::hash_map::Entry::Occupied(mut entry) => {
            if join {
                entry.get_mut().join_assign(&value, ctx);
            } else {
                entry.insert(value);
            }
        }
    }
}

/// Join every contributor into the key's aggregate. The join of zero
/// contributors is `V::bottom`.
fn join_contributions<'a, V>(ctx: &mut V::Ctx, contributors: impl Iterator<Item = &'a V>) -> V
where
    V: JoinContribution + 'a,
{
    let mut joined = V::bottom();
    for value in contributors {
        joined.join_assign(value, ctx);
    }
    joined
}

impl JoinContribution for Vec<Ty> {
    type Ctx = Types;

    fn bottom() -> Self {
        Vec::new()
    }

    /// Pointwise `refine_widen` over a shared arity. Bottom (the empty vector)
    /// seeds from the first contributor; thereafter every contributor carries
    /// the same arity.
    fn join_assign(&mut self, other: &Self, types: &mut Types) {
        if self.is_empty() {
            self.clone_from(other);
            return;
        }
        assert_eq!(
            self.len(),
            other.len(),
            "one activation cannot receive contributions with different arities",
        );
        for (current, next) in self.iter_mut().zip(other.iter()) {
            *current = if *current == *next {
                *current
            } else {
                types.refine_widen(current, next)
            };
        }
    }
}

impl JoinContribution for RuntimeDemand {
    type Ctx = ();

    fn bottom() -> Self {
        RuntimeDemand::ignore()
    }

    fn join_assign(&mut self, other: &Self, _ctx: &mut ()) {
        *self = RuntimeDemand::join(self, other);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashMap, HashSet};

    use super::*;
    use crate::compiler2::{ExecutableNeed, World};
    use crate::telemetry::ConfiguredTelemetry;

    fn test_key(world: &mut World<'_>) -> ActivationKey {
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        let any = world.types_mut().any();
        ActivationKey {
            root,
            function: world.root_function(root),
            input: vec![any, any],
        }
    }

    fn test_executable(world: &mut World<'_>, name: &str) -> ExecutableKey {
        let root = world.submit_root(None, name.to_string(), 0, ExecutableNeed::Value);
        ExecutableKey {
            activation: ActivationKey {
                root,
                function: world.root_function(root),
                input: Vec::new(),
            },
            need: ExecutableNeed::Value,
        }
    }

    fn resolved_surface(tys: &[Ty]) -> CallableDemand {
        CallableDemand::resolved(tys.to_vec())
    }

    #[test]
    fn runtime_demand_ignore_plus_resolved_callable_preserves_the_surface() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let int = world.types_mut().int();

        let joined = RuntimeDemand::ignore().join(&RuntimeDemand::callable(resolved_surface(&[int])));

        assert_eq!(
            joined,
            RuntimeDemand::callable(CallableDemand::resolved(vec![int])),
            "bottom must contribute nothing to callable demand",
        );
    }

    #[test]
    fn runtime_demand_resolved_callable_plus_escape_stays_callable_and_marks_first_class() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let int = world.types_mut().int();

        let joined =
            RuntimeDemand::callable(resolved_surface(&[int])).join(&RuntimeDemand::callable(CallableDemand::escaped()));

        assert_eq!(
            joined,
            RuntimeDemand::callable(CallableDemand {
                resolved: BTreeSet::from([CallableSurface::new(vec![int])]),
                opaque: false,
                escape: true,
            }),
            "escape is a first-class callable demand, not a reason to erase known surfaces",
        );
    }

    #[test]
    fn runtime_demand_tuple_fields_plus_whole_value_collapses_to_value() {
        let joined = RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(), RuntimeDemand::ignore()])
            .join(&RuntimeDemand::whole());

        assert_eq!(joined, RuntimeDemand::whole());
    }

    #[test]
    fn runtime_demand_callable_escape_preserves_known_resolved_surfaces() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let int = world.types_mut().int();
        let atom = world.types_mut().atom();

        let joined = RuntimeDemand::callable(resolved_surface(&[int])).join(&RuntimeDemand::callable(CallableDemand {
            resolved: BTreeSet::from([CallableSurface::new(vec![atom])]),
            opaque: false,
            escape: true,
        }));

        assert_eq!(
            joined,
            RuntimeDemand::callable(CallableDemand {
                resolved: BTreeSet::from([CallableSurface::new(vec![atom]), CallableSurface::new(vec![int]),]),
                opaque: false,
                escape: true,
            }),
            "whole-value callable demand must keep any exact surfaces we already proved",
        );
    }

    #[test]
    fn return_demand_map_joins_two_publishers_by_lub() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let mut demands = ReturnDemandMap::new();
        let executable = test_executable(&mut world, "joined");
        let int = world.types_mut().int();
        let shape_demand = RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(), RuntimeDemand::ignore()]);
        let callable_demand = RuntimeDemand::callable(resolved_surface(&[int]));

        let first = demands.conclude(
            &mut (),
            "caller_a",
            HashSet::new(),
            HashMap::from([(executable.clone(), shape_demand.clone())]),
            false,
        );
        assert!(
            first.changed_keys.contains(&executable),
            "first contribution moves the aggregate off bottom",
        );

        let second = demands.conclude(
            &mut (),
            "caller_b",
            HashSet::new(),
            HashMap::from([(executable.clone(), callable_demand.clone())]),
            false,
        );

        assert!(
            second.changed_keys.contains(&executable),
            "a second publisher's independent callable axis must move the joined demand",
        );
        assert_eq!(
            demands.get(&executable).cloned().unwrap_or_else(RuntimeDemand::ignore),
            shape_demand.join(&callable_demand),
            "ReturnDemand(E) is the lub over every caller contribution",
        );
    }

    #[test]
    fn return_demand_map_retracts_one_publisher_and_reports_only_real_aggregate_moves() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let mut demands = ReturnDemandMap::new();
        let executable = test_executable(&mut world, "retract");

        let caller_a = demands.conclude(
            &mut (),
            "caller_a",
            HashSet::new(),
            HashMap::from([(executable.clone(), RuntimeDemand::whole())]),
            false,
        );
        let caller_b = demands.conclude(
            &mut (),
            "caller_b",
            HashSet::new(),
            HashMap::from([(executable.clone(), RuntimeDemand::whole())]),
            false,
        );

        let redundant_retract = demands.conclude(&mut (), "caller_b", caller_b.output_keys, HashMap::new(), false);
        assert!(
            !redundant_retract.changed_keys.contains(&executable),
            "removing one of two equal top contributions leaves the aggregate unchanged",
        );
        assert_eq!(
            demands.get(&executable).cloned().unwrap_or_else(RuntimeDemand::ignore),
            RuntimeDemand::whole()
        );

        let final_retract = demands.conclude(&mut (), "caller_a", caller_a.output_keys, HashMap::new(), false);
        assert!(
            final_retract.changed_keys.contains(&executable),
            "removing the final publisher moves the aggregate to bottom",
        );
        assert_eq!(
            demands.get(&executable).cloned().unwrap_or_else(RuntimeDemand::ignore),
            RuntimeDemand::ignore(),
            "empty ReturnDemand join is bottom",
        );
    }

    #[test]
    fn return_demand_map_extend_never_lowers_a_standing_contribution() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let mut demands = ReturnDemandMap::new();
        let executable = test_executable(&mut world, "extend");

        demands.extend(
            &mut (),
            "blocked_caller",
            HashMap::from([(executable.clone(), RuntimeDemand::whole())]),
        );
        let lowered = demands.extend(
            &mut (),
            "blocked_caller",
            HashMap::from([(executable.clone(), RuntimeDemand::ignore())]),
        );

        assert!(
            !lowered.changed_keys.contains(&executable),
            "a waiting publisher extends by join and cannot recant an existing demand",
        );
        assert_eq!(
            demands.get(&executable).cloned().unwrap_or_else(RuntimeDemand::ignore),
            RuntimeDemand::whole()
        );
    }

    #[test]
    fn return_demand_map_missing_key_reads_as_bottom() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let demands = ReturnDemandMap::<&'static str>::new();
        let executable = test_executable(&mut world, "bottom");

        assert_eq!(
            demands.get(&executable).cloned().unwrap_or_else(RuntimeDemand::ignore),
            RuntimeDemand::ignore(),
            "ReturnDemand(E) starts at the lattice bottom before any caller contributes",
        );
    }

    #[test]
    fn activation_return_joins_within_an_epoch_and_narrows_only_on_rebase() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world);
        let any = world.types_mut().any();
        let int = world.types_mut().int();

        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(any), false)
                .changed
        );
        // Within an epoch evidence only ascends: int joins into any and
        // disappears — descent is unrepresentable without a ground shift.
        assert!(
            !activations
                .define_return(world.types_mut(), &key, Some(int), false)
                .changed
        );
        assert_eq!(activations.get(&key).and_then(|slot| slot.return_ty()), Some(&any));

        // The ground shifted (rebase): the fresh derivation replaces.
        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(int), true)
                .changed
        );
        assert_eq!(activations.get(&key).and_then(|slot| slot.return_ty()), Some(&int));
    }

    #[test]
    fn activation_return_bottom_is_the_join_identity() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world);
        let int = world.types_mut().int();

        // No evidence adds nothing — before and after real evidence lands.
        assert!(!activations.define_return(world.types_mut(), &key, None, false).changed);
        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(int), false)
                .changed
        );
        assert!(!activations.define_return(world.types_mut(), &key, None, false).changed);
        assert_eq!(activations.get(&key).and_then(|slot| slot.return_ty()), Some(&int));
    }

    #[test]
    fn activation_return_join_ascends_by_union_and_republication_is_quiet() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world);
        let int = world.types_mut().int();
        let atom = world.types_mut().atom();
        let both = world.types_mut().union(int, atom);

        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(int), false)
                .changed
        );
        // Equal republication is quiet — the load-bearing scheduler
        // invariant: changed=false wakes nobody.
        assert!(
            !activations
                .define_return(world.types_mut(), &key, Some(int), false)
                .changed
        );
        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(atom), false)
                .changed
        );
        assert_eq!(activations.get(&key).and_then(|slot| slot.return_ty()), Some(&both));
    }

    #[test]
    fn activation_return_join_preserves_closure_identity() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world);
        let int = world.types_mut().int();
        let target = world.reference_function(super::super::identity::ModuleId::GLOBAL, "f", 1);
        let closure = world.closure_ty(target, vec![int]);

        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(closure), false)
                .changed
        );
        assert!(
            activations
                .define_return(world.types_mut(), &key, Some(int), false)
                .changed
        );
        let joined = *activations
            .get(&key)
            .and_then(|slot| slot.return_ty())
            .expect("joined return");
        assert!(
            world.types_mut().callable_value_clauses(&joined).is_some(),
            "the union join must keep the closure identity resolvable",
        );
    }

    #[test]
    fn activation_return_widening_reports_only_real_coarsening() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world);

        // Atom-by-atom growth ascends strictly but never builds a list
        // spine, so past the budget `convergence_class` is the identity:
        // crossing the threshold coarsens nothing and must not be reported
        // as widening.
        for index in 0..(2 * RETURN_WIDENING_BUDGET) {
            let atom = world.types_mut().atom_lit(&format!("a{index}"));
            let outcome = activations.define_return(world.types_mut(), &key, Some(atom), false);
            assert!(outcome.changed, "each fresh atom is a strict ascent");
            assert!(
                !outcome.widened,
                "round {index}: nothing was coarsened, so nothing may report as widened",
            );
        }

        // The ascent past twice the budget tops out at `any` — a real
        // coarsening, reported exactly once; at the top further evidence
        // joins quietly.
        let atom = world.types_mut().atom_lit("top");
        let outcome = activations.define_return(world.types_mut(), &key, Some(atom), false);
        assert!(outcome.changed && outcome.widened, "topping out at any IS a coarsening");
        let atom = world.types_mut().atom_lit("after");
        let outcome = activations.define_return(world.types_mut(), &key, Some(atom), false);
        assert!(
            !outcome.changed && !outcome.widened,
            "evidence joins quietly at the top"
        );
    }

    #[test]
    fn activation_return_widens_past_the_delay_and_terminates() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let mut activations = ActivationMap::new();
        let key = test_key(&mut world);

        // The canonical divergent ascent: ever-deeper list nests.
        let mut ty = world.types_mut().int();
        let mut widened_at = None;
        for round in 0..(2 * RETURN_WIDENING_BUDGET + 8) {
            ty = world.types_mut().list(ty);
            let outcome = activations.define_return(world.types_mut(), &key, Some(ty), false);
            if outcome.widened && widened_at.is_none() {
                widened_at = Some(round);
            }
            if !outcome.changed {
                // The ladder ended: a strictly-deepening ascent reached a
                // fixed point through the widening operator.
                assert!(widened_at.is_some(), "termination must come from widening");
                return;
            }
        }
        panic!("the widening operator must terminate a strictly-deepening ascent");
    }
}
