//! Compiler2's root-scoped semantic facts.
//!
//! This module stores activation-local summaries and closed-root frontiers that
//! the work graph owns: observed input shapes, reachable callsites, settled
//! return types, and the semantic closure each root has reached.

use std::collections::{HashMap, HashSet};
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
    pub input_types: Vec<Ty>,
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

pub struct ActivationInputMap<P> {
    slots: HashMap<ActivationKey, ActivationInputSlot<P>>,
    output_keys: HashMap<P, HashSet<ActivationKey>>,
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

#[derive(Debug, Clone)]
struct ActivationInputSlot<P> {
    contributors: HashMap<P, Vec<Ty>>,
    joined: Vec<Ty>,
}

#[derive(Debug, Default)]
pub struct ActivationInputReplace {
    pub output_keys: HashSet<ActivationKey>,
    pub changed_keys: HashSet<ActivationKey>,
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

impl<P> ActivationInputMap<P>
where
    P: Clone + Eq + Hash,
{
    pub fn new() -> Self {
        Self {
            slots: HashMap::new(),
            output_keys: HashMap::new(),
        }
    }

    pub fn get(&self, key: &ActivationKey) -> Option<&[Ty]> {
        self.slots.get(key).map(|slot| slot.joined.as_slice())
    }

    /// The concluding-completion arm: the publisher's contribution key set is
    /// replaced (dropping a key withdraws demand — final, and the only path
    /// by which a sole-publisher activation retracts), while entry values
    /// JOIN with the publisher's prior entry unless its ground shifted
    /// (`rebased`) — the only path by which contributed inputs may narrow.
    pub fn conclude(
        &mut self,
        types: &mut Types,
        publisher: P,
        next: HashMap<ActivationKey, Vec<Ty>>,
        rebased: bool,
    ) -> ActivationInputReplace {
        let next_output_keys = next.keys().cloned().collect::<HashSet<_>>();
        let previous_output_keys = if next_output_keys.is_empty() {
            self.output_keys.remove(&publisher).unwrap_or_default()
        } else {
            self.output_keys
                .insert(publisher.clone(), next_output_keys.clone())
                .unwrap_or_default()
        };
        let touched = previous_output_keys
            .iter()
            .cloned()
            .chain(next_output_keys.iter().cloned())
            .collect::<HashSet<_>>();
        let mut changed_keys = HashSet::new();

        for key in touched {
            let mut slot = self.slots.remove(&key).unwrap_or_else(ActivationInputSlot::new);
            let old_joined = (!slot.contributors.is_empty()).then(|| slot.joined.clone());

            match next.get(&key) {
                Some(inputs) => {
                    upsert_contribution(types, &mut slot, &publisher, inputs.clone(), !rebased);
                }
                None => {
                    slot.contributors.remove(&publisher);
                }
            }

            if slot.contributors.is_empty() {
                continue;
            }

            let joined = join_activation_inputs(types, slot.contributors.values());
            if old_joined.as_ref() != Some(&joined) {
                changed_keys.insert(key.clone());
            }
            slot.joined = joined;
            self.slots.insert(key, slot);
        }

        ActivationInputReplace {
            output_keys: next_output_keys,
            changed_keys,
        }
    }

    /// The waiting-completion arm: listed keys gain (or widen) this
    /// publisher's entry, unlisted keys it previously contributed stand
    /// untouched. A blocked publisher recants nothing.
    pub fn extend(
        &mut self,
        types: &mut Types,
        publisher: P,
        next: HashMap<ActivationKey, Vec<Ty>>,
    ) -> ActivationInputReplace {
        if next.is_empty() {
            return ActivationInputReplace::default();
        }
        let next_output_keys = next.keys().cloned().collect::<HashSet<_>>();
        self.output_keys
            .entry(publisher.clone())
            .or_default()
            .extend(next_output_keys.iter().cloned());
        let mut changed_keys = HashSet::new();

        for (key, inputs) in next {
            let mut slot = self.slots.remove(&key).unwrap_or_else(ActivationInputSlot::new);
            let old_joined = (!slot.contributors.is_empty()).then(|| slot.joined.clone());

            upsert_contribution(types, &mut slot, &publisher, inputs, true);

            let joined = join_activation_inputs(types, slot.contributors.values());
            if old_joined.as_ref() != Some(&joined) {
                changed_keys.insert(key.clone());
            }
            slot.joined = joined;
            self.slots.insert(key, slot);
        }

        ActivationInputReplace {
            output_keys: next_output_keys,
            changed_keys,
        }
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
        self.targets.first().map(|target| target.input_types.len()).unwrap_or(0)
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

impl<P> ActivationInputSlot<P> {
    fn new() -> Self {
        Self {
            contributors: HashMap::new(),
            joined: Vec::new(),
        }
    }
}

/// Install one publisher's contribution into a slot. `join` widens slot-wise
/// with the publisher's prior entry (the within-epoch ascent); without it the
/// entry replaces (the rebase path).
fn upsert_contribution<P: Clone + Eq + Hash>(
    types: &mut Types,
    slot: &mut ActivationInputSlot<P>,
    publisher: &P,
    inputs: Vec<Ty>,
    join: bool,
) {
    match slot.contributors.entry(publisher.clone()) {
        std::collections::hash_map::Entry::Vacant(entry) => {
            entry.insert(inputs);
        }
        std::collections::hash_map::Entry::Occupied(mut entry) => {
            if !join {
                entry.insert(inputs);
                return;
            }
            let current = entry.get_mut();
            assert_eq!(
                current.len(),
                inputs.len(),
                "one activation input fact cannot receive differing arities from one publisher",
            );
            for (current_input, next_input) in current.iter_mut().zip(inputs) {
                *current_input = if *current_input == next_input {
                    *current_input
                } else {
                    types.refine_widen(current_input, &next_input)
                };
            }
        }
    }
}

fn join_activation_inputs<'a>(types: &mut Types, contributors: impl Iterator<Item = &'a Vec<Ty>>) -> Vec<Ty> {
    let mut contributors = contributors;
    let Some(first) = contributors.next() else {
        return Vec::new();
    };
    let mut joined = first.clone();
    for inputs in contributors {
        assert_eq!(
            joined.len(),
            inputs.len(),
            "one activation cannot receive contributions with different arities",
        );
        for (joined_ty, input_ty) in joined.iter_mut().zip(inputs.iter().copied()) {
            *joined_ty = if *joined_ty == input_ty {
                *joined_ty
            } else {
                types.refine_widen(joined_ty, &input_ty)
            };
        }
    }
    joined
}

#[cfg(test)]
mod tests {
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
