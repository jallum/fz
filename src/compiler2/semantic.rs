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
    analysis: Option<ActivationAnalysis>,
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

    /// Install one round's return evidence. `None` is the ascent's bottom —
    /// no evidence adds nothing and never erases standing evidence. (The
    /// monotone join over `Some` evidence lands with the widening operator;
    /// until then `Some` over `Some` is last-write.)
    pub fn define_return(&mut self, _types: &mut Types, key: &ActivationKey, evidence: Option<Ty>) -> bool {
        let slot = self.slots.entry(key.clone()).or_insert_with(ActivationSlot::new);
        let Some(next) = evidence else {
            return false;
        };
        match &slot.return_ty {
            Some(current) => {
                let changed = current != &next;
                if changed {
                    slot.return_ty = Some(next);
                }
                changed
            }
            None => {
                slot.return_ty = Some(next);
                true
            }
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

    #[test]
    fn activation_return_replaces_stale_broad_result_with_current_precise_result() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let mut activations = ActivationMap::new();
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        let any = world.types_mut().any();
        let key = ActivationKey {
            root,
            function: world.root_function(root),
            input: vec![any, any],
        };
        let int = world.types_mut().int();

        assert!(activations.define_return(world.types_mut(), &key, Some(any)));
        assert!(
            activations.define_return(world.types_mut(), &key, Some(int)),
            "rerunning one activation with better evidence should replace the stale broad return"
        );
        assert_eq!(activations.get(&key).and_then(|slot| slot.return_ty()), Some(&int));
    }
}
