//! Compiler2's root-scoped semantic facts.
//!
//! This module stores activation-local summaries and closed-root frontiers that
//! the work graph owns: observed input shapes, reachable callsites, settled
//! return types, and the semantic closure each root has reached.

use std::collections::{HashMap, HashSet};

use super::body::{CallSiteId, ValueId};
use super::drive::FactKey;
use super::identity::{ActivationKey, ExecutableKey, FunctionId, RootId};
use super::types::{Ty, Types};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallSiteKey {
    pub activation: ActivationKey,
    pub callsite: CallSiteId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SelectedCallee {
    Function(FunctionId),
    Named { name: String, arity: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallSiteSummary {
    pub callee: SelectedCallee,
    pub input_types: Vec<Ty>,
    pub return_ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActivationAnalysis {
    pub reachable_clauses: Vec<u32>,
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

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DependencySnapshot {
    revisions: HashMap<FactKey, u64>,
}

#[derive(Debug, Clone)]
pub struct ActivationSlot {
    return_ty: Option<Ty>,
    return_revision: u64,
    analysis: Option<ActivationAnalysis>,
    analysis_revision: u64,
}

#[derive(Debug, Default)]
pub struct ActivationMap {
    slots: HashMap<ActivationKey, ActivationSlot>,
}

#[derive(Debug, Default)]
pub struct CallSiteMap {
    slots: HashMap<CallSiteKey, Revisioned<CallSiteSummary>>,
}

#[derive(Debug, Clone)]
pub struct SemanticClosureSlot {
    closure: SemanticClosure,
    dependencies: DependencySnapshot,
    revision: u64,
}

#[derive(Debug, Default)]
pub struct SemanticClosureMap {
    slots: Vec<Option<SemanticClosureSlot>>,
}

#[derive(Debug, Clone)]
struct Revisioned<T> {
    value: T,
    revision: u64,
}

impl ActivationMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&self, key: &ActivationKey) -> Option<&ActivationSlot> {
        self.slots.get(key)
    }

    pub fn define_return(&mut self, types: &mut Types, key: &ActivationKey, return_ty: Ty) -> u64 {
        let slot = self.slots.entry(key.clone()).or_insert_with(ActivationSlot::new);
        match &slot.return_ty {
            Some(current) => {
                let next = if current == &return_ty {
                    *current
                } else {
                    types.refine_widen(current, &return_ty)
                };
                if &next != current {
                    slot.return_ty = Some(next);
                    slot.return_revision += 1;
                }
            }
            None => {
                slot.return_ty = Some(return_ty);
                slot.return_revision += 1;
            }
        }
        slot.return_revision
    }

    pub fn define_analysis(&mut self, key: &ActivationKey, analysis: ActivationAnalysis) -> u64 {
        let slot = self.slots.entry(key.clone()).or_insert_with(ActivationSlot::new);
        if slot.analysis.as_ref() != Some(&analysis) {
            slot.analysis = Some(analysis);
            slot.analysis_revision += 1;
        }
        slot.analysis_revision
    }
}

impl ActivationSlot {
    fn new() -> Self {
        Self {
            return_ty: None,
            return_revision: 0,
            analysis: None,
            analysis_revision: 0,
        }
    }

    pub fn return_revision(&self) -> u64 {
        self.return_revision
    }

    pub fn return_ty(&self) -> Option<&Ty> {
        self.return_ty.as_ref()
    }

    pub fn analysis(&self) -> Option<&ActivationAnalysis> {
        self.analysis.as_ref()
    }

    pub fn analysis_revision(&self) -> u64 {
        self.analysis_revision
    }
}

impl CallSiteMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, key: CallSiteKey, summary: CallSiteSummary) -> u64 {
        match self.slots.get_mut(&key) {
            Some(slot) => {
                if slot.value != summary {
                    slot.revision += 1;
                }
                slot.value = summary;
                slot.revision
            }
            None => {
                self.slots.insert(
                    key,
                    Revisioned {
                        value: summary,
                        revision: 1,
                    },
                );
                1
            }
        }
    }

    pub fn get(&self, key: &CallSiteKey) -> Option<&CallSiteSummary> {
        self.slots.get(key).map(|slot| &slot.value)
    }

    pub fn revision(&self, key: &CallSiteKey) -> Option<u64> {
        self.slots.get(key).map(|slot| slot.revision)
    }
}

impl DependencySnapshot {
    pub fn record(&mut self, fact: FactKey, revision: u64) {
        match self.revisions.get(&fact).copied() {
            Some(existing) => {
                assert_eq!(
                    existing, revision,
                    "dependency snapshots should not observe mixed revisions for one fact"
                );
            }
            None => {
                self.revisions.insert(fact, revision);
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&FactKey, &u64)> {
        self.revisions.iter()
    }
}

impl SemanticClosureMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, root: RootId, closure: SemanticClosure, dependencies: DependencySnapshot) -> u64 {
        self.ensure(root);
        let slot = &mut self.slots[root.as_u32() as usize];
        let revision = match slot {
            Some(existing) if existing.closure == closure && existing.dependencies == dependencies => existing.revision,
            Some(existing) => existing.revision + 1,
            None => 1,
        };
        *slot = Some(SemanticClosureSlot {
            closure,
            dependencies,
            revision,
        });
        revision
    }

    pub fn get(&self, root: RootId) -> Option<&SemanticClosure> {
        self.slots
            .get(root.as_u32() as usize)
            .and_then(|slot| slot.as_ref().map(|slot| &slot.closure))
    }

    pub fn dependencies(&self, root: RootId) -> Option<&DependencySnapshot> {
        self.slots
            .get(root.as_u32() as usize)
            .and_then(|slot| slot.as_ref().map(|slot| &slot.dependencies))
    }

    pub fn revision(&self, root: RootId) -> Option<u64> {
        self.slots
            .get(root.as_u32() as usize)
            .and_then(|slot| slot.as_ref().map(|slot| slot.revision))
    }

    fn ensure(&mut self, root: RootId) {
        let needed = root.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || None);
        }
    }
}
