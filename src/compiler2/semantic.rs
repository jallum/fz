//! Compiler2's root-scoped semantic facts.
//!
//! This module stores activation-local summaries that the work graph owns:
//! observed input shapes, reachable callsites, and settled return types.

use std::collections::HashMap;

use crate::types::{Ty, Types};

use super::body::CallSiteId;
use super::identity::{ActivationKey, ExecutableNeed, FunctionId};

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
    pub arg_types: Vec<Ty>,
    pub need: ExecutableNeed,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActivationSummary {
    pub inputs: Vec<Ty>,
    pub return_ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActivationAnalysis {
    pub reachable_clauses: Vec<u32>,
    pub callsites: Vec<CallSiteId>,
}

#[derive(Debug, Clone)]
pub struct ActivationSlot {
    summary: ActivationSummary,
    input_revision: u64,
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
struct Revisioned<T> {
    value: T,
    revision: u64,
}

impl ActivationMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn activate(&mut self, key: ActivationKey, inputs: Vec<Ty>) -> u64 {
        match self.slots.get_mut(&key) {
            Some(slot) => {
                assert_eq!(
                    slot.summary.inputs.len(),
                    inputs.len(),
                    "activation arity should stay stable for one activation key"
                );

                let mut t = crate::types::new();
                let mut changed = false;
                let widened = slot
                    .summary
                    .inputs
                    .iter()
                    .cloned()
                    .zip(inputs)
                    .map(|(current, observed)| {
                        let next = t.refine_widen(&current, &observed);
                        if next != current {
                            changed = true;
                        }
                        next
                    })
                    .collect::<Vec<_>>();
                if changed {
                    slot.summary.inputs = widened;
                    slot.input_revision += 1;
                }
                slot.input_revision
            }
            None => {
                self.slots.insert(
                    key,
                    ActivationSlot {
                        summary: ActivationSummary {
                            inputs,
                            return_ty: crate::types::new().none(),
                        },
                        input_revision: 1,
                        return_revision: 0,
                        analysis: None,
                        analysis_revision: 0,
                    },
                );
                1
            }
        }
    }

    pub fn get(&self, key: &ActivationKey) -> Option<&ActivationSlot> {
        self.slots.get(key)
    }

    pub fn define_return(&mut self, key: &ActivationKey, return_ty: Ty) -> u64 {
        let slot = self
            .slots
            .get_mut(key)
            .expect("activations should exist before defining return types");
        if slot.summary.return_ty != return_ty {
            slot.summary.return_ty = return_ty;
            slot.return_revision += 1;
        }
        slot.return_revision
    }

    pub fn define_analysis(&mut self, key: &ActivationKey, analysis: ActivationAnalysis) -> u64 {
        let slot = self
            .slots
            .get_mut(key)
            .expect("activations should exist before defining analyses");
        if slot.analysis.as_ref() != Some(&analysis) {
            slot.analysis = Some(analysis);
            slot.analysis_revision += 1;
        }
        slot.analysis_revision
    }
}

impl ActivationSlot {
    pub fn summary(&self) -> &ActivationSummary {
        &self.summary
    }

    pub fn input_revision(&self) -> u64 {
        self.input_revision
    }

    pub fn return_revision(&self) -> u64 {
        self.return_revision
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
                    slot.value = summary;
                    slot.revision += 1;
                }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::RootId;
    use crate::types::Types;

    #[test]
    fn activation_map_widens_same_key_inputs_monotonically() {
        let mut activations = ActivationMap::new();
        let key = ActivationKey {
            root: RootId::from_u32(0),
            function: FunctionId::from_u32(0),
            input: Vec::new(),
        };

        let mut t = crate::types::new();
        let empty = t.empty_list();
        let one = t.int_lit(1);
        let two = t.int_lit(2);
        let singleton = t.non_empty_list(one);
        let widened = t.list(two);

        assert_eq!(activations.activate(key.clone(), vec![empty.clone()]), 1);
        assert_eq!(activations.activate(key.clone(), vec![empty]), 1);
        assert_eq!(activations.activate(key.clone(), vec![singleton]), 2);
        assert_eq!(activations.activate(key.clone(), vec![widened]), 3);

        let observed = activations
            .get(&key)
            .expect("activation should exist after observations")
            .summary();
        let int = t.int();
        let expected = t.list(int);
        assert!(
            t.is_equivalent(&observed.inputs[0], &expected),
            "same-key observations should widen to the stable input join: got {}",
            crate::types::ty_display(&observed.inputs[0])
        );
    }
}
