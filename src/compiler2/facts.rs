use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::hash::Hasher;

use super::{Ty, Types};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FactChange<F> {
    pub key: F,
    pub old_fingerprint: Option<u64>,
    pub new_fingerprint: Option<u64>,
}

#[derive(Debug, Clone)]
pub struct FactReplace<F> {
    pub changed: Vec<FactChange<F>>,
    pub output_keys: HashSet<F>,
}

#[derive(Debug, Clone)]
pub struct FactSlot<J> {
    value: Option<FactValue>,
    fingerprint: Option<u64>,
    contributions: HashMap<J, FactValue>,
}

impl<J> Default for FactSlot<J> {
    fn default() -> Self {
        Self {
            value: None,
            fingerprint: None,
            contributions: HashMap::new(),
        }
    }
}

impl<J> FactSlot<J> {
    pub fn fingerprint(&self) -> Option<u64> {
        self.fingerprint
    }

    pub fn value(&self) -> Option<&FactValue> {
        self.value.as_ref()
    }

    pub fn contributions(&self) -> &HashMap<J, FactValue> {
        &self.contributions
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FactValue {
    Presence(u64),
    Inputs(Vec<Ty>),
}

impl FactValue {
    pub fn presence(revision: u64) -> Self {
        Self::Presence(revision)
    }

    pub fn inputs(types: &mut Types, inputs: Vec<Ty>) -> Self {
        Self::Inputs(
            inputs
                .into_iter()
                .map(|input| types.alpha_normalize_vars(&input))
                .collect(),
        )
    }

    fn fingerprint(&self) -> u64 {
        match self {
            FactValue::Presence(revision) => *revision,
            FactValue::Inputs(inputs) => {
                let mut hasher = DefaultHasher::new();
                inputs.hash(&mut hasher);
                hasher.finish()
            }
        }
    }

    pub(crate) fn join<'a>(types: &mut Types, values: impl IntoIterator<Item = &'a FactValue>) -> Option<FactValue> {
        let mut values = values.into_iter();
        let first = values.next()?.clone();
        Some(match first {
            FactValue::Presence(first) => {
                let mut max = first;
                for value in values {
                    let FactValue::Presence(revision) = value else {
                        panic!("fact contributions for one key should use one value family")
                    };
                    max = max.max(*revision);
                }
                FactValue::Presence(max)
            }
            FactValue::Inputs(first) => {
                let mut joined = first;
                for value in values {
                    let FactValue::Inputs(inputs) = value else {
                        panic!("fact contributions for one key should use one value family")
                    };
                    assert_eq!(
                        joined.len(),
                        inputs.len(),
                        "activation input contributions for one key should have stable arity"
                    );
                    joined = joined
                        .into_iter()
                        .zip(inputs.iter().cloned())
                        .map(|(current, observed)| {
                            if current == observed {
                                current
                            } else {
                                types.refine_widen(&current, &observed)
                            }
                        })
                        .collect();
                }
                FactValue::inputs(types, joined)
            }
        })
    }
}

impl From<u64> for FactValue {
    fn from(revision: u64) -> Self {
        Self::Presence(revision)
    }
}

#[derive(Debug)]
pub struct FactTable<J, F> {
    slots: HashMap<F, FactSlot<J>>,
}

impl<J, F> Default for FactTable<J, F> {
    fn default() -> Self {
        Self { slots: HashMap::new() }
    }
}

impl<J, F> FactTable<J, F>
where
    J: Clone + Eq + Hash,
    F: Clone + Eq + Hash,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn fingerprint(&self, key: &F) -> Option<u64> {
        self.slots.get(key).and_then(FactSlot::fingerprint)
    }

    pub fn slot(&self, key: &F) -> Option<&FactSlot<J>> {
        self.slots.get(key)
    }

    pub fn replace_contributions(
        &mut self,
        types: &mut Types,
        job: &J,
        previous_output_keys: &HashSet<F>,
        outputs: Vec<(F, FactValue)>,
    ) -> FactReplace<F> {
        let mut new_outputs = HashMap::new();
        for (key, value) in outputs {
            assert!(
                new_outputs.insert(key, value).is_none(),
                "job emitted duplicate fact output for one key"
            );
        }
        let output_keys = new_outputs.keys().cloned().collect::<HashSet<_>>();
        let touched = previous_output_keys
            .iter()
            .cloned()
            .chain(output_keys.iter().cloned())
            .collect::<HashSet<_>>();

        let mut changed = Vec::new();
        for key in touched {
            let mut slot = self.slots.remove(&key).unwrap_or_default();
            let old_fingerprint = slot.fingerprint;

            if let Some(value) = new_outputs.remove(&key) {
                slot.contributions.insert(job.clone(), value);
            } else {
                slot.contributions.remove(job);
            }

            let new_value = FactValue::join(types, slot.contributions.values());
            let new_fingerprint = new_value.as_ref().map(FactValue::fingerprint);
            if let Some(value) = new_value {
                slot.fingerprint = new_fingerprint;
                slot.value = Some(value);
                self.slots.insert(key.clone(), slot);
            }

            if old_fingerprint != new_fingerprint {
                changed.push(FactChange {
                    key,
                    old_fingerprint,
                    new_fingerprint,
                });
            }
        }

        FactReplace { changed, output_keys }
    }
}
