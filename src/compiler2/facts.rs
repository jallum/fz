use std::collections::{HashMap, HashSet};
use std::hash::Hash;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fingerprint(u64);

impl Fingerprint {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn absent() -> Self {
        Self(0)
    }

    pub fn as_u64(self) -> u64 {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FactChange<F> {
    pub key: F,
    pub old_fingerprint: Fingerprint,
    pub new_fingerprint: Fingerprint,
}

#[derive(Debug, Clone)]
pub struct FactReplace<F> {
    pub changed: Vec<FactChange<F>>,
    pub output_keys: HashSet<F>,
}

#[derive(Debug, Clone)]
pub struct FactSlot<J, V> {
    aggregate: Option<V>,
    fingerprint: Fingerprint,
    contributions: HashMap<J, V>,
}

impl<J, V> Default for FactSlot<J, V> {
    fn default() -> Self {
        Self {
            aggregate: None,
            fingerprint: Fingerprint::absent(),
            contributions: HashMap::new(),
        }
    }
}

impl<J, V> FactSlot<J, V> {
    pub fn aggregate(&self) -> Option<&V> {
        self.aggregate.as_ref()
    }

    pub fn fingerprint(&self) -> Fingerprint {
        self.fingerprint
    }

    pub fn contributions(&self) -> &HashMap<J, V> {
        &self.contributions
    }
}

pub trait FactAggregator<J, F, V>
where
    J: Eq + Hash,
{
    fn aggregate(&self, key: &F, contributions: &HashMap<J, V>) -> Option<V>;

    fn fingerprint(&self, key: &F, aggregate: &V) -> Fingerprint;
}

#[derive(Debug)]
pub struct FactTable<J, F, V, A> {
    slots: HashMap<F, FactSlot<J, V>>,
    aggregator: A,
}

impl<J, F, V, A> FactTable<J, F, V, A>
where
    J: Clone + Eq + Hash,
    F: Clone + Eq + Hash,
    A: FactAggregator<J, F, V>,
{
    pub fn new(aggregator: A) -> Self {
        Self {
            slots: HashMap::new(),
            aggregator,
        }
    }

    pub fn get(&self, key: &F) -> Option<&V> {
        self.slots.get(key).and_then(FactSlot::aggregate)
    }

    pub fn slot(&self, key: &F) -> Option<&FactSlot<J, V>> {
        self.slots.get(key)
    }

    pub fn replace_contributions(
        &mut self,
        job: &J,
        previous_output_keys: &HashSet<F>,
        outputs: Vec<(F, V)>,
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

            let new_fingerprint = match self.aggregator.aggregate(&key, &slot.contributions) {
                Some(aggregate) => {
                    let fingerprint = self.aggregator.fingerprint(&key, &aggregate);
                    slot.aggregate = Some(aggregate);
                    slot.fingerprint = fingerprint;
                    self.slots.insert(key.clone(), slot);
                    fingerprint
                }
                None => Fingerprint::absent(),
            };

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
