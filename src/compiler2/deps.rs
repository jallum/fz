use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use super::facts::FactUse;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnresolvedWait<J, F> {
    pub fact: FactUse<F>,
    pub jobs: Vec<J>,
}

#[derive(Debug)]
pub struct DependencyIndex<J, F> {
    reads: HashMap<J, HashSet<FactUse<F>>>,
    subscribers: HashMap<FactUse<F>, HashSet<J>>,
    waits: HashMap<J, HashSet<FactUse<F>>>,
    waiters: HashMap<FactUse<F>, HashSet<J>>,
    outputs: HashMap<J, HashSet<F>>,
}

impl<J, F> Default for DependencyIndex<J, F> {
    fn default() -> Self {
        Self {
            reads: HashMap::new(),
            subscribers: HashMap::new(),
            waits: HashMap::new(),
            waiters: HashMap::new(),
            outputs: HashMap::new(),
        }
    }
}

impl<J, F> DependencyIndex<J, F>
where
    J: Clone + Eq + Hash,
    F: Clone + Eq + Hash,
{
    pub fn new() -> Self {
        Self::default()
    }

    /// Add reads without dropping existing subscriptions. A partial (waiting)
    /// run reads less than the job's last full conclusion did, but its
    /// standing claims still depend on those earlier reads — replacing would
    /// unsubscribe the job from facts that can invalidate them.
    pub fn union_reads(&mut self, job: J, mut next_reads: HashSet<FactUse<F>>) {
        if let Some(previous) = self.reads.get(&job) {
            next_reads.retain(|key| !previous.contains(key));
        }
        if next_reads.is_empty() {
            return;
        }
        for key in &next_reads {
            self.subscribers.entry(key.clone()).or_default().insert(job.clone());
        }
        self.reads.entry(job).or_default().extend(next_reads);
    }

    pub fn replace_reads(&mut self, job: J, next_reads: HashSet<FactUse<F>>) {
        if let Some(previous_reads) = self.reads.insert(job.clone(), next_reads.clone()) {
            for key in previous_reads {
                if let Some(jobs) = self.subscribers.get_mut(&key) {
                    jobs.remove(&job);
                    if jobs.is_empty() {
                        self.subscribers.remove(&key);
                    }
                }
            }
        }

        for key in next_reads {
            self.subscribers.entry(key).or_default().insert(job.clone());
        }
    }

    pub fn replace_waits(&mut self, job: J, next_waits: HashSet<FactUse<F>>) {
        if let Some(previous_waits) = self.waits.insert(job.clone(), next_waits.clone()) {
            for fact in previous_waits {
                if let Some(jobs) = self.waiters.get_mut(&fact) {
                    jobs.remove(&job);
                    if jobs.is_empty() {
                        self.waiters.remove(&fact);
                    }
                }
            }
        }

        for fact in next_waits {
            self.waiters.entry(fact).or_default().insert(job.clone());
        }
    }

    pub fn replace_outputs(&mut self, job: J, next_outputs: HashSet<F>) {
        if next_outputs.is_empty() {
            self.outputs.remove(&job);
        } else {
            self.outputs.insert(job, next_outputs);
        }
    }

    pub fn output_keys(&self, job: &J) -> HashSet<F> {
        self.outputs.get(job).cloned().unwrap_or_default()
    }

    pub fn subscribers(&self, fact_use: &FactUse<F>) -> Vec<J> {
        self.subscribers
            .get(fact_use)
            .map(|jobs| jobs.iter().cloned().collect())
            .unwrap_or_default()
    }

    pub fn waiters(&self, fact_use: &FactUse<F>) -> Vec<J> {
        self.waiters
            .get(fact_use)
            .map(|jobs| jobs.iter().cloned().collect())
            .unwrap_or_default()
    }

    pub fn has_unresolved(&self) -> bool {
        !self.waiters.is_empty()
    }

    pub fn unresolved(&self) -> Vec<UnresolvedWait<J, F>> {
        self.waiters
            .iter()
            .map(|(fact, jobs)| UnresolvedWait {
                fact: fact.clone(),
                jobs: jobs.iter().cloned().collect(),
            })
            .collect()
    }
}
