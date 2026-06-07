use std::collections::{HashMap, HashSet};
use std::hash::Hash;

pub trait FactPattern<F> {
    fn matches(&self, fact: &F) -> bool;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExactPattern<F>(pub F);

impl<F> FactPattern<F> for ExactPattern<F>
where
    F: PartialEq,
{
    fn matches(&self, fact: &F) -> bool {
        &self.0 == fact
    }
}

#[derive(Debug)]
pub struct DependencyIndex<J, F, P> {
    reads: HashMap<J, HashSet<F>>,
    subscribers: HashMap<F, HashSet<J>>,
    waits: HashMap<J, HashSet<P>>,
    waiters: HashMap<P, HashSet<J>>,
    outputs: HashMap<J, HashSet<F>>,
}

impl<J, F, P> Default for DependencyIndex<J, F, P> {
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

impl<J, F, P> DependencyIndex<J, F, P>
where
    J: Clone + Eq + Hash,
    F: Clone + Eq + Hash,
    P: Clone + Eq + Hash + FactPattern<F>,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn replace_reads(&mut self, job: J, next_reads: HashSet<F>) {
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

    pub fn replace_waits(&mut self, job: J, next_waits: HashSet<P>) {
        if let Some(previous_waits) = self.waits.insert(job.clone(), next_waits.clone()) {
            for pattern in previous_waits {
                if let Some(jobs) = self.waiters.get_mut(&pattern) {
                    jobs.remove(&job);
                    if jobs.is_empty() {
                        self.waiters.remove(&pattern);
                    }
                }
            }
        }

        for pattern in next_waits {
            self.waiters.entry(pattern).or_default().insert(job.clone());
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

    pub fn subscribers(&self, key: &F) -> Vec<J> {
        self.subscribers
            .get(key)
            .map(|jobs| jobs.iter().cloned().collect())
            .unwrap_or_default()
    }

    pub fn waiters_matching(&self, key: &F) -> Vec<J> {
        self.waiters
            .iter()
            .filter(|(pattern, _)| pattern.matches(key))
            .flat_map(|(_, jobs)| jobs.iter().cloned())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect()
    }
}
