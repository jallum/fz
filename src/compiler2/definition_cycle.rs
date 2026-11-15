//! A module definition that waits on itself.
//!
//! Code that runs while a module is being defined (a macro the body invokes,
//! and everything that macro's compiled program needs) can call into that
//! module. The module's definition then waits on code that waits on the
//! module's definition, and the drive stalls. At the terminal frontier that
//! loop is visible in the waits: each stalled job waits on a fact or a
//! product, each fact has the job that produces it, and each product drive
//! that deferred has the facts it waits on.

use crate::fast_hash::{HashMap, HashSet};

use super::drive::{DependencyKey, FactKey, Job};
use super::identity::ModuleId;
use super::pull::ProductScope;
use fz_engine::UnresolvedWait;

/// The loop through `DefineModule(module)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DefinitionCycle {
    pub(crate) module: ModuleId,
    /// The job on the loop that waits on a fact the module's definition
    /// produces.
    pub(crate) entry: Job,
    /// What the module's definition waits on: the loop's first step.
    pub(crate) exit: DependencyKey,
    /// Every stalled job that waits, directly or through others, on the
    /// module's definition. A wait whose producer is one of them is stalled
    /// because of the loop.
    pub(crate) stalled_by_it: HashSet<Job>,
}

/// Who waits on whom among the stalled jobs.
pub(crate) struct WaitForGraph {
    /// In the frontier's order, so the loop found first is the same on
    /// every run.
    jobs: Vec<Job>,
    edges: HashMap<Job, Vec<(DependencyKey, Vec<Job>)>>,
}

impl WaitForGraph {
    /// `producer` names the job that publishes a fact; `deferred` names the
    /// facts a product drive that deferred is waiting on.
    pub(crate) fn new(
        waits: &[UnresolvedWait<Job, DependencyKey>],
        producer: impl Fn(&FactKey) -> Option<Job>,
        deferred: impl Fn(&ProductScope) -> Vec<FactKey>,
    ) -> Self {
        let mut jobs = Vec::new();
        let mut edges: HashMap<Job, Vec<(DependencyKey, Vec<Job>)>> = HashMap::default();
        for wait in waits {
            let dependency = wait.fact.fact();
            let next: Vec<Job> = match dependency {
                DependencyKey::Fact(fact) => producer(fact).into_iter().collect(),
                DependencyKey::Product(address) => deferred(&address.scope).iter().filter_map(&producer).collect(),
            };
            for job in &wait.jobs {
                let job_edges = edges.entry(job.clone()).or_insert_with(|| {
                    jobs.push(job.clone());
                    Vec::new()
                });
                job_edges.push((dependency.clone(), next.clone()));
            }
        }
        Self { jobs, edges }
    }

    /// The first stalled module definition that its own waits lead back to.
    pub(crate) fn definition_cycle(&self) -> Option<DefinitionCycle> {
        self.jobs.iter().find_map(|job| match job {
            Job::DefineModule(module) => self.cycle_through(*module, job),
            _ => None,
        })
    }

    fn cycle_through(&self, module: ModuleId, definition: &Job) -> Option<DefinitionCycle> {
        let mut reached_by: HashMap<Job, (Job, DependencyKey)> = HashMap::default();
        let mut frontier = vec![definition.clone()];
        while !frontier.is_empty() {
            let mut next_frontier = Vec::new();
            for job in frontier {
                for (dependency, producers) in self.edges_of(&job) {
                    for producer in producers {
                        if producer == definition {
                            if !matches!(dependency, DependencyKey::Fact(_)) {
                                continue;
                            }
                            let exit = self.first_step(definition, &job, dependency, &reached_by);
                            return Some(DefinitionCycle {
                                module,
                                entry: job,
                                exit,
                                stalled_by_it: self.waiting_on(definition),
                            });
                        }
                        if !reached_by.contains_key(producer) {
                            reached_by.insert(producer.clone(), (job.clone(), dependency.clone()));
                            next_frontier.push(producer.clone());
                        }
                    }
                }
            }
            frontier = next_frontier;
        }
        None
    }

    /// The dependency the walk left `definition` by on its way to `last`.
    fn first_step(
        &self,
        definition: &Job,
        last: &Job,
        last_dependency: &DependencyKey,
        reached_by: &HashMap<Job, (Job, DependencyKey)>,
    ) -> DependencyKey {
        let mut step = (last.clone(), last_dependency.clone());
        while step.0 != *definition {
            step = reached_by[&step.0].clone();
        }
        step.1
    }

    /// Every job from which `target` is reachable, `target` included.
    fn waiting_on(&self, target: &Job) -> HashSet<Job> {
        let mut waiters_of: HashMap<&Job, Vec<&Job>> = HashMap::default();
        for (job, job_edges) in &self.edges {
            for producer in job_edges.iter().flat_map(|(_, producers)| producers) {
                waiters_of.entry(producer).or_default().push(job);
            }
        }
        let mut reached = HashSet::from_iter([target.clone()]);
        let mut frontier = vec![target];
        while let Some(job) = frontier.pop() {
            for waiter in waiters_of.get(job).into_iter().flatten() {
                if reached.insert((*waiter).clone()) {
                    frontier.push(waiter);
                }
            }
        }
        reached
    }

    fn edges_of(&self, job: &Job) -> &[(DependencyKey, Vec<Job>)] {
        self.edges.get(job).map(Vec::as_slice).unwrap_or(&[])
    }
}

#[cfg(test)]
#[path = "definition_cycle_test.rs"]
mod definition_cycle_test;
