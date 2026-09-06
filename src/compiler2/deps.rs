use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use super::facts::{DerivationId, FactUse, Publisher};
use super::ordered_set::OrderedSet;
use super::semantic::SemanticOrd;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnresolvedWait<J, F> {
    pub fact: FactUse<F>,
    pub jobs: Vec<J>,
}

/// Two identities, kept apart on purpose (fz-kdt.13.1).
///
/// `reads`/`subscribers`/`outputs` are keyed by `Publisher<J>` — one job's one
/// derivation — because those three are the ledger: a claim belongs to the
/// answer it came from, and finality is a property of that answer's reads.
///
/// `waits`/`waiters` and the derivation roster are keyed by `J`, because a job
/// blocks and runs WHOLE. A wait carries no derivation attribution and could
/// not honestly be given one.
#[derive(Debug)]
pub struct DependencyIndex<J, F> {
    reads: HashMap<Publisher<J>, HashSet<FactUse<F>>>,
    subscribers: HashMap<FactUse<F>, OrderedSet<Publisher<J>>>,
    waits: HashMap<J, HashSet<FactUse<F>>>,
    waiters: HashMap<FactUse<F>, OrderedSet<J>>,
    outputs: HashMap<Publisher<J>, OrderedSet<F>>,
    /// Which derivations each job currently publishes under, in the order the
    /// job first reported them. Insertion-ordered because every job-level fold
    /// below (the claim set, the read union, dirtying a whole job) iterates it,
    /// and those folds feed wake order (`ordered_set.rs`).
    derivations: HashMap<J, OrderedSet<DerivationId>>,
}

impl<J, F> Default for DependencyIndex<J, F> {
    fn default() -> Self {
        Self {
            reads: HashMap::new(),
            subscribers: HashMap::new(),
            waits: HashMap::new(),
            waiters: HashMap::new(),
            outputs: HashMap::new(),
            derivations: HashMap::new(),
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

    pub(crate) fn has_consumers(&self, key: &F) -> bool {
        [FactUse::current(key.clone()), FactUse::settled(key.clone())]
            .iter()
            .any(|usage| {
                self.subscribers.get(usage).is_some_and(|readers| !readers.is_empty())
                    || self.waiters.get(usage).is_some_and(|waiters| !waiters.is_empty())
            })
    }

    pub fn reads(&self, publisher: &Publisher<J>) -> Option<&HashSet<FactUse<F>>> {
        self.reads.get(publisher)
    }

    /// Every fact use the job read, across all its derivations. The
    /// job-granular projection: telemetry attributes reads to the job that ran,
    /// because the job is what ran.
    pub fn job_reads(&self, job: &J) -> HashSet<FactUse<F>> {
        self.job_read_uses(job).cloned().collect()
    }

    fn job_read_uses(&self, job: &J) -> impl Iterator<Item = &FactUse<F>> {
        self.derivations
            .get(job)
            .into_iter()
            .flat_map(|ids| ids.iter())
            .filter_map(move |id| self.reads.get(&Publisher::new(job.clone(), *id)))
            .flatten()
    }

    pub(crate) fn job_dependency_uses(&self, job: &J) -> impl Iterator<Item = &FactUse<F>> {
        self.job_read_uses(job).chain(self.waits.get(job).into_iter().flatten())
    }

    /// Records the derivations `job` published under this run. Idempotent, and
    /// first-registration order is the order the roster keeps. A job that
    /// completes always gets a roster entry, even an empty one — that entry is
    /// what `has_run` reads.
    pub fn register_derivations(&mut self, job: &J, reported: &[DerivationId]) {
        let roster = self.derivations.entry(job.clone()).or_default();
        for derivation in reported {
            roster.insert(*derivation);
        }
    }

    /// The job's derivations as publishers, in roster order.
    pub fn publishers(&self, job: &J) -> Vec<Publisher<J>> {
        self.derivations
            .get(job)
            .map(|ids| ids.iter().map(|id| Publisher::new(job.clone(), *id)).collect())
            .unwrap_or_default()
    }

    /// Drops every derivation of `job` outside `reported`, returning the
    /// publishers that were dropped so the caller can retract their claims.
    /// Retraction-by-omission lifted to the derivation: a job that concludes
    /// and does not report a derivation has withdrawn that whole answer,
    /// exactly as an unlisted output key withdraws one claim.
    pub fn retain_derivations(&mut self, job: &J, reported: &[DerivationId]) -> Vec<Publisher<J>> {
        let dropped = self
            .publishers(job)
            .into_iter()
            .filter(|publisher| !reported.contains(&publisher.derivation))
            .collect::<Vec<_>>();
        if let Some(roster) = self.derivations.get_mut(job) {
            for publisher in &dropped {
                roster.remove(&publisher.derivation);
            }
        }
        dropped
    }

    /// Add reads without dropping existing subscriptions. A derivation that
    /// did not reach its conclusion reads less than its last full conclusion
    /// did, but its standing claims still depend on those earlier reads —
    /// replacing would unsubscribe it from facts that can invalidate them.
    pub fn union_reads(&mut self, publisher: Publisher<J>, mut next_reads: HashSet<FactUse<F>>) {
        if let Some(previous) = self.reads.get(&publisher) {
            next_reads.retain(|key| !previous.contains(key));
        }
        if next_reads.is_empty() {
            return;
        }
        for key in &next_reads {
            self.subscribers
                .entry(key.clone())
                .or_default()
                .insert(publisher.clone());
        }
        self.reads.entry(publisher).or_default().extend(next_reads);
    }

    pub fn replace_reads(&mut self, publisher: Publisher<J>, next_reads: HashSet<FactUse<F>>) {
        if let Some(previous_reads) = self.reads.insert(publisher.clone(), next_reads.clone()) {
            for key in previous_reads {
                if let Some(publishers) = self.subscribers.get_mut(&key) {
                    publishers.remove(&publisher);
                    if publishers.is_empty() {
                        self.subscribers.remove(&key);
                    }
                }
            }
        }

        for key in next_reads {
            self.subscribers.entry(key).or_default().insert(publisher.clone());
        }
    }

    /// Forgets a derivation entirely: its reads unsubscribe and its read entry
    /// goes. Paired with `replace_outputs(publisher, empty)` this is how a
    /// withdrawn answer leaves the ledger with nothing behind.
    pub fn forget_reads(&mut self, publisher: &Publisher<J>) {
        if let Some(previous_reads) = self.reads.remove(publisher) {
            for key in previous_reads {
                if let Some(publishers) = self.subscribers.get_mut(&key) {
                    publishers.remove(publisher);
                    if publishers.is_empty() {
                        self.subscribers.remove(&key);
                    }
                }
            }
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

    pub fn replace_outputs(&mut self, publisher: Publisher<J>, next_outputs: OrderedSet<F>) {
        if next_outputs.is_empty() {
            self.outputs.remove(&publisher);
        } else {
            self.outputs.insert(publisher, next_outputs);
        }
    }

    pub fn output_keys(&self, publisher: &Publisher<J>) -> OrderedSet<F> {
        self.outputs.get(publisher).cloned().unwrap_or_default()
    }

    /// Every key the job claims, across all its derivations, in roster order
    /// then emission order. Both halves are ordered, so this is too.
    pub fn job_output_keys(&self, job: &J) -> OrderedSet<F> {
        let mut keys = OrderedSet::default();
        for publisher in self.publishers(job) {
            if let Some(outputs) = self.outputs.get(&publisher) {
                keys.extend(outputs.iter().cloned());
            }
        }
        keys
    }

    pub fn subscribers<Ctx>(&self, fact_use: &FactUse<F>, ctx: &Ctx) -> Vec<Publisher<J>>
    where
        J: SemanticOrd<Ctx>,
    {
        let mut publishers: Vec<_> = self
            .subscribers
            .get(fact_use)
            .map(|publishers| publishers.iter().cloned().collect())
            .unwrap_or_default();
        publishers.sort_by(|left, right| {
            left.job
                .semantic_cmp(&right.job, ctx)
                .then_with(|| left.derivation.0.cmp(&right.derivation.0))
        });
        publishers
    }

    pub fn waiters<Ctx>(&self, fact_use: &FactUse<F>, ctx: &Ctx) -> Vec<J>
    where
        J: SemanticOrd<Ctx>,
    {
        let mut jobs: Vec<_> = self
            .waiters
            .get(fact_use)
            .map(|jobs| jobs.iter().cloned().collect())
            .unwrap_or_default();
        jobs.sort_by(|left, right| left.semantic_cmp(right, ctx));
        jobs
    }

    pub fn has_waiter(&self, fact_use: &FactUse<F>) -> bool {
        self.waiters.get(fact_use).is_some_and(|jobs| !jobs.is_empty())
    }

    /// Every derivation subscribed to `fact`, in typed publisher order.
    /// Multiplicity across use variants is preserved.
    pub fn readers_of<Ctx>(&self, fact: &F, ctx: &Ctx) -> Vec<Publisher<J>>
    where
        J: SemanticOrd<Ctx>,
    {
        let mut readers = [FactUse::current(fact.clone()), FactUse::settled(fact.clone())]
            .into_iter()
            .flat_map(|fact_use| self.subscribers.get(&fact_use).into_iter().flatten().cloned())
            .collect::<Vec<_>>();
        readers.sort_by(|left, right| {
            left.job
                .semantic_cmp(&right.job, ctx)
                .then_with(|| left.derivation.0.cmp(&right.derivation.0))
        });
        readers
    }

    pub fn waits_for(&self, job: &J) -> HashSet<FactUse<F>> {
        self.waits.get(job).cloned().unwrap_or_default()
    }

    /// Whether `job`'s most recent completion left waits standing.
    pub fn blocked(&self, job: &J) -> bool {
        self.waits.get(job).is_some_and(|waits| !waits.is_empty())
    }

    /// Whether `job` has ever completed a run: completing registers its
    /// derivations (even one that reads and publishes nothing), blocking
    /// records standing waits.
    pub fn has_run(&self, job: &J) -> bool {
        self.derivations.contains_key(job) || self.blocked(job)
    }

    pub fn has_unresolved(&self) -> bool {
        !self.waiters.is_empty()
    }

    /// The facts blocked waiters currently wait on with `Settled` readiness,
    /// facts only — no job lists cloned, no dedup needed (each `FactUse` keys
    /// one waiter set). Iteration order is the `waiters` map's own, so the
    /// caller orders by data before acting.
    pub fn waited_settled_facts(&self) -> Vec<F> {
        self.waiters
            .keys()
            .filter(|fact| fact.readiness() == crate::compiler2::facts::FactReadiness::Settled)
            .map(|fact| fact.fact().clone())
            .collect()
    }

    /// Every standing wait in caller-defined semantic fact/use order. This
    /// inventory is a terminal diagnostic view; generic dependency storage
    /// cannot interpret owner-specific identities such as World-local types.
    pub fn unresolved<Ctx>(&self, ctx: &Ctx) -> Vec<UnresolvedWait<J, F>>
    where
        J: SemanticOrd<Ctx>,
        F: SemanticOrd<Ctx>,
    {
        let mut waits = self
            .waiters
            .iter()
            .map(|(fact, jobs)| UnresolvedWait {
                fact: fact.clone(),
                jobs: jobs.iter().cloned().collect(),
            })
            .collect::<Vec<_>>();
        waits.sort_by(|left, right| left.fact.semantic_cmp(&right.fact, ctx));
        for wait in &mut waits {
            wait.jobs.sort_by(|left, right| left.semantic_cmp(right, ctx));
        }
        waits
    }
}
