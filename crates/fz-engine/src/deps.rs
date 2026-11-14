use crate::fast_hash::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::hash::Hash;

use crate::facts::{FactUse, Publisher, SemanticOrd};
use crate::ordered_set::OrderedSet;
use crate::waits::StandingWaits;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnresolvedWait<J, F> {
    pub fact: FactUse<F>,
    pub jobs: Vec<J>,
}

/// Exact reads and output claims owned by each publisher, and the standing
/// waits owned by each job. Reads and claims are per answer; a wait is what
/// stopped a run, so it belongs to the job that will re-run. Each wait names
/// the job that answers it, so the standing waits are also the graph of which
/// job waits on which.
#[derive(Debug)]
pub struct DependencyIndex<P: Publisher, F> {
    reads: HashMap<P, HashSet<FactUse<F>>>,
    subscribers: HashMap<FactUse<F>, OrderedSet<P>>,
    waits: HashMap<P::Run, StandingWaits<F, P::Run>>,
    waiters: HashMap<FactUse<F>, OrderedSet<P::Run>>,
    outputs: HashMap<P, OrderedSet<F>>,
    /// Every publisher each job currently owns, in emission order. A
    /// conclusion replaces this set, so the publishers a re-run no longer
    /// reaches are the ones it retracts.
    derivations: HashMap<P::Run, OrderedSet<P>>,
    /// Answers for an absent key: a publisher or job with no entry owns, waits
    /// on and publishes nothing.
    no_outputs: OrderedSet<F>,
    no_waits: StandingWaits<F, P::Run>,
    no_derivations: OrderedSet<P>,
}

impl<P: Publisher, F> Default for DependencyIndex<P, F> {
    fn default() -> Self {
        Self {
            reads: HashMap::default(),
            subscribers: HashMap::default(),
            waits: HashMap::default(),
            waiters: HashMap::default(),
            outputs: HashMap::default(),
            derivations: HashMap::default(),
            no_outputs: OrderedSet::default(),
            no_waits: StandingWaits::default(),
            no_derivations: OrderedSet::default(),
        }
    }
}

impl<P, F> DependencyIndex<P, F>
where
    P: Publisher,
    F: Clone + Eq + Hash,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) fn has_consumers(&self, key: &F) -> bool {
        FactUse::every_use(key.clone()).iter().any(|usage| {
            self.subscribers.get(usage).is_some_and(|readers| !readers.is_empty())
                || self.waiters.get(usage).is_some_and(|waiters| !waiters.is_empty())
        })
    }

    pub fn reads(&self, publisher: &P) -> Option<&HashSet<FactUse<F>>> {
        self.reads.get(publisher)
    }

    /// Add reads without dropping existing subscriptions. A job that
    /// did not reach its conclusion reads less than its last full conclusion
    /// did, but its standing claims still depend on those earlier reads —
    /// replacing would unsubscribe it from facts that can invalidate them.
    pub fn union_reads(&mut self, publisher: P, mut next_reads: HashSet<FactUse<F>>) {
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

    pub fn replace_reads(&mut self, publisher: P, next_reads: HashSet<FactUse<F>>) {
        replace_held(&mut self.reads, &mut self.subscribers, publisher, next_reads);
    }

    pub fn replace_waits(&mut self, job: P::Run, next_waits: StandingWaits<F, P::Run>) {
        replace_held(&mut self.waits, &mut self.waiters, job, next_waits);
    }

    pub fn replace_outputs(&mut self, publisher: P, next_outputs: OrderedSet<F>) {
        if next_outputs.is_empty() {
            self.outputs.remove(&publisher);
        } else {
            self.outputs.insert(publisher, next_outputs);
        }
    }

    /// Adds `keys` to the claims `publisher` already holds, in place, and
    /// answers the union.
    pub fn extend_outputs(&mut self, publisher: &P, keys: OrderedSet<F>) -> &OrderedSet<F> {
        if keys.is_empty() {
            return self.output_keys(publisher);
        }
        let held = self.outputs.entry(publisher.clone()).or_default();
        held.extend(keys);
        held
    }

    pub fn output_keys(&self, publisher: &P) -> &OrderedSet<F> {
        self.outputs.get(publisher).unwrap_or(&self.no_outputs)
    }

    pub fn subscribers<Ctx>(&self, fact_use: &FactUse<F>, ctx: &Ctx) -> Vec<P>
    where
        P: SemanticOrd<Ctx>,
    {
        let mut publishers: Vec<_> = self
            .subscribers
            .get(fact_use)
            .map(|publishers| publishers.iter().cloned().collect())
            .unwrap_or_default();
        publishers.sort_by(|left, right| left.semantic_cmp(right, ctx));
        publishers
    }

    pub fn waiters<Ctx>(&self, fact_use: &FactUse<F>, ctx: &Ctx) -> Vec<P::Run>
    where
        P::Run: SemanticOrd<Ctx>,
    {
        let mut jobs: Vec<_> = self
            .waiters
            .get(fact_use)
            .map(|jobs| jobs.iter().cloned().collect())
            .unwrap_or_default();
        jobs.sort_by(|left, right| left.semantic_cmp(right, ctx));
        jobs
    }

    /// Every fact some job is parked on a `Concluded` wait for.
    pub fn concluded_waits(&self) -> impl Iterator<Item = &F> {
        self.waiters.iter().filter_map(|(usage, jobs)| match usage {
            FactUse::Concluded(key) if !jobs.is_empty() => Some(key),
            _ => None,
        })
    }

    pub fn has_waiter(&self, fact_use: &FactUse<F>) -> bool {
        self.waiters.get(fact_use).is_some_and(|jobs| !jobs.is_empty())
    }

    /// Every job subscribed to `fact`, in typed publisher order.
    /// Multiplicity across use variants is preserved.
    pub fn readers_of<Ctx>(&self, fact: &F, ctx: &Ctx) -> Vec<P>
    where
        P: SemanticOrd<Ctx>,
    {
        let mut readers = FactUse::every_use(fact.clone())
            .into_iter()
            .flat_map(|fact_use| self.subscribers.get(&fact_use).into_iter().flatten().cloned())
            .collect::<Vec<_>>();
        readers.sort_by(|left, right| left.semantic_cmp(right, ctx));
        readers
    }

    pub fn waits_for(&self, job: &P::Run) -> &StandingWaits<F, P::Run> {
        self.waits.get(job).unwrap_or(&self.no_waits)
    }

    /// Whether `from` waits, directly or through the jobs it waits on, for an
    /// answer only `to` can give. A run that would wait on a job already
    /// waiting on it would close a cycle of waits nothing can open.
    pub fn waits_reach(&self, from: &P::Run, to: &P::Run) -> bool {
        if self.waits_for(from).is_empty() {
            return false;
        }
        let mut pending = vec![from];
        let mut seen = HashSet::default();
        while let Some(job) = pending.pop() {
            if !seen.insert(job) {
                continue;
            }
            for producer in self.waits_for(job).producers() {
                if producer == to {
                    return true;
                }
                pending.push(producer);
            }
        }
        false
    }

    /// Whether `job`'s most recent completion left waits standing.
    pub fn blocked(&self, job: &P::Run) -> bool {
        self.waits.get(job).is_some_and(|waits| !waits.is_empty())
    }

    /// Every completion records its wait set, including an empty conclusion.
    pub fn has_run(&self, job: &P::Run) -> bool {
        self.waits.contains_key(job)
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
            .filter(|fact| fact.readiness() == crate::facts::FactReadiness::Settled)
            .map(|fact| fact.fact().clone())
            .collect()
    }

    /// Every standing wait in caller-defined semantic fact/use order. This
    /// inventory is a terminal diagnostic view; generic dependency storage
    /// cannot interpret owner-specific identities such as World-local types.
    pub fn unresolved<Ctx>(&self, ctx: &Ctx) -> Vec<UnresolvedWait<P::Run, F>>
    where
        P::Run: SemanticOrd<Ctx>,
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

    /// Every publisher `job` currently owns, in emission order.
    pub fn derivations_of(&self, job: &P::Run) -> &OrderedSet<P> {
        self.derivations.get(job).unwrap_or(&self.no_derivations)
    }

    /// Records the publishers `job` owns after a run. Emission order is the
    /// wake order downstream, so the set keeps it.
    pub fn replace_derivations(&mut self, job: P::Run, next: OrderedSet<P>) {
        if next.is_empty() {
            self.derivations.remove(&job);
        } else {
            self.derivations.insert(job, next);
        }
    }

    /// Drops one publisher's reads and claims entirely: nothing derives it any
    /// more, so it subscribes to nothing and owns nothing.
    pub fn forget(&mut self, publisher: &P) {
        if let Some(previous) = self.reads.remove(publisher) {
            for fact in previous {
                if let Some(publishers) = self.subscribers.get_mut(&fact) {
                    publishers.remove(publisher);
                    if publishers.is_empty() {
                        self.subscribers.remove(&fact);
                    }
                }
            }
        }
        self.outputs.remove(publisher);
    }
}

/// The facts a held collection names.
trait HeldUses<F> {
    fn held_uses<'a>(&'a self) -> impl Iterator<Item = &'a FactUse<F>>
    where
        F: 'a;
}

impl<F: Eq + Hash> HeldUses<F> for HashSet<FactUse<F>> {
    fn held_uses<'a>(&'a self) -> impl Iterator<Item = &'a FactUse<F>>
    where
        F: 'a,
    {
        self.iter()
    }
}

impl<F: Eq + Hash, J> HeldUses<F> for StandingWaits<F, J> {
    fn held_uses<'a>(&'a self) -> impl Iterator<Item = &'a FactUse<F>>
    where
        F: 'a,
    {
        self.uses()
    }
}

/// Stores `next` as what `holder` holds, and brings the reverse index in line:
/// the facts the holder no longer holds forget it, and the facts it holds
/// remember it. The set is stored whole, then read back from where it lives.
fn replace_held<K, F, H>(
    held: &mut HashMap<K, H>,
    holders_of: &mut HashMap<FactUse<F>, OrderedSet<K>>,
    holder: K,
    next: H,
) where
    K: Clone + Eq + Hash,
    F: Clone + Eq + Hash,
    H: HeldUses<F>,
{
    let stored = match held.entry(holder.clone()) {
        Entry::Occupied(mut entry) => {
            let previous = entry.insert(next);
            for fact in previous.held_uses() {
                if let Some(holders) = holders_of.get_mut(fact) {
                    holders.remove(&holder);
                    if holders.is_empty() {
                        holders_of.remove(fact);
                    }
                }
            }
            entry.into_mut()
        }
        Entry::Vacant(entry) => entry.insert(next),
    };
    for fact in stored.held_uses() {
        holders_of.entry(fact.clone()).or_default().insert(holder.clone());
    }
}
