use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use super::agenda::Agenda;
use super::deps::{DependencyIndex, UnresolvedWait};
use super::facts::{ClaimShape, ContentMovement, FactChange, FactMovement, FactState, FactTable, FactUse, Publisher};
use super::ordered_set::OrderedSet;
use super::semantic::SemanticOrd;

/// Reads dependency state from its owner without copying it into the fact table.
/// `None` selects a scheduler-owned fact. `Some` selects external ownership,
/// including when that dependency has no current value.
pub(crate) trait ExternalDependencyStates<F> {
    fn external_state(&self, key: &F) -> Option<FactState>;
}

pub(crate) struct NoExternalDependencyStates;

impl<F> ExternalDependencyStates<F> for NoExternalDependencyStates {
    fn external_state(&self, _key: &F) -> Option<FactState> {
        None
    }
}

/// Why a job entered the agenda. This is observation-only: it never changes
/// which job runs or in what order, it only tags each work-start so a running
/// test can distinguish the compiler's sanctioned entry points from anything
/// else.
///
/// The pull-based northstar (`../pull-based.html`, `.agent/docs/telemetry.md`)
/// allows exactly these ways for a job to start:
///
/// - `Ignition`: an external submission (`World::submit_code`,
///   `submit_module_interface`, `submit_root`) enqueuing the one job that
///   begins that submission's own work. This is the front door, not a job
///   commanding another job.
/// - `ChangedRevisionWake`: `Scheduler::complete`'s wake propagation
///   (`enqueue_dependents`/`enqueue_step`) re-running a job whose fact
///   subscription (read or wait) just changed. This is
///   the core pull mechanism: readers wake because their ground moved, never
///   because a producer pushed them by name.
/// - `ActivationFrontier`: `drive::demand_activation_frontier_analyses`
///   expanding a published activation's standing analysis demand through the
///   fact->producer map. Root entries and caller-discovered callees use this
///   one path.
/// - `BlockedWaiterExpansion`: the fact->producer map
///   (`World::demand_fact_producer`) expanding a blocked waiter's missing
///   fact to its single producer at a drain/stall point — both the bare
///   scheduler's `demand_blocked_wait_producers`/`drive_until` stall pass and
///   the bounded product-pull's own fact-wait loop
///   (`product_drive::drive_product_fact_wait`) use this.
///
/// `Unclassified` is the catch-all default. A future enqueue call site that
/// does not pass one of the reasons above — a reintroduced `follow_up`-style
/// push, for instance — is counted here, which is exactly what trips the
/// running pull-only guard (`work_start_reason_test`'s
/// `pull_only_guard_holds_for_*` cases).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum WorkStartReason {
    Ignition,
    ChangedRevisionWake,
    ActivationFrontier,
    BlockedWaiterExpansion,
    #[default]
    Unclassified,
}

/// A snapshot of a scheduler's cumulative work-start attribution: how many
/// jobs entered the agenda under each `WorkStartReason`, plus how many
/// whole-fact-table scans (`Scheduler::fact_keys`) and drain-time global
/// discovery sweeps were taken. Carried out of the scheduler as a single value
/// so the pull session can record and emit the full breakdown
/// (`pull.session.finished`) without reaching back into the world.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct WorkStartTally {
    pub ignition: u64,
    pub changed_revision_wake: u64,
    pub activation_frontier: u64,
    pub blocked_waiter_expansion: u64,
    pub unclassified: u64,
    pub root_scans: u64,
    pub drain_discovery_sweeps: u64,
}

impl WorkStartTally {
    /// Jobs that entered the agenda with no attributable sanctioned reason.
    /// Must stay zero on every sanctioned path: a reintroduced push (a
    /// follow-up-style enqueue that forgets to name a reason) lands here by
    /// construction, since `WorkStartReason` defaults to `Unclassified`.
    pub fn unsanctioned_work_starts(&self) -> u64 {
        self.unclassified
    }

    pub(crate) fn delta_since(self, earlier: Self) -> Self {
        let delta = |current: u64, previous: u64| {
            current
                .checked_sub(previous)
                .expect("cumulative work-start counters cannot move backwards")
        };
        Self {
            ignition: delta(self.ignition, earlier.ignition),
            changed_revision_wake: delta(self.changed_revision_wake, earlier.changed_revision_wake),
            activation_frontier: delta(self.activation_frontier, earlier.activation_frontier),
            blocked_waiter_expansion: delta(self.blocked_waiter_expansion, earlier.blocked_waiter_expansion),
            unclassified: delta(self.unclassified, earlier.unclassified),
            root_scans: delta(self.root_scans, earlier.root_scans),
            drain_discovery_sweeps: delta(self.drain_discovery_sweeps, earlier.drain_discovery_sweeps),
        }
    }

    pub(crate) fn add(&mut self, other: Self) {
        self.ignition += other.ignition;
        self.changed_revision_wake += other.changed_revision_wake;
        self.activation_frontier += other.activation_frontier;
        self.blocked_waiter_expansion += other.blocked_waiter_expansion;
        self.unclassified += other.unclassified;
        self.root_scans += other.root_scans;
        self.drain_discovery_sweeps += other.drain_discovery_sweeps;
    }
}

/// Whether a wake newly started a job or found it already pending.
///
/// `Enqueued`: `Agenda::enqueue` transitioned the job from absent to pending
/// — a new work start (tallied under `WorkStartReason::ChangedRevisionWake`).
///
/// `Coalesced`: the job was already pending in the agenda from an earlier
/// wake this same `complete` call (agenda dedupe: `Agenda::enqueue` returned
/// false because the job was already queued). This is the only coalescing
/// source — there is no standing-conclusion coalescing left to conflate it
/// with. A job can be coalesced more than once in one `complete` call, once
/// per additional cause that finds it already pending; each is its own
/// record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WakeDisposition {
    Enqueued,
    Coalesced,
}

/// One attributable wake: `cause` is the fact use whose change made `job`
/// re-enter (or attempt to re-enter) the agenda, `disposition` says whether
/// that attempt was the job's new work start or found it already pending,
/// and `shift` carries the same ground-shift-vs-ascent classification
/// `complete` computed for `cause`. Wake order is preserved (the order
/// `enqueue_dependents` visited causes), and a single job can carry more
/// than one `Wake` in the same `AppliedStep` — one per cause that touched
/// it.
#[derive(Debug, Clone)]
pub struct Wake<J, F> {
    pub cause: FactUse<F>,
    pub job: J,
    pub disposition: WakeDisposition,
    pub shift: bool,
}

#[derive(Debug, Clone)]
pub struct AppliedStep<J, F> {
    pub changed: Vec<FactChange<F>>,
    pub movements: Vec<FactMovement<F>>,
    /// Every wake this completion caused, in wake order, each carrying its
    /// own cause and disposition (see `Wake`).
    pub wakes: Vec<Wake<J, F>>,
    pub blocked: Vec<FactUse<F>>,
}

/// What draining a wave of fact changes produced: the wakes it caused, in wake
/// order, and the movements it published.
type DispatchedWave<J, F> = (Vec<Wake<J, F>>, Vec<FactMovement<F>>);

/// One answer: the reads it stands on and the facts it owns. Concluding one
/// replaces both; the publisher's previous claims it no longer lists are
/// retracted.
#[derive(Debug, Clone)]
pub struct DerivationEffects<P, F> {
    pub publisher: P,
    pub reads: HashSet<FactUse<F>>,
    pub outputs: Vec<F>,
    pub changed: Vec<F>,
}

/// One job run: the answers it reached, in emission order, and the waits that
/// stopped it. A run that finished lists the job's own publisher among them;
/// a run with standing waits has not reached that answer yet, so the job's own
/// publisher keeps its claims dirty while every other answer it reached stands.
#[derive(Debug, Clone)]
pub struct CompletionEffects<P, F> {
    pub derivations: Vec<DerivationEffects<P, F>>,
    pub waits: HashSet<FactUse<F>>,
}

impl<P, F> CompletionEffects<P, F> {
    /// The shape of a job that answers one question per run.
    pub fn single(
        publisher: P,
        reads: HashSet<FactUse<F>>,
        waits: HashSet<FactUse<F>>,
        outputs: Vec<F>,
        changed: Vec<F>,
    ) -> Self {
        Self {
            derivations: vec![DerivationEffects {
                publisher,
                reads,
                outputs,
                changed,
            }],
            waits,
        }
    }
}

pub(super) fn take_next_fact_change<F, Ctx>(pending: &mut Vec<FactChange<F>>, ctx: &Ctx) -> Option<FactChange<F>>
where
    F: SemanticOrd<Ctx>,
{
    let next = pending
        .iter()
        .enumerate()
        .min_by(|(left_index, left), (right_index, right)| {
            left.key
                .semantic_cmp(&right.key, ctx)
                .then_with(|| right_index.cmp(left_index))
        })
        .map(|(index, _)| index)?;
    Some(pending.remove(next))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FatalError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DriveOutcome<J, F> {
    DependencyFailed { dependency: F },
    Resolved,
    Unresolved { waits: Vec<UnresolvedWait<J, F>> },
    Fatal { job: J },
    TimedOut { jobs_ran: u64, pending_jobs: usize },
}

#[derive(Debug, Clone, Copy)]
enum ReadFinality {
    Pending(usize),
    Quiescent(usize),
}

impl ReadFinality {
    fn count(self) -> usize {
        match self {
            Self::Pending(count) | Self::Quiescent(count) => count,
        }
    }

    fn is_pending(self) -> bool {
        matches!(self, Self::Pending(_))
    }

    fn after_edge(self, became_quiet: bool) -> Self {
        if !became_quiet {
            return Self::Pending(self.count() + 1);
        }
        let count = self.count().saturating_sub(1);
        match self {
            Self::Pending(_) => Self::Pending(count),
            Self::Quiescent(_) => Self::Quiescent(count),
        }
    }
}

#[derive(Debug)]
pub struct Scheduler<P: Publisher, F> {
    agenda: Agenda<P::Run>,
    facts: FactTable<P, F>,
    deps: DependencyIndex<P, F>,
    /// Jobs whose ground shifted: a fact they read changed in a way that can
    /// invalidate their claims. A rebased job's next conclusion replaces its
    /// cumulative store values instead of joining, and its content changes
    /// propagate as shifts in turn. Cleared on conclusion; kept while waiting.
    rebased: HashSet<P>,
    /// How many of each JOB's recorded reads currently name a fact that
    /// is NOT quiet, with the drain's quiescence certificate where one exists.
    /// A new unquiet edge revokes that certificate; quiet edges decrement the
    /// real count without erasing another input's pending movement. This is the reader half of
    /// transitive finality; the fact half is `FactSlot::unfinal_publishers`,
    /// keyed by the same publisher identity. An absent entry means zero.
    read_finality: HashMap<P, ReadFinality>,
    /// Work-start attribution tally: how many jobs actually entered the
    /// agenda (deduped coalescing does not count) under each
    /// `WorkStartReason`. Observation-only — see `WorkStartReason`.
    work_starts: HashMap<WorkStartReason, u64>,
    /// How many times a whole-fact-table scan (`fact_keys`) has been taken.
    /// The pull-cutover anti-pattern is a producer discovering work by
    /// scanning every fact instead of following named dependencies; this
    /// must stay zero in production (`root_executable_frontier`, the one
    /// production caller, was deleted in fz-go4.18.4-fix).
    root_scans: u64,
    /// Empty-agenda passes that constructed the ordered activation-frontier
    /// and unresolved-wait inventories. The exact nonempty indexes guard this
    /// work, so an unchanged or irrelevant retained request does not increment.
    drain_discovery_sweeps: u64,
}

impl<P, F> Default for Scheduler<P, F>
where
    P: Publisher,
    F: Clone + Eq + Hash + ClaimShape,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<P, F> Scheduler<P, F>
where
    P: Publisher,
    F: Clone + Eq + Hash + ClaimShape,
{
    pub(crate) fn dependency_state(&self, key: &F, external: &impl ExternalDependencyStates<F>) -> FactState {
        external.external_state(key).unwrap_or_else(|| self.facts.state(key))
    }

    fn dependency_is_quiet(&self, key: &F, external: &impl ExternalDependencyStates<F>) -> bool {
        external
            .external_state(key)
            .map_or_else(|| self.facts.is_quiet(key), |state| state.settled)
    }

    pub(crate) fn dependency_satisfies(&self, usage: &FactUse<F>, external: &impl ExternalDependencyStates<F>) -> bool {
        let state = self.dependency_state(usage.fact(), external);
        match usage {
            FactUse::Current(_) => state.revision.is_some(),
            FactUse::Settled(_) => state.revision.is_some() && state.settled,
        }
    }

    pub fn complete_ordered<Ctx>(
        &mut self,
        job: &P::Run,
        effects: CompletionEffects<P, F>,
        ctx: &Ctx,
    ) -> AppliedStep<P::Run, F>
    where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
        F: SemanticOrd<Ctx>,
    {
        self.complete_ordered_with_external(job, effects, &NoExternalDependencyStates, ctx)
    }

    pub fn settle_quiescent_ordered<Ctx>(&mut self, facts: &[F], ctx: &Ctx) -> AppliedStep<P::Run, F>
    where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
        F: SemanticOrd<Ctx>,
    {
        self.settle_quiescent_ordered_with_external(facts, &NoExternalDependencyStates, ctx)
    }

    /// Deliver authoritative external movements through the same finality and wake graph as facts.
    pub(crate) fn apply_external_changes_ordered<Ctx>(
        &mut self,
        mut changes: Vec<FactChange<F>>,
        external: &impl ExternalDependencyStates<F>,
        ctx: &Ctx,
    ) -> AppliedStep<P::Run, F>
    where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
        F: SemanticOrd<Ctx>,
    {
        changes.sort_by(|left, right| left.key.semantic_cmp(&right.key, ctx));
        let mut pending = changes.clone();
        for change in &changes {
            assert!(
                external.external_state(&change.key).is_some(),
                "external movement must name an external dependency"
            );
            if change.readiness_changed() {
                self.propagate_quiet_wave(vec![change.key.clone()], change.new_settled, &mut pending, ctx);
            }
        }
        let (wakes, movements) = self.dispatch_changes(pending, external, ctx);
        AppliedStep {
            changed: changes,
            movements,
            wakes,
            blocked: Vec::new(),
        }
    }

    pub fn new() -> Self {
        Self {
            agenda: Agenda::new(),
            facts: FactTable::new(),
            deps: DependencyIndex::new(),
            rebased: HashSet::new(),
            read_finality: HashMap::new(),
            work_starts: HashMap::new(),
            root_scans: 0,
            drain_discovery_sweeps: 0,
        }
    }

    /// The cumulative work-start attribution snapshot: per-reason agenda-entry
    /// counts (coalesced re-demands of an already-pending job do not count —
    /// they are not a new work start) plus the whole-fact-table-scan count.
    pub fn work_start_tally(&self) -> WorkStartTally {
        let count = |reason| *self.work_starts.get(&reason).unwrap_or(&0);
        WorkStartTally {
            ignition: count(WorkStartReason::Ignition),
            changed_revision_wake: count(WorkStartReason::ChangedRevisionWake),
            activation_frontier: count(WorkStartReason::ActivationFrontier),
            blocked_waiter_expansion: count(WorkStartReason::BlockedWaiterExpansion),
            unclassified: count(WorkStartReason::Unclassified),
            root_scans: self.root_scans,
            drain_discovery_sweeps: self.drain_discovery_sweeps,
        }
    }

    pub(crate) fn note_drain_discovery_sweep(&mut self) {
        self.drain_discovery_sweeps += 1;
    }

    /// Whether `job`'s ground has shifted since it last concluded.
    /// Whether any answer this job owns stood on ground that shifted. The job
    /// re-runs as a whole, so this is the question a re-demand asks.
    pub fn rebased(&self, job: &P::Run) -> bool {
        self.deps
            .derivations_of(job)
            .iter()
            .any(|publisher| self.rebased.contains(publisher))
    }

    pub(crate) fn derivation_rebased(&self, publisher: &P) -> bool {
        self.rebased.contains(publisher)
    }

    pub fn pending_jobs(&self) -> usize {
        self.agenda.len()
    }

    pub fn facts(&self) -> &FactTable<P, F> {
        &self.facts
    }

    /// Iterates every fact key in the table. This is the whole-table-scan
    /// escape hatch the pull-cutover deleted from production
    /// (`root_executable_frontier`); any future caller that reaches for it to
    /// discover work by scanning instead of naming a dependency is the
    /// "root scan" anti-pattern, so each call is tallied (`root_scans`).
    pub fn fact_keys(&mut self) -> impl Iterator<Item = &F> {
        self.root_scans += 1;
        self.facts.keys()
    }

    /// Every key the job claims, in retained publication order.
    /// Every fact this job claims, across every answer it owns.
    pub fn output_keys(&self, job: &P::Run) -> OrderedSet<F> {
        let mut keys = OrderedSet::default();
        for publisher in self.deps.derivations_of(job).iter() {
            keys.extend(self.deps.output_keys(publisher).iter().cloned());
        }
        keys
    }

    /// Every fact use the job's standing answer read.
    /// Every fact use this job read, across every answer it owns.
    pub fn reads(&self, job: &P::Run) -> HashSet<FactUse<F>> {
        self.deps
            .derivations_of(job)
            .iter()
            .filter_map(|publisher| self.deps.reads(publisher))
            .flatten()
            .cloned()
            .collect()
    }

    pub(crate) fn has_dependency_consumers(&self, key: &F) -> bool {
        self.deps.has_consumers(key)
    }

    /// Every fact use this job depends on: what each of its answers read, plus
    /// the waits that stopped its last run.
    pub(crate) fn dependency_uses(&self, job: &P::Run) -> Vec<FactUse<F>> {
        self.deps
            .derivations_of(job)
            .iter()
            .filter_map(|publisher| self.deps.reads(publisher))
            .flatten()
            .cloned()
            .chain(self.deps.waits_for(job))
            .collect()
    }

    #[cfg(test)]
    pub fn unfinal_reads(&self, job: &P) -> usize {
        self.read_finality
            .get(job)
            .filter(|state| state.is_pending())
            .map_or(0, |state| state.count())
    }

    pub fn has_unresolved(&self) -> bool {
        self.deps.has_unresolved()
    }

    /// Whether `job` has ever completed a run: it concluded (reads are
    /// recorded, even empty) or blocked (waits are standing). A job that has
    /// run is reachable by the graph's own wakes; a never-run job has no wake
    /// source, so only a fresh demand can start it.
    pub(crate) fn has_run(&self, job: &P::Run) -> bool {
        self.deps.has_run(job)
    }

    /// Whether `job`'s most recent completion left waits standing.
    pub(crate) fn blocked(&self, job: &P::Run) -> bool {
        self.deps.blocked(job)
    }

    pub fn waited_settled_facts(&self) -> Vec<F> {
        self.deps.waited_settled_facts()
    }

    /// Every standing wait in the semantic order owned by `ctx`.
    pub fn unresolved<Ctx>(&self, ctx: &Ctx) -> Vec<UnresolvedWait<P::Run, F>>
    where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
        F: SemanticOrd<Ctx>,
    {
        self.deps.unresolved(ctx)
    }

    /// Enqueues `job`, tallying the work-start under `reason`. Returns
    /// whether the job was newly enqueued (`false` means it was already
    /// pending and this call coalesced into it — not a new work start, so
    /// the tally does not count it).
    pub fn enqueue(&mut self, job: P::Run, reason: WorkStartReason) -> bool {
        let started = self.agenda.enqueue(job);
        if started {
            *self.work_starts.entry(reason).or_insert(0) += 1;
        }
        started
    }

    pub fn pop(&mut self) -> Option<P::Run> {
        self.agenda.pop()
    }

    /// Concluding replaces reads and claims; waiting extends them and leaves
    /// every owned claim dirty. One completion dispatches one ordered wave.
    pub(crate) fn complete_ordered_with_external<Ctx>(
        &mut self,
        job: &P::Run,
        effects: CompletionEffects<P, F>,
        external: &impl ExternalDependencyStates<F>,
        ctx: &Ctx,
    ) -> AppliedStep<P::Run, F>
    where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
        F: SemanticOrd<Ctx>,
    {
        assert!(
            effects
                .derivations
                .iter()
                .flat_map(|derivation| derivation.outputs.iter().chain(&derivation.changed))
                .all(|key| external.external_state(key).is_none()),
            "external dependencies cannot be published as scheduler facts"
        );
        let waiting = !effects.waits.is_empty();
        let own = P::of_run(job);
        let mut blocked = effects.waits.iter().cloned().collect::<Vec<_>>();
        blocked.sort_by(|left, right| left.semantic_cmp(right, ctx));
        self.deps.replace_waits(job.clone(), effects.waits);

        let previously_owned = self.deps.derivations_of(job);
        let mut pending_changes = Vec::new();
        let mut conclusions = Vec::new();
        let mut listed = OrderedSet::default();
        for mut derivation in effects.derivations {
            // The job's own answer is the one a standing wait leaves
            // unfinished; every other answer this run reached is complete.
            let concluding = !(waiting && derivation.publisher == own);
            derivation.outputs.sort_by(|left, right| left.semantic_cmp(right, ctx));
            derivation.changed.sort_by(|left, right| left.semantic_cmp(right, ctx));
            if concluding {
                self.deps
                    .replace_reads(derivation.publisher.clone(), std::mem::take(&mut derivation.reads));
            } else {
                self.deps
                    .union_reads(derivation.publisher.clone(), std::mem::take(&mut derivation.reads));
            }
            // Only a conclusion has re-derived the standing claims from
            // shifted ground.
            let rebased = if concluding {
                self.rebased.remove(&derivation.publisher)
            } else {
                self.rebased.contains(&derivation.publisher)
            };
            self.refresh_finality(&derivation.publisher, &mut pending_changes, external, ctx);
            let unfinal = self.is_unfinal(&derivation.publisher);
            listed.insert(derivation.publisher.clone());
            conclusions.push((derivation, concluding, rebased, unfinal));
        }

        // Answers this job owned and this run did not reach. A conclusion
        // walked the whole job, so what it does not list is refuted and
        // retracted; a run that is still waiting has simply not got there, so
        // those claims stand, dirty, until it does.
        let unreached = previously_owned
            .iter()
            .filter(|publisher| !listed.contains(publisher))
            .cloned()
            .collect::<Vec<_>>();

        let mut touched = OrderedSet::default();
        for (derivation, ..) in &conclusions {
            touched.extend(derivation.outputs.iter().cloned());
            touched.extend(self.deps.output_keys(&derivation.publisher).iter().cloned());
        }
        for publisher in &unreached {
            touched.extend(self.deps.output_keys(publisher).iter().cloned());
        }
        let quiet_before = self.quiet_snapshot(&touched);

        let mut changed = Vec::new();
        for (derivation, concluding, rebased, unfinal) in conclusions {
            let publisher = derivation.publisher;
            let previous_keys = self.deps.output_keys(&publisher);
            if concluding {
                let concluded = self.facts.replace_outputs_after_run(
                    &publisher,
                    &previous_keys,
                    derivation.outputs,
                    derivation.changed,
                    unfinal,
                    rebased,
                );
                self.deps
                    .replace_outputs(publisher.clone(), concluded.output_keys.clone());
                changed.extend(concluded.changed);
            } else {
                let extended = self.facts.extend_outputs_after_run(
                    &publisher,
                    derivation.outputs,
                    derivation.changed,
                    unfinal,
                    rebased,
                );
                let mut claims = previous_keys;
                claims.extend(extended.output_keys.iter().cloned());
                let dirtied = self.facts.mark_dirty(&publisher, &claims);
                self.deps.replace_outputs(publisher.clone(), claims);
                changed.extend(extended.changed);
                pending_changes.extend(dirtied);
            }
        }

        for publisher in &unreached {
            let previous_keys = self.deps.output_keys(publisher);
            if waiting {
                pending_changes.extend(self.facts.mark_dirty(publisher, &previous_keys));
                continue;
            }
            let retracted =
                self.facts
                    .replace_outputs_after_run(publisher, &previous_keys, Vec::new(), Vec::new(), false, true);
            changed.extend(retracted.changed);
            self.deps.forget(publisher);
            self.rebased.remove(publisher);
            self.read_finality.remove(publisher);
        }

        let owned = if waiting {
            previously_owned
                .iter()
                .cloned()
                .chain(listed.iter().cloned())
                .collect::<OrderedSet<P>>()
        } else {
            listed
        };
        self.deps.replace_derivations(job.clone(), owned);

        pending_changes.extend(changed.iter().cloned());
        self.propagate_quiet_flips(&touched, quiet_before, &mut pending_changes, ctx);
        let (wakes, movements) = self.dispatch_changes(pending_changes, external, ctx);
        AppliedStep {
            changed,
            movements,
            wakes,
            blocked,
        }
    }

    /// Drains a wave of fact changes into wakes. An ascent re-runs readers,
    /// who join. A ground shift additionally rebases them: a retraction, a
    /// replacing fact's content change, or any change concluded by a rebased
    /// publisher can invalidate what readers derived.
    ///
    /// A readiness-only change propagates finality through all concluded readers,
    /// but only a `Settled` waiter can be satisfied by its false-to-true edge.
    /// Sending it to subscribers would recompute a formula whose input content
    /// never moved, which is the one-line "fix" fz-kdt.44 measured and
    /// rejected.
    fn dispatch_changes<Ctx>(
        &mut self,
        mut pending_changes: Vec<FactChange<F>>,
        external: &impl ExternalDependencyStates<F>,
        ctx: &Ctx,
    ) -> DispatchedWave<P::Run, F>
    where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
        F: SemanticOrd<Ctx>,
    {
        let mut wakes = Vec::new();
        let mut moved_keys = HashSet::new();
        while !pending_changes.is_empty() {
            // Dependents can append more movements while this wave drains, so
            // select the typed minimum before each pop. Equal-key movements
            // retain the prior newest-first behavior of stable descending
            // sort followed by pop, without sorting and moving the whole
            // growing frontier on every iteration.
            let change =
                take_next_fact_change(&mut pending_changes, ctx).expect("the non-empty change wave has a next fact");
            if let Some(content_movement) = change.content_movement() {
                let shift = content_movement == ContentMovement::Shift;
                self.enqueue_dependents(
                    FactUse::current(change.key.clone()),
                    shift,
                    &mut pending_changes,
                    &mut wakes,
                    external,
                    ctx,
                );
                self.enqueue_dependents(
                    FactUse::settled(change.key.clone()),
                    shift,
                    &mut pending_changes,
                    &mut wakes,
                    external,
                    ctx,
                );
            } else {
                // A cumulative fact's appearance at bottom moves no content,
                // but it SATISFIES a `Current` wait (presence is the wait's
                // whole question). Waiters only: subscribers read the value,
                // and the value they would re-read is the same nothing.
                if change.old_revision.is_none() && change.new_revision.is_some() {
                    self.wake_satisfied_waiters(
                        FactUse::current(change.key.clone()),
                        false,
                        &mut pending_changes,
                        &mut wakes,
                        external,
                        ctx,
                    );
                }
                if change.readiness_changed() && change.new_settled {
                    self.wake_satisfied_waiters(
                        FactUse::settled(change.key.clone()),
                        false,
                        &mut pending_changes,
                        &mut wakes,
                        external,
                        ctx,
                    );
                }
            }
            moved_keys.insert(change.key);
        }
        let mut movements = moved_keys
            .into_iter()
            .map(|key| FactMovement {
                state: self.dependency_state(&key, external),
                key,
            })
            .collect::<Vec<_>>();
        movements.sort_by(|left, right| left.key.semantic_cmp(&right.key, ctx));
        (wakes, movements)
    }

    /// The drain arbiter.
    ///
    /// Counting alone can never finalize a CYCLE. Take `A <-> B`, each fact
    /// published by a job that reads the other: once both publishers are
    /// clean, A's count still holds B and B's count still holds A, and no
    /// local rule can lower either. The counts are correct — the fixed point
    /// they describe is simply wrong once nothing is left to run.
    ///
    /// So at a drain, and only at a drain, the agenda itself decides. With no
    /// runnable job, the only publisher that could still move a fact is one
    /// paused on a wait. Waking it later dirties its claims and
    /// unfinalizes its readers through the ordinary path, so a fact is
    /// certified only once the walk of its transitive read ground finds no
    /// dirty publisher and no unsettled external product beneath it; every
    /// unquiet fact that walk visited is certified along with it. The
    /// transitive rule is what holds DURING the ascent; the drain is where it
    /// is discharged.
    ///
    /// That makes drain finality optimistic in precisely the way settledness
    /// has always been optimistic: a waiter woken here may publish something
    /// that re-moves the cone, and its readers re-wake through the normal
    /// movement path and re-run. Arbitration starts only from the requested
    /// facts, and each certified publisher retains its real read count under
    /// a quiescence certificate and finalizes its own claims together.
    /// Ordinary quiet propagation carries that ownership decision downstream;
    /// independent publishers stay untouched.
    pub(crate) fn settle_quiescent_ordered_with_external<Ctx>(
        &mut self,
        facts: &[F],
        external: &impl ExternalDependencyStates<F>,
        ctx: &Ctx,
    ) -> AppliedStep<P::Run, F>
    where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
        F: SemanticOrd<Ctx>,
    {
        let mut changes = Vec::new();
        if self.agenda.is_empty() {
            for fact in facts {
                self.settle_quiescent_fact(fact, &mut changes, external, ctx);
            }
        }
        let (wakes, movements) = self.dispatch_changes(changes.clone(), external, ctx);
        AppliedStep {
            changed: changes,
            movements,
            wakes,
            blocked: Vec::new(),
        }
    }

    fn settle_quiescent_fact<Ctx>(
        &mut self,
        fact: &F,
        changes: &mut Vec<FactChange<F>>,
        external: &impl ExternalDependencyStates<F>,
        ctx: &Ctx,
    ) where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
    {
        if self.facts.is_quiet(fact) || !self.facts.is_locally_settled(fact) {
            return;
        }
        let Some(cone) = self.quiescent_cone(fact, external) else {
            return;
        };
        // The walk proved every unquiet fact in the cone final by the same
        // argument, so certify them all: leaving the members unfinal would
        // re-arbitrate each at a later drain and wake their readers again.
        let mut publishers = cone
            .iter()
            .flat_map(|key| self.facts.publishers(key))
            .cloned()
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        publishers.sort_by(|left, right| left.semantic_cmp(right, ctx));
        for publisher in publishers {
            let keys = self.deps.output_keys(&publisher);
            let quiet_before = self.quiet_snapshot(&keys);
            if let Some(state) = self.read_finality.get_mut(&publisher) {
                *state = ReadFinality::Quiescent(state.count());
            }
            for key in &keys {
                if let Some(change) = self.facts.set_publisher_unfinal(key, &publisher, false) {
                    changes.push(change);
                }
            }
            self.propagate_quiet_flips(&keys, quiet_before, changes, ctx);
        }
    }

    /// The unquiet facts beneath this one, when nothing there can still move;
    /// `None` when something can. The walk follows every publisher's reads
    /// down to quiet ground and stops on a dirty publisher or an unsettled
    /// external product. A dirty publisher is a job that has not re-run since
    /// its own ground moved, or one still waiting for a fact nobody has
    /// produced yet; either way the facts above it are clean only because
    /// that run has not happened. A quiet fact ends the walk: nothing beneath
    /// a quiet fact moves. A cycle of clean publishers is therefore final, and
    /// a partial accumulation over an undiscovered layer is not.
    fn quiescent_cone(&self, fact: &F, external: &impl ExternalDependencyStates<F>) -> Option<Vec<F>> {
        let mut pending = vec![fact];
        let mut seen = HashSet::new();
        let mut cone = Vec::new();
        while let Some(key) = pending.pop() {
            if !seen.insert(key) {
                continue;
            }
            if let Some(state) = external.external_state(key) {
                if !state.settled {
                    return None;
                }
                continue;
            }
            if self.facts.is_quiet(key) {
                continue;
            }
            if !self.facts.is_locally_settled(key) {
                return None;
            }
            cone.push(key.clone());
            for publisher in self.facts.publishers(key) {
                if let Some(reads) = self.deps.reads(publisher) {
                    pending.extend(reads.iter().map(FactUse::fact));
                }
            }
        }
        Some(cone)
    }

    /// Whether something this job read can still move.
    fn is_unfinal(&self, publisher: &P) -> bool {
        self.read_finality
            .get(publisher)
            .is_some_and(|state| state.is_pending())
    }

    fn count_unfinal_reads(&self, publisher: &P, external: &impl ExternalDependencyStates<F>) -> usize {
        self.deps.reads(publisher).map_or(0, |reads| {
            reads
                .iter()
                .filter(|read| !self.dependency_is_quiet(read.fact(), external))
                .count()
        })
    }

    fn set_unfinal_reads(&mut self, publisher: &P, count: usize) {
        self.set_read_finality(publisher, ReadFinality::Pending(count));
    }

    fn set_read_finality(&mut self, publisher: &P, state: ReadFinality) {
        if state.count() == 0 {
            self.read_finality.remove(publisher);
        } else {
            self.read_finality.insert(publisher.clone(), state);
        }
    }

    fn quiet_snapshot(&self, keys: &OrderedSet<F>) -> Vec<bool> {
        keys.iter().map(|key| self.facts.is_quiet(key)).collect()
    }

    /// Recomputes one job's unfinal-read count from its current read
    /// set and carries a flip into every fact THAT job publishes. The
    /// wholesale recount is what makes read replacement safe: the count is a
    /// function of the read set, so a replaced, unioned, or emptied read set
    /// cannot leave it stale.
    fn refresh_finality<Ctx>(
        &mut self,
        publisher: &P,
        changes: &mut Vec<FactChange<F>>,
        external: &impl ExternalDependencyStates<F>,
        ctx: &Ctx,
    ) where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
    {
        let count = self.count_unfinal_reads(publisher, external);
        let was_unfinal = self.is_unfinal(publisher);
        self.set_unfinal_reads(publisher, count);
        if (count > 0) == was_unfinal {
            return;
        }
        let keys = self.deps.output_keys(publisher);
        let quiet_before = self.quiet_snapshot(&keys);
        for key in &keys {
            if let Some(change) = self.facts.set_publisher_unfinal(key, publisher, count > 0) {
                changes.push(change);
            }
        }
        self.propagate_quiet_flips(&keys, quiet_before, changes, ctx);
    }

    /// Turns a before/after quiet snapshot of `keys` into the two sign-uniform
    /// waves it implies.
    fn propagate_quiet_flips<Ctx>(
        &mut self,
        keys: &OrderedSet<F>,
        quiet_before: Vec<bool>,
        changes: &mut Vec<FactChange<F>>,
        ctx: &Ctx,
    ) where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
    {
        let mut became_quiet = Vec::new();
        let mut became_unquiet = Vec::new();
        for (key, was_quiet) in keys.iter().zip(quiet_before) {
            match (was_quiet, self.facts.is_quiet(key)) {
                (false, true) => became_quiet.push(key.clone()),
                (true, false) => became_unquiet.push(key.clone()),
                _ => {}
            }
        }
        self.propagate_quiet_wave(became_unquiet, false, changes, ctx);
        self.propagate_quiet_wave(became_quiet, true, changes, ctx);
    }

    /// Edge-triggered transitive finality. `seeds` have just flipped quiet
    /// state; every JOB reading one of them gains or loses an unfinal
    /// read, and a job that flips takes its co-outputs with it.
    /// A job reading both `Current(f)` and `Settled(f)` is adjusted twice,
    /// matching the fact uses counted by `count_unfinal_reads`.
    ///
    /// The wave is sign-uniform — a fact that just went unquiet can only make
    /// readers unquiet — so every count moves one way, every node flips at
    /// most once, and the walk is exactly the affected cone. There is no
    /// sweep, no inventory and no epoch: the only nodes visited are the ones
    /// whose answer changed.
    fn propagate_quiet_wave<Ctx>(
        &mut self,
        seeds: Vec<F>,
        became_quiet: bool,
        changes: &mut Vec<FactChange<F>>,
        ctx: &Ctx,
    ) where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
    {
        let mut frontier = seeds;
        while let Some(fact) = frontier.pop() {
            for reader in self.deps.readers_of(&fact, ctx) {
                let was_unfinal = self.is_unfinal(&reader);
                let previous = self
                    .read_finality
                    .get(&reader)
                    .copied()
                    .unwrap_or(ReadFinality::Pending(0));
                self.set_read_finality(&reader, previous.after_edge(became_quiet));
                let is_unfinal = self.is_unfinal(&reader);
                if is_unfinal == was_unfinal {
                    continue;
                }
                let keys = self.deps.output_keys(&reader);
                for key in &keys {
                    let was_quiet = self.facts.is_quiet(key);
                    if let Some(change) = self.facts.set_publisher_unfinal(key, &reader, is_unfinal) {
                        changes.push(change);
                    }
                    if self.facts.is_quiet(key) != was_quiet {
                        frontier.push(key.clone());
                    }
                }
            }
        }
    }

    /// The changed-revision wake path: a subscriber's fact use changed, so it
    /// re-enters the agenda under `WorkStartReason::ChangedRevisionWake` --
    /// the one work-start reason that is never passed in by a caller, since
    /// it names the wake mechanism itself, not an external demand. Records
    /// one `Wake` attributing `job` to `cause`, whatever the disposition —
    /// there is no dedupe here, since a distinct cause is a distinct
    /// attribution even when it lands on an already-pending job.
    fn enqueue_step(&mut self, job: P::Run, cause: &FactUse<F>, shift: bool, wakes: &mut Vec<Wake<P::Run, F>>) {
        let disposition = if self.agenda.enqueue(job.clone()) {
            *self
                .work_starts
                .entry(WorkStartReason::ChangedRevisionWake)
                .or_insert(0) += 1;
            WakeDisposition::Enqueued
        } else {
            WakeDisposition::Coalesced
        };
        wakes.push(Wake {
            cause: cause.clone(),
            job,
            disposition,
            shift,
        });
    }

    fn enqueue_dependents<Ctx>(
        &mut self,
        fact_use: FactUse<F>,
        shift: bool,
        pending_changes: &mut Vec<FactChange<F>>,
        wakes: &mut Vec<Wake<P::Run, F>>,
        external: &impl ExternalDependencyStates<F>,
        ctx: &Ctx,
    ) where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
    {
        // A movement reopens exactly the answers that read it, and wakes the
        // job that gives them once: the run is what re-derives them, so one
        // movement is one work start. An answer of the same job that did not
        // read this fact is not in question -- re-deriving it will say what it
        // already says -- and dirtying it anyway would reopen, on every wake,
        // the very thing a concluded answer is for.
        let mut woken = OrderedSet::default();
        for publisher in self.deps.subscribers(&fact_use, ctx) {
            if shift {
                self.rebased.insert(publisher.clone());
            }
            self.dirty_claims(&publisher, pending_changes, ctx);
            woken.insert(publisher.run().clone());
        }
        for job in woken.iter().cloned().collect::<Vec<_>>() {
            self.enqueue_step(job, &fact_use, shift, wakes);
        }

        self.wake_satisfied_waiters(fact_use, shift, pending_changes, wakes, external, ctx);
    }

    /// The waiter half of a movement's dispatch, on its own so a PRESENCE
    /// appearance can reach it without the subscriber half: `satisfies` and
    /// the wake path must never disagree. A `Current` wait is satisfied by
    /// presence (`revision.is_some()`), so a cumulative fact appearing at
    /// bottom satisfies it while moving no content -- the waiter must still
    /// run, or it is satisfied-and-asleep forever (fz-kdt.84 review).
    fn wake_satisfied_waiters<Ctx>(
        &mut self,
        fact_use: FactUse<F>,
        shift: bool,
        pending_changes: &mut Vec<FactChange<F>>,
        wakes: &mut Vec<Wake<P::Run, F>>,
        external: &impl ExternalDependencyStates<F>,
        ctx: &Ctx,
    ) where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
    {
        for job in self.deps.waiters(&fact_use, ctx) {
            let waits = self.deps.waits_for(&job);
            if !waits.iter().all(|wait| self.dependency_satisfies(wait, external)) {
                continue;
            }
            // A standing wait belongs to the job's own answer, so satisfying
            // it reopens that answer and no other.
            let own = P::of_run(&job);
            self.dirty_claims(&own, pending_changes, ctx);
            if shift {
                self.rebased.insert(own);
            }
            self.enqueue_step(job, &fact_use, shift, wakes);
        }
    }

    /// Marks every fact this answer claims dirty and carries the resulting
    /// unquiet flips down the cone. A reopened answer stops being final for
    /// everyone downstream of it, not just for its own readers.
    fn dirty_claims<Ctx>(&mut self, publisher: &P, pending_changes: &mut Vec<FactChange<F>>, ctx: &Ctx)
    where
        P: SemanticOrd<Ctx>,
        P::Run: SemanticOrd<Ctx>,
    {
        let keys = self.deps.output_keys(publisher);
        let quiet_before = self.quiet_snapshot(&keys);
        let dirtied = self.facts.mark_dirty(publisher, &keys);
        pending_changes.extend(dirtied);
        self.propagate_quiet_flips(&keys, quiet_before, pending_changes, ctx);
    }
}
