use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use super::agenda::Agenda;
use super::deps::{DependencyIndex, UnresolvedWait};
use super::facts::{ClaimShape, FactChange, FactMovement, FactTable, FactUse};
use super::ordered_set::OrderedSet;

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
///   subscription (read, wait, or settled-presence) just changed. This is
///   the core pull mechanism: readers wake because their ground moved, never
///   because a producer pushed them by name.
/// - `StandingRootFrontier`: `drive::demand_root_entry_analyses` expanding a
///   submitted root's standing entry-analysis demand through the
///   fact->producer map.
/// - `ActivationFrontier`: `drive::demand_activation_frontier_analyses`
///   expanding a discovered callee activation's standing analysis demand
///   through the same map.
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
    StandingRootFrontier,
    ActivationFrontier,
    BlockedWaiterExpansion,
    #[default]
    Unclassified,
}

/// A snapshot of a scheduler's cumulative work-start attribution: how many
/// jobs entered the agenda under each `WorkStartReason`, plus how many
/// whole-fact-table scans (`Scheduler::fact_keys`) were taken. Carried out of
/// the scheduler as a single value so the pull session can record and emit the
/// full per-reason breakdown (`pull.session.finished`) without reaching back
/// into the world.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct WorkStartTally {
    pub ignition: u64,
    pub changed_revision_wake: u64,
    pub standing_root_frontier: u64,
    pub activation_frontier: u64,
    pub blocked_waiter_expansion: u64,
    pub unclassified: u64,
    pub root_scans: u64,
}

impl WorkStartTally {
    /// Jobs that entered the agenda with no attributable sanctioned reason.
    /// Must stay zero on every sanctioned path: a reintroduced push (a
    /// follow-up-style enqueue that forgets to name a reason) lands here by
    /// construction, since `WorkStartReason` defaults to `Unclassified`.
    pub fn unsanctioned_work_starts(&self) -> u64 {
        self.unclassified
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
    pub outputs: OrderedSet<F>,
    pub changed: Vec<FactChange<F>>,
    pub movements: Vec<FactMovement<F>>,
    /// Every wake this completion caused, in wake order, each carrying its
    /// own cause and disposition (see `Wake`).
    pub wakes: Vec<Wake<J, F>>,
    pub blocked: Vec<FactUse<F>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FatalError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DriveOutcome<J, F> {
    Resolved,
    Unresolved { waits: Vec<UnresolvedWait<J, F>> },
    Fatal { job: J },
    TimedOut { jobs_ran: u64, pending_jobs: usize },
}

#[derive(Debug)]
pub struct Scheduler<J, F> {
    agenda: Agenda<J>,
    facts: FactTable<J, F>,
    deps: DependencyIndex<J, F>,
    /// Jobs whose ground shifted: a fact they read changed in a way that can
    /// invalidate their claims. A rebased job's next conclusion replaces its
    /// cumulative store values instead of joining, and its content changes
    /// propagate as shifts in turn. Cleared on conclusion; kept while waiting.
    rebased: HashSet<J>,
    /// How many of each job's recorded reads currently name a fact that is
    /// NOT quiet. Non-zero means the job cannot vouch for anything it
    /// publishes: something it read can still move. This is the reader half of
    /// transitive finality; the fact half is `FactSlot::unfinal_publishers`.
    /// An absent entry means zero.
    unfinal_reads: HashMap<J, usize>,
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
}

impl<J, F> Default for Scheduler<J, F>
where
    J: Clone + Debug + Eq + Hash,
    F: Clone + Eq + Hash + ClaimShape,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<J, F> Scheduler<J, F>
where
    J: Clone + Debug + Eq + Hash,
    F: Clone + Eq + Hash + ClaimShape,
{
    pub fn new() -> Self {
        Self {
            agenda: Agenda::new(),
            facts: FactTable::new(),
            deps: DependencyIndex::new(),
            rebased: HashSet::new(),
            unfinal_reads: HashMap::new(),
            work_starts: HashMap::new(),
            root_scans: 0,
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
            standing_root_frontier: count(WorkStartReason::StandingRootFrontier),
            activation_frontier: count(WorkStartReason::ActivationFrontier),
            blocked_waiter_expansion: count(WorkStartReason::BlockedWaiterExpansion),
            unclassified: count(WorkStartReason::Unclassified),
            root_scans: self.root_scans,
        }
    }

    /// Whether `job`'s ground has shifted since it last concluded.
    pub fn rebased(&self, job: &J) -> bool {
        self.rebased.contains(job)
    }

    pub fn pending_jobs(&self) -> usize {
        self.agenda.len()
    }

    pub fn facts(&self) -> &FactTable<J, F> {
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

    pub fn output_keys(&self, job: &J) -> OrderedSet<F> {
        self.deps.output_keys(job)
    }

    pub fn reads(&self, job: &J) -> Option<&HashSet<FactUse<F>>> {
        self.deps.reads(job)
    }

    /// Whether any job is currently blocked waiting on `fact` (in either its
    /// current or settled use). A pulled producer reads this to learn that a
    /// standing demand for the fact it mints exists, even before it can satisfy
    /// it — so when a later input finally lets it produce, the demand is honored
    /// rather than dropped (fz-f98.14.5).
    pub fn is_waited(&self, fact: &F) -> bool {
        !self.deps.waiters(&FactUse::current(fact.clone())).is_empty()
            || !self.deps.waiters(&FactUse::settled(fact.clone())).is_empty()
            || !self.deps.waiters(&FactUse::settled_presence(fact.clone())).is_empty()
    }

    pub fn has_unresolved(&self) -> bool {
        self.deps.has_unresolved()
    }

    /// Whether `job` has ever completed a run: it concluded (reads are
    /// recorded, even empty) or blocked (waits are standing). A job that has
    /// run is reachable by the graph's own wakes; a never-run job has no wake
    /// source, so only a fresh demand can start it.
    pub(crate) fn has_run(&self, job: &J) -> bool {
        self.deps.has_run(job)
    }

    /// Whether `job`'s most recent completion left waits standing.
    pub(crate) fn blocked(&self, job: &J) -> bool {
        self.deps.blocked(job)
    }

    pub fn waited_settled_facts(&self) -> Vec<F> {
        self.deps.waited_settled_facts()
    }

    pub fn unresolved(&self) -> Vec<UnresolvedWait<J, F>> {
        self.deps.unresolved()
    }

    /// Enqueues `job`, tallying the work-start under `reason`. Returns
    /// whether the job was newly enqueued (`false` means it was already
    /// pending and this call coalesced into it — not a new work start, so
    /// the tally does not count it).
    pub fn enqueue(&mut self, job: J, reason: WorkStartReason) -> bool {
        let started = self.agenda.enqueue(job);
        if started {
            *self.work_starts.entry(reason).or_insert(0) += 1;
        }
        started
    }

    pub fn pop(&mut self) -> Option<J> {
        self.agenda.pop()
    }

    /// Apply one job completion. The semantics bifurcate on `waits`:
    ///
    /// **Concluding** (waits empty) replaces — reads swap subscriptions,
    /// outputs replace claims (retraction-by-omission is available and final).
    ///
    /// **Waiting** (waits non-empty) extends — reads union into the standing
    /// subscriptions, listed outputs union into the standing claims, nothing
    /// retracts, and every claim the job holds is marked dirty so a blocked
    /// publisher's facts never read as settled. Pausing is not recanting.
    pub fn complete(
        &mut self,
        job: &J,
        reads: HashSet<FactUse<F>>,
        waits: HashSet<FactUse<F>>,
        outputs: Vec<F>,
        changed: Vec<F>,
    ) -> AppliedStep<J, F> {
        let waiting = !waits.is_empty();
        // A conclusion discharges the rebase; a blocked run has not yet
        // re-derived its claims from the shifted ground, so it stays pending.
        let was_rebased = if waiting {
            self.rebased.contains(job)
        } else {
            self.rebased.remove(job)
        };
        let blocked = waits.iter().cloned().collect();
        if waiting {
            self.deps.union_reads(job.clone(), reads);
        } else {
            self.deps.replace_reads(job.clone(), reads);
        }
        self.deps.replace_waits(job.clone(), waits);

        // The job's own finality follows its NEW read set, and its standing
        // claims inherit it. Doing this before the outputs land is what lets
        // the publication below record the right finality for every key it
        // touches in one pass, with no repair afterwards.
        let mut pending_changes = Vec::new();
        self.refresh_job_finality(job, &mut pending_changes);
        let job_unfinal = self.job_is_unfinal(job);

        let previous_output_keys = self.deps.output_keys(job);
        let touched = outputs
            .iter()
            .cloned()
            .chain(previous_output_keys.iter().cloned())
            .collect::<OrderedSet<F>>();
        let quiet_before = self.quiet_snapshot(&touched);
        let mut dirtied = Vec::new();
        let replaced = if waiting {
            let extended = self.facts.extend_outputs(job, outputs, changed, job_unfinal);
            let mut claims = previous_output_keys;
            claims.extend(extended.output_keys.iter().cloned());
            dirtied = self.facts.mark_dirty(job, &claims);
            self.deps.replace_outputs(job.clone(), claims);
            extended
        } else {
            let concluded = self
                .facts
                .replace_outputs(job, &previous_output_keys, outputs, changed, job_unfinal);
            self.deps.replace_outputs(job.clone(), concluded.output_keys.clone());
            concluded
        };

        pending_changes.extend(replaced.changed.iter().cloned());
        pending_changes.extend(dirtied);
        self.propagate_quiet_flips(&touched, quiet_before, &mut pending_changes);

        let (wakes, movements) = self.dispatch_changes(pending_changes, was_rebased);
        AppliedStep {
            outputs: replaced.output_keys,
            changed: replaced.changed,
            movements,
            wakes,
            blocked,
        }
    }

    /// Drains a wave of fact changes into wakes. An ascent re-runs readers,
    /// who join. A ground shift additionally rebases them: a retraction, a
    /// replacing fact's content change, or any change concluded by a rebased
    /// publisher can invalidate what readers derived. First appearance is
    /// news, not a shift — nothing read it.
    ///
    /// A readiness-only change (the finality flips this ticket added, and the
    /// dirty/clean flips that were always here) reaches `Settled` and
    /// `SettledPresence` subscribers ONLY. Sending it to `Current` subscribers
    /// would recompute a formula whose input content never moved, which is the
    /// one-line "fix" fz-kdt.44 measured and rejected.
    fn dispatch_changes(
        &mut self,
        mut pending_changes: Vec<FactChange<F>>,
        was_rebased: bool,
    ) -> (Vec<Wake<J, F>>, Vec<FactMovement<F>>) {
        let mut wakes = Vec::new();
        let mut moved_keys = HashSet::new();
        while let Some(change) = pending_changes.pop() {
            if change.content_changed() {
                let retraction = change.new_revision.is_none();
                let revision_bump = change.old_revision.is_some() && change.new_revision.is_some();
                let shift = retraction || (revision_bump && (was_rebased || !change.key.is_cumulative()));
                self.enqueue_dependents(
                    FactUse::current(change.key.clone()),
                    shift,
                    &mut pending_changes,
                    &mut wakes,
                );
                self.enqueue_dependents(
                    FactUse::settled(change.key.clone()),
                    shift,
                    &mut pending_changes,
                    &mut wakes,
                );
                if change.readiness_changed() {
                    self.enqueue_dependents(
                        FactUse::settled_presence(change.key.clone()),
                        false,
                        &mut pending_changes,
                        &mut wakes,
                    );
                }
            } else if change.readiness_changed() {
                self.enqueue_dependents(
                    FactUse::settled(change.key.clone()),
                    false,
                    &mut pending_changes,
                    &mut wakes,
                );
                self.enqueue_dependents(
                    FactUse::settled_presence(change.key.clone()),
                    false,
                    &mut pending_changes,
                    &mut wakes,
                );
            }
            moved_keys.insert(change.key);
        }
        let movements = moved_keys
            .into_iter()
            .map(|key| FactMovement {
                state: self.facts.state(&key),
                key,
            })
            .collect();
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
    /// pending job, the only publisher that could still move a fact is one
    /// paused on a wait, and a paused publisher cannot run until something
    /// wakes it — at which point its claims dirty and its readers unfinalize
    /// through the ordinary path. So `Settled(F)` at a drain is exactly
    /// `locally settled`, which is what it meant everywhere before this
    /// ticket. The transitive rule is what holds DURING the ascent; the drain
    /// is where it is discharged.
    ///
    /// That makes drain finality optimistic in precisely the way settledness
    /// has always been optimistic: a waiter woken here may publish something
    /// that re-moves the cone, and its readers re-wake through the normal
    /// movement path and re-run. Everything downstream follows from the one
    /// seed — one arbitrated fact discharges a whole quiesced cycle — so
    /// nothing is arbitrated that nobody asked about.
    pub fn settle_quiescent(&mut self, facts: &[F]) -> AppliedStep<J, F> {
        let mut changes = Vec::new();
        if self.agenda.is_empty() {
            for fact in facts {
                self.settle_quiescent_fact(fact, &mut changes);
            }
        }
        let (wakes, movements) = self.dispatch_changes(changes.clone(), false);
        AppliedStep {
            outputs: OrderedSet::default(),
            changed: changes,
            movements,
            wakes,
            blocked: Vec::new(),
        }
    }

    fn settle_quiescent_fact(&mut self, fact: &F, changes: &mut Vec<FactChange<F>>) {
        if self.facts.is_quiet(fact) || !self.facts.is_locally_settled(fact) {
            return;
        }
        if let Some(change) = self.facts.clear_unfinal_publishers(fact) {
            changes.push(change);
        }
        if self.facts.is_quiet(fact) {
            self.propagate_quiet_wave(vec![fact.clone()], true, changes);
        }
    }

    /// Whether something `job` read can still move.
    fn job_is_unfinal(&self, job: &J) -> bool {
        self.unfinal_reads.contains_key(job)
    }

    fn count_unfinal_reads(&self, job: &J) -> usize {
        self.deps.reads(job).map_or(0, |reads| {
            reads.iter().filter(|read| !self.facts.is_quiet(read.fact())).count()
        })
    }

    fn set_unfinal_reads(&mut self, job: &J, count: usize) {
        if count == 0 {
            self.unfinal_reads.remove(job);
        } else {
            self.unfinal_reads.insert(job.clone(), count);
        }
    }

    /// Every job subscribed to `fact`, once per fact use it holds. The
    /// multiplicity is deliberate: `count_unfinal_reads` counts fact USES, so
    /// a job reading both `Current(f)` and `Settled(f)` must be adjusted twice
    /// when `f` flips, or the count and the recount disagree.
    fn readers_of(&self, fact: &F) -> Vec<J> {
        let mut readers = self.deps.subscribers(&FactUse::current(fact.clone()));
        readers.extend(self.deps.subscribers(&FactUse::settled(fact.clone())));
        readers.extend(self.deps.subscribers(&FactUse::settled_presence(fact.clone())));
        readers
    }

    fn quiet_snapshot(&self, keys: &OrderedSet<F>) -> Vec<bool> {
        keys.iter().map(|key| self.facts.is_quiet(key)).collect()
    }

    /// Recomputes `job`'s unfinal-read count from its current read set and
    /// carries a flip into every fact it publishes. The wholesale recount is
    /// what makes read replacement safe: the count is a function of the read
    /// set, so a replaced, unioned, or emptied read set cannot leave it stale.
    fn refresh_job_finality(&mut self, job: &J, changes: &mut Vec<FactChange<F>>) {
        let count = self.count_unfinal_reads(job);
        let was_unfinal = self.job_is_unfinal(job);
        self.set_unfinal_reads(job, count);
        if (count > 0) == was_unfinal {
            return;
        }
        let keys = self.deps.output_keys(job);
        let quiet_before = self.quiet_snapshot(&keys);
        for key in &keys {
            if let Some(change) = self.facts.set_publisher_unfinal(key, job, count > 0) {
                changes.push(change);
            }
        }
        self.propagate_quiet_flips(&keys, quiet_before, changes);
    }

    /// Turns a before/after quiet snapshot of `keys` into the two sign-uniform
    /// waves it implies.
    fn propagate_quiet_flips(
        &mut self,
        keys: &OrderedSet<F>,
        quiet_before: Vec<bool>,
        changes: &mut Vec<FactChange<F>>,
    ) {
        let mut became_quiet = Vec::new();
        let mut became_unquiet = Vec::new();
        for (key, was_quiet) in keys.iter().zip(quiet_before) {
            match (was_quiet, self.facts.is_quiet(key)) {
                (false, true) => became_quiet.push(key.clone()),
                (true, false) => became_unquiet.push(key.clone()),
                _ => {}
            }
        }
        self.propagate_quiet_wave(became_unquiet, false, changes);
        self.propagate_quiet_wave(became_quiet, true, changes);
    }

    /// Edge-triggered transitive finality. `seeds` have just flipped quiet
    /// state; every job reading one of them gains or loses an unfinal read,
    /// and a job that flips takes the facts it publishes with it.
    ///
    /// The wave is sign-uniform — a fact that just went unquiet can only make
    /// readers unquiet — so every count moves one way, every node flips at
    /// most once, and the walk is exactly the affected cone. There is no
    /// sweep, no inventory and no epoch: the only nodes visited are the ones
    /// whose answer changed.
    fn propagate_quiet_wave(&mut self, seeds: Vec<F>, became_quiet: bool, changes: &mut Vec<FactChange<F>>) {
        let mut frontier = seeds;
        while let Some(fact) = frontier.pop() {
            for reader in self.readers_of(&fact) {
                let was_unfinal = self.job_is_unfinal(&reader);
                let previous = self.unfinal_reads.get(&reader).copied().unwrap_or(0);
                let count = if became_quiet {
                    previous.saturating_sub(1)
                } else {
                    previous + 1
                };
                self.set_unfinal_reads(&reader, count);
                if (count > 0) == was_unfinal {
                    continue;
                }
                let keys = self.deps.output_keys(&reader);
                for key in &keys {
                    let was_quiet = self.facts.is_quiet(key);
                    if let Some(change) = self.facts.set_publisher_unfinal(key, &reader, count > 0) {
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
    fn enqueue_step(&mut self, job: J, cause: &FactUse<F>, shift: bool, wakes: &mut Vec<Wake<J, F>>) {
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

    fn enqueue_dependents(
        &mut self,
        fact_use: FactUse<F>,
        shift: bool,
        pending_changes: &mut Vec<FactChange<F>>,
        wakes: &mut Vec<Wake<J, F>>,
    ) {
        for job in self.deps.subscribers(&fact_use) {
            self.dirty_claims(&job, pending_changes);
            if shift {
                self.rebased.insert(job.clone());
            }
            self.enqueue_step(job, &fact_use, shift, wakes);
        }

        for job in self.deps.waiters(&fact_use) {
            let waits = self.deps.waits_for(&job);
            if !waits.iter().all(|wait| self.facts.satisfies(wait)) {
                continue;
            }
            self.dirty_claims(&job, pending_changes);
            if shift {
                self.rebased.insert(job.clone());
            }
            self.enqueue_step(job, &fact_use, shift, wakes);
        }
    }

    /// Marks every fact `job` claims dirty and carries the resulting
    /// unquiet flips down the cone. A woken publisher's claims stop being
    /// final for everyone downstream of them, not just for their own readers.
    fn dirty_claims(&mut self, job: &J, pending_changes: &mut Vec<FactChange<F>>) {
        let keys = self.deps.output_keys(job);
        let quiet_before = self.quiet_snapshot(&keys);
        let dirtied = self.facts.mark_dirty(job, &keys);
        pending_changes.extend(dirtied);
        self.propagate_quiet_flips(&keys, quiet_before, pending_changes);
    }
}
