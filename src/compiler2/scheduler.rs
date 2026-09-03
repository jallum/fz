use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use super::agenda::Agenda;
use super::deps::{DependencyIndex, UnresolvedWait};
use super::facts::{ClaimShape, DerivationId, FactChange, FactMovement, FactReplace, FactTable, FactUse, Publisher};
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
/// whole-fact-table scans (`Scheduler::fact_keys`) were taken. Carried out of
/// the scheduler as a single value so the pull session can record and emit the
/// full per-reason breakdown (`pull.session.finished`) without reaching back
/// into the world.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct WorkStartTally {
    pub ignition: u64,
    pub changed_revision_wake: u64,
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
    pub changed: Vec<FactChange<F>>,
    pub movements: Vec<FactMovement<F>>,
    /// Every wake this completion caused, in wake order, each carrying its
    /// own cause and disposition (see `Wake`).
    pub wakes: Vec<Wake<J, F>>,
    pub blocked: Vec<FactUse<F>>,
}

/// One answer a completing job reports: the reads it stands on, the facts it
/// claims, and which of those moved. This is the unit of publisher identity —
/// the engine keeps one claim set, one read set and one finality count per
/// `derivation`, never per job.
///
/// `concluded` says whether the run REACHED this answer. A derivation that
/// concluded replaces (its reads swap subscriptions, its unlisted keys
/// retract, its claims are clean); one that did not extends (its reads union,
/// nothing retracts, its claims stay dirty). A job that returns no waits
/// concluded every derivation it reports -- `complete` enforces it. A blocked job may
/// have reached some of its answers before the block: those are clean, and the
/// ones it never reached stay dirty.
#[derive(Debug, Clone)]
pub struct DerivationEffects<F> {
    pub derivation: DerivationId,
    pub reads: HashSet<FactUse<F>>,
    pub outputs: Vec<F>,
    pub changed: Vec<F>,
    pub concluded: bool,
}

impl<F> DerivationEffects<F> {
    /// The whole job as one answer — every job that does not name derivations.
    pub fn sole(reads: HashSet<FactUse<F>>, outputs: Vec<F>, changed: Vec<F>, concluded: bool) -> Self {
        Self {
            derivation: DerivationId::SOLE,
            reads,
            outputs,
            changed,
            concluded,
        }
    }
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
    facts: FactTable<Publisher<J>, F>,
    deps: DependencyIndex<J, F>,
    /// Jobs whose ground shifted: a fact they read changed in a way that can
    /// invalidate their claims. A rebased job's next conclusion replaces its
    /// cumulative store values instead of joining, and its content changes
    /// propagate as shifts in turn. Cleared on conclusion; kept while waiting.
    rebased: HashSet<J>,
    /// How many of each DERIVATION's recorded reads currently name a fact that
    /// is NOT quiet. Non-zero means that derivation cannot vouch for what it
    /// publishes: something it read can still move. This is the reader half of
    /// transitive finality; the fact half is `FactSlot::unfinal_publishers`,
    /// keyed by the same publisher identity. An absent entry means zero.
    ///
    /// Keyed per derivation, not per job (fz-kdt.13.1): a job whose OTHER
    /// answer stands on moving ground has not made THIS answer provisional.
    unfinal_reads: HashMap<Publisher<J>, usize>,
    /// Work-start attribution tally: how many jobs actually entered the
    /// agenda (deduped coalescing does not count) under each
    /// `WorkStartReason`. Observation-only — see `WorkStartReason`.
    work_starts: HashMap<WorkStartReason, u64>,
    /// Test-only identity trace behind the aggregate tally. Production pays no
    /// storage or clone cost; regression tests use it to reject compensating
    /// per-reason counts that started the wrong jobs.
    #[cfg(test)]
    work_start_trace: Vec<(J, WorkStartReason)>,
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
            #[cfg(test)]
            work_start_trace: Vec::new(),
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
            activation_frontier: count(WorkStartReason::ActivationFrontier),
            blocked_waiter_expansion: count(WorkStartReason::BlockedWaiterExpansion),
            unclassified: count(WorkStartReason::Unclassified),
            root_scans: self.root_scans,
        }
    }

    #[cfg(test)]
    pub fn work_start_trace(&self) -> &[(J, WorkStartReason)] {
        &self.work_start_trace
    }

    /// Whether `job`'s ground has shifted since it last concluded.
    pub fn rebased(&self, job: &J) -> bool {
        self.rebased.contains(job)
    }

    pub fn pending_jobs(&self) -> usize {
        self.agenda.len()
    }

    pub fn facts(&self) -> &FactTable<Publisher<J>, F> {
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

    /// Every key the job claims, across all its derivations, in roster then
    /// emission order.
    pub fn output_keys(&self, job: &J) -> OrderedSet<F> {
        self.deps.job_output_keys(job)
    }

    /// Every fact use the job read, across all its derivations. The job is what
    /// ran, so this is the projection observation asks for.
    pub fn reads(&self, job: &J) -> HashSet<FactUse<F>> {
        self.deps.job_reads(job)
    }

    /// How many of the job's recorded reads name a fact that can still move,
    /// summed over its derivations. Zero means every answer the job holds
    /// stands on quiet ground — the job-level question a readiness-ordered pop
    /// would ask. Per-derivation finality is what the ledger acts on; this is
    /// the fold of it.
    /// Step 4 of fz-kdt.13's strategy (finality-first pop) is CONDITIONAL on
    /// re-measurement; this job-level fold is its accessor and has no
    /// production caller until that step is taken. Drop it if step 4 is not.
    #[cfg(test)]
    pub fn unfinal_reads(&self, job: &J) -> usize {
        self.deps
            .publishers(job)
            .iter()
            .map(|publisher| self.unfinal_reads.get(publisher).copied().unwrap_or(0))
            .sum()
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

    /// Every standing wait, ordered by data — see `DependencyIndex::unresolved`.
    pub fn unresolved(&self) -> Vec<UnresolvedWait<J, F>>
    where
        F: Debug,
    {
        self.deps.unresolved()
    }

    /// Enqueues `job`, tallying the work-start under `reason`. Returns
    /// whether the job was newly enqueued (`false` means it was already
    /// pending and this call coalesced into it — not a new work start, so
    /// the tally does not count it).
    pub fn enqueue(&mut self, job: J, reason: WorkStartReason) -> bool {
        #[cfg(test)]
        let traced_job = job.clone();
        let started = self.agenda.enqueue(job);
        if started {
            *self.work_starts.entry(reason).or_insert(0) += 1;
            #[cfg(test)]
            self.work_start_trace.push((traced_job, reason));
        }
        started
    }

    pub fn pop(&mut self) -> Option<J> {
        self.agenda.pop()
    }

    /// Apply one job completion. A job runs WHOLE, so `waits` are the job's;
    /// its claims are its derivations'. Each derivation is applied in the order
    /// the job reported it, and the whole wave dispatches once at the end.
    ///
    /// The semantics bifurcate per derivation, on whether the run reached it:
    ///
    /// **Concluded** replaces — that derivation's reads swap subscriptions and
    /// its outputs replace its claims, so retraction-by-omission is available
    /// and final for the answer it owns.
    ///
    /// **Unreached** extends — its reads union into the standing
    /// subscriptions, listed outputs union into the standing claims, nothing
    /// retracts, and every claim it holds is marked dirty so an unreached
    /// answer never reads as settled. Pausing is not recanting.
    ///
    /// A job that returns no waits concluded every answer it reports, and the
    /// derivations it does NOT report are withdrawn whole: its silence about
    /// an answer it used to give is knowledge, exactly as its silence about a
    /// key is.
    pub fn complete(
        &mut self,
        job: &J,
        waits: HashSet<FactUse<F>>,
        derivations: Vec<DerivationEffects<F>>,
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
        self.deps.replace_waits(job.clone(), waits);

        // A job with no waits reached every answer it reports -- ENFORCED, not
        // assumed: an unreached derivation on a non-waiting completion would
        // leave dirty claims with no wait, no agenda entry, and no read edge
        // to ever wake the job, wedging every downstream reader unfinal
        // forever. Coercing here makes that state unrepresentable.
        let derivations = derivations
            .into_iter()
            .map(|mut effects| {
                effects.concluded |= !waiting;
                effects
            })
            .collect::<Vec<_>>();
        let reported = derivations
            .iter()
            .map(|derivation| derivation.derivation)
            .collect::<Vec<_>>();
        self.deps.register_derivations(job, &reported);

        let mut pending_changes = Vec::new();
        let mut changed = Vec::new();
        for derivation in derivations {
            let replaced = self.apply_derivation(job, derivation, &mut pending_changes);
            changed.extend(replaced.changed);
        }
        if !waiting {
            self.withdraw_unreported_derivations(job, &reported, &mut pending_changes);
        }

        let (wakes, movements) = self.dispatch_changes(pending_changes, was_rebased);
        AppliedStep {
            changed,
            movements,
            wakes,
            blocked,
        }
    }

    /// Applies one derivation's reads and claims, appending everything that
    /// moved to `pending_changes`. Returns what the fact table published for it.
    fn apply_derivation(
        &mut self,
        job: &J,
        effects: DerivationEffects<F>,
        pending_changes: &mut Vec<FactChange<F>>,
    ) -> FactReplace<F> {
        let publisher = Publisher::new(job.clone(), effects.derivation);
        if effects.concluded {
            self.deps.replace_reads(publisher.clone(), effects.reads);
        } else {
            self.deps.union_reads(publisher.clone(), effects.reads);
        }

        // This derivation's finality follows its NEW read set, and its standing
        // claims inherit it. Doing this before the outputs land is what lets
        // the publication below record the right finality for every key it
        // touches in one pass, with no repair afterwards.
        self.refresh_derivation_finality(&publisher, pending_changes);
        let unfinal = self.derivation_is_unfinal(&publisher);

        let previous_output_keys = self.deps.output_keys(&publisher);
        let touched = effects
            .outputs
            .iter()
            .cloned()
            .chain(previous_output_keys.iter().cloned())
            .collect::<OrderedSet<F>>();
        let quiet_before = self.quiet_snapshot(&touched);
        let mut dirtied = Vec::new();
        let replaced = if effects.concluded {
            let concluded = self.facts.replace_outputs(
                &publisher,
                &previous_output_keys,
                effects.outputs,
                effects.changed,
                unfinal,
            );
            self.deps.replace_outputs(publisher, concluded.output_keys.clone());
            concluded
        } else {
            let extended = self
                .facts
                .extend_outputs(&publisher, effects.outputs, effects.changed, unfinal);
            let mut claims = previous_output_keys;
            claims.extend(extended.output_keys.iter().cloned());
            dirtied = self.facts.mark_dirty(&publisher, &claims);
            self.deps.replace_outputs(publisher, claims);
            extended
        };

        pending_changes.extend(replaced.changed.iter().cloned());
        pending_changes.extend(dirtied);
        self.propagate_quiet_flips(&touched, quiet_before, pending_changes);
        replaced
    }

    /// Retraction-by-omission lifted to the derivation. A concluding job that
    /// no longer gives an answer it used to give retracts that answer whole:
    /// its claims go, its subscriptions go, and its readers hear it as an
    /// ordinary retraction. Only a CONCLUDING job may do this — a blocked one
    /// has not re-derived anything, so its unreached answers stand.
    /// Withdrawal carries no `changed` channel: a derivation owns only keys
    /// whose content is entirely its own contribution, so removing it can
    /// change no still-present multi-publisher fact. Key-granular retraction
    /// (`replace_outputs` with `changed`) remains the tool when a publisher
    /// must mark a co-published fact moved while letting go.
    fn withdraw_unreported_derivations(
        &mut self,
        job: &J,
        reported: &[DerivationId],
        pending_changes: &mut Vec<FactChange<F>>,
    ) {
        for publisher in self.deps.retain_derivations(job, reported) {
            let previous_output_keys = self.deps.output_keys(&publisher);
            let quiet_before = self.quiet_snapshot(&previous_output_keys);
            let retracted =
                self.facts
                    .replace_outputs(&publisher, &previous_output_keys, Vec::new(), Vec::new(), false);
            self.deps.replace_outputs(publisher.clone(), OrderedSet::default());
            self.deps.forget_reads(&publisher);
            self.unfinal_reads.remove(&publisher);
            pending_changes.extend(retracted.changed);
            self.propagate_quiet_flips(&previous_output_keys, quiet_before, pending_changes);
        }
    }

    /// Drains a wave of fact changes into wakes. An ascent re-runs readers,
    /// who join. A ground shift additionally rebases them: a retraction, a
    /// replacing fact's content change, or any change concluded by a rebased
    /// publisher can invalidate what readers derived.
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
                // An APPEARANCE is an ascent, never a shift: there was no
                // earlier answer for the new one to have refuted. A cumulative
                // fact's climb off bottom (0 -> 1) is an ordinary bump, so a
                // REBASED publisher's first real evidence propagates as a shift
                // -- the conservative direction, and measured to add no shift
                // and no rebased completion on any target fixture (fz-kdt.84).
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
                    );
                }
                if change.readiness_changed() {
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

    /// Whether something this derivation read can still move.
    fn derivation_is_unfinal(&self, publisher: &Publisher<J>) -> bool {
        self.unfinal_reads.contains_key(publisher)
    }

    fn count_unfinal_reads(&self, publisher: &Publisher<J>) -> usize {
        self.deps.reads(publisher).map_or(0, |reads| {
            reads.iter().filter(|read| !self.facts.is_quiet(read.fact())).count()
        })
    }

    fn set_unfinal_reads(&mut self, publisher: &Publisher<J>, count: usize) {
        if count == 0 {
            self.unfinal_reads.remove(publisher);
        } else {
            self.unfinal_reads.insert(publisher.clone(), count);
        }
    }

    /// Every derivation subscribed to `fact`, once per fact use it holds. The
    /// multiplicity is deliberate: `count_unfinal_reads` counts fact USES, so a
    /// derivation reading both `Current(f)` and `Settled(f)` must be adjusted
    /// twice when `f` flips, or the count and the recount disagree.
    fn readers_of(&self, fact: &F) -> Vec<Publisher<J>> {
        let mut readers = self.deps.subscribers(&FactUse::current(fact.clone()));
        readers.extend(self.deps.subscribers(&FactUse::settled(fact.clone())));
        readers.extend(self.deps.subscribers(&FactUse::settled_presence(fact.clone())));
        readers
    }

    fn quiet_snapshot(&self, keys: &OrderedSet<F>) -> Vec<bool> {
        keys.iter().map(|key| self.facts.is_quiet(key)).collect()
    }

    /// Recomputes one derivation's unfinal-read count from its current read
    /// set and carries a flip into every fact THAT derivation publishes. The
    /// wholesale recount is what makes read replacement safe: the count is a
    /// function of the read set, so a replaced, unioned, or emptied read set
    /// cannot leave it stale.
    fn refresh_derivation_finality(&mut self, publisher: &Publisher<J>, changes: &mut Vec<FactChange<F>>) {
        let count = self.count_unfinal_reads(publisher);
        let was_unfinal = self.derivation_is_unfinal(publisher);
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
    /// state; every DERIVATION reading one of them gains or loses an unfinal
    /// read, and a derivation that flips takes the facts it publishes with it —
    /// its siblings, which read other ground, are untouched.
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
                let was_unfinal = self.derivation_is_unfinal(&reader);
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
    /// the one work-start reason assigned by the wake mechanism itself rather
    /// than an external demand caller. Records
    /// one `Wake` attributing `job` to `cause`, whatever the disposition —
    /// there is no dedupe here, since a distinct cause is a distinct
    /// attribution even when it lands on an already-pending job.
    fn enqueue_step(&mut self, job: J, cause: &FactUse<F>, shift: bool, wakes: &mut Vec<Wake<J, F>>) {
        let disposition = if self.enqueue(job.clone(), WorkStartReason::ChangedRevisionWake) {
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
        // Subscribers are DERIVATIONS: the answer that actually read this fact
        // is the answer this movement invalidates. An ASCENT dirties only that
        // one; its siblings stand on ground that did not move. A GROUND SHIFT
        // dirties the whole job, because rebasing selects replace-over-join
        // for every cumulative store the job's next conclusion writes — the
        // rebase flag is job-wide, so scoping the dirt beneath it would leave
        // an answer that narrows without ever having been marked provisional.
        // Rebase vetoes all scoping.
        //
        // The AGENDA entry is the job (a job runs whole), and one cause wakes
        // a job once however many of its derivations read the fact: the wake
        // stream attributes evaluations, and the job evaluates once.
        let mut woken = OrderedSet::default();
        for publisher in self.deps.subscribers(&fact_use) {
            if shift {
                self.dirty_job_claims(&publisher.job, pending_changes);
                self.rebased.insert(publisher.job.clone());
            } else {
                self.dirty_claims(&publisher, pending_changes);
            }
            if woken.insert(publisher.job.clone()) {
                self.enqueue_step(publisher.job, &fact_use, shift, wakes);
            }
        }

        self.wake_satisfied_waiters(fact_use, shift, pending_changes, wakes);
    }

    /// The waiter half of a movement's dispatch, on its own so a PRESENCE
    /// appearance can reach it without the subscriber half: `satisfies` and
    /// the wake path must never disagree. A `Current` wait is satisfied by
    /// presence (`revision.is_some()`), so a cumulative fact appearing at
    /// bottom satisfies it while moving no content -- the waiter must still
    /// run, or it is satisfied-and-asleep forever (fz-kdt.84 review).
    fn wake_satisfied_waiters(
        &mut self,
        fact_use: FactUse<F>,
        shift: bool,
        pending_changes: &mut Vec<FactChange<F>>,
        wakes: &mut Vec<Wake<J, F>>,
    ) {
        for job in self.deps.waiters(&fact_use) {
            let waits = self.deps.waits_for(&job);
            if !waits.iter().all(|wait| self.facts.satisfies(wait)) {
                continue;
            }
            // A wait is the JOB's — it carries no derivation attribution — so
            // satisfying it makes every answer the job holds provisional.
            self.dirty_job_claims(&job, pending_changes);
            if shift {
                self.rebased.insert(job.clone());
            }
            self.enqueue_step(job, &fact_use, shift, wakes);
        }
    }

    /// Marks every fact this DERIVATION claims dirty and carries the resulting
    /// unquiet flips down the cone. A woken publisher's claims stop being
    /// final for everyone downstream of them, not just for their own readers.
    fn dirty_claims(&mut self, publisher: &Publisher<J>, pending_changes: &mut Vec<FactChange<F>>) {
        let keys = self.deps.output_keys(publisher);
        let quiet_before = self.quiet_snapshot(&keys);
        let dirtied = self.facts.mark_dirty(publisher, &keys);
        pending_changes.extend(dirtied);
        self.propagate_quiet_flips(&keys, quiet_before, pending_changes);
    }

    /// Dirties every answer the job holds, in roster order. The conservative
    /// arm: used where the cause names no derivation (a satisfied wait) or
    /// where scoping would be unsound (a ground shift).
    fn dirty_job_claims(&mut self, job: &J, pending_changes: &mut Vec<FactChange<F>>) {
        for publisher in self.deps.publishers(job) {
            self.dirty_claims(&publisher, pending_changes);
        }
    }
}
