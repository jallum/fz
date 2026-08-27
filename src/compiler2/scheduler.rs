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

        let previous_output_keys = self.deps.output_keys(job);
        let mut dirtied = Vec::new();
        let replaced = if waiting {
            let extended = self.facts.extend_outputs(job, outputs, changed);
            let mut claims = previous_output_keys;
            claims.extend(extended.output_keys.iter().cloned());
            dirtied = self.facts.mark_dirty(job, &claims);
            self.deps.replace_outputs(job.clone(), claims);
            extended
        } else {
            let concluded = self.facts.replace_outputs(job, &previous_output_keys, outputs, changed);
            self.deps.replace_outputs(job.clone(), concluded.output_keys.clone());
            concluded
        };

        let mut wakes = Vec::new();
        let mut pending_changes = replaced.changed.clone();
        pending_changes.extend(dirtied);
        let mut moved_keys = HashSet::new();
        while let Some(change) = pending_changes.pop() {
            if change.content_changed() {
                // Classify the wave. An ascent re-runs readers, who join. A
                // ground shift additionally rebases them: a retraction, a
                // replacing fact's content change, or any change concluded by
                // a rebased publisher can invalidate what readers derived.
                // First appearance is news, not a shift — nothing read it.
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
        AppliedStep {
            outputs: replaced.output_keys,
            changed: replaced.changed,
            movements,
            wakes,
            blocked,
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
            let dirtied = self.facts.mark_dirty(&job, &self.deps.output_keys(&job));
            pending_changes.extend(dirtied);
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
            let dirtied = self.facts.mark_dirty(&job, &self.deps.output_keys(&job));
            pending_changes.extend(dirtied);
            if shift {
                self.rebased.insert(job.clone());
            }
            self.enqueue_step(job, &fact_use, shift, wakes);
        }
    }
}
