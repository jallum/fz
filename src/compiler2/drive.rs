//! Work loop and shared work vocabulary.
//!
//! This module owns the scheduler-facing shapes: job ids, fact ids, job
//! effects, and the drive loop. Concrete job implementations live under
//! `compiler2::jobs`.

use std::time::{Duration, Instant};

use crate::telemetry::{TelemetryExt, opaque_debug};
use crate::{measurements, metadata};

use super::code::CodeId;
use super::facts::{ClaimShape, FactUse};
use super::identity::{ActivationKey, ExecutableKey, FunctionId, ModuleId, RootId, TypeName};
use super::scheduler::{DriveOutcome, Scheduler};
use super::semantic::CallSiteKey;
use super::world::World;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Job {
    IndexCode(CodeId),
    ScopeCode(CodeId),
    DefineModule(ModuleId),
    DefineModuleInterface(ModuleId),
    PublishFunctionSource(FunctionId),
    ExpandFunctionSource(FunctionId),
    DefineFunction(FunctionId),
    DeriveTypeDef(TypeName),
    DeriveFunctionContract(FunctionId),
    LowerFunction(FunctionId),
    ReifyGuardDispatch(FunctionId),
    PlanEntryDispatch(FunctionId),
    BuildMacroExecutable(FunctionId),
    DeriveRecursive(FunctionId),
    DeriveDispatchMask(FunctionId),
    SeedRoot(RootId),
    SeedActivation(ActivationKey),
    AnalyzeActivation(ActivationKey),
    BuildBackendProduct(RootId),
    LowerNativeProgram(RootId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FactKey {
    CodeIndexed(CodeId),
    CodeScoped(CodeId),
    ModuleIndexed(ModuleId),
    ModuleDefined(ModuleId),
    ModuleInterface(ModuleId),
    FunctionSource(FunctionId),
    ExpandedFunctionSource(FunctionId),
    TypeDefined(TypeName),
    ProtocolDispatch(ModuleId),
    ProtocolImplProviders(ModuleId),
    FunctionDefined(FunctionId),
    FunctionContract(FunctionId),
    LoweredBody(FunctionId),
    GuardDispatch(FunctionId),
    EntryDispatch(FunctionId),
    MacroExecutable(FunctionId),
    Recursive(FunctionId),
    DispatchMask(FunctionId),
    RootEntry(RootId),
    Activation(ActivationKey),
    ActivationInputs(ActivationKey),
    ActivationAnalyzed(ActivationKey),
    ReturnType(ActivationKey),
    CallSiteTargets(CallSiteKey),
    CallSiteSummary(CallSiteKey),
    Executable(ExecutableKey),
    BackendProgram(RootId),
    NativeProgram(RootId),
}

impl ClaimShape for FactKey {
    /// The fixpoint-evidence facts whose stores maintain a monotone join: an
    /// activation's return ascends by union (`ActivationMap::define_return`), and
    /// its body-input evidence ascends by the cross-publisher widen
    /// (`ActivationInputMap`). Every other fact's content overwrites.
    fn is_cumulative(&self) -> bool {
        matches!(self, FactKey::ReturnType(_) | FactKey::ActivationInputs(_))
    }
}

pub type WorkGraph = Scheduler<Job, FactKey>;

#[derive(Debug, Clone, Default)]
pub(crate) struct JobEffects {
    pub(crate) reads: Vec<FactUse<FactKey>>,
    pub(crate) waits: Vec<FactUse<FactKey>>,
    pub(crate) outputs: Vec<FactKey>,
    pub(crate) changed: Vec<FactKey>,
    pub(crate) activation_input_contributions: Vec<(ActivationKey, Vec<super::types::Ty>)>,
    pub(crate) follow_up: Vec<Job>,
}

impl JobEffects {
    pub(crate) fn wait_on_current(fact: FactKey, follow_up: impl IntoIterator<Item = Job>) -> Self {
        Self {
            waits: vec![FactUse::current(fact)],
            follow_up: follow_up.into_iter().collect(),
            ..Self::default()
        }
    }
}

pub(crate) fn current_uses<F>(facts: impl IntoIterator<Item = F>) -> Vec<FactUse<F>> {
    facts.into_iter().map(FactUse::current).collect()
}

pub(crate) fn settled_uses<F>(facts: impl IntoIterator<Item = F>) -> Vec<FactUse<F>> {
    facts.into_iter().map(FactUse::settled).collect()
}

impl World<'_> {
    /// Expands a demanded fact to its single producer and demands that
    /// producer when a run could say something new.
    ///
    /// This map is the one legitimate mechanism for work to start absent a
    /// wake (northstar: pull-based): the wait names the fact, the fact names
    /// its producer, and the producer runs because something waits on its
    /// output — never because another job commanded it. Both the product
    /// drivers (a `PullWait::Fact` with an empty agenda) and the bare
    /// scheduler (`drive_until`'s demand-on-stall pass) consult it.
    ///
    /// Facts whose producers publish them as co-outputs of broader jobs
    /// (source-surface facts, protocol facts, executables, backend programs)
    /// have no arm: their demand rides the mapped facts that gate them.
    /// Returns how many producers were actually demanded.
    pub(crate) fn demand_fact_producer(&mut self, fact: &FactKey) -> u64 {
        let job = match fact {
            FactKey::RootEntry(root) => Some(Job::SeedRoot(*root)),
            FactKey::FunctionDefined(function) => Some(Job::DefineFunction(*function)),
            FactKey::LoweredBody(function) => Some(Job::LowerFunction(*function)),
            FactKey::Recursive(function) => Some(Job::DeriveRecursive(*function)),
            FactKey::DispatchMask(function) => Some(Job::DeriveDispatchMask(*function)),
            FactKey::Activation(activation) | FactKey::ActivationInputs(activation) => {
                Some(Job::SeedActivation(activation.clone()))
            }
            FactKey::ActivationAnalyzed(activation)
            | FactKey::ReturnType(activation)
            | FactKey::CallSiteTargets(CallSiteKey { activation, .. })
            | FactKey::CallSiteSummary(CallSiteKey { activation, .. }) => {
                let activation = activation.clone();
                let mut pokes = 0;
                if !self.has_fact(&FactKey::Activation(activation.clone()))
                    || !self.has_fact(&FactKey::ActivationInputs(activation.clone()))
                {
                    pokes += self.demand_producer_if_needed(Job::SeedActivation(activation.clone()), fact) as u64;
                }
                return pokes + self.demand_producer_if_needed(Job::AnalyzeActivation(activation), fact) as u64;
            }
            _ => None,
        };
        job.map(|job| self.demand_producer_if_needed(job, fact) as u64)
            .unwrap_or(0)
    }

    fn demand_producer_if_needed(&mut self, job: Job, target_fact: &FactKey) -> bool {
        if self.work_graph.output_keys(&job).contains(target_fact) && !self.work_graph.rebased(&job) {
            return false;
        }
        self.demand(job);
        true
    }

    /// Expands the standing demand every submitted root carries: a root is an
    /// external request that its entry activation be analyzed, exactly as the
    /// product boundary treats `RootBackendProduct(root)`. The expansion only
    /// ignites first-run analysis — once `AnalyzeActivation(entry)` has run, the
    /// graph's own wakes carry every later revision — and it can only fire once
    /// the seed has settled the facts that make the entry key derivable.
    /// Returns how many entry analyses were demanded.
    pub(crate) fn demand_root_entry_analyses(&mut self) -> u64 {
        let roots: Vec<RootId> = self.root_ids().collect();
        let mut demanded = 0_u64;
        for root_id in roots {
            let root = self.root_entry(root_id);
            if !self.fact_is_settled(&FactKey::Recursive(root.function))
                || !self.fact_is_settled(&FactKey::DispatchMask(root.function))
            {
                continue;
            }
            let entry = self.activation_key(root_id, root.function, &root.input);
            if self.work_graph.has_run(&Job::AnalyzeActivation(entry.clone())) {
                continue;
            }
            demanded += self.demand_fact_producer(&FactKey::ActivationAnalyzed(entry));
        }
        demanded
    }

    /// Pops the next ready job, expanding the roots' standing entry-analysis
    /// demands when the agenda has drained. Every job loop (the bare drive and
    /// the product fact-wait loops) pulls through this, so first-run ignition
    /// is owned by the scheduler boundary, not by any job's follow-up.
    pub(crate) fn next_ready_job(&mut self) -> Option<Job> {
        if let Some(job) = self.work_graph.pop() {
            return Some(job);
        }
        if self.demand_root_entry_analyses() > 0 {
            return self.work_graph.pop();
        }
        None
    }

    pub(crate) fn drive_for(&mut self, timeout: Option<Duration>) -> DriveOutcome<Job, FactKey> {
        let deadline = timeout.map(|limit| Instant::now() + limit);
        self.drive_until(deadline, timeout)
    }

    /// Runs queued jobs until the work graph has no ready work.
    ///
    /// Each job gets one telemetry span that closes with the job's raw effects
    /// borrowed in place; the applied graph step rides the separate
    /// `work_graph.applied` event that `complete_job` emits. A fatal job closes
    /// its span, closes the drive span as fatal, and stops the loop.
    pub fn drive(&mut self) -> DriveOutcome<Job, FactKey> {
        self.drive_until(None, None)
    }

    fn drive_until(&mut self, deadline: Option<Instant>, timeout: Option<Duration>) -> DriveOutcome<Job, FactKey> {
        self.clear_reported_warnings();
        let mut span = self.tel().span(
            &["fz", "compiler2", "drive"],
            metadata! {
                pending_jobs: self.work_graph.pending_jobs(),
            },
        );
        let mut jobs_ran = 0_u64;
        // Facts whose producers were already demanded at a stall with no fact
        // change since: re-demanding them would re-run byte-identical jobs.
        // Any content change clears the set — shifted ground can make the same
        // demand productive again.
        let mut stall_demanded: std::collections::HashSet<FactKey> = std::collections::HashSet::new();
        let mut changed_since_stall = true;
        'drive: loop {
            while self.work_graph.pending_jobs() > 0 {
                if deadline.is_some_and(|limit| Instant::now() >= limit) {
                    let pending_jobs = self.work_graph.pending_jobs();
                    let timeout_ms = timeout.map_or(0, |limit| limit.as_millis().min(u64::MAX as u128) as u64);
                    self.tel().event(
                        &["fz", "compiler2", "drive", "timed_out"],
                        metadata! {
                            pending_jobs: pending_jobs as u64,
                            jobs_ran: jobs_ran,
                            timeout_ms: timeout_ms,
                        },
                    );
                    self.clear_unresolved_diagnostics();
                    self.flush_reported_warnings();
                    span.stop_with(
                        &measurements! { jobs_ran: jobs_ran },
                        &metadata! {
                            pending_jobs: pending_jobs as u64,
                            timeout_ms: timeout_ms,
                        },
                    );
                    return DriveOutcome::TimedOut { jobs_ran, pending_jobs };
                }
                let Some(job) = self.work_graph.pop() else {
                    break;
                };
                let job_span = self.tel().span(
                    &["fz", "compiler2", "job"],
                    metadata! {
                        job: opaque_debug(&job),
                    },
                );
                let result = super::jobs::run(self, &job);
                match result {
                    Ok(effects) => {
                        jobs_ran += 1;
                        job_span.stop_with(
                            &measurements! {},
                            &metadata! {
                                effects: opaque_debug(&effects),
                            },
                        );
                        let step = self.complete_job(job, effects);
                        changed_since_stall |= !step.changed.is_empty();
                    }
                    Err(_) => {
                        job_span.stop_with(&measurements! {}, &metadata! {});
                        self.clear_unresolved_diagnostics();
                        self.flush_reported_warnings();
                        span.stop_with(
                            &measurements! { jobs_ran: jobs_ran },
                            &metadata! { job: opaque_debug(&job) },
                        );
                        return DriveOutcome::Fatal { job };
                    }
                }
            }
            // The agenda drained. Two standing demand sources remain, both
            // pulls: every submitted root demands its entry analysis, and
            // every blocked waiter's fact names its single producer through
            // the fact->producer map — the same expansion the product drivers
            // perform when a fact wait finds an empty agenda. Only a genuine
            // drain reaches this pass, so it is event-driven, never a
            // per-iteration sweep, and demanding producers is commutative, so
            // the iteration order of the blocked-waiter set cannot matter.
            if std::mem::take(&mut changed_since_stall) {
                stall_demanded.clear();
            }
            let mut producer_pokes = self.demand_root_entry_analyses();
            for wait in self.work_graph.unresolved() {
                if stall_demanded.insert(wait.fact.fact().clone()) {
                    producer_pokes += self.demand_fact_producer(wait.fact.fact());
                }
            }
            if producer_pokes == 0 {
                // Nothing left to demand: either resolved, or a genuine stall.
                break 'drive;
            }
            self.tel().event(
                &["fz", "compiler2", "drive", "demand_on_stall"],
                metadata! {
                    producer_pokes: producer_pokes,
                },
            );
        }
        if !self.work_graph.has_unresolved() {
            self.clear_unresolved_diagnostics();
            self.flush_reported_warnings();
            span.close_with(measurements! { jobs_ran: jobs_ran }, metadata! {});
            DriveOutcome::Resolved
        } else {
            let unresolved = self.work_graph.unresolved();
            self.emit_unresolved_diagnostics(&unresolved);
            self.flush_reported_warnings();
            span.stop_with(
                &measurements! { jobs_ran: jobs_ran },
                &metadata! {
                    waits: opaque_debug(&unresolved),
                },
            );
            DriveOutcome::Unresolved { waits: unresolved }
        }
    }
}
