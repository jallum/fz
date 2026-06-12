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
    AnalyzeActivation(ActivationKey),
    SealSemanticClosure(RootId),
    MaterializeRoot(RootId),
    DeriveAbiReady(RootId),
    DeriveEmissionReady(RootId),
    LowerBackendProgram(RootId),
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
    CallSiteSummary(CallSiteKey),
    Executable(ExecutableKey),
    SemanticClosed(RootId),
    MaterializedProgram(RootId),
    AbiReadyProgram(RootId),
    EmissionReadyProgram(RootId),
    BackendProgram(RootId),
    NativeProgram(RootId),
}

impl ClaimShape for FactKey {
    /// The two fixpoint-evidence facts whose stores maintain a monotone join:
    /// an activation's return ascends by union (`ActivationMap::define_return`)
    /// and its body-input evidence ascends by the cross-publisher widen
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

    pub(crate) fn wait_on_settled(fact: FactKey, follow_up: impl IntoIterator<Item = Job>) -> Self {
        Self {
            waits: vec![FactUse::settled(fact)],
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
                    self.complete_job(job, effects);
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
