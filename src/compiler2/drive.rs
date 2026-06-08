//! Work loop and shared work vocabulary.
//!
//! This module owns the scheduler-facing shapes: job ids, fact ids, job
//! effects, and the drive loop. Concrete job implementations live under
//! `compiler2::jobs`.

use crate::telemetry::{TelemetryExt, opaque};
use crate::{measurements, metadata};

use super::code::CodeId;
use super::facts::FactValue;
use super::identity::{ActivationKey, ExecutableKey, FunctionId, ModuleId, RootId};
use super::scheduler::{DriveOutcome, Scheduler};
use super::semantic::CallSiteKey;
use super::world::World;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Job {
    IndexCode(CodeId),
    ScopeCode(CodeId),
    DefineModule(ModuleId),
    LowerFunction(FunctionId),
    ReifyGuardDispatch(FunctionId),
    PlanEntryDispatch(FunctionId),
    DeriveRecursive(FunctionId),
    DeriveDispatchMask(FunctionId),
    SeedRoot(RootId),
    AnalyzeActivation(ActivationKey),
    SealSemanticClosure(RootId),
    MaterializeRoot(RootId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FactKey {
    CodeIndexed(CodeId),
    CodeScoped(CodeId),
    ModuleIndexed(ModuleId),
    ModuleDefined(ModuleId),
    FunctionDefined(FunctionId),
    LoweredBody(FunctionId),
    GuardDispatch(FunctionId),
    EntryDispatch(FunctionId),
    Recursive(FunctionId),
    DispatchMask(FunctionId),
    RootEntry(RootId),
    Activation(ActivationKey),
    ActivationAnalyzed(ActivationKey),
    ReturnType(ActivationKey),
    CallSiteSummary(CallSiteKey),
    Executable(ExecutableKey),
    SemanticClosed(RootId),
    MaterializedProgram(RootId),
}

pub type WorkGraph = Scheduler<Job, FactKey>;

#[derive(Debug, Clone, Default)]
pub(crate) struct JobEffects {
    pub(crate) reads: Vec<FactKey>,
    pub(crate) waits: Vec<FactKey>,
    pub(crate) outputs: Vec<(FactKey, FactValue)>,
    pub(crate) follow_up: Vec<Job>,
}

impl JobEffects {
    pub(crate) fn wait_on(fact: FactKey, follow_up: impl IntoIterator<Item = Job>) -> Self {
        Self {
            waits: vec![fact],
            follow_up: follow_up.into_iter().collect(),
            ..Self::default()
        }
    }
}

impl World<'_> {
    /// Runs queued jobs until the work graph has no ready work.
    ///
    /// Each job gets one telemetry span. A successful job publishes its effects
    /// to the graph, then closes with the raw effects and applied graph step. A
    /// fatal job closes its span, closes the drive span as fatal, and stops the
    /// loop.
    pub fn drive(&mut self) -> DriveOutcome<Job, FactKey> {
        let mut span = self.tel().span(
            &["fz", "compiler2", "drive"],
            metadata! {
                pending_jobs: self.work_graph.pending_jobs() as u64,
            },
        );
        let mut jobs_ran = 0_u64;
        while let Some(job) = self.work_graph.pop() {
            let job_span = self.tel().span(
                &["fz", "compiler2", "job"],
                metadata! {
                    job: opaque(&job),
                },
            );
            let result = super::jobs::run(self, &job);
            match result {
                Ok(effects) => {
                    jobs_ran += 1;
                    let step = self.complete_job(job.clone(), effects.clone());
                    job_span.stop_with(
                        &measurements! {},
                        &metadata! {
                            effects: opaque(&effects),
                            step: opaque(&step),
                        },
                    );
                }
                Err(_) => {
                    job_span.stop_with(&measurements! {}, &metadata! {});
                    self.clear_unresolved_diagnostics();
                    span.stop_with(&measurements! { jobs_ran: jobs_ran }, &metadata! { job: opaque(&job) });
                    return DriveOutcome::Fatal { job };
                }
            }
        }
        if !self.work_graph.has_unresolved() {
            self.clear_unresolved_diagnostics();
            span.close_with(measurements! { jobs_ran: jobs_ran }, metadata! {});
            DriveOutcome::Resolved
        } else {
            let unresolved = self.work_graph.unresolved();
            self.emit_unresolved_diagnostics(&unresolved);
            span.stop_with(
                &measurements! { jobs_ran: jobs_ran },
                &metadata! {
                    waits: opaque(&unresolved),
                },
            );
            DriveOutcome::Unresolved { waits: unresolved }
        }
    }
}
