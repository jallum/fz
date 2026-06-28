//! Test-facing livelock backstop for drive-heavy tests.
//!
//! A re-derivation loop in the fact engine surfaces only as a slow, opaque
//! drive that eventually trips a timeout or a flat iteration bound -- with no
//! hint as to WHICH job kind is spinning. This handler taps the per-job
//! telemetry span (`["fz","compiler2","job"]`), counts runs per `Job` variant,
//! and panics the instant a variant crosses its cap, naming the runaway kind.
//!
//! It is a BACKSTOP for genuine non-termination, not a tight budget: the cap is
//! generous (consistent with `drive_until_semantic_closure`'s `10_000`
//! iteration bound) so it never false-trips on real convergence. Detecting the
//! subtler "converges, but re-derives more than it should" case (e.g. the
//! demand/analysis volume on heavy enum fixtures, fz-bfh.6) is a separate,
//! tighter, fixture-specific measurement -- deliberately NOT encoded here, so
//! this guard never bakes in tolerance for a known-bad count.
//!
//! Usage: construct one, attach `handler()` to the test's telemetry under
//! `["fz","compiler2","job"]` before driving, then drive as usual.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::drive::Job;
use crate::telemetry::handler::{Event, EventKind, Handler};

/// Generous per-kind ceiling. Any single job kind running this many times in one
/// drive is a re-derivation loop, not a converging fixpoint. Uniform on purpose:
/// per-kind tuning would invite encoding a fixture's known count as "allowed".
const LIVELOCK_CAP: u64 = 10_000;

/// Counts per-`Job`-variant runs across a drive and panics when one exceeds
/// [`LIVELOCK_CAP`]. Share the counts with the attached handler via `handler()`.
pub(super) struct JobBudgetGuard {
    counts: Rc<RefCell<HashMap<&'static str, u64>>>,
}

impl JobBudgetGuard {
    pub(super) fn new() -> Self {
        Self {
            counts: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub(super) fn handler(&self) -> Box<dyn Handler> {
        Box::new(JobBudgetGuardHandler {
            counts: self.counts.clone(),
        })
    }
}

struct JobBudgetGuardHandler {
    counts: Rc<RefCell<HashMap<&'static str, u64>>>,
}

impl Handler for JobBudgetGuardHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "job"] || event.kind != EventKind::SpanStart {
            return;
        }
        let Some(job) = event.metadata.get("job").and_then(|value| value.downcast_ref::<Job>()) else {
            return;
        };
        let kind = job_kind_name(job);
        let mut counts = self.counts.borrow_mut();
        let count = counts.entry(kind).or_default();
        *count += 1;
        assert!(
            *count <= LIVELOCK_CAP,
            "runaway recalculation: job kind `{kind}` ran {count} times (cap {LIVELOCK_CAP}) -- \
             a re-derivation loop, not a converging fixpoint",
        );
    }
}

/// Stable, allocation-free discriminant name for a `Job` (its payload dropped),
/// so runs can be tallied per kind.
fn job_kind_name(job: &Job) -> &'static str {
    use Job::*;
    match job {
        IndexCode(_) => "IndexCode",
        ScopeCode(_) => "ScopeCode",
        DefineModule(_) => "DefineModule",
        DefineModuleInterface(_) => "DefineModuleInterface",
        PublishFunctionSource(_) => "PublishFunctionSource",
        ExpandFunctionSource(_) => "ExpandFunctionSource",
        DefineFunction(_) => "DefineFunction",
        DeriveTypeDef(_) => "DeriveTypeDef",
        DeriveFunctionContract(_) => "DeriveFunctionContract",
        LowerFunction(_) => "LowerFunction",
        ReifyGuardDispatch(_) => "ReifyGuardDispatch",
        PlanEntryDispatch(_) => "PlanEntryDispatch",
        BuildMacroExecutable(_) => "BuildMacroExecutable",
        DeriveRecursive(_) => "DeriveRecursive",
        DeriveDispatchMask(_) => "DeriveDispatchMask",
        SeedRoot(_) => "SeedRoot",
        SeedActivation(_) => "SeedActivation",
        AnalyzeActivation(_) => "AnalyzeActivation",
        DeriveRuntimeDemand(_) => "DeriveRuntimeDemand",
        SealSemanticClosure(_) => "SealSemanticClosure",
        DeriveExecutableTransport(_) => "DeriveExecutableTransport",
        DeriveTransportPlan(_) => "DeriveTransportPlan",
        BuildBackendProduct(_) => "BuildBackendProduct",
        LowerNativeProgram(_) => "LowerNativeProgram",
    }
}
