//! fz-afu.2: jobs start only when their inputs exist.
//!
//! `def main(), do: 1` names 13 job kinds over 2 subjects -- `main/0` and the
//! nested `def/1` macro root it needs compiled first -- 26 subjects in all.
//! Before this fix, `demand_producer_if_needed`'s never-run branch enqueued a
//! job the moment anything demanded its output, regardless of whether the
//! job's own inputs existed yet; the job then discovered its missing input as
//! an early-return wait, one rung per run, and ran again once the fact
//! landed. That produced 44 starts: 26 subjects plus 18 repeats, every one of
//! them a run that concluded with nothing but a blocked fact.
//!
//! A job now declares its gates -- the facts it cannot conclude without,
//! computed from its subject and the facts already present -- and the
//! scheduler checks them before ever starting a never-run job DEMANDED
//! through `World::demand_fact_producer`. A job whose gate is missing is not
//! started; the missing gate's producer is demanded instead. That drops the
//! 44 to 28: every repeat this way saves is a job that would only have
//! discovered its own gate.
//!
//! `World::submit_root` takes the same gated start as every other job: it no
//! longer enqueues `SeedRoot` directly. It demands `RootEntry` through
//! `World::demand_fact_producer`, the same call every gate redirect uses, and
//! `drive::demand_root_frontier_seeds` -- a standing demand shaped exactly
//! like `demand_activation_frontier_analyses` -- keeps re-demanding a
//! submitted root's seed across later drains until `SeedRoot` has actually
//! run. `SeedRoot(main)` and `SeedRoot(def/1)` each run exactly once.
//!
//! One repeat survives: `ScopeCode(user code)` discovers the `def/1` macro
//! root it needs compiled while reading the source -- a wait the job's own
//! walk finds mid-run, never nameable from the subject alone, so it is not a
//! gate. `ScopeCode` runs 3 times for that one subject.
//!
//! Every other kind, and every other subject of a gated kind -- including
//! every `SeedRoot` -- runs exactly once.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::drive::DependencyKey;
use super::world::{JobCompletion, World};
use super::{CodeSubmission, ExecutableNeed, FactKey, Job, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

fn job_kind(job: &Job) -> &'static str {
    match job {
        Job::IndexCode(_) => "IndexCode",
        Job::ScopeCode(_) => "ScopeCode",
        Job::DefineModule(_) => "DefineModule",
        Job::DefineModuleInterface(_) => "DefineModuleInterface",
        Job::ExpandFunctionSource(_) => "ExpandFunctionSource",
        Job::DefineFunction(_) => "DefineFunction",
        Job::DeriveTypeDef(_) => "DeriveTypeDef",
        Job::DeriveFunctionContract(_) => "DeriveFunctionContract",
        Job::LowerFunction(_) => "LowerFunction",
        Job::ReifyGuardDispatch(_) => "ReifyGuardDispatch",
        Job::PlanEntryDispatch(_) => "PlanEntryDispatch",
        Job::DeriveStaticCallees(_) => "DeriveStaticCallees",
        Job::DeriveCallGraphComponent(_) => "DeriveCallGraphComponent",
        Job::DeriveInputDemand(_) => "DeriveInputDemand",
        Job::SeedRoot(_) => "SeedRoot",
        Job::SeedActivation(_) => "SeedActivation",
        Job::AnalyzeActivation(_) => "AnalyzeActivation",
        Job::DeriveExecutableFacts(_) => "DeriveExecutableFacts",
        Job::DeriveCallableConstructionTarget(_) => "DeriveCallableConstructionTarget",
        Job::DeriveRuntimeDemand(_) => "DeriveRuntimeDemand",
    }
}

/// The 9 job kinds fz-afu.2 gives a static gate (`.agent/docs/fact-engine.md`,
/// "A job's gates"). A blocked-only run of any other kind means a job started
/// before its declared inputs existed.
const GATED_KINDS: &[&str] = &[
    "SeedRoot",
    "DefineFunction",
    "ExpandFunctionSource",
    "ScopeCode",
    "DeriveInputDemand",
    "DeriveCallGraphComponent",
    "DeriveRuntimeDemand",
    "LowerFunction",
    "DeriveStaticCallees",
];

struct RunRecord {
    subject: String,
    /// This run's conclusion published nothing and left standing waits: the
    /// same shape as a job that started, found an input missing, and
    /// stopped.
    blocked_only: bool,
    blocked: Vec<DependencyKey>,
}

#[test]
fn def_main_do_1_starts_each_job_once_per_subject() {
    let tel = ConfiguredTelemetry::new();
    let runs: Rc<RefCell<Vec<(&'static str, RunRecord)>>> = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&runs);
    tel.attach_raw_event2::<World, JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, _world, completion| {
            let blocked_only = completion.step.changed.is_empty() && !completion.step.blocked.is_empty();
            let blocked = completion.step.blocked.iter().map(|use_| use_.fact().clone()).collect();
            observed.borrow_mut().push((
                job_kind(&completion.job),
                RunRecord {
                    subject: format!("{:?}", completion.job),
                    blocked_only,
                    blocked,
                },
            ));
        },
    );

    let mut compiler = super::Compiler2::new(tel);
    let user_source = compiler.submit_code(CodeSubmission {
        name: Some("gated_job_starts.fz".to_string()),
        text: "def main(), do: 1\n".to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let result = compiler
        .run_root_interp(root)
        .expect("def main(), do: 1 should compile and run");
    assert_eq!(result, 1);

    let runs = runs.borrow();
    let subjects_and_kinds = || {
        runs.iter()
            .map(|(kind, record)| format!("{kind} {}", record.subject))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        runs.len(),
        28,
        "expected 28 job starts, saw {}:\n{:#?}",
        runs.len(),
        subjects_and_kinds(),
    );

    let mut per_subject: HashMap<(&'static str, &str), usize> = HashMap::new();
    for (kind, record) in runs.iter() {
        *per_subject.entry((*kind, record.subject.as_str())).or_default() += 1;
    }
    assert_eq!(
        per_subject.len(),
        26,
        "expected 26 distinct (kind, subject) pairs, saw {}",
        per_subject.len(),
    );

    let user_scope_code = format!("{:?}", Job::ScopeCode(user_source));
    for (&(kind, subject), &count) in &per_subject {
        let expected = if kind == "ScopeCode" && subject == user_scope_code {
            3
        } else {
            1
        };
        assert_eq!(
            count, expected,
            "{kind} {subject} ran {count} time(s), expected {expected}"
        );
    }

    // No gated kind may conclude a blocked-only run outside the one
    // explained exception: `ScopeCode(user code)`'s discovered macro waits
    // (see the module doc comment for why that one survives).
    for (kind, record) in runs.iter() {
        if !record.blocked_only {
            continue;
        }
        assert!(
            GATED_KINDS.contains(kind),
            "{kind} {} blocked with nothing produced, but {kind} declares no gate -- this run has no explanation",
            record.subject,
        );
        let is_scope_code_discovery = *kind == "ScopeCode" && record.subject == user_scope_code;
        assert!(
            is_scope_code_discovery,
            "{kind} {} concluded with only a blocked gate fact: {:?} -- its gate should have kept it from \
             starting until that fact existed",
            record.subject, record.blocked,
        );
        for fact in &record.blocked {
            assert!(
                !matches!(
                    fact,
                    DependencyKey::Fact(FactKey::CodeIndexed(_)) | DependencyKey::Fact(FactKey::CodeScoped(_))
                ),
                "ScopeCode(user code) blocked on its own gate fact {fact:?} -- the gate should have kept it \
                 from starting at all",
            );
        }
    }
}
