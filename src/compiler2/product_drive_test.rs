//! Regression coverage for the shared `RootBackendProduct` pull-drive seam:
//! one loop (`product_drive::drive_root_backend_product`) reports its four
//! failure shapes through a `ProductDriveError` hook so the interp front door
//! (`String`) and the backend product job (`FatalError`) keep their distinct
//! error surfaces byte-for-byte, even though the loop that discovers the
//! failure lives once.
//!
//! The first block of tests calls the trait implementations directly rather
//! than forcing a genuine product-pull stall through a fixture: the loop
//! control-flow itself is already exercised end-to-end by every other
//! compiler2 test that drives a root to a backend product (`compiler2_test`,
//! `transport_contract_test`, `drive_test`, ...), so the risk unique to this
//! seam is the `ProductDriveError` dispatch — that is what those tests pin.
//!
//! The second block (`*_end_to_end` below) proves the wiring itself: that a
//! genuine failure inside `drive_root_backend_product` reaches the hook with
//! the right `root`/`fact`/`job` arguments, not just that the hook formats
//! them correctly in isolation. `fact_wait_budget_exceeded` and
//! `did_not_settle` go through `drive_root_backend_product_with_budgets`, a
//! test-only budget seam (`product_drive.rs`) — the production entry point
//! always calls it with the real 50,000-job budget for both parameters, so
//! this changes no production behavior.

use super::World;
use super::drive::FactKey;
use super::drive::Job;
use super::facts::FactUse;
use super::identity::{ExecutableNeed, RootId};
use super::product_drive::ProductDriveError;
use super::pull::{ProductKey, PullWait};
use super::scheduler::{DriveOutcome, FatalError};
use super::{CodeSubmission, Compiler2, RootSubmission};
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

fn some_fact() -> FactUse<FactKey> {
    FactUse::settled(FactKey::BackendProgram(RootId::for_test(7)))
}

#[test]
fn string_error_reports_no_ready_producer_with_unresolved_waits() {
    let tel = ConfiguredTelemetry::new();
    let world = World::new(&tel);
    let root = RootId::for_test(7);
    let fact = some_fact();

    let message = <String as ProductDriveError>::no_ready_producer(&world, root, &fact);

    assert_eq!(
        message,
        format!(
            "compiler2 root {} product path waited on {:?} with no ready producer; unresolved={:?}",
            root.as_u32(),
            fact,
            world.work_graph.unresolved()
        )
    );
}

#[test]
fn string_error_reports_fact_wait_budget_exceeded() {
    let tel = ConfiguredTelemetry::new();
    let world = World::new(&tel);
    let root = RootId::for_test(7);
    let fact = some_fact();

    let message = <String as ProductDriveError>::fact_wait_budget_exceeded(&world, root, &fact);

    assert_eq!(
        message,
        format!(
            "compiler2 root {} product path exceeded fact-wait budget for {:?}",
            root.as_u32(),
            fact
        )
    );
}

#[test]
fn string_error_reports_did_not_settle_with_last_wait() {
    let tel = ConfiguredTelemetry::new();
    let world = World::new(&tel);
    let root = RootId::for_test(7);
    let last_wait = Some((ProductKey::RootBackendProduct(root), vec![PullWait::Fact(some_fact())]));

    let message = <String as ProductDriveError>::did_not_settle(&world, root, last_wait.clone());

    assert_eq!(
        message,
        format!(
            "compiler2 root {} product backend did not settle; last wait: {last_wait:?}",
            root.as_u32()
        )
    );
}

#[test]
fn string_error_reports_job_failed_without_the_job_run_error_details() {
    let tel = ConfiguredTelemetry::new();
    let world = World::new(&tel);
    let root = RootId::for_test(7);
    let fact = some_fact();
    let job = Job::BuildBackendProduct(root);

    let message = <String as ProductDriveError>::job_failed(&world, root, &fact, &job, FatalError);

    assert_eq!(
        message,
        format!(
            "compiler2 root {} product path failed while producing {:?}: {:?}",
            root.as_u32(),
            fact,
            job
        )
    );
}

#[test]
fn fatal_error_diagnostic_reports_no_ready_producer() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let world = World::new(&tel);
    let root = RootId::for_test(7);
    let fact = some_fact();

    let result = <FatalError as ProductDriveError>::no_ready_producer(&world, root, &fact);
    assert_eq!(result, FatalError, "the backend job surfaces a FatalError, not text");

    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("no-ready-producer should emit an error diagnostic");
    let message = match event.metadata.get("message") {
        Some(Value::Str(message)) => message.clone(),
        other => panic!("diagnostic event missing message metadata: {other:?}"),
    };
    assert_eq!(
        message,
        format!(
            "compiler2 backend product for root {} waited on {:?} with no ready producer",
            root.as_u32(),
            fact
        )
    );
}

#[test]
fn fatal_error_diagnostic_reports_fact_wait_budget_exceeded() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let world = World::new(&tel);
    let root = RootId::for_test(7);
    let fact = some_fact();

    <FatalError as ProductDriveError>::fact_wait_budget_exceeded(&world, root, &fact);

    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("fact-wait budget exhaustion should emit an error diagnostic");
    let message = match event.metadata.get("message") {
        Some(Value::Str(message)) => message.clone(),
        other => panic!("diagnostic event missing message metadata: {other:?}"),
    };
    assert_eq!(
        message,
        format!(
            "compiler2 backend product for root {} exceeded fact-wait budget for {:?}",
            root.as_u32(),
            fact
        )
    );
}

#[test]
fn fatal_error_diagnostic_reports_did_not_settle_without_last_wait_detail() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let world = World::new(&tel);
    let root = RootId::for_test(7);
    let last_wait = Some((ProductKey::RootBackendProduct(root), vec![PullWait::Fact(some_fact())]));

    <FatalError as ProductDriveError>::did_not_settle(&world, root, last_wait);

    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("did-not-settle should emit an error diagnostic");
    let message = match event.metadata.get("message") {
        Some(Value::Str(message)) => message.clone(),
        other => panic!("diagnostic event missing message metadata: {other:?}"),
    };
    // Unlike the interp front door's `String` error, the backend job's
    // diagnostic never carried the `last_wait` detail -- preserved as-is.
    assert_eq!(
        message,
        format!("compiler2 backend product for root {} did not settle", root.as_u32())
    );
}

#[test]
fn fatal_error_job_failed_forwards_the_jobs_run_error_unchanged() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let world = World::new(&tel);
    let root = RootId::for_test(7);
    let fact = some_fact();
    let job = Job::BuildBackendProduct(root);

    let result = <FatalError as ProductDriveError>::job_failed(&world, root, &fact, &job, FatalError);
    assert_eq!(result, FatalError);

    // The failed job already emitted its own diagnostic through `jobs::run`;
    // this boundary must not emit a second one for the same failure.
    assert!(
        capture.last(&["fz", "diag", "error"]).is_none(),
        "job_failed must not emit its own diagnostic on top of the job's"
    );
}

// --- end-to-end: genuine drive failures reaching each hook ---------------

/// `no_ready_producer`: a root submitted for a function name that is never
/// defined by any submitted code. `SeedRoot` claims `RootEntry` as an output
/// on its very first (still-blocked) run -- `World::demand_producer_if_needed`
/// then treats that fact as already claimed and never re-demands `SeedRoot`,
/// so `RootEntry`'s own keying wait resolves quickly, but the `Recursive`
/// keying wait it gates (`jobs::backend::produce_root_backend_product`) has
/// no other path to `DeriveRecursive` for a function that is never scoped:
/// the fact-wait's agenda drains and `demand_fact_producer` has nothing left
/// to poke. This is a real dead end reachable from ordinary (if buggy) input
/// -- a typo'd entry-point name -- not a fabricated one.
#[test]
fn string_error_end_to_end_no_ready_producer_from_undefined_root_entry() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "totally_undefined_entry".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let function = compiler.root_function(root);

    let error = compiler
        .run_root_interp(root)
        .expect_err("a root naming an entry no code ever defines should never settle");

    let fact = FactUse::settled(FactKey::Recursive(function));
    assert_eq!(
        error,
        format!(
            "compiler2 root {} product path waited on {:?} with no ready producer; unresolved={:?}",
            root.as_u32(),
            fact,
            // Read after the fact so the assertion mirrors exactly what the
            // hook itself reports, not a separately reconstructed guess.
            compiler.world().work_graph.unresolved()
        ),
        "the String path should report the undefined entry's Recursive keying wait, got: {error}"
    );
}

#[test]
fn fatal_error_end_to_end_no_ready_producer_from_undefined_root_entry() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut world = World::new(&tel);
    let root = world.submit_root(None, "totally_undefined_entry".to_string(), 0, ExecutableNeed::Value);
    let function = world.root_function(root);

    world.demand(Job::BuildBackendProduct(root));
    let outcome = world.drive_for(None);
    assert!(
        matches!(&outcome, DriveOutcome::Fatal { job } if *job == Job::BuildBackendProduct(root)),
        "the backend product job should fail fatally when its entry is never defined, got: {outcome:?}"
    );

    let fact = FactUse::settled(FactKey::Recursive(function));
    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("no-ready-producer should emit an error diagnostic");
    let message = match event.metadata.get("message") {
        Some(Value::Str(message)) => message.clone(),
        other => panic!("diagnostic event missing message metadata: {other:?}"),
    };
    assert_eq!(
        message,
        format!(
            "compiler2 backend product for root {} waited on {:?} with no ready producer",
            root.as_u32(),
            fact
        ),
        "the FatalError path should report the undefined entry's Recursive keying wait"
    );
}

/// `fact_wait_budget_exceeded`: an ordinary, fully resolvable root (`add1`),
/// driven through the test-only budget seam with the inner per-fact-wait job
/// budget forced to zero. `drive_product_fact_wait`'s budget check runs after
/// every job unconditionally, so the very first job any real fact-wait runs
/// already exceeds a budget of zero -- this is the same check production
/// hits at 50,001 jobs, just forced early so the test stays fast.
#[test]
fn string_error_end_to_end_fact_wait_budget_exceeded_on_a_real_drive() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("fixtures2/behavior/add1.fz".to_string()),
        include_str!("../../fixtures2/behavior/add1.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    let result = super::product_drive::drive_root_backend_product_with_budgets::<String>(
        &mut world,
        root,
        super::product_drive::PRODUCT_DRIVE_BUDGET,
        0,
    );
    let error = match result {
        Ok(_) => panic!("a zero fact-wait budget should trip on the first job any real fact-wait runs"),
        Err(error) => error,
    };
    assert!(
        error.contains(&format!(
            "compiler2 root {} product path exceeded fact-wait budget for",
            root.as_u32()
        )),
        "should report the fact-wait budget exceeded template, got: {error}"
    );
}

#[test]
fn fatal_error_end_to_end_fact_wait_budget_exceeded_on_a_real_drive() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut world = World::new(&tel);
    world.submit_code(
        Some("fixtures2/behavior/add1.fz".to_string()),
        include_str!("../../fixtures2/behavior/add1.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    let result = super::product_drive::drive_root_backend_product_with_budgets::<FatalError>(
        &mut world,
        root,
        super::product_drive::PRODUCT_DRIVE_BUDGET,
        0,
    );
    assert_eq!(
        result.err(),
        Some(FatalError),
        "a zero fact-wait budget should trip fatally on a real drive"
    );

    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("fact-wait budget exhaustion should emit an error diagnostic");
    let message = match event.metadata.get("message") {
        Some(Value::Str(message)) => message.clone(),
        other => panic!("diagnostic event missing message metadata: {other:?}"),
    };
    assert!(
        message.starts_with(&format!(
            "compiler2 backend product for root {} exceeded fact-wait budget for",
            root.as_u32()
        )),
        "should report the fact-wait budget exceeded template, got: {message}"
    );
}

/// `did_not_settle`: the same ordinary `add1` root, driven with the outer
/// product-stack budget forced small enough that the stack pull cannot reach
/// a settled `RootBackendProduct` before the budget runs out, while the inner
/// fact-wait budget stays generous so real jobs run and populate `last_wait`
/// with genuine content (not `None`).
#[test]
fn string_error_end_to_end_did_not_settle_on_a_real_drive() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("fixtures2/behavior/add1.fz".to_string()),
        include_str!("../../fixtures2/behavior/add1.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    let result = super::product_drive::drive_root_backend_product_with_budgets::<String>(
        &mut world,
        root,
        3,
        super::product_drive::PRODUCT_DRIVE_BUDGET,
    );
    let error = match result {
        Ok(_) => panic!("a product-stack budget of 3 should exhaust before add1's product settles"),
        Err(error) => error,
    };
    assert!(
        error.starts_with(&format!(
            "compiler2 root {} product backend did not settle; last wait: Some(",
            root.as_u32()
        )),
        "should report did-not-settle with a populated last wait, got: {error}"
    );
}

/// `job_failed`: a runtime root submitted against a `defmacro` entry.
/// `jobs::root::seed_root` rejects a `RootKind::Runtime` root whose function
/// `is_macro` before it publishes anything, returning `Err(FatalError)`
/// straight from `jobs::run`. `SeedRoot` is the sole producer named by every
/// one of `produce_root_backend_product`'s keying waits
/// (`RootEntry`/`DispatchMask`/`Recursive`) and is already agenda-queued
/// from the root's own ignition, so it runs -- and fails -- inside
/// `drive_product_fact_wait`'s own job loop while satisfying the first of
/// those waits, not somewhere else in the pipeline: a genuine, minimal
/// construction of the seam under test, not a fabricated one.
#[test]
fn string_error_end_to_end_job_failed_from_runtime_root_targeting_a_macro() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_only_root.fz".to_string()),
        text: "defmacro inc(x) do\n  quote do: unquote(x) + 1\nend\n".to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "inc".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });

    let function = compiler.root_function(root);
    let error = compiler
        .run_root_interp(root)
        .expect_err("a runtime root targeting a macro entry must fail, not silently succeed");

    // `produce_root_backend_product`'s keying waits fire in reverse order
    // (`Recursive`, `DispatchMask`, `RootEntry`), and `SeedRoot` -- the only
    // producer any of the three names -- is already agenda-queued from the
    // root's ignition, so it runs while satisfying the *first* wait in that
    // reversed order: `Recursive`, not `RootEntry`, even though `SeedRoot`
    // never gets far enough to publish either fact on this rejecting run.
    let fact = FactUse::settled(FactKey::Recursive(function));
    let job = Job::SeedRoot(root);
    assert_eq!(
        error,
        format!(
            "compiler2 root {} product path failed while producing {:?}: {:?}",
            root.as_u32(),
            fact,
            job
        ),
        "the String path should report the Recursive fact-wait's SeedRoot job failure, got: {error}"
    );
}

#[test]
fn fatal_error_end_to_end_job_failed_from_runtime_root_targeting_a_macro() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut world = World::new(&tel);
    world.submit_code(
        Some("macro_only_root.fz".to_string()),
        "defmacro inc(x) do\n  quote do: unquote(x) + 1\nend\n".to_string(),
    );
    let root = world.submit_root(None, "inc".to_string(), 1, ExecutableNeed::Value);

    world.demand(Job::BuildBackendProduct(root));
    let outcome = world.drive_for(None);
    assert!(
        matches!(&outcome, DriveOutcome::Fatal { job } if *job == Job::BuildBackendProduct(root)),
        "the backend product job should fail fatally when its root targets a macro, got: {outcome:?}"
    );

    // `job_failed` forwards the failed job's own `FatalError` unchanged, so
    // exactly one diagnostic reaches telemetry: `SeedRoot`'s own
    // `emit_root_error`, not a second one from this boundary.
    assert_eq!(
        capture.count(&["fz", "diag", "error"]),
        1,
        "job_failed must not emit a diagnostic on top of the failing job's own"
    );
    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("SeedRoot's macro rejection should emit an error diagnostic");
    let message = match event.metadata.get("message") {
        Some(Value::Str(message)) => message.clone(),
        other => panic!("diagnostic event missing message metadata: {other:?}"),
    };
    assert_eq!(
        message, "compiler2 runtime root cannot target macro `inc/1`",
        "should surface SeedRoot's own rejection message unchanged"
    );
}

#[test]
fn fatal_error_end_to_end_did_not_settle_on_a_real_drive() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut world = World::new(&tel);
    world.submit_code(
        Some("fixtures2/behavior/add1.fz".to_string()),
        include_str!("../../fixtures2/behavior/add1.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    let result = super::product_drive::drive_root_backend_product_with_budgets::<FatalError>(
        &mut world,
        root,
        3,
        super::product_drive::PRODUCT_DRIVE_BUDGET,
    );
    assert_eq!(
        result.err(),
        Some(FatalError),
        "a product-stack budget of 3 should exhaust fatally before add1's product settles"
    );

    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("did-not-settle should emit an error diagnostic");
    let message = match event.metadata.get("message") {
        Some(Value::Str(message)) => message.clone(),
        other => panic!("diagnostic event missing message metadata: {other:?}"),
    };
    // Unlike the interp front door's `String` error, the backend job's
    // diagnostic never carries the `last_wait` detail -- preserved as-is.
    assert_eq!(
        message,
        format!("compiler2 backend product for root {} did not settle", root.as_u32())
    );
}
