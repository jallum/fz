//! Regression coverage for the shared `RootBackendProduct` pull-drive seam:
//! one loop (`product_drive::drive_root_backend_product`) reports its four
//! failure shapes through a `ProductDriveError` hook so the interp front door
//! (`String`) and the backend product job (`FatalError`) keep their distinct
//! error surfaces byte-for-byte, even though the loop that discovers the
//! failure lives once.
//!
//! These tests call the trait implementations directly rather than forcing a
//! genuine product-pull stall through a fixture: the loop control-flow itself
//! is already exercised end-to-end by every other compiler2 test that drives
//! a root to a backend product (`compiler2_test`, `transport_contract_test`,
//! `drive_test`, ...), so the risk unique to this seam is the
//! `ProductDriveError` dispatch — that is what these tests pin.

use super::World;
use super::drive::FactKey;
use super::drive::Job;
use super::facts::FactUse;
use super::identity::RootId;
use super::product_drive::ProductDriveError;
use super::pull::{ProductKey, PullWait};
use super::scheduler::FatalError;
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
