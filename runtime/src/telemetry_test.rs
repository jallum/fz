use super::*;
use crate::heap::{GcStats, SchemaRegistry};
use crate::process::CollectionBoundary;
use std::cell::RefCell;
use std::rc::Rc;

fn line(event: RuntimeEvent<'_>) -> String {
    let mut out = String::new();
    write_line(&mut out, 12, 3, 4, &event);
    out
}

#[test]
fn an_event_without_a_payload_writes_an_empty_metadata_object() {
    assert_eq!(
        line(RuntimeEvent::ExecutionReady),
        r#"{"name":["fz","runtime","execution_ready"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{}}"#
    );
}

#[test]
fn a_sleep_writes_its_wait_in_nanoseconds() {
    assert_eq!(
        line(RuntimeEvent::SchedulerSlept(Duration::from_millis(10))),
        r#"{"name":["fz","runtime","scheduler_slept"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"wait_ns":10000000}}"#
    );
}

#[test]
fn a_probe_writes_its_outcome_and_what_the_gift_cost() {
    let probe = SendProbe {
        outcome: ProbeOutcome::Miss,
        receiver: 2,
        reductions: -7,
        gift_bytes: 80,
        gift_blocks: 1,
    };
    assert_eq!(
        line(RuntimeEvent::SendProbe(&probe)),
        r#"{"name":["fz","runtime","send","probe"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"outcome":"miss","receiver":2,"reductions":-7,"gift_bytes":80,"gift_blocks":1}}"#
    );
}

#[test]
fn a_collection_writes_its_boundary_and_the_stats_that_describe_it() {
    let collection = Collection {
        pid: 5,
        boundary: CollectionBoundary::Park,
        stats: GcStats {
            copied_bytes: 288,
            live_bytes: 288,
            from_space_capacity_bytes: 4096,
            blocks_released: 1,
            blocks_after: 2,
            ..GcStats::default()
        },
    };
    assert_eq!(
        line(RuntimeEvent::Gc(&collection)),
        r#"{"name":["fz","runtime","gc"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"pid":5,"boundary":"park","copied_bytes":288,"live_bytes":288,"from_space_capacity_bytes":4096,"blocks_released":1,"blocks_after":2}}"#
    );
}

#[test]
fn a_run_end_writes_the_pool_census() {
    let ended = RunEnded {
        pool_outstanding_before_run: 30,
        pool_outstanding_after_run: 30,
        pool_cached_blocks: 1,
    };
    assert_eq!(
        line(RuntimeEvent::RunEnded(ended)),
        r#"{"name":["fz","runtime","run_ended"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"pool_outstanding_before_run":30,"pool_outstanding_after_run":30,"pool_cached_blocks":1}}"#
    );
}

#[test]
fn an_exit_nests_the_process_as_an_opaque_value() {
    let mut process = Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    process.pid = 1;
    process.halt_value = -4;
    process.failed = true;
    process.dtors_dispatched = 3;
    let live = process.heap.live_count();
    let used = process.heap.bytes_used();
    assert_eq!(
        line(RuntimeEvent::ProcessExited(&process)),
        format!(
            r#"{{"name":["fz","runtime","process_exited"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{{}},"metadata":{{"pid":1,"process":{{"opaque_type":"fz_runtime::process::Process","live_count":{live},"bytes_used":{used},"list_retention_attempts":0,"list_retention_hits":0,"raises_delivered":0,"reduction_yields":0,"dtors_dispatched":3,"halt_value":-4,"failed":true}}}}}}"#
        )
    );
}

#[test]
fn a_sample_counts_blocks_still_held_and_matches_once_they_are_returned() {
    let before = crate::heap::pool_outstanding_blocks();
    let process = crate::process::Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    let held = RunEnded::sample(before);
    assert_eq!(held.pool_outstanding_before_run, before);
    assert!(
        held.pool_outstanding_after_run > before,
        "a live process holds at least its tip block"
    );
    drop(process);
    let returned = RunEnded::sample(before);
    assert_eq!(
        returned.pool_outstanding_after_run, before,
        "tearing the process down returns every block it took"
    );
}
