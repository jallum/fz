use super::*;
use crate::heap::{Footprint, GcStats, SchemaRegistry, StubCounts, StubSite};
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
fn a_timer_arming_writes_its_timer_pid_arm_time_and_deadline() {
    let armed = TimerArmed {
        timer: 5,
        pid: 2,
        armed: Duration::from_millis(5),
        deadline: Duration::from_millis(80),
    };
    assert_eq!(
        line(RuntimeEvent::TimerArmed(armed)),
        r#"{"name":["fz","runtime","timer","armed"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"timer":5,"pid":2,"armed_ns":5000000,"deadline_ns":80000000}}"#
    );
}

#[test]
fn a_timer_firing_and_a_timer_cancelling_write_their_timer_and_pid() {
    assert_eq!(
        line(RuntimeEvent::TimerFired(TimerFired { timer: 5, pid: 2 })),
        r#"{"name":["fz","runtime","timer","fired"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"timer":5,"pid":2}}"#
    );
    assert_eq!(
        line(RuntimeEvent::TimerCancelled(TimerCancelled { timer: 5, pid: 2 })),
        r#"{"name":["fz","runtime","timer","cancelled"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"timer":5,"pid":2}}"#
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
fn a_collection_writes_its_boundary_its_stats_and_the_bytes_in_use_and_idle_when_it_ended() {
    let mut stubs_made = StubCounts::default();
    let mut stubs_survived = StubCounts::default();
    let mut binrefs_made = StubCounts::default();
    binrefs_made.record(StubSite::MessageCopy);
    for _ in 0..3 {
        stubs_made.record(StubSite::AppendedInPlace);
    }
    stubs_made.record(StubSite::MessageCopy);
    stubs_survived.record(StubSite::AppendedInPlace);
    let collection = Collection {
        pid: 5,
        boundary: CollectionBoundary::Park,
        stats: GcStats {
            copied_bytes: 288,
            live_bytes: 288,
            young_bytes: 3072,
            young_budget: 2048,
            from_space_capacity_bytes: 4096,
            blocks_released: 1,
            to_space_guess_bytes: 1024,
            to_space_capacity_bytes: 1024,
            blocks_after: 2,
            stub_visits: 7,
            stubs_made,
            binrefs_made,
            stubs_survived,
            ..GcStats::default()
        },
        footprint: Footprint {
            in_use_bytes: 9216,
            idle_bytes: 4096,
            peak_in_use_bytes: 20480,
        },
    };
    assert_eq!(
        line(RuntimeEvent::Gc(&collection)),
        r#"{"name":["fz","runtime","gc"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"pid":5,"boundary":"park","generation":"minor","copied_bytes":288,"live_bytes":288,"young_bytes":3072,"young_budget":2048,"from_space_capacity_bytes":4096,"blocks_released":1,"to_space_guess_bytes":1024,"to_space_capacity_bytes":1024,"blocks_after":2,"stub_visits":7,"in_use_bytes":9216,"idle_bytes":4096,"stubs_made":{"appended_in_place":3,"window_of_buffer":0,"grown_buffer":0,"filled_buffer":0,"message_copy":1,"static_literal":0},"binrefs_made":{"appended_in_place":0,"window_of_buffer":0,"grown_buffer":0,"filled_buffer":0,"message_copy":1,"static_literal":0},"stubs_survived":{"appended_in_place":1,"window_of_buffer":0,"grown_buffer":0,"filled_buffer":0,"message_copy":0,"static_literal":0}}}"#
    );
}

#[test]
fn a_run_end_writes_the_pool_census_and_the_bytes_in_use_idle_and_at_peak() {
    let ended = RunEnded {
        pool_outstanding_before_run: 30,
        pool_outstanding_after_run: 30,
        pool_cached_blocks: 1,
        footprint: Footprint {
            in_use_bytes: 9216,
            idle_bytes: 4096,
            peak_in_use_bytes: 20480,
        },
    };
    assert_eq!(
        line(RuntimeEvent::RunEnded(ended)),
        r#"{"name":["fz","runtime","run_ended"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"pool_outstanding_before_run":30,"pool_outstanding_after_run":30,"pool_cached_blocks":1,"in_use_bytes":9216,"idle_bytes":4096,"peak_in_use_bytes":20480}}"#
    );
}

#[test]
fn an_exit_nests_the_process_as_an_opaque_value() {
    let mut process = Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    process.pid = 1;
    process.halt_value = -4;
    process.failed = true;
    process.dtors_dispatched = 3;
    process.parks = 5;
    let live = process.heap.live_count();
    let used = process.heap.bytes_used();
    assert_eq!(
        line(RuntimeEvent::ProcessExited(&process)),
        format!(
            r#"{{"name":["fz","runtime","process_exited"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{{}},"metadata":{{"pid":1,"process":{{"opaque_type":"fz_runtime::process::Process","live_count":{live},"bytes_used":{used},"list_retention_attempts":0,"list_retention_hits":0,"struct_retention_attempts":0,"struct_retention_hits":0,"raises_delivered":0,"reduction_yields":0,"parks":5,"dtors_dispatched":3,"frame_copies":0,"halt_value":-4,"failed":true}}}}}}"#
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

#[test]
fn a_sample_reads_the_threads_footprint_with_a_live_process_holding_bytes() {
    let before = crate::heap::pool_footprint();
    let process = crate::process::Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    let held = RunEnded::sample(0).footprint;
    assert!(
        held.in_use_bytes > before.in_use_bytes,
        "a live process holds its tip block"
    );
    assert!(held.peak_in_use_bytes >= held.in_use_bytes);
    drop(process);
    let returned = RunEnded::sample(0).footprint;
    assert_eq!(returned.in_use_bytes, before.in_use_bytes, "teardown returns its bytes");
    assert!(returned.peak_in_use_bytes >= held.peak_in_use_bytes);
}
