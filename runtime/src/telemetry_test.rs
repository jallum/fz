use super::*;
use crate::any_value::AnyValueRef;
use crate::heap::{Footprint, GcStats, Heap, SchemaRegistry, StubCounts, StubSite, pool_footprint};
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
        gift_roots: 2,
    };
    assert_eq!(
        line(RuntimeEvent::SendProbe(&probe)),
        r#"{"name":["fz","runtime","send","probe"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"outcome":"miss","receiver":2,"reductions":-7,"gift_bytes":80,"gift_blocks":1,"gift_roots":2}}"#
    );
}

/// A heap whose tip holds one live list cell, so a collection leaves a
/// from-space of one 4096-byte block and one old block.
fn heap_with_one_live_cell() -> (Heap, Vec<AnyValueRef>) {
    let mut heap = Heap::new(4096, crate::bits::bits_test::fresh_registry());
    let cell = heap.alloc_list_cons_int(1, AnyValueRef::empty_list()).unwrap();
    (heap, vec![cell])
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
    let stats = GcStats {
        copied_objects: 6,
        copied_bytes: 288,
        live_bytes: 288,
        young_bytes: 3072,
        young_budget: 2048,
        received_bytes: 1024,
        young_binary_bytes: 300000,
        binary_budget: 262144,
        to_space_guess_bytes: 1024,
        blocks_after: 2,
        stub_visits: 7,
        stubs_made,
        binrefs_made,
        stubs_survived,
        ..GcStats::default()
    };
    let (mut heap, mut roots) = heap_with_one_live_cell();
    let mut collected_stats = GcStats::default();
    let collected = heap.collect(&mut roots, &mut collected_stats);
    let collection = Collection {
        pid: 5,
        boundary: CollectionBoundary::Park,
    };

    let written = line(RuntimeEvent::Gc(collection, &stats, collected.heap()));

    drop(collected);
    let Footprint {
        in_use_bytes,
        idle_bytes,
        ..
    } = pool_footprint();
    assert_eq!(
        written,
        format!(
            r#"{{"name":["fz","runtime","gc"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{{}},"metadata":{{"pid":5,"boundary":"park","generation":"minor","copied_objects":6,"copied_bytes":288,"live_bytes":288,"young_bytes":3072,"young_budget":2048,"received_bytes":1024,"young_binary_bytes":300000,"binary_budget":262144,"from_space_capacity_bytes":4096,"blocks_released":1,"to_space_guess_bytes":1024,"to_space_capacity_bytes":1024,"blocks_after":2,"stub_visits":7,"in_use_bytes":{in_use_bytes},"idle_bytes":{idle_bytes},"stubs_made":{{"appended_in_place":3,"window_of_buffer":0,"grown_buffer":0,"filled_buffer":0,"message_copy":1,"static_literal":0}},"binrefs_made":{{"appended_in_place":0,"window_of_buffer":0,"grown_buffer":0,"filled_buffer":0,"message_copy":1,"static_literal":0}},"stubs_survived":{{"appended_in_place":1,"window_of_buffer":0,"grown_buffer":0,"filled_buffer":0,"message_copy":0,"static_literal":0}}}}}}"#
        )
    );
}

/// The writer reads the pool while the collection still holds its from-space,
/// and reports the bytes as they stand once it is released: the from-space is
/// no longer in use and rests idle in the pool.
#[test]
fn the_bytes_in_use_and_idle_are_those_of_the_pool_once_the_from_space_is_released() {
    let (mut heap, mut roots) = heap_with_one_live_cell();
    let mut stats = GcStats::default();
    let collected = heap.collect(&mut roots, &mut stats);
    let held = pool_footprint();

    let reported = collected.heap().collected_blocks().footprint_once_released(held);

    drop(collected);
    let released = pool_footprint();
    assert_eq!(reported.in_use_bytes, released.in_use_bytes);
    assert_eq!(reported.idle_bytes, released.idle_bytes);
    assert_eq!(reported.peak_in_use_bytes, released.peak_in_use_bytes);
    assert_eq!(held.in_use_bytes - released.in_use_bytes, 4096, "the from-space block");
}

/// The capacities a collection reports are sums over its blocks, taken when
/// the writer asks: one 4096-byte tip was copied out of, and the copy filled
/// one block of the to-space guess's size.
#[test]
fn the_writer_computes_the_capacities_and_the_block_count_from_the_blocks() {
    let (mut heap, mut roots) = heap_with_one_live_cell();
    let mut stats = GcStats::default();
    let collected = heap.collect(&mut roots, &mut stats);

    let blocks = collected.heap().collected_blocks();

    assert_eq!(blocks.blocks_released(), 1);
    assert_eq!(blocks.from_space_capacity_bytes(), 4096);
    assert_eq!(blocks.to_space_capacity_bytes(), 1024);
    assert_eq!(collected.stats().to_space_guess_bytes, 1024);
    drop(collected);
    assert_eq!(
        heap.collected_blocks().blocks_released(),
        0,
        "the from-space is released with the collection"
    );
}

/// A raise's text is the hook's bytes, read as UTF-8 lossily by the writer: no
/// text is made to carry it, and bytes that are not UTF-8 are replaced.
#[test]
fn a_raise_borrows_the_hooks_bytes_and_the_writer_decodes_them() {
    let kind = b"error";
    let name = b"Elixir.Bad\xFFName";
    let raise = unsafe { Raise::from_hook_args(kind.as_ptr(), kind.len(), name.as_ptr(), name.len(), 2, 96) };
    assert_eq!(
        raise.kind.as_ptr(),
        kind.as_ptr(),
        "the record points at the hook's bytes"
    );
    assert_eq!(
        line(RuntimeEvent::Raise(&raise)),
        "{\"name\":[\"fz\",\"runtime\",\"raise\"],\"time_ns\":12,\"kind\":\"event\",\"span_id\":3,\"parent_span_id\":4,\"measurements\":{},\"metadata\":{\"kind\":\"error\",\"exception\":\"Elixir.Bad\u{FFFD}Name\",\"handler_depth\":2,\"stack_bytes\":96}}"
    );
}

#[test]
fn a_raise_record_made_for_a_listener_reads_back_as_the_raise_it_came_from() {
    let raise = Raise {
        kind: b"error",
        exception: b"Elixir.ArgumentError",
        handler_depth: 1,
        stack_bytes: 8,
    };
    assert_eq!(RaiseRecord::of(&raise).as_raise(), raise);
}

#[test]
fn a_run_end_writes_the_pool_census_the_bytes_in_use_idle_and_at_peak_and_the_trims() {
    let ended = RunEnded {
        pool_outstanding_before_run: 30,
        pool_outstanding_after_run: 30,
        pool_cached_blocks: 1,
        footprint: Footprint {
            in_use_bytes: 9216,
            idle_bytes: 4096,
            peak_in_use_bytes: 20480,
            trims: 7,
            pages_given_back: 96,
        },
    };
    assert_eq!(
        line(RuntimeEvent::RunEnded(ended)),
        r#"{"name":["fz","runtime","run_ended"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"pool_outstanding_before_run":30,"pool_outstanding_after_run":30,"pool_cached_blocks":1,"in_use_bytes":9216,"idle_bytes":4096,"peak_in_use_bytes":20480,"trims":7,"pages_given_back":96}}"#
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
    let used = process.heap.bytes_used();
    assert_eq!(
        line(RuntimeEvent::ProcessExited(&process)),
        format!(
            r#"{{"name":["fz","runtime","process_exited"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{{}},"metadata":{{"pid":1,"process":{{"opaque_type":"fz_runtime::process::Process","bytes_used":{used},"binaries_shared":0,"raises_delivered":0,"reduction_yields":0,"parks":5,"dtors_dispatched":3,"frame_copies":0,"halt_value":-4,"failed":true}}}}}}"#
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

/// A site's line names where the objects were placed, what they are, and how
/// many and how large; a function name is written as a JSON string whatever
/// characters a symbol carries.
#[test]
fn an_allocation_site_writes_its_function_object_count_and_bytes() {
    let site = crate::alloc_site::AllocSiteCount {
        function: r#"Main."odd"/2__e7"#.to_owned(),
        kind: crate::heap::HeapAllocKind::Continuation,
        placed: crate::heap::AllocStat {
            allocs: 1000,
            bytes: 48_000,
        },
    };
    assert_eq!(
        line(RuntimeEvent::AllocSite(&site)),
        r#"{"name":["fz","runtime","alloc_site"],"time_ns":12,"kind":"event","span_id":3,"parent_span_id":4,"measurements":{},"metadata":{"function":"Main.\"odd\"/2__e7","object":"continuation","allocs":1000,"bytes":48000}}"#
    );
}
