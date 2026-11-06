//! The scheduling core's sleep telemetry, observed through the real `run` (JIT)
//! and `interp` doors.

use super::SCHEDULER_SLEPT;
use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;
use std::cell::RefCell;
use std::rc::Rc;
use std::time::Duration;

#[derive(Clone, Copy)]
enum Door {
    Jit,
    Interp,
}

/// Runs `source` through `door` and returns the wait of every scheduler sleep.
fn sleeps_while_running(source: &str, door: Door) -> Vec<Duration> {
    let tel = ConfiguredTelemetry::new();
    let slept = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&slept);
    tel.attach_raw_event1::<Duration, _>(&SCHEDULER_SLEPT, move |_, _, _, wait| sink.borrow_mut().push(*wait));

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/scheduler_sleep.fz".to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    match door {
        Door::Jit => compiler.run_root_jit(root).map(|_| ()),
        Door::Interp => compiler.run_root_interp(root).map(|_| ()),
    }
    .unwrap_or_else(|error| panic!("scheduler sleep fixture should run: {error}"));
    slept.take()
}

const LONE_TIMEOUT: &str = include_str!("../../fixtures/00687_a_receive_after_times_out_with_an_empty_mailbox.fz");
const CANCELLED_TIMEOUT: &str =
    include_str!("../../fixtures/00692_a_message_that_arrives_first_cancels_the_timeout.fz");

/// With nothing else able to run, the 10ms timer is the only work left: the
/// core sleeps for it once instead of calling the program idle.
fn assert_sleeps_once_for_the_lone_timeout(door: Door) {
    let slept = sleeps_while_running(LONE_TIMEOUT, door);
    assert_eq!(slept.len(), 1, "one sleep for the one pending timer: {slept:?}");
    assert!(
        slept[0] <= Duration::from_millis(10),
        "waits no longer than the timeout"
    );
}

#[test]
fn the_jit_sleeps_for_a_lone_receive_timeout() {
    assert_sleeps_once_for_the_lone_timeout(Door::Jit);
}

#[test]
fn the_interpreter_sleeps_for_a_lone_receive_timeout() {
    assert_sleeps_once_for_the_lone_timeout(Door::Interp);
}

#[test]
fn a_message_that_beats_the_timer_cancels_it_so_nothing_sleeps() {
    for door in [Door::Jit, Door::Interp] {
        assert!(sleeps_while_running(CANCELLED_TIMEOUT, door).is_empty());
    }
}
