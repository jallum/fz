//! The runtime's sleep and raise telemetry, observed through the real `run` (JIT)
//! and `interp` doors.

use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;
use fz_runtime::telemetry::SCHEDULER_SLEPT;
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

// ---------------------------------------------------------------------------
// Raises, observed through the same two doors.

use super::{ExitRecord, ProcessExitCapture};
use fz_runtime::telemetry::{RAISE, Raise};

/// Runs `source` through `door` and returns every raise the runtime reported
/// with the main process's exit record.
fn raises_while_running(source: &str, door: Door) -> (Vec<Raise>, ExitRecord) {
    let tel = ConfiguredTelemetry::new();
    let raises = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&raises);
    tel.attach_raw_event1::<Raise, _>(&RAISE, move |_, _, _, raise| sink.borrow_mut().push(raise.clone()));
    let exits = ProcessExitCapture::new();
    exits.install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.set_output(crate::exec::runtime::DbgCapture::new().sink());
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/raise.fz".to_string()),
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
    .unwrap_or_else(|error| panic!("raise fixture should run: {error}"));
    let main_exit = exits.last().expect("the main process exits");
    (raises.take(), main_exit)
}

const NESTED_RESCUE: &str = include_str!("../../fixtures/00821_a_nested_try_rescues_at_the_innermost_handler.fz");
const AFTER_THEN_RESCUE: &str =
    include_str!("../../fixtures/00833_an_after_runs_on_a_raise_and_the_outer_rescue_sees_the_original.fz");
const RAISING_LOOP: &str =
    include_str!("../../fixtures/00826_a_loop_that_raises_and_rescues_every_iteration_runs_to_the_end.fz");
const ALLOCATING_TRY_BODY: &str =
    include_str!("../../fixtures/00831_a_handler_outlives_the_yields_and_collections_of_its_try_body.fz");

/// A raise under two tries is one event naming its kind, its exception and the
/// two handlers that could take it, and the exit record counts the delivery.
fn assert_one_raise_under_two_handlers(door: Door) {
    let (raises, exit) = raises_while_running(NESTED_RESCUE, door);
    assert_eq!(
        raises,
        vec![Raise {
            kind: "error".to_string(),
            exception: "Elixir.ArgumentError".to_string(),
            handler_depth: 2,
        }]
    );
    assert_eq!(exit.raises_delivered, 1);
    assert!(!exit.failed);
}

#[test]
fn the_jit_reports_a_raise_with_its_handler_depth_and_counts_the_delivery() {
    assert_one_raise_under_two_handlers(Door::Jit);
}

#[test]
fn the_interpreter_reports_a_raise_with_its_handler_depth_and_counts_the_delivery() {
    assert_one_raise_under_two_handlers(Door::Interp);
}

/// A raise through an `after` is two events: the original, under the `after`
/// handler and the enclosing rescue, then the `after` handler's re-raise of
/// the same exception, under the rescue alone. Both are delivered.
fn assert_after_re_raises_the_original(door: Door) {
    let (raises, exit) = raises_while_running(AFTER_THEN_RESCUE, door);
    let raise_at = |handler_depth| Raise {
        kind: "error".to_string(),
        exception: "Elixir.ArgumentError".to_string(),
        handler_depth,
    };
    assert_eq!(raises, vec![raise_at(2), raise_at(1)]);
    assert_eq!(exit.raises_delivered, 2);
    assert!(!exit.failed);
}

#[test]
fn the_jit_re_raises_through_an_after_to_the_enclosing_rescue() {
    assert_after_re_raises_the_original(Door::Jit);
}

#[test]
fn the_interpreter_re_raises_through_an_after_to_the_enclosing_rescue() {
    assert_after_re_raises_the_original(Door::Interp);
}

/// A loop that raises and rescues on every iteration delivers every raise to
/// its one handler.
fn assert_every_iteration_delivers(door: Door) -> ExitRecord {
    let (raises, exit) = raises_while_running(RAISING_LOOP, door);
    assert_eq!(raises.len(), 100_000);
    assert!(raises.iter().all(|raise| raise.handler_depth == 1));
    assert_eq!(exit.raises_delivered, 100_000);
    assert!(!exit.failed);
    exit
}

/// A delivered handler runs inside the same quantum, so the loop's reductions
/// accumulate and the scheduler gets its turn through the ordinary reduction
/// yield.
#[test]
fn the_jit_delivers_every_raise_of_a_rescuing_loop_and_yields() {
    let exit = assert_every_iteration_delivers(Door::Jit);
    assert!(exit.reduction_yields >= 1, "the loop yields to the scheduler: {exit:?}");
}

/// A delivered raise unwinds the machine frames between its `try` and the raise
/// before the handler runs, so a loop that raises on every iteration needs the
/// same stack for its hundred-thousandth raise as for its first. The thread's
/// stack is far smaller than a quantum of orphaned frames would need.
#[test]
fn the_jit_runs_a_raising_loop_on_a_small_stack() {
    let small_stack = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let (raises, exit) = raises_while_running(RAISING_LOOP, Door::Jit);
            assert_eq!(raises.len(), 100_000);
            assert_eq!(exit.raises_delivered, 100_000);
        })
        .expect("spawn the small-stack thread");
    small_stack
        .join()
        .expect("the raising loop finishes on a 256 KiB stack");
}

#[test]
fn the_interpreter_delivers_every_raise_of_a_rescuing_loop() {
    assert_every_iteration_delivers(Door::Interp);
}

/// A try body that spends more than a quantum's reductions and conses past the
/// collector's threshold yields and is collected with its handler on the stack;
/// the raise at its end still reaches that handler. Two hundred thousand cons
/// cells were allocated and almost none are live at the end, so the collector
/// ran while the handlers were roots.
#[test]
fn the_jit_keeps_a_handler_across_the_yields_and_collections_of_its_try_body() {
    let (raises, exit) = raises_while_running(ALLOCATING_TRY_BODY, Door::Jit);
    assert_eq!(raises.len(), 100);
    assert_eq!(exit.raises_delivered, 100);
    assert!(exit.reduction_yields >= 1, "the body yields inside its try: {exit:?}");
    assert!(
        exit.live_count < 1_000,
        "the collector ran under the handlers: {exit:?}"
    );
    assert!(!exit.failed);
}
