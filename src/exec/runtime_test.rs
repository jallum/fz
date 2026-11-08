//! The runtime's sleep and raise telemetry, observed through the real `run` (JIT)
//! and `interp` doors.

use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission, RunFailure};
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
    let (raises, exit, ran) = observe_run(source, door);
    ran.unwrap_or_else(|error| panic!("raise fixture should run: {error}"));
    (raises, exit)
}

/// Runs `source` through `door` and returns how the run ended, with every raise
/// reported and the main process's exit record.
fn observe_run(source: &str, door: Door) -> (Vec<Raise>, ExitRecord, Result<(), RunFailure>) {
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
    let ran = match door {
        Door::Jit => compiler.run_root_jit(root).map(|_| ()),
        Door::Interp => compiler.run_root_interp(root).map(|_| ()),
    };
    let main_exit = exits.last().expect("the main process exits");
    (raises.take(), main_exit, ran)
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
        without_stack_depth(raises),
        vec![Raise {
            kind: "error".to_string(),
            exception: "Elixir.ArgumentError".to_string(),
            handler_depth: 2,
            stack_bytes: 0,
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
        stack_bytes: 0,
    };
    assert_eq!(without_stack_depth(raises), vec![raise_at(2), raise_at(1)]);
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
    assert_eq!(raises.len(), 10_000);
    assert!(raises.iter().all(|raise| raise.handler_depth == 1));
    assert_eq!(exit.raises_delivered, 10_000);
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

/// A handler resumes from the quantum entry, so a loop that raises on every
/// iteration repeats its depth instead of rising: every one of the hundred
/// thousand raises is delivered at one of a few depths, the entry path (the
/// first iteration), the resumed-handler path and the resumed-yield paths.
#[test]
fn the_jit_delivers_every_raise_of_a_loop_at_a_few_stack_depths() {
    let (raises, exit) = raises_while_running(RAISING_LOOP, Door::Jit);
    assert_eq!(raises.len(), 10_000);
    assert_eq!(exit.raises_delivered, 10_000);
    assert!(
        distinct_depths(&raises) <= MOST_DEPTHS_OF_A_RAISING_LOOP,
        "the depth repeats: {:?}",
        depths_seen(&raises)
    );
}

#[test]
fn the_interpreter_delivers_every_raise_of_a_rescuing_loop() {
    assert_every_iteration_delivers(Door::Interp);
}

/// The interpreter's handler also resumes from its quantum entry, so its
/// ten thousand raises are delivered at a few depths, not a rising run.
#[test]
fn the_interpreter_delivers_every_raise_of_a_loop_at_a_few_stack_depths() {
    let (raises, _) = raises_while_running(RAISING_LOOP, Door::Interp);
    assert_eq!(raises.len(), 10_000);
    assert!(
        distinct_depths(&raises) <= MOST_DEPTHS_OF_A_RAISING_LOOP,
        "the depth repeats: {:?}",
        depths_seen(&raises)
    );
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

// Kinds and exit statuses.

fn raise_of(kind: &str, depth: usize) -> Raise {
    Raise {
        kind: kind.to_string(),
        exception: String::new(),
        handler_depth: depth,
        stack_bytes: 0,
    }
}

/// The records with their machine-stack depth zeroed, for tests that compare
/// what was raised and not where the machine stack stood.
fn without_stack_depth(raises: Vec<Raise>) -> Vec<Raise> {
    raises
        .into_iter()
        .map(|raise| Raise {
            stack_bytes: 0,
            ..raise
        })
        .collect()
}

fn depths_seen(raises: &[Raise]) -> Vec<usize> {
    let mut seen: Vec<usize> = raises.iter().map(|raise| raise.stack_bytes).collect();
    seen.sort_unstable();
    seen.dedup();
    seen
}

/// The depths a raising loop is delivered at: the entry path, the
/// resumed-handler path and the resumed-yield paths. A loop that sank deeper
/// with each iteration would show hundreds.
const MOST_DEPTHS_OF_A_RAISING_LOOP: usize = 4;

/// How many different machine-stack depths a run's raises were delivered at.
fn distinct_depths(raises: &[Raise]) -> usize {
    raises
        .iter()
        .map(|raise| raise.stack_bytes)
        .collect::<std::collections::BTreeSet<_>>()
        .len()
}

/// A raise whose depth is `stack_bytes`, for exercising the depth counting.
fn raise_at_depth(stack_bytes: usize) -> Raise {
    Raise {
        stack_bytes,
        ..raise_of("error", 1)
    }
}

/// The depth count tells a loop that repeats its depth from one that sinks
/// deeper with each iteration, which is the difference the loop tests rely on.
#[test]
fn the_depth_count_tells_a_repeating_loop_from_a_sinking_one() {
    let sinking: Vec<_> = (0..1000).map(|i| raise_at_depth(100 + 40 * i)).collect();
    let repeating: Vec<_> = (0..1000).map(|i| raise_at_depth(100 + 40 * (i % 3))).collect();
    assert_eq!(distinct_depths(&sinking), 1000);
    assert_eq!(distinct_depths(&repeating), 3);
}

/// A throw and an exit each reach the handler as one raise event naming their
/// kind, and neither fails the process.
fn assert_throw_and_exit_report_their_kinds(door: Door) {
    let source = "def main() do\n  try do\n    throw(:ball)\n  catch\n    v -> v\n  end\n  try do\n    exit(:gone)\n  catch\n    :exit, r -> r\n  end\nend\n";
    let (raises, exit, ran) = observe_run(source, door);
    assert_eq!(ran, Ok(()));
    assert_eq!(
        without_stack_depth(raises),
        vec![raise_of("throw", 1), raise_of("exit", 1)]
    );
    assert_eq!(exit.raises_delivered, 2);
    assert!(!exit.failed);
}

#[test]
fn the_jit_reports_a_throw_and_an_exit_with_their_kinds() {
    assert_throw_and_exit_report_their_kinds(Door::Jit);
}

#[test]
fn the_interpreter_reports_a_throw_and_an_exit_with_their_kinds() {
    assert_throw_and_exit_report_their_kinds(Door::Interp);
}

/// How a main process that ends by an uncaught raise ends the run: the status
/// Elixir's CLI gives it, and whether the exit record calls it a failure.
fn assert_main_status(door: Door, body: &str, ends: Result<(), RunFailure>, failed: bool) {
    let source = format!("def main() do\n  {body}\nend\n");
    let (_, exit, ran) = observe_run(&source, door);
    assert_eq!(ran, ends, "{body}");
    assert_eq!(exit.failed, failed, "{body}");
}

fn assert_main_statuses_follow_the_cli(door: Door) {
    assert_main_status(door, "exit(:normal)", Ok(()), false);
    assert_main_status(door, "exit(:shutdown)", Ok(()), false);
    assert_main_status(door, "exit({:shutdown, 0})", Ok(()), false);
    assert_main_status(door, "exit({:shutdown, 7})", Err(RunFailure::MainExited(7)), true);
    assert_main_status(door, "exit({:shutdown, 1})", Err(RunFailure::MainFailed), true);
    assert_main_status(door, "exit(:boom)", Err(RunFailure::MainFailed), true);
    assert_main_status(door, "throw(:ball)", Err(RunFailure::MainFailed), true);
    assert_main_status(door, "raise \"boom\"", Err(RunFailure::MainFailed), true);
}

#[test]
fn the_jit_ends_main_with_the_status_of_its_uncaught_raise() {
    assert_main_statuses_follow_the_cli(Door::Jit);
}

#[test]
fn the_interpreter_ends_main_with_the_status_of_its_uncaught_raise() {
    assert_main_statuses_follow_the_cli(Door::Interp);
}
