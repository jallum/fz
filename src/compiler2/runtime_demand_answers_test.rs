//! A runtime-demand answer is published once, when everything it depends on
//! is known, and no run is ever wasted on an answer that later moves.
//!
//! Runtime demand flows both ways through a call. The caller decides how much
//! of the callee's result it needs (down), and the callee decides how much of
//! each argument it needs (up). One `DeriveRuntimeDemand` job per executable
//! computes both, so on a chain `main -> f -> g -> h` each caller runs once to
//! send its demand down and once more when its callee's argument demand comes
//! back up, and the leaf runs once:
//!
//! | program               | by hand                   |
//! |-----------------------|---------------------------|
//! | `main -> g`           | main 2, g 1         = 3   |
//! | `main -> g -> h`      | main 2, g 2, h 1    = 5   |
//! | `main -> f -> g -> h` | main 2, f 2, g 2, h 1 = 7 |
//! | `main: k(h(1))`       | main 3, k 1, h 1    = 5   |
//!
//! In `k(h(1))` the demand sent down to `h` is however much `k` needs of its
//! argument, so it waits for `k`'s answer: a downward answer can depend on an
//! upward one, and the rule is per answer, not per direction.
//!
//! A run that is still waiting publishes what it knows of its own upward
//! answer, marking what it does not know yet. Only a partner in a cycle reads
//! that; everyone else waits until the answer is concluded. So the measure of
//! waste is a *shift wake*: a run caused by a change to something the job
//! already consumed. Acyclic programs have none, and their demand facts
//! settle as they are published, never at the drain.
//!
//! Every count below adds the one run of the `def/1` macro root's own
//! executable, which every program compiles first; programs that use Kernel
//! arithmetic also compile the `defp/1` root.

use std::cell::RefCell;
use std::rc::Rc;

use super::drive::DependencyKey;
use super::scheduler::AppliedStep;
use super::world::{JobCompletion, World};
use super::{CodeSubmission, ExecutableNeed, FactKey, Job, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

#[derive(Default)]
struct DemandWork {
    runs: usize,
    shift_wakes: usize,
    settled_at_drain: Vec<String>,
}

fn is_runtime_demand_fact(fact: &DependencyKey) -> bool {
    matches!(
        fact,
        DependencyKey::Fact(
            FactKey::RuntimeDemand(_) | FactKey::RuntimeDemandInputs(_) | FactKey::RuntimeDemandInput(_)
        )
    )
}

fn count_shift_wakes(work: &mut DemandWork, step: &AppliedStep<Job, DependencyKey>) {
    work.shift_wakes += step
        .wakes
        .iter()
        .filter(|wake| wake.shift && matches!(wake.job, Job::DeriveRuntimeDemand(_)))
        .count();
}

fn runtime_demand_work(source: &str, expected: i64) -> DemandWork {
    let tel = ConfiguredTelemetry::new();
    let work: Rc<RefCell<DemandWork>> = Rc::default();
    let observed = Rc::clone(&work);
    tel.attach_raw_event2::<World, JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, _world, completion| {
            let mut work = observed.borrow_mut();
            if matches!(completion.job, Job::DeriveRuntimeDemand(_)) {
                work.runs += 1;
            }
            count_shift_wakes(&mut work, &completion.step);
        },
    );
    let observed = Rc::clone(&work);
    tel.attach_raw_event1::<AppliedStep<Job, DependencyKey>, _>(
        &["fz", "compiler2", "work_graph", "quiesced"],
        move |_, _, _, step| {
            let mut work = observed.borrow_mut();
            count_shift_wakes(&mut work, step);
            work.settled_at_drain.extend(
                step.changed
                    .iter()
                    .filter(|change| is_runtime_demand_fact(&change.key) && change.new_settled && !change.old_settled)
                    .map(|change| format!("{:?}", change.key)),
            );
        },
    );

    let mut compiler = super::Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("runtime_demand_answers.fz".to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let result = compiler
        .run_root_interp(root)
        .expect("the program should compile and run");
    assert_eq!(result, expected);
    std::mem::take(&mut *work.borrow_mut())
}

fn assert_acyclic_answers_settle_as_published(source: &str, expected: i64, expected_runs: usize) {
    let work = runtime_demand_work(source, expected);
    assert_eq!(
        (work.runs, work.shift_wakes),
        (expected_runs, 0),
        "expected {expected_runs} DeriveRuntimeDemand runs and no shift wakes"
    );
    assert!(
        work.settled_at_drain.is_empty(),
        "an acyclic program's demand facts settle as they are published, not at the drain: {:#?}",
        work.settled_at_drain,
    );
}

#[test]
fn a_single_call_sends_demand_down_then_reads_it_back_up() {
    assert_acyclic_answers_settle_as_published("def g(x), do: x\ndef main(), do: g(1)\n", 1, 3 + 1);
}

#[test]
fn a_three_level_chain_derives_each_answer_once() {
    assert_acyclic_answers_settle_as_published("def h(x), do: x\ndef g(x), do: h(x)\ndef main(), do: g(1)\n", 1, 5 + 1);
}

#[test]
fn a_four_level_chain_derives_each_answer_once() {
    assert_acyclic_answers_settle_as_published(
        "def h(x), do: x\ndef g(x), do: h(x)\ndef f(x), do: g(x)\ndef main(), do: f(1)\n",
        1,
        7 + 1,
    );
}

#[test]
fn demand_sent_down_waits_for_the_consumer_of_the_result() {
    assert_acyclic_answers_settle_as_published("def h(x), do: x\ndef k(y), do: y\ndef main(), do: k(h(1))\n", 1, 5 + 1);
}

/// `f` matches `n` against `0`, so it needs all of `n` whatever `g` says: an
/// integer cannot be needed more than whole. Its answer is earned before
/// anyone else answers, `g` reads it as `f`'s partner, and the demand `f`
/// sends into Kernel arithmetic for `n - 1` is sent once, already final.
/// By hand: main 2, f 3, g 1, and the arithmetic chain 11, plus both roots.
#[test]
fn a_recursive_pair_sends_demand_out_of_the_cycle_once() {
    let work = runtime_demand_work(
        "def f(0), do: 0\ndef f(n), do: g(n - 1)\ndef g(n), do: f(n)\ndef main(), do: f(3)\n",
        0,
    );
    assert_eq!((work.runs, work.shift_wakes), (19, 0));
}

/// A cycle made of closure calls, which the static call graph cannot see:
/// `step` calls the lambda it was given, and the lambda calls `step`. The
/// lambda passes both of its arguments straight to `step`, so the first
/// answer it can give says nothing about them, and `step`'s second arrow
/// climbs once when the real answer arrives.
/// By hand: main 2, step 2 + 2 (two arrows), lambda 2, plus the root.
#[test]
fn a_closure_cycle_climbs_once() {
    let work = runtime_demand_work(
        "def step(k, []), do: 0\ndef step(k, [_ | t]), do: k.(k, t)\ndef main(), do: step(fn(kk, m) -> step(kk, m) end, [1, 2])\n",
        0,
    );
    assert_eq!((work.runs, work.shift_wakes), (9, 1));
}

/// `acc` is passed back to `loop` and nothing else, so its demand is
/// `acc = acc`: never needed. `loop` works out its own upward answer before
/// the demand it sends down, so the arithmetic for `n - 1` is asked once, for
/// all of its result.
/// By hand: main 2, loop 2, and the arithmetic chain 11, plus both roots.
#[test]
fn a_self_call_sends_demand_down_from_its_own_answer() {
    let work = runtime_demand_work(
        "def loop(acc, 0), do: 0\ndef loop(acc, n), do: loop(acc, n - 1)\ndef main(), do: loop(1, 3)\n",
        0,
    );
    assert_eq!((work.runs, work.shift_wakes), (17, 0));
}
