//! A function's input demand is built from its callees' answers, each read
//! once, instead of from a walk over every callee's body.
//!
//! When a body hands a parameter unchanged to a callee, the callee's demand at
//! that position is part of the caller's. So `DeriveInputDemand(f)` joins its
//! own dispatch mask with the `InputDemand` of each callee it forwards to.
//! There are three ways to meet such a callee:
//!
//! - its answer has concluded: read it, once;
//! - it is already waiting on `f`: the two are one cycle, so `f` reads the
//!   callee's body facts and solves both in the same run;
//! - otherwise: wait for its answer.
//!
//! On a chain `main -> f -> g -> h` each caller runs once to learn which
//! answer it needs and once when that answer arrives, and the leaf runs once:
//!
//! | job                     | runs | reads per run          |
//! |-------------------------|------|------------------------|
//! | `f`, `g`                | 2    | 3, then 4 (the answer) |
//! | `h`, `main`, `def/1`    | 1    | 3                      |
//!
//! Every program also derives the `def/1` macro root's demand first; programs
//! that use Kernel arithmetic also derive `defp/1`'s.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use super::drive::DependencyKey;
use super::facts::FactUse;
use super::identity::FunctionId;
use super::world::{JobCompletion, World};
use super::{CodeSubmission, ExecutableNeed, FactKey, Job, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

/// One `DeriveInputDemand` completion: whose demand it derived, how many facts
/// its job stands on after the run, and the function-scoped ones by name.
#[derive(Debug, Clone)]
struct DemandRun {
    function: String,
    read_count: usize,
    reads: Vec<DemandRead>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DemandRead {
    fact: &'static str,
    of: String,
    concluded: bool,
}

#[derive(Default)]
struct DemandWork {
    runs: Vec<DemandRun>,
    answers: BTreeMap<String, String>,
}

fn function_name(world: &World, function: FunctionId) -> String {
    let denotation = world.function_ref(function);
    format!("{}/{}", denotation.display_name(), denotation.arity)
}

/// Module-qualified, so a protocol callback (`Enumerable.reduce_while/3`)
/// never collides in a name census with the `Enum` helper that calls it
/// (`Enum.reduce_while/3`).
fn qualified_function_name(world: &World, function: FunctionId) -> String {
    let denotation = world.function_ref(function);
    match world.module_denotation(denotation.module) {
        Some(module) => format!("{module}.{}/{}", denotation.display_name(), denotation.arity),
        None => format!("{}/{}", denotation.display_name(), denotation.arity),
    }
}

fn demand_read(world: &World, read: &FactUse<DependencyKey>) -> Option<DemandRead> {
    let DependencyKey::Fact(fact) = read.fact() else {
        return None;
    };
    let (kind, function) = match fact {
        FactKey::StaticCallees(function) => ("StaticCallees", *function),
        FactKey::EntryDispatch(function) => ("EntryDispatch", *function),
        FactKey::LoweredBody(function) => ("LoweredBody", *function),
        FactKey::FunctionDefined(function) => ("FunctionDefined", *function),
        FactKey::InputDemand(function) => ("InputDemand", *function),
        _ => return None,
    };
    Some(DemandRead {
        fact: kind,
        of: function_name(world, function),
        concluded: matches!(read, FactUse::Concluded(_)),
    })
}

fn input_demand_work(source: &str) -> DemandWork {
    let tel = ConfiguredTelemetry::new();
    let work: Rc<RefCell<DemandWork>> = Rc::default();
    let observed = Rc::clone(&work);
    tel.attach_raw_event2::<World, JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, world, completion| {
            let Job::DeriveInputDemand(function) = completion.job else {
                return;
            };
            let name = function_name(world, function);
            let answered = completion.step.blocked.is_empty();
            let standing = world.work_graph.reads(&completion.job);
            let read_count = standing.len();
            let mut reads = standing
                .iter()
                .filter_map(|read| demand_read(world, read))
                .collect::<Vec<_>>();
            reads.sort_by(|left, right| (left.fact, &left.of).cmp(&(right.fact, &right.of)));
            let mut work = observed.borrow_mut();
            if answered && let Some(demand) = world.input_demand(function) {
                work.answers.insert(name.clone(), format!("{demand:?}"));
            }
            work.runs.push(DemandRun {
                function: name,
                read_count,
                reads,
            });
        },
    );

    run_main(tel, source);
    std::mem::take(&mut *work.borrow_mut())
}

/// Compiles and runs `source`'s `main/0`, with `tel`'s observers attached.
fn run_main(tel: ConfiguredTelemetry, source: &str) {
    let mut compiler = super::Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("input_demand_answers.fz".to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .run_root_interp(root)
        .expect("the program should compile and run");
}

fn runs_of<'a>(work: &'a DemandWork, function: &str) -> Vec<&'a DemandRun> {
    work.runs.iter().filter(|run| run.function == function).collect()
}

fn body_reads_of_other_functions(work: &DemandWork) -> Vec<(String, DemandRead)> {
    work.runs
        .iter()
        .flat_map(|run| {
            run.reads
                .iter()
                .filter(|read| read.fact != "InputDemand" && read.of != run.function)
                .map(|read| (run.function.clone(), read.clone()))
        })
        .collect()
}

fn total_reads(work: &DemandWork) -> usize {
    work.runs.iter().map(|run| run.read_count).sum()
}

fn most_reads_in_one_run(work: &DemandWork) -> usize {
    work.runs.iter().map(|run| run.read_count).max().unwrap_or(0)
}

#[test]
fn a_chain_reads_each_callee_answer_once_and_no_callee_body() {
    // `junk` is threaded through unread: carrying a list keeps every row off
    // R1's self-keyed shortcut (a ground int argument alone answers its own
    // `Recursive`/`InputDemand` with no fact asked at all), so the chain's
    // demand is genuinely derived here.
    let work = input_demand_work(
        "def h(x, junk), do: x\ndef g(x, junk), do: h(x, junk)\ndef f(x, junk), do: g(x, junk)\ndef main(), do: f(1, [1])\n",
    );
    let counts = ["f/2", "g/2", "h/2", "main/0"].map(|function| (function, runs_of(&work, function).len()));
    // `main/0` takes no arguments, so it is self-keyed by construction (R1):
    // nothing ever calls it, so nothing ever demands its own `InputDemand`.
    assert_eq!(counts, [("f/2", 2), ("g/2", 2), ("h/2", 1), ("main/0", 0)]);
    assert_eq!(
        body_reads_of_other_functions(&work),
        Vec::new(),
        "an acyclic caller reads its callees' answers, never their bodies"
    );
    let f = runs_of(&work, "f/2");
    assert!(
        f[1].reads.contains(&DemandRead {
            fact: "InputDemand",
            of: "g/2".to_string(),
            concluded: true,
        }),
        "f reads g's answer once it has concluded: {:?}",
        f[1].reads
    );
    // main/0's own `InputDemand` is never derived, so its run and its reads
    // are not among these: five runs total (f twice, g twice, h once).
    assert_eq!((total_reads(&work), most_reads_in_one_run(&work)), (17, 4));
}

/// `ping` and `pong` hand `x` back and forth, so their demands are one
/// cycle. `ping` runs first and waits for `pong`; `pong` finds `ping` waiting
/// on it and reads `ping`'s body facts. `pong` also passes `n` unchanged to
/// `Kernel.-/2` in `n - 1`, so its first run waits for that answer, and `-`
/// for its four arithmetic externs. Its second run walks `ping` again and
/// solves the pair; `ping` then reads `pong`'s answer.
/// By hand: ping 2, pong 2, `-` 2, each extern 1.
#[test]
fn a_forwarding_cycle_is_solved_by_the_callee_that_is_waited_on() {
    // `junk` is threaded through unread: carrying a list keeps every row off
    // R1's self-keyed shortcut (ground int/atom arguments alone answer their
    // own `Recursive`/`InputDemand` with no fact asked at all), so the cycle's
    // demand is genuinely derived here.
    let work = input_demand_work(
        "def ping(n, x, junk), do: pong(n, x, junk)\ndef pong(0, x, junk), do: x\ndef pong(n, x, junk), do: ping(n - 1, x, junk)\ndef main(), do: ping(3, :a, [1])\n",
    );
    assert_eq!(work.answers.get("ping/3"), Some(&PING_ANSWER.to_string()));
    assert_eq!(work.answers.get("pong/3"), Some(&PONG_ANSWER.to_string()));
    let counts = ["ping/3", "pong/3", "-/2"].map(|function| (function, runs_of(&work, function).len()));
    assert_eq!(counts, [("ping/3", 2), ("pong/3", 2), ("-/2", 2)]);
    let partner_body = ["EntryDispatch", "LoweredBody", "StaticCallees"].map(|fact| DemandRead {
        fact,
        of: "ping/3".to_string(),
        concluded: false,
    });
    let expected = [&partner_body[..], &partner_body[..]]
        .concat()
        .into_iter()
        .map(|read| ("pong/3".to_string(), read))
        .collect::<Vec<_>>();
    assert_eq!(
        body_reads_of_other_functions(&work),
        expected,
        "only the cycle partner's body is read, once in each run of the callee it waits on"
    );
}

/// The answers the whole-cone walk derived for the cycle above, before
/// composition. Composing from answers must not change them. `junk` (slot 2)
/// is never read, matched, or returned, so it carries `Ignore` throughout.
const PING_ANSWER: &str = "InputDemand { local_dispatch: [Ignore, Ignore, Ignore], forwarded_dispatch: \
     [Whole, Ignore, Ignore], returned: [Ignore, Whole, Ignore] }";
const PONG_ANSWER: &str = "InputDemand { local_dispatch: [Whole, Ignore, Ignore], forwarded_dispatch: \
     [Whole, Ignore, Ignore], returned: [Ignore, Whole, Ignore] }";

/// `Enum.take/2` forwards its list and count through a dozen Enum helpers, a
/// protocol callback and its implementation. Reading answers instead of
/// bodies keeps every run small.
///
/// fz-xxd.11: `(76, 264, 8)` -> `(76, 282, 8)`. An extern has no lowered
/// body, so the input-demand walk answers each of the eighteen externs that
/// `+` and `==` name in their clauses as a bodyless leaf, reading
/// `FunctionDefined` and `ModuleDefined` where it used to read the stand-in
/// body's `EntryDispatch`. Those externs are named by clauses dispatch never
/// selects here; dispatch-aware static callees remove them from this walk.
#[test]
fn enum_take_derives_input_demand_proportionally() {
    let work = input_demand_work("def main(), do: Enum.take([1, 2, 3], 2)\n");
    assert_eq!(
        (work.runs.len(), total_reads(&work), most_reads_in_one_run(&work)),
        (45, 149, 6)
    );
}

/// `Enum.all?/1` reaches the protocol callback `Enumerable.reduce_while/3`.
/// The callback's own question is which implementation to reach, answered
/// from the receiver's type alone -- it depends on no other fact, so its
/// answer is published once. What an implementation asks of its inputs is
/// asked where it is called, not by the callback, so the callback's demand
/// is `Whole` on the receiver and nothing else.
///
/// So no function's `InputDemand` is revised after it is published, even
/// though `Enumerable.List` is defined only after the callback's answer is.
/// An answer that joined the implementations defined so far would be
/// revised when it lands, and so would its callers `Enum.reduce_while/3`
/// and `Enum.all?/1`.
#[test]
fn a_protocol_callback_s_input_demand_is_published_once() {
    let work = revised_input_demand_work("def main(), do: Enum.all?([1])\n");
    assert_eq!(
        work.revised,
        Vec::<String>::new(),
        "no function's InputDemand should be revised after it is published: {:?}",
        work.revised
    );
    assert_eq!(
        work.answers.get("Enumerable.reduce_while/3"),
        Some(
            &"InputDemand { local_dispatch: [Whole, Ignore, Ignore], \
              forwarded_dispatch: [Whole, Ignore, Ignore], returned: [Ignore, Ignore, Ignore] }"
                .to_string()
        ),
        "the callback asks Whole of its receiver and nothing of its other slots"
    );
}

/// Every `InputDemand` publication that replaced an earlier one, and each
/// function's final answer.
#[derive(Default)]
struct RevisionWork {
    /// Every function whose `InputDemand` was published more than once, one
    /// entry per revision after the first.
    revised: Vec<String>,
    answers: BTreeMap<String, String>,
}

fn revised_input_demand_work(source: &str) -> RevisionWork {
    let tel = ConfiguredTelemetry::new();
    let work: Rc<RefCell<RevisionWork>> = Rc::default();
    let observed = Rc::clone(&work);
    tel.attach_raw_event2::<World, JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, world, completion| {
            let Job::DeriveInputDemand(function) = completion.job else {
                return;
            };
            let name = qualified_function_name(world, function);
            let mut work = observed.borrow_mut();
            for change in &completion.step.changed {
                let DependencyKey::Fact(FactKey::InputDemand(revised)) = &change.key else {
                    continue;
                };
                if change.old_revision.is_some() {
                    work.revised.push(qualified_function_name(world, *revised));
                }
            }
            if completion.step.blocked.is_empty()
                && let Some(demand) = world.input_demand(function)
            {
                work.answers.insert(name, format!("{demand:?}"));
            }
        },
    );

    run_main(tel, source);
    std::mem::take(&mut *work.borrow_mut())
}
