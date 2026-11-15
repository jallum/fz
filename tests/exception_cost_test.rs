//! What the exception facility costs a compile, counted in jobs.
//!
//! A program that can raise pays a fixed amount once: its entry runs `main`
//! under the handler that words an uncaught raise. Beyond that the cost
//! follows what the program says about exceptions and nothing else: a function
//! that neither raises nor handles adds what it would add to a program with no
//! raise in it, and each raise site, each handler and each exception type adds
//! a bounded number of jobs however many there are.
//!
//! The count is the `compiler2.job` spans in `--log-telemetry`.

use std::env::temp_dir;
use std::fs::{File, remove_file, write};
use std::io::{BufRead, BufReader};
use std::process::{Command, id};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");

const JOB_LINE: &str = r#"{"name":["fz","compiler2","job"]"#;
const SPAN_START: &str = r#""kind":"span_start""#;

/// `pick/1` has a clause calling each `name{i}/1`, and `main` calls it with a
/// number no clause but the last matches, so the program compiles every one
/// of them and exits cleanly. `last` is what `main` then does when its
/// argument count is one no run has.
fn program(definitions: &str, name: &str, count: usize, last: &str) -> String {
    let clauses: String = (0..count)
        .map(|i| format!("def pick({i}), do: {name}{i}({i})\n"))
        .collect();
    format!(
        "{definitions}{clauses}def pick(_), do: :ok\n\
         def main() do\n  n = length(System.argv()) + 100\n  pick(n)\n  if n == 0, do: {last}\n  :ok\nend\n"
    )
}

fn plain_functions(count: usize, last: &str) -> String {
    let definitions: String = (0..count).map(|i| format!("def p{i}(x), do: [x, {i}]\n")).collect();
    program(&definitions, "p", count, last)
}

fn raise_sites(count: usize) -> String {
    let definitions: String = (0..count)
        .map(|i| format!("def f{i}(x), do: raise(ArgumentError, \"bad {i}\")\n"))
        .collect();
    program(&definitions, "f", count, ":done")
}

fn handlers(count: usize) -> String {
    let definitions: String = (0..count)
        .map(|i| {
            format!(
                "def g{i}(n) do\n  try do\n    if n == {i}, do: raise(ArgumentError, \"bad\")\n    :ok\n  \
                 rescue\n    e in ArgumentError -> e.message\n  end\nend\n"
            )
        })
        .collect();
    program(&definitions, "g", count, ":done")
}

fn exception_types(count: usize) -> String {
    let definitions: String = (0..count)
        .map(|i| {
            format!("defmodule E{i} do\n  defexception [:message]\nend\ndef f{i}(x), do: raise(E{i}, \"bad {i}\")\n")
        })
        .collect();
    program(&definitions, "f", count, ":done")
}

fn jobs(label: &str, source: String) -> usize {
    let stem = format!("fz2_exception_cost_{}_{label}", id());
    let program = temp_dir().join(format!("{stem}.fz"));
    let trace = temp_dir().join(format!("{stem}.jsonl"));
    write(&program, source).expect("write program");
    let output = Command::new(FZ2_BIN)
        .arg("--log-telemetry")
        .arg(&trace)
        .arg("interp")
        .arg(&program)
        .output()
        .expect("invoke fz2 interp with telemetry");
    assert!(
        output.status.success(),
        "{label}: fz2 interp exited {}:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let jobs = BufReader::new(File::open(&trace).expect("open telemetry trace"))
        .lines()
        .map(|line| line.expect("telemetry line is UTF-8"))
        .filter(|line| line.starts_with(JOB_LINE) && line.contains(SPAN_START))
        .count();
    let _ = remove_file(&program);
    let _ = remove_file(&trace);
    jobs
}

/// The jobs each further unit adds, measured over two stretches of the same
/// family. The two agree when the cost is the same for every unit.
fn jobs_per_unit(label: &str, family: impl Fn(usize) -> String, counts: [usize; 3]) -> usize {
    let [few, some, many] = counts.map(|count| (count, jobs(&format!("{label}{count}"), family(count))));
    let per_unit = |(low, low_jobs): (usize, usize), (high, high_jobs): (usize, usize)| {
        let (added, units) = (high_jobs - low_jobs, high - low);
        assert_eq!(added % units, 0, "{label}: {added} jobs over {units} units");
        added / units
    };
    let early = per_unit(few, some);
    assert_eq!(
        early,
        per_unit(some, many),
        "{label}: every unit costs what the first ones cost"
    );
    early
}

#[test]
fn a_function_that_neither_raises_nor_handles_pays_nothing_for_exceptions() {
    let quiet = jobs_per_unit("quiet", |count| plain_functions(count, ":done"), [1, 5, 20]);
    let raising = jobs_per_unit(
        "raising",
        |count| plain_functions(count, "raise(ArgumentError, \"x\")"),
        [1, 5, 20],
    );
    assert_eq!(
        raising, quiet,
        "a plain function costs the same whether or not the program around it raises"
    );
}

#[test]
fn each_raise_site_and_handler_costs_a_fixed_number_of_jobs() {
    assert_eq!(jobs_per_unit("site", raise_sites, [1, 5, 20]), 13, "per raise site");
    assert_eq!(jobs_per_unit("handler", handlers, [1, 4, 16]), 15, "per handler");
}

/// An exception type costs 40 jobs: 15 for the function that raises it, 7 for
/// its `exception/1`, 16 for its `message/1`, one to define its module, and one
/// more analysis of `Exception.message/1`, which dispatches to every type.
#[test]
fn each_exception_type_costs_forty_jobs() {
    let one = jobs("few_types1", exception_types(1));
    let six = jobs("few_types6", exception_types(6));
    assert_eq!(six - one, 5 * 40, "five further exception types");
}

/// Past eight exception types the program pays a bounded extra that does not
/// grow with their number. `Kernel.panic/1` keeps one row of inputs for each
/// type raised into it, up to `ACTIVATION_INPUT_ROW_BUDGET`; past that the rows
/// widen to one, the union of the types. No single type keys the extern
/// `panic/1` calls, but their union does, so `panic/1` is analysed once more
/// and the extern is activated a second time: at most five jobs, however many
/// types follow.
#[test]
fn many_exception_types_cost_a_bounded_extra_for_the_union_raised() {
    let one = jobs("many_types1", exception_types(1));
    let extra = |count: usize| jobs(&format!("many_types{count}"), exception_types(count)) - one - (count - 1) * 40;
    let (sixteen, twenty_six) = (extra(16), extra(26));
    assert!(
        (1..=5).contains(&sixteen),
        "sixteen types cost {sixteen} jobs beyond forty each"
    );
    assert!(
        (1..=5).contains(&twenty_six),
        "twenty-six types cost {twenty_six} jobs beyond forty each"
    );
}
