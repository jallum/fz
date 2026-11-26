//! `tools/distill-telemetry.exs` reads a `--log-telemetry` JSONL stream and
//! prints, among other sections, a per-kind runs-vs-subjects census and the
//! cause of every wake. Both are pure counts over the stream's own
//! `time_ns`/`elapsed_ns` fields, so a fixed trace produces byte-identical
//! output on every machine and every run, and the whole of stdout is compared.
//!
//! `tests/distill_telemetry/main_returns_one.jsonl` (`def main(), do: 1`) is
//! the smallest program there is: 22 job runs over 20 subjects, 2 re-runs
//! (`ScopeCode`, 4 runs over 2 subjects). The cause table counts every
//! wake that started its job -- 12 of them, none already pending -- and one of those
//! (`ScopeCode` woken by the nested `def/1` macro root's
//! `Product(root_backend_product)` settling) arrives on
//! `work_graph.dependencies_moved`, not `work_graph.applied`, which is why
//! the distiller reads all three step-carrying events. The per-reason
//! `work_starts` counts sum to the 22 job runs. The trace was captured with:
//!
//!     cargo build
//!     target/debug/fz2 --log-telemetry tests/distill_telemetry/main_returns_one.jsonl \
//!         interp tests/distill_telemetry/main_returns_one.fz
//!
//! `main_returns_one.expected.txt` is what real `elixir` prints for that trace;
//! regenerate it with `elixir tools/distill-telemetry.exs
//! tests/distill_telemetry/main_returns_one.jsonl`. `fz2` running the same
//! script through `interp`, `run` and `build` must print it byte for byte.
//!
//! `tests/distill_telemetry/tied_rows.jsonl` (`def main(), do: Map.get(%{a: 1}, :a)`)
//! is a trace in which rows tie on the figure a table sorts by, at the `--top 32`
//! cut. Every table breaks ties by the row's own label, so the rows a cut keeps
//! do not depend on the order a map hands its entries back in, which Elixir
//! leaves unspecified and fz does not reproduce. `tied_rows.expected.txt` is what
//! `elixir tools/distill-telemetry.exs --top 32` prints for it. The trace is kept
//! as captured, with its wake `disposition` fields renamed to `admission`
//! (`enqueued` -> `started`): a fresh capture has different timings and may
//! not tie.
//!
//! Compiling the script is itself a measurement. One drive of the product
//! stack spends at most `PRODUCT_DRIVE_BUDGET` requests, and a compile runs
//! several drives; the ceilings below bound the script's compile by the numbers
//! `pull.drive.finished`, `pull.product.requested` and `work_graph.applied`
//! report.

use std::env::temp_dir;
use std::fs::{File, create_dir, read_dir, read_to_string, remove_dir_all, remove_file, write};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, id};
use std::sync::atomic::{AtomicU64, Ordering};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");
const SCRIPT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tools/distill-telemetry.exs");
const TRACE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/distill_telemetry/main_returns_one.jsonl"
);
const EXPECTED: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/distill_telemetry/main_returns_one.expected.txt"
);

const TIED_TRACE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/distill_telemetry/tied_rows.jsonl");
const TIED_EXPECTED: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/distill_telemetry/tied_rows.expected.txt"
);
const TIED_ARGS: [&str; 3] = ["--top", "32", TIED_TRACE];

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn unique_temp_path(prefix: &str, suffix: &str) -> PathBuf {
    let nonce = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    temp_dir().join(format!("{}_{}_{}{}", prefix, id(), nonce, suffix))
}

fn expected_stdout() -> String {
    expectation(EXPECTED)
}

fn expectation(path: &str) -> String {
    read_to_string(path).unwrap_or_else(|e| panic!("read {path}: {e}"))
}

fn stdout_of_success(output: Output, what: &str) -> String {
    assert!(
        output.status.success(),
        "{what} exited {}:\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{what} wrote to stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap_or_else(|e| panic!("{what} stdout is UTF-8: {e}"))
}

fn assert_prints_expected(actual: &str, what: &str) {
    assert_prints(actual, &expected_stdout(), what);
}

fn assert_prints(actual: &str, expected: &str, what: &str) {
    assert!(
        actual == expected,
        "{what} did not print what real elixir prints for the same trace.\n--- expected ---\n{expected}\n--- actual ---\n{actual}"
    );
}

/// The reference: the checked-in expectation is what `elixir` prints today.
#[test]
fn elixir_prints_the_checked_in_expectation() {
    let output = Command::new("elixir")
        .arg(SCRIPT)
        .arg(TRACE)
        .output()
        .expect("spawn `elixir tools/distill-telemetry.exs` (is Elixir installed and on PATH?)");
    assert_prints_expected(&stdout_of_success(output, "elixir distill-telemetry.exs"), "elixir");
}

/// The reference for the trace whose rows tie at the cut.
#[test]
fn elixir_prints_the_checked_in_expectation_for_tied_rows() {
    let output = Command::new("elixir")
        .arg(SCRIPT)
        .args(TIED_ARGS)
        .output()
        .expect("spawn `elixir tools/distill-telemetry.exs` (is Elixir installed and on PATH?)");
    assert_prints(
        &stdout_of_success(output, "elixir distill-telemetry.exs --top 32"),
        &expectation(TIED_EXPECTED),
        "elixir, tied rows",
    );
}

/// The distiller under the interpreter prints exactly what elixir prints.
#[test]
fn interp_runs_the_distiller_as_elixir_does() {
    let output = Command::new(FZ2_BIN)
        .args(["interp", SCRIPT, TRACE])
        .output()
        .expect("invoke fz2 interp");
    assert_prints_expected(&stdout_of_success(output, "fz2 interp"), "fz2 interp");
}

/// The distiller under the JIT prints exactly what elixir prints.
#[test]
fn run_runs_the_distiller_as_elixir_does() {
    let output = Command::new(FZ2_BIN)
        .args(["run", SCRIPT, TRACE])
        .output()
        .expect("invoke fz2 run");
    assert_prints_expected(&stdout_of_success(output, "fz2 run"), "fz2 run");
}

/// The distiller built ahead of time prints exactly what elixir prints.
#[test]
fn build_links_the_distiller_that_prints_as_elixir_does() {
    let binary = unique_temp_path("fz2_distiller", ".bin");
    let build = Command::new(FZ2_BIN)
        .arg("build")
        .arg("-o")
        .arg(&binary)
        .arg(SCRIPT)
        .output()
        .expect("invoke fz2 build");
    stdout_of_success(build, "fz2 build");
    let run = Command::new(&binary).arg(TRACE).output();
    let tied = Command::new(&binary).args(TIED_ARGS).output();
    let _ = remove_file(&binary);
    let _ = remove_file(binary.with_extension("bin.o"));
    let run = run.expect("run the built distiller");
    assert_prints_expected(&stdout_of_success(run, "the built distiller"), "the built distiller");
    // Rows that tie at the cut are the same rows elixir keeps, whatever order
    // a map's entries come back in.
    let tied = tied.expect("run the built distiller over tied rows");
    assert_prints(
        &stdout_of_success(tied, "the built distiller, tied rows"),
        &expectation(TIED_EXPECTED),
        "the built distiller, tied rows",
    );
}

/// What a compile's telemetry says it spent on the product stack.
#[derive(Debug, PartialEq, Eq)]
struct CompileSpend {
    /// Every `pull.product.requested`, over all drives.
    requests: u64,
    /// `requests` of each `pull.drive.finished`, in drive order.
    drives: Vec<u64>,
    /// Every derivation the World's job completions filed, over all jobs.
    derivations: u64,
    /// Every read those derivations handed the World, counted per derivation.
    reads_handed: u64,
}

impl CompileSpend {
    fn largest_drive(&self) -> u64 {
        self.drives.iter().copied().max().unwrap_or(0)
    }
}

const REQUESTED_LINE: &str = r#"{"name":["fz","compiler2","pull","product","requested"]"#;
const APPLIED_LINE: &str = r#"{"name":["fz","compiler2","work_graph","applied"]"#;
const DRIVE_FINISHED_LINE: &str = r#"{"name":["fz","compiler2","pull","drive","finished"]"#;

fn read_compile_spend(trace: &Path) -> CompileSpend {
    let lines = BufReader::new(File::open(trace).unwrap_or_else(|e| panic!("open {}: {e}", trace.display())));
    let mut spend = CompileSpend {
        requests: 0,
        drives: Vec::new(),
        derivations: 0,
        reads_handed: 0,
    };
    for line in lines.lines() {
        let line = line.expect("telemetry line is UTF-8");
        if line.starts_with(REQUESTED_LINE) {
            spend.requests += 1;
        } else if line.starts_with(DRIVE_FINISHED_LINE) {
            let event: serde_json::Value = serde_json::from_str(&line).expect("drive event is JSON");
            let requests = event["metadata"]["requests"]
                .as_u64()
                .expect("drive.finished carries requests");
            spend.drives.push(requests);
        } else if line.starts_with(APPLIED_LINE) {
            let event: serde_json::Value = serde_json::from_str(&line).expect("applied event is JSON");
            let completion = &event["metadata"]["completion"];
            spend.derivations += completion["derivations"].as_u64().unwrap_or(0);
            spend.reads_handed += completion["reads_handed"].as_u64().unwrap_or(0);
        }
    }
    spend
}

/// The most the distiller's compile may spend, part by part, before any change
/// in flight moves it. Each is develop's measured value when the moves were last
/// folded in. A change that moves the spend records the move in a file of its
/// own under `CEILING_MOVES`, so changes in flight never edit the same lines.
const CEILINGS: [(&str, u64); 5] = [
    // The drive `PRODUCT_DRIVE_BUDGET` (50,000) bounds: its headroom is the margin
    // before the compile stops with a budget error.
    ("largest drive requests", 11_438),
    ("total requests", 11_559),
    ("drives", 25),
    ("derivations", 18_943),
    // A reach job reads the edge fact of every node in its cone, so each of its
    // runs hands one read per node.
    ("reads handed", 136_381),
];

/// One `<ticket>.moves` file per change: lines of `<part> <signed delta>`, and
/// `#` lines saying why the spend moved and who accepted a rise.
const CEILING_MOVES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/distill_telemetry/ceiling_moves");

/// One change's movement of the ceilings, read from its `.moves` file.
struct CeilingMove {
    ticket: String,
    deltas: Vec<(String, i64)>,
}

impl CeilingMove {
    fn delta_of(&self, part: &str) -> Option<i64> {
        self.deltas
            .iter()
            .find_map(|(moved, delta)| (moved == part).then_some(*delta))
    }
}

fn read_ceiling_moves(dir: &Path) -> Vec<CeilingMove> {
    let mut files: Vec<PathBuf> = read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|entry| entry.expect("ceiling_moves entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "moves"))
        .collect();
    // Sorted so the printed breakdown reads the same on every machine.
    files.sort();
    files.iter().map(|file| read_ceiling_move(file)).collect()
}

fn read_ceiling_move(file: &Path) -> CeilingMove {
    let ticket = file
        .file_stem()
        .expect("a .moves file has a stem")
        .to_string_lossy()
        .into_owned();
    let text = read_to_string(file).unwrap_or_else(|e| panic!("read {}: {e}", file.display()));
    let mut deltas: Vec<(String, i64)> = Vec::new();
    for line in text.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (part, delta) = parse_delta(&ticket, line);
        assert!(
            CEILINGS.iter().any(|(known, _)| *known == part),
            "{ticket}.moves moves {part:?}, which is not a ceiling"
        );
        assert!(
            deltas.iter().all(|(moved, _)| *moved != part),
            "{ticket}.moves moves {part:?} twice"
        );
        deltas.push((part, delta));
    }
    CeilingMove { ticket, deltas }
}

fn parse_delta(ticket: &str, line: &str) -> (String, i64) {
    let (part, delta) = line
        .rsplit_once(char::is_whitespace)
        .unwrap_or_else(|| panic!("{ticket}.moves line {line:?} is not `<part> <signed delta>`"));
    let delta = delta
        .parse::<i64>()
        .unwrap_or_else(|e| panic!("{ticket}.moves line {line:?}: delta {delta:?}: {e}"));
    (part.trim().to_string(), delta)
}

/// A part's ceiling: its base plus every change's move, with the breakdown the
/// test prints beside it.
fn ceiling_of(part: &str, base: u64, moves: &[CeilingMove]) -> (u64, String) {
    let mut limit = i128::from(base);
    let mut breakdown = base.to_string();
    for (ticket, delta) in moves
        .iter()
        .filter_map(|change| change.delta_of(part).map(|delta| (&change.ticket, delta)))
    {
        limit += i128::from(delta);
        breakdown.push_str(&format!(" {delta:+} {ticket}"));
    }
    let limit = u64::try_from(limit).unwrap_or_else(|_| panic!("{part}'s ceiling {breakdown} is below zero"));
    (limit, breakdown)
}

/// Compiling the distiller spends no more of the product stack and of the
/// World's completions than its ceilings allow. The test prints what it
/// measured beside each ceiling's breakdown, so a move is the difference
/// between the measured figure and the ceiling, copied into the change's own
/// `.moves` file.
#[test]
fn the_distiller_compiles_inside_its_ceilings() {
    let trace = unique_temp_path("fz2_distiller_compile", ".jsonl");
    let output = Command::new(FZ2_BIN)
        .arg("--log-telemetry")
        .arg(&trace)
        .args(["interp", SCRIPT, TRACE])
        .output()
        .expect("invoke fz2 interp with telemetry");
    let stdout = stdout_of_success(output, "fz2 interp --log-telemetry");
    let spend = read_compile_spend(&trace);
    let _ = remove_file(&trace);
    assert_prints_expected(&stdout, "fz2 interp --log-telemetry");

    let measured = [
        spend.largest_drive(),
        spend.requests,
        spend.drives.len() as u64,
        spend.derivations,
        spend.reads_handed,
    ];
    let moves = read_ceiling_moves(Path::new(CEILING_MOVES));
    let mut overshoots = Vec::new();
    for ((part, base), value) in CEILINGS.into_iter().zip(measured) {
        let (ceiling, breakdown) = ceiling_of(part, base, &moves);
        println!("{part}: {value} (ceiling {ceiling} = {breakdown})");
        if value > ceiling {
            overshoots.push(format!(
                "{part} is {value}, {} over its ceiling of {ceiling} ({breakdown})",
                value - ceiling
            ));
        }
    }
    assert!(
        overshoots.is_empty(),
        "the distiller's compile spent more than its ceilings allow: {}. A rise is investigated \
         before a ceiling moves.",
        overshoots.join("; ")
    );
}

fn ceiling_moves_dir(files: &[(&str, &str)]) -> PathBuf {
    let dir = unique_temp_path("fz2_ceiling_moves", "");
    create_dir(&dir).expect("create ceiling_moves dir");
    for (name, text) in files {
        write(dir.join(name), text).expect("write a moves file");
    }
    dir
}

/// Two changes in flight each record their own move in a file of their own,
/// and the ceiling is the base plus both: neither edits a line the other does.
#[test]
fn moves_from_changes_in_flight_add_to_the_base() {
    let dir = ceiling_moves_dir(&[
        ("fz-a.moves", "# a rise the user accepted\nderivations +2\n"),
        ("fz-b.moves", "derivations -1\ndrives +1\n"),
        ("README.md", "derivations +1000\n"),
    ]);
    let moves = read_ceiling_moves(&dir);
    let _ = remove_dir_all(&dir);
    assert_eq!(
        ceiling_of("derivations", 100, &moves),
        (101, "100 +2 fz-a -1 fz-b".to_string())
    );
    assert_eq!(ceiling_of("drives", 25, &moves), (26, "25 +1 fz-b".to_string()));
    assert_eq!(ceiling_of("reads handed", 7, &moves), (7, "7".to_string()));
}

/// A move must name a ceiling that exists, so a misspelt part fails loudly
/// instead of moving nothing.
#[test]
#[should_panic(expected = "which is not a ceiling")]
fn a_move_of_a_part_that_is_not_a_ceiling_is_refused() {
    let dir = ceiling_moves_dir(&[("fz-c.moves", "derivation +5\n")]);
    read_ceiling_moves(&dir);
}
