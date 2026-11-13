//! `tools/distill-telemetry.exs` reads a `--log-telemetry` JSONL stream and
//! prints, among other sections, a per-kind runs-vs-subjects census and the
//! cause of every wake. Both are pure counts over the stream's own
//! `time_ns`/`elapsed_ns` fields, so a fixed trace produces byte-identical
//! output on every machine and every run, and the whole of stdout is compared.
//!
//! `tests/distill_telemetry/main_returns_one.jsonl` (`def main(), do: 1`) is
//! the smallest program there is: 22 job runs over 20 subjects, 2 re-runs
//! (`ScopeCode`, 4 runs over 2 subjects). The cause table counts every
//! `enqueued` wake -- 12 of them, none coalesced -- and one of those
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
//! Compiling the script is itself a measurement. One drive of the product
//! stack spends at most `PRODUCT_DRIVE_BUDGET` requests, and a compile runs
//! several drives; the pin below holds the script's compile to the numbers
//! `pull.drive.finished` and `pull.product.requested` report.

use std::env::temp_dir;
use std::fs::{File, read_to_string, remove_file};
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

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn unique_temp_path(prefix: &str, suffix: &str) -> PathBuf {
    let nonce = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    temp_dir().join(format!("{}_{}_{}{}", prefix, id(), nonce, suffix))
}

fn expected_stdout() -> String {
    read_to_string(EXPECTED).unwrap_or_else(|e| panic!("read {EXPECTED}: {e}"))
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
    assert!(
        actual == expected_stdout(),
        "{what} did not print what real elixir prints for the same trace.\n--- expected ---\n{}\n--- actual ---\n{actual}",
        expected_stdout()
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
    let _ = remove_file(&binary);
    let _ = remove_file(binary.with_extension("bin.o"));
    let run = run.expect("run the built distiller");
    assert_prints_expected(&stdout_of_success(run, "the built distiller"), "the built distiller");
}

/// What a compile's telemetry says it spent on the product stack.
#[derive(Debug, PartialEq, Eq)]
struct CompileSpend {
    /// Every `pull.product.requested`, over all drives.
    requests: u64,
    /// `requests` of each `pull.drive.finished`, in drive order.
    drives: Vec<u64>,
}

impl CompileSpend {
    fn largest_drive(&self) -> u64 {
        self.drives.iter().copied().max().unwrap_or(0)
    }
}

const REQUESTED_LINE: &str = r#"{"name":["fz","compiler2","pull","product","requested"]"#;
const DRIVE_FINISHED_LINE: &str = r#"{"name":["fz","compiler2","pull","drive","finished"]"#;

fn read_compile_spend(trace: &Path) -> CompileSpend {
    let lines = BufReader::new(File::open(trace).unwrap_or_else(|e| panic!("open {}: {e}", trace.display())));
    let mut spend = CompileSpend {
        requests: 0,
        drives: Vec::new(),
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
        }
    }
    spend
}

/// Compiling the distiller spends this much of the product stack. The largest
/// drive is the one `PRODUCT_DRIVE_BUDGET` bounds, so its headroom is the
/// margin before the compile stops with a budget error; the total and the
/// drive count say how the rest of the compile is spread.
#[test]
fn the_distiller_compiles_inside_the_product_drive_budget() {
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

    let measured = (spend.largest_drive(), spend.requests, spend.drives.len());
    assert_eq!(
        measured,
        (49_760, 51_196, 28),
        "(largest drive requests, total requests, drives) for the distiller's compile moved. \
         A fall is lowered in this pin; a rise is investigated first, because the largest drive \
         may not exceed PRODUCT_DRIVE_BUDGET (50,000)."
    );
}
