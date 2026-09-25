//! `tools/distill-telemetry.exs` reads a `--log-telemetry` JSONL stream and
//! prints, among other sections, a per-kind runs-vs-subjects census and the
//! cause of every re-run. Both are pure counts over the stream's own
//! `time_ns`/`elapsed_ns` fields, so a fixed trace produces byte-identical
//! output on every machine and every run; wall-clock-derived sections
//! (`timeline`, `span names by inclusive time`, ...) are not asserted on
//! here because their milliseconds vary run to run.
//!
//! `tests/distill_telemetry/main_returns_one.jsonl` (`def main(), do: 1`) is
//! the smallest program there is: 44 job starts over 26 subjects, 18
//! re-runs, every one of them matched to an `enqueued` wake -- one of those
//! wakes (`ScopeCode(17)` woken by the nested `def/1` macro root's
//! `Product(root_backend_product)` settling) arrives on
//! `work_graph.dependencies_moved`, not `work_graph.applied`, which is why
//! the distiller reads all three step-carrying events. It was captured with:
//!
//!     cargo build
//!     target/debug/fz2 --log-telemetry tests/distill_telemetry/main_returns_one.jsonl \
//!         interp tests/distill_telemetry/main_returns_one.fz
//!
//! Regenerate `expected_job_census.txt` / `expected_rerun_causes.txt` by
//! running the distiller over that trace and copying the two sections named
//! below out of its stdout.

use std::path::Path;
use std::process::Command;

const SCRIPT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tools/distill-telemetry.exs");
const TRACE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/distill_telemetry/main_returns_one.jsonl"
);

fn distill_stdout() -> String {
    let output = Command::new("elixir")
        .arg(SCRIPT)
        .arg(TRACE)
        .output()
        .expect("spawn `elixir tools/distill-telemetry.exs` (is Elixir installed and on PATH?)");
    assert!(
        output.status.success(),
        "distill-telemetry.exs exited {}:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("distiller stdout is UTF-8")
}

fn expected(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/distill_telemetry")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

/// Per job kind: runs, distinct subjects, excess (runs minus subjects), and
/// the worst single subject's run count. A kind with zero excess ran each of
/// its subjects exactly once.
#[test]
fn distiller_reports_job_runs_vs_subjects() {
    let actual = distill_stdout();
    let expected = expected("expected_job_census.txt");
    assert!(
        actual.contains(&expected),
        "\"job runs vs subjects\" section did not match.\n--- expected ---\n{expected}\n--- actual (full stdout) ---\n{actual}"
    );
}

/// Every re-run's cause, read from the wakes on `work_graph.applied`,
/// `work_graph.dependencies_moved` and `work_graph.quiesced` -- not inferred
/// -- grouped by (job kind, changed fact + use, completing job kind,
/// disposition). Only `enqueued` wakes count toward a re-run; `coalesced`
/// wakes land on a re-run some other wake already enqueued and are reported
/// separately. The distiller cross-checks its own count against the trace's
/// session-summed `WorkStartTally` and halts loudly on a mismatch rather than
/// printing an unexplained row.
#[test]
fn distiller_reports_the_cause_of_every_rerun() {
    let actual = distill_stdout();
    let expected = expected("expected_rerun_causes.txt");
    assert!(
        actual.contains(&expected),
        "\"cause of every re-run\" section did not match.\n--- expected ---\n{expected}\n--- actual (full stdout) ---\n{actual}"
    );
}
