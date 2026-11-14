//! A body of N non-tail calls is cut into N resume entries, and entry K holds
//! the K values still live after the Kth call. An entry reached from exactly
//! one other entry reuses that entry's transport layout for a capture both
//! hold, so only the entry that first holds a value requests an `EntryCapture`
//! product for it. The count of those requests is linear in N, not N^2/2.
//!
//! The count comes from `pull.product.requested` events in `--log-telemetry`.

use std::env::temp_dir;
use std::fs::{File, remove_file, write};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, id};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");

const REQUESTED_LINE: &str = r#"{"name":["fz","compiler2","pull","product","requested"]"#;
const ENTRY_CAPTURE_POSITION: &str = r#""position":{"kind":"EntryCapture""#;

/// `main` calls `f` N times, binds each result, and sums them last, so every
/// result stays live across all the calls after it.
fn sequential_calls_program(calls: usize) -> String {
    let binds: String = (1..=calls).map(|i| format!("  a{i} = f({i})\n")).collect();
    let sum = (1..=calls).map(|i| format!("a{i}")).collect::<Vec<_>>().join(" + ");
    format!("def f(x), do: x + 1\ndef main() do\n{binds}  IO.inspect({sum})\nend\n")
}

fn entry_capture_requests(program: &Path, trace: &Path) -> (String, usize) {
    let output = Command::new(FZ2_BIN)
        .arg("--log-telemetry")
        .arg(trace)
        .arg("interp")
        .arg(program)
        .output()
        .expect("invoke fz2 interp with telemetry");
    assert!(
        output.status.success(),
        "fz2 interp exited {}:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let lines = BufReader::new(File::open(trace).expect("open telemetry trace"));
    let requests = lines
        .lines()
        .map(|line| line.expect("telemetry line is UTF-8"))
        .filter(|line| line.starts_with(REQUESTED_LINE) && line.contains(ENTRY_CAPTURE_POSITION))
        .count();
    (String::from_utf8(output.stdout).expect("stdout is UTF-8"), requests)
}

fn requests_for_sequential_calls(calls: usize) -> (String, usize) {
    let stem = format!("fz2_entry_capture_{}_{calls}", id());
    let program: PathBuf = temp_dir().join(format!("{stem}.fz"));
    let trace: PathBuf = temp_dir().join(format!("{stem}.jsonl"));
    write(&program, sequential_calls_program(calls)).expect("write program");
    let measured = entry_capture_requests(&program, &trace);
    let _ = remove_file(&program);
    let _ = remove_file(&trace);
    measured
}

#[test]
fn a_body_of_n_sequential_calls_requests_two_n_plus_six_entry_captures() {
    for (calls, expected) in [(3, 12), (308, 622)] {
        let (stdout, requests) = requests_for_sequential_calls(calls);
        let sum: usize = (1..=calls).map(|i| i + 1).sum();
        assert_eq!(stdout.trim(), sum.to_string(), "the program computes the sum");
        assert_eq!(
            requests, expected,
            "EntryCapture requests for {calls} sequential calls whose results stay live: an entry \
             reached from one entry reuses its capture layouts, so the count is 2N+6, not N^2/2"
        );
    }
}
