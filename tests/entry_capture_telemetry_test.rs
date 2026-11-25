//! A body of N non-tail calls is cut into N resume entries, and entry K holds
//! the K values still live after the Kth call. An entry reached from exactly
//! one other entry reuses that entry's transport layout for a capture both
//! hold, so the layouts the body fact derives are linear in N, not N^2/2.
//!
//! Every position of an executable's body is laid out by one
//! `DeriveTransportBody` job, so what grows with N is the reads that job and
//! its neighbours hand, not the jobs. The totals come from the
//! `work_graph.applied` completions in `--log-telemetry`: the derivations stay
//! the same however many calls the body holds, and each further call hands
//! two more reads, one for each of the two entries it adds.

use std::env::temp_dir;
use std::fs::{File, remove_file, write};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, id};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");

const APPLIED_LINE: &str = r#"{"name":["fz","compiler2","work_graph","applied"]"#;

/// `main` calls `f` N times, binds each result, and sums them last, so every
/// result stays live across all the calls after it.
fn sequential_calls_program(calls: usize) -> String {
    let binds: String = (1..=calls).map(|i| format!("  a{i} = f({i})\n")).collect();
    let sum = (1..=calls).map(|i| format!("a{i}")).collect::<Vec<_>>().join(" + ");
    format!("def f(x), do: x + 1\ndef main() do\n{binds}  IO.inspect({sum})\nend\n")
}

/// What a compile spends: derivations and reads handed over every completion.
struct Spend {
    derivations: u64,
    reads_handed: u64,
}

fn compile_spend(program: &Path, trace: &Path) -> (String, Spend) {
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
    let mut spend = Spend {
        derivations: 0,
        reads_handed: 0,
    };
    for line in lines.lines().map(|line| line.expect("telemetry line is UTF-8")) {
        if !line.starts_with(APPLIED_LINE) {
            continue;
        }
        let event: serde_json::Value = serde_json::from_str(&line).expect("applied event is JSON");
        let completion = &event["metadata"]["completion"];
        spend.derivations += completion["derivations"].as_u64().unwrap_or(0);
        spend.reads_handed += completion["reads_handed"].as_u64().unwrap_or(0);
    }
    (String::from_utf8(output.stdout).expect("stdout is UTF-8"), spend)
}

fn spend_for_sequential_calls(calls: usize) -> Spend {
    let stem = format!("fz2_entry_capture_{}_{calls}", id());
    let program: PathBuf = temp_dir().join(format!("{stem}.fz"));
    let trace: PathBuf = temp_dir().join(format!("{stem}.jsonl"));
    write(&program, sequential_calls_program(calls)).expect("write program");
    let (stdout, spend) = compile_spend(&program, &trace);
    let _ = remove_file(&program);
    let _ = remove_file(&trace);
    let sum: usize = (1..=calls).map(|i| i + 1).sum();
    assert_eq!(stdout.trim(), sum.to_string(), "the program computes the sum");
    spend
}

#[test]
fn each_sequential_call_adds_two_reads_and_no_derivation() {
    let (few, many) = (3, 308);
    let (few_spend, many_spend) = (spend_for_sequential_calls(few), spend_for_sequential_calls(many));
    assert_eq!(
        many_spend.derivations, few_spend.derivations,
        "the body's layouts are derived by the same jobs however many calls it holds"
    );
    assert_eq!(
        many_spend.reads_handed - few_spend.reads_handed,
        2 * (many - few) as u64,
        "{many} sequential calls whose results stay live read {few} calls' worth plus two for each \
         further call: an entry reached from one entry reuses its capture layouts, so each call \
         adds two, not N/2"
    );
}
