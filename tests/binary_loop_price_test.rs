//! What a loop over a binary costs a byte, counted in instructions retired.
//!
//! A clause chain that reads one byte at a cursor and recurses on the rest is
//! how every byte scanner in the library is written. Its price per byte is
//! what the lowering of the chain decides: a byte read twice, a question asked
//! twice, or a value spilled to the stack each costs instructions on every
//! byte of every input. The price is read from a built executable, as the
//! difference between scanning the same binary many times and once.

#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

use std::env::temp_dir;
use std::fs::{remove_file, write};
use std::path::PathBuf;
use std::process::{Command, id};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");
const BYTES: u64 = 1_000_000;
/// Passes beyond the first; start-up varies by about a million instructions
/// a run, so the measured span must be large beside it.
const EXTRA_PASSES: u32 = 8;

/// The price of a byte with the first byte read once and the cursor held in a
/// register across the iteration: 40.40, within 0.03 from run to run. A
/// lowering that costs more has lost a fact the loop carried; one that costs
/// less lowers this figure.
const MOST_INSTRUCTIONS_PER_BYTE: f64 = 40.5;

/// The string-scanning clauses of the JSON decoder, scanning `BYTES` bytes
/// `passes` times.
fn scanner(passes: u32) -> String {
    format!(
        "defmodule Scan do\n\
         \x20 def pick([h | _]), do: h\n\
         \x20 def scan(s, b = <<\"\\\"\", r :: binary>>, acc), do: {{:ok, s, b, r, acc}}\n\
         \x20 def scan(s, b = <<\"\\\\\", r :: binary>>, acc), do: {{:esc, s, b, r, acc}}\n\
         \x20 def scan(_s, b = <<c, _r :: binary>>, _acc) when c < 32, do: {{:error, b}}\n\
         \x20 def scan(s, <<c, r :: binary>>, acc) when c < 128, do: scan(s, r, acc)\n\
         \x20 def scan(_s, \"\", _acc), do: {{:error, \"\"}}\n\
         \x20 def scan(s, b, acc), do: {{:other, s, b, acc}}\n\
         \x20 def passes(0, _s, total), do: total\n\
         \x20 def passes(k, s, total) do\n\
         \x20   {{:ok, _, _, rest, _}} = scan(\"x\", s, 0)\n\
         \x20   passes(k - 1, s, total + byte_size(rest))\n\
         \x20 end\n\
         end\n\
         def main() do\n\
         \x20 s = String.duplicate(\"a\", {BYTES}) <> \"\\\"\"\n\
         \x20 dbg(Scan.passes({passes}, Scan.pick([s, 7]), 0))\n\
         \x20 nil\n\
         end\n"
    )
}

fn temp_path(name: &str, suffix: &str) -> PathBuf {
    temp_dir().join(format!("fz2_binary_loop_price_{}_{name}{suffix}", id()))
}

/// Instructions retired by the executable built from `source`.
fn instructions_retired(name: &str, source: &str) -> u64 {
    let source_path = temp_path(name, ".fz");
    let exe_path = temp_path(name, "");
    write(&source_path, source).expect("write the scanner");
    let built = Command::new(FZ2_BIN)
        .args(["build", "-o"])
        .arg(&exe_path)
        .arg(&source_path)
        .output()
        .expect("invoke fz2 build");
    assert!(built.status.success(), "build failed: {built:?}");
    // libmalloc's magazine state makes instruction counts bimodal; one
    // magazine makes them repeatable.
    let run = Command::new("/usr/bin/time")
        .arg("-l")
        .arg(&exe_path)
        .env("MallocMaxMagazines", "1")
        .output()
        .expect("run the scanner under time");
    let _ = remove_file(&source_path);
    let _ = remove_file(&exe_path);
    assert!(run.status.success(), "the scanner ran: {run:?}");
    String::from_utf8_lossy(&run.stderr)
        .lines()
        .find_map(|line| line.trim().strip_suffix(" instructions retired"))
        .and_then(|count| count.trim().parse().ok())
        .expect("time -l reports instructions retired")
}

/// A byte of a clause chain that reads one byte and recurses costs no more
/// instructions than the chain's own tests and read: the cursor stays in a
/// register from one byte to the next, and a clause that begins where the
/// last one began asks nothing again.
#[test]
fn a_byte_scanner_costs_no_more_than_its_own_tests_per_byte() {
    let once = instructions_retired("once", &scanner(1));
    let many = instructions_retired("many", &scanner(1 + EXTRA_PASSES));
    let per_byte = (many - once) as f64 / (EXTRA_PASSES as u64 * BYTES) as f64;
    println!("{per_byte:.3} instructions per byte (at most {MOST_INSTRUCTIONS_PER_BYTE})");
    assert!(
        per_byte <= MOST_INSTRUCTIONS_PER_BYTE,
        "{per_byte:.2} instructions per byte, at most {MOST_INSTRUCTIONS_PER_BYTE}"
    );
}
