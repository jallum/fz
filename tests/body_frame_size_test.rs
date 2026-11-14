//! A body of N non-tail calls is cut into N continuations. They run in one
//! body frame: the first holds a slot for every value the chain keeps, and each
//! later one writes only the values that are new at its call. So the native code
//! and the stack slots the program compiles to grow in proportion to N, not
//! N^2/2 as they would if each continuation copied every live value again.
//!
//! The sizes come from the `fz.codegen.define_function` span stops in
//! `--log-telemetry`, which carry each function's `code_bytes` and
//! `stack_slot_bytes`.

use std::env::temp_dir;
use std::fs::{File, remove_file, write};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, id};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");

const DEFINE_FUNCTION_STOP: &str = r#"{"name":["fz","codegen","define_function"]"#;

/// `main` calls `f` N times, binds each result, and sums them last, so every
/// result stays live across all the calls after it.
fn sequential_calls_program(calls: usize) -> String {
    let binds: String = (1..=calls).map(|i| format!("  a{i} = f({i})\n")).collect();
    let sum = (1..=calls).map(|i| format!("a{i}")).collect::<Vec<_>>().join(" + ");
    format!("def f(x), do: x + 1\ndef main() do\n{binds}  IO.inspect({sum})\nend\n")
}

#[derive(Debug, Default, Clone, Copy)]
struct NativeSize {
    code_bytes: u64,
    stack_slot_bytes: u64,
}

fn field(line: &str, name: &str) -> u64 {
    let key = format!("\"{name}\":");
    let start = line.find(&key).unwrap_or_else(|| panic!("`{name}` in {line}")) + key.len();
    let digits: String = line[start..].chars().take_while(char::is_ascii_digit).collect();
    digits
        .parse()
        .unwrap_or_else(|_| panic!("`{name}` is a count in {line}"))
}

fn native_size(program: &Path, trace: &Path) -> (String, NativeSize) {
    let output = Command::new(FZ2_BIN)
        .arg("--log-telemetry")
        .arg(trace)
        .arg("run")
        .arg(program)
        .output()
        .expect("invoke fz2 run with telemetry");
    assert!(
        output.status.success(),
        "fz2 run exited {}:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let lines = BufReader::new(File::open(trace).expect("open telemetry trace"));
    let size = lines
        .lines()
        .map(|line| line.expect("telemetry line is UTF-8"))
        .filter(|line| line.starts_with(DEFINE_FUNCTION_STOP) && line.contains(r#""kind":"span_stop""#))
        .fold(NativeSize::default(), |size, line| NativeSize {
            code_bytes: size.code_bytes + field(&line, "code_bytes"),
            stack_slot_bytes: size.stack_slot_bytes + field(&line, "stack_slot_bytes"),
        });
    (String::from_utf8(output.stdout).expect("stdout is UTF-8"), size)
}

fn size_for_sequential_calls(calls: usize) -> NativeSize {
    let stem = format!("fz2_body_frame_{}_{calls}", id());
    let program: PathBuf = temp_dir().join(format!("{stem}.fz"));
    let trace: PathBuf = temp_dir().join(format!("{stem}.jsonl"));
    write(&program, sequential_calls_program(calls)).expect("write program");
    let (stdout, size) = native_size(&program, &trace);
    let _ = remove_file(&program);
    let _ = remove_file(&trace);
    let sum: usize = (1..=calls).map(|i| i + 1).sum();
    assert_eq!(stdout.trim(), sum.to_string(), "the program computes the sum");
    size
}

#[test]
fn native_code_and_stack_slots_grow_linearly_in_the_calls_of_a_body() {
    let small = size_for_sequential_calls(308);
    let large = size_for_sequential_calls(1000);
    let ratio = |large: u64, small: u64| large as f64 / small as f64;
    let calls_ratio = 1000.0 / 308.0;
    assert!(
        ratio(large.code_bytes, small.code_bytes) < 4.0,
        "code bytes for 1000 vs 308 sequential calls ({large:?} vs {small:?}) grow with the calls \
         ({calls_ratio:.2}x), not their square ({:.2}x)",
        calls_ratio * calls_ratio
    );
    assert!(
        ratio(large.stack_slot_bytes, small.stack_slot_bytes) < 4.0,
        "stack slot bytes for 1000 vs 308 sequential calls ({large:?} vs {small:?}) grow with the \
         calls ({calls_ratio:.2}x), not their square ({:.2}x)",
        calls_ratio * calls_ratio
    );
}
