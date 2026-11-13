//! A guard that does arithmetic over operands of mixed number lanes answers as
//! Elixir does, on the interpreter, the JIT and the AOT build.
//!
//! `tests/guard_matrix/programs.json` holds every generated program and the
//! list Elixir prints for it. Each program is an entry guard or a receive guard
//! over one arithmetic operator and one pair of operand kinds (integer, float,
//! `integer | float`, untyped, or a literal), evaluated at every value pair its
//! kinds allow. Elixir's answers are captured once, so this test needs no
//! Elixir. To regenerate the table, with `elixir` on PATH:
//!
//!     python3 tests/guard_matrix/generate.py tests/guard_matrix/programs.json

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");
const TABLE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/guard_matrix/programs.json");
const SCRATCH: &str = concat!(env!("CARGO_TARGET_TMPDIR"), "/guard_matrix");
const WORKERS: usize = 4;

struct Program {
    name: String,
    source: String,
    expected: String,
}

fn programs() -> Vec<Program> {
    let table = fs::read_to_string(TABLE).unwrap_or_else(|e| panic!("read {TABLE}: {e}"));
    let rows: serde_json::Value = serde_json::from_str(&table).expect("the table is JSON");
    rows.as_array()
        .expect("the table is a list of programs")
        .iter()
        .map(|row| {
            let field = |key: &str| {
                row[key]
                    .as_str()
                    .unwrap_or_else(|| panic!("a row has `{key}`"))
                    .to_string()
            };
            Program {
                name: field("name"),
                source: field("source"),
                expected: field("expected"),
            }
        })
        .collect()
}

fn stdout_or_failure(command: &mut Command) -> String {
    let output = command.output().expect("run fz2");
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if output.status.success() {
        return stdout;
    }
    let stderr = String::from_utf8_lossy(&output.stderr);
    let first = stderr.lines().find(|line| !line.trim().is_empty()).unwrap_or("");
    format!("{} stdout={stdout:?} stderr={first:?}", output.status)
}

/// What each of the three paths printed for the program, in path order.
fn answers(directory: &Path, program: &Program) -> [(&'static str, String); 3] {
    fs::create_dir_all(directory).expect("create the program directory");
    let source = directory.join("program.fz");
    fs::write(&source, &program.source).expect("write the program");
    let binary = directory.join("program.bin");
    let built = Command::new(FZ2_BIN)
        .args(["build", "-o"])
        .arg(&binary)
        .arg(&source)
        .output()
        .expect("run fz2 build");
    let build = if built.status.success() {
        stdout_or_failure(&mut Command::new(&binary))
    } else {
        let stderr = String::from_utf8_lossy(&built.stderr);
        format!("build failed: {}", stderr.lines().next().unwrap_or(""))
    };
    [
        (
            "interp",
            stdout_or_failure(Command::new(FZ2_BIN).arg("interp").arg(&source)),
        ),
        ("run", stdout_or_failure(Command::new(FZ2_BIN).arg("run").arg(&source))),
        ("build", build),
    ]
}

fn mismatches(program: &Program) -> Vec<String> {
    let directory: PathBuf = Path::new(SCRATCH).join(&program.name);
    let found = answers(&directory, program)
        .into_iter()
        .filter(|(_, got)| *got != program.expected)
        .map(|(path, got)| format!("{} via {path}: Elixir {}, fz {got}", program.name, program.expected))
        .collect();
    let _ = fs::remove_dir_all(&directory);
    found
}

#[test]
fn mixed_lane_guard_arithmetic_answers_as_elixir_does_on_every_path() {
    let programs = programs();
    assert_eq!(programs.len(), 296, "the table holds every generated program");
    let next = Mutex::new(0usize);
    let failures = Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..WORKERS {
            scope.spawn(|| {
                loop {
                    let index = {
                        let mut next = next.lock().unwrap();
                        *next += 1;
                        *next - 1
                    };
                    let Some(program) = programs.get(index) else { return };
                    failures.lock().unwrap().extend(mismatches(program));
                }
            });
        }
    });
    let mut failures = failures.into_inner().unwrap();
    failures.sort();
    assert!(
        failures.is_empty(),
        "{} program/path pairs differ from Elixir:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
