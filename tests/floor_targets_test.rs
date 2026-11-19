//! `tools/floor` holds the programs binary performance work is measured on and
//! the hand-written arm64 code each one should compile to.

use std::fs;
use std::path::Path;

const FLOOR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tools/floor");

/// The targets `targets.sh` measures: the words of its `for t in ...; do` line.
fn measured_targets() -> Vec<String> {
    let script = fs::read_to_string(Path::new(FLOOR).join("targets.sh")).expect("read targets.sh");
    let line = script
        .lines()
        .find(|line| line.starts_with("for t in "))
        .expect("targets.sh lists its targets on a `for t in` line");
    line.trim_start_matches("for t in ")
        .trim_end_matches("; do")
        .split_whitespace()
        .map(str::to_owned)
        .collect()
}

/// A program's `# target:` line is the row the report compares it with, so a
/// name no target answers to would print a blank where a number belongs.
#[test]
fn every_program_names_a_target_that_is_measured() {
    let targets = measured_targets();
    let mut unknown = Vec::new();
    for entry in fs::read_dir(Path::new(FLOOR).join("programs")).expect("read programs") {
        let path = entry.expect("program entry").path();
        let source = fs::read_to_string(&path).expect("read program");
        for line in source.lines().filter(|line| line.starts_with("# target:")) {
            let name = line.trim_start_matches("# target:").trim();
            if !targets.iter().any(|target| target == name) {
                unknown.push(format!("{}: {name}", path.display()));
            }
        }
    }
    assert!(
        unknown.is_empty(),
        "programs name targets nothing measures: {unknown:#?}"
    );
}

/// Each hand-written target computes what plain C computes over random
/// binaries of both layouts; a target that is fast and wrong is not a target.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn the_hand_written_targets_agree_with_their_reference() {
    let output = std::process::Command::new(Path::new(FLOOR).join("targets.sh"))
        .arg("test")
        .output()
        .expect("run tools/floor/targets.sh test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success() && stdout.contains("ok:"),
        "targets.sh test failed:\n{stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
