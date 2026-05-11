//! fz-ul4.23.1 — fixture matrix.
//!
//! Walks `fixtures/*.fz`, parses the header comments at the top of each
//! file, and runs every fixture through each declared path. stdout is
//! compared against a sidecar `<name>.expected` (empty if the sidecar
//! is absent). Exit code must be 0.
//!
//! Header grammar (lines must precede the first non-comment line):
//!
//!     # purpose: one-line statement of what this fixture proves
//!     # paths:   comma-separated list of backends (`jit`, eventually `interp`, `aot`)
//!     # kind:    `run` (default if `fn main` present) or `test`
//!
//! Empty `paths:` is a flagged deferral — the runner skips, but the
//! fixture must include a `# defer:` line so the gap is named.
//!
//! Workflow: re-run with `BLESS=1 cargo test fixture_matrix` to rewrite
//! `.expected` files from current stdout. On failure (non-bless) the
//! actual stdout is dropped at `<name>.output` for diffing.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const FZ_BIN: &str = env!("CARGO_BIN_EXE_fz");

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Run,
    Test,
}

#[derive(Debug)]
struct Header {
    purpose: String,
    paths: Vec<String>,
    kind: Kind,
    defer: Option<String>,
}

fn parse_header(src: &str) -> Result<Header, String> {
    let mut purpose: Option<String> = None;
    let mut paths: Option<Vec<String>> = None;
    let mut kind: Option<Kind> = None;
    let mut defer: Option<String> = None;
    for line in src.lines() {
        let t = line.trim_start();
        if t.is_empty() {
            continue;
        }
        let Some(rest) = t.strip_prefix('#') else {
            break;
        };
        let rest = rest.trim_start();
        let parse_kv = |key: &str| rest.strip_prefix(key).map(|v| v.trim().to_string());
        if let Some(v) = parse_kv("purpose:") {
            purpose = Some(v);
        } else if let Some(v) = parse_kv("paths:") {
            paths = Some(
                v.split(',')
                    .map(|s| s.trim().to_string())
                    .filter(|s| !s.is_empty() && s != "none")
                    .collect(),
            );
        } else if let Some(v) = parse_kv("kind:") {
            kind = Some(match v.as_str() {
                "run" => Kind::Run,
                "test" => Kind::Test,
                other => return Err(format!("unknown kind: {}", other)),
            });
        } else if let Some(v) = parse_kv("defer:") {
            defer = Some(v);
        }
    }
    let purpose = purpose.ok_or("missing `# purpose:` header")?;
    let paths = paths.ok_or("missing `# paths:` header")?;
    let kind = kind.unwrap_or_else(|| {
        if has_main(src) {
            Kind::Run
        } else {
            Kind::Test
        }
    });
    if paths.is_empty() && defer.is_none() {
        return Err("empty `# paths:` without a `# defer:` rationale".into());
    }
    Ok(Header {
        purpose,
        paths,
        kind,
        defer,
    })
}

fn has_main(src: &str) -> bool {
    src.lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .any(|l| l.contains("fn main(") || l.contains("fn main "))
}

fn discover() -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = fs::read_dir("fixtures")
        .expect("fixtures/ should exist")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("fz"))
        .collect();
    out.sort();
    out
}

/// Outcome of running a fixture through a single path.
enum RunOutcome {
    /// Process exited 0 with this stdout.
    Ok(String),
    /// Process exited 75 (EX_TEMPFAIL): the path is declared by the fixture
    /// but not yet wired (e.g. `fz interp` stub before fz-ul4.23.5.2). The
    /// matrix logs but does not fail.
    Deferred(String),
    /// Anything else — real failure.
    Failed(String),
}

fn run_path(fixture: &Path, header: &Header, path: &str) -> RunOutcome {
    let subcmd = match (path, header.kind) {
        ("jit", Kind::Run) => "run",
        ("jit", Kind::Test) => "test",
        ("interp", _) => "interp",
        ("aot", _) => {
            return RunOutcome::Failed(format!(
                "path '{}' not yet wired (fz-ul4.23.6)",
                path
            ));
        }
        _ => {
            return RunOutcome::Failed(format!("unknown path `{}`", path));
        }
    };
    let out = match Command::new(FZ_BIN).arg(subcmd).arg(fixture).output() {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(format!("spawn fz: {}", e)),
    };
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    if let Some(75) = out.status.code() {
        return RunOutcome::Deferred(stderr.trim_end().to_string());
    }
    if !out.status.success() {
        return RunOutcome::Failed(format!("exit {}: {}", out.status, stderr.trim_end()));
    }
    match String::from_utf8(out.stdout) {
        Ok(s) => RunOutcome::Ok(s),
        Err(e) => RunOutcome::Failed(format!("stdout utf8: {}", e)),
    }
}

fn normalize(s: &str) -> String {
    if s.is_empty() || s.ends_with('\n') {
        s.to_string()
    } else {
        format!("{}\n", s)
    }
}

enum CheckOutcome {
    /// Real pass against the .expected sidecar.
    Pass,
    /// Path is declared but not yet wired (subcommand returned exit 75).
    /// Surfaced in the test output but doesn't fail.
    Deferred(String),
    /// Mismatch or fatal error.
    Fail(String),
}

fn check(fixture: &Path, header: &Header, path: &str, bless: bool) -> CheckOutcome {
    let actual = match run_path(fixture, header, path) {
        RunOutcome::Ok(s) => s,
        RunOutcome::Deferred(msg) => return CheckOutcome::Deferred(msg),
        RunOutcome::Failed(e) => return CheckOutcome::Fail(e),
    };
    let actual = normalize(&actual);
    let expected_path = fixture.with_extension("expected");
    let expected = fs::read_to_string(&expected_path).unwrap_or_default();
    let expected = normalize(&expected);
    if actual == expected {
        // Clean up any stale .output from a prior failure.
        let _ = fs::remove_file(fixture.with_extension("output"));
        return CheckOutcome::Pass;
    }
    if bless {
        if actual.is_empty() {
            let _ = fs::remove_file(&expected_path);
        } else if let Err(e) = fs::write(&expected_path, &actual) {
            return CheckOutcome::Fail(format!("bless write: {}", e));
        }
        return CheckOutcome::Pass;
    }
    let output_path = fixture.with_extension("output");
    let _ = fs::write(&output_path, &actual);
    CheckOutcome::Fail(format!(
        "stdout mismatch for {} via {}; wrote {}\n--- expected\n{}--- actual\n{}",
        fixture.display(),
        path,
        output_path.display(),
        expected,
        actual
    ))
}

/// Regenerate `fixtures/index.md` from headers and assert it matches the
/// checked-in file. `BLESS=1` rewrites the index in place.
#[test]
fn fixture_index_up_to_date() {
    let bless = std::env::var("BLESS").ok().as_deref() == Some("1");
    let mut rows: Vec<(String, String, String)> = Vec::new();
    for f in discover() {
        let src = fs::read_to_string(&f).expect("read");
        let header = match parse_header(&src) {
            Ok(h) => h,
            Err(_) => continue,
        };
        let name = f.file_name().unwrap().to_string_lossy().into_owned();
        let paths = if header.paths.is_empty() {
            match header.defer.as_deref() {
                Some(d) => format!("_(deferred: {})_", d),
                None => "_(deferred)_".into(),
            }
        } else {
            header.paths.join(", ")
        };
        rows.push((name, header.purpose, paths));
    }
    let mut out = String::new();
    out.push_str("# Fixture index\n\n");
    out.push_str("Regenerated from header comments by `cargo test fixture_index_up_to_date`.\n");
    out.push_str("Run with `BLESS=1` to rewrite after editing fixtures.\n\n");
    out.push_str("| file | purpose | paths |\n");
    out.push_str("|------|---------|-------|\n");
    for (name, purpose, paths) in &rows {
        out.push_str(&format!("| `{}` | {} | {} |\n", name, purpose, paths));
    }
    let index_path = PathBuf::from("fixtures/index.md");
    let current = fs::read_to_string(&index_path).unwrap_or_default();
    if current == out {
        return;
    }
    if bless {
        fs::write(&index_path, &out).expect("bless index write");
        return;
    }
    panic!(
        "fixtures/index.md is out of date. Re-run with `BLESS=1 cargo test fixture_index_up_to_date`.\n\n--- expected\n{}\n--- actual\n{}",
        out, current
    );
}

/// `fz interp` exits 75 (EX_TEMPFAIL) when the requested fixture exercises
/// an IR construct the rebuilt interp doesn't yet support. The matrix
/// treats exit 75 as "deferred path" and logs without failing — this lets
/// us roll out interp coverage one fixture at a time.
///
/// A fixture that uses spawn/send/receive (concurrency_ping_pong.fz) is
/// currently deferred because concurrency in interp lands in
/// fz-ul4.23.5.8. Once that ticket lands, this test will need a
/// different fixture (or be retired).
#[test]
fn fz_interp_defers_unsupported_fixtures() {
    let out = Command::new(FZ_BIN)
        .args(["interp", "fixtures/concurrency_ping_pong.fz"])
        .output()
        .expect("spawn fz interp");
    assert_eq!(
        out.status.code(),
        Some(75),
        "fz interp on closure-using fixture should exit 75 (deferred), got status {:?}\nstderr:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("not yet supported"),
        "expected 'not yet supported' message, got: {}",
        stderr
    );
}

/// `fz dump --emit clif` smoke test. Confirms the feedback-loop subcommand
/// is wired and produces real CLIF for a baseline fixture.
#[test]
fn fz_dump_emits_clif() {
    let out = Command::new(FZ_BIN)
        .args(["dump", "fixtures/add1.fz"])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("; fn add1"), "missing add1 banner\n{}", stdout);
    assert!(stdout.contains("; fn main"), "missing main banner\n{}", stdout);
    assert!(stdout.contains("function "), "no Cranelift function header\n{}", stdout);

    let filtered = Command::new(FZ_BIN)
        .args(["dump", "fixtures/add1.fz", "--fn", "add1"])
        .output()
        .expect("spawn fz dump --fn");
    assert!(filtered.status.success());
    let s = String::from_utf8_lossy(&filtered.stdout);
    assert!(s.contains("; fn add1"));
    assert!(!s.contains("; fn main"), "filter leaked main: {}", s);
}

#[test]
fn fixture_matrix() {
    let bless = std::env::var("BLESS").ok().as_deref() == Some("1");
    let mut failures: Vec<String> = Vec::new();
    let mut deferred_paths: Vec<(PathBuf, String, String)> = Vec::new();
    let mut deferred_fixtures: Vec<(PathBuf, String, String)> = Vec::new();
    let fixtures = discover();
    assert!(!fixtures.is_empty(), "no fixtures discovered");
    for f in fixtures {
        let src = match fs::read_to_string(&f) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!("{}: read: {}", f.display(), e));
                continue;
            }
        };
        let header = match parse_header(&src) {
            Ok(h) => h,
            Err(e) => {
                failures.push(format!("{}: header: {}", f.display(), e));
                continue;
            }
        };
        if header.paths.is_empty() {
            deferred_fixtures.push((
                f,
                header.purpose.clone(),
                header.defer.unwrap_or_default(),
            ));
            continue;
        }
        for path in &header.paths {
            match check(&f, &header, path, bless) {
                CheckOutcome::Pass => {}
                CheckOutcome::Deferred(msg) => {
                    deferred_paths.push((f.clone(), path.clone(), msg));
                }
                CheckOutcome::Fail(e) => failures.push(e),
            }
        }
    }
    if !deferred_fixtures.is_empty() {
        eprintln!("deferred fixtures (no paths wired yet):");
        for (f, purpose, why) in &deferred_fixtures {
            eprintln!("  {}: {}\n    defer: {}", f.display(), purpose, why);
        }
    }
    if !deferred_paths.is_empty() {
        eprintln!("deferred paths (declared but stub):");
        for (f, path, msg) in &deferred_paths {
            eprintln!("  {} via {}: {}", f.display(), path, msg);
        }
    }
    assert!(
        failures.is_empty(),
        "{} fixture failure(s):\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}
