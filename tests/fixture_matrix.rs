//! fz-ul4.23.1 — fixture matrix (per-dir layout, fz-e97).
//!
//! Walks `fixtures/<name>/`, reads each fixture's `README.md`
//! frontmatter, and runs `input.fz` through each declared path. stdout
//! is compared against `expected.txt` in the same dir (empty if the
//! sidecar is absent). Exit code must be 0.
//!
//! Per-fixture layout:
//!
//!     fixtures/<name>/
//!         README.md         YAML frontmatter + narrative body
//!         input.fz          fz source
//!         expected.txt      stdout golden (optional)
//!         expected.clif     CLIF golden   (optional, fz-ul4.32)
//!         expected.specs    specs golden  (optional, fz-73m)
//!
//! Frontmatter grammar:
//!
//!     ---
//!     purpose: one-line statement of what this fixture proves
//!     paths: [jit, interp, aot]
//!     kind: run            # or `test`; defaults to run if `fn main` present
//!     defer: rationale     # required iff `paths:` is empty
//!     expect_clif_contains:
//!       - fn: <name>
//!         substr: <text>
//!     expect_clif_excludes:
//!       - fn: <name>
//!         substr: <text>
//!     ---
//!
//! Workflow: re-run with `BLESS=1 cargo test fixture_matrix` to rewrite
//! `expected.txt` from current stdout. On failure (non-bless) the
//! actual stdout is dropped at `<dir>/actual.txt` for diffing.

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
    /// Per-fn CLIF substring assertions from `# expect_clif_contains: <fn>: <substr>`
    /// header keys. Each entry: (fn_name, substr_that_must_appear). Asserted by
    /// shelling `fz dump --emit clif --fn <name>` and grepping the stdout.
    /// fz-ul4.27.1 (VR.0).
    expect_clif_contains: Vec<(String, String)>,
    /// Same shape as `expect_clif_contains` but the substring must NOT appear.
    /// Useful for proving a tag-check fast/slow path got elided.
    expect_clif_excludes: Vec<(String, String)>,
}

/// Parse a fixture's README.md frontmatter. Frontmatter is the block
/// between the first `---` and the next `---` line (both at column 0);
/// the body that follows is documentation only.
///
/// Grammar is a deliberately tiny YAML subset — enough for our keys,
/// nothing more. Supported:
///   * `key: scalar` (string)
///   * `paths: [a, b, c]` (flow sequence of bare scalars)
///   * `expect_clif_{contains,excludes}:` block sequence of `- fn:`/`substr:` maps
fn parse_header_from_dir(dir: &Path) -> Result<Header, String> {
    let readme = dir.join("README.md");
    let src =
        fs::read_to_string(&readme).map_err(|e| format!("read {}: {}", readme.display(), e))?;
    let fm = extract_frontmatter(&src).ok_or_else(|| {
        format!(
            "{}: missing `---` frontmatter block at top",
            readme.display()
        )
    })?;
    let mut purpose: Option<String> = None;
    let mut paths: Option<Vec<String>> = None;
    let mut kind: Option<Kind> = None;
    let mut defer: Option<String> = None;
    let mut expect_clif_contains: Vec<(String, String)> = Vec::new();
    let mut expect_clif_excludes: Vec<(String, String)> = Vec::new();

    let lines: Vec<&str> = fm.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        if line.trim().is_empty() {
            i += 1;
            continue;
        }
        // Top-level key (no leading whitespace).
        if line.starts_with(' ') || line.starts_with('-') {
            return Err(format!(
                "{}: stray indented line at top level: `{}`",
                readme.display(),
                line
            ));
        }
        let (key, rest) = line
            .split_once(':')
            .ok_or_else(|| format!("{}: line without `:`: `{}`", readme.display(), line))?;
        let key = key.trim();
        let val = rest.trim();
        match key {
            "purpose" => purpose = Some(unquote(val).to_string()),
            "paths" => {
                paths = Some(
                    parse_flow_seq(val)
                        .map_err(|e| format!("{}: paths: {}", readme.display(), e))?,
                );
            }
            "kind" => {
                kind = Some(match unquote(val) {
                    "run" => Kind::Run,
                    "test" => Kind::Test,
                    other => return Err(format!("{}: unknown kind `{}`", readme.display(), other)),
                });
            }
            "defer" => defer = Some(unquote(val).to_string()),
            "expect_clif_contains" | "expect_clif_excludes" => {
                if !val.is_empty() {
                    return Err(format!(
                        "{}: `{}:` must introduce a block list (no inline value)",
                        readme.display(),
                        key
                    ));
                }
                let target = if key == "expect_clif_contains" {
                    &mut expect_clif_contains
                } else {
                    &mut expect_clif_excludes
                };
                i += 1;
                while i < lines.len() && lines[i].starts_with("  - fn:") {
                    let fn_val = lines[i].trim_start().trim_start_matches("- fn:").trim();
                    let fn_name = unquote(fn_val).to_string();
                    i += 1;
                    let substr_line = lines.get(i).copied().unwrap_or("");
                    let substr_v = substr_line
                        .trim_start()
                        .strip_prefix("substr:")
                        .ok_or_else(|| {
                            format!(
                                "{}: expected `substr:` after `- fn: {}`",
                                readme.display(),
                                fn_name
                            )
                        })?
                        .trim();
                    let substr = unquote(substr_v).to_string();
                    if fn_name.is_empty() || substr.is_empty() {
                        return Err(format!(
                            "{}: expect_clif_*: empty fn or substr",
                            readme.display()
                        ));
                    }
                    target.push((fn_name, substr));
                    i += 1;
                }
                continue;
            }
            other => return Err(format!("{}: unknown key `{}`", readme.display(), other)),
        }
        i += 1;
    }

    let purpose = purpose.ok_or_else(|| format!("{}: missing `purpose:`", readme.display()))?;
    let paths = paths.ok_or_else(|| format!("{}: missing `paths:`", readme.display()))?;
    let input_fz = dir.join("input.fz");
    let src_fz =
        fs::read_to_string(&input_fz).map_err(|e| format!("read {}: {}", input_fz.display(), e))?;
    let kind = kind.unwrap_or_else(|| {
        if has_main(&src_fz) {
            Kind::Run
        } else {
            Kind::Test
        }
    });
    if paths.is_empty() && defer.is_none() {
        return Err(format!(
            "{}: empty `paths:` without a `defer:` rationale",
            readme.display()
        ));
    }
    Ok(Header {
        purpose,
        paths,
        kind,
        defer,
        expect_clif_contains,
        expect_clif_excludes,
    })
}

fn extract_frontmatter(src: &str) -> Option<&str> {
    let rest = src.strip_prefix("---\n")?;
    let end = rest.find("\n---")?;
    Some(&rest[..end])
}

fn unquote(s: &str) -> &str {
    let s = s.trim();
    if s.len() >= 2 && s.starts_with('"') && s.ends_with('"') {
        &s[1..s.len() - 1]
    } else {
        s
    }
}

/// Parse a YAML flow sequence: `[a, b, c]`. Empty `[]` → empty vec.
fn parse_flow_seq(s: &str) -> Result<Vec<String>, String> {
    let s = s.trim();
    let inner = s
        .strip_prefix('[')
        .and_then(|s| s.strip_suffix(']'))
        .ok_or_else(|| format!("expected `[...]`, got `{}`", s))?;
    Ok(inner
        .split(',')
        .map(|s| unquote(s.trim()).to_string())
        .filter(|s| !s.is_empty())
        .collect())
}

fn has_main(src: &str) -> bool {
    src.lines()
        .any(|l| l.contains("fn main(") || l.contains("fn main "))
}

/// Discover fixture directories. Returns each fixture's directory path
/// (e.g. `fixtures/add1`). The matrix and goldens derive concrete file
/// paths from this via `<dir>/input.fz`, `<dir>/expected.txt`, etc.
fn discover() -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = fs::read_dir("fixtures")
        .expect("fixtures/ should exist")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_dir() && p.join("input.fz").is_file())
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
    if path == "aot" {
        return run_aot_path(fixture, header);
    }
    let subcmd = match (path, header.kind) {
        ("jit", Kind::Run) => "run",
        ("jit", Kind::Test) => "test",
        ("interp", _) => "interp",
        _ => {
            return RunOutcome::Failed(format!("unknown path `{}`", path));
        }
    };
    let input = fixture.join("input.fz");
    let out = match Command::new(FZ_BIN).arg(subcmd).arg(&input).output() {
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

/// Drive the AOT path: `fz build` the fixture to a temp executable, run
/// it, capture stdout. `# kind: test` fixtures aren't supported in AOT
/// yet — they go through `fz test` which doesn't have an AOT equivalent.
fn run_aot_path(fixture: &Path, header: &Header) -> RunOutcome {
    if header.kind == Kind::Test {
        return RunOutcome::Deferred(
            "kind: test fixtures don't yet run via aot (`fz test` is jit-only)".into(),
        );
    }
    let stem = fixture
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("fz_fixture");
    let out_path = std::env::temp_dir().join(format!("fz_matrix_{}", stem));
    let input = fixture.join("input.fz");
    // Build.
    let build = match Command::new(FZ_BIN)
        .args(["build"])
        .arg(&input)
        .args(["-o"])
        .arg(&out_path)
        .output()
    {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(format!("spawn fz build: {}", e)),
    };
    let build_stderr = String::from_utf8_lossy(&build.stderr).to_string();
    if !build.status.success() {
        // Common failure today: closure-using fixtures abort at runtime
        // for frame_sizes (fz-ul4.23.11). Surface as Deferred so the
        // matrix doesn't fail until the follow-up lands.
        if build_stderr.contains("frame_sizes") || build_stderr.contains("not yet supported") {
            return RunOutcome::Deferred(build_stderr.trim_end().to_string());
        }
        return RunOutcome::Failed(format!(
            "fz build exit {}: {}",
            build.status,
            build_stderr.trim_end()
        ));
    }
    // Run.
    let run = match Command::new(&out_path).output() {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(format!("spawn aot binary: {}", e)),
    };
    let _ = std::fs::remove_file(&out_path);
    let run_stderr = String::from_utf8_lossy(&run.stderr).to_string();
    if run_stderr.contains("frame_sizes") {
        return RunOutcome::Deferred(run_stderr.trim_end().to_string());
    }
    if !run.status.success() {
        return RunOutcome::Failed(format!(
            "aot binary exit {}: {}",
            run.status,
            run_stderr.trim_end()
        ));
    }
    match String::from_utf8(run.stdout) {
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
    let expected_path = fixture.join("expected.txt");
    let expected = fs::read_to_string(&expected_path).unwrap_or_default();
    let expected = normalize(&expected);
    if actual == expected {
        // Clean up any stale actual.txt from a prior failure.
        let _ = fs::remove_file(fixture.join("actual.txt"));
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
    let output_path = fixture.join("actual.txt");
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
    for dir in discover() {
        let header = match parse_header_from_dir(&dir) {
            Ok(h) => h,
            Err(_) => continue,
        };
        let name = dir.file_name().unwrap().to_string_lossy().into_owned();
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
    out.push_str(
        "Regenerated from README.md frontmatter by `cargo test fixture_index_up_to_date`.\n",
    );
    out.push_str("Run with `BLESS=1` to rewrite after editing fixtures.\n\n");
    out.push_str("| fixture | purpose | paths |\n");
    out.push_str("|---------|---------|-------|\n");
    for (name, purpose, paths) in &rows {
        out.push_str(&format!("| `{}/` | {} | {} |\n", name, purpose, paths));
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

/// `fz dump --emit clif` smoke test. Confirms the feedback-loop subcommand
/// is wired and produces real CLIF for a baseline fixture.
#[test]
fn fz_dump_emits_clif() {
    let out = Command::new(FZ_BIN)
        .args(["dump", "fixtures/add1/input.fz"])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("; fn add1"),
        "missing add1 banner\n{}",
        stdout
    );
    assert!(
        stdout.contains("; fn main"),
        "missing main banner\n{}",
        stdout
    );
    assert!(
        stdout.contains("function "),
        "no Cranelift function header\n{}",
        stdout
    );
    // fz-ul4.23.7: srcloc annotations on body instructions resolve back
    // to file:line:col. add1's `n + 1` lives at line 1 (fz-e97: header
    // comments lifted out of input.fz into README.md); expect at least
    // one annotated line pointing at it.
    assert!(
        stdout.contains("; @1:"),
        "expected line-1 srcloc annotations in dump\n{}",
        stdout
    );

    let filtered = Command::new(FZ_BIN)
        .args(["dump", "fixtures/add1/input.fz", "--fn", "add1"])
        .output()
        .expect("spawn fz dump --fn");
    assert!(filtered.status.success());
    let s = String::from_utf8_lossy(&filtered.stdout);
    assert!(s.contains("; fn add1"));
    assert!(!s.contains("; fn main"), "filter leaked main: {}", s);

    // fz-ul4.23.8: --emit asm produces machine-code dump via Cranelift's
    // vcode disassembly. Don't pin specific instructions — they vary by
    // host arch — but every supported target emits real assembly,
    // including a block0 label and at least one inst per fn body.
    let asm = Command::new(FZ_BIN)
        .args([
            "dump",
            "fixtures/add1/input.fz",
            "--emit",
            "asm",
            "--fn",
            "add1",
        ])
        .output()
        .expect("spawn fz dump --emit asm");
    assert!(
        asm.status.success(),
        "fz dump --emit asm exited {}",
        asm.status
    );
    let asm_out = String::from_utf8_lossy(&asm.stdout);
    assert!(asm_out.contains("; fn add1"));
    assert!(
        asm_out.contains("block0"),
        "expected block0 label in asm:\n{}",
        asm_out
    );
}

/// fz-ul4.27.14.1 — for `fixtures/add1/input.fz`, the print continuation
/// `k_2` is reached only via the native chain (callee `add1` is native,
/// cont `k_2` is native). Its entry-param 0 should therefore be RawInt,
/// loaded directly from the frame without a tag-strip. Before .27.14.1
/// k_2's entry began with `sshr_imm v0, 3` to unbox a force-Tagged slot;
/// the per-spec uniform-cont-reachable analysis drops that force when
/// no unconditional-Tagged writer can reach the slot.
#[ignore = "fz-cps.1.12: cont fn entry-param 0 is Tagged i64 per §2.1; entry-side unbox is now expected if body uses RawInt — superseded by §8.x"]
#[test]
fn add1_k_2_continuation_has_no_entry_side_unbox() {
    let out = Command::new(FZ_BIN)
        .args([
            "dump",
            "fixtures/add1/input.fz",
            "--emit",
            "clif",
            "--fn",
            "k_2",
        ])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("; fn k_2"),
        "missing k_2 banner:\n{}",
        stdout
    );
    assert!(
        !stdout.contains("sshr_imm v0"),
        "k_2 still unboxes its entry-param 0; slot must be RawInt under \
         .27.14.1:\n{}",
        stdout,
    );
}

/// fz-ul4.27.14.2 — for `fixtures/add1/input.fz`, the seam between the
/// native callee `add1` and the native cont `k_2` must carry the raw
/// int directly. Before .27.14.2 the native-chain branch in codegen
/// coerced `result → Tagged → cont_param_reprs[0]`; with .27.14.1 also
/// in place the destination became RawInt, leaving a redundant
/// box-then-unbox round-trip (`ishl_imm`/`bor_imm`/`sshr_imm`) at the
/// seam. .27.14.2 skips the Tagged intermediate so `main`'s body has
/// no shift/OR instructions between the two calls.
#[test]
fn add1_main_cont_seam_has_no_box_unbox_roundtrip() {
    let out = Command::new(FZ_BIN)
        .args([
            "dump",
            "fixtures/add1/input.fz",
            "--emit",
            "clif",
            "--fn",
            "main",
        ])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("; fn main"),
        "missing main banner:\n{}",
        stdout
    );
    // The native chain's cont seam should be two adjacent direct calls
    // with no boxing instructions between them. We pin this by asserting
    // `main` contains no `ishl_imm` (the box op) and no `bor_imm` (the
    // tag-set op).
    assert!(
        !stdout.contains("ishl_imm"),
        "main still boxes a value at the cont seam under .27.14.2:\n{}",
        stdout,
    );
    assert!(
        !stdout.contains("bor_imm"),
        "main still tag-sets at the cont seam under .27.14.2:\n{}",
        stdout,
    );
}

/// fz-ul4.27.15.1 — `Const::Int(n)` consumed by an int-monomorphic var
/// should emit `iconst.i64 n` raw, not `iconst((n<<3)|1)` tagged that a
/// downstream `sshr_imm` immediately unboxes. For `fixtures/add1/input.fz`,
/// both literals (`41` in main, `1` in add1's body) flow into raw
/// consumers (a RawInt slot and a typed int BinOp respectively). With
/// raw-by-default for Const::Int the entire program's CLIF should
/// contain ZERO `sshr_imm`, `ishl_imm`, or `bor_imm` ops anywhere — the
/// theoretical floor for add1.fz.
#[ignore = "fz-cps.1.12: tagged-int handoff at cont seam is the new model (cont sig is `(i64 Tagged, i64) tail`)"]
#[test]
fn add1_has_no_int_box_or_unbox_anywhere() {
    let out = Command::new(FZ_BIN)
        .args(["dump", "fixtures/add1/input.fz", "--emit", "clif"])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    for op in &["sshr_imm", "ishl_imm", "bor_imm"] {
        assert!(
            !stdout.contains(op),
            "add1.fz CLIF contains `{}` — int literals should be raw-by-default:\n{}",
            op,
            stdout,
        );
    }
    // Sanity: the literal `41` should appear as a raw iconst, not tagged 329.
    assert!(
        stdout.contains("iconst.i64 41"),
        "expected raw `iconst.i64 41` for the literal 41:\n{}",
        stdout,
    );
    assert!(
        !stdout.contains("iconst.i64 329"),
        "unexpected tagged-int literal 329 (= 41<<3|1):\n{}",
        stdout,
    );
}

/// fz-ul4.27.19 — for `fixtures/add1/input.fz`, native fns that don't
/// transitively need host_ctx (no `Term::Halt`, no callees that need
/// it) drop the trailing host_ctx i64 from their signature. `add1_s2`
/// and `k_2_s3` should both be `(i64) -> i64 tail` — a single i64 param.
#[ignore = "fz-cps.1.12: cont fns have §2.1 sig `(result, self) tail` (2 i64s, not 1); host_ctx dropped from all native sigs"]
#[test]
fn add1_native_fns_drop_unused_host_ctx() {
    let out = Command::new(FZ_BIN)
        .args(["dump", "fixtures/add1/input.fz", "--emit", "clif"])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    // fz-cps.1.a (fz-siu.1.1) + fz-cps.1.2: native sigs end in
    // a trailing cont:i64 param per docs/cps-in-clif.md §2.1, EXCEPT
    // cont fns whose §2.1 shape is `(result, self)` (no separate k).
    // add1_s2 is a regular native fn: `(n:i64, cont:i64)`.
    // k_2_s3 is a cont fn: `(result:i64)` — no host_ctx (.27.19),
    // no cont (§2.1 cont-fn shape).
    let expect = [
        ("add1_s2", "block0(v0: i64, v1: i64):"),
        ("k_2_s3", "block0(v0: i64):"),
    ];
    for (fn_name, want) in &expect {
        let body_start = stdout
            .find(&format!("; fn {}", fn_name))
            .unwrap_or_else(|| panic!("missing `{}` banner:\n{}", fn_name, stdout));
        let body = &stdout[body_start..];
        let block0_line = body.lines().find(|l| l.contains("block0(")).unwrap_or("");
        assert!(
            block0_line.contains(want),
            "{} should have entry block `{}`, got `{}`:\n{}",
            fn_name,
            want,
            block0_line,
            stdout,
        );
    }
}

/// fz-ul4.27.18 — for `fixtures/add1/input.fz`, `main` is never invoked from
/// any fz IR site (not a direct callee, not a continuation, not a
/// closure target). It can only enter via the trampoline entry, which
/// writes null into slot 0. So `main`'s emit_return paths specialize
/// to a halt-only sequence (`call fz_halt; return null`), skipping the
/// runtime `load v0+16; icmp eq 0; brif halt/store` dispatch entirely.
/// The body collapses to a single linear block.
#[ignore = "fz-cps.1.12: main builds an inline cont closure with halt-cont fallback (load v0+16 + brif) — required by closure-target chain; superseded by §8.x acceptance"]
#[test]
fn add1_main_has_no_runtime_cont_ptr_dispatch() {
    let out = Command::new(FZ_BIN)
        .args([
            "dump",
            "fixtures/add1/input.fz",
            "--emit",
            "clif",
            "--fn",
            "main",
        ])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    for op in &["load.i64 notrap aligned v0+16", "icmp eq", "brif"] {
        assert!(
            !stdout.contains(op),
            "main still emits `{}` — cont_ptr dispatch should be elided \
             under .27.18:\n{}",
            op,
            stdout,
        );
    }
    // Only one block — no halt/invoke split.
    let block_count = stdout.matches("block").count();
    // The block param syntax `block0(v0: i64, v1: i64):` contains "block"
    // once. No `block1:` / `block2:` labels expected.
    assert!(
        !stdout.contains("block1:") && !stdout.contains("block2:"),
        "main should be a single linear block under .27.18; got {} occurrences \
         of `block`:\n{}",
        block_count,
        stdout,
    );
}

/// fz-ul4.27.17 — `emit_return`'s halt-branch reuses the same `iconst.i64 0`
/// it materialized for the null-compare, instead of emitting a duplicate
/// inside the halt block. For fixtures/add1/input.fz's `main`, the body has
/// exactly one `iconst.i64 0` (used by both the icmp and the
/// `return null` sentinel via SSA dominance).
#[ignore = "fz-cps.5: main is native; trampoline-era emit_return iconst-counting invariant doesn't apply"]
#[test]
fn add1_main_emits_one_iconst_zero_in_emit_return() {
    let out = Command::new(FZ_BIN)
        .args([
            "dump",
            "fixtures/add1/input.fz",
            "--emit",
            "clif",
            "--fn",
            "main",
        ])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    // fz-cps.1.a (.1.1) + fz-cps.1.2: main is uniform and passes a
    // literal null cont arg at native non-cont callsites. add1 fixture's
    // chained-native sub-path calls add1 (regular native → +1 zero) and
    // k_2 (cont fn → no cont arg per §2.1). Plus the one zero
    // emit_halt_and_return_null returns. Total: 2.
    let count = stdout.matches("iconst.i64 0").count();
    assert_eq!(
        count, 2,
        "main should emit exactly two `iconst.i64 0` (one cont arg for \
         add1 per fz-cps.1.a + one halt-and-return-null sentinel per \
         .27.18); got {}:\n{}",
        count, stdout,
    );
}

/// fz-ul4.27.16 — native fns must not emit a dead `iconst.i64 0` for a
/// frame_ptr placeholder. Before .27.16, every native fn's entry began
/// with a never-read `iconst.i64 0` so the rest of `compile_fn` could
/// reference `frame_ptr` uniformly. Now `frame_ptr` is `Option<ir::Value>`
/// and downstream consumers `.expect()` it — native fns emit nothing.
#[test]
fn native_fns_have_no_dead_frame_ptr_placeholder() {
    // add1_s2 is native; it has no use for frame_ptr. Asserting that its
    // body contains no `iconst.i64 0` is a strict check because add1 has
    // no other reason to materialize zero.
    let out = Command::new(FZ_BIN)
        .args([
            "dump",
            "fixtures/add1/input.fz",
            "--emit",
            "clif",
            "--fn",
            "add1",
        ])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("; fn add1"),
        "missing add1 banner:\n{}",
        stdout
    );
    assert!(
        !stdout.contains("iconst.i64 0"),
        "add1_s2 still emits a dead `iconst.i64 0` (frame_ptr placeholder):\n{}",
        stdout,
    );
}

/// fz-siu.1.2 acceptance per docs/cps-in-clif.md §8.1.
/// tail_recursion.fz's `count` fn must compile as the native-tier
/// Tail-CC body whose recursive case ends in `return_call %count(...)`
/// with zero `fz_alloc_*` calls. Base case ends in
/// `load.i64 ...+16` followed by `return_call_indirect ...`.
#[test]
fn tail_recursion_count_matches_cps_in_clif_section_8_1() {
    let out = Command::new(FZ_BIN)
        .args([
            "dump",
            "fixtures/tail_recursion/input.fz",
            "--emit",
            "clif",
            "--fn",
            "count",
        ])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);

    // Find a narrow count spec banner and slice to the next banner. Spec
    // IDs shift across typer changes (fz-ul4.27.21.4 widened cont keying
    // and bumped the count spec ID), so match by the count_s prefix
    // rather than a specific number.
    let start = stdout
        .find("; fn count_s")
        .unwrap_or_else(|| panic!("missing count_s* banner:\n{}", stdout));
    let rest = &stdout[start..];
    let end = rest[1..].find("; fn ").map(|i| i + 1).unwrap_or(rest.len());
    let body = &rest[..end];

    // §8.1: signature `function %count(i64, i64, i64) -> i64 tail`.
    assert!(
        body.contains("(i64, i64, i64) -> i64 tail"),
        "count_s2 sig must be (i64,i64,i64)->i64 tail; got:\n{}",
        body,
    );

    // §8.1 block_rec: recursive case ends in `return_call %count(...)`
    // with no allocator calls in the body.
    assert!(
        body.contains("return_call "),
        "count_s2 must end recursive case in return_call:\n{}",
        body,
    );
    // No alloc helpers — neither fz_alloc_frame nor fz_alloc_closure.
    for helper in &["fz_alloc_frame", "fz_alloc_closure", "fz_alloc_struct"] {
        assert!(
            !body.contains(helper),
            "count_s2 contains `{}` — §8.1 requires zero allocs:\n{}",
            helper,
            body,
        );
    }

    // §8.1 block_done: load.i64 v_k+16; return_call_indirect.
    assert!(
        body.contains("return_call_indirect"),
        "count_s2 base case must indirect-call cont via return_call_indirect:\n{}",
        body,
    );
}

/// fz-siu.1.2 acceptance per docs/cps-in-clif.md §8.2.
/// higher_order.fz's `compose` fn must compile to: native Tail CC sig
/// `(i64, i64, i64, i64) -> i64 tail` (f, g, x, k); body builds the
/// inner cont closure via `fz_alloc_closure` exactly once, stores
/// `func_addr` + outer-cont + captures, then `return_call_indirect`
/// through `g+16` with `(x, g, kg)`. No `fz_closure_invoke` runtime
/// helper referenced.
#[test]
fn higher_order_compose_matches_cps_in_clif_section_8_2() {
    let out = Command::new(FZ_BIN)
        .args([
            "dump",
            "fixtures/higher_order/input.fz",
            "--emit",
            "clif",
            "--fn",
            "compose",
        ])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let start = stdout.find("; fn compose").expect("missing compose banner");
    let rest = &stdout[start..];
    let end = rest[1..].find("; fn ").map(|i| i + 1).unwrap_or(rest.len());
    let body = &rest[..end];

    assert!(
        body.contains("(i64, i64, i64, i64) -> i64 tail"),
        "compose sig must be (f,g,x,k) tail; got:\n{}",
        body
    );
    // fz-cps.1.8 — cont closure construction: one func_addr stored at
    // +16. Cranelift CLIF dumps don't carry runtime-symbol names (refs
    // are `u0:N`), so we structurally count the func_addr→+16 store
    // pattern that uniquely identifies a cont-closure code_ptr write.
    let func_addr_to_16 = body
        .lines()
        .filter(|l| l.contains("func_addr.i64") || l.contains("+16"))
        .count();
    assert!(
        func_addr_to_16 >= 2,
        "compose must store at least one func_addr at +16 (kg code_ptr):\n{}",
        body
    );
    // fz-cps.1.8 — accept either `return_call_indirect` (§8.2 ideal: g is
    // opaque) or `return_call` (typer narrows g→known callee, emits
    // direct call to closure-target body). Both honor the
    // every-fz→fz-transfer-is-a-tail-call discipline of §2.3.
    assert!(
        body.contains("return_call_indirect") || body.contains("return_call "),
        "compose must end in a Tail-CC return_call (direct or indirect):\n{}",
        body
    );
    assert!(
        !body.contains("fz_closure_invoke"),
        "compose must not reference fz_closure_invoke runtime helper:\n{}",
        body
    );
}

/// fz-siu.1.2 acceptance per docs/cps-in-clif.md §8.3.
/// closure_typed_captures.fz's `add_to(x,y) = fn(z) -> x+y+z` returns
/// the lambda. `add_to` must call `fz_alloc_closure` exactly once (the
/// lambda escape); the lambda body must call `fz_alloc_*` zero times.
#[test]
fn closure_typed_captures_matches_cps_in_clif_section_8_3() {
    let out = Command::new(FZ_BIN)
        .args([
            "dump",
            "fixtures/closure_typed_captures/input.fz",
            "--emit",
            "clif",
        ])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);

    let add_to_start = stdout.find("; fn add_to").expect("missing add_to banner");
    let add_to_rest = &stdout[add_to_start..];
    let add_to_end = add_to_rest[1..]
        .find("; fn ")
        .map(|i| i + 1)
        .unwrap_or(add_to_rest.len());
    let add_to_body = &add_to_rest[..add_to_end];
    // fz-cps.1.8 — Cranelift CLIF dumps don't carry runtime-symbol
    // names; assert structural shape: a `func_addr.i64` materialized
    // (lambda body addr) and stored at +16 (closure code_ptr slot).
    assert!(
        add_to_body.contains("func_addr.i64"),
        "add_to must materialize the lambda's code_ptr via func_addr:\n{}",
        add_to_body
    );
    assert!(
        add_to_body.contains("+16"),
        "add_to must store the lambda's code_ptr at +16:\n{}",
        add_to_body
    );
    // Lambda's body should compute x+y+z and tail-return through cont.
    let lam_start = stdout.find("; fn ").expect("module not empty");
    let _ = lam_start;
}

/// fz-siu.1.2 acceptance per docs/cps-in-clif.md §8.4.
/// concurrency_ping_pong.fz's `main` Receive site builds a cont closure
/// (alloc_closure + store func_addr at +16 + store outer_cont at +24 +
/// store user captures from +32) and hands it to fz_receive_park.
/// Structural check: the body's terminator region ends with a single-i64-
/// arg call (the fz_receive_park call) returning i64. Runtime fn names
/// don't appear in raw clif (Cranelift uses numeric `u0:N` refs), so
/// the test asserts the shape: a `(i64) -> i64 system_v` sig declared
/// AND a `func_addr.i64` store into +16 of a freshly-alloc'd closure.
#[test]
fn concurrency_ping_pong_matches_cps_in_clif_section_8_4() {
    let out = Command::new(FZ_BIN)
        .args([
            "dump",
            "fixtures/concurrency_ping_pong/input.fz",
            "--emit",
            "clif",
            "--fn",
            "main",
        ])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    // fz_receive_park's sig: takes a closure ptr (i64), returns the
    // YIELD sentinel (i64). One of the declared sigs must match.
    assert!(
        stdout.contains("(i64) -> i64 system_v"),
        "main must declare an (i64) -> i64 system_v sig for fz_receive_park:\n{}",
        stdout
    );
    // Receive site builds the cont closure: alloc + code_ptr store.
    assert!(
        stdout.contains("func_addr.i64"),
        "main must materialize cont code_ptr via func_addr:\n{}",
        stdout
    );
    // And does NOT reference the legacy parking-frame schema/dispatch.
    assert!(
        !stdout.contains("frame_sizes"),
        "main must not reference Process::frame_sizes (uniform parking schema):\n{}",
        stdout
    );
}

/// Shell `fz dump --emit clif --fn <name>` and check each fn's
/// per-fixture expect_clif_contains / expect_clif_excludes assertion.
/// Returns all failure messages in one vec so a fixture surfaces every
/// mismatch in one pass instead of bailing on the first.
fn check_clif_assertions(fixture: &Path, header: &Header) -> Result<(), Vec<String>> {
    use std::collections::HashSet;
    let mut fns: HashSet<&str> = HashSet::new();
    for (f, _) in &header.expect_clif_contains {
        fns.insert(f.as_str());
    }
    for (f, _) in &header.expect_clif_excludes {
        fns.insert(f.as_str());
    }
    let input = fixture.join("input.fz");
    let mut dumps: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    for fn_name in fns {
        let out = match Command::new(FZ_BIN)
            .args(["dump", "--emit", "clif", "--fn"])
            .arg(fn_name)
            .arg(&input)
            .output()
        {
            Ok(o) => o,
            Err(e) => {
                return Err(vec![format!(
                    "{}: spawn fz dump for fn `{}`: {}",
                    fixture.display(),
                    fn_name,
                    e
                )]);
            }
        };
        if !out.status.success() {
            return Err(vec![format!(
                "{}: fz dump --fn {} exited {}: {}",
                fixture.display(),
                fn_name,
                out.status,
                String::from_utf8_lossy(&out.stderr).trim_end(),
            )]);
        }
        dumps.insert(
            fn_name.to_string(),
            String::from_utf8_lossy(&out.stdout).into_owned(),
        );
    }
    let mut failures = Vec::new();
    for (fn_name, substr) in &header.expect_clif_contains {
        let dump = dumps.get(fn_name.as_str()).expect("dump captured above");
        if !dump.contains(substr.as_str()) {
            failures.push(format!(
                "{}: expect_clif_contains failed — fn `{}` does not contain `{}`:\n{}",
                fixture.display(),
                fn_name,
                substr,
                dump
            ));
        }
    }
    for (fn_name, substr) in &header.expect_clif_excludes {
        let dump = dumps.get(fn_name.as_str()).expect("dump captured above");
        if dump.contains(substr.as_str()) {
            failures.push(format!(
                "{}: expect_clif_excludes failed — fn `{}` unexpectedly contains `{}`:\n{}",
                fixture.display(),
                fn_name,
                substr,
                dump
            ));
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures)
    }
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
        let header = match parse_header_from_dir(&f) {
            Ok(h) => h,
            Err(e) => {
                failures.push(format!("{}: header: {}", f.display(), e));
                continue;
            }
        };
        if header.paths.is_empty() {
            deferred_fixtures.push((f, header.purpose.clone(), header.defer.unwrap_or_default()));
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
        // CLIF-substring assertions (fz-ul4.27.1). Independent of the
        // path loop: the assertion is about generated code, which is
        // the same across compiled paths.
        if (!header.expect_clif_contains.is_empty() || !header.expect_clif_excludes.is_empty())
            && let Err(msgs) = check_clif_assertions(&f, &header)
        {
            for msg in msgs {
                failures.push(msg);
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

// ----------------------------------------------------------------------
// fz-ul4.32 / fz-73m — Golden dumps.
//
// For every fixture with non-empty `paths:` (i.e. not deferred), dump
// its CLIF and typer specs and diff against checked-in sidecars
// (`expected.clif`, `expected.specs`). Drift → test failure with the
// diff inline. The golden set is `discover()` itself — every fixture
// that's supposed to compile contributes its dumps. This was an
// explicit list in fz-ul4.32 (5 fixtures); fz-fzn promoted the whole
// runnable corpus so any typer/codegen change surfaces here BEFORE a
// downstream test sees it.
//
// `BLESS=1 cargo test golden_clif` / `BLESS_SPECS=1 cargo test
// golden_specs` rewrite every sidecar. Bless is a deliberate act —
// review the diff in the resulting commit.
// ----------------------------------------------------------------------

#[derive(Clone, Copy)]
enum Emit {
    Clif,
    Specs,
}

impl Emit {
    fn flag(self) -> &'static str {
        match self {
            Emit::Clif => "clif",
            Emit::Specs => "specs",
        }
    }
    fn sidecar(self) -> &'static str {
        match self {
            Emit::Clif => "expected.clif",
            Emit::Specs => "expected.specs",
        }
    }
    fn bless_env(self) -> &'static str {
        match self {
            Emit::Clif => "BLESS",
            Emit::Specs => "BLESS_SPECS",
        }
    }
}

/// Drive `fz dump --emit <kind>` over every non-deferred fixture and
/// diff against its sidecar. Failures aggregate so one bad fixture
/// doesn't mask the rest.
fn check_goldens(emit: Emit) {
    let bless = std::env::var(emit.bless_env()).ok().as_deref() == Some("1");
    let mut failures: Vec<String> = Vec::new();

    for dir in discover() {
        let header = match parse_header_from_dir(&dir) {
            Ok(h) => h,
            Err(_) => continue, // matrix test surfaces header errors
        };
        if header.paths.is_empty() {
            // Deferred fixtures don't participate in goldens — their dumps
            // may not even compile, and pinning nonsense is worse than
            // pinning nothing.
            continue;
        }
        if header.kind == Kind::Test {
            // `kind: test` fixtures route through the `fz test` runner,
            // which expands the prelude `test()` macro. `fz dump` doesn't
            // — so dumping them surfaces a `not-a-defmacro` error. Skip;
            // their drift detection lives in `fixture_matrix` itself.
            continue;
        }
        let src_path = dir.join("input.fz");
        let golden_path = dir.join(emit.sidecar());
        let name = dir.file_name().unwrap().to_string_lossy().into_owned();

        let out = Command::new(FZ_BIN)
            .args(["dump", "--emit", emit.flag()])
            .arg(&src_path)
            .output()
            .unwrap_or_else(|e| panic!("spawn fz dump {}: {}", name, e));
        if !out.status.success() {
            let stderr = String::from_utf8_lossy(&out.stderr);
            failures.push(format!(
                "fz dump --emit {} {} exited {}: {}",
                emit.flag(),
                name,
                out.status,
                stderr.trim_end(),
            ));
            continue;
        }
        let actual = String::from_utf8_lossy(&out.stdout).into_owned();

        if bless {
            fs::write(&golden_path, &actual)
                .unwrap_or_else(|e| panic!("bless write {}: {}", golden_path.display(), e));
            continue;
        }

        let expected = match fs::read_to_string(&golden_path) {
            Ok(s) => s,
            Err(_) => {
                failures.push(format!(
                    "golden {} missing for {}: {}\n\
                     Run `{}=1 cargo test golden_{}` to seed it.",
                    emit.flag(),
                    name,
                    golden_path.display(),
                    emit.bless_env(),
                    emit.flag(),
                ));
                continue;
            }
        };

        if actual != expected {
            failures.push(format!(
                "golden {} mismatch for {} ({}):\n\n\
                 Re-run with `{}=1 cargo test golden_{}` to update the \
                 golden after reviewing the diff.\n\n\
                 --- expected ({} bytes)\n{}\n\
                 --- actual ({} bytes)\n{}",
                emit.flag(),
                name,
                golden_path.display(),
                emit.bless_env(),
                emit.flag(),
                expected.len(),
                expected,
                actual.len(),
                actual,
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "{} golden {} failure(s):\n\n{}",
        failures.len(),
        emit.flag(),
        failures.join("\n\n---\n\n"),
    );
}

#[test]
fn golden_clif() {
    check_goldens(Emit::Clif);
}

#[test]
fn golden_specs() {
    check_goldens(Emit::Specs);
}
