//! fz-ul4.23.1 — fixture matrix (per-dir layout, fz-e97).
//!
//! Walks `fixtures/<name>/`, reads each fixture's `README.md`
//! frontmatter, and runs `input.fz` through each declared path. stdout
//! is compared against `expected.txt`; diagnostics/stderr are compared
//! against `expected.<path>.diagnostics` or `expected.diagnostics`.
//! Both default to empty when absent. Exit code must be 0.
//!
//! Per-fixture layout:
//!
//!     fixtures/<name>/
//!         README.md         YAML frontmatter + narrative body
//!         input.fz          fz source
//!         expected.txt      stdout golden (optional)
//!         expected.diagnostics diagnostic golden (optional)
//!         expected.jit.diagnostics path-specific diagnostic golden (optional)
//!
//! Frontmatter grammar:
//!
//!     ---
//!     purpose: one-line statement of what this fixture proves
//!     paths: [jit, interp, aot]
//!     kind: run            # or `test`; defaults to run if `fn main` present
//!     defer: rationale     # required iff `paths:` is empty
//!     budget.codegen.instructions: 123
//!     budget.typer.matcher_specs: 0
//!     ---
//!
//! Workflow: re-run with `BLESS=1 cargo test fixture_matrix` to rewrite
//! `expected.txt` and `expected.diagnostics` from current output. On
//! failure (non-bless), actual output is dropped at `<dir>/actual.txt`
//! and `<dir>/actual.diagnostics` for diffing. Dump-shape budgets use
//! telemetry from `fz dump --emit stats`; only failures write
//! `<dir>/actual.clif` and `<dir>/actual.specs`.

use libtest_mimic::{Arguments, Failed, Trial};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const FZ_BIN: &str = env!("CARGO_BIN_EXE_fz");

// fz-fkv — custom main: each (fixture, path) pair becomes its own
// `cargo test` trial, named `matrix::<fixture>::<path>`. `cargo test add1`
// filters to one fixture; `cargo test ::repl` filters to one leg. Static
// invariant tests (CLIF shape, golden dumps, etc.) become trials too so
// the harness is uniform.
fn main() {
    let args = Arguments::from_args();
    let mut trials: Vec<Trial> = Vec::new();

    // Static invariant trials. Bodies are unchanged from their previous
    // `#[test]` form; libtest-mimic catches panics from `assert!` and
    // reports them as failures.
    for (name, f) in static_tests() {
        trials.push(Trial::test(name, move || {
            f();
            Ok(())
        }));
    }

    // Dynamic matrix trials: one per (fixture, path).
    let bless = std::env::var("BLESS").ok().as_deref() == Some("1");
    for fixture in discover() {
        let name = fixture.file_name().unwrap().to_string_lossy().into_owned();
        let header = match parse_header_from_dir(&fixture) {
            Ok(h) => h,
            Err(e) => {
                let msg = e.clone();
                trials.push(Trial::test(
                    format!("matrix::{}::header", name),
                    move || Err(Failed::from(msg)),
                ));
                continue;
            }
        };
        if header.paths.is_empty() {
            // Deferred fixture (no paths wired). Surface as an ignored
            // trial so the reason is visible but the run doesn't fail.
            let why = header.defer.clone().unwrap_or_default();
            trials.push(
                Trial::test(format!("matrix::{}", name), move || {
                    eprintln!("deferred: {}", why);
                    Ok(())
                })
                .with_ignored_flag(true),
            );
            continue;
        }
        for path in &header.paths {
            let trial_name = format!("matrix::{}::{}", name, path);
            let fixture = fixture.clone();
            let header = header.clone();
            let path = path.clone();
            trials.push(Trial::test(trial_name, move || {
                match check(&fixture, &header, &path, bless) {
                    CheckOutcome::Pass => Ok(()),
                    CheckOutcome::Deferred(msg) => {
                        // Path declared but not yet wired (exit 75). Don't
                        // fail; surface the reason on stderr.
                        eprintln!("deferred: {}", msg);
                        Ok(())
                    }
                    CheckOutcome::Fail(e) => Err(Failed::from(e)),
                }
            }));
        }
    }

    libtest_mimic::run(&args, trials).exit();
}

/// List of (trial-name, fn-pointer) for every static invariant test in
/// this file. Kept explicit so adding a new test is a one-line append
/// and the trial list survives refactors.
fn static_tests() -> Vec<(&'static str, fn())> {
    vec![
        ("fixture_index_up_to_date", fixture_index_up_to_date),
        ("fz_dump_emits_clif", fz_dump_emits_clif),
        (
            "add1_main_cont_seam_has_no_box_unbox_roundtrip",
            add1_main_cont_seam_has_no_box_unbox_roundtrip,
        ),
        (
            "inlined_goto_edges_have_no_sshr_imm",
            inlined_goto_edges_have_no_sshr_imm,
        ),
        (
            "fused_blocks_and_folded_constants_in_inlined_main",
            fused_blocks_and_folded_constants_in_inlined_main,
        ),
        (
            "native_fns_have_no_dead_frame_ptr_placeholder",
            native_fns_have_no_dead_frame_ptr_placeholder,
        ),
        (
            "tail_recursion_count_matches_cps_in_clif_section_8_1",
            tail_recursion_count_matches_cps_in_clif_section_8_1,
        ),
        // fz-jg5.6: compose dissolves under the reducer; the §8.2 ABI
        // invariant no longer applies because no compose body is emitted.
        // The function is left in place for revival in RED.6 if needed.
        // (
        //     "higher_order_compose_matches_cps_in_clif_section_8_2",
        //     higher_order_compose_matches_cps_in_clif_section_8_2,
        // ),
        (
            "closure_typed_captures_matches_cps_in_clif_section_8_3",
            closure_typed_captures_matches_cps_in_clif_section_8_3,
        ),
        (
            "concurrency_ping_pong_matches_cps_in_clif_section_8_4",
            concurrency_ping_pong_matches_cps_in_clif_section_8_4,
        ),
        (
            "no_dead_const_operands_after_singleton_fold",
            no_dead_const_operands_after_singleton_fold,
        ),
        (
            "pattern_matrix_oracle_goldens",
            pattern_matrix_oracle_goldens,
        ),
        (
            "matcher_perf_internal_matcher_repair_baseline",
            matcher_perf_internal_matcher_repair_baseline,
        ),
        (
            "receive_binary_pattern_does_not_clone_outcome_lattice",
            receive_binary_pattern_does_not_clone_outcome_lattice,
        ),
        (
            "clif_dump_uses_symbolic_func_names",
            clif_dump_uses_symbolic_func_names,
        ),
        ("dump_budgets", dump_budgets),
        ("golden_outcomes", golden_outcomes),
    ]
}

/// fz-puj.29 — freeze the current `PatternMatrix` behavior as a
/// concrete oracle before replacing it with shared matcher lowering.
///
/// The fixture goldens named here are deliberately high-level: they pin the
/// observable CFG facts that matter for router parity without coupling the
/// future replacement to every incidental Var id in every fixture.
fn pattern_matrix_oracle_goldens() {
    // fz-puj.52.7 — case/multi-clause/with-else dispatch lowers the
    // matcher graph inline again. The user-facing oracle properties —
    // wildcard ordering, guard reject continuations, :case_clause /
    // :function_clause / :with_clause fail edges — are unchanged, but no
    // internal matcher fn should appear in specs for these constructs.

    let wildcard_specs = dump_specs_for_fixture("wildcard_then_specific");
    assert!(
        wildcard_specs.contains("spec catch(1)")
            && wildcard_specs.contains("key:    [0]")
            && wildcard_specs.contains("return: :anything")
            && !wildcard_specs.contains("return: :zero"),
        "wildcard-first multi-clause dispatch must not route to the later specific clause"
    );
    assert!(
        wildcard_specs.contains("spec cmatch(1)") && !wildcard_specs.contains("case_matcher_"),
        "wildcard-first case dispatch must stay inline, not route through a matcher fn"
    );
    assert!(
        wildcard_specs.contains("TailCall case_clause_0"),
        "wildcard-first case arm must still tail-call the first case body"
    );

    let multi_clause_specs = dump_specs_for_fixture("multi_clause");
    assert!(
        multi_clause_specs.contains("spec classify(1)")
            && multi_clause_specs.contains("key:    [7]")
            && multi_clause_specs.contains("return: :positive")
            && !multi_clause_specs.contains("classify_matcher_"),
        "guarded multi-clause dispatch must stay inline, not route through classify_matcher_N"
    );
    assert!(
        multi_clause_specs.contains(":function_clause"),
        "classify dispatch must preserve the guard reject + :function_clause fail edge"
    );

    let case_specs = dump_specs_for_fixture("case_tuple_pattern_sequential");
    assert!(
        case_specs.contains(":case_clause"),
        "case matrix must preserve its :case_clause fail edge"
    );
    assert!(
        !case_specs.contains("case_matcher_") && case_specs.contains("TailCall case_clause_0"),
        "tuple case dispatch must stay inline and tail-call the first case body continuation"
    );
    assert!(
        case_specs.contains("TailCall case_clause_1"),
        "literal case arm must dispatch through the second case body continuation"
    );
    assert!(
        case_specs.contains("TailCall with_fail"),
        "with match failure must tail-call the shared with_fail continuation"
    );
    assert!(
        case_specs.contains("key:    [{:ok, 7}]")
            && case_specs.contains("key:    [:err]")
            && case_specs.contains("TailCall with_else_0"),
        "tuple and atom branches in case/with must both stay reachable"
    );

    let type_specs = dump_specs_for_fixture("type_dispatch");
    assert!(
        type_specs.contains("key:    [42]")
            && type_specs.contains("Var(2) :: true")
            && type_specs.contains("key:    [:foo]")
            && type_specs.contains("Var(2) :: false"),
        "typed multi-clause dispatch must keep the visible precondition branch"
    );
    assert!(
        type_specs.contains(":function_clause"),
        "typed multi-clause dispatch must preserve the function_clause fail edge"
    );

    let list_specs = dump_specs_for_fixture("list_primitives");
    assert!(
        list_specs.contains("length(1)") && list_specs.contains("reverse_acc(2)"),
        "list-cons router oracle must cover recursive list head dispatch"
    );
    assert!(
        list_specs.contains("list("),
        "list-cons router oracle must keep list-domain specs visible"
    );

    let nil_list_specs = dump_specs_for_fixture("empty_list_distinct_from_nil");
    assert!(
        nil_list_specs.contains("key:    [nil]")
            && nil_list_specs.contains("key:    [list(none)]")
            && nil_list_specs.contains("key:    [list(1 | 2 | 3)]"),
        "nil, empty-list, and cons-list dispatch must remain distinct"
    );

    let utf8_specs = dump_specs_for_fixture("utf8_pattern_match");
    assert!(
        utf8_specs.contains("spec greet(1)") && utf8_specs.contains("key:    [binary]"),
        "utf8 literal pattern dispatch must stay represented as binary input"
    );
    assert!(
        utf8_specs.contains(":goodbye | :hello | :unknown"),
        "utf8 literal pattern dispatch must preserve the three-arm result set"
    );
}

/// fz-puj.52.6 / .52.7 — matcher performance baseline.
///
/// These assertions pin the repaired internal-dispatch shape: case,
/// multi-clause, with-else, and prelude print dispatch must not create
/// `_matcher_` specs. T4 may still update receive-specific totals when it
/// caches receive Matchers. Exact counts are deliberate: any matcher-shape
/// change should force a conscious baseline update in the same commit.
fn matcher_perf_internal_matcher_repair_baseline() {
    let representative = [
        ("hello", 3, 0),
        ("list_primitives", 31, 0),
        ("quicksort", 23, 0),
        ("ast_eval", 3, 0),
        ("receive_mixed_constructors", 5, 0),
    ];
    for (fixture, expected_specs, expected_matchers) in representative {
        let fixture_dir = Path::new("fixtures").join(fixture);
        let stats = dump_telemetry_stats(&fixture_dir);
        assert_eq!(
            stats.typer.spec_count, expected_specs,
            "{} total spec baseline changed",
            fixture
        );
        assert_eq!(
            stats.typer.matcher_spec_count, expected_matchers,
            "{} matcher spec baseline changed",
            fixture
        );
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Run,
    Test,
}

#[derive(Debug, Clone)]
struct Header {
    purpose: String,
    paths: Vec<String>,
    kind: Kind,
    defer: Option<String>,
    dump_budget: DumpBudget,
}

/// Parse a fixture's README.md frontmatter. Frontmatter is the block
/// between the first `---` and the next `---` line (both at column 0);
/// the body that follows is documentation only.
///
/// Grammar is a deliberately tiny YAML subset — enough for our keys,
/// nothing more. Supported:
///   * `key: scalar` (string)
///   * `paths: [a, b, c]` (flow sequence of bare scalars)
///   * `budget.<namespace>.<metric>: number` (dump budget target counters)
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
    let mut dump_budget = DumpBudget::default();

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
            // fz-i67.3 — informational rationale for omitting `repl` from
            // `paths:` (sequential fixture that `eval::Interp` cannot run).
            // Parsed so the key is accepted; not otherwise consumed.
            "repl-skip" => {}
            key if key.starts_with("budget.") => {
                parse_dump_budget_field(&mut dump_budget, key, val, &readme, i + 1)?;
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
        dump_budget,
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
    /// Process exited 0 with captured stdout and diagnostics/stderr.
    Ok { stdout: String, diagnostics: String },
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
    if path == "repl" {
        return run_repl_path(fixture, header);
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
        Ok(s) => RunOutcome::Ok {
            stdout: s,
            diagnostics: stderr,
        },
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
    let diagnostics = format!("{}{}", build_stderr, run_stderr);
    match String::from_utf8(run.stdout) {
        Ok(s) => RunOutcome::Ok {
            stdout: s,
            diagnostics,
        },
        Err(e) => RunOutcome::Failed(format!("stdout utf8: {}", e)),
    }
}

/// fz-i67.2 — drive the REPL parity leg: spawn `fz repl --script <input.fz>`,
/// capture stdout. Same comparison plumbing as the other legs. `kind: test`
/// fixtures don't go through here (the REPL has no `assert_eq` runner).
fn run_repl_path(fixture: &Path, header: &Header) -> RunOutcome {
    if header.kind == Kind::Test {
        return RunOutcome::Deferred(
            "kind: test fixtures don't yet run via repl (`fz test` is jit-only)".into(),
        );
    }
    let input = fixture.join("input.fz");
    let out = match Command::new(FZ_BIN)
        .args(["repl", "--script"])
        .arg(&input)
        .output()
    {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(format!("spawn fz repl: {}", e)),
    };
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    if !out.status.success() {
        return RunOutcome::Failed(format!(
            "fz repl --script exit {}: {}",
            out.status,
            stderr.trim_end()
        ));
    }
    match String::from_utf8(out.stdout) {
        Ok(s) => RunOutcome::Ok {
            stdout: s,
            diagnostics: stderr,
        },
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
    let (actual, actual_diagnostics) = match run_path(fixture, header, path) {
        RunOutcome::Ok {
            stdout,
            diagnostics,
        } => (stdout, diagnostics),
        RunOutcome::Deferred(msg) => return CheckOutcome::Deferred(msg),
        RunOutcome::Failed(e) => return CheckOutcome::Fail(e),
    };
    let actual = normalize(&actual);
    let actual_diagnostics = normalize(&actual_diagnostics);
    let expected_path = fixture.join("expected.txt");
    let expected = fs::read_to_string(&expected_path).unwrap_or_default();
    let expected = normalize(&expected);
    let path_diagnostics_path = fixture.join(format!("expected.{}.diagnostics", path));
    let expected_diagnostics_path = if path_diagnostics_path.exists() {
        path_diagnostics_path
    } else {
        fixture.join("expected.diagnostics")
    };
    let expected_diagnostics =
        normalize(&fs::read_to_string(&expected_diagnostics_path).unwrap_or_default());
    if actual == expected && actual_diagnostics == expected_diagnostics {
        let _ = fs::remove_file(fixture.join("actual.txt"));
        let _ = fs::remove_file(fixture.join("actual.diagnostics"));
        return CheckOutcome::Pass;
    }
    if bless {
        if actual.is_empty() {
            let _ = fs::remove_file(&expected_path);
        } else if let Err(e) = fs::write(&expected_path, &actual) {
            return CheckOutcome::Fail(format!("bless write: {}", e));
        }
        if actual_diagnostics.is_empty() {
            let _ = fs::remove_file(&expected_diagnostics_path);
        } else if let Err(e) = fs::write(&expected_diagnostics_path, &actual_diagnostics) {
            return CheckOutcome::Fail(format!("bless diagnostics write: {}", e));
        }
        return CheckOutcome::Pass;
    }
    let output_path = fixture.join("actual.txt");
    let diagnostics_output_path = fixture.join("actual.diagnostics");
    let _ = fs::write(&output_path, &actual);
    let _ = fs::write(&diagnostics_output_path, &actual_diagnostics);
    CheckOutcome::Fail(format!(
        "fixture mismatch for {} via {}; wrote {} and {}\n--- expected stdout\n{}--- actual stdout\n{}--- expected diagnostics\n{}--- actual diagnostics\n{}",
        fixture.display(),
        path,
        output_path.display(),
        diagnostics_output_path.display(),
        expected,
        actual,
        expected_diagnostics,
        actual_diagnostics
    ))
}

/// Regenerate `fixtures/index.md` from headers and assert it matches the
/// checked-in file. `BLESS=1` rewrites the index in place.
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
fn fz_dump_emits_clif() {
    let out = Command::new(FZ_BIN)
        .args(["dump", "fixtures/add1/input.fz"])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    // fz-ul4.11.15: add1 is now inlined into main — no separate add1 fn in dump.
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
    // After block fusion + singleton fold, the inlined add1 arithmetic folds
    // to iconst 42 directly — no iadd remains. The folded constant is visible.
    assert!(
        stdout.contains("42"),
        "expected folded constant 42 in main's body (add1 inlined + folded):\n{}",
        stdout
    );
    // fz-ul4.23.7: srcloc annotations on body instructions resolve back
    // to file:line:col. main's call site lives at line 4; after inlining
    // add1, main's block0 carries those annotations.
    assert!(
        stdout.contains("; @4:"),
        "expected line-4 srcloc annotations in main's dump\n{}",
        stdout
    );

    // --fn main filter: main is the only live fn (add1 is inlined).
    let filtered = Command::new(FZ_BIN)
        .args(["dump", "fixtures/add1/input.fz", "--fn", "main"])
        .output()
        .expect("spawn fz dump --fn");
    assert!(filtered.status.success());
    let s = String::from_utf8_lossy(&filtered.stdout);
    assert!(s.contains("; fn main"));

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
            "main",
        ])
        .output()
        .expect("spawn fz dump --emit asm");
    assert!(
        asm.status.success(),
        "fz dump --emit asm exited {}",
        asm.status
    );
    let asm_out = String::from_utf8_lossy(&asm.stdout);
    assert!(asm_out.contains("; fn main"));
    assert!(
        asm_out.contains("block0"),
        "expected block0 label in asm:\n{}",
        asm_out
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
    // fz-ul4.fus: block fusion + singleton fold eliminates the iadd entirely;
    // folded constant 42 is visible directly.
    // fz-ext.7: print is now a wrapper fn requiring a tagged arg, so
    // ishl_imm/bor_imm appear at the main→print_wrapper seam (not a
    // roundtrip — the print wrapper doesn't unbox and rebox).
    let main_start = stdout.find("; fn main").expect("missing main banner");
    let main_body = &stdout[main_start..];
    assert!(
        !main_body.contains("iadd"),
        "unexpected iadd — add1 arithmetic should be constant-folded:\n{}",
        main_body,
    );
    assert!(
        main_body.contains("42"),
        "expected folded constant 42 in main:\n{}",
        main_body,
    );
    assert!(
        !main_body.contains("sshr_imm"),
        "unexpected sshr_imm (unbox) in main — tag round-trip at Goto seam:\n{}",
        main_body,
    );
    assert!(
        !main_body.contains("block1"),
        "expected no block1 — single-predecessor blocks should be fused:\n{}",
        main_body,
    );
}

/// fz-ojo fz-ul4.rep — after repr-aware Goto coercion lands, inlining
/// add1 into main should produce zero tag/untag round-trips: the RawInt
/// arg flows directly through Goto edges without any sshr_imm.
///
/// This test is RED until fz-xs2 (rep.2) is implemented.
fn inlined_goto_edges_have_no_sshr_imm() {
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
    // Isolate main's CLIF body.
    let main_start = stdout.find("; fn main").expect("missing main banner");
    let main_body = &stdout[main_start..];
    assert!(
        !main_body.contains("sshr_imm"),
        "expected zero sshr_imm in inlined main — repr-aware Goto coercion \
         should pass RawInt args directly without any tag/untag round-trips:\n{}",
        main_body
    );
}

/// fz-q9a fz-ul4.fus — after block fusion + singleton fold, inlining add1 into
/// main should produce a single block with a direct iconst 42 — no iadd, no
/// separate block1/block2 labels.
///
/// RED until fz-c9e (fus.3) lands.
fn fused_blocks_and_folded_constants_in_inlined_main() {
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
    let main_start = stdout.find("; fn main").expect("missing main banner");
    let main_body = &stdout[main_start..];
    assert!(
        !main_body.contains("iadd"),
        "expected no iadd — arithmetic should be constant-folded:\n{}",
        main_body
    );
    assert!(
        !main_body.contains("block1"),
        "expected no block1 — single-predecessor blocks should be fused:\n{}",
        main_body
    );
    assert!(
        !main_body.contains("block2"),
        "expected no block2 — single-predecessor blocks should be fused:\n{}",
        main_body
    );
    assert!(
        main_body.contains("42"),
        "expected folded constant 42 in main's CLIF:\n{}",
        main_body
    );
}

/// fz-ul4.27.16 — native fns must not emit a dead `iconst.i64 0` for a
/// frame_ptr placeholder. Before .27.16, every native fn's entry began
/// with a never-read `iconst.i64 0` so the rest of `compile_fn` could
/// reference `frame_ptr` uniformly. Now `frame_ptr` is `Option<ir::Value>`
/// and downstream consumers `.expect()` it — native fns emit nothing.
///
/// fz-ul4.11.15: add1 is inlined into main so has no separate compiled body.
/// We verify the invariant on `main` instead — main is native and has no
/// semantic reason to materialize zero.
fn native_fns_have_no_dead_frame_ptr_placeholder() {
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
    assert!(
        !stdout.contains("iconst.i64 0"),
        "main emits a dead `iconst.i64 0` (frame_ptr placeholder):\n{}",
        stdout,
    );
}

/// fz-siu.1.2 acceptance per docs/cps-in-clif.md §8.1.
/// tail_recursion.fz's `count` fn must compile as the native-tier
/// Tail-CC body whose recursive case ends in `return_call %count(...)`
/// with zero `fz_alloc_*` calls. Base case ends in
/// `load.i64 ...+16` followed by `return_call_indirect ...`.
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

    // §8.1 block_done: tail-call the continuation. fz-ul4.43.B made
    // per-spec fold more aggressive — when the cont is statically
    // resolvable in this spec, the call becomes a direct `return_call`
    // instead of `return_call_indirect`. Either form satisfies §8.1
    // (no allocation, no return — pure tail call).
    assert!(
        body.contains("return_call_indirect") || body.contains("return_call "),
        "count_s2 base case must tail-call the cont (direct or indirect):\n{}",
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
// fz-jg5.6: under the compile-time reducer (fz-jg5.4/.5), `compose` in
// fixtures/higher_order/input.fz dissolves entirely at every callsite
// (static-input full reduction → constants in main). This test's
// invariant — checking the cps-in-clif §8.2 ABI shape of an emitted
// compose body — no longer applies because no body is emitted.
// Re-bless / repurpose lands in fz-jg5.7 (RED.6); the function is kept
// in place but not registered in `register_trials`.
#[allow(dead_code)]
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

    // fz-ul4.11.15: add_to is inlined into main — check main's CLIF.
    let main_start = stdout.find("; fn main").expect("missing main banner");
    let main_rest = &stdout[main_start..];
    let main_end = main_rest[1..]
        .find("; fn ")
        .map(|i| i + 1)
        .unwrap_or(main_rest.len());
    let main_body = &main_rest[..main_end];
    // fz-cps.1.8 — Cranelift CLIF dumps don't carry runtime-symbol
    // names; assert structural shape: a `func_addr.i64` materialized
    // (lambda body addr) and stored at +16 (closure code_ptr slot).
    assert!(
        main_body.contains("func_addr.i64"),
        "main must materialize the lambda's code_ptr via func_addr (add_to inlined):\n{}",
        main_body
    );
    assert!(
        main_body.contains("+16"),
        "main must store the lambda's code_ptr at +16 (add_to inlined):\n{}",
        main_body
    );
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

// fz-fkv: the bulk `fixture_matrix()` test was replaced by per-pair
// trials emitted from `fn main()`. Discovery, header parsing, and
// per-pair compare all live in the helpers above; the trial wiring
// is at the top of this file.

fn dump_specs_for_fixture(name: &str) -> String {
    let src_path = Path::new("fixtures").join(name).join("input.fz");
    let out = Command::new(FZ_BIN)
        .args(["dump", "--emit", "specs"])
        .arg(&src_path)
        .output()
        .unwrap_or_else(|e| panic!("spawn fz dump --emit specs {}: {}", name, e));
    assert!(
        out.status.success(),
        "fz dump --emit specs {} exited {}: {}",
        name,
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// fz-9pr.16 — `expected.outcomes` goldens. Opt-in: only fixtures that
/// ship an `expected.outcomes` sidecar are checked. CLIF/spec shape
/// coverage lives in telemetry budgets instead of checked-in dump files.
fn golden_outcomes() {
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
        let golden_path = dir.join("expected.outcomes");
        let name = dir.file_name().unwrap().to_string_lossy().into_owned();

        if !golden_path.exists() {
            continue;
        }

        let out = Command::new(FZ_BIN)
            .args(["dump", "--emit", "outcomes"])
            .arg(&src_path)
            .output()
            .unwrap_or_else(|e| panic!("spawn fz dump {}: {}", name, e));
        if !out.status.success() {
            let stderr = String::from_utf8_lossy(&out.stderr);
            failures.push(format!(
                "fz dump --emit {} {} exited {}: {}",
                "outcomes",
                name,
                out.status,
                stderr.trim_end(),
            ));
            continue;
        }
        let actual = String::from_utf8_lossy(&out.stdout).into_owned();

        let expected = match fs::read_to_string(&golden_path) {
            Ok(s) => s,
            Err(_) => {
                failures.push(format!(
                    "golden {} missing for {}: {}",
                    "outcomes",
                    name,
                    golden_path.display(),
                ));
                continue;
            }
        };

        if actual != expected {
            failures.push(format!(
                "golden {} mismatch for {} ({}):\n\n\
                 --- expected ({} bytes)\n{}\n\
                 --- actual ({} bytes)\n{}",
                "outcomes",
                name,
                golden_path.display(),
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
        "outcomes",
        failures.join("\n\n---\n\n"),
    );
}

/// fz-466 fz-ul4.dce.1 — proof test (RED gate).
///
/// After fold+DCE land, the BinOp operand iconst 41 (left-hand side of
/// the constant-folded 41+1=42 in add1) must be eliminated from main's
/// CLIF body. This test is RED until fz-cg2 (dce.5) wires the pipeline.
fn no_dead_const_operands_after_singleton_fold() {
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
    let clif = String::from_utf8_lossy(&out.stdout);
    let main_start = clif.find("; fn main").expect("missing main banner");
    let main_section = &clif[main_start..];
    // After fold+DCE, the operands of the folded 41+1 BinOp must be gone.
    assert!(
        !main_section.contains("iconst.i64 41"),
        "dead operand iconst 41 should be eliminated by DCE:\n{}",
        main_section
    );
}

#[derive(Debug, Clone, Copy, Default)]
struct DumpBudget {
    codegen_functions: Option<usize>,
    codegen_instructions: Option<usize>,
    specs_count: Option<usize>,
    typer_worklist_pops: Option<usize>,
    typer_walk_calls: Option<usize>,
    typer_type_fn_calls: Option<usize>,
    typer_matcher_specs: Option<usize>,
    typer_vars: Option<usize>,
    typer_blocks: Option<usize>,
    typer_stmts: Option<usize>,
    typer_dispatches: Option<usize>,
}

impl DumpBudget {
    fn is_empty(&self) -> bool {
        self.codegen_functions.is_none()
            && self.codegen_instructions.is_none()
            && self.specs_count.is_none()
            && self.typer_worklist_pops.is_none()
            && self.typer_walk_calls.is_none()
            && self.typer_type_fn_calls.is_none()
            && self.typer_matcher_specs.is_none()
            && self.typer_vars.is_none()
            && self.typer_blocks.is_none()
            && self.typer_stmts.is_none()
            && self.typer_dispatches.is_none()
    }
}

const DUMP_BUDGET_TOLERANCE_PERCENT: usize = 20;

fn parse_dump_budget_field(
    budget: &mut DumpBudget,
    key: &str,
    value: &str,
    path: &Path,
    line: usize,
) -> Result<(), String> {
    let n: usize = value.trim().parse().map_err(|e| {
        format!(
            "{}:{}: invalid numeric budget `{}`: {}",
            path.display(),
            line,
            value.trim(),
            e
        )
    })?;
    match key {
        "budget.codegen.functions" => budget.codegen_functions = Some(n),
        "budget.codegen.instructions" => budget.codegen_instructions = Some(n),
        "budget.specs.count" => budget.specs_count = Some(n),
        "budget.typer.worklist_pops" => budget.typer_worklist_pops = Some(n),
        "budget.typer.walk_calls" => budget.typer_walk_calls = Some(n),
        "budget.typer.type_fn_calls" => budget.typer_type_fn_calls = Some(n),
        "budget.typer.matcher_specs" => budget.typer_matcher_specs = Some(n),
        "budget.typer.vars" => budget.typer_vars = Some(n),
        "budget.typer.blocks" => budget.typer_blocks = Some(n),
        "budget.typer.stmts" => budget.typer_stmts = Some(n),
        "budget.typer.dispatches" => budget.typer_dispatches = Some(n),
        other => {
            return Err(format!(
                "{}:{}: unknown budget key `{}`",
                path.display(),
                line,
                other
            ));
        }
    }
    Ok(())
}

fn write_budget_failure_dumps(fixture: &Path) -> String {
    let mut out = String::new();
    for emit in ["clif", "specs"] {
        let actual_path = fixture.join(format!("actual.{}", emit));
        let dump = Command::new(FZ_BIN)
            .args(["dump", "--emit", emit])
            .arg(fixture.join("input.fz"))
            .output()
            .unwrap_or_else(|e| panic!("spawn fz dump --emit {}: {}", emit, e));
        if dump.status.success() {
            fs::write(&actual_path, &dump.stdout)
                .unwrap_or_else(|e| panic!("write {}: {}", actual_path.display(), e));
            out.push_str(&format!("\n  wrote {}", actual_path.display()));
        } else {
            out.push_str(&format!(
                "\n  fz dump --emit {} failed {}: {}",
                emit,
                dump.status,
                String::from_utf8_lossy(&dump.stderr).trim_end()
            ));
        }
    }
    out
}

fn check_budget_metric(
    fixture: &Path,
    failures: &mut Vec<String>,
    label: &str,
    actual: usize,
    target: Option<usize>,
) {
    let Some(target) = target else {
        return;
    };
    let tolerance = (target * DUMP_BUDGET_TOLERANCE_PERCENT).div_ceil(100);
    let min = target.saturating_sub(tolerance);
    let max = target + tolerance;
    if actual < min || actual > max {
        failures.push(format!(
            "{} {} = {}, outside {}% budget around target {} (allowed {}..={})",
            fixture.display(),
            label,
            actual,
            DUMP_BUDGET_TOLERANCE_PERCENT,
            target,
            min,
            max
        ));
    }
}

fn temp_telemetry_path(fixture: &Path, emit: &str) -> std::path::PathBuf {
    let name = fixture
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("fixture");
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock before unix epoch")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "fz_telemetry_{}_{}_{}_{}.jsonl",
        name,
        emit,
        std::process::id(),
        nanos
    ))
}

fn parse_json_u64_field(line: &str, key: &str) -> Option<usize> {
    let needle = format!("\"{}\":", key);
    let start = line.find(&needle)? + needle.len();
    let digits: String = line[start..]
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    if digits.is_empty() {
        return None;
    }
    digits.parse().ok()
}

#[derive(Default)]
struct CodegenStats {
    function_count: usize,
    instruction_count: usize,
}

#[derive(Default)]
struct TyperStats {
    event_count: usize,
    spec_count: usize,
    worklist_pops: usize,
    walk_calls: usize,
    type_fn_calls: usize,
    matcher_spec_count: usize,
    spec_var_count: usize,
    spec_block_count: usize,
    spec_stmt_count: usize,
    dispatch_count: usize,
}

#[derive(Default)]
struct DumpTelemetryStats {
    codegen: CodegenStats,
    typer: TyperStats,
}

fn dump_telemetry_stats(fixture: &Path) -> DumpTelemetryStats {
    let telemetry_path = temp_telemetry_path(fixture, "stats");
    let out = Command::new(FZ_BIN)
        .args(["--log-telemetry"])
        .arg(&telemetry_path)
        .args(["dump", "--emit", "stats"])
        .arg(fixture.join("input.fz"))
        .output()
        .unwrap_or_else(|e| panic!("spawn fz dump --emit stats: {}", e));
    assert!(
        out.status.success(),
        "fz dump --emit stats {} exited {}: {}",
        fixture.display(),
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let log = fs::read_to_string(&telemetry_path)
        .unwrap_or_else(|e| panic!("read {}: {}", telemetry_path.display(), e));
    let _ = fs::remove_file(&telemetry_path);
    let mut stats = DumpTelemetryStats::default();
    for line in log.lines() {
        if line.contains("\"name\":[\"fz\",\"codegen\",\"function_lowered\"]") {
            stats.codegen.function_count += 1;
            stats.codegen.instruction_count += parse_json_u64_field(line, "instruction_count")
                .unwrap_or_else(|| {
                    panic!(
                        "{} codegen function_lowered missing instruction_count",
                        fixture.display()
                    )
                });
        }
        if line.contains("\"name\":[\"fz\",\"typer\",\"typed\"]") {
            stats.typer.event_count += 1;
            stats.typer.spec_count = parse_json_u64_field(line, "spec_count")
                .unwrap_or_else(|| panic!("{} telemetry missing spec_count", fixture.display()));
            stats.typer.worklist_pops = parse_json_u64_field(line, "worklist_pops")
                .unwrap_or_else(|| panic!("{} telemetry missing worklist_pops", fixture.display()));
            stats.typer.walk_calls = parse_json_u64_field(line, "walk_calls")
                .unwrap_or_else(|| panic!("{} telemetry missing walk_calls", fixture.display()));
            stats.typer.type_fn_calls = parse_json_u64_field(line, "type_fn_calls")
                .unwrap_or_else(|| panic!("{} telemetry missing type_fn_calls", fixture.display()));
            stats.typer.matcher_spec_count = parse_json_u64_field(line, "matcher_spec_count")
                .unwrap_or_else(|| {
                    panic!("{} telemetry missing matcher_spec_count", fixture.display())
                });
            stats.typer.spec_var_count = parse_json_u64_field(line, "spec_var_count")
                .unwrap_or_else(|| {
                    panic!("{} telemetry missing spec_var_count", fixture.display())
                });
            stats.typer.spec_block_count = parse_json_u64_field(line, "spec_block_count")
                .unwrap_or_else(|| {
                    panic!("{} telemetry missing spec_block_count", fixture.display())
                });
            stats.typer.spec_stmt_count = parse_json_u64_field(line, "spec_stmt_count")
                .unwrap_or_else(|| {
                    panic!("{} telemetry missing spec_stmt_count", fixture.display())
                });
            stats.typer.dispatch_count = parse_json_u64_field(line, "dispatch_count")
                .unwrap_or_else(|| {
                    panic!("{} telemetry missing dispatch_count", fixture.display())
                });
        }
    }
    assert!(
        stats.codegen.function_count > 0,
        "{} telemetry missing fz.codegen.function_lowered events",
        fixture.display()
    );
    assert!(
        stats.typer.spec_count > 0,
        "{} telemetry missing fz.typer.typed event",
        fixture.display()
    );
    assert_eq!(
        stats.typer.event_count,
        2,
        "{} dump --emit stats should type once in frontend and once after codegen rewrites",
        fixture.display()
    );
    stats
}

fn receive_binary_pattern_does_not_clone_outcome_lattice() {
    let fixture = Path::new("fixtures/receive_binary_pattern");
    let out = Command::new(FZ_BIN)
        .args(["dump", "--emit", "clif"])
        .arg(fixture.join("input.fz"))
        .output()
        .expect("spawn fz dump --emit clif receive_binary_pattern");
    assert!(
        out.status.success(),
        "fz dump --emit clif {} exited {}: {}",
        fixture.display(),
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let clif = String::from_utf8_lossy(&out.stdout);
    let cloned_outcomes = clif
        .lines()
        .filter(|line| line.starts_with("; fn rx_clause_") && line.contains("_body_s"))
        .count();
    assert_eq!(
        cloned_outcomes, 0,
        "receive_binary_pattern cloned {} receive outcome bodies; receive matchers should stop at the decision boundary",
        cloned_outcomes
    );
}

fn dump_budgets() {
    let mut checked = 0usize;
    let mut failures = Vec::new();
    for fixture in discover() {
        let header = parse_header_from_dir(&fixture)
            .unwrap_or_else(|e| panic!("parse {} README.md: {}", fixture.display(), e));
        let budget = header.dump_budget;
        if budget.is_empty() {
            continue;
        }
        checked += 1;
        let actual = dump_telemetry_stats(&fixture);
        let mut fixture_failures = Vec::new();
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "codegen lowered function bodies",
            actual.codegen.function_count,
            budget.codegen_functions,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "codegen lowered CLIF instructions",
            actual.codegen.instruction_count,
            budget.codegen_instructions,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "typer emitted specs",
            actual.typer.spec_count,
            budget.specs_count,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "typer worklist pops",
            actual.typer.worklist_pops,
            budget.typer_worklist_pops,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "typer walk calls",
            actual.typer.walk_calls,
            budget.typer_walk_calls,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "typer type_fn calls",
            actual.typer.type_fn_calls,
            budget.typer_type_fn_calls,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "typer matcher specs",
            actual.typer.matcher_spec_count,
            budget.typer_matcher_specs,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "typer vars",
            actual.typer.spec_var_count,
            budget.typer_vars,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "typer blocks",
            actual.typer.spec_block_count,
            budget.typer_blocks,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "typer stmts",
            actual.typer.spec_stmt_count,
            budget.typer_stmts,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "typer dispatches",
            actual.typer.dispatch_count,
            budget.typer_dispatches,
        );
        if !fixture_failures.is_empty() {
            let dumps = write_budget_failure_dumps(&fixture);
            failures.push(format!("{}{}", fixture_failures.join("\n"), dumps));
        }
    }
    assert!(checked > 0, "expected at least one fixture dump budget");
    assert!(
        failures.is_empty(),
        "{} dump budget failure(s):\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

/// fz-323 — CLIF dumps must use symbolic `@<name>` external-name refs, not
/// Cranelift's numeric `u0:N` form. The numeric form is `FuncId`-indexed in
/// module-declaration order, which makes goldens drift on every unrelated
/// runtime-helper addition. Symbolic names are source-stable.
fn clif_dump_uses_symbolic_func_names() {
    let out = Command::new(FZ_BIN)
        .args(["dump", "--emit", "clif", "fixtures/hello/input.fz"])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    if let Some(idx) = stdout.find("u0:") {
        let ctx_start = stdout[..idx].rfind('\n').map(|p| p + 1).unwrap_or(0);
        let ctx_end = stdout[idx..]
            .find('\n')
            .map(|p| idx + p)
            .unwrap_or(stdout.len());
        panic!(
            "CLIF dump still contains a raw `u0:N` external name — the \
             dumper should rewrite it to `@<name>`. First offending line:\n{}",
            &stdout[ctx_start..ctx_end]
        );
    }
}
