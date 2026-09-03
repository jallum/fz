use std::collections::{BTreeMap, BTreeSet};
use std::env::temp_dir;
use std::ffi::OsStr;
use std::fs::{metadata, read_to_string, remove_file, write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, id};
use std::sync::atomic::{AtomicU64, Ordering};

use fz::causal::{CausalReport, FormulaWork, ProductWork, parse_public_trace};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");
static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn unique_temp_path(prefix: &str, suffix: &str) -> PathBuf {
    let nonce = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    temp_dir().join(format!("{}_{}_{}{}", prefix, id(), nonce, suffix))
}

fn run_fz2(args: &[&OsStr]) -> Output {
    Command::new(FZ2_BIN).args(args).output().expect("invoke fz2 binary")
}

fn run_fz2_without_color(args: &[&OsStr]) -> Output {
    Command::new(FZ2_BIN)
        .env("NO_COLOR", "1")
        .args(args)
        .output()
        .expect("invoke fz2 binary")
}

fn fixture_expected_stdout(path: &str) -> String {
    // Goldens are stem-scoped sidecars (`<stem>.expected.txt`), the same naming
    // `fixture_matrix` resolves via `sidecar_path`. The earlier `expected.txt`
    // sibling never existed, so every output-bearing fixture silently compared
    // against the empty string; fixtures that print nothing matched by accident.
    let fixture = Path::new(path);
    let stem = fixture
        .file_stem()
        .and_then(OsStr::to_str)
        .unwrap_or_else(|| panic!("fixture path has no stem: {path}"));
    let expected = fixture.with_file_name(format!("{stem}.expected.txt"));
    if expected.exists() {
        read_to_string(&expected).unwrap_or_else(|error| panic!("read {}: {error}", expected.display()))
    } else {
        String::new()
    }
}

/// Trailing-newline normalization, identical to `fixture_matrix`'s `normalize`:
/// a golden and a program's stdout that differ only by a final newline are the
/// same observation. Keeping this in step with the matrix means the two harnesses
/// judge fixture output by one rule instead of drifting apart.
fn normalize_stdout(s: &str) -> String {
    if s.is_empty() || s.ends_with('\n') {
        s.to_string()
    } else {
        format!("{s}\n")
    }
}

fn assert_successful_stdout(out: &Output, expected: &str, context: &str) {
    assert!(
        out.status.success(),
        "{context} should succeed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        normalize_stdout(&String::from_utf8(out.stdout.clone()).expect("stdout is utf-8")),
        normalize_stdout(expected),
        "{context} should print the expected stdout"
    );
    assert!(
        out.stderr.is_empty(),
        "{context} should write nothing to stderr; got: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

fn assert_compiler2_telemetry_only(path: &Path, context: &str) {
    let log = read_to_string(path).unwrap_or_else(|error| panic!("read telemetry log {}: {error}", path.display()));
    assert!(
        log.contains("\"compiler2\""),
        "{context} should emit compiler2 telemetry; log=\n{log}",
    );
    assert!(
        !log.contains("\"planner\""),
        "{context} should not emit legacy planner telemetry; log=\n{log}",
    );
    assert!(
        !log.contains("\"type_infer\""),
        "{context} should not emit legacy type_infer telemetry; log=\n{log}",
    );
    assert!(
        !log.contains("\"frontend\""),
        "{context} should not invoke the old frontend path; log=\n{log}",
    );
}

fn assert_bounded_public_trace(path: &Path, context: &str, max_events: usize, max_bytes: u64) {
    let log = read_to_string(path).unwrap_or_else(|error| panic!("read telemetry log {}: {error}", path.display()));
    assert!(
        log.lines().count() <= max_events,
        "{context} exceeded telemetry event budget: {} > {max_events}",
        log.lines().count()
    );
    assert!(
        metadata(path).expect("telemetry metadata").len() <= max_bytes,
        "{context} exceeded telemetry byte budget"
    );
    assert!(
        log.contains("\"pull\",\"session\""),
        "{context} needs a pull session signal"
    );
    assert!(
        log.contains("\"pull\",\"product\",\"settled\""),
        "{context} needs a settled product signal"
    );
    assert!(log.contains("\"job\""), "{context} needs job hotspot signal");
}

fn assert_lexer_passes_match_submitted_sources(path: &Path, context: &str, expected_sources: &[String]) {
    let log = read_to_string(path).unwrap_or_else(|error| panic!("read telemetry log {}: {error}", path.display()));
    let mut counts = BTreeMap::<String, usize>::new();
    for line in log.lines() {
        if !line.contains("\"name\":[\"fz\",\"lexer\",\"pass\"]") || !line.contains("\"kind\":\"span_start\"") {
            continue;
        }
        let source = json_string_field(line, "source_name")
            .unwrap_or_else(|| panic!("{context} lexer.pass span_start should carry source_name; line={line}"));
        *counts.entry(source).or_insert(0) += 1;
    }

    let mut expected = expected_sources.to_vec();
    expected.sort();
    let actual = counts.keys().cloned().collect::<Vec<_>>();
    assert_eq!(
        actual, expected,
        "{context} should lex exactly the submitted sources, with no fragment pseudo-sources; counts={counts:?}"
    );
    let pass_count = counts.values().sum::<usize>();
    assert_eq!(
        pass_count,
        expected_sources.len(),
        "{context} should lex each submitted source exactly once; counts={counts:?}"
    );
}

fn json_string_field(line: &str, field: &str) -> Option<String> {
    let marker = format!("\"{field}\":\"");
    let start = line.find(&marker)? + marker.len();
    let rest = &line[start..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

fn assert_source_production_telemetry(path: &Path, context: &str) {
    assert_compiler2_telemetry_only(path, context);
}

fn assert_native_backend_compile_telemetry(path: &Path, context: &str) {
    let log = read_to_string(path).unwrap_or_else(|error| panic!("read telemetry log {}: {error}", path.display()));
    assert!(
        log.contains("\"name\":[\"fz\",\"compiler2\",\"native_backend\",\"compile\"]"),
        "{context} should name the compiler2 native-backend boundary; log=\n{log}",
    );
    assert!(
        log.contains("\"name\":[\"fz\",\"codegen\",\"compile\"]"),
        "{context} should include the nested codegen compile span; log=\n{log}",
    );
}

fn assert_aot_link_telemetry(path: &Path, context: &str) {
    let log = read_to_string(path).unwrap_or_else(|error| panic!("read telemetry log {}: {error}", path.display()));
    for name in [
        r#""name":["fz","compiler2","aot","write_object"]"#,
        r#""name":["fz","compiler2","aot","resolve_runtime_archive"]"#,
        r#""name":["fz","compiler2","aot","link"]"#,
    ] {
        assert!(log.contains(name), "{context} should emit {name}; log=\n{log}");
    }
    // WHICH archive `fz2 build` may use is decided by the environment, not by
    // the build. A coverage run cannot link the embedded archive -- it is
    // instrumented -- so `runtime_archive_plan` deliberately rebuilds a clean
    // one into an isolated target dir. CI runs this whole suite under
    // `cargo llvm-cov`, so asserting "embedded" unconditionally asserts the
    // developer's environment rather than the contract. Assert the source the
    // environment mandates, and keep it exact in both directions so a build
    // that silently rebuilds outside coverage is still a failure.
    let expected_source = if coverage_environment() {
        "isolated_coverage_build"
    } else {
        "embedded"
    };
    assert!(
        log.contains(&format!(r#""source":"{expected_source}""#)),
        "{context} should resolve the {expected_source} runtime archive; log=\n{log}"
    );
}

/// Mirrors `aot_link::coverage_env_present`, which is crate-private and cannot
/// be reached from an integration test that observes `fz2` as a subprocess.
/// Both read the same four variables; they must agree.
fn coverage_environment() -> bool {
    fn mentions_coverage(name: &str) -> bool {
        std::env::var(name)
            .map(|value| value.contains("instrument-coverage") || value.contains("llvm-cov"))
            .unwrap_or(false)
    }
    std::env::var_os("CARGO_LLVM_COV").is_some()
        || std::env::var_os("LLVM_PROFILE_FILE").is_some()
        || mentions_coverage("RUSTFLAGS")
        || mentions_coverage("CARGO_ENCODED_RUSTFLAGS")
}

fn output_text(out: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

fn assert_file_contains(path: &Path, needle: &str, context: &str) {
    let text = read_to_string(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    assert!(
        text.contains(needle),
        "{context} should contain `{needle}`; got:\n{text}"
    );
}

#[test]
fn help_lists_compiler2_commands_on_stdout() {
    for flag in ["help", "--help", "-h"] {
        let out = Command::new(FZ2_BIN)
            .arg(flag)
            .output()
            .unwrap_or_else(|error| panic!("spawn fz2 {flag}: {error}"));
        assert!(out.status.success(), "fz2 {flag} should exit 0, got {:?}", out.status);
        let stdout = String::from_utf8(out.stdout).expect("help is utf-8");
        for command in ["run", "build", "interp", "help"] {
            assert!(
                stdout.contains(command),
                "fz2 {flag} output should mention `{command}`; got:\n{stdout}"
            );
        }
        assert!(
            stdout.contains("--dump <spec>"),
            "fz2 {flag} output should mention the dump flag; got:\n{stdout}"
        );
        assert!(
            out.stderr.is_empty(),
            "fz2 {flag} should write nothing to stderr; got: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

#[test]
fn run_and_interp_stay_on_compiler2_telemetry() {
    let source_path = unique_temp_path("fz2_enum_reduce", ".fz");
    write(
        &source_path,
        r#"
fn main(), do: Enum.reduce([1, 2, 3, 4, 5], 0, fn (x, acc) -> x + acc end)
"#,
    )
    .expect("write Compiler2 run fixture");

    for command in ["run", "interp"] {
        let telemetry_path = unique_temp_path(&format!("fz2_{command}"), ".jsonl");
        let expected_lexer_sources = vec![
            source_path.to_string_lossy().into_owned(),
            "runtime:runtime.fz".to_string(),
            "runtime:Enum.fz".to_string(),
            "runtime:Enumerable.fz".to_string(),
            "runtime:Kernel.fz".to_string(),
            "runtime:List.fz".to_string(),
        ];
        let out = run_fz2(&[
            OsStr::new("--log-telemetry"),
            telemetry_path.as_os_str(),
            OsStr::new(command),
            source_path.as_os_str(),
        ]);
        assert!(
            out.status.success(),
            "fz2 {command} should succeed; stdout={:?} stderr={:?}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert_compiler2_telemetry_only(&telemetry_path, &format!("fz2 {command}"));
        assert_lexer_passes_match_submitted_sources(
            &telemetry_path,
            &format!("fz2 {command}"),
            &expected_lexer_sources,
        );
        let _ = remove_file(&telemetry_path);
    }

    let _ = remove_file(&source_path);
}

#[test]
fn compiler2_pull_telemetry_is_bounded_and_keeps_public_trace_signals() {
    // Budgets re-pinned for the fz-kdt.34 causality stream (fz-kdt.52), then
    // again for its self-describing definition lines (fz-kdt.34.6), and again
    // for fz-kdt.56: the public trace deliberately carries one
    // `work_graph.applied` per applied job (the completion seam) plus product
    // settlement/cache/displacement events, so events and bytes scale with work
    // done, and one `fz.compiler2.canon.*` line per DISTINCT raw id so the log
    // is a self-contained dictionary. fz-kdt.56 split the call graph's edge
    // extraction out of `DeriveRecursive` into its own `DeriveStaticCallees`
    // job, so the stream gained that job's completions: +100 events / +53,539
    // bytes on 00181, +6 events on 00009. fz-kdt.44 then made settledness
    // transitive, which moved the stream in BOTH directions: it added the drain
    // arbiter's `work_graph.quiesced` steps (+37 on 00181, none on 00009) while
    // shrinking every `changed` array, because a fact that is transitively
    // unfinal no longer flips its settled bit on each local dirty/clean cycle.
    // Net on 00181: 1,545 -> 1,563 events, 970,146 -> 921,532 bytes; 00009 is
    // 205 events either way, 105,699 -> 105,683 bytes. Stacking onto #110
    // replaces 24 dispatch-mask and 3 function-contract evaluations with 42
    // input-demand evaluations and one analysis: 16 net evaluations, hence 32
    // job-span events plus 16 applied events; one fewer canonical type makes
    // the trace 1,613 -> 1,660 events. Pins keep tight headroom so creep
    // without cause still trips them.
    for (fixture, max_events, max_bytes) in [
        ("fixtures2/00181_enum_reduce_operator_ref.fz", 1_700, 1024 * 1024),
        ("fixtures2/00009_no_runtime.fz", 300, 128 * 1024),
    ] {
        let telemetry_path = unique_temp_path("fz2_bounded_pull", ".jsonl");
        let output = run_fz2(&[
            OsStr::new("--log-telemetry"),
            telemetry_path.as_os_str(),
            OsStr::new("interp"),
            OsStr::new(fixture),
        ]);
        assert_successful_stdout(&output, &fixture_expected_stdout(fixture), fixture);
        assert_bounded_public_trace(&telemetry_path, fixture, max_events, max_bytes);
        let _ = remove_file(telemetry_path);
    }
}

/// fz-kdt.34's cross-run acceptance: two SEPARATE PROCESSES compiling one input
/// must have done the same WORK, measured from the public log alone.
///
/// Two processes is the point. `RandomState` reseeds per process, so raw arena
/// ids genuinely drift between the two logs (fz-kdt.47 measured 16 differing
/// slots over four runs) and no `World` survives to translate them. The logs
/// translate themselves: each carries `fz.compiler2.canon.*` definition lines
/// for every raw id it names, and the causal report joins through them. Raw ids
/// may differ; canonical identity may not.
///
/// Recursive-search counts, typed completion publication, and cache behavior
/// are all part of the comparand. There is no product-specific exclusion:
/// owner-ordered completion waves make the whole canonical causal inventory
/// reproducible.
///
/// Work counts only — no wall-clock quantity appears in the comparand.
#[test]
fn causal_work_multisets_agree_across_two_processes() {
    for (fixture, golden) in [
        (
            "fixtures2/00420_enum_take_drop_split.fz",
            "fixtures2/behavior/enum_take_drop_split.fz",
        ),
        (
            "fixtures2/behavior/enum_predicate_search.fz",
            "fixtures2/behavior/enum_predicate_search.fz",
        ),
        (
            "fixtures2/behavior/fz_f98_range_map_converges.fz",
            "fixtures2/behavior/fz_f98_range_map_converges.fz",
        ),
    ] {
        let mut multisets = Vec::new();
        let mut outputs = Vec::new();
        for tag in ["first", "second"] {
            let telemetry_path = unique_temp_path(&format!("fz2_causal_{tag}"), ".jsonl");
            let out = run_fz2(&[
                OsStr::new("--log-telemetry"),
                telemetry_path.as_os_str(),
                OsStr::new("interp"),
                OsStr::new(fixture),
            ]);
            assert_successful_stdout(&out, &fixture_expected_stdout(golden), fixture);
            outputs.push(out.stdout);

            let log = std::fs::read(&telemetry_path).expect("read public telemetry log");
            let report = CausalReport::derive(&parse_public_trace(&log));
            assert!(
                report.recursive_search.searches > 0,
                "{tag} {fixture}: no recursive search work"
            );
            assert!(
                report.undefined_first_uses.is_empty(),
                "the {tag} {fixture} log must define every raw id it names; first gap: {:?}",
                report.undefined_first_uses.first()
            );
            assert!(
                report.canon.types() > 0 && report.canon.functions() > 0,
                "the {tag} {fixture} log must carry a populated canon dictionary"
            );
            if fixture.ends_with("fz_f98_range_map_converges.fz") {
                assert!(
                    report.uncaused.is_empty(),
                    "the {tag} {fixture} log must attribute every evaluation; first unattributed: {:?}",
                    report.uncaused.first()
                );
            }
            multisets.push(report.canonical_multiset());
            let _ = remove_file(&telemetry_path);
        }

        let (first, second) = (&multisets[0], &multisets[1]);
        assert_eq!(
            outputs[0], outputs[1],
            "{fixture}: runtime output moved across processes"
        );
        assert!(
            first.len() > 1_000,
            "expected a substantial {fixture} comparand, got {} entries",
            first.len()
        );
        assert_eq!(
            first, second,
            "two processes compiling {fixture} must agree on every canonical work count"
        );
    }
}

/// `--dump backend` is the canonical external form, so two SEPARATE PROCESSES
/// compiling one input must write byte-identical files.
///
/// Two processes is the point. Inside one process a `HashMap`'s iteration order
/// is stable enough to hide the defect; across processes `RandomState` reseeds,
/// so a rendering derived from `{:#?}` differs run to run even when the two
/// programs are equal (fz-kdt.6). The sibling `--dump native` still renders
/// with `{:#?}`, and on this very fixture two processes write files that differ
/// at char 59,803 of 98,141 — which is what this test asserts can no longer
/// happen to the backend dump. Nor is the arena a comparand: a `Ty` is a
/// position in one `World`. The same two process logs prove that product
/// identities carrying callable surfaces are canonical without requiring a
/// second compilation just for that observation.
#[test]
fn backend_dump_is_byte_identical_across_two_processes() {
    let mut observed_callable_resolutions = 0;
    for fixture in [
        "fixtures2/00420_enum_take_drop_split.fz",
        "fixtures2/behavior/enum_predicate_search.fz",
        "fixtures2/behavior/fz_f98_range_map_converges.fz",
    ] {
        let first_path = unique_temp_path("fz2_backend_canon_a", ".backend");
        let second_path = unique_temp_path("fz2_backend_canon_b", ".backend");
        let first_trace = unique_temp_path("fz2_backend_canon_a", ".jsonl");
        let second_trace = unique_temp_path("fz2_backend_canon_b", ".jsonl");
        let mut callable_resolutions = Vec::new();

        for (path, trace) in [(&first_path, &first_trace), (&second_path, &second_trace)] {
            let spec = format!("backend={}", path.display());
            let out = run_fz2(&[
                OsStr::new("--log-telemetry"),
                trace.as_os_str(),
                OsStr::new("interp"),
                OsStr::new("--dump"),
                OsStr::new(&spec),
                OsStr::new(fixture),
            ]);
            assert!(
                out.status.success() && out.stderr.is_empty(),
                "{fixture}: backend-dump process failed: {}",
                String::from_utf8_lossy(&out.stderr)
            );
            let log = std::fs::read(trace).expect("read public telemetry log");
            let report = CausalReport::derive(&parse_public_trace(&log));
            let identities = report
                .products
                .keys()
                .filter(|identity| identity.contains("\"kind\":\"callable_resolution\""))
                .cloned()
                .collect::<BTreeSet<_>>();
            assert!(
                identities.iter().all(|identity| !identity.contains("?ty:")),
                "{fixture}: the public trace must canonicalize every callable-resolution surface type: \
                 {identities:?}"
            );
            callable_resolutions.push(identities);
        }

        assert_eq!(
            callable_resolutions[0], callable_resolutions[1],
            "{fixture}: two processes must publish the same canonical callable-resolution identities"
        );
        observed_callable_resolutions += callable_resolutions[0].len();

        let first = read_to_string(&first_path).expect("read first backend dump");
        let second = read_to_string(&second_path).expect("read second backend dump");
        assert!(
            first.len() > 1_000,
            "{fixture}: the backend dump should describe a whole program, got {} bytes",
            first.len()
        );
        assert!(
            !first.contains("Ty("),
            "{fixture}: the canonical backend dump must not carry raw interner ids"
        );
        let divergence = first
            .lines()
            .zip(second.lines())
            .position(|(left, right)| left != right);
        assert!(
            first == second,
            "{fixture}: two processes must write one canonical backend dump; they first differ at line \
             {divergence:?}:\n  first:  {:?}\n  second: {:?}",
            divergence.and_then(|at| first.lines().nth(at)),
            divergence.and_then(|at| second.lines().nth(at)),
        );

        let _ = remove_file(&first_path);
        let _ = remove_file(&second_path);
        let _ = remove_file(&first_trace);
        let _ = remove_file(&second_trace);
    }
    assert!(
        observed_callable_resolutions > 0,
        "the three demand fixtures must exercise a real callable-resolution product path"
    );
}

#[test]
fn build_accepts_repeated_dump_specs_with_extension_or_kind_override() {
    let source_path = unique_temp_path("fz2_dump_build", ".fz");
    let output_path = unique_temp_path("fz2_dump_build", ".out");
    let types_path = unique_temp_path("fz2_dump_types", ".types");
    let activations_path = unique_temp_path("fz2_dump_activations", ".txt");
    let native_path = unique_temp_path("fz2_dump_native", ".native");
    let fnir_path = unique_temp_path("fz2_dump_fnir", ".txt");
    let clif_path = unique_temp_path("fz2_dump_clif", ".clif");
    let activations_spec = format!("activations={}", activations_path.display());
    let fnir_spec = format!("fnir={}", fnir_path.display());

    write(&source_path, "fn main(), do: 42\n").expect("write dump fixture");

    let out = run_fz2(&[
        OsStr::new("build"),
        OsStr::new("--dump"),
        types_path.as_os_str(),
        OsStr::new("--dump"),
        OsStr::new(&activations_spec),
        OsStr::new("--dump"),
        native_path.as_os_str(),
        OsStr::new("--dump"),
        OsStr::new(&fnir_spec),
        OsStr::new("--dump"),
        clif_path.as_os_str(),
        source_path.as_os_str(),
        OsStr::new("-o"),
        output_path.as_os_str(),
    ]);

    assert!(
        out.status.success(),
        "fz2 build with dumps should succeed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(metadata(&output_path).is_ok(), "build should produce the linked output");
    assert_file_contains(&types_path, "main/0[] =>", "types dump");
    assert_file_contains(&activations_path, "main/0[]", "activations dump");
    assert_file_contains(&native_path, "NativeProgram", "native dump");
    assert_file_contains(&fnir_path, "FnIr", "fnir dump");
    assert_file_contains(&clif_path, "function", "clif dump");

    let _ = remove_file(&clif_path);
    let _ = remove_file(&fnir_path);
    let _ = remove_file(&native_path);
    let _ = remove_file(&activations_path);
    let _ = remove_file(&types_path);
    let _ = remove_file(&output_path);
    let _ = remove_file(&source_path);
}

#[test]
fn quicksort_run_lexes_each_source_once() {
    let telemetry_path = unique_temp_path("fz2_quicksort", ".jsonl");
    let fixture = "fixtures2/behavior/quicksort.fz";
    let expected_lexer_sources = vec![
        fixture.to_string(),
        "runtime:runtime.fz".to_string(),
        "runtime:Kernel.fz".to_string(),
        "runtime:Process.fz".to_string(),
    ];

    let out = run_fz2(&[
        OsStr::new("--log-telemetry"),
        telemetry_path.as_os_str(),
        OsStr::new("run"),
        OsStr::new(fixture),
    ]);
    assert!(
        out.status.success(),
        "fz2 quicksort run should succeed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert_compiler2_telemetry_only(&telemetry_path, "fz2 run quicksort");
    assert_lexer_passes_match_submitted_sources(&telemetry_path, "fz2 run quicksort", &expected_lexer_sources);
    assert_native_backend_compile_telemetry(&telemetry_path, "fz2 run quicksort");

    let _ = remove_file(&telemetry_path);
}

#[test]
fn build_stays_on_compiler2_telemetry_and_links_a_native_binary() {
    let source_path = unique_temp_path("fz2_build", ".fz");
    let out_bin = unique_temp_path("fz2_build", ".bin");
    let telemetry_path = unique_temp_path("fz2_build", ".jsonl");
    write(&source_path, "fn main(), do: 0\n").expect("write Compiler2 build fixture");

    let build = Command::new(FZ2_BIN)
        .current_dir(temp_dir())
        .env("CARGO", "/definitely/not/cargo")
        .args([
            OsStr::new("--log-telemetry"),
            telemetry_path.as_os_str(),
            OsStr::new("build"),
            source_path.as_os_str(),
            OsStr::new("-o"),
            out_bin.as_os_str(),
        ])
        .output()
        .expect("invoke fz2 binary outside its build directory");
    assert!(
        build.status.success(),
        "fz2 build should succeed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    assert_compiler2_telemetry_only(&telemetry_path, "fz2 build");
    assert_aot_link_telemetry(&telemetry_path, "fz2 build");
    assert!(
        metadata(&out_bin).is_ok(),
        "fz2 build should produce a linked native binary at {}",
        out_bin.display()
    );

    let run = Command::new(&out_bin).output().expect("run fz2-built binary");
    assert!(
        run.status.success(),
        "fz2-built binary should run successfully; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );

    let _ = remove_file(&telemetry_path);
    let _ = remove_file(&source_path);
    let _ = remove_file(&out_bin);
    let _ = remove_file(out_bin.with_extension("bin.o"));
}

#[test]
fn run_and_interp_execute_map_struct_and_bitstring_fixtures() {
    for fixture in [
        "fixtures2/behavior/map_three_path_parity.fz",
        "fixtures2/behavior/defstruct_runtime.fz",
        "fixtures2/behavior/utf8_smart_constructor.fz",
    ] {
        let expected = fixture_expected_stdout(fixture);
        for command in ["run", "interp"] {
            let out = run_fz2(&[OsStr::new(command), OsStr::new(fixture)]);
            assert_successful_stdout(&out, &expected, &format!("fz2 {command} {fixture}"));
        }
    }
}

#[test]
fn run_and_interp_execute_source_production_macro_and_sugar_fixtures() {
    for fixture in [
        "fixtures2/behavior/macro_inc.fz",
        "fixtures2/behavior/cross_module_macro.fz",
        "fixtures2/behavior/item_macro_source.fz",
        "fixtures2/behavior/pipe_headless_case.fz",
        "fixtures2/behavior/lambda_sugars.fz",
        "fixtures2/behavior/operator_sugars.fz",
    ] {
        let expected = fixture_expected_stdout(fixture);
        for command in ["run", "interp"] {
            let telemetry_path = unique_temp_path("fz2_source_production", ".jsonl");
            let out = run_fz2(&[
                OsStr::new("--log-telemetry"),
                telemetry_path.as_os_str(),
                OsStr::new(command),
                OsStr::new(fixture),
            ]);
            assert_successful_stdout(&out, &expected, &format!("fz2 {command} {fixture}"));
            assert_source_production_telemetry(&telemetry_path, &format!("fz2 {command} {fixture}"));
            let _ = remove_file(&telemetry_path);
        }
    }
}

#[test]
fn run_reports_unrequired_remote_macro_during_source_production() {
    let source_path = unique_temp_path("fz2_remote_macro_without_require", ".fz");
    write(
        &source_path,
        r#"
defmodule Helpers do
  fn double(x), do: x * 2

  defmacro twice(x) do
    quote do: double(unquote(x))
  end
end

defmodule App do
  fn run(), do: Helpers.twice(21)
end

fn main(), do: App.run()
"#,
    )
    .expect("write missing require fixture");

    let out = run_fz2_without_color(&[OsStr::new("run"), source_path.as_os_str()]);
    assert!(
        !out.status.success(),
        "fz2 run should reject unrequired remote macro; output={}",
        output_text(&out)
    );
    let text = output_text(&out);
    assert!(
        text.contains("macro/not-required") && text.contains("require Helpers"),
        "fz2 diagnostic should name the missing require; output={text}",
    );
    assert!(
        text.contains(&format!("--> {}:", source_path.display())),
        "fz2 diagnostic should locate the remote macro call; output={text}",
    );
    assert!(
        text.contains("Helpers.twice(21)"),
        "fz2 diagnostic should show the offending source; output={text}"
    );
    assert!(
        !text.contains("\x1b["),
        "NO_COLOR must disable ANSI escapes; output={text}"
    );

    let _ = remove_file(&source_path);
}

#[test]
fn runtime_demand_order_fixtures_cross_every_cli_execution_boundary() {
    for (fixture, golden) in [
        (
            "fixtures2/00420_enum_take_drop_split.fz",
            "fixtures2/behavior/enum_take_drop_split.fz",
        ),
        (
            "fixtures2/behavior/enum_predicate_search.fz",
            "fixtures2/behavior/enum_predicate_search.fz",
        ),
        (
            "fixtures2/behavior/fz_f98_range_map_converges.fz",
            "fixtures2/behavior/fz_f98_range_map_converges.fz",
        ),
    ] {
        let expected = fixture_expected_stdout(golden);
        for mode in ["interp", "run"] {
            let out = run_fz2(&[OsStr::new(mode), OsStr::new(fixture)]);
            assert_successful_stdout(&out, &expected, &format!("fz2 {mode} {fixture}"));
        }
        let out_bin = unique_temp_path("fz2_runtime_demand_order", ".bin");
        let build = run_fz2(&[
            OsStr::new("build"),
            OsStr::new(fixture),
            OsStr::new("-o"),
            out_bin.as_os_str(),
        ]);
        assert_successful_stdout(&build, "", &format!("fz2 build {fixture}"));
        let run = Command::new(&out_bin)
            .output()
            .unwrap_or_else(|error| panic!("run built binary for {fixture}: {error}"));
        assert_successful_stdout(&run, &expected, &format!("built {fixture}"));
        let _ = remove_file(&out_bin);
        let _ = remove_file(out_bin.with_extension("bin.o"));
    }
}

#[test]
fn build_executes_map_struct_bitstring_and_enum_halt_fixtures() {
    for fixture in [
        "fixtures2/behavior/map_three_path_parity.fz",
        "fixtures2/behavior/defstruct_runtime.fz",
        "fixtures2/behavior/utf8_smart_constructor.fz",
    ] {
        let expected = fixture_expected_stdout(fixture);
        let out_bin = unique_temp_path("fz2_fixture_build", ".bin");
        let build = run_fz2(&[
            OsStr::new("build"),
            OsStr::new(fixture),
            OsStr::new("-o"),
            out_bin.as_os_str(),
        ]);
        assert!(
            build.status.success(),
            "fz2 build {fixture} should succeed; stdout={:?} stderr={:?}",
            String::from_utf8_lossy(&build.stdout),
            String::from_utf8_lossy(&build.stderr)
        );
        let run = Command::new(&out_bin)
            .output()
            .unwrap_or_else(|error| panic!("run built binary for {fixture}: {error}"));
        assert_successful_stdout(&run, &expected, &format!("fz2 build/run {fixture}"));
        let _ = remove_file(&out_bin);
        let _ = remove_file(out_bin.with_extension("bin.o"));
    }
}

/// fz-bdk: a runtime fault must exit nonzero and name its reason on every
/// native path. The dispatch miss is dynamically-arising (which atom `pick`
/// returns depends on execution), so no compile-time diagnostic can close it;
/// the compiled trap fires -- and the process-exit boundary must report it
/// instead of unifying fault-halt with normal completion (exit 0, silent).
#[test]
fn run_and_built_binary_report_runtime_dispatch_faults() {
    let source = "fn pick(0), do: :first\n\
                  fn pick(_), do: :third\n\n\
                  fn handle(:first), do: 1\n\
                  fn handle(:second), do: 2\n\n\
                  fn main() do\n  dbg(1)\n  dbg(handle(pick(5)))\n  dbg(2)\nend\n";
    let src_path = unique_temp_path("fz2_runtime_fault", ".fz");
    write(&src_path, source).expect("write runtime-fault source");

    let run = run_fz2_without_color(&[OsStr::new("run"), src_path.as_os_str()]);
    let run_stdout = String::from_utf8_lossy(&run.stdout);
    let run_stderr = String::from_utf8_lossy(&run.stderr);
    assert!(
        !run.status.success(),
        "fz2 run must exit nonzero on a runtime fault; stdout={run_stdout:?} stderr={run_stderr:?}"
    );
    assert!(
        run_stdout.contains('1') && !run_stdout.contains('2'),
        "side effects up to the trap survive, nothing after it: {run_stdout:?}"
    );
    assert!(
        run_stderr.contains("function_clause"),
        "the fault reason must reach stderr: {run_stderr:?}"
    );

    let out_bin = unique_temp_path("fz2_runtime_fault_build", ".bin");
    let build = run_fz2(&[
        OsStr::new("build"),
        src_path.as_os_str(),
        OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "fz2 build should compile the runtime-fault program (the fault is dynamic); stderr={:?}",
        String::from_utf8_lossy(&build.stderr)
    );
    let built = Command::new(&out_bin).output().expect("run built runtime-fault binary");
    let built_stdout = String::from_utf8_lossy(&built.stdout);
    let built_stderr = String::from_utf8_lossy(&built.stderr);
    assert!(
        !built.status.success(),
        "the built binary must exit nonzero on a runtime fault; stdout={built_stdout:?} stderr={built_stderr:?}"
    );
    assert!(
        built_stdout.contains('1') && !built_stdout.contains('2'),
        "side effects up to the trap survive, nothing after it: {built_stdout:?}"
    );
    assert!(
        built_stderr.contains("function_clause"),
        "the fault reason must reach the built binary's stderr: {built_stderr:?}"
    );
    let _ = remove_file(&src_path);
    let _ = remove_file(&out_bin);
    let _ = remove_file(out_bin.with_extension("bin.o"));
}

#[test]
fn native_enum_take_drop_split_preserves_tuple_accumulator_lists() {
    let fixture = "fixtures2/behavior/enum_take_drop_split.fz";
    let expected = fixture_expected_stdout(fixture);
    let run = run_fz2(&[OsStr::new("run"), OsStr::new(fixture)]);
    assert_successful_stdout(&run, &expected, &format!("fz2 run {fixture}"));

    let out_bin = unique_temp_path("fz2_enum_take_drop_split_build", ".bin");
    let build = run_fz2(&[
        OsStr::new("build"),
        OsStr::new(fixture),
        OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "fz2 build {fixture} should succeed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let built = Command::new(&out_bin)
        .output()
        .unwrap_or_else(|error| panic!("run built binary for {fixture}: {error}"));
    assert_successful_stdout(&built, &expected, &format!("fz2 build/run {fixture}"));
    let _ = remove_file(&out_bin);
    let _ = remove_file(out_bin.with_extension("bin.o"));
}

#[test]
fn native_enum_take_positive_single_call_survives_reduction_yield() {
    let source_path = unique_temp_path("fz2_enum_take_positive_single", ".fz");
    write(
        &source_path,
        "fn main() do\n  xs = [1, 2, 3, 4, 5]\n  dbg(Enum.take(xs, 3))\nend\n",
    )
    .unwrap_or_else(|error| panic!("write {}: {error}", source_path.display()));

    let out = run_fz2(&[OsStr::new("run"), source_path.as_os_str()]);
    assert_successful_stdout(&out, "[1, 2, 3]\n", "fz2 run minimal positive Enum.take fixture");
    let _ = remove_file(&source_path);
}

#[test]
fn native_enum_every_functions_reject_negative_intervals_consistently() {
    for (name, expression) in [
        ("map_every", "Enum.map_every([1, 2, 3], -1, fn (value) -> value end)"),
        ("take_every", "Enum.take_every([1, 2, 3], -1)"),
        ("drop_every", "Enum.drop_every([1, 2, 3], -1)"),
    ] {
        let source_path = unique_temp_path(&format!("fz2_enum_{name}_negative"), ".fz");
        write(&source_path, format!("fn main(), do: {expression}\n"))
            .unwrap_or_else(|error| panic!("write {}: {error}", source_path.display()));

        let out = run_fz2(&[OsStr::new("run"), source_path.as_os_str()]);
        assert!(
            !out.status.success(),
            "Enum.{name} should reject a negative interval; output={}",
            output_text(&out)
        );
        assert!(out.stdout.is_empty(), "Enum.{name} should not write stdout");
        assert_eq!(
            String::from_utf8_lossy(&out.stderr),
            "fz panic: \"Enum.OutOfBoundsError\"\n",
            "Enum.{name} should use the established out-of-bounds failure"
        );

        let _ = remove_file(&source_path);
    }
}

#[test]
fn run_and_interp_execute_case_and_with_fixtures() {
    let fixture = "fixtures2/behavior/case_with_total.fz";
    let expected = fixture_expected_stdout(fixture);
    for command in ["run", "interp"] {
        let out = run_fz2(&[OsStr::new(command), OsStr::new(fixture)]);
        assert_successful_stdout(&out, &expected, &format!("fz2 {command} {fixture}"));
    }
}

#[test]
fn run_and_interp_report_partial_case_and_with_warnings() {
    let fixture = "fixtures2/behavior/case_tuple_pattern_sequential.fz";
    let expected = fixture_expected_stdout(fixture);
    for command in ["run", "interp"] {
        let out = run_fz2_without_color(&[OsStr::new(command), OsStr::new(fixture)]);
        assert!(
            out.status.success(),
            "fz2 {command} {fixture} should succeed; stdout={:?} stderr={:?}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(
            String::from_utf8(out.stdout.clone()).expect("stdout is utf-8"),
            expected,
            "fz2 {command} {fixture} should print the expected stdout"
        );
        let stderr = String::from_utf8(out.stderr.clone()).expect("stderr is utf-8");
        assert!(
            stderr.contains("warning[type/no-matching-clause]: `case` clauses don't cover every input"),
            "fz2 {command} should warn for partial case clauses; stderr={stderr}"
        );
        assert!(
            stderr.contains("warning[type/no-matching-clause]: `with else` clauses don't cover every input"),
            "fz2 {command} should warn for partial with else clauses; stderr={stderr}"
        );
        assert!(stderr.contains("--> fixtures2/behavior/case_tuple_pattern_sequential.fz:"));
        assert!(stderr.contains("matched values may fall through here"));
        assert!(stderr.contains("= note: an input matched by no clause halts with `:case_clause` at runtime"));
        assert!(stderr.contains("= help: add a wildcard clause `_ -> ...` to cover any remaining input"));
        assert!(
            !stderr.contains("\x1b["),
            "NO_COLOR must disable ANSI escapes; stderr={stderr}"
        );
    }
}

#[test]
fn build_executes_case_and_with_fixtures() {
    let fixture = "fixtures2/behavior/case_with_total.fz";
    let expected = fixture_expected_stdout(fixture);
    let out_bin = unique_temp_path("fz2_control_fixture_build", ".bin");
    let build = run_fz2(&[
        OsStr::new("build"),
        OsStr::new(fixture),
        OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "fz2 build {fixture} should succeed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let run = Command::new(&out_bin)
        .output()
        .unwrap_or_else(|error| panic!("run built binary for {fixture}: {error}"));
    assert_successful_stdout(&run, &expected, &format!("fz2 build/run {fixture}"));
    let _ = remove_file(&out_bin);
    let _ = remove_file(out_bin.with_extension("bin.o"));
}

#[test]
fn run_and_interp_execute_receive_fixtures() {
    for fixture in [
        "fixtures2/behavior/concurrency_ping_pong.fz",
        "fixtures2/behavior/receive_selective_refs.fz",
        "fixtures2/behavior/receive_float_pattern.fz",
    ] {
        let expected = fixture_expected_stdout(fixture);
        for command in ["run", "interp"] {
            let out = run_fz2(&[OsStr::new(command), OsStr::new(fixture)]);
            assert_successful_stdout(&out, &expected, &format!("fz2 {command} {fixture}"));
        }
    }
}

#[test]
fn build_executes_receive_fixtures() {
    for fixture in [
        "fixtures2/behavior/concurrency_ping_pong.fz",
        "fixtures2/behavior/receive_selective_refs.fz",
        "fixtures2/behavior/receive_float_pattern.fz",
    ] {
        let expected = fixture_expected_stdout(fixture);
        let out_bin = unique_temp_path("fz2_receive_fixture_build", ".bin");
        let build = run_fz2(&[
            OsStr::new("build"),
            OsStr::new(fixture),
            OsStr::new("-o"),
            out_bin.as_os_str(),
        ]);
        assert!(
            build.status.success(),
            "fz2 build {fixture} should succeed; stdout={:?} stderr={:?}",
            String::from_utf8_lossy(&build.stdout),
            String::from_utf8_lossy(&build.stderr)
        );
        let run = Command::new(&out_bin)
            .output()
            .unwrap_or_else(|error| panic!("run built binary for {fixture}: {error}"));
        assert_successful_stdout(&run, &expected, &format!("fz2 build/run {fixture}"));
        let _ = remove_file(&out_bin);
        let _ = remove_file(out_bin.with_extension("bin.o"));
    }
}

#[test]
fn run_interp_and_build_execute_cond_source() {
    let source_path = unique_temp_path("fz2_cond", ".fz");
    write(
        &source_path,
        r#"
fn main() do
  cond do
    false -> dbg(:bad)
    2 + 2 == 4 -> dbg(:ok)
  end
end
"#,
    )
    .expect("write cond fixture");

    for command in ["run", "interp"] {
        let out = run_fz2(&[OsStr::new(command), source_path.as_os_str()]);
        assert_successful_stdout(&out, ":ok\n", &format!("fz2 {command} cond source"));
    }

    let out_bin = unique_temp_path("fz2_cond_build", ".bin");
    let build = run_fz2(&[
        OsStr::new("build"),
        source_path.as_os_str(),
        OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "fz2 build cond source should succeed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let run = Command::new(&out_bin).output().expect("run built cond binary");
    assert_successful_stdout(&run, ":ok\n", "fz2 build/run cond source");

    let _ = remove_file(&source_path);
    let _ = remove_file(&out_bin);
    let _ = remove_file(out_bin.with_extension("bin.o"));
}

/// fz-kdt.44: the drain arbiter's readiness step is on the public stream.
///
/// Settledness is transitive — a fact is final only when its whole upstream
/// cone is quiescent — and counting can never finalize a cycle, so at a drain
/// the arbiter discharges the standing settled questions and publishes the
/// resulting settled-bit flips as `work_graph.quiesced`. That event is the
/// only graph movement with no job completion behind it. Without it the stream
/// would show a fact's `settled` bit changing between two `movements`
/// renderings with nothing on the log to explain it, and any evaluation woken
/// by such a flip would classify as uncaused.
///
/// fz-kdt.45 made `DeriveExecutableFacts(E)` a scheduler job whose direct fact
/// formula stands on settled `ActivationAnalyzed` and `CallSiteSummary` facts.
/// Their finality flips therefore wake that exact producer. Product waits are
/// still polled by the pull driver; the newly live readiness cause comes from
/// this direct scheduler fact boundary, independent of how root analysis is
/// ignited.
#[test]
fn the_drain_arbiter_publishes_readiness_only_movement_and_attributes_every_evaluation() {
    let fixture = "fixtures2/00181_enum_reduce_operator_ref.fz";
    let telemetry_path = unique_temp_path("fz2_quiesced", ".jsonl");
    let out = run_fz2(&[
        OsStr::new("--log-telemetry"),
        telemetry_path.as_os_str(),
        OsStr::new("interp"),
        OsStr::new(fixture),
    ]);
    assert_successful_stdout(&out, &fixture_expected_stdout(fixture), fixture);

    let log = std::fs::read(&telemetry_path).expect("read public telemetry log");
    let events = parse_public_trace(&log);
    let quiesced: Vec<_> = events
        .iter()
        .filter(|ev| {
            ev.name
                .iter()
                .map(String::as_str)
                .eq(["fz", "compiler2", "work_graph", "quiesced"])
        })
        .collect();
    assert_eq!(quiesced.len(), 34, "{fixture}: quiescence event count moved");

    let mut wakes = Vec::new();
    for event in &quiesced {
        let step = event.metadata.get("step").expect("a quiesced event carries its step");
        for change in step.get("changed").and_then(|c| c.as_array()).into_iter().flatten() {
            assert_eq!(
                change.get("old_revision"),
                change.get("new_revision"),
                "the arbiter moves readiness only; no cell value changes"
            );
            assert_ne!(
                change.get("old_settled"),
                change.get("new_settled"),
                "every entry in a quiesced step's changed array must be a settled-bit flip; \
                 the array carries only the arbiter's own flips by construction (subscriber \
                 dirtying travels via movements), so this pins the flip shape"
            );
        }
        wakes.extend(step.get("wakes").and_then(|w| w.as_array()).into_iter().flatten());
    }

    let mut wake_causes = BTreeSet::new();
    let mut wake_dispositions = BTreeMap::new();
    for wake in &wakes {
        let cause = wake.get("cause").expect("a readiness wake names its cause");
        let cause_kind = cause
            .get("kind")
            .and_then(serde_json::Value::as_str)
            .expect("a readiness wake names its fact kind");
        let job = wake.get("job").expect("a readiness wake names its job");
        assert_eq!(
            cause.get("use").and_then(serde_json::Value::as_str),
            Some("settled"),
            "the direct producer must wait for settled semantic facts: {wake:?}"
        );
        assert_eq!(
            job.get("kind").and_then(serde_json::Value::as_str),
            Some("DeriveExecutableFacts"),
            "only the direct executable-fact producer wakes here: {wake:?}"
        );
        assert_eq!(
            job.get("need").and_then(serde_json::Value::as_str),
            Some("value"),
            "this census derives value-needed executable facts: {wake:?}"
        );
        for field in ["root_id", "function_id", "arrow"] {
            let cause_component = cause
                .get(field)
                .and_then(serde_json::Value::as_u64)
                .unwrap_or_else(|| panic!("the cause must name its activation {field}: {wake:?}"));
            let job_component = job
                .get(field)
                .and_then(serde_json::Value::as_u64)
                .unwrap_or_else(|| panic!("the producer must name its activation {field}: {wake:?}"));
            assert_eq!(
                cause_component, job_component,
                "the semantic fact must wake its exact executable producer: {wake:?}"
            );
        }
        let cause_fields = cause
            .as_object()
            .expect("a readiness cause is an object")
            .keys()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let expected_cause_fields = match cause_kind {
            "ActivationAnalyzed" => BTreeSet::from(["arrow", "function_id", "kind", "root_id", "use"]),
            "CallSiteSummary" => {
                cause
                    .get("callsite")
                    .and_then(serde_json::Value::as_u64)
                    .expect("a CallSiteSummary cause must name its exact callsite");
                BTreeSet::from(["arrow", "callsite", "function_id", "kind", "root_id", "use"])
            }
            _ => panic!("only direct executable-fact prerequisites wake here: {wake:?}"),
        };
        assert_eq!(
            cause_fields, expected_cause_fields,
            "each prerequisite kind must carry exactly its semantic identity: {wake:?}"
        );
        assert_eq!(
            job.as_object()
                .expect("a readiness job is an object")
                .keys()
                .map(String::as_str)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["arrow", "function_id", "kind", "need", "root_id"]),
            "DeriveExecutableFacts must carry exactly one executable identity: {wake:?}"
        );
        assert_eq!(
            wake.get("shift").and_then(serde_json::Value::as_bool),
            Some(false),
            "readiness alone is not a content shift: {wake:?}"
        );
        wake_causes.insert(cause_kind);
        let disposition = wake
            .get("disposition")
            .and_then(serde_json::Value::as_str)
            .expect("a readiness wake names its agenda disposition");
        *wake_dispositions.entry(disposition).or_insert(0) += 1;
    }
    assert_eq!(
        wake_causes,
        BTreeSet::from(["ActivationAnalyzed", "CallSiteSummary"]),
        "{fixture}: both direct semantic prerequisite kinds must exercise readiness"
    );
    assert_eq!(
        wake_dispositions,
        BTreeMap::from([("coalesced", 3), ("enqueued", 18)]),
        "{fixture}: direct-fact readiness wake accounting moved"
    );

    let report = CausalReport::derive(&events);
    let executable_fact_readiness = report
        .formulas
        .iter()
        .filter(|(formula, _)| formula.contains("\"kind\":\"DeriveExecutableFacts\""))
        .map(|(_, work)| work.readiness_caused)
        .sum::<u64>();
    let formula_totals = report.formula_totals();
    assert!(
        executable_fact_readiness > 0,
        "the direct fact producer must exercise the causal replay's readiness class"
    );
    assert_eq!(
        executable_fact_readiness, formula_totals.readiness_caused,
        "all readiness-caused work in this fixture comes from the direct executable-fact boundary"
    );
    assert_eq!(
        formula_totals,
        FormulaWork {
            evaluations: 324,
            initial: 166,
            content_caused: 140,
            readiness_caused: 18,
            uncaused: 0,
            changed_outputs: 191,
            unchanged_outputs: 133,
            wakes: 141,
            blocked_completions: 145,
        },
        "{fixture}: causal or output work moved outside the readiness reclassification"
    );
    assert_eq!(
        report.product_totals(),
        ProductWork {
            settlements: 408,
            changed: 408,
            unchanged: 0,
            cache_hits: 18,
            displacements: 0,
            generations: BTreeSet::new(),
        },
        "{fixture}: product work moved while pinning direct-fact readiness"
    );
    assert!(
        report.uncaused.is_empty(),
        "every evaluation must still name a moved input; first unattributed: {:?}",
        report.uncaused.first()
    );
    assert!(
        report.readiness_without_settled_wake.is_empty(),
        "a readiness cause is only claimable where a Settled/SettledPresence wake carried it"
    );
    let _ = remove_file(&telemetry_path);
}

/// A stalled compile's error message is the same text on every run (fz-kdt.109).
///
/// A program that cannot settle reports its standing waits, and that list used
/// to come out of a `HashMap` in iteration order — a per-process `RandomState`
/// artifact, so one binary printed a different message run to run (five runs of
/// this fixture produced four distinct stderr renderings, and 90 of the 577
/// fixtures stall). That makes the message unreadable as a comparand: a sweep
/// cannot tell a real diagnostic movement from reshuffled text. Separate
/// processes are the honest probe — each gets its own hash seed.
#[test]
fn fz2_stall_diagnostic_is_byte_identical_across_runs() {
    let fixture = OsStr::new("fixtures2/00050_empty.fz");
    let args = [OsStr::new("interp"), fixture];
    let renderings = (0..3)
        .map(|_| {
            let output = run_fz2_without_color(&args);
            String::from_utf8(output.stderr).expect("fz2 stderr is utf-8")
        })
        .collect::<Vec<_>>();

    assert!(
        renderings[0].contains("no ready producer; unresolved="),
        "the fixture must still reach the stall diagnostic for this pin to mean anything, got: {}",
        renderings[0]
    );
    for (run, rendering) in renderings.iter().enumerate().skip(1) {
        assert_eq!(
            rendering, &renderings[0],
            "run {run} rendered the same stall differently than run 0"
        );
    }
}
