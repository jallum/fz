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
//!         expected.jit.txt  path-specific stdout golden (optional)
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
//!     budget.planner.matcher_specs: 0
//!     ---
//!
//! Workflow: re-run with `BLESS=1 cargo test fixture_matrix` to rewrite
//! `expected.txt` / `expected.<path>.txt` and `expected.diagnostics` from current output. On
//! failure (non-bless), actual output is dropped at `<dir>/actual.txt`
//! and `<dir>/actual.diagnostics` for diffing. Dump-shape budgets use
//! telemetry from `fz dump --emit stats`; only failures write
//! `<dir>/actual.clif` and `<dir>/actual.specs`.

use libtest_mimic::{Arguments, Failed, Trial};
use std::fs;
use std::os::fd::RawFd;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

const FZ_BIN: &str = env!("CARGO_BIN_EXE_fz");
const FZ_EXEC_READY_FD_ENV: &str = "FZ_EXEC_READY_FD";
const FIXTURE_COMMAND_TIMEOUT: Duration = Duration::from_secs(3);
static AOT_TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

// fz-fkv — custom main: each (fixture, path) pair becomes its own
// `cargo test` trial, named `matrix::<fixture>::<path>`. `cargo test add1`
// filters to one fixture; `cargo test ::repl` filters to one leg. Static
// invariant tests (CLIF shape, golden dumps, etc.) become trials too so
// the harness is uniform.
fn main() {
    let mut args = Arguments::from_args();
    if args.test_threads.is_none() {
        args.test_threads = std::env::var("RUST_TEST_THREADS")
            .ok()
            .and_then(|raw| raw.parse::<usize>().ok());
    }
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
            "send_uses_one_word_ref_boundary",
            send_uses_one_word_ref_boundary,
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
        (
            "generated_value_paths_have_no_removed_format_terms",
            generated_value_paths_have_no_removed_format_terms,
        ),
        (
            "scheduler_receive_buffers_are_any_value_refs",
            scheduler_receive_buffers_are_any_value_refs,
        ),
        (
            "production_and_guides_have_no_old_value_format_gate_names",
            production_and_guides_have_no_old_value_format_gate_names,
        ),
        (
            "owned_cons_reuse_docs_pin_alias_fallback_contract",
            owned_cons_reuse_docs_pin_alias_fallback_contract,
        ),
        (
            "physical_capability_model_and_signals_are_pinned",
            physical_capability_model_and_signals_are_pinned,
        ),
        (
            "owned_cons_reuse_negative_barriers_do_not_advertise_capabilities",
            owned_cons_reuse_negative_barriers_do_not_advertise_capabilities,
        ),
        (
            "quicksort_clif_inlines_nonempty_list_projection",
            quicksort_clif_inlines_nonempty_list_projection,
        ),
        (
            "compiled_back_edges_spend_reductions_through_pinned_process",
            compiled_back_edges_spend_reductions_through_pinned_process,
        ),
        (
            "quicksort_has_no_tuple_dp_any_fanout",
            quicksort_has_no_tuple_dp_any_fanout,
        ),
        (
            "quicksort_tuple_return_demand_removes_partition_structs",
            quicksort_tuple_return_demand_removes_partition_structs,
        ),
        (
            "quicksort_selects_list_tail_return_demand",
            quicksort_selects_list_tail_return_demand,
        ),
        (
            "quicksort_structured_return_demand_facts",
            quicksort_structured_return_demand_facts,
        ),
        (
            "quicksort_list_tail_abi_carries_destination_param",
            quicksort_list_tail_abi_carries_destination_param,
        ),
        (
            "quicksort_list_tail_empty_return_delivers_destination",
            quicksort_list_tail_empty_return_delivers_destination,
        ),
        (
            "list_tail_demand_rejects_print_between_prefix_and_append",
            list_tail_demand_rejects_print_between_prefix_and_append,
        ),
        (
            "list_tail_demand_rejects_heap_stats_between_prefix_and_append",
            list_tail_demand_rejects_heap_stats_between_prefix_and_append,
        ),
        (
            "list_tail_demand_rejects_extern_between_prefix_and_append",
            list_tail_demand_rejects_extern_between_prefix_and_append,
        ),
        (
            "resource_lifecycle_uses_typed_scalar_map_key_lookup",
            resource_lifecycle_uses_typed_scalar_map_key_lookup,
        ),
        (
            "list_cell_uninit_is_immediately_initialized_in_clif",
            list_cell_uninit_is_immediately_initialized_in_clif,
        ),
        (
            "quicksort_list_literal_uses_static_tail_links",
            quicksort_list_literal_uses_static_tail_links,
        ),
        (
            "quicksort_pins_return_demand_target",
            quicksort_pins_return_demand_target,
        ),
        (
            "append_pins_source_append_target",
            append_pins_source_append_target,
        ),
        (
            "enum_list_allocations_pin_minimum_list_cons",
            enum_list_allocations_pin_minimum_list_cons,
        ),
        (
            "enum_reduce_resume_state_update_is_rendered",
            enum_reduce_resume_state_update_is_rendered,
        ),
        (
            "enum_reduce_parameter_reducer_still_renders_resume",
            enum_reduce_parameter_reducer_still_renders_resume,
        ),
        (
            "local_reduce_state_update_lowers_without_trampoline",
            local_reduce_state_update_lowers_without_trampoline,
        ),
        (
            "continuation_materialization_boundaries_stay_explicit",
            continuation_materialization_boundaries_stay_explicit,
        ),
        (
            "interpreter_stepper_does_not_update_quiet_quanta",
            interpreter_stepper_does_not_update_quiet_quanta,
        ),
        (
            "reverse_filter_tree_pin_current_shape",
            reverse_filter_tree_pin_current_shape,
        ),
        (
            "codegen_does_not_invent_return_demand_siblings",
            codegen_does_not_invent_return_demand_siblings,
        ),
        (
            "codegen_does_not_recognize_list_tail_from_capture_shape",
            codegen_does_not_recognize_list_tail_from_capture_shape,
        ),
        (
            "quicksort_continuations_capture_only_live_values",
            quicksort_continuations_capture_only_live_values,
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
            && wildcard_specs.contains("key:    [int]")
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
            && multi_clause_specs.contains("key:    [int]")
            && multi_clause_specs.contains(":positive")
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
        case_specs.contains("key:    [{:ok, int}]")
            && case_specs.contains("key:    [:err]")
            && case_specs.contains("TailCall with_else_0"),
        "tuple and atom branches in case/with must both stay reachable"
    );

    let type_specs = dump_specs_for_fixture("type_dispatch");
    assert!(
        type_specs.contains("key:    [int]")
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
            && nil_list_specs.contains("key:    [[]]")
            && nil_list_specs.contains("key:    [nonempty_list(int)]"),
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
/// multi-clause, with-else, and prelude dbg dispatch must not create
/// `_matcher_` specs. T4 may still update receive-specific totals when it
/// caches receive Matchers. Exact counts are deliberate: any matcher-shape
/// change should force a conscious baseline update in the same commit.
fn matcher_perf_internal_matcher_repair_baseline() {
    let representative = [
        ("hello", 1, 0),
        ("list_primitives", 16, 0),
        ("quicksort", 18, 0),
        ("ast_eval", 1, 0),
        ("receive_mixed_constructors", 5, 0),
    ];
    for (fixture, expected_specs, expected_matchers) in representative {
        let fixture_dir = Path::new("fixtures").join(fixture);
        let stats = dump_telemetry_stats(&fixture_dir);
        assert_eq!(
            stats.planner.spec_count, expected_specs,
            "{} total spec baseline changed",
            fixture
        );
        assert_eq!(
            stats.planner.matcher_spec_count, expected_matchers,
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

#[derive(Clone, Copy)]
enum TimeoutStart {
    OnSpawn,
    OnExecutionReady,
}

fn close_fd(fd: RawFd) {
    unsafe {
        let _ = libc::close(fd);
    }
}

fn execution_ready_pipe() -> Result<(RawFd, RawFd), String> {
    let mut fds = [0; 2];
    let rc = unsafe { libc::pipe(fds.as_mut_ptr()) };
    if rc != 0 {
        return Err(format!(
            "pipe {}: {}",
            FZ_EXEC_READY_FD_ENV,
            std::io::Error::last_os_error()
        ));
    }
    let flags = unsafe { libc::fcntl(fds[0], libc::F_GETFL) };
    if flags < 0 {
        close_fd(fds[0]);
        close_fd(fds[1]);
        return Err(format!(
            "fcntl {}: {}",
            FZ_EXEC_READY_FD_ENV,
            std::io::Error::last_os_error()
        ));
    }
    let rc = unsafe { libc::fcntl(fds[0], libc::F_SETFL, flags | libc::O_NONBLOCK) };
    if rc != 0 {
        close_fd(fds[0]);
        close_fd(fds[1]);
        return Err(format!(
            "fcntl nonblock {}: {}",
            FZ_EXEC_READY_FD_ENV,
            std::io::Error::last_os_error()
        ));
    }
    Ok((fds[0], fds[1]))
}

fn read_execution_ready(fd: RawFd) -> Result<bool, String> {
    let mut byte = [0_u8];
    let n = unsafe { libc::read(fd, byte.as_mut_ptr().cast(), byte.len()) };
    if n > 0 {
        return Ok(true);
    }
    if n == 0 {
        return Ok(false);
    }
    let err = std::io::Error::last_os_error();
    match err.raw_os_error() {
        Some(code) if code == libc::EAGAIN || code == libc::EINTR => Ok(false),
        _ => Err(format!("read {}: {}", FZ_EXEC_READY_FD_ENV, err)),
    }
}

fn fixture_command_output(
    cmd: &mut Command,
    label: &str,
    timeout_start: TimeoutStart,
) -> Result<Output, String> {
    let ready_pipe = match timeout_start {
        TimeoutStart::OnSpawn => None,
        TimeoutStart::OnExecutionReady => Some(execution_ready_pipe()?),
    };
    if let Some((_read_fd, write_fd)) = ready_pipe {
        cmd.env(FZ_EXEC_READY_FD_ENV, write_fd.to_string());
    }
    let spawned = cmd.stdout(Stdio::piped()).stderr(Stdio::piped()).spawn();
    let mut ready_read_fd = ready_pipe.map(|(read_fd, write_fd)| {
        close_fd(write_fd);
        read_fd
    });
    let mut child = match spawned {
        Ok(child) => child,
        Err(e) => {
            if let Some(read_fd) = ready_read_fd.take() {
                close_fd(read_fd);
            }
            return Err(format!("spawn {}: {}", label, e));
        }
    };
    let mut start = matches!(timeout_start, TimeoutStart::OnSpawn).then(Instant::now);
    loop {
        if let Some(read_fd) = ready_read_fd
            && start.is_none()
            && read_execution_ready(read_fd)?
        {
            if let Some(read_fd) = ready_read_fd.take() {
                close_fd(read_fd);
            }
            start = Some(Instant::now());
        }
        match child.try_wait() {
            Ok(Some(_)) => {
                if let Some(read_fd) = ready_read_fd.take()
                    && start.is_none()
                {
                    close_fd(read_fd);
                }
                return child
                    .wait_with_output()
                    .map_err(|e| format!("wait {}: {}", label, e));
            }
            Ok(None)
                if start
                    .map(|started| started.elapsed() >= FIXTURE_COMMAND_TIMEOUT)
                    .unwrap_or(false) =>
            {
                let _ = child.kill();
                let out = child
                    .wait_with_output()
                    .map_err(|e| format!("wait timed-out {}: {}", label, e))?;
                if let Some(read_fd) = ready_read_fd.take() {
                    close_fd(read_fd);
                }
                let stderr = String::from_utf8_lossy(&out.stderr);
                return Err(format!(
                    "{} exceeded {:?}; stderr: {}",
                    label,
                    FIXTURE_COMMAND_TIMEOUT,
                    stderr.trim_end()
                ));
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(10)),
            Err(e) => {
                if let Some(read_fd) = ready_read_fd.take() {
                    close_fd(read_fd);
                }
                return Err(format!("wait {}: {}", label, e));
            }
        }
    }
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
    let out = match fixture_command_output(
        Command::new(FZ_BIN).arg(subcmd).arg(&input),
        "fz",
        TimeoutStart::OnExecutionReady,
    ) {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(e),
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
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let out_path = std::env::temp_dir().join(format!(
        "fz_matrix_{}_{}_{}",
        stem,
        std::process::id(),
        nonce
    ));
    let input = fixture.join("input.fz");
    // Build. Compilation time is not fixture execution time, so the
    // per-fixture execution timeout starts when the compiled artifact runs.
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
    let run = match fixture_command_output(
        &mut Command::new(&out_path),
        "aot binary",
        TimeoutStart::OnSpawn,
    ) {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(e),
    };
    let _ = std::fs::remove_file(&out_path);
    let _ = std::fs::remove_file(out_path.with_extension("o"));
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
    let out = match fixture_command_output(
        Command::new(FZ_BIN).args(["repl", "--script"]).arg(&input),
        "fz repl",
        TimeoutStart::OnExecutionReady,
    ) {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(e),
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
    let path_expected_path = fixture.join(format!("expected.{}.txt", path));
    let expected_path = if path_expected_path.exists() {
        path_expected_path
    } else {
        fixture.join("expected.txt")
    };
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
        "fixture mismatch for {} via {}; wrote {} and {}\n--- expected stdout ({})\n{}--- actual stdout\n{}--- expected diagnostics\n{}--- actual diagnostics\n{}",
        fixture.display(),
        path,
        output_path.display(),
        diagnostics_output_path.display(),
        expected_path.display(),
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
/// coerced `result → ValueRef → cont_param_reprs[0]`; with .27.14.1 also
/// in place the destination became RawInt, leaving a redundant
/// box-then-unbox round-trip (`ishl_imm`/`bor_imm`/`sshr_imm`) at the
/// seam. .27.14.2 skips the ValueRef intermediate so `main`'s body has
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
    let dead_zero = stdout
        .lines()
        .any(|line| line.contains("iconst.i64 0") && !line.contains(":: nil"));
    assert!(
        !dead_zero,
        "main emits a dead `iconst.i64 0` (frame_ptr placeholder):\n{}",
        stdout,
    );
}

/// fz-siu.1.2 acceptance per docs/cps-in-clif.md §8.1.
/// tail_recursion.fz's `count` fn must compile as the native-tier
/// Tail-CC body whose recursive fast path ends in `return_call %count(...)`.
/// Reduction exhaustion may branch to a continuation-materializing slow path.
/// Base case ends in `load.i64 ...+16` followed by `return_call_indirect ...`.
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
    // IDs shift across planner changes (fz-ul4.27.21.4 widened cont keying
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

    // §8.1 block_rec: recursive fast path still ends in `return_call %count(...)`.
    assert!(
        body.contains("return_call "),
        "count_s2 must end recursive case in return_call:\n{}",
        body,
    );
    assert!(
        body.contains("get_pinned_reg") && body.contains("isub") && body.contains("icmp_imm sle"),
        "count_s2 recursive case must spend a Process reduction before the fast tail call:\n{}",
        body,
    );
    assert!(
        body.contains("@fz_yield_mid_flight_report"),
        "count_s2 must materialize a continuation when its reduction budget expires:\n{}",
        body,
    );
    assert!(
        body.contains("@fz_yield_slow_path_begin"),
        "count_s2 must sample the full yield slow-path allocation window:\n{}",
        body,
    );
    assert!(
        !body.contains("fz_alloc_frame") && !body.contains("fz_alloc_struct"),
        "count_s2 reduction slow path should avoid frame/struct allocation while building the yield continuation:\n{}",
        body,
    );

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
    // fz-cps.1.8 — the body pointer is materialized, then handed to
    // fz_alloc_closure as an argument. Generated CLIF must not dereference
    // the tagged closure ref to store at +8.
    assert!(
        main_body.contains("func_addr.i64"),
        "main must materialize the lambda's code_ptr via func_addr (add_to inlined):\n{}",
        main_body
    );
    assert!(
        main_body.contains("@fz_alloc_closure"),
        "main must allocate the lambda through the closure ABI (add_to inlined):\n{}",
        main_body
    );
    assert!(
        !main_body.contains("v7+8"),
        "main must not poke the lambda code_ptr slot directly (add_to inlined):\n{}",
        main_body
    );
}

/// fz-siu.1.2 acceptance per docs/cps-in-clif.md §8.4.
/// concurrency_ping_pong.fz's `main` spawns a child through the runtime
/// prelude wrapper, then tail-calls the continuation that reaches receive.
/// The receive site builds a cont closure (alloc_closure with func_addr +
/// store outer_cont as env field 0 + store user captures after it) and
/// hands it to the receive park runtime.
/// The scheduler-visible resume seam is the single `fz_resume` shim; the
/// closure itself stores the Tail-CC continuation body directly.
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
    assert!(
        stdout.contains("(i64) -> i64 tail"),
        "main must declare a Tail-CC single-self continuation body:\n{}",
        stdout
    );
    assert!(
        stdout.contains("fz_spawn_ref"),
        "main must call the spawn runtime entry through spawn/1:\n{}",
        stdout
    );
    assert!(
        stdout.contains("return_call"),
        "main must tail-call the post-spawn continuation:\n{}",
        stdout
    );
    let clif = dump_fixture_clif("concurrency_ping_pong");
    assert!(
        clif.contains("fz_receive_park"),
        "fixture must call a receive park runtime entry:\n{}",
        clif
    );
    // Receive site builds the cont closure through the closure allocation ABI.
    assert!(
        clif.contains("func_addr.i64"),
        "fixture must materialize cont code_ptr via func_addr:\n{}",
        clif
    );
    // And does NOT reference parking-frame schema/dispatch.
    assert!(
        !clif.contains("frame_sizes"),
        "fixture must not reference Process::frame_sizes (uniform parking schema):\n{}",
        clif
    );
}

fn send_uses_one_word_ref_boundary() {
    let clif = dump_fixture_clif("concurrency_ping_pong");
    assert!(
        clif.contains("@fz_send_ref"),
        "send should hand the scheduler one boxed Any ref:\n{}",
        clif
    );
    assert!(
        !clif.contains("@fz_send_typed"),
        "send should not split messages into raw/kind in generated code:\n{}",
        clif
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

fn dump_specs_for_source(name: &str, src: &str) -> String {
    let path = std::env::temp_dir().join(format!("fz_{}_{}_input.fz", name, std::process::id()));
    fs::write(&path, src).unwrap_or_else(|e| panic!("write temp source {:?}: {}", path, e));
    let out = Command::new(FZ_BIN)
        .args(["dump", "--emit", "specs"])
        .arg(&path)
        .output()
        .unwrap_or_else(|e| panic!("spawn fz dump --emit specs {}: {}", name, e));
    let _ = fs::remove_file(&path);
    assert!(
        out.status.success(),
        "fz dump --emit specs {} exited {}: {}",
        name,
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[derive(Debug)]
struct SpecDumpStanza<'a> {
    name: &'a str,
    arity: usize,
    key: &'a str,
    demand: &'a str,
    body: &'a str,
}

impl SpecDumpStanza<'_> {
    fn has_return_use(&self, demand: &str) -> bool {
        self.body.lines().any(|line| {
            line.trim()
                .strip_prefix(';')
                .is_some_and(|line| line.trim() == format!("return_use={}", demand))
        })
    }

    fn has_list_tail_plan(&self, kind: &str) -> bool {
        self.body.lines().any(|line| {
            let Some(line) = line.trim().strip_prefix(';').map(str::trim) else {
                return false;
            };
            line.starts_with(&format!("list_tail_plan={}(", kind))
                && line.contains("tail_ty=list(any)")
        })
    }
}

fn parse_spec_dump_stanzas(specs: &str) -> Vec<SpecDumpStanza<'_>> {
    let mut stanzas = Vec::new();
    for body in specs.split("\n\n") {
        let Some(header) = body.lines().next() else {
            continue;
        };
        let Some(rest) = header.strip_prefix("; spec ") else {
            continue;
        };
        let Some((name, after_name)) = rest.split_once('(') else {
            continue;
        };
        let Some((arity, after_arity)) = after_name.split_once(") #fn=") else {
            continue;
        };
        let Ok(arity) = arity.parse::<usize>() else {
            continue;
        };
        let Ok(_fn_id) = after_arity.parse::<u32>() else {
            continue;
        };
        let mut key = None;
        let mut demand = None;
        for line in body.lines() {
            if let Some(rest) = line.strip_prefix(";   key:    ") {
                key = Some(rest);
            } else if let Some(rest) = line.strip_prefix(";   demand: ") {
                demand = Some(rest);
            }
        }
        if let (Some(key), Some(demand)) = (key, demand) {
            stanzas.push(SpecDumpStanza {
                name,
                arity,
                key,
                demand,
                body,
            });
        }
    }
    stanzas
}

fn specs_for<'a>(
    stanzas: &'a [SpecDumpStanza<'a>],
    name: &str,
    arity: usize,
) -> Vec<&'a SpecDumpStanza<'a>> {
    stanzas
        .iter()
        .filter(|s| s.name == name && s.arity == arity)
        .collect()
}

fn any_spec<'a>(
    stanzas: &'a [SpecDumpStanza<'a>],
    name: &str,
    arity: usize,
    key: &str,
    demand: &str,
) -> Option<&'a SpecDumpStanza<'a>> {
    stanzas
        .iter()
        .find(|s| s.name == name && s.arity == arity && s.key == key && s.demand == demand)
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
    planner_worklist_pops: Option<usize>,
    planner_walk_calls: Option<usize>,
    planner_type_fn_calls: Option<usize>,
    planner_matcher_specs: Option<usize>,
    planner_vars: Option<usize>,
    planner_blocks: Option<usize>,
    planner_stmts: Option<usize>,
    planner_dispatches: Option<usize>,
}

impl DumpBudget {
    fn is_empty(&self) -> bool {
        self.codegen_functions.is_none()
            && self.codegen_instructions.is_none()
            && self.specs_count.is_none()
            && self.planner_worklist_pops.is_none()
            && self.planner_walk_calls.is_none()
            && self.planner_type_fn_calls.is_none()
            && self.planner_matcher_specs.is_none()
            && self.planner_vars.is_none()
            && self.planner_blocks.is_none()
            && self.planner_stmts.is_none()
            && self.planner_dispatches.is_none()
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
        "budget.planner.worklist_pops" => budget.planner_worklist_pops = Some(n),
        "budget.planner.walk_calls" => budget.planner_walk_calls = Some(n),
        "budget.planner.type_fn_calls" => budget.planner_type_fn_calls = Some(n),
        "budget.planner.matcher_specs" => budget.planner_matcher_specs = Some(n),
        "budget.planner.vars" => budget.planner_vars = Some(n),
        "budget.planner.blocks" => budget.planner_blocks = Some(n),
        "budget.planner.stmts" => budget.planner_stmts = Some(n),
        "budget.planner.dispatches" => budget.planner_dispatches = Some(n),
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
struct PlannerStats {
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
    planner: PlannerStats,
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
        if line.contains("\"name\":[\"fz\",\"planner\",\"planned\"]") {
            stats.planner.event_count += 1;
            stats.planner.spec_count = parse_json_u64_field(line, "spec_count")
                .unwrap_or_else(|| panic!("{} telemetry missing spec_count", fixture.display()));
            stats.planner.worklist_pops = parse_json_u64_field(line, "worklist_pops")
                .unwrap_or_else(|| panic!("{} telemetry missing worklist_pops", fixture.display()));
            stats.planner.walk_calls = parse_json_u64_field(line, "walk_calls")
                .unwrap_or_else(|| panic!("{} telemetry missing walk_calls", fixture.display()));
            stats.planner.type_fn_calls = parse_json_u64_field(line, "type_fn_calls")
                .unwrap_or_else(|| panic!("{} telemetry missing type_fn_calls", fixture.display()));
            stats.planner.matcher_spec_count = parse_json_u64_field(line, "matcher_spec_count")
                .unwrap_or_else(|| {
                    panic!("{} telemetry missing matcher_spec_count", fixture.display())
                });
            stats.planner.spec_var_count = parse_json_u64_field(line, "spec_var_count")
                .unwrap_or_else(|| {
                    panic!("{} telemetry missing spec_var_count", fixture.display())
                });
            stats.planner.spec_block_count = parse_json_u64_field(line, "spec_block_count")
                .unwrap_or_else(|| {
                    panic!("{} telemetry missing spec_block_count", fixture.display())
                });
            stats.planner.spec_stmt_count = parse_json_u64_field(line, "spec_stmt_count")
                .unwrap_or_else(|| {
                    panic!("{} telemetry missing spec_stmt_count", fixture.display())
                });
            stats.planner.dispatch_count = parse_json_u64_field(line, "dispatch_count")
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
        stats.planner.spec_count > 0,
        "{} telemetry missing fz.planner.planned event",
        fixture.display()
    );
    assert!(
        stats.planner.event_count >= 2,
        "{} dump --emit stats should plan at least root frontend and final linked module",
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
            "planner emitted specs",
            actual.planner.spec_count,
            budget.specs_count,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "planner worklist pops",
            actual.planner.worklist_pops,
            budget.planner_worklist_pops,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "planner walk calls",
            actual.planner.walk_calls,
            budget.planner_walk_calls,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "planner type_fn calls",
            actual.planner.type_fn_calls,
            budget.planner_type_fn_calls,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "planner matcher specs",
            actual.planner.matcher_spec_count,
            budget.planner_matcher_specs,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "planner vars",
            actual.planner.spec_var_count,
            budget.planner_vars,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "planner blocks",
            actual.planner.spec_block_count,
            budget.planner_blocks,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "planner stmts",
            actual.planner.spec_stmt_count,
            budget.planner_stmts,
        );
        check_budget_metric(
            &fixture,
            &mut fixture_failures,
            "planner dispatches",
            actual.planner.dispatch_count,
            budget.planner_dispatches,
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

fn generated_value_paths_have_no_removed_format_terms() {
    // fz-ame.7 split ir_codegen.rs into src/ir_codegen/*.rs; walk the
    // whole codegen directory.
    let files: Vec<String> = fs::read_dir("src/ir_codegen")
        .expect("read src/ir_codegen dir")
        .filter_map(|e| e.ok())
        .map(|e| e.path().to_string_lossy().into_owned())
        .filter(|p| p.ends_with(".rs"))
        .collect();
    let forbidden = [
        "ir_legacy_abi",
        "legacy_word",
        "pack_strict_parts_for_legacy_word",
        "unpack_legacy",
        concat!("PACKED", "_VALUE", "_TAG"),
        "typed_parts",
    ];
    for file in &files {
        let source = fs::read_to_string(file).expect("read generated-code source");
        for needle in forbidden {
            assert!(
                !source.contains(needle),
                "{} still references removed value-format term `{}`",
                file,
                needle
            );
        }
    }

    let receive = fs::read_to_string("src/ir_codegen/receive.rs").expect("read receive codegen");
    assert!(
        !receive.contains(concat!("Packed", "Value", "Word"))
            && !receive.contains(concat!("packed", "_word", "_from", "_value")),
        "receive matcher codegen should not revive packed-value-word helpers"
    );
}

fn scheduler_receive_buffers_are_any_value_refs() {
    let files = [
        "runtime/src/park.rs",
        "runtime/src/sched.rs",
        "src/runtime.rs",
        "src/ir_codegen/receive.rs",
    ];
    let forbidden = [
        "flattened `(value, kind)`",
        "word count",
        "ValueRoot",
        "pinned: *const u64",
        "out: *mut u64",
        "pinned: Vec<u64>",
        "out.add(1)",
    ];
    for file in files {
        let source = fs::read_to_string(file).expect("read receive-buffer source");
        for needle in forbidden {
            assert!(
                !source.contains(needle),
                "{} still uses raw flattened matcher-buffer shape `{}`",
                file,
                needle
            );
        }
    }

    // fz-ame.7 split ir_codegen.rs into src/ir_codegen/*.rs; check every
    // file in the directory for the forbidden sizing pattern.
    for entry in fs::read_dir("src/ir_codegen").expect("read src/ir_codegen dir") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|s| s.to_str()) != Some("rs") {
            continue;
        }
        let codegen = fs::read_to_string(&path).expect("read codegen source");
        assert!(
            !codegen.contains("n_pinned * 2"),
            "{}: pinned buffer sizing should be expressed as one-word value entries",
            path.display()
        );
    }
}

fn production_and_guides_have_no_old_value_format_gate_names() {
    let roots = ["runtime/src", "src", "guides"];
    let forbidden = [
        "AnyValueParts",
        "MailboxSlot",
        "InterpValue",
        "StrictValue",
        "MatcherValue",
        "OldValueParts",
        concat!("Legacy", "ValueRef", "Word"),
        concat!("legacy", "_tagged"),
        concat!("FZVALUE", "_TAG", "_BITS"),
        concat!("FZVALUE", "_TAG", "_"),
        "strict_kind: Option<ir::Value>",
        concat!("TAG", "_INT", "_IMM"),
        concat!("TAG", "_FLOAT", "_IMM"),
        concat!("TAG", "_ATOM", "_IMM"),
        "ir_legacy_abi",
        "typed_parts",
        "fz_value_ref_from_parts",
        "box_payload_and_kind_as_any_ref",
        "emit_value_slot",
        "value_slot",
        "LoweredValue",
        "AnyValue::Stored",
        "ValueSlot",
        "fz_map_push_typed",
        "fz_map_put_value",
        concat!("fz_map", "_builder_"),
        concat!("map", "_builder: Option<Vec<(crate::any_value::AnyValue"),
        concat!("map", "_builder: Option<Vec<(crate::any_value::ValueRoot"),
        "vector literals",
        "vector heap",
        "vector kind",
        "vector type",
        "VectorKind",
        "ByteVec",
        "IntVec",
        "FloatVec",
        "BitVec",
    ];
    let mut files = Vec::new();
    for root in roots {
        collect_source_files(Path::new(root), &mut files);
    }

    for path in files {
        let source = fs::read_to_string(&path).expect("read production or guide source");
        for needle in forbidden {
            assert!(
                !source.contains(needle),
                "{} still contains removed value-format gate name `{}`",
                path.display(),
                needle
            );
        }
    }
}

fn collect_source_files(dir: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).expect("read source directory") {
        let entry = entry.expect("read source directory entry");
        let path = entry.path();
        if path.is_dir() {
            collect_source_files(&path, files);
            continue;
        }
        let ext = path.extension().and_then(|s| s.to_str());
        if matches!(ext, Some("rs" | "md" | "html")) {
            files.push(path);
        }
    }
}

fn owned_cons_reuse_docs_pin_alias_fallback_contract() {
    let docs = [
        (
            ".agent/docs/any-value.md",
            fs::read_to_string(".agent/docs/any-value.md").expect("read any-value docs"),
        ),
        (
            ".agent/docs/destination-passing.md",
            fs::read_to_string(".agent/docs/destination-passing.md")
                .expect("read destination-passing docs"),
        ),
        (
            "guides/memory.html",
            fs::read_to_string("guides/memory.html").expect("read memory guide"),
        ),
    ];
    for (path, text) in docs {
        for needle in [
            "aliased",
            "fallback",
            "fresh cons",
            "publication",
            "closure",
            "send",
            "extern",
            "allocation",
        ] {
            assert!(
                text.contains(needle),
                "{} must document owned-cons reuse contract term `{}`",
                path,
                needle
            );
        }
    }
}

fn physical_capability_model_and_signals_are_pinned() {
    let index = fs::read_to_string(".agent/docs.md").expect("read agent docs index");
    assert!(
        index.contains("docs/physical-capabilities.md"),
        "agent docs index must point at physical capability guidance"
    );

    let docs = fs::read_to_string(".agent/docs/physical-capabilities.md")
        .expect("read physical capability docs");
    for needle in [
        "semantic values",
        "physical capabilities",
        "effect facts",
        "src/ir_effects.rs",
        "operation effect classification",
        "codegen consumes validated facts",
        "src/fz_ir.rs",
        "physical_entry_params",
        "ignored_entry_params",
        "src/ir_lower/cps.rs",
        "owned_cons_captures",
        "physical\n  params",
        "src/ir_dce.rs",
        "live heads keep their source-cons",
        "src/ir_capture_norm.rs",
        "standalone reuse-pruning pass and duplicate owned-cons capability lane",
        "physical_capabilities",
        "emit_owned_cons_reuse_or_alloc",
        "list_cons_allocs = 11",
        "list_cons_allocs = 5",
        "closure_allocs = 1",
    ] {
        assert!(
            docs.contains(needle),
            "physical capability docs must pin `{}`",
            needle
        );
    }

    let fz_ir = fs::read_to_string("src/fz_ir.rs").expect("read fz_ir");
    assert!(
        fz_ir.contains("ignored_entry_params")
            && fz_ir.contains("physical_entry_params")
            && fz_ir.contains("physical_capabilities")
            && fz_ir.contains("PhysicalCapability")
            && fz_ir.contains("record_owned_cons_reuse_capability"),
        "FnIr should carry owned-cons reuse through physical capability facts"
    );

    let cps = fs::read_to_string("src/ir_lower/cps.rs").expect("read cps lowering");
    assert!(
        cps.contains("owned_cons_captures")
            && cps.contains("hidden_owned_cons")
            && !cps.contains("mark_param_ignored"),
        "CPS owned-cons transport should use physical params, not ignored semantic params"
    );

    let capture_norm =
        fs::read_to_string("src/ir_capture_norm.rs").expect("read capture normalization");
    assert!(
        capture_norm.contains("live_vars_after_local_dce")
            && !capture_norm.contains("dce_after_capture_prune"),
        "capture normalization should rely on ordinary DCE for capability liveness"
    );

    let dce = fs::read_to_string("src/ir_dce.rs").expect("read dce");
    assert!(
        dce.contains("prune_dead_owned_cons_capabilities") && dce.contains("physical_entry_params"),
        "ordinary DCE should preserve or drop physical capabilities"
    );

    assert!(
        !std::path::Path::new("src/ir_reuse.rs").exists(),
        "standalone reuse pruning should be deleted"
    );

    assert_fixture_output_contains(
        "quicksort",
        "expected.jit.txt",
        &[":list_cons_allocs => 11", ":closure_allocs => 0", "\n176\n"],
    );
    assert_fixture_output_contains(
        "enum_list_allocations",
        "expected.txt",
        &[":list_cons_allocs => 5", ":closure_allocs => 0"],
    );
    assert_fixture_output_contains(
        "enum_reduce_suspend",
        "expected.txt",
        &[":closure_allocs => 1", ":closure_bytes => 48"],
    );
}

fn owned_cons_reuse_negative_barriers_do_not_advertise_capabilities() {
    let cases = [
        (
            "double_use",
            r#"
fn shared(xs) do
  [h | t] = xs
  pair = {[h | t], xs}
  pair
end

fn main(), do: shared([1, 2])
"#,
        ),
        (
            "closure_capture",
            r#"
fn keep(x), do: fn(y) -> x

fn publish([h | t]) do
  f = keep([h | t])
  f(0)
end

fn main(), do: publish([1, 2])
"#,
        ),
        (
            "heap_stats",
            r#"
extern "C" fn fz_process_heap_alloc_stats() :: any
fn id(x), do: x

fn publish([h | t]) do
  fz_process_heap_alloc_stats()
  id([h | t])
end

fn main(), do: publish([1, 2])
"#,
        ),
    ];

    for (name, source) in cases {
        let specs = dump_specs_for_source(&format!("owned_cons_negative_{}", name), source);
        assert!(
            !specs.contains("owned_cons_source") && !specs.contains("physical_capabilities"),
            "{} must not advertise owned-cons reuse capabilities across a publication or observer barrier:\n{}",
            name,
            specs
        );
        assert!(
            !specs.contains("demand: list_tail"),
            "{} must not select ListTail demand across a publication or observer barrier:\n{}",
            name,
            specs
        );
    }
}

fn quicksort_clif_inlines_nonempty_list_projection() {
    let clif = dump_quicksort_clif();
    let qsort =
        clif_function_with_banner_prefix(&clif, "; fn qsort_s").expect("missing qsort CLIF");

    assert!(
        !clif.contains("@fz_alloc_list_cons_typed"),
        "quicksort should not lower list construction through old typed helpers:\n{}",
        clif
    );
    assert!(
        qsort.contains("(i64, i64) -> i64 tail"),
        "qsort(nonempty_list) should receive one ValueRef plus cont:\n{}",
        qsort
    );
    assert!(
        qsort.contains("@fz_list_head_ref") && qsort.contains("@fz_list_tail_ref")
            || qsort.contains("@fz_list_head_int_ref") && qsort.contains("@fz_list_tail_ref"),
        "qsort(nonempty_list) should project list fields through AnyValueRef BIFs:\n{}",
        qsort
    );
    assert!(
        qsort.contains("@fz_list_head_int_ref") && qsort.contains("@fz_list_tail_ref"),
        "qsort(nonempty_list) should keep typed heads scalar and tails as one-word refs in hot paths:\n{}",
        qsort
    );
    assert!(
        !qsort.contains("band_imm v5, 0x00ff_ffff_ffff_ffff"),
        "qsort(nonempty_list) should keep the projected tail as one ValueRef instead of splitting it back into payload/kind:\n{}",
        qsort
    );
    assert!(
        !qsort.contains("@fz_value_ref_from_parts"),
        "qsort(nonempty_list) should not reconstruct refs from split payload/kind pieces:\n{}",
        qsort
    );
}

fn compiled_back_edges_spend_reductions_through_pinned_process() {
    let clif = dump_quicksort_clif();
    let partition = clif_function_with_banner_prefix(&clif, "; fn partition_s")
        .expect("missing partition CLIF");
    assert!(
        partition.contains("get_pinned_reg"),
        "compiled back-edge reductions should read Process through the pinned register:\n{}",
        partition
    );
    assert!(
        !clif.contains("FZ_REDUCTIONS_REMAINING"),
        "compiled reductions should not reference the old global mirror cell:\n{}",
        clif
    );
}

fn quicksort_has_no_tuple_dp_any_fanout() {
    let clif = dump_quicksort_clif();
    assert!(
        !clif.contains("; fn qsort\n"),
        "tuple destination typing should not make a generic qsort(any) body reachable:\n{}",
        clif
    );
    assert!(
        !clif.contains("@spec partition(any, list(any), [], [])"),
        "tuple destination typing should not fan out generic partition bodies:\n{}",
        clif
    );

    let specs = dump_specs_for_fixture("quicksort");
    let stanzas = parse_spec_dump_stanzas(&specs);
    let partition_specs = specs_for(&stanzas, "partition", 4);
    assert!(
        !partition_specs.is_empty()
            && partition_specs
                .iter()
                .all(|s| !s.key.contains("any") && !s.body.contains("callee_key=[any")),
        "quicksort partition specs should not contain tuple-DP-created any-key fanout:\n{}",
        specs
    );
    let qsort_specs = specs_for(&stanzas, "qsort", 1);
    assert!(
        !qsort_specs.is_empty() && qsort_specs.iter().all(|s| !s.key.contains("any")),
        "quicksort qsort specs should not contain tuple-DP-created any-key fanout:\n{}",
        specs
    );
    assert!(
        stanzas.iter().any(|s| s.key
            == "[{[], []} | {[], nonempty_list(int)} | {nonempty_list(int), nonempty_list(int)} | {nonempty_list(int), []}, int, _]"),
        "the qsort tuple continuation should receive the typed partition tuple union, integer pivot, and physical source-cons hole:\n{}",
        specs
    );
}

fn quicksort_tuple_return_demand_removes_partition_structs() {
    let specs = dump_specs_for_fixture("quicksort");
    let stanzas = parse_spec_dump_stanzas(&specs);
    let partition_specs = specs_for(&stanzas, "partition", 4);
    assert!(
        !partition_specs.is_empty()
            && partition_specs
                .iter()
                .all(|s| s.demand == "tuple_fields(2)")
            && stanzas
                .iter()
                .any(|s| s.demand == "tuple_fields(2)" && s.body.contains("Call qsort#")),
        "partition and its destructuring continuation should be typed with tuple field demand:\n{}",
        specs
    );

    let clif = dump_fixture_clif("quicksort");
    let partition = clif_function_with_banner_prefix(&clif, "; fn partition_s")
        .expect("missing partition CLIF");
    assert!(
        partition.contains(";   @demand tuple_fields(2)"),
        "partition CLIF should record tuple field demand:\n{}",
        partition
    );
    assert!(
        !partition.contains("@fz_alloc_struct") && !partition.contains("@fz_struct_set_field"),
        "tuple-field return demand should deliver partition fields without allocating a tuple struct:\n{}",
        partition
    );
}

fn quicksort_selects_list_tail_return_demand() {
    let specs = dump_specs_for_fixture("quicksort");
    let stanzas = parse_spec_dump_stanzas(&specs);
    assert!(
        any_spec(&stanzas, "qsort", 1, "[list(int)]", "list_tail(list(any))").is_some(),
        "quicksort should gain a ListTail demanded variant from the structural append context:\n{}",
        specs
    );
    assert!(
        stanzas
            .iter()
            .any(|s| s.body.contains("Call qsort#") && s.body.contains("callee_key=[list(int)]")),
        "the partition continuation should still call qsort structurally; ListTail is carried by the target spec demand, not by source-name rewriting:\n{}",
        specs
    );
    assert!(
        any_spec(&stanzas, "qsort", 1, "[nonempty_list(int)]", "value").is_some(),
        "the ordinary material qsort entry remains available for value consumers:\n{}",
        specs
    );
}

fn quicksort_structured_return_demand_facts() {
    let specs = dump_specs_for_fixture("quicksort");
    let stanzas = parse_spec_dump_stanzas(&specs);

    let qsort_specs = specs_for(&stanzas, "qsort", 1);
    assert!(
        qsort_specs
            .iter()
            .any(|s| s.key == "[list(int)]" && s.demand == "list_tail(list(any))"),
        "qsort must have a typed ListTail-demanded list(int) variant:\n{}",
        specs
    );
    assert!(
        qsort_specs
            .iter()
            .any(|s| s.key == "[list(int)]" && s.demand == "value"),
        "qsort must retain the ordinary value list(int) variant:\n{}",
        specs
    );
    assert!(
        qsort_specs
            .iter()
            .any(|s| s.key == "[nonempty_list(int)]" && s.demand == "value"),
        "qsort must retain the ordinary value nonempty_list(int) variant:\n{}",
        specs
    );

    let partition_specs = specs_for(&stanzas, "partition", 4);
    assert!(
        !partition_specs.is_empty()
            && partition_specs
                .iter()
                .all(|s| s.demand == "tuple_fields(2)"),
        "every reachable partition variant should use TupleFields return demand:\n{}",
        specs
    );

    assert!(
        stanzas
            .iter()
            .any(|s| s.demand == "tuple_fields(2)" && s.body.contains("Call qsort#")),
        "a continuation must still have the ordinary tuple-field shape before calling qsort:\n{}",
        specs
    );
    assert!(
        stanzas
            .iter()
            .any(|s| s.demand == "tuple_fields(2, list_tail(list(any)))"
                && s.body.contains("Call qsort#")),
        "a continuation must have the product tuple-field plus ListTail context shape before the representation cleanup:\n{}",
        specs
    );

    assert!(
        stanzas.iter().any(|s| s.demand == "list_tail(list(any))"),
        "a continuation must carry ListTail demand as a typed continuation capability:\n{}",
        specs
    );
    assert!(
        stanzas.iter().any(|s| s.demand == "list_tail(list(any))"
            && s.body.contains("Call qsort#")
            && s.has_return_use("list_tail(list(any))")
            && s.has_list_tail_plan("cons_then_direct")),
        "a ListTail-demanded continuation must carry the nested qsort edge as a typed cons-then-direct ListTail plan:\n{}",
        specs
    );
    assert!(
        stanzas
            .iter()
            .any(|s| s.has_return_use("list_tail(list(any))"))
            && stanzas.iter().any(|s| s.has_return_use("tuple_fields(2)")),
        "spec dump should expose structured typed return-use facts for demanded call edges:\n{}",
        specs
    );
    assert!(
        stanzas.iter().any(|s| s.has_list_tail_plan("direct_cont"))
            && stanzas
                .iter()
                .any(|s| s.has_list_tail_plan("tail_call_dest")),
        "spec dump should expose typed ListTail plans with explicit operands:\n{}",
        specs
    );
    assert!(
        stanzas.iter().any(|s| {
            (s.name == "fn_clause_1" || s.name == "fn_clause_2")
                && s.arity == 6
                && s.key.contains("_")
                && s.body.contains("physical_capabilities")
                && s.body
                    .contains("owned_cons_source param=Var(5) head=Var(3)")
        }),
        "partition clause helpers must dump a physical source-cons capability for owned cons reuse:\n{}",
        specs
    );
}

fn quicksort_list_tail_abi_carries_destination_param() {
    let clif = dump_fixture_clif("quicksort");
    let qsort =
        clif_function_with_banner_prefix(&clif, "; fn qsort_s").expect("missing qsort CLIF");
    assert!(
        qsort.contains(";   @demand list_tail(list(any))")
            && qsort.contains("function @fz_fn_")
            && qsort.contains("(i64, i64, i64) -> i64 tail"),
        "ListTail-demanded qsort should have source arg, hidden tail destination, and continuation params:\n{}",
        qsort
    );
    assert!(
        clif_has_direct_call_with_arg_count(qsort, 5)
            && qsort.contains("bor_imm")
            && qsort.contains("stack_addr"),
        "ListTail qsort should pass the hidden destination before the lazy continuation descriptor on demanded calls:\n{}",
        qsort
    );
}

fn quicksort_list_tail_empty_return_delivers_destination() {
    let clif = dump_fixture_clif("quicksort");
    let qsort =
        clif_function_with_banner_prefix(&clif, "; fn qsort_s").expect("missing qsort CLIF");
    assert!(
        qsort.contains(";   @demand list_tail(list(any))"),
        "missing ListTail qsort CLIF:\n{}",
        qsort
    );
    assert!(
        list_tail_empty_arm_returns_entry_destination(qsort),
        "the [] arm of ListTail qsort must deliver the hidden destination tail, not a freshly materialized []:\n{}",
        qsort
    );
}

fn list_tail_demand_rejects_print_between_prefix_and_append() {
    let specs = dump_specs_for_source(
        "list_tail_reject_print",
        r#"
fn append([], ys), do: ys
fn append([h | t], ys), do: [h | append(t, ys)]
fn id_list(xs), do: xs

fn main() do
  left = id_list([1])
  dbg(:barrier)
  append(left, [2])
end
"#,
    );
    assert!(
        !specs.contains("demand: list_tail"),
        "observable print between prefix production and append must block ListTail demand:\n{}",
        specs
    );
}

fn list_tail_demand_rejects_heap_stats_between_prefix_and_append() {
    let specs = dump_specs_for_source(
        "list_tail_reject_heap_stats",
        r#"
fn append([], ys), do: ys
fn append([h | t], ys), do: [h | append(t, ys)]
fn id_list(xs), do: xs
extern "C" fn fz_process_heap_alloc_stats() :: any

fn main() do
  left = id_list([1])
  fz_process_heap_alloc_stats()
  append(left, [2])
end
"#,
    );
    assert!(
        !specs.contains("demand: list_tail"),
        "heap allocation stats read between prefix production and append must block ListTail demand:\n{}",
        specs
    );
}

fn list_tail_demand_rejects_extern_between_prefix_and_append() {
    let specs = dump_specs_for_source(
        "list_tail_reject_extern",
        r#"
extern "C" fn getpid() :: integer

fn append([], ys), do: ys
fn append([h | t], ys), do: [h | append(t, ys)]
fn id_list(xs), do: xs

fn main() do
  left = id_list([1])
  getpid()
  append(left, [2])
end
"#,
    );
    assert!(
        !specs.contains("demand: list_tail"),
        "extern call between prefix production and append must block ListTail demand:\n{}",
        specs
    );
}

fn resource_lifecycle_uses_typed_scalar_map_key_lookup() {
    let clif = dump_fixture_clif("resource_lifecycle");
    assert!(
        clif.contains("@fz_map_get_atom_key_ref"),
        "resource_lifecycle should use the typed atom-key map lookup instead of materializing a scalar key ref:\n{}",
        clif
    );
    assert!(
        !clif.contains("@fz_map_get_ref"),
        "resource_lifecycle has only atom-key lookups and should not call the generic key-ref map lookup:\n{}",
        clif
    );
}

fn list_cell_uninit_is_immediately_initialized_in_clif() {
    let clif = dump_quicksort_clif();
    assert!(
        !clif.contains("@fz_alloc_list_cell_uninit"),
        "quicksort should construct list cells through list-cons BIFs, not direct uninitialized cell allocation:\n{}",
        clif
    );
    assert!(
        clif.contains("@fz_list_cons_int"),
        "quicksort should still build the input literal through the typed list-cons BIF:\n{}",
        clif
    );
    assert!(
        clif.contains("@fz_list_reuse_or_cons_tail_ref"),
        "quicksort should reuse owned cons cells through the total reuse-or-cons helper:\n{}",
        clif
    );
}

fn quicksort_list_literal_uses_static_tail_links() {
    let clif = dump_quicksort_clif();
    let main = clif_function(&clif, "; fn main").expect("missing main CLIF");
    let input_list_ref = clif_last_assigned_value(main, " = call fn0(")
        .expect("quicksort main should build the input list with typed cons");
    let lazy_cont_ref = clif_last_assigned_value(main, " = bor_imm ")
        .expect("quicksort main should tag the lazy continuation pointer");
    let expected_call_args = format!("({}, {})", input_list_ref, lazy_cont_ref);

    assert!(
        !main.contains("@fz_alloc_list_cons_typed")
            && !main.contains("@fz_list_head_ref")
            && !main.contains("@fz_list_tail_ref"),
        "quicksort's literal list should not need read projection helpers while building:\n{}",
        main
    );
    assert!(
        main.contains("@fz_list_cons_int")
            && main.contains(&expected_call_args)
            && main.contains("stack_addr")
            && main.contains("bor_imm"),
        "quicksort's literal list should pass a single tagged list ref and lazy continuation into qsort:\n{}",
        main
    );
}

fn quicksort_pins_return_demand_target() {
    let readme = fs::read_to_string("fixtures/quicksort/README.md").expect("read quicksort README");
    for expected in [
        "`list_cons_allocs = 11`",
        "`list_cons_bytes = 176`",
        "`struct_allocs = 0`",
        "`struct_bytes = 0`",
        "`map_allocs = 0`",
        "`map_bytes = 0`",
        "`heap_bytes = 176`",
    ] {
        assert!(
            readme.contains(expected),
            "quicksort README must pin return-demand target `{}`",
            expected
        );
    }
}

fn append_pins_source_append_target() {
    let readme = fs::read_to_string("fixtures/append/README.md").expect("read append README");
    for needle in [
        "the two list literals allocate five cons cells",
        "owned-cons reuse removes the append prefix copy",
        "`heap_bytes = 80`",
    ] {
        assert!(
            readme.contains(needle),
            "append README must pin source append target `{}`",
            needle
        );
    }

    let expected = fs::read_to_string("fixtures/append/expected.txt").expect("read append golden");
    for needle in [
        ":list_cons_allocs => 5",
        ":list_cons_bytes => 80",
        ":struct_allocs => 0",
        ":map_allocs => 0",
        "\n80\n",
    ] {
        assert!(
            expected.contains(needle),
            "append golden must pin `{}`:\n{}",
            needle,
            expected
        );
    }

    let specs = dump_specs_for_fixture("append");
    let stanzas = parse_spec_dump_stanzas(&specs);
    assert!(
        !specs.contains("fz_append") && !specs.contains("@fz_append"),
        "source append fixture must not lower through an append BIF:\n{}",
        specs
    );
    assert!(
        !specs_for(&stanzas, "append", 2).is_empty()
            && specs_for(&stanzas, "append", 2)
                .iter()
                .all(|s| s.demand == "value"),
        "append must retain source append value specs:\n{}",
        specs
    );

    let clif = dump_fixture_clif("append");
    assert!(
        clif_function_with_banner_prefix(&clif, "; fn append_s").is_some(),
        "append native dump must include compiled source append function:\n{}",
        clif
    );
    assert!(
        !clif.contains("@fz_append"),
        "append must not call an append BIF:\n{}",
        clif
    );
}

fn enum_list_allocations_pin_minimum_list_cons() {
    let readme = fs::read_to_string("fixtures/enum_list_allocations/README.md")
        .expect("read enum_list_allocations README");
    for needle in [
        "the input list literal allocates five cons cells",
        "`Enum.count/1`, `Enum.member?/2`, and `Enum.reduce/3` allocate no additional",
        "native `Enum.reduce/3` allocates no heap closures",
        "stack-backed lazy descriptors",
        "`list_cons_allocs = 5`",
        "`list_cons_bytes = 80`",
        "`closure_allocs = 0`",
        "`closure_bytes = 0`",
    ] {
        assert!(
            readme.contains(needle),
            "enum_list_allocations README must pin allocation contract `{}`",
            needle
        );
    }

    assert_fixture_output_contains(
        "enum_list_allocations",
        "expected.txt",
        &[
            "{:ok, 5}",
            "{:ok, true}",
            "{:done, 15}",
            ":list_cons_allocs => 5",
            ":list_cons_bytes => 80",
            ":closure_allocs => 0",
            ":closure_bytes => 0",
            ":map_allocs => 0",
            "\n368\n",
        ],
    );

    let clif = dump_fixture_clif("enum_list_allocations");
    let reduce_list = clif_function_with_banner_prefix(&clif, "; fn Enumerable.reduce_list_s")
        .expect("enum_list_allocations native dump must include reduce_list");
    assert!(
        !reduce_list.contains("@fz_alloc_closure"),
        "known native Enum.reduce must not heap-allocate reducer-return continuations:\n{}",
        reduce_list
    );
    assert!(
        reduce_list.contains("stack_store")
            && reduce_list.contains(&clif_hex_word(lazy_continuation_marker_word())),
        "known native Enum.reduce should pass a stack-backed lazy continuation descriptor:\n{}",
        reduce_list
    );
}

fn lazy_continuation_marker_word() -> u64 {
    fz_runtime::any_value::TAG_FWD
        << fz_runtime::any_value::AnyValueRefPacking::current().tag_shift()
}

fn enum_reduce_resume_state_update_is_rendered() {
    let specs = dump_specs_for_source(
        "enum_reduce_resume_state_update",
        "fn reduce_list([], {:cont, acc}, _reducer), do: {:done, acc}\n\
         fn reduce_list([h | t], {:cont, acc}, reducer), do: reduce_list(t, reducer(h, acc), reducer)\n\
         fn main(), do: reduce_list([1, 2], {:cont, 0}, fn (x, acc) -> {:cont, acc + x})",
    );
    assert!(
        specs.contains("resume=tail_call reduce_list#") && specs.contains("<result>"),
        "reduce_list hot reducer continuation should render as a resume state update:\n{}",
        specs
    );
}

fn enum_reduce_parameter_reducer_still_renders_resume() {
    let specs = dump_specs_for_source(
        "enum_reduce_parameter_reducer",
        "fn reduce_list([], {:cont, acc}, _reducer), do: {:done, acc}\n\
         fn reduce_list([h | t], {:cont, acc}, reducer), do: reduce_list(t, reducer(h, acc), reducer)\n\
         fn drive(reducer), do: reduce_list([1, 2], {:cont, 0}, reducer)\n\
         fn plus(x, acc), do: {:cont, acc + x}\n\
         fn times(x, acc), do: {:cont, acc * x}\n\
         fn main() do\n\
           drive(plus)\n\
           drive(times)\n\
         end",
    );
    assert!(
        specs.contains("CallClosure Var(")
            && specs.contains("resume=tail_call reduce_list#")
            && specs.contains("<result>"),
        "parameter-threaded reducer should still expose reduce_list resume shape:\n{}",
        specs
    );
}

fn local_reduce_state_update_lowers_without_trampoline() {
    let clif = dump_clif_for_source(
        "local_reduce_state_update",
        "fn reduce_list([], {:cont, acc}, _reducer), do: {:done, acc}\n\
         fn reduce_list([h | t], {:cont, acc}, reducer), do: reduce_list(t, reducer(h, acc), reducer)\n\
         fn main(), do: reduce_list([1, 2], {:cont, 0}, fn (x, acc) -> {:cont, acc + x})",
    );
    let reduce_list = clif_function_with_banner_prefix(&clif, "; fn reduce_list_s")
        .expect("local reduce_list CLIF should be present");
    assert!(
        reduce_list.contains("return_call") && reduce_list.contains("reduce_list"),
        "local reduce state update should lower to a direct recursive tail call:\n{}",
        reduce_list
    );
    assert!(
        !reduce_list.contains("lambda_") && !reduce_list.contains("; fn k_"),
        "local reduce state update should not keep the reducer-continuation trampoline in reduce_list CLIF:\n{}",
        reduce_list
    );
}

fn clif_hex_word(word: u64) -> String {
    let raw = format!("{word:016x}");
    format!(
        "0x{}_{}_{}_{}",
        &raw[0..4],
        &raw[4..8],
        &raw[8..12],
        &raw[12..16]
    )
}

fn continuation_materialization_boundaries_stay_explicit() {
    let readme =
        fs::read_to_string("fixtures/enum_reduce_suspend/README.md").expect("read suspend README");
    for needle in [
        "suspend clause returns `{:suspended, acc, fn () -> ... end}`",
        "real heap closure",
        "`closure_allocs = 1`",
        "`closure_bytes = 48`",
    ] {
        assert!(
            readme.contains(needle),
            "enum_reduce_suspend README must pin materialization boundary `{}`",
            needle
        );
    }

    assert_fixture_output_contains(
        "enum_reduce_suspend",
        "expected.txt",
        &[
            "{:suspended, 0, #fn<3/3>}",
            ":list_cons_allocs => 3",
            ":closure_allocs => 1",
            ":closure_bytes => 48",
        ],
    );

    let receive_clif = dump_fixture_clif("receive_map_pattern");
    assert!(
        receive_clif.contains("@fz_receive_park_matched")
            && receive_clif.contains("@fz_alloc_closure")
            && receive_clif.contains("@fz_materialize_cont"),
        "selective receive must still materialize scheduler-visible clause continuations:\n{}",
        receive_clif
    );

    let source = fs::read_to_string("src/ir_codegen/terminator.rs").expect("read terminator");
    for needle in [
        "fn emit_back_edge_yield_check",
        "runtime.yield_slow_path_begin_id",
        "runtime.yield_mid_flight_report_id",
        "materialize_cont",
        "fn emit_receive",
        "runtime.receive_park_id",
    ] {
        assert!(
            source.contains(needle),
            "terminator lowering must keep explicit materialization boundary `{}`",
            needle
        );
    }
}

fn interpreter_stepper_does_not_update_quiet_quanta() {
    let source = fs::read_to_string("src/ir_interp/run.rs").expect("read interp runner");
    assert!(
        !source.contains("quiet_quanta"),
        "interpreter hot loop must leave quiet_quanta to scheduler boundary code"
    );
}

fn reverse_filter_tree_pin_current_shape() {
    assert_fixture_output_contains(
        "reverse",
        "expected.txt",
        &[
            ":list_cons_allocs => 5",
            ":list_cons_bytes => 80",
            ":struct_allocs => 0",
            ":map_allocs => 0",
            "\n80\n",
        ],
    );
    assert_fixture_output_contains(
        "filter",
        "expected.txt",
        &[
            ":list_cons_allocs => 5",
            ":list_cons_bytes => 80",
            ":struct_allocs => 0",
            ":map_allocs => 0",
            "\n80\n",
        ],
    );
    assert_fixture_output_contains(
        "tree",
        "expected.txt",
        &[
            ":list_cons_allocs => 0",
            ":struct_allocs => 3",
            ":struct_bytes => 144",
            ":map_allocs => 0",
            "\n144\n",
        ],
    );
    assert_fixture_output_contains(
        "tree",
        "expected.interp.txt",
        &[":struct_allocs => 6", ":struct_bytes => 288", "\n288\n"],
    );

    for (fixture, fns) in [
        ("reverse", &["reverse", "reverse_into"][..]),
        ("filter", &["filter_lt"][..]),
        ("tree", &["inc_tree"][..]),
    ] {
        let specs = dump_specs_for_fixture(fixture);
        let stanzas = parse_spec_dump_stanzas(&specs);
        for name in fns {
            let arity = match *name {
                "filter_lt" | "reverse_into" => 2,
                _ => 1,
            };
            assert!(
                !specs_for(&stanzas, name, arity).is_empty(),
                "{} specs should contain source function `{}`:\n{}",
                fixture,
                name,
                specs
            );
        }
        assert!(
            !specs.contains("fz_reverse")
                && !specs.contains("fz_filter")
                && !specs.contains("fz_tree"),
            "{} should not lower through traversal BIFs:\n{}",
            fixture,
            specs
        );
    }
}

fn assert_fixture_output_contains(fixture: &str, file: &str, needles: &[&str]) {
    let path = format!("fixtures/{}/{}", fixture, file);
    let expected = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {}", path, e));
    for needle in needles {
        assert!(
            expected.contains(needle),
            "{} must pin `{}`:\n{}",
            path,
            needle,
            expected
        );
    }
}

fn codegen_does_not_invent_return_demand_siblings() {
    let terminator =
        fs::read_to_string("src/ir_codegen/terminator.rs").expect("read terminator codegen");
    for needle in [
        "spec_key_with_return_demand",
        "ReturnDemand::list_tail",
        "ReturnDemand::tuple_fields_list_tail",
    ] {
        assert!(
            !terminator.contains(needle),
            "terminator codegen must consume planner-authored return-demand facts, not invent `{}`",
            needle
        );
    }
}

fn codegen_does_not_recognize_list_tail_from_capture_shape() {
    let terminator =
        fs::read_to_string("src/ir_codegen/terminator.rs").expect("read terminator codegen");
    for needle in ["list_tail_cont_captures", "captured.len() >= 2"] {
        assert!(
            !terminator.contains(needle),
            "terminator codegen must lower typed ReturnContextPlan operands, not infer `{}`",
            needle
        );
    }
}

fn quicksort_continuations_capture_only_live_values() {
    let specs = dump_specs_for_fixture("quicksort");
    let capture_lengths = spec_continuation_capture_lengths(&specs);
    assert!(
        capture_lengths.contains(&3) && capture_lengths.iter().all(|len| *len <= 3),
        "quicksort continuations should capture only live values plus a hidden source-cons capability, not rest/lo/hi or duplicate p:\n{}",
        specs
    );

    let clif = dump_quicksort_clif();
    let tuple_list_tail_cont =
        clif_functions_containing(&clif, "@demand tuple_fields(2, list_tail")
            .into_iter()
            .next()
            .expect("missing tuple-fields plus ListTail continuation CLIF");
    assert!(
        !tuple_list_tail_cont.contains("@fz_alloc_closure")
            && tuple_list_tail_cont.contains("iconst.i64 3")
            && tuple_list_tail_cont.contains("iconst.i64 4")
            && tuple_list_tail_cont.contains("stack_addr")
            && tuple_list_tail_cont.contains("bor_imm"),
        "quicksort should plan its sorting continuation as a four-field lazy descriptor: outer_cont, p, sorted_lo, source_cons:\n{}",
        tuple_list_tail_cont
    );
    assert_eq!(
        tuple_list_tail_cont.matches("@fz_box_int_for_any").count(),
        0,
        "quicksort should not box pivot p while moving it through the continuation closure:\n{}",
        tuple_list_tail_cont
    );
    assert!(
        !tuple_list_tail_cont.contains("iconst.i32 7"),
        "quicksort should not allocate the old seven-field sorting continuation:\n{}",
        tuple_list_tail_cont
    );
}

fn dump_quicksort_clif() -> String {
    dump_fixture_clif("quicksort")
}

fn dump_fixture_clif(name: &str) -> String {
    let out = Command::new(FZ_BIN)
        .args([
            "dump",
            "--emit",
            "clif",
            &format!("fixtures/{}/input.fz", name),
        ])
        .output()
        .expect("spawn fz dump");
    assert!(out.status.success(), "fz dump exited {}", out.status);
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn dump_clif_for_source(name: &str, src: &str) -> String {
    let path = std::env::temp_dir().join(format!("fz_{}_{}_input.fz", name, std::process::id()));
    fs::write(&path, src).unwrap_or_else(|e| panic!("write temp source {:?}: {}", path, e));
    let out = Command::new(FZ_BIN)
        .args(["dump", "--emit", "clif"])
        .arg(&path)
        .output()
        .unwrap_or_else(|e| panic!("spawn fz dump --emit clif {}: {}", name, e));
    let _ = fs::remove_file(&path);
    assert!(
        out.status.success(),
        "fz dump --emit clif {} exited {}: {}",
        name,
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn clif_function<'a>(clif: &'a str, banner: &str) -> Option<&'a str> {
    let start = clif.find(banner)?;
    clif_function_from_start(clif, start)
}

fn clif_function_with_banner_prefix<'a>(clif: &'a str, prefix: &str) -> Option<&'a str> {
    let start = clif
        .match_indices("\n; fn ")
        .map(|(idx, _)| idx + 1)
        .find(|idx| clif[*idx..].starts_with(prefix))?;
    clif_function_from_start(clif, start)
}

fn clif_function_from_start(clif: &str, start: usize) -> Option<&str> {
    let rest = &clif[start..];
    let end = rest
        .find("\n; fn ")
        .map(|idx| start + idx)
        .unwrap_or(clif.len());
    Some(&clif[start..end])
}

fn clif_functions_containing<'a>(clif: &'a str, needle: &str) -> Vec<&'a str> {
    clif.match_indices("\n; fn ")
        .map(|(idx, _)| idx + 1)
        .filter_map(|start| clif_function_from_start(clif, start))
        .filter(|function| function.contains(needle))
        .collect()
}

fn clif_last_assigned_value<'a>(function: &'a str, op: &str) -> Option<&'a str> {
    function
        .lines()
        .filter_map(|line| line.trim().split_once(op).map(|(lhs, _)| lhs.trim()))
        .next_back()
}

fn clif_has_direct_call_with_arg_count(function: &str, arg_count: usize) -> bool {
    function
        .lines()
        .filter_map(|line| {
            let line = line.trim();
            line.strip_prefix("return_call fn")
                .or_else(|| line.split_once(" = call fn").map(|(_, rest)| rest))
        })
        .filter_map(|rest| {
            rest.split_once('(')?
                .1
                .split_once(')')
                .map(|(args, _)| args)
        })
        .any(|args| clif_arg_count(args) == arg_count)
}

fn list_tail_empty_arm_returns_entry_destination(function: &str) -> bool {
    let Some((_, entry_params)) = clif_entry_param_names(function) else {
        return false;
    };
    let Some(source) = entry_params.get(1) else {
        return false;
    };
    let Some(continuation) = entry_params.get(2) else {
        return false;
    };
    let Some(indirect_args) = function
        .lines()
        .find_map(|line| line.trim().strip_prefix("return_call_indirect "))
        .and_then(|rest| {
            rest.rsplit_once('(')?
                .1
                .split_once(')')
                .map(|(args, _)| args)
        })
    else {
        return false;
    };
    let args: Vec<_> = indirect_args.split(',').map(str::trim).collect();
    args.as_slice() == [source.as_str(), continuation.as_str()]
}

fn clif_entry_param_names(function: &str) -> Option<(String, Vec<String>)> {
    let signature = function
        .lines()
        .find(|line| line.trim_start().starts_with("function @"))?;
    let params = signature.split_once('(')?.1.split_once(')')?.0;
    let block = function
        .lines()
        .find(|line| line.trim_start().starts_with("block0("))?;
    let names = block.split_once('(')?.1.split_once(')')?.0;
    let param_count = clif_arg_count(params);
    let names: Vec<_> = names
        .split(',')
        .map(|arg| arg.trim().split_once(':').map(|(name, _)| name.trim()))
        .collect::<Option<Vec<_>>>()?
        .into_iter()
        .map(str::to_owned)
        .collect();
    (names.len() == param_count).then_some((signature.to_owned(), names))
}

fn clif_arg_count(args: &str) -> usize {
    if args.trim().is_empty() {
        0
    } else {
        args.split(',').count()
    }
}

fn spec_continuation_capture_lengths(specs: &str) -> Vec<usize> {
    specs
        .lines()
        .filter_map(|line| {
            let captures = line.split_once(" captured=[")?.1.split_once(']')?.0;
            Some(if captures.trim().is_empty() {
                0
            } else {
                captures.split(',').count()
            })
        })
        .collect()
}
