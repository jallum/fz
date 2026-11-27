//! fz-ul4.23.1 — fixture matrix.
//!
//! Walks `fixtures/*.fz` and runs each source program through the
//! compiler2 behavioural matrix. Behavioural metadata and optional prose live in a
//! comment-frontmatter block at the top of the source file, and sibling
//! sidecars carry the few artifacts that really need to stay out of the
//! program itself. stdout is compared against `expected.txt`;
//! diagnostics/stderr are compared against `expected.<path>.diagnostics` or
//! `expected.diagnostics`. Both default to empty when absent. Exit code must be
//! 0 unless the fixture declares a negative `expect:` contract.
//!
//! Single-file fixture layout:
//!
//!     fixtures/<NNNNN>_<name>.fz
//!     fixtures/<NNNNN>_<name>.expected.txt
//!     fixtures/<NNNNN>_<name>.expected.run.txt
//!     fixtures/<NNNNN>_<name>.expected.diagnostics
//!     fixtures/<NNNNN>_<name>.expected.run.diagnostics
//!     fixtures/<NNNNN>_<name>.expected.stderr
//!     fixtures/<NNNNN>_<name>.oracle.exs
//!
//! Frontmatter grammar:
//!
//!     #---
//!     purpose: one-line statement of what this fixture proves
//!     kind: run            # or `test`; defaults to run if `def main` is present
//!     expect: success      # or `abort` (run-time) / `diagnostic` (compile-time)
//!     diagnostic.code: spec/violation  # for telemetry-backed diagnostic fixtures
//!     defer: rationale     # optional whole-fixture deferral
//!     defer.build: rationale  # optional per-path deferral
//!     oracle: self         # the fixture is valid Elixir: its stdout owns expected.txt
//!                          # (or `oracle: <file>.exs`, a hand-written Elixir twin)
//!     oracle.stamp: 0123456789abcdef  # written by ORACLE=regen; see below
//!     args: -- "" "a b"    # program command line: after the source path for
//!                          # run/interp, to the built binary and to `elixir`;
//!                          # split on spaces, double quotes keep spaces
//!     timeout.interp_secs: 30  # path-specific CPU-limit override
//!     #---
//!
//! Every program invocation -- each `fz2` command, each built binary, each
//! Elixir oracle -- starts in its own empty working directory that the harness
//! creates and removes, so a fixture that writes a relative file name never
//! shares it with another path or run. Paths handed to programs are absolute.
//!
//! Behavioural routes default to `run`, `interp`, and `build`. A fixture may
//! narrow that set with a filename prefix such as `a-resource_dtor.fz` or
//! `00001_ja-some_fixture.fz`; `j` means `run`, `i` means `interp`, and `a`
//! means `build`.
//!
//! When `oracle:` is set, the `oracle_goldens_match_elixir` static test checks
//! the pair against the real `elixir` binary: the oracle's stdout must equal
//! `expected.txt`. `oracle: self` runs `elixir` on the fixture file itself; a
//! twin is a sibling `.exs` for a fixture that is not valid Elixir. A
//! successful fixture's fz paths reproduce that golden, so `fz == Elixir` holds
//! transitively. For an `expect: abort` oracle, Elixir must exit 1 with the
//! `expected.stderr` golden in its stderr, and its stdout is the golden; the fz
//! paths prove their rejection through `expected.stderr` and print the same
//! stdout. Elixir owns the golden -- per-path bless never rewrites
//! `expected.txt` for an oracle fixture.
//!
//! The header's `oracle.stamp` is a hash of the oracle program (for
//! `oracle: self`, the fixture without its stamp line), the golden and the
//! args. When it equals the hash of what is on disk, Elixir has already
//! confirmed the pair and is not started; otherwise the pair is run and
//! compared, and a pair Elixir agrees with but whose stamp is stale or missing
//! fails. `ORACLE=regen` rewrites goldens and stamps from Elixir's output,
//! `ORACLE=check` runs Elixir for every pair ignoring stamps (CI runs it when a
//! pull request changes the pinned Elixir or OTP version), and
//! `ORACLE_FIXTURE=<stem>` narrows either to one fixture.
//!
//! `expect: success` (the default) requires exit 0 with matching stdout/diagnostics.
//! `expect: abort` flips the contract: the program's main process fails, so it
//! must exit 1, and its stderr must contain the `expected.stderr` golden as a
//! substring. `expect:
//! diagnostic` checks the emitted `[fz, diag, error]` telemetry code.
//!
//! Workflow: re-run with `BLESS=1 cargo test fixture_matrix` to rewrite
//! `expected.txt` / `expected.<path>.txt` and `expected.diagnostics` from current output. On
//! failure (non-bless), actual output is dropped at sibling
//! `<name>.actual.txt` and `<name>.actual.diagnostics` for diffing.
//! Compiler-shape contracts live in compiler2 telemetry and fixture metadata.

use fz_fixture_metadata::{
    FixtureExpect as Fixture2Expect, FixtureKind as Fixture2Kind, FixtureMatrixPath, FixtureMetadata,
    fixture_matrix_paths_from_filename, oracle_stamp, parse_fixture_metadata, with_oracle_stamp, without_oracle_stamp,
};
use libtest_mimic::{Arguments, Failed, FormatSetting, Trial};
use std::collections::BTreeSet;
use std::env::{temp_dir, var};
use std::fs::{self, File, remove_file};
use std::io::{Error, Read, Seek, SeekFrom, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::process::{CommandExt as _, ExitStatusExt as _};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Output, Stdio, id};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
use std::time::{Duration, Instant};

#[path = "fixture_matrix/child_limit.rs"]
mod child_limit;
#[path = "fixture_matrix/child_limit_test.rs"]
mod child_limit_test;

use child_limit::{ChildLimit, SAMPLE_INTERVAL, Window, group_cpu_time};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");
const FZ_EXEC_READY_FD_ENV: &str = "FZ_EXEC_READY_FD";
/// The `oracle:` value that names the fixture file itself as the Elixir program.
const SELF_ORACLE: &str = "self";
/// Elixir's logger prints a crashed process's report on stdout, racing the
/// program's own exit. The report is never the program's output, so the oracle
/// runs Elixir with its logger silenced.
const ELIXIR_LOGGER_SILENCED: [&str; 2] = ["--erl", "-logger level none"];
const DEFAULT_FIXTURE_CPU_LIMIT: Duration = Duration::from_secs(20);
const MIN_EXECUTION_READY_WRITE_FD: RawFd = 10;
static AOT_TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

// fz-fkv — custom main: each (fixture, path) pair becomes its own
// `cargo test` trial, named `matrix::<fixture>::<path>`. `cargo test add1`
// filters to one fixture; `cargo test ::build` filters to one leg. Static
// invariant tests (CLIF shape, golden dumps, etc.) become trials too so
// the harness is uniform.
fn main() {
    let mut args = Arguments::from_args();
    args.format.get_or_insert(FormatSetting::Terse);
    if args.test_threads.is_none() {
        args.test_threads = var("RUST_TEST_THREADS").ok().and_then(|raw| raw.parse::<usize>().ok());
    }
    let mut trials: Vec<Trial> = Vec::new();

    // Static invariant trials. Bodies are unchanged from their previous
    // `#[test]` form; libtest-mimic catches panics from `assert!` and
    // reports them as failures.
    for (name, f) in static_tests() {
        let trial = Trial::test(name, move || {
            f();
            Ok(())
        });
        trials.push(trial);
    }

    // Dynamic matrix trials: one per (fixture, path).
    let bless = var("BLESS").ok().as_deref() == Some("1");
    for fixture in discover() {
        let name = fixture.name();
        let header = match parse_header(&fixture) {
            Ok(h) => h,
            Err(e) => {
                let msg = e.clone();
                trials.push(Trial::test(format!("matrix::{}::header", name), move || {
                    Err(Failed::from(msg))
                }));
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
            let trial_name = format!("matrix::{}::{}", name, path.id());
            let fixture = fixture.clone();
            let header = header.clone();
            let path = *path;
            let deferred_reason = header.defer_for_path(path).map(str::to_string);
            let is_deferred = deferred_reason.is_some();
            let mut trial = Trial::test(trial_name, move || {
                if let Some(reason) = &deferred_reason {
                    eprintln!("deferred: {}", reason);
                    return Ok(());
                }
                match check(&fixture, &header, path, bless) {
                    CheckOutcome::Pass => Ok(()),
                    CheckOutcome::Deferred(msg) => {
                        // Path declared but not yet wired (exit 75). Don't
                        // fail; surface the reason on stderr.
                        eprintln!("deferred: {}", msg);
                        Ok(())
                    }
                    CheckOutcome::Fail(e) => Err(Failed::from(e)),
                }
            });
            if is_deferred {
                trial = trial.with_ignored_flag(true);
            }
            trials.push(trial);
        }
    }

    libtest_mimic::run(&args, trials).exit();
}

/// List of (trial-name, fn-pointer) for every static invariant test in
/// this file. Kept explicit so adding a new test is a one-line append
/// and the trial list survives refactors.
fn static_tests() -> Vec<(&'static str, fn())> {
    vec![
        (
            "fixture_telemetry_reserves_its_path",
            fixture_telemetry_reserves_its_path,
        ),
        (
            "fixture_telemetry_cleans_failed_invocations",
            fixture_telemetry_cleans_failed_invocations,
        ),
        (
            "fixture_invocations_own_their_working_directory",
            fixture_invocations_own_their_working_directory,
        ),
        (
            "fixture_telemetry_concurrent_spec_violations",
            fixture_telemetry_concurrent_spec_violations,
        ),
        ("fixtures2_single_file_matrix_smoke", fixtures2_single_file_matrix_smoke),
        ("fixtures_describe_themselves", fixtures_describe_themselves),
        ("fixtures_lie_in_claimed_blocks", fixtures_lie_in_claimed_blocks),
        (
            "fixture_block_check_names_unclaimed_fixtures",
            fixture_block_check_names_unclaimed_fixtures,
        ),
        (
            "fixture_self_description_check_fails_on_violations",
            fixture_self_description_check_fails_on_violations,
        ),
        (
            "fixture_main_detection_follows_def_surface",
            fixture_main_detection_follows_def_surface,
        ),
        (
            "fixture_output_canonicalizes_closure_denotations",
            fixture_output_canonicalizes_closure_denotations,
        ),
        (
            "fixtures_route_via_filename_not_paths_frontmatter",
            fixtures_route_via_filename_not_paths_frontmatter,
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
            "runtime_private_helpers_declare_their_domains",
            runtime_private_helpers_declare_their_domains,
        ),
        (
            "quicksort_pins_return_demand_target",
            quicksort_pins_return_demand_target,
        ),
        (
            "enum_list_allocations_pin_minimum_list_cons",
            enum_list_allocations_pin_minimum_list_cons,
        ),
        (
            "enum_sort_constant_sorter_erased_under_return_demand_specs",
            enum_sort_constant_sorter_erased_under_return_demand_specs,
        ),
        (
            "self_send_copies_the_message_and_the_senders_list_stays_intact",
            self_send_copies_the_message_and_the_senders_list_stays_intact,
        ),
        (
            "a_list_a_continuation_captures_stays_rewritable_in_place",
            a_list_a_continuation_captures_stays_rewritable_in_place,
        ),
        (
            "a_struct_update_rewrites_only_a_base_nothing_else_holds",
            a_struct_update_rewrites_only_a_base_nothing_else_holds,
        ),
        (
            "a_resumed_frame_never_pops_across_a_block_boundary",
            a_resumed_frame_never_pops_across_a_block_boundary,
        ),
        (
            "each_place_a_binary_gains_a_second_holder_marks_it_shared",
            each_place_a_binary_gains_a_second_holder_marks_it_shared,
        ),
        (
            "a_send_probes_on_the_sender_and_gifts_its_result_through_the_receivers_in_queue",
            a_send_probes_on_the_sender_and_gifts_its_result_through_the_receivers_in_queue,
        ),
        (
            "a_hit_gifts_the_roots_a_clause_reads_and_not_one_copy_per_variable",
            a_hit_gifts_the_roots_a_clause_reads_and_not_one_copy_per_variable,
        ),
        (
            "a_matched_reply_fixture_collects_only_the_child_and_only_where_it_yields",
            a_matched_reply_fixture_collects_only_the_child_and_only_where_it_yields,
        ),
        (
            "a_long_body_copies_its_frame_forward_when_a_collection_kept_it",
            a_long_body_copies_its_frame_forward_when_a_collection_kept_it,
        ),
        (
            "a_list_the_body_no_longer_uses_is_not_kept_by_its_frame",
            a_list_the_body_no_longer_uses_is_not_kept_by_its_frame,
        ),
        (
            "a_receiver_parked_on_a_pinned_list_is_collected_on_every_path_and_still_matches",
            a_receiver_parked_on_a_pinned_list_is_collected_on_every_path_and_still_matches,
        ),
        (
            "a_programs_allocation_sites_are_reported_on_every_path_and_agree_between_run_and_build",
            a_programs_allocation_sites_are_reported_on_every_path_and_agree_between_run_and_build,
        ),
        (
            "a_resource_freed_by_a_collection_runs_its_destructor_once_on_every_path",
            a_resource_freed_by_a_collection_runs_its_destructor_once_on_every_path,
        ),
        (
            "a_receive_guard_reading_self_is_decided_by_the_receiver_whoever_runs_the_probe",
            a_receive_guard_reading_self_is_decided_by_the_receiver_whoever_runs_the_probe,
        ),
        (
            "a_receiver_left_parked_with_queued_gifts_drops_them_at_teardown",
            a_receiver_left_parked_with_queued_gifts_drops_them_at_teardown,
        ),
        (
            "many_senders_into_one_guarded_receive_gift_one_message_each_and_leave_the_misses_queued",
            many_senders_into_one_guarded_receive_gift_one_message_each_and_leave_the_misses_queued,
        ),
        (
            "a_large_list_passed_back_and_forth_crosses_as_one_gift_per_message_on_every_path",
            a_large_list_passed_back_and_forth_crosses_as_one_gift_per_message_on_every_path,
        ),
        (
            "a_built_binary_reports_the_same_probes_collections_and_destructors_as_run",
            a_built_binary_reports_the_same_probes_collections_and_destructors_as_run,
        ),
        (
            "a_receive_timer_is_armed_then_fired_or_cancelled_and_fires_in_deadline_order_on_every_path",
            a_receive_timer_is_armed_then_fired_or_cancelled_and_fires_in_deadline_order_on_every_path,
        ),
        ("fixture_hang_guard_policy", fixture_hang_guard_policy),
        (
            "a_child_kept_off_the_cpu_is_not_charged_for_waiting",
            child_limit_test::a_child_kept_off_the_cpu_is_not_charged_for_waiting,
        ),
        (
            "a_child_that_burns_cpu_past_the_limit_is_charged_for_it",
            child_limit_test::a_child_that_burns_cpu_past_the_limit_is_charged_for_it,
        ),
        (
            "a_descendant_that_burns_cpu_is_charged_to_the_child",
            child_limit_test::a_descendant_that_burns_cpu_is_charged_to_the_child,
        ),
        (
            "a_child_that_hangs_hits_the_wall_ceiling",
            child_limit_test::a_child_that_hangs_hits_the_wall_ceiling,
        ),
        (
            "a_failure_names_both_the_cpu_and_the_wall_time",
            child_limit_test::a_failure_names_both_the_cpu_and_the_wall_time,
        ),
        (
            "a_proc_stat_line_is_charged_to_its_group_by_the_fields_after_the_command_name",
            child_limit_test::a_proc_stat_line_is_charged_to_its_group_by_the_fields_after_the_command_name,
        ),
        (
            "execution_ready_writer_uses_multi_digit_descriptor",
            execution_ready_writer_uses_multi_digit_descriptor,
        ),
        (
            "fixture_command_capture_does_not_wait_for_an_open_writer",
            fixture_command_capture_does_not_wait_for_an_open_writer,
        ),
        (
            "fixture_command_rejects_missing_readiness",
            fixture_command_rejects_missing_readiness,
        ),
        (
            "fixture_command_verdict_follows_the_fixture_expectation",
            fixture_command_verdict_follows_the_fixture_expectation,
        ),
        ("fixture_readiness_eof_before_exit", fixture_readiness_eof_before_exit),
        ("fixture_readiness_exit_before_eof", fixture_readiness_exit_before_eof),
        (
            "fixture_readiness_drains_an_exited_child",
            fixture_readiness_drains_an_exited_child,
        ),
        (
            "kind_test_commands_signal_execution_ready_per_test",
            kind_test_commands_signal_execution_ready_per_test,
        ),
        (
            "execution_guard_covers_the_program_not_the_compile",
            execution_guard_covers_the_program_not_the_compile,
        ),
        (
            "kind_test_timeouts_kill_the_outer_command_and_its_hung_root",
            kind_test_timeouts_kill_the_outer_command_and_its_hung_root,
        ),
        (
            "build_output_owner_cleans_timeout_and_error_paths",
            build_output_owner_cleans_timeout_and_error_paths,
        ),
        (
            "diagnostic_build_path_cleans_every_output",
            diagnostic_build_path_cleans_every_output,
        ),
        ("oracle_goldens_match_elixir", oracle_goldens_match_elixir),
        (
            "oracle_regen_leaves_a_golden_that_already_matches_untouched",
            oracle_regen_leaves_a_golden_that_already_matches_untouched,
        ),
        (
            "oracle_regen_rewrites_a_golden_that_differs",
            oracle_regen_rewrites_a_golden_that_differs,
        ),
        (
            "oracle_unchanged_pair_does_not_start_elixir",
            oracle_unchanged_pair_does_not_start_elixir,
        ),
        (
            "oracle_pair_with_a_changed_script_golden_or_args_runs_elixir",
            oracle_pair_with_a_changed_script_golden_or_args_runs_elixir,
        ),
        (
            "oracle_agreeing_pair_with_a_stale_or_missing_stamp_fails_naming_regen",
            oracle_agreeing_pair_with_a_stale_or_missing_stamp_fails_naming_regen,
        ),
        (
            "oracle_check_mode_runs_elixir_despite_a_current_stamp",
            oracle_check_mode_runs_elixir_despite_a_current_stamp,
        ),
        (
            "oracle_stamps_in_the_tree_are_current_so_no_elixir_starts",
            oracle_stamps_in_the_tree_are_current_so_no_elixir_starts,
        ),
        (
            "oracle_stamp_of_a_self_oracle_hashes_the_fixture_without_its_stamp_line",
            oracle_stamp_of_a_self_oracle_hashes_the_fixture_without_its_stamp_line,
        ),
        (
            "oracle_self_runs_the_fixture_file_under_elixir",
            oracle_self_runs_the_fixture_file_under_elixir,
        ),
        (
            "an_oracle_ignores_the_report_of_a_spawned_process_that_crashed",
            an_oracle_ignores_the_report_of_a_spawned_process_that_crashed,
        ),
        (
            "oracle_abort_requires_exit_1_the_stderr_golden_and_the_stdout_golden",
            oracle_abort_requires_exit_1_the_stderr_golden_and_the_stdout_golden,
        ),
        (
            "oracle_regen_of_an_abort_writes_stdout_only",
            oracle_regen_of_an_abort_writes_stdout_only,
        ),
        (
            "an_fz_abort_of_an_oracle_fixture_must_print_the_stdout_golden",
            an_fz_abort_of_an_oracle_fixture_must_print_the_stdout_golden,
        ),
    ]
}

fn fixtures2_single_file_matrix_smoke() {
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = temp_dir().join(format!("fz_fixtures2_matrix_smoke_{}_{}", id(), nonce));
    fs::create_dir_all(&dir).expect("create smoke fixture dir");
    let path = dir.join("matrix_smoke.fz");
    fs::write(
        &path,
        "\
#---\n\
# purpose: single-file fixtures2 behavioural matrix smoke\n\
#---\n\
def main() do\n\
  dbg(1 + 1)\n\
end\n",
    )
    .expect("write smoke fixture");
    fs::write(dir.join("matrix_smoke.expected.txt"), "2\n").expect("write smoke golden");

    let fixture = FixtureCase::new(path.clone());
    let header = parse_header(&fixture).expect("parse smoke fixture header");
    for path in [
        FixtureMatrixPath::Run,
        FixtureMatrixPath::Interp,
        FixtureMatrixPath::Build,
    ] {
        match check(&fixture, &header, path, false) {
            CheckOutcome::Pass => {}
            other => panic!("fixtures2 single-file smoke via {} failed: {other:?}", path.id()),
        }
    }

    let _ = fs::remove_file(dir.join("matrix_smoke.expected.txt"));
    let _ = fs::remove_file(&path);
    let _ = fs::remove_dir(&dir);
}

/// True when `stem` matches `^\d{5}_[a-z0-9][a-z0-9_-]*$` — five digits, an
/// underscore, then a lowercase-alnum-led name (route codes like
/// `00001_ja-name` are legal; see `fixture_matrix_paths_from_filename`).
fn fixture_stem_is_numbered(stem: &str) -> bool {
    let bytes = stem.as_bytes();
    if bytes.len() < 7 || !bytes[..5].iter().all(u8::is_ascii_digit) || bytes[5] != b'_' {
        return false;
    }
    let tail = &stem[6..];
    match tail.chars().next() {
        Some(first) if first.is_ascii_lowercase() || first.is_ascii_digit() => {}
        _ => return false,
    }
    tail.chars()
        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_' || c == '-')
}

fn record_fixture_number(
    stem: &str,
    path: &Path,
    numbers: &mut std::collections::BTreeMap<String, PathBuf>,
    violations: &mut Vec<String>,
) {
    let number = &stem[..5];
    if let Some(first) = numbers.get(number) {
        violations.push(format!(
            "{}: number `{number}` reused (already used by {}); renumber one of them to the next free number in its block",
            path.display(),
            first.display()
        ));
    } else {
        numbers.insert(number.to_string(), path.to_path_buf());
    }
}

/// Every self-description invariant a `fixtures/*.fz` file must uphold:
/// parseable frontmatter carrying a `purpose`, and a `NNNNN_name` stem whose
/// number does not collide with any other fixture — including the numbered
/// homes in `number_only_dirs`, which are checked for uniqueness only. Those
/// dirs are the `fixtures2` corpus mid-migration into `fixtures/`; they are
/// not held to the purpose/stem rules, only asked not to collide with the
/// numbers `fixtures/` is claiming. Returns every violation found rather
/// than stopping at the first, so one failing trial reports the whole list.
fn fixture_self_description_violations(described_dirs: &[&Path], number_only_dirs: &[&Path]) -> Vec<String> {
    let mut violations = Vec::new();
    let mut numbers: std::collections::BTreeMap<String, PathBuf> = std::collections::BTreeMap::new();

    let mut described: Vec<PathBuf> = Vec::new();
    for dir in described_dirs {
        let Ok(entries) = fs::read_dir(dir) else { continue };
        described.extend(
            entries
                .filter_map(|e| e.ok())
                .map(|e| e.path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "fz")),
        );
    }
    described.sort();

    for path in &described {
        let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
        if !fixture_stem_is_numbered(&stem) {
            violations.push(format!(
                "{}: stem `{stem}` does not match ^\\d{{5}}_[a-z0-9][a-z0-9_-]*$",
                path.display()
            ));
            continue;
        }
        let source = fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
        let purpose = parse_fixture_metadata(&source)
            .unwrap_or_else(|e| panic!("parse frontmatter for {}: {e}", path.display()))
            .and_then(|metadata| metadata.purpose);
        if purpose.is_none() {
            violations.push(format!("{}: frontmatter has no `purpose:`", path.display()));
        }
        record_fixture_number(&stem, path, &mut numbers, &mut violations);
    }

    for dir in number_only_dirs {
        let Ok(entries) = fs::read_dir(dir) else { continue };
        for path in entries
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "fz"))
        {
            let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
            if !fixture_stem_is_numbered(&stem) {
                continue; // unnumbered: not part of the numbered corpus
            }
            record_fixture_number(&stem, &path, &mut numbers, &mut violations);
        }
    }

    violations
}

fn fixtures_describe_themselves() {
    let violations = fixture_self_description_violations(&[Path::new("fixtures")], &[Path::new("fixtures2")]);
    assert!(
        violations.is_empty(),
        "fixtures/*.fz must describe themselves (purpose, NNNNN_name stem, unique number):\n{}",
        violations.join("\n")
    );
}

/// The inclusive number ranges claimed by the rows of the block table in
/// `.agent/docs/fixtures.md`: lines shaped `| `NNNNN-NNNNN` | owner |`.
fn claimed_fixture_blocks(doc: &str) -> Vec<(u32, u32)> {
    doc.lines()
        .filter_map(|line| {
            let cell = line.strip_prefix("| `")?.split_once("` |")?.0;
            let (first, last) = cell.split_once('-')?;
            let digits = |s: &str| (s.len() == 5 && s.bytes().all(|b| b.is_ascii_digit())).then(|| s.parse().ok())?;
            Some((digits(first)?, digits(last)?))
        })
        .collect()
}

/// One violation per numbered `fixtures/*.fz` file whose number lies in no
/// claimed block.
fn unclaimed_fixture_violations(dir: &Path, claims: &[(u32, u32)]) -> Vec<String> {
    let mut paths: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "fz"))
        .collect();
    paths.sort();
    paths
        .iter()
        .filter_map(|path| {
            let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
            if !fixture_stem_is_numbered(&stem) {
                return None;
            }
            let number: u32 = stem[..5].parse().unwrap();
            let claimed = claims.iter().any(|&(first, last)| (first..=last).contains(&number));
            (!claimed).then(|| {
                format!(
                    "{}: number {number:05} lies in no claimed block; claim a block in the table in \
                     .agent/docs/fixtures.md (Reserved ranges), or renumber the fixture into its epic's block",
                    path.display()
                )
            })
        })
        .collect()
}

fn fixtures_lie_in_claimed_blocks() {
    let doc = fs::read_to_string(".agent/docs/fixtures.md").expect("read .agent/docs/fixtures.md");
    let claims = claimed_fixture_blocks(&doc);
    assert!(
        !claims.is_empty(),
        "no `| `NNNNN-NNNNN` | owner |` rows found in .agent/docs/fixtures.md"
    );
    let violations = unclaimed_fixture_violations(Path::new("fixtures"), &claims);
    assert!(
        violations.is_empty(),
        "every fixture number must lie in a block claimed in .agent/docs/fixtures.md:\n{}",
        violations.join("\n")
    );
}

fn fixture_block_check_names_unclaimed_fixtures() {
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = temp_dir().join(format!("fz_fixture_blocks_{}_{}", id(), nonce));
    fs::create_dir_all(&dir).expect("create block smoke dir");
    for name in ["00010_inside.fz", "00500_outside.fz"] {
        fs::write(dir.join(name), "").expect("write block smoke fixture");
    }
    let claims = claimed_fixture_blocks("| Block | Owner |\n| `00001-00099` | fz-x |\n| `00100-00199` | fz-y |\n");
    let violations = unclaimed_fixture_violations(&dir, &claims);
    let _ = fs::remove_dir_all(&dir);

    assert_eq!(claims, vec![(1, 99), (100, 199)], "table rows parse into ranges");
    assert_eq!(
        violations.len(),
        1,
        "only the unclaimed fixture is named: {violations:?}"
    );
    assert!(violations[0].contains("00500_outside.fz") && violations[0].contains("00500"));
}

fn fixture_self_description_check_fails_on_violations() {
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = temp_dir().join(format!("fz_fixture_self_description_{}_{}", id(), nonce));
    fs::create_dir_all(&dir).expect("create self-description smoke dir");

    // (a) missing purpose
    fs::write(
        dir.join("00001_no_purpose.fz"),
        "#---\n# root: main/0\n#---\ndef main() do\nend\n",
    )
    .expect("write no-purpose fixture");
    // (b) unnumbered name
    fs::write(
        dir.join("unnumbered_name.fz"),
        "#---\n# purpose: unnumbered\n#---\ndef main() do\nend\n",
    )
    .expect("write unnumbered fixture");
    // (c) reused number, both files otherwise well-formed
    fs::write(
        dir.join("00002_dup_a.fz"),
        "#---\n# purpose: first of a reused number\n#---\ndef main() do\nend\n",
    )
    .expect("write dup_a fixture");
    fs::write(
        dir.join("00002_dup_b.fz"),
        "#---\n# purpose: second of a reused number\n#---\ndef main() do\nend\n",
    )
    .expect("write dup_b fixture");

    let violations = fixture_self_description_violations(&[&dir], &[]);

    let _ = fs::remove_dir_all(&dir);

    assert!(
        violations.iter().any(|v| v.contains("no `purpose:`")),
        "expected a missing-purpose violation, got: {violations:?}"
    );
    assert!(
        violations.iter().any(|v| v.contains("does not match")),
        "expected an unnumbered-name violation, got: {violations:?}"
    );
    assert!(
        violations.iter().any(|v| v.contains("reused")),
        "expected a reused-number violation, got: {violations:?}"
    );
    assert_eq!(
        violations.len(),
        3,
        "expected exactly 3 violations, got: {violations:?}"
    );
}

fn fixtures_route_via_filename_not_paths_frontmatter() {
    for entry in fs::read_dir("fixtures").expect("read fixtures") {
        let path = entry.expect("fixture dir entry").path();
        if path.extension().is_none_or(|ext| ext != "fz") {
            continue;
        }
        let source = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
        assert!(
            !source.contains("# paths:"),
            "{} should derive behavioural routing from the filename/default matrix, not `paths:` frontmatter",
            path.display()
        );
        assert!(
            !source.contains("timeout.repl_secs"),
            "{} should not carry dead `repl` timeout cruft in the compiler2 matrix",
            path.display()
        );
        let fixture = FixtureCase::new(path.clone());
        let header = parse_header(&fixture).unwrap_or_else(|error| panic!("parse {}: {error}", path.display()));
        assert!(
            header
                .path_timeouts
                .iter()
                .all(|(_, timeout)| *timeout > DEFAULT_FIXTURE_CPU_LIMIT),
            "{} carries a timeout override no more generous than the shared CPU limit; \
             that is a performance stopwatch, not a nontermination backstop",
            path.display()
        );
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Run,
    Test,
}

/// What outcome a fixture declares it expects. The default (`Success`) is the
/// implicit contract for every fixture: exit 0, stdout/diagnostics match their
/// goldens. The two failure modes pin *negative* claims — a program that must
/// be rejected or must abort — which the matrix otherwise cannot express,
/// because it scores any nonzero exit as a failure before comparing output.
/// Abort fixtures pin stderr. A diagnostic fixture pins one of two things.
/// Declaring `diagnostic.code` pins the telemetry diagnostic code, so rendered
/// wording can improve without changing the semantic oracle; that is the right
/// pin when the code is what distinguishes this rejection from its neighbours.
/// Leaving it out falls back to the `expected.stderr` substring, which is the
/// right pin when several rejections share one code and the wording carries the
/// claim — a family of unbound-name diagnostics whose text is the contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum Expect {
    /// Exit 0; stdout + diagnostics compared against goldens. The default.
    #[default]
    Success,
    /// Run-time abort (nonzero exit while running), e.g. a failed `assert`
    /// routing through `Kernel.panic`. AOT: the build must succeed first, then
    /// the binary must abort.
    Abort,
    /// Compile-time rejection (nonzero exit before running), e.g. an `@spec`
    /// violation. AOT: the `fz2 build` itself must fail.
    Diagnostic,
}

#[derive(Debug, Clone)]
struct Header {
    paths: Vec<FixtureMatrixPath>,
    kind: Kind,
    expect: Expect,
    diagnostic_code: Option<String>,
    defer: Option<String>,
    path_deferrals: Vec<(FixtureMatrixPath, String)>,
    /// Relative path (within the fixture dir) to an Elixir twin whose stdout
    /// owns `expected.txt`. See `oracle_goldens_match_elixir`.
    oracle: Option<String>,
    /// The `oracle.stamp` recorded in the header.
    oracle_stamp: Option<String>,
    /// The program's command line, passed after the source path to run and
    /// interp, to the built binary, and to the Elixir oracle.
    args: Vec<String>,
    path_timeouts: Vec<(FixtureMatrixPath, Duration)>,
}

impl Header {
    fn timeout_for_path(&self, path: FixtureMatrixPath) -> Duration {
        self.path_timeouts
            .iter()
            .find_map(|(timeout_path, timeout)| (*timeout_path == path).then_some(*timeout))
            .unwrap_or(DEFAULT_FIXTURE_CPU_LIMIT)
    }

    fn defer_for_path(&self, path: FixtureMatrixPath) -> Option<&str> {
        self.path_deferrals
            .iter()
            .find_map(|(deferred_path, rationale)| (*deferred_path == path).then_some(rationale.as_str()))
    }

    /// `expect: diagnostic` declares a source the compiler must refuse, so no
    /// program may start; every other expectation runs one.
    fn execution_boundary(&self) -> ExecutionBoundary {
        match self.expect {
            Expect::Diagnostic => ExecutionBoundary::Refused,
            Expect::Success | Expect::Abort => ExecutionBoundary::Announced,
        }
    }
}

fn absolute(path: &Path) -> PathBuf {
    std::path::absolute(path).unwrap_or_else(|error| panic!("absolute {}: {error}", path.display()))
}

#[derive(Debug, Clone)]
struct FixtureCase {
    path: PathBuf,
}

impl FixtureCase {
    fn new(path: impl Into<PathBuf>) -> Self {
        Self { path: path.into() }
    }

    fn name(&self) -> String {
        self.path.file_stem().unwrap().to_string_lossy().into_owned()
    }

    fn display_path(&self) -> &Path {
        self.path.as_path()
    }

    /// Absolute, because every program invocation starts in its own working
    /// directory rather than the repository root.
    fn source_path(&self) -> PathBuf {
        absolute(&self.path)
    }

    fn source_dir(&self) -> PathBuf {
        self.path.parent().expect("fixture parent").to_path_buf()
    }

    fn sidecar_path(&self, suffix: &str) -> PathBuf {
        let stem = self.path.file_stem().expect("fixture stem").to_string_lossy();
        self.path.with_file_name(format!("{stem}.{suffix}"))
    }

    fn actual_path(&self, artifact: &str) -> PathBuf {
        self.sidecar_path(&format!("actual.{artifact}"))
    }

    fn oracle_path(&self, rel: &str) -> PathBuf {
        if rel == SELF_ORACLE {
            return self.source_path();
        }
        if rel == "oracle.exs" {
            return absolute(&self.sidecar_path(rel));
        }
        absolute(&self.source_dir().join(rel))
    }

    fn canonical_source_name(&self) -> String {
        self.path.to_string_lossy().into_owned()
    }

    fn normalize_expected_diagnostics(&self, text: &str) -> String {
        let text = text.replace(
            self.source_path().to_string_lossy().as_ref(),
            &self.canonical_source_name(),
        );
        text.split_inclusive('\n')
            .map(|line| self.normalize_gutter_padding(line))
            .collect()
    }

    fn normalize_actual_diagnostics(&self, text: &str) -> String {
        let text = self.normalize_expected_diagnostics(text);
        self.normalize_reported_source_lines(&text)
    }

    fn normalize_reported_source_lines(&self, text: &str) -> String {
        text.split_inclusive('\n')
            .map(|line| {
                let line = self.normalize_path_line_ref(line);
                self.normalize_gutter_line_ref(&line)
            })
            .collect()
    }

    fn normalize_path_line_ref(&self, line: &str) -> String {
        let marker = format!("{}:", self.canonical_source_name());
        let Some(start) = line.find(&marker) else {
            return line.to_string();
        };
        let number_start = start + marker.len();
        let bytes = line.as_bytes();
        let number_end = take_ascii_digits(bytes, number_start);
        if number_end == number_start || number_end >= bytes.len() || bytes[number_end] != b':' {
            return line.to_string();
        }
        let reported = line[number_start..number_end]
            .parse::<usize>()
            .expect("path line number");
        let normalized = self.normalize_reported_line_number(reported);
        let mut out = String::with_capacity(line.len());
        out.push_str(&line[..number_start]);
        out.push_str(&normalized.to_string());
        out.push_str(&line[number_end..]);
        out
    }

    fn normalize_gutter_line_ref(&self, line: &str) -> String {
        let line = self.normalize_gutter_padding(line);
        let bytes = line.as_bytes();
        let index = 0usize;
        let digits_end = take_ascii_digits(bytes, index);
        if digits_end == index
            || digits_end + 1 >= bytes.len()
            || bytes[digits_end] != b' '
            || bytes[digits_end + 1] != b'|'
        {
            return line;
        }
        let reported = line[index..digits_end].parse::<usize>().expect("gutter line number");
        let normalized = self.normalize_reported_line_number(reported);
        let mut out = String::with_capacity(line.len());
        out.push_str(&normalized.to_string());
        out.push_str(&line[digits_end..]);
        out
    }

    fn normalize_gutter_padding(&self, line: &str) -> String {
        let bytes = line.as_bytes();
        let mut index = 0usize;
        while index < bytes.len() && bytes[index] == b' ' {
            index += 1;
        }
        let digits_end = take_ascii_digits(bytes, index);
        if digits_end == index
            || digits_end + 1 >= bytes.len()
            || bytes[digits_end] != b' '
            || bytes[digits_end + 1] != b'|'
        {
            return line.to_string();
        }
        let mut out = String::with_capacity(line.len());
        out.push_str(&line[index..digits_end]);
        out.push_str(&line[digits_end..]);
        out
    }

    fn normalize_reported_line_number(&self, reported: usize) -> usize {
        let prefix = self.leading_comment_lines();
        if reported > prefix { reported - prefix } else { reported }
    }

    fn leading_comment_lines(&self) -> usize {
        fs::read_to_string(&self.path)
            .unwrap_or_else(|e| panic!("read {}: {}", self.path.display(), e))
            .lines()
            .take_while(|line| line.trim_start().starts_with('#'))
            .count()
    }
}

fn take_ascii_digits(bytes: &[u8], mut index: usize) -> usize {
    while index < bytes.len() && bytes[index].is_ascii_digit() {
        index += 1;
    }
    index
}

fn has_main(src: &str) -> bool {
    src.lines()
        .any(|line| line.contains("def main(") || line.contains("def main "))
}

fn fixture_main_detection_follows_def_surface() {
    assert!(has_main("def main(), do: :ok\n"));
    assert!(has_main("def main do\n  :ok\nend\n"));
}

fn parse_header(fixture: &FixtureCase) -> Result<Header, String> {
    parse_header_from_single_file(&fixture.path)
}

fn parse_header_from_single_file(path: &Path) -> Result<Header, String> {
    let source = fs::read_to_string(path).map_err(|e| format!("read {}: {}", path.display(), e))?;
    let metadata = parse_fixture_metadata(&source)
        .map_err(|e| format!("{}: {}", path.display(), e))?
        .ok_or_else(|| format!("{}: missing fixtures2 `#---` frontmatter block", path.display()))?;
    header_from_fixture_metadata(path, &source, &metadata)
}

fn header_from_fixture_metadata(path: &Path, source: &str, metadata: &FixtureMetadata) -> Result<Header, String> {
    let _purpose = metadata
        .purpose
        .clone()
        .ok_or_else(|| format!("{}: missing `purpose:`", path.display()))?;
    let paths = if metadata.matrix.defer.is_some() {
        Vec::new()
    } else {
        fixture_matrix_paths_from_filename(path)
            .map_err(|e| format!("{}: {}", path.display(), e))?
            .unwrap_or_else(|| FixtureMatrixPath::ALL.to_vec())
    };
    let kind = match metadata.matrix.kind {
        Some(Fixture2Kind::Run) => Kind::Run,
        Some(Fixture2Kind::Test) => Kind::Test,
        None => {
            if has_main(source) {
                Kind::Run
            } else {
                Kind::Test
            }
        }
    };
    let expect = match metadata.matrix.expect {
        Some(Fixture2Expect::Success) | None => Expect::Success,
        Some(Fixture2Expect::Abort) => Expect::Abort,
        Some(Fixture2Expect::Diagnostic) => Expect::Diagnostic,
    };
    for deferral in &metadata.matrix.path_deferrals {
        if !paths.contains(&deferral.path) {
            return Err(format!(
                "{}: `defer.{}` names an undeclared path",
                path.display(),
                deferral.path
            ));
        }
    }
    let path_timeouts = metadata
        .matrix
        .path_timeouts
        .iter()
        .map(|timeout| (timeout.path, Duration::from_secs(timeout.seconds)))
        .collect();
    Ok(Header {
        paths,
        kind,
        expect,
        diagnostic_code: metadata.matrix.diagnostic_code.clone(),
        defer: metadata.matrix.defer.clone(),
        path_deferrals: metadata
            .matrix
            .path_deferrals
            .iter()
            .map(|deferral| (deferral.path, deferral.rationale.clone()))
            .collect(),
        oracle: metadata.matrix.oracle.clone(),
        oracle_stamp: metadata.matrix.oracle_stamp.clone(),
        args: metadata.matrix.args.clone(),
        path_timeouts,
    })
}

/// Discover behavioural fixtures under `fixtures/` — the flat, numbered,
/// purpose-bearing home. The directory is walked non-recursively; sorted by
/// name so trial order (and BLESS diffs) stay stable across runs.
fn discover() -> Vec<FixtureCase> {
    let dir = Path::new("fixtures");
    let mut out: Vec<FixtureCase> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{} should exist: {}", dir.display(), e))
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "fz"))
        .map(FixtureCase::new)
        .collect();
    out.sort_by_key(|fixture| fixture.name());
    out
}

/// A faithful capture of what the program did on one path — exit status plus
/// output — with *no* success/failure judgement applied. That judgement is the
/// fixture's `expect:` policy, applied uniformly in `check()`, so the
/// success-vs-failure rule lives in one place rather than being re-derived in
/// each path runner.
struct Ran {
    /// The program's exit status.
    status: ExitStatus,
    /// stdout, captured verbatim.
    stdout: String,
    /// stderr / diagnostics, captured verbatim.
    diagnostics: String,
}

/// Outcome of running a fixture through a single path.
enum RunOutcome {
    /// The program ran to completion; see [`Ran`].
    Ran(Ran),
    /// Process exited 75 (EX_TEMPFAIL): the path is declared by the fixture
    /// but not yet wired (e.g. `fz interp` stub before fz-ul4.23.5.2). The
    /// matrix logs but does not fail.
    Deferred(String),
    /// The harness itself failed — spawn error, timeout, or a build that was
    /// required to succeed (for an `expect: success`/`abort` AOT fixture) but
    /// didn't. Never the program's own nonzero exit.
    Failed(String),
}

/// What a command is expected to do about starting a program. It decides both
/// when the execution clock starts and what the readiness pipe must show.
#[derive(Clone, Copy)]
enum ExecutionBoundary {
    /// The command is itself the thing being timed — a built binary, a build,
    /// an oracle — so the execution clock starts at spawn and there is no
    /// readiness pipe.
    Spawn,
    /// A program starts and announces itself; each announcement opens an
    /// execution window.
    Announced,
    /// The fixture declares that the compiler must refuse this source, so no
    /// program may start and an announcement is the finding.
    Refused,
}

enum ExecutionReady {
    Pending,
    Ready,
    Closed,
}

#[derive(Debug, PartialEq, Eq)]
enum FixtureCommandState {
    Running,
    Exited,
    /// The command did not do what the fixture expects about starting a
    /// program; the variant carries the finding.
    BoundaryFailed(String),
}

/// The fixture's own expectation decides the verdict, not the exit status: a
/// fixture that expects a program to run is not served by a command that exits
/// nonzero without running one, and a fixture that expects to be refused is not
/// served by a compiler that ran its program anyway. Until the command exits,
/// pipe EOF decides nothing; the setup guard bounds the wait.
fn fixture_command_state(
    boundary: ExecutionBoundary,
    readiness_bytes: usize,
    status: Option<ExitStatus>,
) -> FixtureCommandState {
    if status.is_none() {
        return FixtureCommandState::Running;
    }
    match (boundary, readiness_bytes) {
        (ExecutionBoundary::Announced, 0) => {
            FixtureCommandState::BoundaryFailed("never started a program (0 readiness bytes)".to_string())
        }
        (ExecutionBoundary::Refused, started @ 1..) => FixtureCommandState::BoundaryFailed(format!(
            "started a program ({started} readiness bytes) though the fixture declares the compiler must refuse it"
        )),
        _ => FixtureCommandState::Exited,
    }
}

#[derive(Debug)]
struct GuardedOutput {
    output: Output,
    execution_ready_count: usize,
}

struct CommandCapture {
    stdout: File,
    stderr: File,
}

impl CommandCapture {
    fn new() -> Result<Self, String> {
        Ok(Self {
            stdout: anonymous_capture("stdout")?,
            stderr: anonymous_capture("stderr")?,
        })
    }

    fn stdio(&self) -> Result<(Stdio, Stdio), String> {
        let clone = |file: &File| file.try_clone().map(Stdio::from).map_err(|error| error.to_string());
        Ok((clone(&self.stdout)?, clone(&self.stderr)?))
    }

    fn output(mut self, status: ExitStatus) -> Result<Output, String> {
        fn read(file: &mut File) -> Result<Vec<u8>, String> {
            let length = file.metadata().map_err(|error| error.to_string())?.len();
            file.seek(SeekFrom::Start(0)).map_err(|error| error.to_string())?;
            let mut bytes = Vec::new();
            file.take(length)
                .read_to_end(&mut bytes)
                .map_err(|error| error.to_string())?;
            Ok(bytes)
        }
        Ok(Output {
            status,
            stdout: read(&mut self.stdout)?,
            stderr: read(&mut self.stderr)?,
        })
    }
}

struct FixtureTempFile {
    path: Option<PathBuf>,
    file: Option<File>,
}

impl FixtureTempFile {
    fn new(label: &str) -> Result<Self, String> {
        loop {
            let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
            let path = temp_dir().join(format!("fz_fixture_{}_{}_{}", id(), nonce, label));
            match File::options().read(true).write(true).create_new(true).open(&path) {
                Ok(file) => {
                    return Ok(Self {
                        path: Some(path),
                        file: Some(file),
                    });
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(format!("create fixture {label}: {error}")),
            }
        }
    }

    fn path(&self) -> &Path {
        self.path.as_deref().expect("named temporary file has a path")
    }

    fn unlink(mut self) -> Result<File, String> {
        let path = self.path();
        remove_file(path).map_err(|error| format!("unlink {}: {error}", path.display()))?;
        self.path = None;
        Ok(self.file.take().expect("created capture has a file"))
    }
}

impl Drop for FixtureTempFile {
    fn drop(&mut self) {
        if let Some(path) = &self.path {
            let _ = remove_file(path);
        }
    }
}

/// The working directory of one program invocation: empty when the program
/// starts, removed when the invocation ends however it ends. A relative file
/// name therefore means a file no other run can see.
struct FixtureWorkingDir {
    path: PathBuf,
}

impl FixtureWorkingDir {
    fn new() -> Result<Self, String> {
        let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let path = temp_dir().join(format!("fz_fixture_{}_{}_cwd", id(), nonce));
        fs::create_dir(&path).map_err(|error| format!("create working directory {}: {error}", path.display()))?;
        Ok(Self { path })
    }
}

impl Drop for FixtureWorkingDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn anonymous_capture(stream: &str) -> Result<File, String> {
    FixtureTempFile::new(stream)?.unlink()
}

fn default_child_limit() -> ChildLimit {
    ChildLimit::of_cpu(DEFAULT_FIXTURE_CPU_LIMIT)
}

fn execution_start(boundary: ExecutionBoundary, now: Instant) -> Option<Instant> {
    matches!(boundary, ExecutionBoundary::Spawn).then_some(now)
}

fn execution_ready_pipe() -> Result<(OwnedFd, OwnedFd), String> {
    let mut fds = [0; 2];
    let rc = unsafe { libc::pipe(fds.as_mut_ptr()) };
    if rc != 0 {
        return Err(format!("pipe {}: {}", FZ_EXEC_READY_FD_ENV, Error::last_os_error()));
    }
    let read_fd = unsafe { OwnedFd::from_raw_fd(fds[0]) };
    let write_fd = unsafe { OwnedFd::from_raw_fd(fds[1]) };
    let inherited_write_fd = unsafe { libc::fcntl(write_fd.as_raw_fd(), libc::F_DUPFD, MIN_EXECUTION_READY_WRITE_FD) };
    if inherited_write_fd < 0 {
        return Err(format!(
            "duplicate {} writer: {}",
            FZ_EXEC_READY_FD_ENV,
            Error::last_os_error()
        ));
    }
    let write_fd = unsafe { OwnedFd::from_raw_fd(inherited_write_fd) };
    let flags = unsafe { libc::fcntl(read_fd.as_raw_fd(), libc::F_GETFL) };
    if flags < 0 {
        return Err(format!("fcntl {}: {}", FZ_EXEC_READY_FD_ENV, Error::last_os_error()));
    }
    let rc = unsafe { libc::fcntl(read_fd.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) };
    if rc != 0 {
        return Err(format!(
            "fcntl nonblock {}: {}",
            FZ_EXEC_READY_FD_ENV,
            Error::last_os_error()
        ));
    }
    Ok((read_fd, write_fd))
}

#[derive(Clone, Copy)]
enum ReadyWriterAction {
    Inherit,
    CloseBeforeExec,
    SignalBeforeExec,
}

fn configure_ready_writer(cmd: &mut Command, fd: RawFd, action: ReadyWriterAction) {
    if matches!(action, ReadyWriterAction::Inherit) {
        return;
    }
    unsafe {
        cmd.pre_exec(move || {
            if matches!(action, ReadyWriterAction::SignalBeforeExec) {
                let byte = [1_u8];
                if libc::write(fd, byte.as_ptr().cast(), byte.len()) != 1 {
                    return Err(Error::last_os_error());
                }
            }
            if libc::close(fd) != 0 {
                return Err(Error::last_os_error());
            }
            Ok(())
        });
    }
}

fn read_execution_ready(fd: &OwnedFd) -> Result<ExecutionReady, String> {
    let mut byte = [0_u8];
    let n = unsafe { libc::read(fd.as_raw_fd(), byte.as_mut_ptr().cast(), byte.len()) };
    if n > 0 {
        return Ok(ExecutionReady::Ready);
    }
    if n == 0 {
        return Ok(ExecutionReady::Closed);
    }
    let err = Error::last_os_error();
    match err.raw_os_error() {
        Some(code) if code == libc::EAGAIN || code == libc::EINTR => Ok(ExecutionReady::Pending),
        _ => Err(format!("read {}: {}", FZ_EXEC_READY_FD_ENV, err)),
    }
}

fn fixture_command_output(
    cmd: &mut Command,
    label: &str,
    boundary: ExecutionBoundary,
    timeout: Duration,
) -> Result<Output, String> {
    fixture_command_output_with_ready_writer_action(
        cmd,
        label,
        boundary,
        ChildLimit::of_cpu(timeout),
        ReadyWriterAction::Inherit,
    )
}

fn fixture_command_output_with_ready_writer_action(
    cmd: &mut Command,
    label: &str,
    boundary: ExecutionBoundary,
    limit: ChildLimit,
    ready_writer_action: ReadyWriterAction,
) -> Result<Output, String> {
    guarded_fixture_command(cmd, label, boundary, default_child_limit(), limit, ready_writer_action)
        .map(|finished| finished.output)
}

fn guarded_fixture_command(
    cmd: &mut Command,
    label: &str,
    boundary: ExecutionBoundary,
    setup_limit: ChildLimit,
    execution_limit: ChildLimit,
    ready_writer_action: ReadyWriterAction,
) -> Result<GuardedOutput, String> {
    let ready_pipe = match boundary {
        ExecutionBoundary::Spawn => None,
        ExecutionBoundary::Announced | ExecutionBoundary::Refused => Some(execution_ready_pipe()?),
    };
    if let Some((_read_fd, write_fd)) = ready_pipe.as_ref() {
        cmd.env(FZ_EXEC_READY_FD_ENV, write_fd.as_raw_fd().to_string());
        configure_ready_writer(cmd, write_fd.as_raw_fd(), ready_writer_action);
    }
    let working_dir = FixtureWorkingDir::new()?;
    cmd.current_dir(&working_dir.path);
    let capture = CommandCapture::new()?;
    let (stdout, stderr) = capture.stdio()?;
    cmd.process_group(0);
    let spawned = cmd.stdout(stdout).stderr(stderr).spawn();
    let ready_read_fd = ready_pipe.map(|(read_fd, _write_fd)| read_fd);
    let child = spawned.map_err(|error| format!("spawn {}: {}", label, error))?;
    wait_fixture_command(
        FixtureProcess { child, capture },
        ready_read_fd,
        label,
        boundary,
        setup_limit,
        execution_limit,
    )
}

fn wait_fixture_command(
    process: FixtureProcess,
    mut ready_read_fd: Option<OwnedFd>,
    label: &str,
    boundary: ExecutionBoundary,
    setup_limit: ChildLimit,
    execution_limit: ChildLimit,
) -> Result<GuardedOutput, String> {
    let spawned_at = Instant::now();
    let mut process = WatchedProcess::start(process, label)?;
    let mut execution = execution_start(boundary, spawned_at).map(|started| Window::open(started, Duration::ZERO));
    let mut setup = Window::open(spawned_at, Duration::ZERO);
    let mut execution_ready_count = 0;
    loop {
        let (window, limit) = active_window(&mut execution, &mut setup, execution_limit, setup_limit);
        // The one wait: until the child exits, a readiness byte arrives, the
        // next CPU reading is due, or the wall ceiling passes.
        let wake = (Instant::now() + SAMPLE_INTERVAL).min(window.started() + limit.wall_ceiling());
        let exited = process.wait_for_activity(ready_read_fd.as_ref(), wake);
        // Observe exit before draining: an exited child's final ready byte is
        // already in the pipe, even if it arrived after the previous drain.
        let status = if exited { Some(process.exit_status()) } else { None };
        while let Some(read_fd) = ready_read_fd.as_ref() {
            match read_execution_ready(read_fd) {
                Ok(ExecutionReady::Ready) => {
                    // Every announcement starts an execution window: a command
                    // that runs several programs in turn gives each its own,
                    // charged from the CPU the group had spent by then.
                    execution_ready_count += 1;
                    match process.cpu_time() {
                        Ok(group_cpu) => execution = Some(Window::open(Instant::now(), group_cpu)),
                        Err(error) => return Err(process.fail(label, error)),
                    }
                }
                Ok(ExecutionReady::Pending) => break,
                Ok(ExecutionReady::Closed) => {
                    ready_read_fd = None;
                }
                Err(error) => {
                    return Err(process.fail(label, error));
                }
            }
        }
        match fixture_command_state(boundary, execution_ready_count, status) {
            FixtureCommandState::BoundaryFailed(finding) => {
                let output = process.finish(label)?;
                return Err(format!(
                    "{} {}; stderr: {}",
                    label,
                    finding,
                    String::from_utf8_lossy(&output.stderr).trim_end()
                ));
            }
            FixtureCommandState::Exited => {
                let output = process.finish(label)?;
                return Ok(GuardedOutput {
                    output,
                    execution_ready_count,
                });
            }
            FixtureCommandState::Running => {
                let (window, limit) = active_window(&mut execution, &mut setup, execution_limit, setup_limit);
                let group_cpu = match process.cpu_time() {
                    Ok(group_cpu) => group_cpu,
                    Err(error) => return Err(process.fail(label, error)),
                };
                if let Some(exceeded) = limit.exceeded(window.charge(group_cpu)) {
                    let output = process.finish(label)?;
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    let stderr = stderr.trim_end();
                    return Err(if execution.is_some() {
                        format!("{label} exceeded {exceeded}; stderr: {stderr}")
                    } else {
                        format!("{label} did not signal execution ready within {exceeded}; stderr: {stderr}")
                    });
                }
            }
        }
    }
}

/// The window and limit now in force: the execution window once a program has
/// started, the setup window before.
fn active_window<'a>(
    execution: &'a mut Option<Window>,
    setup: &'a mut Window,
    execution_limit: ChildLimit,
    setup_limit: ChildLimit,
) -> (&'a mut Window, ChildLimit) {
    match execution {
        Some(window) => (window, execution_limit),
        None => (setup, setup_limit),
    }
}

/// The command a fixture check spawned, with its capture, as the caller hands
/// it to `wait_fixture_command`.
struct FixtureProcess {
    child: Child,
    capture: CommandCapture,
}

/// A spawned command whose exit is delivered by a waiter thread that owns the
/// `Child`: the thread blocks in `wait()`, sends the status, then writes one
/// byte to `exit_wake`, so the caller can sleep in `poll(2)` on the exit and on
/// the readiness pipe together.
struct WatchedProcess {
    pid: libc::pid_t,
    exit_receiver: mpsc::Receiver<ExitStatus>,
    exit_wake: OwnedFd,
    exited: Option<ExitStatus>,
    capture: CommandCapture,
}

impl WatchedProcess {
    fn start(process: FixtureProcess, label: &str) -> Result<Self, String> {
        let FixtureProcess { mut child, capture } = process;
        let pid = child.id() as libc::pid_t;
        let mut fds = [0; 2];
        if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
            let error = format!("pipe exit wake for {label}: {}", Error::last_os_error());
            return Err(FixtureProcess { child, capture }.abandon(label, error));
        }
        let wake_read = unsafe { OwnedFd::from_raw_fd(fds[0]) };
        let wake_write = unsafe { OwnedFd::from_raw_fd(fds[1]) };
        let (sender, exit_receiver) = mpsc::channel();
        let waiter_label = label.to_string();
        std::thread::spawn(move || {
            let status = wait_child(&mut child, &waiter_label);
            let _ = sender.send(status);
            let byte = [1_u8];
            unsafe { libc::write(wake_write.as_raw_fd(), byte.as_ptr().cast(), byte.len()) };
        });
        Ok(Self {
            pid,
            exit_receiver,
            exit_wake: wake_read,
            exited: None,
            capture,
        })
    }

    /// Blocks until the child has exited, a readiness byte can be read, or
    /// `deadline` passes, and says whether the child has exited.
    fn wait_for_activity(&self, ready: Option<&OwnedFd>, deadline: Instant) -> bool {
        let mut fds = vec![libc::pollfd {
            fd: self.exit_wake.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        }];
        if let Some(ready) = ready {
            fds.push(libc::pollfd {
                fd: ready.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            });
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        let millis = remaining.as_millis().saturating_add(1).min(i32::MAX as u128) as i32;
        unsafe { libc::poll(fds.as_mut_ptr(), fds.len() as libc::nfds_t, millis) };
        fds[0].revents & libc::POLLIN != 0
    }

    /// The CPU the child's process group has spent so far.
    fn cpu_time(&self) -> Result<Duration, String> {
        group_cpu_time(self.pid)
    }

    /// The status of the child, which has exited.
    fn exit_status(&mut self) -> ExitStatus {
        *self.exited.get_or_insert_with(|| {
            self.exit_receiver
                .recv()
                .expect("the waiter thread delivers the exit status")
        })
    }

    /// Whether the waiter thread has already delivered the exit status.
    fn has_exited(&mut self) -> bool {
        if self.exited.is_none() {
            self.exited = self.exit_receiver.try_recv().ok();
        }
        self.exited.is_some()
    }

    fn finish(mut self, label: &str) -> Result<Output, String> {
        let already_reaped = self.has_exited();
        let group_error = if already_reaped {
            None
        } else {
            kill_process_group(self.pid).err()
        };
        if group_error.is_some()
            && let Err(direct_error) = kill_pid(self.pid)
            && direct_error.raw_os_error() != Some(libc::ESRCH)
        {
            // This is our direct child and the harness does not change credentials.
            // If it is still live after both SIGKILL attempts fail, waiting would
            // hang and returning would silently detach a process the harness owns.
            panic!("owned child stayed live after group and direct kill failed: {direct_error}");
        }
        let status = self.exit_status();
        if let Some(error) = group_error {
            return Err(format!("teardown {label}: {error}; leader reaped as {status}"));
        }
        self.capture.output(status)
    }

    fn fail(self, label: &str, message: String) -> String {
        match self.finish(label) {
            Ok(_) => message,
            Err(error) => format!("{message}; {error}"),
        }
    }
}

impl FixtureProcess {
    /// Kill and reap a command that never reached a waiter.
    fn abandon(mut self, label: &str, message: String) -> String {
        let _ = kill_process_group(self.child.id() as libc::pid_t);
        let _ = self.child.kill();
        wait_child(&mut self.child, label);
        message
    }
}

fn wait_child(child: &mut Child, label: &str) -> ExitStatus {
    loop {
        match child.wait() {
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Ok(status) => return status,
            Err(wait_error) => match child.try_wait() {
                Ok(Some(status)) => return status,
                Ok(None) => panic!("wait {label} failed while owned child stayed live: {wait_error}"),
                Err(poll_error) => panic!("cannot prove {label} reaped after wait failed: {wait_error}; {poll_error}"),
            },
        }
    }
}

fn kill_pid(pid: libc::pid_t) -> std::io::Result<()> {
    loop {
        if unsafe { libc::kill(pid, libc::SIGKILL) } == 0 {
            return Ok(());
        }
        let error = Error::last_os_error();
        if error.raw_os_error() != Some(libc::EINTR) {
            return Err(error);
        }
    }
}

fn kill_process_group(leader: libc::pid_t) -> Result<(), String> {
    let process_group = -leader;
    loop {
        if unsafe { libc::kill(process_group, libc::SIGKILL) } == 0 {
            return Ok(());
        }
        let error = Error::last_os_error();
        match error.raw_os_error() {
            Some(libc::EINTR) => continue,
            Some(libc::ESRCH) => return Ok(()),
            _ => return Err(format!("kill process group {leader}: {error}")),
        }
    }
}

fn fixture_hang_guard_policy() {
    assert_eq!(
        DEFAULT_FIXTURE_CPU_LIMIT,
        Duration::from_secs(20),
        "the default CPU limit is the CI-proven nontermination backstop, not a performance stopwatch"
    );
    let now = Instant::now();
    assert_eq!(
        execution_start(ExecutionBoundary::Announced, now),
        None,
        "pre-execution work must not arm the execution limit"
    );
    assert_eq!(
        execution_start(ExecutionBoundary::Refused, now),
        None,
        "a compile that must be refused is setup work from start to finish"
    );
    assert_eq!(
        execution_start(ExecutionBoundary::Spawn, now),
        Some(now),
        "a spawn-timed command arms its execution guard immediately"
    );
}

fn execution_ready_writer_uses_multi_digit_descriptor() {
    let (_read_fd, write_fd) = execution_ready_pipe().expect("create readiness pipe");
    assert!(write_fd.as_raw_fd() >= MIN_EXECUTION_READY_WRITE_FD);
}

fn fixture_command_capture_does_not_wait_for_an_open_writer() {
    let capture = CommandCapture::new().expect("create anonymous regular-file capture");
    let mut writer = capture.stdout.try_clone().expect("clone capture writer");
    writer.write_all(b"bounded snapshot").expect("write snapshot");

    let out = capture.output(ExitStatus::from_raw(0)).expect("read bounded snapshot");
    assert!(out.status.success());
    assert_eq!(out.stdout, b"bounded snapshot");
    assert!(out.stderr.is_empty());
    writer.write_all(b" after return").expect("writer remains open");
}

fn fixture_command_rejects_missing_readiness() {
    let error = fixture_command_output_with_ready_writer_action(
        Command::new("sh").args(["-c", "sleep 2"]),
        "unannounced command",
        ExecutionBoundary::Announced,
        default_child_limit(),
        ReadyWriterAction::CloseBeforeExec,
    )
    .expect_err("a command that ends without starting a program must be reported");
    assert_eq!(
        error,
        "unannounced command never started a program (0 readiness bytes); stderr: "
    );

    let error = fixture_command_output(
        Command::new("sh").args(["-c", "sleep 2 &"]),
        "pre-ready leader",
        ExecutionBoundary::Announced,
        DEFAULT_FIXTURE_CPU_LIMIT,
    )
    .expect_err("an inherited writer must not conceal a leader that starts no program");
    assert_eq!(
        error,
        "pre-ready leader never started a program (0 readiness bytes); stderr: "
    );

    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let pid_path = temp_dir().join(format!("fz_setup_hang_{}_{}.pid", id(), nonce));
    let error = guarded_fixture_command(
        Command::new("sh")
            .env("FZ_SETUP_HANG_PID_PATH", &pid_path)
            .args(["-c", "printf %s $$ > \"$FZ_SETUP_HANG_PID_PATH\"; sleep 2"]),
        "setup-hung fixture",
        ExecutionBoundary::Announced,
        ChildLimit::new(Duration::from_secs(1), Duration::from_secs(1)),
        default_child_limit(),
        ReadyWriterAction::Inherit,
    )
    .expect_err("a live command that never signals readiness must hit the setup guard");
    assert_eq!(
        error,
        "setup-hung fixture did not signal execution ready within the 1s wall ceiling (CPU 0.0s); stderr: "
    );
    assert_reaped(read_pid(&pid_path));
    let _ = fs::remove_file(pid_path);
}

/// The fixture's expectation, not the exit status, says whether a program had
/// to run. An `expect: abort` program exits nonzero after running, so a
/// nonzero exit can never stand in for the boundary; an `expect: diagnostic`
/// source must be refused before any program starts, so a byte from one means
/// the compiler accepted what it was told to reject.
fn fixture_command_verdict_follows_the_fixture_expectation() {
    let probe = |code: i32| {
        let mut command = Command::new("sh");
        command.args([
            "-c",
            "printf 'probe diagnostic\\n' >&2; exit \"$1\"",
            "verdict probe",
            &code.to_string(),
        ]);
        command
    };

    let error = fixture_command_output_with_ready_writer_action(
        &mut probe(7),
        "aborting program",
        ExecutionBoundary::Announced,
        default_child_limit(),
        ReadyWriterAction::Inherit,
    )
    .expect_err("a nonzero exit does not excuse a program that never started");
    assert_eq!(
        error,
        "aborting program never started a program (0 readiness bytes); stderr: probe diagnostic"
    );

    let finished = fixture_command_output_with_ready_writer_action(
        &mut probe(7),
        "refused source",
        ExecutionBoundary::Refused,
        default_child_limit(),
        ReadyWriterAction::Inherit,
    )
    .expect("a refused source starts no program, and its diagnostic is the answer");
    assert_eq!(finished.status.code(), Some(7));
    assert_eq!(finished.stderr, b"probe diagnostic\n");

    let error = fixture_command_output_with_ready_writer_action(
        &mut probe(0),
        "refused source",
        ExecutionBoundary::Refused,
        default_child_limit(),
        ReadyWriterAction::SignalBeforeExec,
    )
    .expect_err("a program that starts under a refusal expectation is the finding");
    assert_eq!(
        error,
        "refused source started a program (1 readiness bytes) though the fixture declares the compiler must refuse it; stderr: probe diagnostic"
    );
}

fn fixture_readiness_eof_before_exit() {
    assert_missing_readiness_observation_order(false);
}

fn fixture_readiness_exit_before_eof() {
    assert_missing_readiness_observation_order(true);
}

fn fixture_readiness_drains_an_exited_child() {
    for exit_code in [0, 7] {
        let (read_fd, write_fd) = execution_ready_pipe().expect("create readiness pipe");
        let capture = CommandCapture::new().expect("create command capture");
        let (stdout, stderr) = capture.stdio().expect("capture child output");
        let mut command = Command::new("sh");
        command
            .args([
                "-c",
                "printf 'child diagnostic\\n' >&2; exit \"$1\"",
                "readiness probe",
                &exit_code.to_string(),
            ])
            .stdout(stdout)
            .stderr(stderr)
            .process_group(0);
        configure_ready_writer(&mut command, write_fd.as_raw_fd(), ReadyWriterAction::SignalBeforeExec);
        let mut child = command.spawn().expect("spawn exited readiness probe");
        let pid = child.id() as libc::pid_t;
        drop(write_fd);
        assert_eq!(
            child.wait().expect("exit before reading readiness").code(),
            Some(exit_code)
        );
        let result = wait_fixture_command(
            FixtureProcess { child, capture },
            Some(read_fd),
            "exited readiness probe",
            ExecutionBoundary::Announced,
            default_child_limit(),
            default_child_limit(),
        );
        assert_reaped(pid);
        // An exited child's buffered byte is drained and counted before its
        // status is classified, so a program that announced itself and then
        // exited — successfully or not — is judged on its own terms.
        let finished = result.expect("consume the exited child's buffered signal before judging its status");
        assert_eq!(finished.execution_ready_count, 1);
        assert_eq!(finished.output.status.code(), Some(exit_code));
        assert_eq!(finished.output.stderr, b"child diagnostic\n");
    }
}

fn assert_missing_readiness_observation_order(exit_first: bool) {
    let (read_fd, write_fd) = execution_ready_pipe().expect("create readiness pipe");
    let capture = CommandCapture::new().expect("create command capture");
    let (stdout, stderr) = capture.stdio().expect("capture child output");
    let mut command = Command::new("sh");
    command
        .args(["-c", "printf 'setup diagnostic\\n' >&2; read release; exit 0"])
        .stdin(Stdio::piped())
        .stdout(stdout)
        .stderr(stderr)
        .process_group(0);
    configure_ready_writer(&mut command, write_fd.as_raw_fd(), ReadyWriterAction::CloseBeforeExec);
    let mut child = command.spawn().expect("spawn readiness observation probe");
    let pid = child.id() as libc::pid_t;
    drop(write_fd);
    if !exit_first {
        let mut ready = libc::pollfd {
            fd: read_fd.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        assert_eq!(unsafe { libc::poll(&mut ready, 1, 20_000) }, 1);
        assert_eq!(ready.revents & libc::POLLHUP, libc::POLLHUP);
        assert!(
            child
                .try_wait()
                .expect("observe child blocked on control pipe")
                .is_none()
        );
        assert_eq!(
            fixture_command_state(ExecutionBoundary::Announced, 0, None),
            FixtureCommandState::Running,
            "a closed readiness pipe is not a verdict on its own: the exit status decides"
        );
    }
    child
        .stdin
        .take()
        .expect("child control pipe")
        .write_all(b"exit\n")
        .unwrap();
    assert!(child.wait().expect("observe child exit").success());
    assert_ne!(
        capture.stderr.metadata().expect("inspect captured diagnostics").len(),
        0,
        "the probe writes its diagnostic before it exits, and its exit has been observed"
    );
    assert_eq!(
        fixture_command_state(
            ExecutionBoundary::Announced,
            0,
            child.try_wait().expect("observe child status")
        ),
        FixtureCommandState::BoundaryFailed("never started a program (0 readiness bytes)".to_string()),
        "an exit with no boundary is the same verdict whichever observation lands first"
    );
    let error = wait_fixture_command(
        FixtureProcess { child, capture },
        Some(read_fd),
        "missing readiness probe",
        ExecutionBoundary::Announced,
        default_child_limit(),
        default_child_limit(),
    )
    .expect_err("both observation orders reject the same missing boundary");
    assert_reaped(pid);
    assert_eq!(
        error,
        "missing readiness probe never started a program (0 readiness bytes); stderr: setup diagnostic"
    );
}

fn read_pid(path: &Path) -> libc::pid_t {
    fs::read_to_string(path)
        .expect("read child pid")
        .parse()
        .expect("parse child pid")
}

fn assert_reaped(pid: libc::pid_t) {
    assert_eq!(unsafe { libc::kill(pid, 0) }, -1);
    assert_eq!(Error::last_os_error().raw_os_error(), Some(libc::ESRCH));
}

/// Every program that starts announces its own boundary. `fz2 test` starts one
/// per test, in a child process that inherits the readiness descriptor and
/// reaches the same seam, so a two-test fixture produces two bytes and the
/// discovering parent contributes none. A `run-test-root` invoked directly is
/// one program and produces one.
fn kind_test_commands_signal_execution_ready_per_test() {
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let fixture = temp_dir().join(format!("fz_kind_test_ready_{}_{}.fz", id(), nonce));
    fs::write(
        &fixture,
        "#---\n# purpose: readiness probe\n# kind: test\n#---\ntest(:passes, do: true || raise(\"expected true\"))\ntest(:also_passes, do: true || raise(\"expected true\"))\n",
    )
    .expect("write kind:test readiness probe");

    for interp in [false, true] {
        let mut command = Command::new(FZ2_BIN);
        command.arg("test");
        if interp {
            command.arg("--interp");
        }
        command.arg(&fixture);
        assert_execution_ready_count(&mut command, "fz2 test", 2);
    }

    for interp in [false, true] {
        let mut command = Command::new(FZ2_BIN);
        command.arg("run-test-root").arg(&fixture).args(["-", "passes"]);
        if interp {
            command.arg("--interp");
        }
        assert_execution_ready_count(&mut command, "fz2 run-test-root", 1);
    }

    let _ = fs::remove_file(fixture);
}

fn assert_execution_ready_count(command: &mut Command, label: &str, expected: usize) {
    let finished = guarded_fixture_command(
        command,
        label,
        ExecutionBoundary::Announced,
        default_child_limit(),
        default_child_limit(),
        ReadyWriterAction::Inherit,
    )
    .unwrap_or_else(|error| panic!("run `{label}` readiness probe: {error}"));
    assert!(finished.output.status.success());
    assert_eq!(finished.execution_ready_count, expected);
}

/// The execution guard measures the program, not the compiler that produced it.
/// `json_roundtrip` compiles for seconds and then runs in about thirty
/// milliseconds, so a two-second execution window fits the program many times
/// over while the compile alone would blow it: the lane can only go red if the
/// readiness byte is written before a compile that takes longer than two
/// seconds. A faster machine shortens the compile and the program alike, so the
/// trial never flips green to red on better hardware -- it only loses
/// discrimination. The compile itself stays under the usual setup guard.
fn execution_guard_covers_the_program_not_the_compile() {
    let fixture = absolute(Path::new("fixtures/01521_json_roundtrip.fz"));
    for door in ["run", "interp"] {
        let label = format!("fz2 {door}");
        let finished = guarded_fixture_command(
            Command::new(FZ2_BIN).arg(door).arg(&fixture),
            &label,
            ExecutionBoundary::Announced,
            default_child_limit(),
            ChildLimit::of_cpu(Duration::from_secs(2)),
            ReadyWriterAction::Inherit,
        )
        .unwrap_or_else(|error| panic!("the program runs well inside a two-second window: {error}"));
        assert!(finished.output.status.success(), "{label} must succeed");
        assert_eq!(finished.execution_ready_count, 1);
    }
}

fn kind_test_timeouts_kill_the_outer_command_and_its_hung_root() {
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let fixture = temp_dir().join(format!("fz_kind_test_hang_{}_{}.fz", id(), nonce));
    fs::write(
        &fixture,
        "#---\n# purpose: timeout probe\n# kind: test\n#---\ntest(:hangs, do: loop())\ndef loop(), do: loop()\n",
    )
    .expect("write kind:test timeout probe");

    for args in [&["test"][..], &["test", "--interp"][..]] {
        let label = format!("fz2 {}", args.join(" "));
        let error = fixture_command_output(
            Command::new(FZ2_BIN).args(args).arg(&fixture),
            &label,
            ExecutionBoundary::Announced,
            Duration::from_secs(1),
        )
        .expect_err("a kind:test root that never returns must time out");
        assert!(
            error.starts_with(&format!("{label} exceeded 1s of CPU (wall ")),
            "a root that spins is charged its CPU: {error}"
        );
    }

    let _ = fs::remove_file(fixture);
}

fn build_output_owner_cleans_timeout_and_error_paths() {
    let path = temp_build_output_path("owner_timeout");
    let timeout = with_fz2_build_outputs(path.clone(), |out_path| {
        seed_fz2_build_outputs(out_path);
        fixture_command_output(
            Command::new("sh").args(["-c", "sleep 2"]),
            "timed-out build probe",
            ExecutionBoundary::Spawn,
            Duration::from_millis(20),
        )
    });
    assert!(
        timeout
            .unwrap_err()
            .contains("exceeded the 200ms wall ceiling (CPU 0.0s)")
    );
    assert_fz2_build_outputs_absent(&path);

    let path = temp_build_output_path("owner_error");
    let error = with_fz2_build_outputs(path.clone(), |out_path| {
        seed_fz2_build_outputs(out_path);
        Err::<(), _>("build failed")
    });
    assert_eq!(error, Err("build failed"));
    assert_fz2_build_outputs_absent(&path);
}

fn diagnostic_build_path_cleans_every_output() {
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let fixture_path = temp_dir().join(format!("fz_diagnostic_cleanup_{}_{}.fz", id(), nonce));
    fs::write(
        &fixture_path,
        "#---\n# purpose: diagnostic cleanup probe\n# expect: diagnostic\n# diagnostic.code: probe/unexpected\n#---\ndef main(), do: 0\n",
    )
    .expect("write diagnostic cleanup fixture");
    let fixture = FixtureCase::new(fixture_path.clone());
    let header = parse_header(&fixture).expect("parse diagnostic cleanup fixture");
    let out_path = temp_build_output_path("diagnostic");
    let outcome = run_fz2_build_path_to(&fixture, &header, out_path.clone());
    assert!(
        matches!(&outcome, RunOutcome::Ran(ran) if ran.status.success()),
        "the deliberately valid diagnostic fixture must exercise unexpected build success"
    );
    assert_fz2_build_outputs_absent(&out_path);
    let _ = fs::remove_file(fixture_path);
}

fn temp_build_output_path(label: &str) -> PathBuf {
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    temp_dir().join(format!("fz2_matrix_{label}_{}_{}", id(), nonce))
}

fn seed_fz2_build_outputs(out_path: &Path) {
    for path in [
        out_path.to_path_buf(),
        out_path.with_extension("o"),
        out_path.with_extension("bin.o"),
    ] {
        fs::write(path, b"partial build output").expect("seed partial build output");
    }
}

fn assert_fz2_build_outputs_absent(out_path: &Path) {
    for path in [
        out_path.to_path_buf(),
        out_path.with_extension("o"),
        out_path.with_extension("bin.o"),
    ] {
        assert!(!path.exists(), "build output leaked: {}", path.display());
    }
}

fn run_path(fixture: &FixtureCase, header: &Header, path: FixtureMatrixPath) -> RunOutcome {
    // `kind: test` fixtures always go through the `fz2 test` discovery/report
    // front door, on whichever backend the path names (JIT for `run`, the
    // backend interpreter for `interp` via `--interp`) — there is no `kind:
    // test` equivalent of a bare `fz2 interp`, since a test fixture has no
    // `main/0` for that command to seed.
    let args: &[&str] = match (path, header.kind) {
        (FixtureMatrixPath::Run, Kind::Run) => &["run"],
        (FixtureMatrixPath::Run, Kind::Test) => &["test"],
        (FixtureMatrixPath::Interp, Kind::Test) => &["test", "--interp"],
        (FixtureMatrixPath::Interp, Kind::Run) => &["interp"],
        (FixtureMatrixPath::Build, _) => return run_fz2_build_path(fixture, header),
    };
    let input = fixture.source_path();
    let out = match fixture_command_output(
        Command::new(FZ2_BIN).args(args).arg(&input).args(program_args(header)),
        "fz2",
        header.execution_boundary(),
        header.timeout_for_path(path),
    ) {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(e),
    };
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    RunOutcome::Ran(Ran {
        status: out.status,
        stdout: String::from_utf8_lossy(&out.stdout).to_string(),
        diagnostics: stderr,
    })
}

/// What follows the source path of `fz2 run|interp`: the fixture's `args:`.
/// A `kind: test` fixture runs through `fz2 test`, which takes none.
fn program_args(header: &Header) -> &[String] {
    match header.kind {
        Kind::Run => &header.args,
        Kind::Test => &[],
    }
}

fn run_fz2_build_path(fixture: &FixtureCase, header: &Header) -> RunOutcome {
    if header.kind == Kind::Test {
        return RunOutcome::Deferred("kind: test fixtures don't yet run via build".into());
    }
    let stem = fixture.name();
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let out_path = temp_dir().join(format!("fz2_matrix_{}_{}_{}", stem, id(), nonce));
    run_fz2_build_path_to(fixture, header, out_path)
}

fn run_fz2_build_path_to(fixture: &FixtureCase, header: &Header, out_path: PathBuf) -> RunOutcome {
    with_fz2_build_outputs(out_path, |out_path| run_fz2_build_path_owned(fixture, header, out_path))
}

fn run_fz2_build_path_owned(fixture: &FixtureCase, header: &Header, out_path: &Path) -> RunOutcome {
    let input = fixture.source_path();
    let build = match fixture_command_output(
        Command::new(FZ2_BIN)
            .args(["build"])
            .arg(&input)
            .args(["-o"])
            .arg(out_path),
        "fz2 build",
        ExecutionBoundary::Spawn,
        DEFAULT_FIXTURE_CPU_LIMIT,
    ) {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(e),
    };
    let build_stderr = String::from_utf8_lossy(&build.stderr).to_string();
    if header.expect == Expect::Diagnostic {
        return RunOutcome::Ran(Ran {
            status: build.status,
            stdout: String::from_utf8_lossy(&build.stdout).to_string(),
            diagnostics: build_stderr,
        });
    }
    if !build.status.success() {
        return RunOutcome::Failed(format!("fz2 build exit {}: {}", build.status, build_stderr.trim_end()));
    }
    let run = match fixture_command_output(
        Command::new(out_path).args(&header.args),
        "fz2-built binary",
        ExecutionBoundary::Spawn,
        header.timeout_for_path(FixtureMatrixPath::Build),
    ) {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(e),
    };
    let run_stderr = String::from_utf8_lossy(&run.stderr).to_string();
    let diagnostics = format!("{}{}", build_stderr, run_stderr);
    // Code that runs while a module is defined prints during the build, and
    // the rest prints from the binary: together they are what the program
    // says.
    let stdout = format!(
        "{}{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&run.stdout)
    );
    RunOutcome::Ran(Ran {
        status: run.status,
        stdout,
        diagnostics,
    })
}

struct Fz2BuildOutputs {
    out_path: PathBuf,
}

impl Fz2BuildOutputs {
    fn new(out_path: PathBuf) -> Self {
        Self { out_path }
    }

    fn path(&self) -> &Path {
        &self.out_path
    }
}

impl Drop for Fz2BuildOutputs {
    fn drop(&mut self) {
        remove_fz2_build_outputs(self.path());
    }
}

fn with_fz2_build_outputs<T>(out_path: PathBuf, run: impl FnOnce(&Path) -> T) -> T {
    let outputs = Fz2BuildOutputs::new(out_path);
    run(outputs.path())
}

fn remove_fz2_build_outputs(out_path: &Path) {
    let _ = remove_file(out_path);
    let _ = remove_file(out_path.with_extension("o"));
    let _ = remove_file(out_path.with_extension("bin.o"));
}

fn normalize(s: &str) -> String {
    let normalized = canonicalize_closure_denotations(s);
    if normalized.is_empty() || normalized.ends_with('\n') {
        normalized
    } else {
        format!("{normalized}\n")
    }
}

/// The runtime's closure denotation is a process-local allocation index. It
/// makes a useful opaque identity while a program is running, but unrelated
/// source (such as another runtime module) can change it. Fixture output pins
/// the stable rendered shape and declared arity instead.
fn canonicalize_closure_denotations(text: &str) -> String {
    let mut normalized = String::with_capacity(text.len());
    let mut cursor = 0;
    while cursor < text.len() {
        let rest = &text[cursor..];
        if rest.starts_with("#fn<") {
            let denotation_start = cursor + "#fn<".len();
            let denotation_end = take_ascii_digits(text.as_bytes(), denotation_start);
            if denotation_end > denotation_start && text.as_bytes().get(denotation_end) == Some(&b'/') {
                normalized.push_str(&text[cursor..denotation_start]);
                normalized.push_str("id");
                cursor = denotation_end;
                continue;
            }
        }
        let next = rest.chars().next().expect("cursor remains at a character boundary");
        normalized.push(next);
        cursor += next.len_utf8();
    }
    normalized
}

fn fixture_output_canonicalizes_closure_denotations() {
    assert_eq!(
        normalize("#fn<111/0>\n#fn<112/2>"),
        "#fn<id/0>\n#fn<id/2>\n",
        "fixture output must retain a closure's rendered form and arity without pinning its minted identity",
    );
    assert_eq!(
        normalize("#fn<id/0>\n#fn<missing slash>"),
        "#fn<id/0>\n#fn<missing slash>\n",
        "only a numeric denotation in the runtime closure form is canonicalized",
    );
}

/// Fixtures whose pinned contract is output + allocations, not compiled
/// call-graph shape. `reductions_remaining` is charged per back-edge
/// yield-check that native codegen emits for a Tarjan SCC pass over the
/// fully-specialized call graph (native_codegen/terminator.rs), so it drifts
/// on any refactor that reshapes specialization even when output and every
/// allocation counter stay byte-identical (see fz-myo). append/quicksort/
/// reverse are closure-free, protocol-free recursive fixtures that isolate
/// that shape churn as a canary rather than exercising a real allocation
/// contract on the counter, so the strict compare excludes it here while
/// every other fixture keeps it pinned exactly.
const SHAPE_ONLY_REDUCTION_FIXTURES: &[&str] = &["append", "quicksort", "reverse"];

/// Blank out the `:reductions_remaining => N` value so the strict stdout
/// compare ignores codegen-shape drift on that single counter. The golden and
/// the freshly-run output both keep printing the real number — this only
/// changes what the equality check looks at, so the counter stays fully
/// visible for manual inspection and `BLESS=1` still records the live value.
fn mask_reductions_remaining(text: &str) -> String {
    const KEY: &str = ":reductions_remaining => ";
    let Some(key_start) = text.find(KEY) else {
        return text.to_string();
    };
    let value_start = key_start + KEY.len();
    let value_end = text[value_start..]
        .find(|c: char| !c.is_ascii_digit())
        .map(|offset| value_start + offset)
        .unwrap_or(text.len());
    format!("{}<masked>{}", &text[..value_start], &text[value_end..])
}

#[derive(Debug)]
enum CheckOutcome {
    /// Real pass against the .expected sidecar.
    Pass,
    /// Path is declared but not yet wired (subcommand returned exit 75).
    /// Surfaced in the test output but doesn't fail.
    Deferred(String),
    /// Mismatch or fatal error.
    Fail(String),
}

fn check(fixture: &FixtureCase, header: &Header, path: FixtureMatrixPath, bless: bool) -> CheckOutcome {
    let ran = match run_path(fixture, header, path) {
        RunOutcome::Ran(ran) => ran,
        RunOutcome::Deferred(msg) => return CheckOutcome::Deferred(msg),
        RunOutcome::Failed(e) => return CheckOutcome::Fail(e),
    };
    match header.expect {
        Expect::Success => check_success(fixture, path, bless, &ran, header.oracle.is_some()),
        Expect::Abort => check_failure(fixture, header, "abort", path, bless, &ran),
        Expect::Diagnostic => check_failure(fixture, header, "diagnostic", path, bless, &ran),
    }
}

/// `expect: success` (the default): the program must exit 0, and its stdout and
/// diagnostics must match their goldens (absent golden ⇒ expected empty).
fn check_success(
    fixture: &FixtureCase,
    path: FixtureMatrixPath,
    bless: bool,
    ran: &Ran,
    oracle_owned: bool,
) -> CheckOutcome {
    let path_id = path.id();
    if !ran.status.success() {
        return CheckOutcome::Fail(format!(
            "{} via {}: expected success but the program exited nonzero\n--- stderr\n{}",
            fixture.display_path().display(),
            path_id,
            fixture.normalize_actual_diagnostics(&ran.diagnostics).trim_end()
        ));
    }
    let actual = normalize(&ran.stdout);
    let actual_diagnostics = normalize(&fixture.normalize_actual_diagnostics(&ran.diagnostics));
    let path_expected_path = fixture.sidecar_path(&format!("expected.{}.txt", path_id));
    let expected_path = if path_expected_path.exists() {
        path_expected_path
    } else {
        fixture.sidecar_path("expected.txt")
    };
    let expected = fs::read_to_string(&expected_path).unwrap_or_default();
    let expected = normalize(&expected);
    let path_diagnostics_path = fixture.sidecar_path(&format!("expected.{}.diagnostics", path_id));
    let expected_diagnostics_path = if path_diagnostics_path.exists() {
        path_diagnostics_path
    } else {
        fixture.sidecar_path("expected.diagnostics")
    };
    let expected_diagnostics = normalize(
        &fixture.normalize_expected_diagnostics(&fs::read_to_string(&expected_diagnostics_path).unwrap_or_default()),
    );
    let (actual_for_compare, expected_for_compare) = if SHAPE_ONLY_REDUCTION_FIXTURES.contains(&fixture.name().as_str())
    {
        (mask_reductions_remaining(&actual), mask_reductions_remaining(&expected))
    } else {
        (actual.clone(), expected.clone())
    };
    if actual_for_compare == expected_for_compare && actual_diagnostics == expected_diagnostics {
        let _ = fs::remove_file(fixture.actual_path("txt"));
        let _ = fs::remove_file(fixture.actual_path("diagnostics"));
        return CheckOutcome::Pass;
    }
    if bless {
        // Elixir owns expected.txt for oracle fixtures — per-path bless must not
        // rewrite it, or a divergent fz path would silently redefine the golden.
        if !oracle_owned {
            if actual.is_empty() {
                let _ = fs::remove_file(&expected_path);
            } else if let Err(e) = fs::write(&expected_path, &actual) {
                return CheckOutcome::Fail(format!("bless write: {}", e));
            }
        }
        if actual_diagnostics.is_empty() {
            let _ = fs::remove_file(&expected_diagnostics_path);
        } else if let Err(e) = fs::write(&expected_diagnostics_path, &actual_diagnostics) {
            return CheckOutcome::Fail(format!("bless diagnostics write: {}", e));
        }
        return CheckOutcome::Pass;
    }
    let output_path = fixture.actual_path("txt");
    let diagnostics_output_path = fixture.actual_path("diagnostics");
    let _ = fs::write(&output_path, &actual);
    let _ = fs::write(&diagnostics_output_path, &actual_diagnostics);
    CheckOutcome::Fail(format!(
        "fixture mismatch for {} via {}; wrote {} and {}\n--- expected stdout ({})\n{}--- actual stdout\n{}--- expected diagnostics\n{}--- actual diagnostics\n{}",
        fixture.display_path().display(),
        path_id,
        output_path.display(),
        diagnostics_output_path.display(),
        expected_path.display(),
        expected,
        actual,
        expected_diagnostics,
        actual_diagnostics
    ))
}

/// `expect: abort`: the program must exit nonzero, and its stderr must
/// *contain* the `expected.stderr` golden as a substring. A
/// substring (not an exact match) is the right pin for a negative claim: the
/// stable fact is "this message appears", while the surrounding text carries
/// per-path prefixes and absolute source paths that would make an exact golden
/// brittle across the compiler2 matrix.
///
/// `expect: diagnostic` uses the same nonzero contract but, when the fixture
/// declares `diagnostic.code`, asserts the `[fz, diag, error]` telemetry event
/// instead of pinning rendered stderr.
///
/// BLESS seeds a missing `expected.stderr` with the full captured stderr so the
/// author can trim it to the stable line; it never overwrites a curated golden.
///
/// `kind` is `"abort"` or `"diagnostic"` — the failure mode named in messages.
fn check_failure(
    fixture: &FixtureCase,
    header: &Header,
    kind: &str,
    path: FixtureMatrixPath,
    bless: bool,
    ran: &Ran,
) -> CheckOutcome {
    let path_id = path.id();
    let diagnostics = fixture.normalize_actual_diagnostics(&ran.diagnostics);
    if ran.status.success() {
        return CheckOutcome::Fail(format!(
            "{} via {}: expected {} (nonzero exit) but the program exited 0",
            fixture.display_path().display(),
            path_id,
            kind
        ));
    }
    if kind == "abort" && ran.status.code() != Some(1) {
        return CheckOutcome::Fail(format!(
            "{} via {}: expected abort, a failed main process exiting 1, but the program exited {}\n--- stderr\n{}",
            fixture.display_path().display(),
            path_id,
            ran.status,
            diagnostics.trim_end()
        ));
    }
    if kind == "abort"
        && header.oracle.is_some()
        && let Some(mismatch) = abort_stdout_mismatch(fixture, path_id, ran)
    {
        return mismatch;
    }
    if kind == "diagnostic"
        && let Some(code) = &header.diagnostic_code
    {
        return check_diagnostic_telemetry(fixture, header, path, code);
    }
    let path_golden = fixture.sidecar_path(&format!("expected.{}.stderr", path_id));
    let golden_path = if path_golden.exists() {
        path_golden
    } else {
        fixture.sidecar_path("expected.stderr")
    };
    let golden = fixture.normalize_expected_diagnostics(&fs::read_to_string(&golden_path).unwrap_or_default());
    let needle = golden.trim();
    if needle.is_empty() {
        if bless {
            if let Err(e) = fs::write(&golden_path, &diagnostics) {
                return CheckOutcome::Fail(format!("bless stderr write: {}", e));
            }
            // Seeded with full stderr; the author trims to the stable claim.
            return CheckOutcome::Pass;
        }
        return CheckOutcome::Fail(format!(
            "{} via {}: expect {} but no {} golden; run BLESS=1 to seed it, then trim to the stable line\n--- stderr\n{}",
            fixture.display_path().display(),
            path_id,
            kind,
            golden_path.display(),
            diagnostics.trim_end()
        ));
    }
    if diagnostics.contains(needle) {
        let _ = fs::remove_file(fixture.actual_path("stderr"));
        return CheckOutcome::Pass;
    }
    let actual_path = fixture.actual_path("stderr");
    let _ = fs::write(&actual_path, &diagnostics);
    CheckOutcome::Fail(format!(
        "{} via {}: stderr does not contain the {} golden; wrote {}\n--- expected substring ({})\n{}\n--- actual stderr\n{}",
        fixture.display_path().display(),
        path_id,
        kind,
        actual_path.display(),
        golden_path.display(),
        needle,
        diagnostics.trim_end()
    ))
}

/// An abort of an oracle fixture prints, before it fails, the stdout Elixir
/// printed before the same failure: `expected.txt`.
fn abort_stdout_mismatch(fixture: &FixtureCase, path_id: &str, ran: &Ran) -> Option<CheckOutcome> {
    let actual = normalize(&ran.stdout);
    let expected = normalize(&fs::read_to_string(fixture.sidecar_path("expected.txt")).unwrap_or_default());
    if actual == expected {
        let _ = fs::remove_file(fixture.actual_path("txt"));
        return None;
    }
    let output_path = fixture.actual_path("txt");
    let _ = fs::write(&output_path, &actual);
    Some(CheckOutcome::Fail(format!(
        "{} via {}: aborted with stdout that differs from the Elixir-owned golden; wrote {}\n--- expected stdout\n{}--- actual stdout\n{}",
        fixture.display_path().display(),
        path_id,
        output_path.display(),
        expected,
        actual
    )))
}

fn check_diagnostic_telemetry(
    fixture: &FixtureCase,
    header: &Header,
    path: FixtureMatrixPath,
    expected_code: &str,
) -> CheckOutcome {
    let (out, log) = match run_path_logged(fixture, header, path) {
        Ok(out) => out,
        Err(e) => return CheckOutcome::Fail(e),
    };
    let code_needle = format!("\"code\":\"{}\"", expected_code);
    let found = log
        .lines()
        .any(|line| line.contains("\"name\":[\"fz\",\"diag\",\"error\"]") && line.contains(&code_needle));
    if found {
        let _ = fs::remove_file(fixture.actual_path("telemetry"));
        let _ = fs::remove_file(fixture.actual_path("stderr"));
        return CheckOutcome::Pass;
    }
    let actual_path = fixture.actual_path("telemetry");
    let _ = fs::write(&actual_path, &log);
    CheckOutcome::Fail(format!(
        "{} via {}: diagnostic telemetry did not contain code `{}`; wrote {}\n--- stderr\n{}",
        fixture.display_path().display(),
        path.id(),
        expected_code,
        actual_path.display(),
        String::from_utf8_lossy(&out.stderr).trim_end()
    ))
}

fn run_path_logged(
    fixture: &FixtureCase,
    header: &Header,
    path: FixtureMatrixPath,
) -> Result<(Output, String), String> {
    with_fixture_telemetry(|telemetry_path| run_path_logged_to(fixture, header, path, telemetry_path))
}

fn with_fixture_telemetry(run: impl FnOnce(&Path) -> Result<Output, String>) -> Result<(Output, String), String> {
    let telemetry = FixtureTempFile::new("telemetry.jsonl")?;
    let output = run(telemetry.path())?;
    let log = fs::read_to_string(telemetry.path())
        .map_err(|error| format!("read {}: {error}", telemetry.path().display()))?;
    telemetry.unlink()?;
    Ok((output, log))
}

/// `fz2 --log-telemetry <log> build`, then, for a program that compiled, the
/// built binary with `FZ_LOG_TELEMETRY` naming the same log, so the log holds
/// the compile events and then the run's. Returns the binary's output, or the
/// build's when it failed or the fixture has no program to run.
fn build_then_run_logged_to(fixture: &FixtureCase, header: &Header, telemetry_path: &Path) -> Result<Output, String> {
    let stem = fixture.name();
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let out_path = temp_dir().join(format!("fz2_matrix_diag_{}_{}_{}", stem, id(), nonce));
    let result = fixture_command_output(
        Command::new(FZ2_BIN)
            .args(["--log-telemetry"])
            .arg(telemetry_path)
            .args(["build"])
            .arg(fixture.source_path())
            .args(["-o"])
            .arg(&out_path),
        "fz2 build --log-telemetry",
        ExecutionBoundary::Spawn,
        DEFAULT_FIXTURE_CPU_LIMIT,
    )
    .and_then(|build| {
        if !build.status.success() || header.kind != Kind::Run {
            return Ok(build);
        }
        fixture_command_output(
            Command::new(&out_path)
                .args(&header.args)
                .env("FZ_LOG_TELEMETRY", telemetry_path),
            "fz2-built binary",
            ExecutionBoundary::Spawn,
            header.timeout_for_path(FixtureMatrixPath::Build),
        )
    });
    remove_fz2_build_outputs(&out_path);
    result
}

fn run_path_logged_to(
    fixture: &FixtureCase,
    header: &Header,
    path: FixtureMatrixPath,
    telemetry_path: &Path,
) -> Result<Output, String> {
    if path == FixtureMatrixPath::Build {
        return build_then_run_logged_to(fixture, header, telemetry_path);
    }
    let input = fixture.source_path();
    let mut cmd = Command::new(FZ2_BIN);
    cmd.args(["--log-telemetry"]).arg(telemetry_path);
    match (path, header.kind) {
        (FixtureMatrixPath::Run, Kind::Run) => {
            cmd.arg("run").arg(input).args(program_args(header));
        }
        (FixtureMatrixPath::Run, Kind::Test) => {
            cmd.arg("test").arg(input);
        }
        (FixtureMatrixPath::Interp, Kind::Test) => {
            cmd.args(["test", "--interp"]).arg(input);
        }
        (FixtureMatrixPath::Interp, Kind::Run) => {
            cmd.arg("interp").arg(input).args(program_args(header));
        }
        (FixtureMatrixPath::Build, _) => unreachable!("build returns above"),
    }
    fixture_command_output(
        &mut cmd,
        "fz2 --log-telemetry",
        header.execution_boundary(),
        header.timeout_for_path(path),
    )
}

/// Elixir oracle. For every fixture that declares an `oracle` (`self`, or a
/// `<file>.exs` twin), the canonical `expected.txt` golden must equal the
/// stdout of running that Elixir program under the real `elixir` binary. A
/// successful fixture's compiler2 paths reproduce that golden, so
/// `fz == Elixir` holds transitively. An `expect: abort` oracle must also exit
/// 1 with `expected.stderr` in its stderr; each fz path pins the same stderr
/// and stdout.
///
/// A pair whose header `oracle.stamp` equals the stamp of the script, golden
/// and args on disk was confirmed by Elixir already, so Elixir is not run for
/// it. A pair with a different or missing stamp is run and compared; when
/// Elixir agrees but the stamp is stale or missing the trial fails and names
/// the regen command, so the tree never carries a wrong stamp.
///
/// `ORACLE=regen` rewrites `expected.txt` and the header's `oracle.stamp` from
/// the Elixir output; `ORACLE=check` ignores stamps, runs Elixir for every pair
/// and fails on any difference from the golden (the check after an Elixir
/// upgrade; CI runs it on a pull request that changes the pinned Elixir or OTP
/// version). `ORACLE_FIXTURE=<stem>` narrows either mode to one fixture. Requires the `elixir` binary on PATH (Elixir 1.19+); a spawn
/// failure fails loudly by design — the oracle is the signal, so a missing
/// oracle is a hard error, not a skip.
fn oracle_goldens_match_elixir() {
    let mode = OracleMode::from_env();
    let only = var("ORACLE_FIXTURE").ok();
    let mut failures: Vec<String> = Vec::new();
    let mut selected = 0usize;
    for fixture in discover() {
        if only.as_deref().is_some_and(|stem| stem != fixture.name()) {
            continue;
        }
        let header = match parse_header(&fixture) {
            Ok(h) => h,
            Err(_) => continue,
        };
        let Some(oracle_rel) = header.oracle.as_deref() else {
            continue;
        };
        selected += 1;
        let oracle_path = fixture.oracle_path(oracle_rel);
        if let Some(failure) = verify_oracle_pair(&fixture, &header, &oracle_path, mode).failure {
            failures.push(failure);
        }
    }
    if let Some(stem) = only.as_deref().filter(|_| selected == 0) {
        failures.push(format!("ORACLE_FIXTURE `{stem}` names no oracle fixture"));
    }
    assert!(
        failures.is_empty(),
        "oracle golden mismatches ({}):\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

/// What happened to one oracle pair: whether Elixir was started for it, and
/// why the pair failed, if it did.
#[derive(Debug)]
struct OracleVerdict {
    spawned_elixir: bool,
    failure: Option<String>,
}

fn verify_oracle_pair(fixture: &FixtureCase, header: &Header, oracle_path: &Path, mode: OracleMode) -> OracleVerdict {
    let script = match oracle_stamp_bytes(header, oracle_path) {
        Ok(script) => script,
        Err(e) => {
            return OracleVerdict {
                spawned_elixir: false,
                failure: Some(format!("{}: {e}", fixture.display_path().display())),
            };
        }
    };
    let golden = fs::read(fixture.sidecar_path("expected.txt")).unwrap_or_default();
    let stamp = oracle_stamp(&script, &golden, &header.args);
    let current = header.oracle_stamp.as_deref() == Some(stamp.as_str());
    if current && matches!(mode, OracleMode::Verify) {
        return OracleVerdict {
            spawned_elixir: false,
            failure: None,
        };
    }
    let outcome = run_elixir_oracle(fixture, header, oracle_path).and_then(|actual| match mode {
        OracleMode::Verify => compare_oracle_golden(fixture, &actual).and_then(|()| {
            if current {
                Ok(())
            } else {
                Err(stale_stamp_failure(fixture, header))
            }
        }),
        OracleMode::Check => compare_oracle_golden(fixture, &actual),
        OracleMode::Regen => regenerate_oracle_pair(fixture, header, &script, &actual),
    });
    OracleVerdict {
        spawned_elixir: true,
        failure: outcome.err(),
    }
}

/// The oracle bytes a stamp hashes: the twin's bytes, or for `oracle: self` the
/// fixture's own bytes without its stamp line.
fn oracle_stamp_bytes(header: &Header, oracle_path: &Path) -> Result<Vec<u8>, String> {
    let bytes = fs::read(oracle_path).map_err(|e| format!("oracle `{}` not readable: {e}", oracle_path.display()))?;
    if header.oracle.as_deref() != Some(SELF_ORACLE) {
        return Ok(bytes);
    }
    let source = String::from_utf8(bytes).map_err(|e| format!("oracle `{}`: {e}", oracle_path.display()))?;
    without_oracle_stamp(&source)
        .map(String::into_bytes)
        .map_err(|e| format!("oracle `{}`: {e}", oracle_path.display()))
}

fn stale_stamp_failure(fixture: &FixtureCase, header: &Header) -> String {
    let state = if header.oracle_stamp.is_some() {
        "stale"
    } else {
        "missing"
    };
    format!(
        "{}: Elixir agrees with the golden but `oracle.stamp` is {state}; run \
         `ORACLE=regen ORACLE_FIXTURE={} cargo test --test fixture_matrix oracle_goldens_match_elixir`",
        fixture.display_path().display(),
        fixture.name()
    )
}

/// What `oracle_goldens_match_elixir` does with each oracle pair.
#[derive(Clone, Copy)]
enum OracleMode {
    /// Run Elixir for each pair whose stamp does not match, compare with the
    /// golden, and require the stamp to be current.
    Verify,
    /// Run Elixir for every pair, ignoring stamps, and compare with the golden.
    Check,
    /// Run Elixir, rewrite the golden and record the pair's stamp.
    Regen,
}

impl OracleMode {
    fn from_env() -> Self {
        match var("ORACLE").as_deref() {
            Err(_) => Self::Verify,
            Ok("check") => Self::Check,
            Ok("regen") => Self::Regen,
            Ok(other) => panic!("ORACLE must be `check` or `regen`, got `{other}`"),
        }
    }
}

/// Elixir's normalized stdout for one oracle fixture. A success fixture's
/// Elixir exits 0. An `expect: abort` fixture's Elixir fails the way fz does:
/// exit 1 with the `expected.stderr` golden in its stderr.
fn run_elixir_oracle(fixture: &FixtureCase, header: &Header, oracle_path: &Path) -> Result<String, String> {
    let label = format!("elixir {}", oracle_path.display());
    let out = fixture_command_output(
        Command::new("elixir")
            .args(ELIXIR_LOGGER_SILENCED)
            .arg(oracle_path)
            .args(&header.args),
        &label,
        ExecutionBoundary::Spawn,
        DEFAULT_FIXTURE_CPU_LIMIT,
    )
    .map_err(|e| {
        format!(
            "{}: `{}` failed: {} (is Elixir installed and on PATH?)",
            fixture.display_path().display(),
            label,
            e
        )
    })?;
    let stderr = fixture.normalize_actual_diagnostics(&String::from_utf8_lossy(&out.stderr));
    let failure = match header.expect {
        Expect::Abort => elixir_abort_failure(fixture, &out.status, &stderr),
        _ => (!out.status.success()).then(|| format!("exited {}", out.status)),
    };
    if let Some(failure) = failure {
        return Err(format!(
            "{}: `elixir {}` {failure}:\n{}",
            fixture.display_path().display(),
            oracle_path.display(),
            stderr.trim_end()
        ));
    }
    Ok(normalize(&String::from_utf8_lossy(&out.stdout)))
}

/// Why Elixir's run is not the abort `expected.stderr` pins, if it is not.
fn elixir_abort_failure(fixture: &FixtureCase, status: &ExitStatus, stderr: &str) -> Option<String> {
    if status.code() != Some(1) {
        return Some(format!("exited {status}, expected an abort exiting 1"));
    }
    let golden = fs::read_to_string(fixture.sidecar_path("expected.stderr")).unwrap_or_default();
    let needle = fixture.normalize_expected_diagnostics(&golden);
    let needle = needle.trim();
    (needle.is_empty() || !stderr.contains(needle)).then(|| {
        format!(
            "aborted, but its stderr does not contain the expected.stderr golden\n--- expected substring\n{needle}\n--- elixir stderr"
        )
    })
}

fn compare_oracle_golden(fixture: &FixtureCase, actual: &str) -> Result<(), String> {
    let expected = normalize(&fs::read_to_string(fixture.sidecar_path("expected.txt")).unwrap_or_default());
    if actual == expected {
        let _ = fs::remove_file(fixture.actual_path("oracle.txt"));
        return Ok(());
    }
    let actual_path = fixture.actual_path("oracle.txt");
    let _ = fs::write(&actual_path, actual);
    Err(format!(
        "{}: oracle mismatch; wrote {}\n--- expected.txt (Elixir-owned golden)\n{}--- elixir actual\n{}",
        fixture.display_path().display(),
        actual_path.display(),
        expected,
        actual
    ))
}

/// Makes the golden say what Elixir printed and records the stamp of the
/// resulting pair in the fixture header. A golden whose normalized text already
/// equals Elixir's output stays byte for byte as it is, and the stamp covers
/// the bytes on disk.
fn regenerate_oracle_pair(fixture: &FixtureCase, header: &Header, script: &[u8], actual: &str) -> Result<(), String> {
    let at = |step: &str, e: &dyn std::fmt::Display| format!("{}: {step}: {e}", fixture.display_path().display());
    let golden_path = fixture.sidecar_path("expected.txt");
    let on_disk = fs::read_to_string(&golden_path).unwrap_or_default();
    if normalize(&on_disk) != actual {
        if actual.is_empty() {
            let _ = fs::remove_file(&golden_path);
        } else {
            fs::write(&golden_path, actual).map_err(|e| at("write golden", &e))?;
        }
    }
    let golden = fs::read(&golden_path).unwrap_or_default();
    let stamp = oracle_stamp(script, &golden, &header.args);
    let source = fs::read_to_string(&fixture.path).map_err(|e| at("read fixture", &e))?;
    let stamped = with_oracle_stamp(&source, &stamp).map_err(|e| at("stamp header", &e))?;
    if stamped != source {
        fs::write(&fixture.path, stamped).map_err(|e| at("write fixture", &e))?;
    }
    Ok(())
}

const ORACLE_PROBE_SCRIPT: &str = "IO.write(\"x\")\n";

fn oracle_regen_fixture(tag: &str, golden: Option<&str>) -> (PathBuf, FixtureCase, Header) {
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = temp_dir().join(format!("fz_oracle_regen_{tag}_{}_{nonce}", id()));
    fs::create_dir_all(&dir).expect("create regen fixture dir");
    let path = dir.join("regen.fz");
    fs::write(
        &path,
        "#---\n# purpose: regen probe\n# oracle: oracle.exs\n#---\ndef main(), do: 1\n",
    )
    .expect("write fixture");
    fs::write(dir.join("regen.oracle.exs"), ORACLE_PROBE_SCRIPT).expect("write oracle");
    if let Some(golden) = golden {
        fs::write(dir.join("regen.expected.txt"), golden).expect("write golden");
    }
    let fixture = FixtureCase::new(path);
    let header = parse_header(&fixture).expect("parse regen fixture header");
    (dir, fixture, header)
}

fn oracle_regen_leaves_a_golden_that_already_matches_untouched() {
    // Elixir printed "x"; the golden lacks the trailing newline that
    // normalization adds, so it already matches and must not be rewritten.
    let (dir, fixture, header) = oracle_regen_fixture("keep", Some("x"));
    regenerate_oracle_pair(&fixture, &header, ORACLE_PROBE_SCRIPT.as_bytes(), "x\n").expect("regen");
    assert_eq!(fs::read(dir.join("regen.expected.txt")).expect("golden"), b"x");
    let stamped = parse_header(&fixture).expect("reparse").oracle_stamp;
    let expected = oracle_stamp(ORACLE_PROBE_SCRIPT.as_bytes(), b"x", &[]);
    assert_eq!(
        stamped.as_deref(),
        Some(expected.as_str()),
        "stamp covers on-disk bytes"
    );
    let _ = fs::remove_dir_all(dir);
}

fn oracle_regen_rewrites_a_golden_that_differs() {
    let (dir, fixture, header) = oracle_regen_fixture("rewrite", Some("old\n"));
    regenerate_oracle_pair(&fixture, &header, ORACLE_PROBE_SCRIPT.as_bytes(), "x\n").expect("regen");
    assert_eq!(fs::read(dir.join("regen.expected.txt")).expect("golden"), b"x\n");
    let stamped = parse_header(&fixture).expect("reparse").oracle_stamp;
    let expected = oracle_stamp(ORACLE_PROBE_SCRIPT.as_bytes(), b"x\n", &[]);
    assert_eq!(stamped.as_deref(), Some(expected.as_str()));
    let _ = fs::remove_dir_all(dir);
}

/// A stamped pair whose script prints `x` and whose golden is `x\n`.
fn stamped_oracle_fixture(tag: &str) -> (PathBuf, FixtureCase, PathBuf) {
    let (dir, fixture, header) = oracle_regen_fixture(tag, Some("x\n"));
    regenerate_oracle_pair(&fixture, &header, ORACLE_PROBE_SCRIPT.as_bytes(), "x\n").expect("stamp");
    let oracle_path = fixture.oracle_path("oracle.exs");
    (dir, fixture, oracle_path)
}

fn verdict(fixture: &FixtureCase, oracle_path: &Path, mode: OracleMode) -> OracleVerdict {
    let header = parse_header(fixture).expect("reparse header");
    verify_oracle_pair(fixture, &header, oracle_path, mode)
}

fn oracle_unchanged_pair_does_not_start_elixir() {
    let (dir, fixture, oracle_path) = stamped_oracle_fixture("unchanged");
    let verdict = verdict(&fixture, &oracle_path, OracleMode::Verify);
    assert!(
        !verdict.spawned_elixir,
        "a stamped, unchanged pair must not start Elixir"
    );
    assert_eq!(verdict.failure, None);
    let _ = fs::remove_dir_all(dir);
}

fn oracle_pair_with_a_changed_script_golden_or_args_runs_elixir() {
    let (dir, fixture, oracle_path) = stamped_oracle_fixture("changed");
    fs::write(&oracle_path, "IO.write(\"y\")\n").expect("change script");
    let verdict_after_script = verdict(&fixture, &oracle_path, OracleMode::Verify);
    assert!(verdict_after_script.spawned_elixir, "a changed script runs Elixir");
    assert!(
        verdict_after_script
            .failure
            .is_some_and(|f| f.contains("oracle mismatch"))
    );

    fs::write(&oracle_path, ORACLE_PROBE_SCRIPT).expect("restore script");
    fs::write(fixture.sidecar_path("expected.txt"), "z\n").expect("change golden");
    let verdict_after_golden = verdict(&fixture, &oracle_path, OracleMode::Verify);
    assert!(verdict_after_golden.spawned_elixir, "a changed golden runs Elixir");
    assert!(
        verdict_after_golden
            .failure
            .is_some_and(|f| f.contains("oracle mismatch"))
    );

    fs::write(fixture.sidecar_path("expected.txt"), "x\n").expect("restore golden");
    let source = fs::read_to_string(&fixture.path).expect("read fixture");
    fs::write(
        &fixture.path,
        source.replace("# oracle: oracle.exs\n", "# oracle: oracle.exs\n# args: a\n"),
    )
    .expect("change args");
    let verdict_after_args = verdict(&fixture, &oracle_path, OracleMode::Verify);
    assert!(verdict_after_args.spawned_elixir, "changed args run Elixir");
    let _ = fs::remove_dir_all(dir);
}

fn oracle_agreeing_pair_with_a_stale_or_missing_stamp_fails_naming_regen() {
    let (dir, fixture, oracle_path) = stamped_oracle_fixture("stale");
    let stamp_line = format!(
        "# oracle.stamp: {}\n",
        parse_header(&fixture).expect("header").oracle_stamp.expect("stamp")
    );
    let source = fs::read_to_string(&fixture.path).expect("read fixture");
    let stale = source.replace(&stamp_line, "# oracle.stamp: 0000000000000000\n");
    let missing = source.replace(&stamp_line, "");
    for (state, text) in [("stale", stale), ("missing", missing)] {
        fs::write(&fixture.path, text).expect("write fixture");
        let verdict = verdict(&fixture, &oracle_path, OracleMode::Verify);
        assert!(verdict.spawned_elixir, "{state}: Elixir confirms the pair");
        let failure = verdict.failure.unwrap_or_else(|| panic!("{state} stamp must fail"));
        assert!(failure.contains(state), "{failure}");
        assert!(failure.contains("ORACLE=regen ORACLE_FIXTURE=regen"), "{failure}");
    }
    let _ = fs::remove_dir_all(dir);
}

fn oracle_check_mode_runs_elixir_despite_a_current_stamp() {
    let (dir, fixture, oracle_path) = stamped_oracle_fixture("check");
    let verdict = verdict(&fixture, &oracle_path, OracleMode::Check);
    assert!(verdict.spawned_elixir, "check mode ignores stamps");
    assert_eq!(verdict.failure, None);
    let _ = fs::remove_dir_all(dir);
}

fn oracle_stamps_in_the_tree_are_current_so_no_elixir_starts() {
    let mut started: Vec<String> = Vec::new();
    for fixture in discover() {
        let Ok(header) = parse_header(&fixture) else { continue };
        let Some(oracle_rel) = header.oracle.as_deref() else {
            continue;
        };
        let oracle_path = fixture.oracle_path(oracle_rel);
        if verify_oracle_pair(&fixture, &header, &oracle_path, OracleMode::Verify).spawned_elixir {
            started.push(fixture.name());
        }
    }
    assert!(
        started.is_empty(),
        "oracle pairs whose stamp is not current (regen them): {started:?}"
    );
}

const SELF_ORACLE_HEADER: &str = "#---\n# purpose: self oracle probe\n# oracle: self\n";

/// A fixture that is its own oracle: `header_extra` joins the frontmatter and
/// `program` is the Elixir body.
fn self_oracle_fixture(tag: &str, header_extra: &str, program: &str, golden: Option<&str>) -> (PathBuf, FixtureCase) {
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = temp_dir().join(format!("fz_oracle_self_{tag}_{}_{nonce}", id()));
    fs::create_dir_all(&dir).expect("create self oracle dir");
    let path = dir.join("probe.fz");
    fs::write(&path, format!("{SELF_ORACLE_HEADER}{header_extra}#---\n{program}")).expect("write fixture");
    if let Some(golden) = golden {
        fs::write(dir.join("probe.expected.txt"), golden).expect("write golden");
    }
    (dir, FixtureCase::new(path))
}

fn self_verdict(fixture: &FixtureCase, mode: OracleMode) -> OracleVerdict {
    let header = parse_header(fixture).expect("header");
    let oracle_path = fixture.oracle_path(header.oracle.as_deref().expect("oracle"));
    verify_oracle_pair(fixture, &header, &oracle_path, mode)
}

fn regen_self(fixture: &FixtureCase) -> OracleVerdict {
    self_verdict(fixture, OracleMode::Regen)
}

fn oracle_stamp_of_a_self_oracle_hashes_the_fixture_without_its_stamp_line() {
    let (dir, fixture) = self_oracle_fixture("stamp", "", "IO.write(\"x\")\n", Some("x\n"));
    let regen = regen_self(&fixture);
    assert_eq!(regen.failure, None);
    let stamped = fs::read_to_string(&fixture.path).expect("stamped fixture");
    assert_eq!(stamped.matches("oracle.stamp").count(), 1, "{stamped}");
    let stamp_free = without_oracle_stamp(&stamped).expect("strip");
    assert_eq!(
        parse_header(&fixture).expect("header").oracle_stamp,
        Some(oracle_stamp(stamp_free.as_bytes(), b"x\n", &[])),
        "the stamp covers the fixture without its own stamp line"
    );
    let verdict = self_verdict(&fixture, OracleMode::Verify);
    assert!(!verdict.spawned_elixir, "a stamped self oracle does not start Elixir");
    assert_eq!(verdict.failure, None);
    fs::write(&fixture.path, stamped.replace("IO.write(\"x\")", "IO.write(\"y\")")).expect("edit program");
    assert!(
        self_verdict(&fixture, OracleMode::Verify).spawned_elixir,
        "editing the fixture invalidates its stamp"
    );
    let _ = fs::remove_dir_all(dir);
}

fn oracle_self_runs_the_fixture_file_under_elixir() {
    let (dir, fixture) = self_oracle_fixture(
        "runs",
        "# args: -- \"a b\"\n",
        "IO.write(Enum.join(System.argv(), \"|\") <> \"\\n\")\n",
        Some("--|a b\n"),
    );
    let verdict = self_verdict(&fixture, OracleMode::Check);
    assert!(verdict.spawned_elixir);
    assert_eq!(verdict.failure, None, "Elixir ran the fixture file with its args");
    let _ = fs::remove_dir_all(dir);
}

fn an_oracle_ignores_the_report_of_a_spawned_process_that_crashed() {
    let (dir, fixture) = self_oracle_fixture(
        "spawn_crash",
        "",
        "spawn(fn -> raise \"lost\" end)\nProcess.sleep(200)\nIO.puts(\"main carried on\")\n",
        Some("main carried on\n"),
    );
    let verdict = self_verdict(&fixture, OracleMode::Check);
    assert!(verdict.spawned_elixir);
    assert_eq!(
        verdict.failure, None,
        "the crash report is the logger's, not the program's output"
    );
    let _ = fs::remove_dir_all(dir);
}

const ABORT_PROBE: &str = "IO.puts(\"before\")\nthrow(:ball)\n";

fn oracle_abort_requires_exit_1_the_stderr_golden_and_the_stdout_golden() {
    let abort = "# expect: abort\n";
    let (dir, fixture) = self_oracle_fixture("abort", abort, ABORT_PROBE, Some("before\n"));
    fs::write(fixture.sidecar_path("expected.stderr"), "** (throw) :ball\n").expect("stderr golden");
    let ok = self_verdict(&fixture, OracleMode::Check);
    assert_eq!(ok.failure, None, "exit 1, the banner on stderr and the stdout agree");

    fs::write(fixture.sidecar_path("expected.txt"), "other\n").expect("change stdout golden");
    let failure = self_verdict(&fixture, OracleMode::Check)
        .failure
        .expect("stdout differs");
    assert!(failure.contains("oracle mismatch"), "{failure}");

    fs::write(fixture.sidecar_path("expected.txt"), "before\n").expect("restore stdout golden");
    fs::write(fixture.sidecar_path("expected.stderr"), "** (throw) :other\n").expect("change stderr golden");
    let failure = self_verdict(&fixture, OracleMode::Check)
        .failure
        .expect("stderr differs");
    assert!(
        failure.contains("does not contain the expected.stderr golden"),
        "{failure}"
    );

    fs::write(fixture.sidecar_path("expected.stderr"), "** (throw) :ball\n").expect("restore stderr golden");
    let source = fs::read_to_string(&fixture.path).expect("read fixture");
    fs::write(&fixture.path, source.replace("throw(:ball)", "IO.puts(\"after\")")).expect("no abort");
    let failure = self_verdict(&fixture, OracleMode::Check)
        .failure
        .expect("exit 0 is no abort");
    assert!(failure.contains("expected an abort exiting 1"), "{failure}");
    let _ = fs::remove_dir_all(dir);
}

fn oracle_regen_of_an_abort_writes_stdout_only() {
    let (dir, fixture) = self_oracle_fixture(
        "abort_regen",
        "# expect: abort\n",
        ABORT_PROBE,
        Some("before\n** (throw) :ball\n"),
    );
    fs::write(fixture.sidecar_path("expected.stderr"), "** (throw) :ball\n").expect("stderr golden");
    assert_eq!(regen_self(&fixture).failure, None);
    assert_eq!(
        fs::read(fixture.sidecar_path("expected.txt")).expect("golden"),
        b"before\n"
    );
    assert_eq!(
        fs::read(fixture.sidecar_path("expected.stderr")).expect("stderr golden"),
        b"** (throw) :ball\n",
        "regen leaves the stderr golden alone"
    );
    let _ = fs::remove_dir_all(dir);
}

fn an_fz_abort_of_an_oracle_fixture_must_print_the_stdout_golden() {
    let (dir, fixture) = self_oracle_fixture("fz_abort", "# expect: abort\n", ABORT_PROBE, Some("before\n"));
    fs::write(fixture.sidecar_path("expected.stderr"), "** (throw) :ball\n").expect("stderr golden");
    let header = parse_header(&fixture).expect("header");
    let ran = |stdout: &str| Ran {
        status: ExitStatus::from_raw(1 << 8),
        stdout: stdout.to_string(),
        diagnostics: "** (throw) :ball\n".to_string(),
    };
    let path = FixtureMatrixPath::Run;
    assert!(matches!(
        check_failure(&fixture, &header, "abort", path, false, &ran("before\n")),
        CheckOutcome::Pass
    ));
    let CheckOutcome::Fail(message) = check_failure(&fixture, &header, "abort", path, false, &ran("")) else {
        panic!("an abort whose stdout differs from the golden must fail");
    };
    assert!(message.contains("differs from the Elixir-owned golden"), "{message}");
    let _ = fs::remove_dir_all(dir);
}

// fz-fkv: the bulk `fixture_matrix()` test was replaced by per-pair
// trials emitted by the custom Rust harness entry point. Discovery,
// header parsing, and per-pair compare all live in the helpers above;
// the trial wiring is at the top of this file.

fn fixture_telemetry_reserves_its_path() {
    let telemetry = FixtureTempFile::new("telemetry.jsonl").expect("reserve telemetry");
    let path = telemetry.path().to_path_buf();
    assert!(
        path.is_file(),
        "telemetry invocation must reserve its path before spawning a writer"
    );
    assert_eq!(
        File::create_new(&path).unwrap_err().kind(),
        std::io::ErrorKind::AlreadyExists
    );
    drop(telemetry);
    assert!(!path.exists(), "only dropping the owner removes its reservation");
}

/// A program that writes a relative file name writes into a directory that
/// belongs to that one invocation, so two runs of the same program never see
/// each other's file, and the directory is gone once the invocation ends --
/// whether it exited, failed or timed out.
fn fixture_invocations_own_their_working_directory() {
    let write_then_read_back = || {
        let mut command = Command::new("sh");
        command.args([
            "-c",
            "test ! -e shared.tmp && echo mine > shared.tmp && cat shared.tmp && pwd",
        ]);
        let output = fixture_command_output(
            &mut command,
            "relative file writer",
            ExecutionBoundary::Spawn,
            DEFAULT_FIXTURE_CPU_LIMIT,
        )
        .expect("a fresh working directory holds no earlier run's file");
        assert!(output.status.success());
        let text = String::from_utf8(output.stdout).expect("utf8 output");
        let (content, dir) = text.split_once('\n').expect("file content then directory");
        assert_eq!(content, "mine");
        PathBuf::from(dir.trim_end())
    };
    let first = write_then_read_back();
    let second = write_then_read_back();
    assert_ne!(first, second, "every invocation gets its own directory");
    for dir in [&first, &second] {
        assert!(!dir.exists(), "working directory leaked: {}", dir.display());
    }

    let dir_file = temp_build_output_path("scratch_dir_name");
    let error = fixture_command_output_with_ready_writer_action(
        Command::new("sh").env("FZ_SCRATCH_DIR_PATH", &dir_file).args([
            "-c",
            "pwd > \"$FZ_SCRATCH_DIR_PATH\"; printf . > /dev/fd/$FZ_EXEC_READY_FD; sleep 2",
        ]),
        "timed-out relative file writer",
        ExecutionBoundary::Announced,
        ChildLimit::new(Duration::from_millis(500), Duration::from_millis(500)),
        ReadyWriterAction::Inherit,
    )
    .expect_err("the probe outlives its window");
    assert!(error.contains("exceeded"), "{error}");
    let recorded = fs::read_to_string(&dir_file).expect("probe recorded its directory");
    let timed_out_dir = PathBuf::from(recorded.trim_end());
    let _ = fs::remove_file(dir_file);
    assert!(
        !timed_out_dir.exists(),
        "a timed-out invocation releases its directory: {}",
        timed_out_dir.display()
    );
}

fn fixture_telemetry_cleans_failed_invocations() {
    let mut reserved = PathBuf::new();
    let result = with_fixture_telemetry(|path| {
        reserved = path.to_path_buf();
        fs::write(path, "unfinished telemetry").expect("write partial log");
        Err("child failed before completion".into())
    });
    assert_eq!(result.unwrap_err(), "child failed before completion");
    assert!(!reserved.exists(), "failed commands must release their telemetry");

    let result = with_fixture_telemetry(|path| {
        reserved = path.to_path_buf();
        fs::remove_file(path).expect("inject premature removal");
        Ok(Output {
            status: ExitStatus::from_raw(0),
            stdout: Vec::new(),
            stderr: Vec::new(),
        })
    });
    assert!(
        result
            .unwrap_err()
            .starts_with(&format!("read {}:", reserved.display())),
        "a missing log after completion must remain a hard read error"
    );

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        with_fixture_telemetry(|path| {
            reserved = path.to_path_buf();
            panic!("injected invocation panic");
        })
    }));
    assert!(result.is_err());
    assert!(!reserved.exists(), "unwinding must release the reservation");
}

fn fixture_telemetry_concurrent_spec_violations() {
    const INVOCATIONS: usize = 24;
    let barrier = std::sync::Barrier::new(INVOCATIONS);
    let paths = std::thread::scope(|scope| {
        let handles = (0..INVOCATIONS)
            .map(|index| {
                let barrier = &barrier;
                scope.spawn(move || {
                    let fixture = FixtureCase::new("fixtures/00142_spec_float_disjoint.fz");
                    let header = parse_header(&fixture).expect("parse spec violation");
                    let leg = [
                        FixtureMatrixPath::Run,
                        FixtureMatrixPath::Interp,
                        FixtureMatrixPath::Build,
                    ][index % 3];
                    let mut reserved = PathBuf::new();
                    let (output, log) = with_fixture_telemetry(|path| {
                        reserved = path.to_path_buf();
                        assert!(path.is_file());
                        barrier.wait();
                        run_path_logged_to(&fixture, &header, leg, path)
                    })
                    .expect("complete telemetry invocation");
                    assert!(!output.status.success(), "spec violation must reject compilation");
                    assert!(log.ends_with('\n'), "completed JSONL must end on a whole record");
                    let events = log
                        .lines()
                        .map(|line| {
                            serde_json::from_str::<serde_json::Value>(line)
                                .expect("every completed telemetry record must parse")
                        })
                        .collect::<Vec<_>>();
                    assert!(
                        events
                            .iter()
                            .any(|event| event["name"] == serde_json::json!(["fz", "diag", "error"])
                                && event["metadata"]["diagnostic"]["code"] == "spec/violation"),
                        "each invocation must retain its diagnostic"
                    );
                    assert!(!reserved.exists(), "successful reads must release their reservation");
                    reserved
                })
            })
            .collect::<Vec<_>>();
        handles
            .into_iter()
            .map(|handle| handle.join().expect("telemetry worker"))
            .collect::<Vec<_>>()
    });
    assert_eq!(
        paths.iter().collect::<std::collections::BTreeSet<_>>().len(),
        INVOCATIONS,
        "simultaneous paths, including repeated fixture legs, must never alias"
    );
}

fn parse_json_u64_field(line: &str, key: &str) -> Option<usize> {
    let needle = format!("\"{}\":", key);
    let start = line.find(&needle)? + needle.len();
    let digits: String = line[start..].chars().take_while(|c| c.is_ascii_digit()).collect();
    if digits.is_empty() {
        return None;
    }
    digits.parse().ok()
}

fn required_json_u64_field(line: &str, key: &str, context: &str) -> usize {
    parse_json_u64_field(line, key).unwrap_or_else(|| panic!("{context} missing {key}"))
}

#[derive(Debug, Default, PartialEq, Eq)]
struct ListRetentionTelemetryStats {
    construction_count: usize,
    physical_capture_count: usize,
    runtime_attempted_count: usize,
    runtime_reused_count: usize,
}

impl ListRetentionTelemetryStats {
    fn runtime_fallback_count(&self) -> usize {
        self.runtime_attempted_count.saturating_sub(self.runtime_reused_count)
    }
}

fn list_retention_telemetry_stats_for_fixture(fixture: &FixtureCase) -> ListRetentionTelemetryStats {
    let header = parse_header(fixture).unwrap_or_else(|error| panic!("parse fixture header: {error}"));
    let (out, log) = run_path_logged(fixture, &header, FixtureMatrixPath::Run)
        .unwrap_or_else(|e| panic!("run fz2 run --log-telemetry: {}", e));
    assert!(
        out.status.success(),
        "fz2 run --log-telemetry {} exited {}: {}",
        fixture.display_path().display(),
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let mut stats = ListRetentionTelemetryStats::default();
    let mut saw_native_event = false;
    for line in log.lines() {
        if line.contains("\"name\":[\"fz\",\"compiler2\",\"native_program\",\"list_retention\"]") {
            saw_native_event = true;
            stats.construction_count = parse_json_u64_field(line, "construction_count").unwrap_or_else(|| {
                panic!(
                    "{} telemetry missing construction_count",
                    fixture.display_path().display()
                )
            });
            stats.physical_capture_count = parse_json_u64_field(line, "physical_capture_count").unwrap_or_else(|| {
                panic!(
                    "{} telemetry missing physical_capture_count",
                    fixture.display_path().display()
                )
            });
        }
    }
    for site in reuse_sites_in(&log).iter().filter(|site| site.object == "list") {
        stats.runtime_attempted_count += site.hits + site.misses;
        stats.runtime_reused_count += site.hits;
    }
    assert!(
        saw_native_event,
        "{} telemetry missing fz.compiler2.native_program.list_retention event",
        fixture.display_path().display()
    );
    stats
}

fn scheduler_receive_buffers_are_any_value_refs() {
    let files = [
        "runtime/src/park.rs",
        "runtime/src/sched.rs",
        "src/exec/runtime.rs",
        "src/compiler2/native_codegen/receive.rs",
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

    for dir in ["src/ir_codegen", "src/compiler2/native_codegen"] {
        for entry in fs::read_dir(dir).unwrap_or_else(|e| panic!("read {} dir: {}", dir, e)) {
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

/// A private runtime helper is still a callable surface. Without a spec its
/// parameters have the domain `any`, so list- or tuple-only clauses are
/// genuinely partial and the coverage warning is correct. Keep the invariant
/// structural: lazy runtime loading cannot exercise every helper in one
/// fixture, but every declared private signature must have a matching spec.
fn runtime_private_helpers_declare_their_domains() {
    let mut private = BTreeSet::new();
    let mut specified = BTreeSet::new();

    let mut paths = fs::read_dir("lib")
        .expect("read runtime library")
        .map(|entry| entry.expect("read runtime library entry").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "fz"))
        .collect::<Vec<_>>();
    paths.sort();

    for path in paths {
        let source = fs::read_to_string(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        for (line_index, line) in source.lines().enumerate() {
            if line.trim_start().starts_with("defp ") {
                let signature = runtime_source_signature(line, "defp ")
                    .unwrap_or_else(|| panic!("parse private runtime helper at {}:{}", path.display(), line_index + 1));
                private.insert(format!("{}:{signature}", path.display()));
            }
            if let Some(signature) = runtime_source_signature(line, "@spec ") {
                specified.insert(format!("{}:{signature}", path.display()));
            }
        }
    }

    let missing = private.difference(&specified).cloned().collect::<Vec<_>>();
    assert!(
        missing.is_empty(),
        "private runtime helpers need explicit parameter and result domains:\n{}",
        missing.join("\n")
    );
}

fn runtime_source_signature(line: &str, marker: &str) -> Option<String> {
    let declaration = line.trim_start().strip_prefix(marker)?;
    let open = declaration.find('(')?;
    let name = &declaration[..open];
    if name.is_empty()
        || !name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'?' | b'!'))
    {
        return None;
    }
    let arity = runtime_source_parameter_arity(&declaration[open + 1..])?;
    Some(format!("{name}/{arity}"))
}

fn runtime_source_parameter_arity(parameters: &str) -> Option<usize> {
    let bytes = parameters.as_bytes();
    let mut depth = 0usize;
    let mut commas = 0usize;
    let mut saw_argument = false;
    let mut quote = None;
    let mut escaped = false;
    let mut index = 0usize;

    while index < bytes.len() {
        let byte = bytes[index];
        if let Some(delimiter) = quote {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == delimiter {
                quote = None;
            }
            index += 1;
            continue;
        }
        if matches!(byte, b'\'' | b'"') {
            quote = Some(byte);
            saw_argument = true;
            index += 1;
            continue;
        }
        if bytes[index..].starts_with(b"<<") {
            depth += 1;
            saw_argument = true;
            index += 2;
            continue;
        }
        if bytes[index..].starts_with(b">>") {
            depth = depth.checked_sub(1)?;
            index += 2;
            continue;
        }
        match byte {
            b'(' | b'[' | b'{' => {
                depth += 1;
                saw_argument = true;
            }
            b']' | b'}' => depth = depth.checked_sub(1)?,
            b')' if depth == 0 => return Some(if saw_argument { commas + 1 } else { 0 }),
            b')' => depth -= 1,
            b',' if depth == 0 => commas += 1,
            byte if !byte.is_ascii_whitespace() => saw_argument = true,
            _ => {}
        }
        index += 1;
    }
    None
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

fn quicksort_pins_return_demand_target() {
    let readme = fs::read_to_string("fixtures/01577_quicksort.fz").expect("read quicksort README");
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

fn enum_list_allocations_pin_minimum_list_cons() {
    let readme =
        fs::read_to_string("fixtures/01456_enum_list_allocations.fz").expect("read enum_list_allocations README");
    for needle in [
        "the input list literal allocates five cons cells",
        "`Enum.count/1`, `Enum.member?/2`, and `Enum.reduce/3` allocate no additional",
        "public `Enum.reduce/3` stays a small wrapper over `Enumerable.reduce/3`",
        "static protocol dispatch routes the known list receiver",
        "the public reducer bridge closure is erased on every path",
        "`list_cons_allocs = 5`",
        "`list_cons_bytes = 80`",
        "`struct_allocs = 0`",
        "without rebuilding the pair",
        "final list/struct/map heap headline is `80`",
    ] {
        assert!(
            readme.contains(needle),
            "enum_list_allocations README must pin allocation contract `{}`",
            needle
        );
    }

    assert_fixture_output_contains(
        "fixtures/01456_enum_list_allocations.fz",
        "expected.txt",
        &["5\ntrue\n15", "{5, 80,"],
    );
    // Destructuring alone carries no retention. These read-only consumers have
    // no retaining construction, physical source capture, or runtime attempt.
    let stats =
        list_retention_telemetry_stats_for_fixture(&FixtureCase::new("fixtures/01456_enum_list_allocations.fz"));
    assert_eq!(
        stats,
        ListRetentionTelemetryStats {
            construction_count: 0,
            physical_capture_count: 0,
            runtime_attempted_count: 0,
            runtime_reused_count: 0,
        },
        "enum_list_allocations should keep count/member?/reduce on the no-extra-list-cons path",
    );
    assert_eq!(stats.runtime_fallback_count(), 0);
}

fn enum_sort_constant_sorter_erased_under_return_demand_specs() {
    assert_fixture_output_contains(
        "fixtures/01460_enum_sort.fz",
        "expected.txt",
        &["{22, 352, 0, 0, 2, 64, 0, 0}"],
    );

    let readme = fs::read_to_string("fixtures/01460_enum_sort.fz").expect("read enum_sort README");
    for needle in [
        "default sorter is erased",
        "return-demand-specialized runtime-library",
        "not only value-demand specs",
    ] {
        assert!(readme.contains(needle), "enum_sort README must pin `{}`", needle);
    }

    // The sort walks its input once by count and never copies a half, so the
    // only retaining constructions are in the merge, and every attempt keeps
    // its source cell.
    let stats = list_retention_telemetry_stats_for_fixture(&FixtureCase::new("fixtures/01460_enum_sort.fz"));
    assert_eq!(
        stats,
        ListRetentionTelemetryStats {
            construction_count: 4,
            physical_capture_count: 8,
            runtime_attempted_count: 48,
            runtime_reused_count: 48,
        },
        "enum_sort pins retaining constructions, actual physical captures, and runtime reuse",
    );
    assert_eq!(stats.runtime_fallback_count(), 0);
}

fn self_send_copies_the_message_and_the_senders_list_stays_intact() {
    let fixture = FixtureCase::new(
        "fixtures/00900_a_self_send_copies_its_message_as_a_send_to_another_process_does_and_the_senders_list_stays_intact.fz",
    );
    let expected = fs::read_to_string(fixture.sidecar_path("expected.txt")).expect("read 00900 expected.txt");
    assert_eq!(
        expected, "[1, 9]\n3\n[4, 5, 6]\n[4, 9]\n",
        "the control rewrite prints [1, 9]; the send copies the message's three list cells; the received message is intact; the refused rewrite still yields [4, 9]"
    );

    // Four one-cons constructions retain a source cell: the two identical
    // aliases, the control rewrite that runs in place, and the rewrite of the
    // sent cell. Only the last one misses, because the call-site ownership rule
    // published the cell at the send.
    let stats = list_retention_telemetry_stats_for_fixture(&fixture);
    assert_eq!(
        (stats.runtime_attempted_count, stats.runtime_reused_count),
        (4, 3),
        "self-send fixture pins four retention attempts with exactly one refused rewrite",
    );
    assert_eq!(stats.runtime_fallback_count(), 1);
}

fn a_list_a_continuation_captures_stays_rewritable_in_place() {
    let fixture = FixtureCase::new(
        "fixtures/01296_a_list_a_continuation_captures_is_rewritten_in_place_unless_a_call_aliases_it.fz",
    );
    let expected = fs::read_to_string(fixture.sidecar_path("expected.txt")).expect("read 01296 expected.txt");
    assert_eq!(
        expected, "[1, 2]\n[4, 3]\n[4, 5, 6]\n",
        "the unaliased cell is rewritten; the aliased cell's other name still reads its original contents"
    );

    // Three one-cons constructions retain a source cell: the identical twin,
    // the rewrite of the cell only a continuation captures, and the rewrite of
    // the cell a call argument aliases. Only the last one misses.
    let stats = list_retention_telemetry_stats_for_fixture(&fixture);
    assert_eq!(
        (stats.runtime_attempted_count, stats.runtime_reused_count),
        (3, 2),
        "a capture does not share its list; the call-site publication of an aliased argument does",
    );
    assert_eq!(stats.runtime_fallback_count(), 1);
}

/// The struct updates the program made on `path`, and how many of them stored
/// into their base: `(attempts, hits)` summed over the reuse sites of structs
/// and of tuples.
fn struct_retention_for_fixture(fixture: &FixtureCase, path: FixtureMatrixPath) -> (usize, usize) {
    let label = format!("{path:?}");
    reuse_sites_in(&telemetry_log_for_fixture(fixture, path, &label))
        .iter()
        .filter(|site| site.object == "struct" || site.object == "tuple")
        .fold((0, 0), |(attempts, hits), site| {
            (attempts + site.hits + site.misses, hits + site.hits)
        })
}

/// The binaries each process of `fixture` marked shared on `path`, in pid
/// order, read from the processes' exit events.
fn binaries_shared_by_process(fixture: &FixtureCase, path: FixtureMatrixPath) -> Vec<usize> {
    let header = parse_header(fixture).unwrap_or_else(|error| panic!("parse fixture header: {error}"));
    let (out, log) = run_path_logged(fixture, &header, path)
        .unwrap_or_else(|error| panic!("{path:?} {} with telemetry: {error}", fixture.display_path().display()));
    assert!(
        out.status.success(),
        "{path:?} {} exited {}: {}",
        fixture.display_path().display(),
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let context = fixture.display_path().display().to_string();
    let mut by_pid: Vec<(usize, usize)> = log
        .lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"runtime\",\"process_exited\"]"))
        .map(|line| {
            (
                required_json_u64_field(line, "pid", &context),
                required_json_u64_field(line, "binaries_shared", &context),
            )
        })
        .collect();
    by_pid.sort_unstable();
    by_pid.into_iter().map(|(_, shared)| shared).collect()
}

/// A frame is popped when it resumes and ends at the bump pointer. With a
/// block's end another block's start, the frame that ends one block and the
/// callee's frame that begins the next pass the same test, and the pop moves
/// the pointer below the second block. Later allocations then write into the
/// first block's tail, which corrupts memory with telemetry on or off, and the
/// young byte count underflows. The fixture runs with telemetry because the
/// runtime's debug arithmetic makes that underflow a panic.
fn a_resumed_frame_never_pops_across_a_block_boundary() {
    let fixture =
        FixtureCase::new("fixtures/01751_a_deep_non_tail_recursion_pops_each_resumed_frame_within_its_own_block.fz");
    let header = parse_header(&fixture).unwrap_or_else(|error| panic!("parse fixture header: {error}"));
    for path in [
        FixtureMatrixPath::Run,
        FixtureMatrixPath::Interp,
        FixtureMatrixPath::Build,
    ] {
        let (out, _log) = run_path_logged(&fixture, &header, path)
            .unwrap_or_else(|error| panic!("{path:?} {} with telemetry: {error}", fixture.display_path().display()));
        assert!(
            out.status.success(),
            "{path:?} {} exited {}: {}",
            fixture.display_path().display(),
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            "4504500\n",
            "{path:?}: the sum of the frames"
        );
    }
}

/// Each process publishes one fresh binary at one place and sends what it
/// published as its last act, so its count is what that publication marked:
/// a store into a container or a closure marks the binary, as does a call
/// made while the caller holds it; a message copy leaves the sender's binary
/// with its one holder, but `send` returns its message, so the sender's
/// frame holds the binary past `fz_send` and marks it, and so a reduction
/// yield before the send marks it too. Every path counts the same, because
/// every mark is `Heap::share` or its inline form. The main process, which
/// spawns them and prints what they send, comes first and is not part of the
/// claim.
fn each_place_a_binary_gains_a_second_holder_marks_it_shared() {
    let fixture = FixtureCase::new("fixtures/01711_each_place_a_binary_gains_a_second_holder_marks_it_shared.fz");
    let expected = vec![
        1, 1, // unpublished: `send` returns the message, so the frame holds it past `fz_send`
        2, 1, // tuple field
        2, 1, // struct field
        2, 1, // list head
        2, 1, // map key
        2, 1, // map value
        2, 1, // closure capture
        1, 1, // a call made while the caller holds it
        2, 1, // self-send
        1, 1, // reduction yield
    ];
    for path in [
        FixtureMatrixPath::Run,
        FixtureMatrixPath::Interp,
        FixtureMatrixPath::Build,
    ] {
        assert_eq!(
            binaries_shared_by_process(&fixture, path)[1..],
            expected,
            "{path:?}: (small, large) per publication",
        );
    }
}

fn a_struct_update_rewrites_only_a_base_nothing_else_holds() {
    let fixture = FixtureCase::new(
        "fixtures/01309_a_struct_update_rewrites_its_base_in_place_only_when_nothing_else_holds_it.fz",
    );

    // Thirteen struct updates on every path. Natively only the threaded
    // loop's second and third steps store into their base: its first base is
    // read-only program data, and every other base is published -- passed to
    // a call its caller still reads, stored in a tuple, captured, received as
    // a message, or kept by a collection.
    for path in [FixtureMatrixPath::Run, FixtureMatrixPath::Build] {
        assert_eq!(
            struct_retention_for_fixture(&fixture, path),
            (13, 2),
            "{path:?}: only the threaded loop's own copies are rewritten",
        );
    }

    // interp builds every literal on the heap, so each loop's first step
    // rewrites too, and it collects only between quanta, so nothing kept
    // `kept` before its update.
    assert_eq!(
        struct_retention_for_fixture(&fixture, FixtureMatrixPath::Interp),
        (13, 9),
        "interp: the literals and the uncollected `kept` are rewritten as well",
    );
}

/// One `fz.runtime.send.probe` event as the jsonl log renders it.
#[derive(Clone, Debug, PartialEq, Eq)]
struct SendProbeEvent {
    outcome: String,
    receiver: usize,
    gift_bytes: usize,
    gift_blocks: usize,
}

impl SendProbeEvent {
    fn new(outcome: &str, receiver: usize, gift_bytes: usize, gift_blocks: usize) -> Self {
        Self {
            outcome: outcome.to_string(),
            receiver,
            gift_bytes,
            gift_blocks,
        }
    }
}

fn json_str_field(line: &str, key: &str) -> Option<String> {
    let needle = format!("\"{}\":\"", key);
    let start = line.find(&needle)? + needle.len();
    let end = line[start..].find('"')?;
    Some(line[start..start + end].to_string())
}

/// The telemetry log of one `--log-telemetry` run of the fixture on `path`.
fn telemetry_log_for_fixture(fixture: &FixtureCase, path: FixtureMatrixPath, label: &str) -> String {
    let header = parse_header(fixture).unwrap_or_else(|error| panic!("parse fixture header: {error}"));
    let (out, log) =
        run_path_logged(fixture, &header, path).unwrap_or_else(|e| panic!("fz2 {label} --log-telemetry: {}", e));
    assert!(
        out.status.success(),
        "fz2 {label} --log-telemetry {} exited {}: {}",
        fixture.display_path().display(),
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    log
}

/// Every send probe the fixture emits on `path`, in emission order.
fn send_probe_events_for_fixture(fixture: &FixtureCase, path: FixtureMatrixPath, label: &str) -> Vec<SendProbeEvent> {
    telemetry_log_for_fixture(fixture, path, label)
        .lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"runtime\",\"send\",\"probe\"]"))
        .map(|line| SendProbeEvent {
            outcome: json_str_field(line, "outcome").unwrap_or_else(|| panic!("send probe missing outcome")),
            receiver: required_json_u64_field(line, "receiver", "send probe"),
            gift_bytes: required_json_u64_field(line, "gift_bytes", "send probe"),
            gift_blocks: required_json_u64_field(line, "gift_blocks", "send probe"),
        })
        .collect()
}

/// The `gift_roots` of every hit send probe the fixture emits on `path`.
fn hit_gift_roots_for_fixture(fixture: &FixtureCase, path: FixtureMatrixPath, label: &str) -> Vec<usize> {
    telemetry_log_for_fixture(fixture, path, label)
        .lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"runtime\",\"send\",\"probe\"]"))
        .filter(|line| json_str_field(line, "outcome").as_deref() == Some("hit"))
        .map(|line| required_json_u64_field(line, "gift_roots", "send probe"))
        .collect()
}

/// The clause of 01740 binds seven variables: a tuple field, a list cell with
/// its head and tail, and the length, payload and rest of a binary. The cell's
/// head and tail are read out of the cell, so the gift carries five roots: the
/// number, the cell, and the three binary parts.
fn a_hit_gifts_the_roots_a_clause_reads_and_not_one_copy_per_variable() {
    let fixture =
        FixtureCase::new("fixtures/01740_a_receive_clause_reads_its_variables_out_of_the_roots_it_was_gifted.fz");
    for (path, label) in RUNTIME_TELEMETRY_PATHS {
        assert_eq!(
            hit_gift_roots_for_fixture(&fixture, path, label),
            vec![5],
            "{label}: the one gifted hit carries five roots for seven variables"
        );
    }
}

/// One `fz.runtime.alloc_site` event as the jsonl log renders it.
#[derive(Debug, PartialEq, Eq)]
struct AllocSiteEvent {
    function: String,
    object: String,
    allocs: usize,
    bytes: usize,
}

/// Every site the fixture's run reports having placed an object, in emission
/// order.
fn alloc_sites_for_fixture(fixture: &FixtureCase, path: FixtureMatrixPath, label: &str) -> Vec<AllocSiteEvent> {
    telemetry_log_for_fixture(fixture, path, label)
        .lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"runtime\",\"alloc_site\"]"))
        .map(|line| AllocSiteEvent {
            function: json_str_field(line, "function").unwrap_or_else(|| panic!("alloc_site event missing function")),
            object: json_str_field(line, "object").unwrap_or_else(|| panic!("alloc_site event missing object")),
            allocs: required_json_u64_field(line, "allocs", "alloc_site event"),
            bytes: required_json_u64_field(line, "bytes", "alloc_site event"),
        })
        .collect()
}

/// One `fz.runtime.reuse_site` event as the jsonl log renders it.
#[derive(Debug, PartialEq, Eq)]
struct ReuseSiteEvent {
    function: String,
    object: String,
    hits: usize,
    misses: usize,
}

/// Every reuse site a run's log reports, in emission order.
fn reuse_sites_in(log: &str) -> Vec<ReuseSiteEvent> {
    log.lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"runtime\",\"reuse_site\"]"))
        .map(|line| ReuseSiteEvent {
            function: json_str_field(line, "function").unwrap_or_else(|| panic!("reuse_site event missing function")),
            object: json_str_field(line, "object").unwrap_or_else(|| panic!("reuse_site event missing object")),
            hits: required_json_u64_field(line, "hits", "reuse_site event"),
            misses: required_json_u64_field(line, "misses", "reuse_site event"),
        })
        .collect()
}

/// The sites belong to the program, not to the path it took: the ring of
/// actors names the same functions with the same counts when it is compiled and
/// run in one step and when it is built and then run. Compiled code places the
/// ring's frames itself, so some sites are functions of the program and the
/// rest are runtime functions it called.
fn a_programs_allocation_sites_are_reported_on_every_path_and_agree_between_run_and_build() {
    let fixture = FixtureCase::new("fixtures/00570_actor_ring.fz");
    let run = alloc_sites_for_fixture(&fixture, FixtureMatrixPath::Run, "run");
    let built = alloc_sites_for_fixture(&fixture, FixtureMatrixPath::Build, "build");
    assert!(
        run.iter()
            .any(|site| site.object == "continuation" && !site.function.starts_with("runtime::")),
        "the ring's own functions place continuation frames: {run:?}"
    );
    assert!(
        run.iter().any(|site| site.function.starts_with("runtime::")),
        "the ring calls runtime functions that allocate: {run:?}"
    );
    assert_eq!(run, built);

    let interpreted = alloc_sites_for_fixture(&fixture, FixtureMatrixPath::Interp, "interp");
    assert!(
        !interpreted.is_empty() && interpreted.iter().all(|site| site.function.starts_with("runtime::")),
        "an interpreted program has no compiled code, so every site is a runtime function: {interpreted:?}"
    );
}

/// One `fz.runtime.gc` event as the jsonl log renders it.
struct GcEvent {
    pid: usize,
    boundary: String,
    copied_bytes: usize,
}

/// Every collection the fixture reports on `path`, in emission order.
fn gc_events_for_fixture(fixture: &FixtureCase, path: FixtureMatrixPath, label: &str) -> Vec<GcEvent> {
    telemetry_log_for_fixture(fixture, path, label)
        .lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"runtime\",\"gc\"]"))
        .map(|line| GcEvent {
            pid: required_json_u64_field(line, "pid", "gc event"),
            boundary: json_str_field(line, "boundary").unwrap_or_else(|| panic!("gc event missing boundary")),
            copied_bytes: required_json_u64_field(line, "copied_bytes", "gc event"),
        })
        .collect()
}

/// The destructors the fixture's exiting processes report having dispatched.
fn dtors_dispatched_for_fixture(fixture: &FixtureCase, path: FixtureMatrixPath, label: &str) -> usize {
    telemetry_log_for_fixture(fixture, path, label)
        .lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"runtime\",\"process_exited\"]"))
        .map(|line| required_json_u64_field(line, "dtors_dispatched", "process_exited event"))
        .sum()
}

/// The paths whose runtime telemetry the pins compare.
const RUNTIME_TELEMETRY_PATHS: [(FixtureMatrixPath, &str); 3] = [
    (FixtureMatrixPath::Run, "run"),
    (FixtureMatrixPath::Interp, "interp"),
    (FixtureMatrixPath::Build, "build"),
];

/// A resource the heap frees is destroyed by its own fz closure at the next
/// scheduler boundary, whichever path ran the program.
fn a_resource_freed_by_a_collection_runs_its_destructor_once_on_every_path() {
    // The resource is dropped inside `drop_one`, then 20000 list cells are
    // built. The JIT collects while they are built and finds the stub dead; the
    // interpreter, which never yields, is not collected and its exit sweep
    // releases the stub. One destructor either way.
    let midlife = FixtureCase::new(
        "fixtures/00906_a_resource_dropped_mid_run_runs_its_destructor_once_when_a_collection_frees_it.fz",
    );
    let collections = gc_events_for_fixture(&midlife, FixtureMatrixPath::Run, "run");
    assert!(
        collections.iter().any(|event| event.boundary == "yield"),
        "run: the allocation makes the heap due at a yield, before the process exits"
    );
    for (path, label) in RUNTIME_TELEMETRY_PATHS {
        assert_eq!(
            dtors_dispatched_for_fixture(&midlife, path, label),
            1,
            "{label}: the dropped resource's destructor is dispatched once"
        );
    }

    // Three resources are still held when main returns; the exit sweep queues
    // one destructor each.
    let at_exit = FixtureCase::new(
        "fixtures/00907_resources_alive_at_exit_run_their_destructors_when_the_exit_sweep_releases_them.fz",
    );
    for (path, label) in RUNTIME_TELEMETRY_PATHS {
        assert_eq!(
            dtors_dispatched_for_fixture(&at_exit, path, label),
            3,
            "{label}: one destructor per resource held at exit"
        );
    }
}

fn a_send_probes_on_the_sender_and_gifts_its_result_through_the_receivers_in_queue() {
    let matched =
        FixtureCase::new("fixtures/00901_a_matched_reply_is_gifted_by_the_sender_and_grafted_by_the_parent.fz");
    let expected = fs::read_to_string(matched.sidecar_path("expected.txt")).expect("read 00901 expected.txt");
    assert_eq!(
        expected, "[1, 2, 3]\n50000\n",
        "the parent prints the matched reply and finds the whole log in its mailbox"
    );
    let unmatched = FixtureCase::new("fixtures/00902_an_unmatched_message_is_gifted_whole_and_waits_in_the_mailbox.fz");
    let expected = fs::read_to_string(unmatched.sidecar_path("expected.txt")).expect("read 00902 expected.txt");
    assert_eq!(
        expected, ":go\n~c\"\\a\\b\"\n",
        "the parent takes :go first, then the earlier unmatched tuple from its mailbox"
    );

    for (path, label) in RUNTIME_TELEMETRY_PATHS {
        // The 50000-element log misses: the tuple and every cons cell cross
        // as one gift. The reply hits: exactly the three bound cells cross,
        // and the receiver is woken by that one hit.
        let events = send_probe_events_for_fixture(&matched, path, label);
        assert_eq!(
            events,
            vec![
                SendProbeEvent::new("miss", 1, 800_032, 1),
                SendProbeEvent::new("hit", 1, 48, 1),
            ],
            "{label}: one miss gifting the whole log in one block, then one hit gifting three cons cells"
        );
        assert_eq!(
            events.iter().filter(|e| e.outcome == "hit").count(),
            1,
            "{label}: the parent is woken once"
        );

        // The tuple misses and crosses whole; the matching atom binds nothing,
        // so its gift has no block at all.
        let events = send_probe_events_for_fixture(&unmatched, path, label);
        assert_eq!(
            events,
            vec![
                SendProbeEvent::new("miss", 1, 64, 1),
                SendProbeEvent::new("hit", 1, 0, 0)
            ],
            "{label}: the unmatched tuple is gifted whole; the matching atom gifts nothing"
        );

        // The probes say the sender built each gift. The copy site says how
        // many cells were copied in the whole run: exactly the cells those
        // gifts carry, so the receiver copied none of them again.
        assert_eq!(
            copied_list_cells_for_fixture(&matched, path, label),
            50_003,
            "{label}: the log's 50000 cells and the reply's 3 are each copied once"
        );
        assert_eq!(
            copied_list_cells_for_fixture(&unmatched, path, label),
            2,
            "{label}: the unmatched tuple's 2 cells are copied once"
        );
    }
}

/// The list cells deep copies placed during the fixture's run, whichever
/// process made them.
fn copied_list_cells_for_fixture(fixture: &FixtureCase, path: FixtureMatrixPath, label: &str) -> usize {
    alloc_sites_for_fixture(fixture, path, label)
        .iter()
        .filter(|site| site.function == "runtime::copy_list_cell")
        .map(|site| site.allocs)
        .sum()
}

/// In fixture 00901 only the child is ever collected, and only on the path that
/// yields mid-run. The parent is collected on no path: its heap is not due when
/// it parks, and the gifts it grafts afterwards raise its baseline to its fill.
/// (Fixture 00905 pins a collection at a park on every path.)
fn a_matched_reply_fixture_collects_only_the_child_and_only_where_it_yields() {
    let fixture =
        FixtureCase::new("fixtures/00901_a_matched_reply_is_gifted_by_the_sender_and_grafted_by_the_parent.fz");

    // The child yields on its reduction budget while it builds and sends the
    // 50000-element log; a yield collects only when the heap is due, once the
    // child has allocated as many bytes as it held live after its last
    // collection. The log is built one cell per element, so the bytes a
    // quantum allocates are mostly cells that survive, and the child is
    // collected on 3 of its yields. Its exit is not a collection.
    let events = gc_events_for_fixture(&fixture, FixtureMatrixPath::Run, "run");
    let count = |boundary: &str| events.iter().filter(|e| e.boundary == boundary).count();
    assert_eq!(
        (count("yield"), count("park"), count("exit")),
        (3, 0, 0),
        "run: the child's collected yields and nothing else"
    );
    assert!(events.iter().all(|e| e.pid != 1), "run: the parent is never collected");
    assert_eq!(
        events.iter().map(|e| e.copied_bytes).sum::<usize>(),
        512_416,
        "run: the bytes every collection copied"
    );

    // The interpreter charges no reductions, so the child builds and sends its
    // whole log inside one quantum and is never collected.
    let events = gc_events_for_fixture(&fixture, FixtureMatrixPath::Interp, "interp");
    assert!(
        events.is_empty(),
        "interp: no yield mid-run and no parent collection, so nothing is collected"
    );
}

/// The parked receiver's pinned list is a root of the collection that follows
/// its park on every path, so the matcher still finds it.
fn a_receiver_parked_on_a_pinned_list_is_collected_on_every_path_and_still_matches() {
    let fixture =
        FixtureCase::new("fixtures/00905_a_receiver_parked_on_a_pinned_list_is_collected_and_still_matches.fz");
    for (path, label) in RUNTIME_TELEMETRY_PATHS {
        let events = gc_events_for_fixture(&fixture, path, label);
        assert!(
            !events.iter().any(|event| event.pid == 1 && event.boundary == "yield"),
            "{label}: nothing is collected before the parent parks, so its heap is due at the park"
        );
        assert!(
            events
                .iter()
                .any(|event| event.boundary == "park" && event.copied_bytes >= 1_600),
            "{label}: the parked parent is collected with its 100-cell pinned list live"
        );
    }
}

fn a_receive_guard_reading_self_is_decided_by_the_receiver_whoever_runs_the_probe() {
    let fixture =
        FixtureCase::new("fixtures/00904_a_receive_guard_reads_the_receivers_pid_even_when_a_sender_runs_the_probe.fz");
    let expected = fs::read_to_string(fixture.sidecar_path("expected.txt")).expect("read 00904 expected.txt");
    assert_eq!(
        expected, ":carried_the_receivers_pid\n:carried_the_senders_pid\n",
        "the guard accepts the message carrying the receiver's pid; the one carrying the sender's pid waits in the mailbox"
    );
    for (path, label) in RUNTIME_TELEMETRY_PATHS {
        // The child runs the probe, so a guard that asked the matcher's
        // process for `self()` would hit on the first message.
        let events = send_probe_events_for_fixture(&fixture, path, label);
        let outcomes: Vec<_> = events.iter().map(|e| e.outcome.as_str()).collect();
        assert_eq!(
            outcomes,
            vec!["miss", "hit"],
            "{label}: the sender's own pid misses; the receiver's pid hits"
        );
        let blocks: Vec<_> = events.iter().map(|e| e.gift_blocks).collect();
        assert_eq!(
            blocks,
            vec![1, 0],
            "{label}: the miss gifts the message in one block; the hit binds only the atom `label`, since the guard reads `who` from the message and the body never does"
        );
    }
}

fn a_receiver_left_parked_with_queued_gifts_drops_them_at_teardown() {
    let fixture = FixtureCase::new("fixtures/00903_a_receiver_left_parked_with_queued_gifts_drops_them_at_teardown.fz");
    let expected = fs::read_to_string(fixture.sidecar_path("expected.txt")).expect("read 00903 expected.txt");
    assert_eq!(
        expected, ":child_is_parked\n:done\n",
        "the run prints both lines and ends with the child still parked"
    );
    for (path, label) in RUNTIME_TELEMETRY_PATHS {
        let events = send_probe_events_for_fixture(&fixture, path, label);
        let misses_for_the_child: Vec<_> = events
            .iter()
            .filter(|e| e.outcome == "miss" && e.receiver == 2)
            .collect();
        // Each gift is measured first and occupies one block: the tuple and
        // its 1000 cells (32 + 1000 * 16), the tuple and its two cells
        // (32 + 2 * 16), and one atom, which is its own ref and takes no block.
        assert_eq!(
            misses_for_the_child,
            vec![
                &SendProbeEvent::new("miss", 2, 16_032, 1),
                &SendProbeEvent::new("miss", 2, 64, 1),
                &SendProbeEvent::new("miss", 2, 0, 0),
            ],
            "{label}: all three messages are probed and gifted to the parked child, which never grafts them; each holds one exactly sized block that teardown must return"
        );
        assert_eq!(
            events.iter().filter(|e| e.outcome == "hit").count(),
            1,
            "{label}: only the child's announcement wakes anyone"
        );
        let (before, after) = run_ended_pool_census(&fixture, path, label);
        assert_eq!(
            after, before,
            "{label}: the run returned every block it took, including the gifts still queued on the parked child"
        );
    }
}

/// A long body's steps share one frame. A collection keeps the frame in an
/// old block, and the next step's write into it would name a young object from
/// an object no minor collection looks inside, so the write goes to a copy at
/// the heap tip. The fixture's twenty calls each build and drop a
/// thirty-thousand-element list, so collections run while the frame is live.
/// A clause loop charges one reduction per step, so collections fall every
/// 4,000 steps, and three of them find the frame old: three copies. Which
/// collections find it old depends on the step of the body each one falls at.
/// The interpreter has no frames and copies none.
fn a_long_body_copies_its_frame_forward_when_a_collection_kept_it() {
    let fixture = FixtureCase::new("fixtures/01254_a_long_body_copies_its_frame_forward_when_a_collection_kept_it.fz");
    for (path, label, copies) in [
        (FixtureMatrixPath::Run, "run", 3),
        (FixtureMatrixPath::Build, "build", 3),
        (FixtureMatrixPath::Interp, "interp", 0),
    ] {
        assert_eq!(
            frame_copies_for_fixture(&fixture, path, label),
            copies,
            "{label}: body frames copied to the tip"
        );
    }
}

/// The body frame holds a forty-thousand-element list until the step
/// that measures it, and the step after clears the slot. The collections that
/// follow copy what the program still uses and not the list: neither of the
/// last two copies more than 48,512 bytes, cells of a three-thousand-element
/// list of `g`'s and little else. Collections fall every 4,000 steps of a
/// clause loop's one reduction each, so that is where the last two land. When
/// the program's last expression still reads the list, the collection after it
/// copies the list's young cells too: 656,432 bytes.
fn a_list_the_body_no_longer_uses_is_not_kept_by_its_frame() {
    let fixture = FixtureCase::new("fixtures/01256_a_list_the_body_no_longer_uses_is_not_kept_by_its_frame.fz");
    for (path, label) in [(FixtureMatrixPath::Run, "run"), (FixtureMatrixPath::Build, "build")] {
        let events = gc_events_for_fixture(&fixture, path, label);
        let tail = &events[events.len().saturating_sub(2)..];
        assert_eq!(
            tail.iter().map(|e| e.copied_bytes).max(),
            Some(48_512),
            "{label}: the most bytes one of the last two collections copied"
        );
    }
}

/// The body frames the fixture's exiting processes report having copied to the
/// heap tip.
fn frame_copies_for_fixture(fixture: &FixtureCase, path: FixtureMatrixPath, label: &str) -> usize {
    telemetry_log_for_fixture(fixture, path, label)
        .lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"runtime\",\"process_exited\"]"))
        .map(|line| required_json_u64_field(line, "frame_copies", "process_exited event"))
        .sum()
}

/// `(pid, boundary, copied_bytes)` of every collection, in emission order.
fn collections_as_tuples(events: &[GcEvent]) -> Vec<(usize, &str, usize)> {
    events
        .iter()
        .map(|event| (event.pid, event.boundary.as_str(), event.copied_bytes))
        .collect()
}

fn many_senders_into_one_guarded_receive_gift_one_message_each_and_leave_the_misses_queued() {
    let fixture = FixtureCase::new(
        "fixtures/00910_many_senders_into_one_guarded_receive_gift_one_message_each_and_leave_the_misses_queued.fz",
    );
    let expected = fs::read_to_string(fixture.sidecar_path("expected.txt")).expect("read 00910 expected.txt");
    assert_eq!(
        expected, "11375\n3875\n",
        "the parent sums jobs 51..=100 then jobs 1..=50, each as the job number plus its two-element payload sum"
    );

    // The guard accepts jobs above 50, so jobs 1..=50 miss, job 51 hits, and
    // the receive is then decided: jobs 52..=100 miss without a second probe.
    // A miss gifts the whole message (a three-slot tuple, 48 bytes, and two
    // cells, 32); the hit gifts the two payload cells (32), the bound number
    // crossing as its word and kind with no block.
    let mut probes = vec![SendProbeEvent::new("miss", 1, 80, 1); 50];
    probes.push(SendProbeEvent::new("hit", 1, 32, 1));
    probes.extend(vec![SendProbeEvent::new("miss", 1, 80, 1); 49]);
    for (path, label) in RUNTIME_TELEMETRY_PATHS {
        let events = send_probe_events_for_fixture(&fixture, path, label);
        assert_eq!(
            events, probes,
            "{label}: fifty misses, the one hit, then forty-nine misses"
        );
        assert_eq!(
            events.iter().map(|e| e.gift_bytes).sum::<usize>(),
            7_952,
            "{label}: 99 misses of 80 bytes and one hit of 32"
        );
        let (before, after) = run_ended_pool_census(&fixture, path, label);
        assert_eq!(
            after, before,
            "{label}: the run returned every block it took, queued gifts included"
        );
    }

    // The interpreter collects the parent once, as it parks (32 bytes live).
    // The JIT collects it once as it parks (304 bytes, which include the
    // closures its park record holds); the parent's exit after grafting 99
    // gifts is not a collection. Neither path collects a child.
    let events = gc_events_for_fixture(&fixture, FixtureMatrixPath::Interp, "interp");
    assert_eq!(
        collections_as_tuples(&events),
        vec![(1, "park", 32)],
        "interp: the parent's park only"
    );
    let events = gc_events_for_fixture(&fixture, FixtureMatrixPath::Run, "run");
    assert_eq!(
        collections_as_tuples(&events),
        vec![(1, "park", 304)],
        "run: the parent's park only; its exit is not collected"
    );
}

fn a_large_list_passed_back_and_forth_crosses_as_one_gift_per_message_on_every_path() {
    let fixture = FixtureCase::new(
        "fixtures/00911_two_processes_pass_a_large_list_back_and_forth_and_each_message_crosses_in_one_gift.fz",
    );
    let expected = fs::read_to_string(fixture.sidecar_path("expected.txt")).expect("read 00911 expected.txt");
    assert_eq!(
        expected, ":child_is_parked\n4\n20000\n200010000\n",
        "four rounds, and the list the parent ends with is the 20000 elements it began with"
    );

    // Every send finds its receiver parked on a matching receive, so every
    // message is a hit. The child's announcement binds nothing and gifts
    // nothing. Each ball gifts its 20000 cells (320000 bytes), the bound
    // number crossing as its word and kind with no block, alternating child,
    // parent.
    let ball = |receiver| SendProbeEvent::new("hit", receiver, 320_000, 1);
    let mut probes = vec![SendProbeEvent::new("hit", 1, 0, 0)];
    for _ in 0..4 {
        probes.push(ball(2));
        probes.push(ball(1));
    }
    for (path, label) in RUNTIME_TELEMETRY_PATHS {
        let events = send_probe_events_for_fixture(&fixture, path, label);
        assert_eq!(events, probes, "{label}: the announcement, then eight balls, all hits");
        assert_eq!(
            events.iter().map(|e| e.gift_bytes).sum::<usize>(),
            2_560_000,
            "{label}: eight balls of 320000 bytes"
        );
        let (before, after) = run_ended_pool_census(&fixture, path, label);
        assert_eq!(after, before, "{label}: the run returned every block it took");
    }

    // A ball waits outside the receiver's heap until the receive that takes it
    // grafts it, young. At 320000 bytes a ball is far past the 4096-byte budget
    // floor, so the receiver is due at the park that follows each receive, and
    // the ball, dead by then, is reclaimed with nothing copied. The interpreter
    // never yields, so every one of its collections is at a park: the parent's
    // for the announcement, then one per ball taken. The JIT yields while the
    // parent builds the list: a clause loop charges one reduction per step, so a
    // yield falls every 4,000 steps, and it collects only when the heap is due.
    // Each minor collection copies what was allocated since the last one;
    // those whose old bytes passed twice what the last major collection left
    // are major and copy everything live. A park copies the closures its park
    // record holds.
    let events = gc_events_for_fixture(&fixture, FixtureMatrixPath::Interp, "interp");
    assert_eq!(
        collections_as_tuples(&events),
        vec![
            (1, "park", 0),
            (2, "park", 0),
            (1, "park", 0),
            (2, "park", 0),
            (1, "park", 0),
            (2, "park", 0),
            (1, "park", 0),
        ],
        "interp: the parent's park for the announcement, then the park after each ball a process took, with nothing live"
    );
    let events = gc_events_for_fixture(&fixture, FixtureMatrixPath::Run, "run");
    assert_eq!(
        collections_as_tuples(&events),
        vec![
            // Each entry's call of its body returns to a 32-byte continuation, live in the
            // parent's collections that copy its oldest values.
            (1, "yield", 64_144),
            (1, "yield", 192_144),
            (2, "park", 320),
            (1, "park", 208),
            (2, "park", 192),
            (1, "park", 144),
            (2, "park", 192),
            (1, "park", 144),
            (1, "yield", 288_128),
        ],
        "run: the parent's collected yields and each park that follows a ball taken"
    );
}

/// The built binary reports what the scheduler does exactly as `fz2 run` does:
/// the same probes with the same gifts, the same collections, and the same
/// destructors dispatched at each exit.
fn a_built_binary_reports_the_same_probes_collections_and_destructors_as_run() {
    for fixture in [
        "fixtures/00901_a_matched_reply_is_gifted_by_the_sender_and_grafted_by_the_parent.fz",
        "fixtures/00910_many_senders_into_one_guarded_receive_gift_one_message_each_and_leave_the_misses_queued.fz",
        "fixtures/00911_two_processes_pass_a_large_list_back_and_forth_and_each_message_crosses_in_one_gift.fz",
        "fixtures/00906_a_resource_dropped_mid_run_runs_its_destructor_once_when_a_collection_frees_it.fz",
        "fixtures/00907_resources_alive_at_exit_run_their_destructors_when_the_exit_sweep_releases_them.fz",
    ] {
        let fixture = FixtureCase::new(fixture);
        let name = fixture.display_path().display().to_string();
        let (run, build) = (FixtureMatrixPath::Run, FixtureMatrixPath::Build);
        assert_eq!(
            send_probe_events_for_fixture(&fixture, build, "build"),
            send_probe_events_for_fixture(&fixture, run, "run"),
            "{name}: build probes the same sends with the same gifts as run"
        );
        let built = gc_events_for_fixture(&fixture, build, "build");
        let ran = gc_events_for_fixture(&fixture, run, "run");
        assert_eq!(
            collections_as_tuples(&built),
            collections_as_tuples(&ran),
            "{name}: build collects the same pids at the same boundaries copying the same bytes as run"
        );
        assert_eq!(
            dtors_dispatched_by_pid(&fixture, build, "build"),
            dtors_dispatched_by_pid(&fixture, run, "run"),
            "{name}: build dispatches the same destructors per process as run"
        );
    }
}

/// One receive-after timer event as the jsonl log renders it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TimerEvent {
    Armed {
        timer: usize,
        pid: usize,
        armed_ns: usize,
        deadline_ns: usize,
    },
    Fired {
        timer: usize,
        pid: usize,
    },
    Cancelled {
        timer: usize,
        pid: usize,
    },
}

fn timer_events_for_fixture(fixture: &FixtureCase, path: FixtureMatrixPath, label: &str) -> Vec<TimerEvent> {
    telemetry_log_for_fixture(fixture, path, label)
        .lines()
        .filter_map(|line| {
            let timer = || required_json_u64_field(line, "timer", "timer event");
            let pid = || required_json_u64_field(line, "pid", "timer event");
            if line.contains("\"name\":[\"fz\",\"runtime\",\"timer\",\"armed\"]") {
                let armed_ns = required_json_u64_field(line, "armed_ns", "timer armed event");
                let deadline_ns = required_json_u64_field(line, "deadline_ns", "timer armed event");
                Some(TimerEvent::Armed {
                    timer: timer(),
                    pid: pid(),
                    armed_ns,
                    deadline_ns,
                })
            } else if line.contains("\"name\":[\"fz\",\"runtime\",\"timer\",\"fired\"]") {
                Some(TimerEvent::Fired {
                    timer: timer(),
                    pid: pid(),
                })
            } else if line.contains("\"name\":[\"fz\",\"runtime\",\"timer\",\"cancelled\"]") {
                Some(TimerEvent::Cancelled {
                    timer: timer(),
                    pid: pid(),
                })
            } else {
                None
            }
        })
        .collect()
}

fn armed_timers(events: &[TimerEvent]) -> Vec<(usize, usize, usize)> {
    events
        .iter()
        .filter_map(|event| match *event {
            TimerEvent::Armed {
                timer,
                pid,
                deadline_ns,
                ..
            } => Some((timer, pid, deadline_ns)),
            _ => None,
        })
        .collect()
}

fn fired_timers(events: &[TimerEvent]) -> Vec<usize> {
    events
        .iter()
        .filter_map(|event| match *event {
            TimerEvent::Fired { timer, .. } => Some(timer),
            _ => None,
        })
        .collect()
}

fn cancelled_timers(events: &[TimerEvent]) -> Vec<usize> {
    events
        .iter()
        .filter_map(|event| match *event {
            TimerEvent::Cancelled { timer, .. } => Some(timer),
            _ => None,
        })
        .collect()
}

/// The one timer armed was armed for exactly `requested_ns`: its deadline is
/// its arm time plus the timeout the receive asked for.
fn assert_armed_for_exactly(events: &[TimerEvent], requested_ns: usize, label: &str) {
    let [
        TimerEvent::Armed {
            armed_ns, deadline_ns, ..
        },
        ..,
    ] = events[..]
    else {
        panic!("{label}: the first timer event is an arming: {events:?}");
    };
    assert_eq!(
        deadline_ns - armed_ns,
        requested_ns,
        "{label}: the timer is armed with its full deadline: {events:?}"
    );
}

/// Every armed timer fires, and in the order of the deadlines the runtime
/// reported when it armed them. The deadlines are the runtime's own, so the
/// claim holds however long the machine stalled between the two arms.
fn assert_timers_fire_in_deadline_order(events: &[TimerEvent], expected_timers: usize, label: &str) {
    let mut by_deadline = armed_timers(events);
    assert_eq!(by_deadline.len(), expected_timers, "{label}: timers armed: {events:?}");
    by_deadline.sort_by_key(|&(timer, _, deadline_ns)| (deadline_ns, timer));
    assert_eq!(
        fired_timers(events),
        by_deadline.iter().map(|&(timer, _, _)| timer).collect::<Vec<_>>(),
        "{label}: timers fire nearest deadline first: {events:?}"
    );
    assert!(
        cancelled_timers(events).is_empty(),
        "{label}: no timer is cancelled: {events:?}"
    );
}

/// A receive-after timer is armed with a deadline and then either fires or is
/// cancelled by the message that wakes its process; when several are pending,
/// they fire nearest deadline first. Read from the event stream of each path,
/// so no assertion waits on, or races, a clock.
fn a_receive_timer_is_armed_then_fired_or_cancelled_and_fires_in_deadline_order_on_every_path() {
    let fixture = |name| FixtureCase::new(name);
    let lone = fixture("fixtures/00687_a_receive_after_times_out_with_an_empty_mailbox.fz");
    let cancelled = fixture("fixtures/00692_a_message_that_arrives_first_cancels_the_timeout.fz");
    let late = fixture("fixtures/00690_a_late_message_beats_a_long_timeout.fz");
    let staggered = fixture("fixtures/00693_two_staggered_timeouts_each_wake_their_own_process.fz");
    let nested = fixture("fixtures/00691_a_child_and_its_parent_both_time_out_in_order.fz");
    for (path, label) in RUNTIME_TELEMETRY_PATHS {
        let events = timer_events_for_fixture(&lone, path, label);
        assert!(
            matches!(
                events[..],
                [TimerEvent::Armed { timer: armed, pid: 1, .. }, TimerEvent::Fired { timer: fired, pid: 1 }] if armed == fired
            ),
            "{label}: the lone timeout is armed by main and then fires: {events:?}"
        );

        assert_armed_for_exactly(&events, 1_000_000, label);

        let events = timer_events_for_fixture(&cancelled, path, label);
        assert!(
            matches!(
                events[..],
                [TimerEvent::Armed { timer: armed, pid: 1, .. }, TimerEvent::Cancelled { timer: gone, pid: 1 }] if armed == gone
            ),
            "{label}: the message that arrives first cancels main's timer and nothing fires: {events:?}"
        );
        assert_armed_for_exactly(&events, 60_000_000_000, label);

        let events = timer_events_for_fixture(&late, path, label);
        let armed = armed_timers(&events);
        assert_eq!(
            armed.len(),
            2,
            "{label}: main's long timer and the child's short one: {events:?}"
        );
        let (parent_timer, _, parent_deadline) =
            *armed.iter().find(|&&(_, pid, _)| pid == 1).expect("main armed a timer");
        let (child_timer, _, child_deadline) = *armed
            .iter()
            .find(|&&(_, pid, _)| pid != 1)
            .expect("child armed a timer");
        assert!(
            child_deadline < parent_deadline,
            "{label}: the child's timer is the nearer: {events:?}"
        );
        assert_eq!(
            fired_timers(&events),
            vec![child_timer],
            "{label}: only the child's timer fires: {events:?}"
        );
        assert_eq!(
            cancelled_timers(&events),
            vec![parent_timer],
            "{label}: the late message cancels main's: {events:?}"
        );

        assert_timers_fire_in_deadline_order(&timer_events_for_fixture(&staggered, path, label), 2, label);
        assert_timers_fire_in_deadline_order(&timer_events_for_fixture(&nested, path, label), 2, label);
    }
}

/// `(pid, dtors_dispatched)` of every exit, in emission order.
fn dtors_dispatched_by_pid(fixture: &FixtureCase, path: FixtureMatrixPath, label: &str) -> Vec<(usize, usize)> {
    telemetry_log_for_fixture(fixture, path, label)
        .lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"runtime\",\"process_exited\"]"))
        .map(|line| {
            (
                required_json_u64_field(line, "pid", "process_exited event"),
                required_json_u64_field(line, "dtors_dispatched", "process_exited event"),
            )
        })
        .collect()
}

/// `(pool_outstanding_before_run, pool_outstanding_after_run)` from the one
/// `fz.runtime.run_ended` event the fixture's run emits on `path`.
fn run_ended_pool_census(fixture: &FixtureCase, path: FixtureMatrixPath, label: &str) -> (usize, usize) {
    let header = parse_header(fixture).unwrap_or_else(|error| panic!("parse fixture header: {error}"));
    let (out, log) =
        run_path_logged(fixture, &header, path).unwrap_or_else(|e| panic!("fz2 {label} --log-telemetry: {}", e));
    assert!(out.status.success(), "fz2 {label} exited {}", out.status);
    let ended: Vec<&str> = log
        .lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"runtime\",\"run_ended\"]"))
        .collect();
    assert_eq!(ended.len(), 1, "{label}: exactly one run_ended event");
    (
        required_json_u64_field(ended[0], "pool_outstanding_before_run", "run_ended"),
        required_json_u64_field(ended[0], "pool_outstanding_after_run", "run_ended"),
    )
}

fn assert_fixture_output_contains(fixture: &str, file: &str, needles: &[&str]) {
    let path = FixtureCase::new(fixture).sidecar_path(file);
    let expected = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
    for needle in needles {
        assert!(
            expected.contains(needle),
            "{} must pin `{}`:\n{}",
            path.display(),
            needle,
            expected
        );
    }
}
