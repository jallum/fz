//! fz-ul4.23.1 — fixture matrix.
//!
//! Walks `fixtures2/behavior/*.fz` and runs each source program through the
//! compiler2 behavioural matrix. Behavioural metadata and optional prose live in a
//! comment-frontmatter block at the top of the source file, and sibling
//! sidecars carry the few artifacts that really need to stay out of the
//! program itself. stdout is compared against `expected.txt`;
//! diagnostics/stderr are compared against `expected.<path>.diagnostics` or
//! `expected.diagnostics`. Both default to empty when absent. Exit code must be
//! 0 unless the fixture declares a negative `expect:` contract.
//!
//! Single-file fixtures2 layout:
//!
//!     fixtures2/behavior/<name>.fz
//!     fixtures2/behavior/<name>.expected.txt
//!     fixtures2/behavior/<name>.expected.run.txt
//!     fixtures2/behavior/<name>.expected.diagnostics
//!     fixtures2/behavior/<name>.expected.run.diagnostics
//!     fixtures2/behavior/<name>.expected.stderr
//!     fixtures2/behavior/<name>.oracle.exs
//!
//! Frontmatter grammar:
//!
//!     #---
//!     purpose: one-line statement of what this fixture proves
//!     kind: run            # or `test`; defaults to run if `fn main` present
//!     expect: success      # or `abort` (run-time) / `diagnostic` (compile-time)
//!     diagnostic.code: spec/violation  # for telemetry-backed diagnostic fixtures
//!     defer: rationale     # optional whole-fixture deferral
//!     defer.build: rationale  # optional per-path deferral
//!     oracle: oracle.exs   # Elixir twin: its stdout owns expected.txt
//!     timeout.interp_secs: 15  # path-specific timeout override
//!     #---
//!
//! Behavioural routes default to `run`, `interp`, and `build`. A fixture may
//! narrow that set with a filename prefix such as `a-resource_dtor.fz` or
//! `00001_ja-some_fixture.fz`; `j` means `run`, `i` means `interp`, and `a`
//! means `build`.
//!
//! When `oracle:` is set, the `oracle_goldens_match_elixir` static test runs the
//! named Elixir program under the real `elixir` binary and asserts its stdout
//! equals `expected.txt` (and owns it under `BLESS=1`). The per-path matrix
//! trials independently assert each fz path reproduces that same golden, so
//! `fz == Elixir` holds transitively. Elixir owns the golden — per-path bless
//! never rewrites `expected.txt` for an oracle fixture.
//!
//! `expect: success` (the default) requires exit 0 with matching stdout/diagnostics.
//! `expect: abort` flips the contract: the program must exit nonzero and its
//! stderr must contain the `expected.stderr` golden as a substring. `expect:
//! diagnostic` checks the emitted `[fz, diag, error]` telemetry code.
//!
//! Workflow: re-run with `BLESS=1 cargo test fixture_matrix` to rewrite
//! `expected.txt` / `expected.<path>.txt` and `expected.diagnostics` from current output. On
//! failure (non-bless), actual output is dropped at sibling
//! `<name>.actual.txt` and `<name>.actual.diagnostics` for diffing.
//! Compiler-shape contracts live in compiler2 telemetry and fixture metadata.

use fz::compiler2::{
    FixtureExpect as Fixture2Expect, FixtureKind as Fixture2Kind, FixtureMatrixPath, FixtureMetadata,
    fixture_matrix_paths_from_filename, parse_fixture_metadata,
};
use libtest_mimic::{Arguments, Failed, Trial};
use std::env::{temp_dir, var};
use std::fs::{self, remove_file};
use std::io::Error;
use std::os::fd::RawFd;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio, id};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread::sleep;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");
const FZ_EXEC_READY_FD_ENV: &str = "FZ_EXEC_READY_FD";
const FIXTURE_COMMAND_TIMEOUT: Duration = Duration::from_secs(3);
static AOT_TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

// fz-fkv — custom main: each (fixture, path) pair becomes its own
// `cargo test` trial, named `matrix::<fixture>::<path>`. `cargo test add1`
// filters to one fixture; `cargo test ::build` filters to one leg. Static
// invariant tests (CLIF shape, golden dumps, etc.) become trials too so
// the harness is uniform.
fn main() {
    let mut args = Arguments::from_args();
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
        ("fixtures2_single_file_matrix_smoke", fixtures2_single_file_matrix_smoke),
        (
            "behavior_fixtures_route_via_filename_not_paths_frontmatter",
            behavior_fixtures_route_via_filename_not_paths_frontmatter,
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
            "interpreter_stepper_does_not_update_quiet_quanta",
            interpreter_stepper_does_not_update_quiet_quanta,
        ),
        ("oracle_goldens_match_elixir", oracle_goldens_match_elixir),
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
fn main() do\n\
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

fn behavior_fixtures_route_via_filename_not_paths_frontmatter() {
    for entry in fs::read_dir("fixtures2/behavior").expect("read behaviour fixtures") {
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
/// Abort fixtures pin stderr; diagnostic fixtures pin the telemetry diagnostic
/// code so rendered wording can improve without changing the semantic oracle.
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
    path_timeouts: Vec<(FixtureMatrixPath, Duration)>,
}

impl Header {
    fn timeout_for_path(&self, path: FixtureMatrixPath) -> Duration {
        self.path_timeouts
            .iter()
            .find_map(|(timeout_path, timeout)| (*timeout_path == path).then_some(*timeout))
            .unwrap_or(FIXTURE_COMMAND_TIMEOUT)
    }

    fn defer_for_path(&self, path: FixtureMatrixPath) -> Option<&str> {
        self.path_deferrals
            .iter()
            .find_map(|(deferred_path, rationale)| (*deferred_path == path).then_some(rationale.as_str()))
    }
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

    fn source_path(&self) -> PathBuf {
        self.path.clone()
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
        if rel == "oracle.exs" {
            return self.sidecar_path(rel);
        }
        self.source_dir().join(rel)
    }

    fn canonical_source_name(&self) -> String {
        format!("fixtures2/behavior/{}.fz", self.name())
    }

    fn normalize_expected_diagnostics(&self, text: &str) -> String {
        let text = text.replace(self.path.to_string_lossy().as_ref(), &self.canonical_source_name());
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

fn behavior_fixture_path(name: &str) -> PathBuf {
    PathBuf::from("fixtures2/behavior").join(format!("{name}.fz"))
}

fn behavior_fixture_case(name: &str) -> FixtureCase {
    FixtureCase::new(behavior_fixture_path(name))
}

fn behavior_fixture_sidecar_path(name: &str, suffix: &str) -> PathBuf {
    behavior_fixture_case(name).sidecar_path(suffix)
}

fn take_ascii_digits(bytes: &[u8], mut index: usize) -> usize {
    while index < bytes.len() && bytes[index].is_ascii_digit() {
        index += 1;
    }
    index
}

fn has_main(src: &str) -> bool {
    src.lines().any(|l| l.contains("fn main(") || l.contains("fn main "))
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
        path_timeouts,
    })
}

/// Discover behavioural fixtures under the unified fixtures2 corpus.
fn discover() -> Vec<FixtureCase> {
    let behavior_dir = Path::new("fixtures2/behavior");
    let mut out: Vec<FixtureCase> = fs::read_dir(behavior_dir)
        .expect("fixtures2/behavior should exist")
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
    success: bool,
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
        return Err(format!("pipe {}: {}", FZ_EXEC_READY_FD_ENV, Error::last_os_error()));
    }
    let flags = unsafe { libc::fcntl(fds[0], libc::F_GETFL) };
    if flags < 0 {
        close_fd(fds[0]);
        close_fd(fds[1]);
        return Err(format!("fcntl {}: {}", FZ_EXEC_READY_FD_ENV, Error::last_os_error()));
    }
    let rc = unsafe { libc::fcntl(fds[0], libc::F_SETFL, flags | libc::O_NONBLOCK) };
    if rc != 0 {
        close_fd(fds[0]);
        close_fd(fds[1]);
        return Err(format!(
            "fcntl nonblock {}: {}",
            FZ_EXEC_READY_FD_ENV,
            Error::last_os_error()
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
    let err = Error::last_os_error();
    match err.raw_os_error() {
        Some(code) if code == libc::EAGAIN || code == libc::EINTR => Ok(false),
        _ => Err(format!("read {}: {}", FZ_EXEC_READY_FD_ENV, err)),
    }
}

fn fixture_command_output(
    cmd: &mut Command,
    label: &str,
    timeout_start: TimeoutStart,
    timeout: Duration,
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
                return child.wait_with_output().map_err(|e| format!("wait {}: {}", label, e));
            }
            Ok(None) if start.map(|started| started.elapsed() >= timeout).unwrap_or(false) => {
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
                    timeout,
                    stderr.trim_end()
                ));
            }
            Ok(None) => sleep(Duration::from_millis(10)),
            Err(e) => {
                if let Some(read_fd) = ready_read_fd.take() {
                    close_fd(read_fd);
                }
                return Err(format!("wait {}: {}", label, e));
            }
        }
    }
}

fn run_path(fixture: &FixtureCase, header: &Header, path: FixtureMatrixPath) -> RunOutcome {
    let subcmd = match (path, header.kind) {
        (FixtureMatrixPath::Run, Kind::Run) => "run",
        (FixtureMatrixPath::Run, Kind::Test) => "test",
        (FixtureMatrixPath::Interp, _) => "interp",
        (FixtureMatrixPath::Build, _) => return run_fz2_build_path(fixture, header),
    };
    let input = fixture.source_path();
    let out = match fixture_command_output(
        Command::new(FZ2_BIN).arg(subcmd).arg(&input),
        "fz2",
        TimeoutStart::OnExecutionReady,
        header.timeout_for_path(path),
    ) {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(e),
    };
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    RunOutcome::Ran(Ran {
        success: out.status.success(),
        stdout: String::from_utf8_lossy(&out.stdout).to_string(),
        diagnostics: stderr,
    })
}

fn run_fz2_build_path(fixture: &FixtureCase, header: &Header) -> RunOutcome {
    if header.kind == Kind::Test {
        return RunOutcome::Deferred("kind: test fixtures don't yet run via build".into());
    }
    let stem = fixture.name();
    let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let out_path = temp_dir().join(format!("fz2_matrix_{}_{}_{}", stem, id(), nonce));
    let input = fixture.source_path();
    let build = match Command::new(FZ2_BIN)
        .args(["build"])
        .arg(&input)
        .args(["-o"])
        .arg(&out_path)
        .output()
    {
        Ok(o) => o,
        Err(e) => return RunOutcome::Failed(format!("spawn fz2 build: {}", e)),
    };
    let build_stderr = String::from_utf8_lossy(&build.stderr).to_string();
    if header.expect == Expect::Diagnostic {
        return RunOutcome::Ran(Ran {
            success: build.status.success(),
            stdout: String::from_utf8_lossy(&build.stdout).to_string(),
            diagnostics: build_stderr,
        });
    }
    if !build.status.success() {
        remove_fz2_build_outputs(&out_path);
        return RunOutcome::Failed(format!("fz2 build exit {}: {}", build.status, build_stderr.trim_end()));
    }
    let run = match fixture_command_output(
        &mut Command::new(&out_path),
        "fz2-built binary",
        TimeoutStart::OnSpawn,
        header.timeout_for_path(FixtureMatrixPath::Build),
    ) {
        Ok(o) => o,
        Err(e) => {
            remove_fz2_build_outputs(&out_path);
            return RunOutcome::Failed(e);
        }
    };
    remove_fz2_build_outputs(&out_path);
    let run_stderr = String::from_utf8_lossy(&run.stderr).to_string();
    let diagnostics = format!("{}{}", build_stderr, run_stderr);
    RunOutcome::Ran(Ran {
        success: run.status.success(),
        stdout: String::from_utf8_lossy(&run.stdout).to_string(),
        diagnostics,
    })
}

fn remove_fz2_build_outputs(out_path: &Path) {
    let _ = remove_file(out_path);
    let _ = remove_file(out_path.with_extension("o"));
    let _ = remove_file(out_path.with_extension("bin.o"));
}

fn normalize(s: &str) -> String {
    if s.is_empty() || s.ends_with('\n') {
        s.to_string()
    } else {
        format!("{}\n", s)
    }
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
    if !ran.success {
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
    if actual == expected && actual_diagnostics == expected_diagnostics {
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
    if ran.success {
        return CheckOutcome::Fail(format!(
            "{} via {}: expected {} (nonzero exit) but the program exited 0",
            fixture.display_path().display(),
            path_id,
            kind
        ));
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

fn check_diagnostic_telemetry(
    fixture: &FixtureCase,
    header: &Header,
    path: FixtureMatrixPath,
    expected_code: &str,
) -> CheckOutcome {
    let telemetry_path = temp_telemetry_path(fixture, "diagnostic");
    let out = match run_path_logged(fixture, header, path, &telemetry_path) {
        Ok(out) => out,
        Err(e) => return CheckOutcome::Fail(e),
    };
    let log =
        fs::read_to_string(&telemetry_path).unwrap_or_else(|e| panic!("read {}: {}", telemetry_path.display(), e));
    let _ = fs::remove_file(&telemetry_path);
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
    telemetry_path: &Path,
) -> Result<Output, String> {
    if path == FixtureMatrixPath::Build {
        let stem = fixture.name();
        let nonce = AOT_TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let out_path = temp_dir().join(format!("fz2_matrix_diag_{}_{}_{}", stem, id(), nonce));
        let out = fixture_command_output(
            Command::new(FZ2_BIN)
                .args(["--log-telemetry"])
                .arg(telemetry_path)
                .args(["build"])
                .arg(fixture.source_path())
                .args(["-o"])
                .arg(&out_path),
            "fz2 build --log-telemetry",
            TimeoutStart::OnSpawn,
            header.timeout_for_path(path),
        );
        remove_fz2_build_outputs(&out_path);
        return out;
    }
    let input = fixture.source_path();
    let mut cmd = Command::new(FZ2_BIN);
    cmd.args(["--log-telemetry"]).arg(telemetry_path);
    match (path, header.kind) {
        (FixtureMatrixPath::Run, Kind::Run) => {
            cmd.arg("run").arg(input);
        }
        (FixtureMatrixPath::Run, Kind::Test) => {
            cmd.arg("test").arg(input);
        }
        (FixtureMatrixPath::Interp, _) => {
            cmd.arg("interp").arg(input);
        }
        (FixtureMatrixPath::Build, _) => unreachable!("build returns above"),
    }
    fixture_command_output(
        &mut cmd,
        "fz2 --log-telemetry",
        TimeoutStart::OnExecutionReady,
        header.timeout_for_path(path),
    )
}

/// fz-g58.1 — Elixir oracle. For every fixture that declares `oracle: <file>.exs`,
/// the canonical `expected.txt` golden must equal the stdout of running that
/// Elixir twin under the real `elixir` binary. This makes "matches Elixir" a
/// mechanical diff rather than a hand-authored claim: Elixir owns the golden,
/// and the per-path matrix trials independently assert each compiler2 path
/// reproduces the same `expected.txt` — so `fz == Elixir` holds transitively.
///
/// `BLESS=1` regenerates `expected.txt` from the Elixir output. Requires the
/// `elixir` binary on PATH (Elixir 1.19+); a spawn failure fails loudly by
/// design — the oracle is the signal, so a missing oracle is a hard error, not
/// a skip.
fn oracle_goldens_match_elixir() {
    let bless = var("BLESS").ok().as_deref() == Some("1");
    let mut failures: Vec<String> = Vec::new();
    for fixture in discover() {
        let header = match parse_header(&fixture) {
            Ok(h) => h,
            Err(_) => continue,
        };
        let Some(oracle_rel) = header.oracle.as_deref() else {
            continue;
        };
        let oracle_path = fixture.oracle_path(oracle_rel);
        if !oracle_path.is_file() {
            failures.push(format!(
                "{}: oracle `{}` not found",
                fixture.display_path().display(),
                oracle_path.display()
            ));
            continue;
        }
        let out = match Command::new("elixir").arg(&oracle_path).output() {
            Ok(o) => o,
            Err(e) => {
                failures.push(format!(
                    "{}: spawn `elixir {}`: {} (is Elixir installed and on PATH?)",
                    fixture.display_path().display(),
                    oracle_path.display(),
                    e
                ));
                continue;
            }
        };
        if !out.status.success() {
            failures.push(format!(
                "{}: `elixir {}` exited {}:\n{}",
                fixture.display_path().display(),
                oracle_path.display(),
                out.status,
                String::from_utf8_lossy(&out.stderr).trim_end()
            ));
            continue;
        }
        let actual = normalize(&String::from_utf8_lossy(&out.stdout));
        let expected_path = fixture.sidecar_path("expected.txt");
        if bless {
            if actual.is_empty() {
                let _ = fs::remove_file(&expected_path);
            } else if let Err(e) = fs::write(&expected_path, &actual) {
                failures.push(format!("{}: bless write: {}", fixture.display_path().display(), e));
            }
            continue;
        }
        let expected = normalize(&fs::read_to_string(&expected_path).unwrap_or_default());
        if actual == expected {
            let _ = fs::remove_file(fixture.actual_path("oracle.txt"));
        } else {
            let actual_path = fixture.actual_path("oracle.txt");
            let _ = fs::write(&actual_path, &actual);
            failures.push(format!(
                "{}: oracle mismatch; wrote {}\n--- expected.txt (Elixir-owned golden)\n{}--- elixir actual\n{}",
                fixture.display_path().display(),
                actual_path.display(),
                expected,
                actual
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "oracle golden mismatches ({}):\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

// fz-fkv: the bulk `fixture_matrix()` test was replaced by per-pair
// trials emitted from `fn main()`. Discovery, header parsing, and
// per-pair compare all live in the helpers above; the trial wiring
// is at the top of this file.

fn temp_telemetry_path(fixture: &FixtureCase, emit: &str) -> PathBuf {
    let name = fixture.name();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock before unix epoch")
        .as_nanos();
    temp_dir().join(format!("fz_telemetry_{}_{}_{}_{}.jsonl", name, emit, id(), nanos))
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
struct ReusableConsTelemetryStats {
    birth_count: usize,
    transport_count: usize,
    codegen_candidate_count: usize,
    codegen_consumed_count: usize,
    runtime_attempted_count: usize,
    runtime_reused_count: usize,
}

impl ReusableConsTelemetryStats {
    fn runtime_fallback_count(&self) -> usize {
        self.runtime_attempted_count.saturating_sub(self.runtime_reused_count)
    }
}

fn reusable_cons_telemetry_stats_for_fixture(fixture: &FixtureCase) -> ReusableConsTelemetryStats {
    let telemetry_path = temp_telemetry_path(fixture, "reusable_cons");
    let out = Command::new(FZ2_BIN)
        .args(["--log-telemetry"])
        .arg(&telemetry_path)
        .args(["run"])
        .arg(fixture.source_path())
        .output()
        .unwrap_or_else(|e| panic!("spawn fz2 run --log-telemetry: {}", e));
    assert!(
        out.status.success(),
        "fz2 run --log-telemetry {} exited {}: {}",
        fixture.display_path().display(),
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let log =
        fs::read_to_string(&telemetry_path).unwrap_or_else(|e| panic!("read {}: {}", telemetry_path.display(), e));
    let _ = fs::remove_file(&telemetry_path);
    let mut stats = ReusableConsTelemetryStats::default();
    let mut saw_native_event = false;
    for line in log.lines() {
        if line.contains("\"name\":[\"fz\",\"compiler2\",\"native_program\",\"reusable_cons\"]") {
            saw_native_event = true;
            stats.birth_count = parse_json_u64_field(line, "birth_count")
                .unwrap_or_else(|| panic!("{} telemetry missing birth_count", fixture.display_path().display()));
            stats.transport_count = parse_json_u64_field(line, "transport_count")
                .unwrap_or_else(|| panic!("{} telemetry missing transport_count", fixture.display_path().display()));
            continue;
        }
        if line.contains("\"name\":[\"fz\",\"codegen\",\"function_lowered\"]")
            && line.contains("\"body_kind\":\"fz_spec\"")
        {
            stats.codegen_candidate_count += parse_json_u64_field(line, "reusable_cons_candidate_count").unwrap_or(0);
            stats.codegen_consumed_count += parse_json_u64_field(line, "reusable_cons_consumed_count").unwrap_or(0);
            continue;
        }
        if line.contains("\"name\":[\"fz\",\"runtime\",\"process_exited\"]") {
            let fixture = fixture.display_path().display().to_string();
            stats.runtime_attempted_count += required_json_u64_field(line, "reusable_cons_attempts", &fixture);
            stats.runtime_reused_count += required_json_u64_field(line, "reusable_cons_reused", &fixture);
        }
    }
    assert!(
        saw_native_event,
        "{} telemetry missing fz.compiler2.native_program.reusable_cons event",
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
    let readme = fs::read_to_string("fixtures2/behavior/quicksort.fz").expect("read quicksort README");
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
        fs::read_to_string("fixtures2/behavior/enum_list_allocations.fz").expect("read enum_list_allocations README");
    for needle in [
        "the input list literal allocates five cons cells",
        "`Enum.count/1`, `Enum.member?/2`, and `Enum.reduce/3` allocate no additional",
        "public `Enum.reduce/3` stays a small wrapper over `Enumerable.reduce/3`",
        "static protocol dispatch routes the known list receiver",
        "native `Enum.reduce/3` allocates one wrapper closure",
        "`list_cons_allocs = 5`",
        "`list_cons_bytes = 80`",
        "`closure_allocs = 1`",
        "`closure_bytes = 32`",
        "final list/struct/map heap headline is `368`",
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
        &["5\ntrue\n15", "{5, 80, 9, 288, 1, 32, 3, 48, 0, 0}", "\n368\n"],
    );
    let stats = reusable_cons_telemetry_stats_for_fixture(&behavior_fixture_case("enum_list_allocations"));
    assert_eq!(
        stats,
        ReusableConsTelemetryStats {
            birth_count: 8,
            transport_count: 0,
            codegen_candidate_count: 0,
            codegen_consumed_count: 0,
            runtime_attempted_count: 0,
            runtime_reused_count: 0,
        },
        "enum_list_allocations should keep count/member?/reduce on the no-extra-list-cons path",
    );
    assert_eq!(stats.runtime_fallback_count(), 0);
}

fn enum_sort_constant_sorter_erased_under_return_demand_specs() {
    assert_fixture_output_contains("enum_sort", "expected.txt", &["{22, 352, 0, 0, 0, 0, 0, 0}"]);

    let readme = fs::read_to_string("fixtures2/behavior/enum_sort.fz").expect("read enum_sort README");
    for needle in [
        "default sorter is erased",
        "return-demand-specialized runtime-library",
        "not only value-demand specs",
    ] {
        assert!(readme.contains(needle), "enum_sort README must pin `{}`", needle);
    }

    let stats = reusable_cons_telemetry_stats_for_fixture(&behavior_fixture_case("enum_sort"));
    assert_eq!(
        stats,
        ReusableConsTelemetryStats {
            birth_count: 15,
            transport_count: 21,
            codegen_candidate_count: 15,
            codegen_consumed_count: 15,
            runtime_attempted_count: 132,
            runtime_reused_count: 132,
        },
        "enum_sort should make reusable-cons birth, transport, and consumption visible in compiler2 telemetry",
    );
    assert_eq!(stats.runtime_fallback_count(), 0);
}

fn interpreter_stepper_does_not_update_quiet_quanta() {
    let source = fs::read_to_string("src/ir_interp/backend.rs").expect("read interp backend runner");
    assert!(
        !source.contains("quiet_quanta"),
        "interpreter hot loop must leave quiet_quanta to scheduler boundary code"
    );
}

fn assert_fixture_output_contains(fixture: &str, file: &str, needles: &[&str]) {
    let path = behavior_fixture_sidecar_path(fixture, file);
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
