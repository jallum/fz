use std::collections::{BTreeMap, BTreeSet};
use std::env::temp_dir;
use std::ffi::{OsStr, OsString};
use std::fs::{metadata, read_to_string, remove_file, write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, id};
use std::sync::atomic::{AtomicU64, Ordering};

use fz::causal::{CausalReport, FormulaWork, parse_public_trace};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");
static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TargetFixture {
    source: &'static str,
    golden: &'static str,
}

const TARGET_FIXTURES: [TargetFixture; 3] = [
    TargetFixture {
        source: "fixtures2/00420_enum_take_drop_split.fz",
        golden: "fixtures2/behavior/enum_take_drop_split.fz",
    },
    TargetFixture {
        source: "fixtures2/behavior/enum_predicate_search.fz",
        golden: "fixtures2/behavior/enum_predicate_search.fz",
    },
    TargetFixture {
        source: "fixtures2/behavior/fz_f98_range_map_converges.fz",
        golden: "fixtures2/behavior/fz_f98_range_map_converges.fz",
    },
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ObservationDoor {
    Interp,
    Run,
}

impl ObservationDoor {
    const fn name(self) -> &'static str {
        match self {
            Self::Interp => "interp",
            Self::Run => "run",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ObservationTelemetry {
    PublicJsonl,
}

impl ObservationTelemetry {
    const fn name(self) -> &'static str {
        match self {
            Self::PublicJsonl => "public-jsonl",
        }
    }

    fn append_args(self, path: &Path, args: &mut Vec<OsString>) {
        match self {
            Self::PublicJsonl => {
                args.push("--log-telemetry".into());
                args.push(path.into());
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ObservationDump {
    Backend,
    Native,
}

impl ObservationDump {
    const fn name(self) -> &'static str {
        match self {
            Self::Backend => "backend",
            Self::Native => "native",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ObservationEnvironment {
    inherited: bool,
    fixed_overrides: &'static [(&'static str, &'static str)],
}

impl std::fmt::Display for ObservationEnvironment {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(if self.inherited { "inherited" } else { "fixed" })?;
        for (name, value) in self.fixed_overrides {
            write!(formatter, "+{name}={value}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ObservationSpec {
    door: ObservationDoor,
    telemetry: ObservationTelemetry,
    dump: ObservationDump,
    environment: ObservationEnvironment,
}

const TARGET_OBSERVATION_SPEC: ObservationSpec = ObservationSpec {
    door: ObservationDoor::Interp,
    telemetry: ObservationTelemetry::PublicJsonl,
    dump: ObservationDump::Backend,
    environment: ObservationEnvironment {
        inherited: true,
        fixed_overrides: &[],
    },
};

impl ObservationSpec {
    fn invocation(self, fixture: TargetFixture, trace: &Path, dump: &Path) -> ObservationInvocation {
        let mut args = Vec::with_capacity(6);
        self.telemetry.append_args(trace, &mut args);
        args.push(self.door.name().into());
        args.push("--dump".into());
        args.push(format!("{}={}", self.dump.name(), dump.display()).into());
        args.push(fixture.source.into());
        ObservationInvocation {
            args,
            environment: self.environment,
        }
    }
}

impl std::fmt::Display for ObservationSpec {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "door={} telemetry={} dump={} env={}",
            self.door.name(),
            self.telemetry.name(),
            self.dump.name(),
            self.environment,
        )
    }
}

#[derive(Debug, PartialEq, Eq)]
struct ObservationInvocation {
    args: Vec<OsString>,
    environment: ObservationEnvironment,
}

impl ObservationInvocation {
    fn command(&self) -> Command {
        self.configure(Command::new(FZ2_BIN))
    }

    fn configure(&self, mut command: Command) -> Command {
        if !self.environment.inherited {
            command.env_clear();
        }
        command.envs(self.environment.fixed_overrides.iter().copied());
        command.args(&self.args);
        command
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ObservationProcess {
    First,
    Second,
}

impl ObservationProcess {
    const ALL: [Self; 2] = [Self::First, Self::Second];

    const fn phase(self) -> &'static str {
        match self {
            Self::First => "first-process",
            Self::Second => "second-process",
        }
    }
}

fn unique_temp_path(prefix: &str, suffix: &str) -> PathBuf {
    let nonce = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    temp_dir().join(format!("{}_{}_{}{}", prefix, id(), nonce, suffix))
}

fn sum_reporting_counts(counts: impl IntoIterator<Item = (String, u64)>) -> BTreeMap<String, u64> {
    counts.into_iter().fold(BTreeMap::new(), |mut sums, (identity, count)| {
        *sums.entry(identity).or_default() += count;
        sums
    })
}

fn run_fz2(args: &[&OsStr]) -> Output {
    Command::new(FZ2_BIN).args(args).output().expect("invoke fz2 binary")
}

#[derive(Debug)]
struct ObservationFailure {
    spec: ObservationSpec,
    fixture: &'static str,
    phase: &'static str,
    ratchet: &'static str,
    detail: String,
}

impl std::fmt::Display for ObservationFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "fixture={} {} phase={} ratchet={}: {}",
            self.fixture, self.spec, self.phase, self.ratchet, self.detail,
        )
    }
}

impl std::error::Error for ObservationFailure {}

fn observation_failure(
    spec: ObservationSpec,
    fixture: TargetFixture,
    phase: &'static str,
    ratchet: &'static str,
    detail: impl Into<String>,
) -> ObservationFailure {
    ObservationFailure {
        spec,
        fixture: fixture.source,
        phase,
        ratchet,
        detail: detail.into(),
    }
}

struct OwnedObservationFile {
    path: Option<PathBuf>,
}

impl OwnedObservationFile {
    fn new(prefix: &str, suffix: &str) -> Self {
        Self {
            path: Some(unique_temp_path(prefix, suffix)),
        }
    }

    fn path(&self) -> &Path {
        self.path
            .as_deref()
            .expect("owned observation file was already consumed")
    }

    fn read_and_remove(mut self, request: ProcessRequest, artifact: &str) -> Result<Vec<u8>, ObservationFailure> {
        let path = self.path();
        let bytes = std::fs::read(path).map_err(|error| {
            observation_failure(
                request.spec,
                request.fixture,
                request.process.phase(),
                "observation-production",
                format!("read {artifact} {}: {error}", path.display()),
            )
        })?;
        remove_file(path).map_err(|error| {
            observation_failure(
                request.spec,
                request.fixture,
                request.process.phase(),
                "observation-production",
                format!("remove {artifact} {}: {error}", path.display()),
            )
        })?;
        self.path = None;
        Ok(bytes)
    }
}

impl Drop for OwnedObservationFile {
    fn drop(&mut self) {
        if let Some(path) = self.path.take() {
            let _ = remove_file(path);
        }
    }
}

#[derive(Clone)]
struct ProcessObservation {
    stdout: String,
    stderr: Vec<u8>,
    report: CausalReport,
    construction_targets: BTreeSet<String>,
    backend: String,
}

struct TargetObservation<T = ProcessObservation> {
    spec: ObservationSpec,
    fixture: TargetFixture,
    processes: [T; 2],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ProcessRequest {
    spec: ObservationSpec,
    fixture: TargetFixture,
    process: ObservationProcess,
}

fn produce_target_observations<T, E>(
    spec: ObservationSpec,
    mut produce_process: impl FnMut(ProcessRequest) -> Result<T, E>,
) -> Result<Vec<TargetObservation<T>>, E> {
    TARGET_FIXTURES
        .into_iter()
        .map(|fixture| {
            let request = |process| ProcessRequest { spec, fixture, process };
            Ok(TargetObservation {
                spec,
                fixture,
                processes: [
                    produce_process(request(ObservationProcess::First))?,
                    produce_process(request(ObservationProcess::Second))?,
                ],
            })
        })
        .collect()
}

#[test]
fn reporting_counts_add_canonical_equivalent_rows() {
    assert_eq!(
        sum_reporting_counts([("same identity".to_string(), 1), ("same identity".to_string(), 2)]),
        BTreeMap::from([("same identity".to_string(), 3)])
    );
}

#[test]
fn target_fixture_observations_call_the_process_producer_exactly_twice_per_fixture() {
    #[derive(Debug, PartialEq, Eq)]
    struct ProcessSentinel {
        invocation: usize,
        fixture: TargetFixture,
        process: ObservationProcess,
    }

    let mut invocations = 0;
    let observations = produce_target_observations(TARGET_OBSERVATION_SPEC, |request| {
        invocations += 1;
        Ok::<_, std::convert::Infallible>(ProcessSentinel {
            invocation: invocations,
            fixture: request.fixture,
            process: request.process,
        })
    })
    .expect("the sentinel producer is infallible");

    assert_eq!(observations.len(), 3, "one bundle belongs to each fixture");
    assert_eq!(invocations, 6, "each bundle needs two independent compiler processes");
    for (fixture_index, observation) in observations.iter().enumerate() {
        assert_eq!(observation.fixture, TARGET_FIXTURES[fixture_index]);
        assert_eq!(observation.spec, TARGET_OBSERVATION_SPEC);
        assert_eq!(observation.processes[0].fixture, observation.fixture);
        assert_eq!(observation.processes[1].fixture, observation.fixture);
        assert_eq!(observation.processes[0].process, ObservationProcess::First);
        assert_eq!(observation.processes[1].process, ObservationProcess::Second);
        assert_ne!(
            observation.processes[0].invocation, observation.processes[1].invocation,
            "a bundle must not clone one process result into both comparison slots"
        );
        assert_eq!(
            [observation.processes[0].invocation, observation.processes[1].invocation],
            [fixture_index * 2 + 1, fixture_index * 2 + 2],
            "fixture and process production order must remain deterministic"
        );
    }
}

fn compile_process_observation(request: ProcessRequest) -> Result<ProcessObservation, ObservationFailure> {
    let phase = request.process.phase();
    let trace = OwnedObservationFile::new(&format!("fz2_target_{phase}"), ".jsonl");
    let backend = OwnedObservationFile::new(&format!("fz2_target_{phase}"), ".backend");
    let invocation = request.spec.invocation(request.fixture, trace.path(), backend.path());
    let output = invocation.command().output().map_err(|error| {
        observation_failure(
            request.spec,
            request.fixture,
            phase,
            "observation-production",
            format!("spawn compiler process: {error}"),
        )
    })?;
    if !output.status.success() {
        return Err(observation_failure(
            request.spec,
            request.fixture,
            phase,
            "observation-production",
            format!(
                "compiler process exited {:?}; stdout={:?} stderr={:?}",
                output.status.code(),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
            ),
        ));
    }

    let trace = trace.read_and_remove(request, "public trace")?;
    let backend = backend.read_and_remove(request, "backend dump")?;
    let report = std::panic::catch_unwind(|| CausalReport::derive(&parse_public_trace(&trace))).map_err(|payload| {
        let detail = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or("non-string panic");
        observation_failure(
            request.spec,
            request.fixture,
            phase,
            "observation-production",
            format!("decode/replay public trace panicked: {detail}"),
        )
    })?;

    let construction_targets = report
        .formulas
        .keys()
        .filter(|identity| {
            serde_json::from_str::<serde_json::Value>(identity)
                .ok()
                .and_then(|identity| {
                    identity
                        .get("kind")
                        .and_then(serde_json::Value::as_str)
                        .map(str::to_owned)
                })
                .is_some_and(|kind| kind == "DeriveCallableConstructionTarget")
        })
        .cloned()
        .collect();
    let stdout = String::from_utf8(output.stdout).map_err(|error| {
        observation_failure(
            request.spec,
            request.fixture,
            phase,
            "observation-production",
            format!("runtime stdout is not UTF-8: {error}"),
        )
    })?;
    Ok(ProcessObservation {
        stdout,
        stderr: output.stderr,
        report,
        construction_targets,
        backend: String::from_utf8(backend).map_err(|error| {
            observation_failure(
                request.spec,
                request.fixture,
                phase,
                "observation-production",
                format!("backend dump is not UTF-8: {error}"),
            )
        })?,
    })
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

fn public_trace_ratchet(observation: &TargetObservation) -> Result<usize, ObservationFailure> {
    let expected = fixture_expected_stdout(observation.fixture.golden);
    let mut construction_targets = 0;
    for (process, process_observation) in ObservationProcess::ALL.into_iter().zip(&observation.processes) {
        let phase = process.phase();
        let fail =
            |detail: String| observation_failure(observation.spec, observation.fixture, phase, "public-trace", detail);
        if normalize_stdout(&process_observation.stdout) != normalize_stdout(&expected) {
            return Err(fail(format!(
                "runtime stdout differs from the fixture golden: {:?}",
                process_observation.stdout
            )));
        }
        if !process_observation.stderr.is_empty() {
            return Err(fail(format!(
                "compiler process wrote stderr: {}",
                String::from_utf8_lossy(&process_observation.stderr)
            )));
        }
        let report = &process_observation.report;
        if report.recursive_search.searches == 0 {
            return Err(fail("recursive-search population is empty".to_string()));
        }
        if let Some(gap) = report.undefined_first_uses.first() {
            return Err(fail(format!("public trace used an undefined raw id first: {gap:?}")));
        }
        if report.canon.types() == 0 || report.canon.functions() == 0 {
            return Err(fail("public trace canon dictionary is empty".to_string()));
        }
        if observation.fixture.source.ends_with("fz_f98_range_map_converges.fz")
            && let Some(unattributed) = report.uncaused.first()
        {
            return Err(fail(format!("evaluation is unattributed: {unattributed:?}")));
        }
        if let Some(undefined) = process_observation
            .construction_targets
            .iter()
            .find(|identity| identity.contains("?ty:"))
        {
            return Err(fail(format!(
                "callable-construction target surface has an undefined canonical type: {undefined}"
            )));
        }
        construction_targets += process_observation.construction_targets.len();
    }
    Ok(construction_targets)
}

fn causal_work_ratchet(observation: &TargetObservation) -> Result<(), ObservationFailure> {
    let fail = |detail: String| {
        observation_failure(
            observation.spec,
            observation.fixture,
            "cross-process-comparison",
            "causal-work",
            detail,
        )
    };
    let [first, second] = &observation.processes;
    if first.stdout != second.stdout {
        return Err(fail("runtime output moved across processes".to_string()));
    }
    let first = first.report.canonical_multiset();
    let second = second.report.canonical_multiset();
    if first.len() <= 1_000 {
        return Err(fail(format!(
            "canonical work comparand is vacuous: {} entries",
            first.len()
        )));
    }
    if first != second {
        let divergence = first
            .iter()
            .find(|(key, count)| second.get(*key) != Some(count))
            .or_else(|| second.iter().find(|(key, _)| !first.contains_key(*key)));
        return Err(fail(format!(
            "canonical work differs; first divergence: {divergence:?}"
        )));
    }
    Ok(())
}

fn backend_identity_ratchet(observation: &TargetObservation) -> Result<usize, ObservationFailure> {
    let fail =
        |phase, detail| observation_failure(observation.spec, observation.fixture, phase, "backend-identity", detail);
    for (process, process_observation) in ObservationProcess::ALL.into_iter().zip(&observation.processes) {
        let phase = process.phase();
        if process_observation.backend.len() <= 1_000 {
            return Err(fail(
                phase,
                format!("backend dump is vacuous: {} bytes", process_observation.backend.len()),
            ));
        }
        if process_observation.backend.contains("Ty(") {
            return Err(fail(phase, "backend dump carries a raw type interner id".to_string()));
        }
    }

    let [first, second] = &observation.processes;
    if first.construction_targets != second.construction_targets {
        return Err(fail(
            "cross-process-comparison",
            "canonical callable-construction target identities differ".to_string(),
        ));
    }
    if first.backend != second.backend {
        let divergence = first
            .backend
            .lines()
            .zip(second.backend.lines())
            .position(|(left, right)| left != right);
        return Err(fail(
            "cross-process-comparison",
            format!(
                "canonical backend differs first at line {divergence:?}: first={:?} second={:?}",
                divergence.and_then(|at| first.backend.lines().nth(at)),
                divergence.and_then(|at| second.backend.lines().nth(at)),
            ),
        ));
    }
    Ok(first.construction_targets.len())
}

fn synthetic_process_observation(fixture: TargetFixture) -> ProcessObservation {
    ProcessObservation {
        stdout: fixture_expected_stdout(fixture.golden),
        stderr: Vec::new(),
        report: CausalReport::default(),
        construction_targets: BTreeSet::new(),
        backend: "x".repeat(1_001),
    }
}

#[test]
fn target_observation_consumer_failures_retain_exact_attribution() {
    let fixture = TARGET_FIXTURES[0];
    let base = synthetic_process_observation(fixture);

    let public = public_trace_ratchet(&TargetObservation {
        spec: TARGET_OBSERVATION_SPEC,
        fixture,
        processes: [base.clone(), base.clone()],
    })
    .expect_err("an empty public report must fail");
    assert_eq!(public.phase, "first-process");
    assert_eq!(public.ratchet, "public-trace");

    let mut changed_output = base.clone();
    changed_output.stdout.push('!');
    let causal = causal_work_ratchet(&TargetObservation {
        spec: TARGET_OBSERVATION_SPEC,
        fixture,
        processes: [base.clone(), changed_output],
    })
    .expect_err("different process output must fail");
    assert_eq!(causal.phase, "cross-process-comparison");
    assert_eq!(causal.ratchet, "causal-work");

    let mut changed_backend = base.clone();
    changed_backend.backend.push('!');
    let backend = backend_identity_ratchet(&TargetObservation {
        spec: TARGET_OBSERVATION_SPEC,
        fixture,
        processes: [base, changed_backend],
    })
    .expect_err("different backend artifacts must fail");
    assert_eq!(backend.phase, "cross-process-comparison");
    assert_eq!(backend.ratchet, "backend-identity");

    for failure in [public, causal, backend] {
        let context = failure.to_string();
        assert!(context.contains(fixture.source));
        assert!(context.contains("door=interp telemetry=public-jsonl dump=backend"));
        assert!(context.contains("phase="));
        assert!(context.contains("ratchet="));
    }
}

#[test]
fn observation_spec_moves_invocation_and_failure_context_together() {
    let changed = ObservationSpec {
        door: ObservationDoor::Run,
        telemetry: ObservationTelemetry::PublicJsonl,
        dump: ObservationDump::Native,
        environment: ObservationEnvironment {
            inherited: false,
            fixed_overrides: &[("FZ_OBSERVATION_TEST", "isolated")],
        },
    };
    let fixture = TARGET_FIXTURES[0];
    let trace = Path::new("trace.jsonl");
    let dump = Path::new("artifact.dump");
    let normal = TARGET_OBSERVATION_SPEC.invocation(fixture, trace, dump);
    let changed_invocation = changed.invocation(fixture, trace, dump);

    assert_ne!(changed_invocation, normal);
    let command = changed_invocation.command();
    assert_eq!(
        command.get_args().map(OsStr::to_owned).collect::<Vec<_>>(),
        [
            "--log-telemetry",
            "trace.jsonl",
            "run",
            "--dump",
            "native=artifact.dump",
            fixture.source,
        ]
        .map(OsString::from)
        .to_vec()
    );

    const AMBIENT_KEY: &str = "FZ_TFN31_AMBIENT_SENTINEL_7A16D2";
    const AMBIENT_VALUE: &str = "visible-only-when-inherited";
    let ambient_line = format!("{AMBIENT_KEY}={AMBIENT_VALUE}");
    let environment = |invocation: &ObservationInvocation| {
        let mut child = Command::new("/bin/sh");
        child.args(["-c", "/usr/bin/env"]);
        child.env(AMBIENT_KEY, AMBIENT_VALUE);
        let output = invocation
            .configure(child)
            .output()
            .expect("run controlled environment child");
        assert!(output.status.success(), "controlled environment child must succeed");
        String::from_utf8(output.stdout).expect("controlled environment is UTF-8")
    };
    let inherited_environment = environment(&normal);
    let fixed_environment = environment(&changed_invocation);
    assert!(
        inherited_environment.lines().any(|line| line == ambient_line),
        "an inherited observation environment must preserve the child's ambient sentinel"
    );
    assert!(
        fixed_environment.lines().all(|line| line != ambient_line),
        "a fixed observation environment must clear the child's ambient sentinel"
    );
    assert!(
        fixed_environment
            .lines()
            .any(|line| line == "FZ_OBSERVATION_TEST=isolated"),
        "a fixed observation environment must apply its declared overrides"
    );

    let failure = observation_failure(changed, fixture, "second-process", "probe", "deliberate failure");
    let context = failure.to_string();
    assert!(context.contains("door=run telemetry=public-jsonl dump=native"));
    assert!(context.contains("env=fixed+FZ_OBSERVATION_TEST=isolated"));
    assert!(context.contains("phase=second-process ratchet=probe"));
}

#[test]
fn observation_outputs_are_removed_when_partial_production_returns_early() {
    fn abandon_partial_outputs() -> Result<(), Vec<PathBuf>> {
        let trace = OwnedObservationFile::new("fz2_target_early_error", ".jsonl");
        let backend = OwnedObservationFile::new("fz2_target_early_error", ".backend");
        let paths = vec![trace.path().to_path_buf(), backend.path().to_path_buf()];
        write(trace.path(), b"partial trace").expect("write partial trace");
        write(backend.path(), b"partial backend").expect("write partial backend");
        Err(paths)
    }

    let paths = abandon_partial_outputs().expect_err("the partial producer deliberately returns early");

    assert!(
        paths.iter().all(|path| !path.exists()),
        "Drop must remove every owned output when production exits before consumption: {paths:?}"
    );
}

#[test]
fn target_observation_temp_files_have_parallel_collision_free_ownership() {
    let paths = std::thread::scope(|scope| {
        (0..32)
            .map(|_| {
                scope.spawn(|| {
                    let file = OwnedObservationFile::new("fz2_target_parallel", ".tmp");
                    let path = file.path().to_path_buf();
                    write(&path, path.as_os_str().as_encoded_bytes()).expect("write owned temp output");
                    let bytes = file
                        .read_and_remove(
                            ProcessRequest {
                                spec: TARGET_OBSERVATION_SPEC,
                                fixture: TARGET_FIXTURES[0],
                                process: ObservationProcess::First,
                            },
                            "parallel ownership probe",
                        )
                        .expect("read and remove owned temp output");
                    assert_eq!(bytes, path.as_os_str().as_encoded_bytes());
                    path
                })
            })
            .map(|thread| thread.join().expect("parallel temp owner"))
            .collect::<Vec<_>>()
    });
    assert_eq!(paths.iter().collect::<BTreeSet<_>>().len(), paths.len());
    assert!(paths.iter().all(|path| !path.exists()));
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
    // fz-kdt.5's request/evaluation/wait identities make product work exactly
    // attributable. fz-tfn.38 then made each product evaluation's exact fact
    // prerequisite set one arbiter boundary and made the job span timing-only;
    // under llvm-cov 00181 emits 2,958 events / 1,394,744 bytes / 32 quiescence
    // steps. The bounds retain modest headroom while unrelated public-stream
    // creep still trips.
    for (fixture, max_events, max_bytes) in [
        ("fixtures2/00181_enum_reduce_operator_ref.fz", 3_000, 1_600 * 1024),
        ("fixtures2/00009_no_runtime.fz", 400, 192 * 1024),
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

/// One immutable observation bundle now feeds the public-trace, causal-work,
/// and canonical-backend ratchets. Each fixture is still compiled in two
/// SEPARATE processes: `RandomState` must reseed across the comparison boundary,
/// and the logs must translate their own raw arena ids. What disappeared is the
/// second three-fixture producer loop that recompiled the same process/config/
/// front-door observations solely so another pure assertion could read them.
///
/// Work counts only — no wall-clock quantity appears in the comparand.
#[test]
fn target_fixture_public_causal_and_backend_observations_are_reproducible() {
    let observations = produce_target_observations(TARGET_OBSERVATION_SPEC, compile_process_observation)
        .unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(
        observations.len(),
        3,
        "the three byte-identical fixture/config/front-door keys need three bundle productions"
    );
    assert_eq!(
        observations
            .iter()
            .map(|observation| observation.processes.len())
            .sum::<usize>(),
        6,
        "each bundle must retain two separate-process observations"
    );

    let mut public_construction_targets = 0;
    let mut backend_construction_targets = 0;
    for observation in &observations {
        public_construction_targets += public_trace_ratchet(observation).unwrap_or_else(|error| panic!("{error}"));
        causal_work_ratchet(observation).unwrap_or_else(|error| panic!("{error}"));
        backend_construction_targets += backend_identity_ratchet(observation).unwrap_or_else(|error| panic!("{error}"));
    }
    assert!(
        public_construction_targets > 0 && backend_construction_targets > 0,
        "the three demand fixtures must carry exact callable targets from public facts into the backend"
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
///
/// fz-tfn.8 made executable effects ordinary product formulas. The mutually
/// recursive `List.reduce_cont/3` and `List.reduce_step/3` formulas settle as
/// one group; their two suspended stack requests then read the values that
/// group just published without evaluating either producer again.
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
    assert_eq!(
        quiesced.len(),
        32,
        "{fixture}: exact product prerequisite sets must stay within the 34-event drain-arbiter ceiling"
    );

    let mut wakes = Vec::new();
    let mut readiness_changes = BTreeMap::new();
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
            let kind = change
                .get("kind")
                .and_then(serde_json::Value::as_str)
                .expect("every readiness change names its fact kind");
            *readiness_changes.entry(kind).or_insert(0) += 1;
        }
        wakes.extend(step.get("wakes").and_then(|w| w.as_array()).into_iter().flatten());
    }
    assert_eq!(
        readiness_changes,
        BTreeMap::from([
            ("Activation", 4),
            ("ActivationAnalyzed", 10),
            ("ActivationInputs", 9),
            ("CallSiteSummary", 11),
            ("CallSiteTargets", 6),
            ("ReturnType", 10),
            ("RuntimeDemand", 10),
        ]),
        "batching one product evaluation's settled prerequisites must preserve every typed readiness transition"
    );

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
            // The two retained backend projections are product completions,
            // not scheduler-formula evaluations.
            evaluations: 363,
            initial: 176,
            content_caused: 169,
            readiness_caused: 18,
            uncaused: 0,
            changed_outputs: 213,
            unchanged_outputs: 150,
            wakes: 181,
            blocked_completions: 168,
        },
        "{fixture}: the reactive RuntimeDemand formula work or its causal classification moved"
    );
    let products = report.product_totals();
    let effect_cache_hits = sum_reporting_counts(
        report
            .products
            .iter()
            .filter(|(product, work)| product.kind() == Some("executable_effects") && work.cache_hits > 0)
            .map(|(product, work)| (product.canonical_identity(&report.canon), work.cache_hits)),
    );
    let effect_identity = |function_id, arrow| {
        serde_json::json!({
            "arrow": arrow,
            "function_id": function_id,
            "kind": "executable_effects",
            "need": "value",
            "root_id": 0,
        })
        .to_string()
    };
    assert_eq!(
        effect_cache_hits,
        BTreeMap::from([
            (
                effect_identity("List.reduce_cont/3", "fp[F] (list(int), int, a2) -> r0"),
                1,
            ),
            (
                effect_identity("List.reduce_step/3", "fp[F] (list(int), {:cont, int}, a2) -> r0",),
                1,
            ),
        ]),
        "{fixture}: the reactive effect group must leave one cache-only suspended request per member"
    );
    assert_eq!(
        (
            products.settlements,
            products.distinct_generations,
            products.changed,
            products.unchanged,
            products.cache_hits,
            products.displacements,
        ),
        (396, 396, 396, 0, 16, 0),
        "{fixture}: reactive product settlement work moved while pinning exact-prerequisite readiness"
    );
    assert!(
        report.uncaused.is_empty(),
        "every evaluation must still name a moved input; first unattributed: {:?}",
        report.uncaused.first()
    );
    assert!(
        report.readiness_without_settled_wake.is_empty(),
        "a readiness cause is only claimable where a Settled wake carried it"
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
