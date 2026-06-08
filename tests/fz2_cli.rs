use std::env::temp_dir;
use std::ffi::OsStr;
use std::fs::{metadata, read_to_string, remove_file, write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, id};
use std::sync::atomic::{AtomicU64, Ordering};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");
static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn unique_temp_path(prefix: &str, suffix: &str) -> PathBuf {
    let nonce = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    temp_dir().join(format!("{}_{}_{}{}", prefix, id(), nonce, suffix))
}

fn run_fz2(args: &[&OsStr]) -> Output {
    Command::new(FZ2_BIN).args(args).output().expect("invoke fz2 binary")
}

fn fixture_expected_stdout(path: &str) -> String {
    let expected = Path::new(path).with_file_name("expected.txt");
    if expected.exists() {
        read_to_string(&expected).unwrap_or_else(|error| panic!("read {}: {error}", expected.display()))
    } else {
        String::new()
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
        String::from_utf8(out.stdout.clone()).expect("stdout is utf-8"),
        expected,
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
        let _ = remove_file(&telemetry_path);
    }

    let _ = remove_file(&source_path);
}

#[test]
fn build_stays_on_compiler2_telemetry_and_links_a_native_binary() {
    let source_path = unique_temp_path("fz2_build", ".fz");
    let out_bin = unique_temp_path("fz2_build", ".bin");
    let telemetry_path = unique_temp_path("fz2_build", ".jsonl");
    write(&source_path, "fn main(), do: 0\n").expect("write Compiler2 build fixture");

    let build = run_fz2(&[
        OsStr::new("--log-telemetry"),
        telemetry_path.as_os_str(),
        OsStr::new("build"),
        source_path.as_os_str(),
        OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "fz2 build should succeed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    assert_compiler2_telemetry_only(&telemetry_path, "fz2 build");
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
        "fixtures/map_three_path_parity/input.fz",
        "fixtures/defstruct_runtime/input.fz",
        "fixtures/utf8_smart_constructor/input.fz",
    ] {
        let expected = fixture_expected_stdout(fixture);
        for command in ["run", "interp"] {
            let out = run_fz2(&[OsStr::new(command), OsStr::new(fixture)]);
            assert_successful_stdout(&out, &expected, &format!("fz2 {command} {fixture}"));
        }
    }
}

#[test]
fn build_executes_map_struct_and_bitstring_fixtures() {
    for fixture in [
        "fixtures/map_three_path_parity/input.fz",
        "fixtures/defstruct_runtime/input.fz",
        "fixtures/utf8_smart_constructor/input.fz",
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
