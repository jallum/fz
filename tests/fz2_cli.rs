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
    assert!(
        !log.contains("\"frontend\""),
        "{context} should not invoke the old frontend path; log=\n{log}",
    );
}

fn assert_source_production_telemetry(path: &Path, context: &str, expect_macro_expansion: bool) {
    assert_compiler2_telemetry_only(path, context);
    let log = read_to_string(path).unwrap_or_else(|error| panic!("read telemetry log {}: {error}", path.display()));
    assert!(
        log.contains("\"function\",\"source\",\"noted\""),
        "{context} should publish FunctionSource facts; log=\n{log}",
    );
    assert!(
        log.contains("\"compiler_service\",\"define\""),
        "{context} should define source through the Fz.Compiler boundary; log=\n{log}",
    );
    if expect_macro_expansion {
        assert!(
            log.contains("\"macro\",\"expanded\""),
            "{context} should execute macro expansion in source production; log=\n{log}",
        );
    }
}

fn output_text(out: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
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
fn run_and_interp_execute_source_production_macro_and_sugar_fixtures() {
    for (fixture, expect_macro_expansion) in [
        ("fixtures/macro_inc/input.fz", true),
        ("fixtures/cross_module_macro/input.fz", true),
        ("fixtures/item_macro_source/input.fz", true),
        ("fixtures/pipe_headless_case/input.fz", false),
        ("fixtures/lambda_sugars/input.fz", false),
        ("fixtures/operator_sugars/input.fz", false),
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
            assert_source_production_telemetry(
                &telemetry_path,
                &format!("fz2 {command} {fixture}"),
                expect_macro_expansion,
            );
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

    let out = run_fz2(&[OsStr::new("run"), source_path.as_os_str()]);
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

    let _ = remove_file(&source_path);
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

#[test]
fn run_and_interp_execute_case_and_with_fixtures() {
    let fixture = "fixtures/case_with_total/input.fz";
    let expected = fixture_expected_stdout(fixture);
    for command in ["run", "interp"] {
        let out = run_fz2(&[OsStr::new(command), OsStr::new(fixture)]);
        assert_successful_stdout(&out, &expected, &format!("fz2 {command} {fixture}"));
    }
}

#[test]
fn run_and_interp_report_partial_case_and_with_warnings() {
    let fixture = "fixtures/case_tuple_pattern_sequential/input.fz";
    let expected = fixture_expected_stdout(fixture);
    for command in ["run", "interp"] {
        let out = run_fz2(&[OsStr::new(command), OsStr::new(fixture)]);
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
    }
}

#[test]
fn build_executes_case_and_with_fixtures() {
    let fixture = "fixtures/case_with_total/input.fz";
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
        "fixtures/concurrency_ping_pong/input.fz",
        "fixtures/receive_selective_refs/input.fz",
        "fixtures/receive_float_pattern/input.fz",
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
        "fixtures/concurrency_ping_pong/input.fz",
        "fixtures/receive_selective_refs/input.fz",
        "fixtures/receive_float_pattern/input.fz",
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
