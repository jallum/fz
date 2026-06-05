use serde_json::Value;
use std::env::temp_dir;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, id};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{collections::BTreeSet, ffi::OsStr};

const FZ_BIN: &str = env!("CARGO_BIN_EXE_fz");
static UNIQUE_PATH_COUNTER: AtomicU64 = AtomicU64::new(0);

fn unique_path(stem: &str, ext: &str) -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock before unix epoch")
        .as_nanos();
    let seq = UNIQUE_PATH_COUNTER.fetch_add(1, Ordering::Relaxed);
    temp_dir().join(format!("{stem}-{}-{nonce}-{seq}.{ext}", id()))
}

fn read_events(path: &Path) -> Vec<Value> {
    fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
        .lines()
        .map(|line| serde_json::from_str(line).unwrap_or_else(|e| panic!("parse telemetry line `{line}`: {e}")))
        .collect()
}

fn event_matches(ev: &Value, name: &[&str]) -> bool {
    ev.get("name")
        .and_then(Value::as_array)
        .map(|segments| {
            segments.len() == name.len()
                && segments
                    .iter()
                    .zip(name.iter())
                    .all(|(actual, expected)| actual.as_str() == Some(*expected))
        })
        .unwrap_or(false)
}

fn metadata_is(ev: &Value, key: &str, expected: &str) -> bool {
    ev.get("metadata")
        .and_then(|metadata| metadata.get(key))
        .and_then(Value::as_str)
        .map(|actual| actual == expected)
        .unwrap_or(false)
}

fn measurement_u64(ev: &Value, key: &str) -> u64 {
    ev.get("measurements")
        .and_then(|measurements| measurements.get(key))
        .and_then(Value::as_u64)
        .unwrap_or_else(|| panic!("missing u64 measurement `{key}` in {ev}"))
}

fn span_id(ev: &Value) -> u64 {
    ev.get("span_id")
        .and_then(Value::as_u64)
        .unwrap_or_else(|| panic!("missing span_id in {ev}"))
}

fn compiler_event_count(events: &[Value], event_name: &[&str], module_key: &str) -> usize {
    events
        .iter()
        .filter(|ev| event_matches(ev, event_name) && metadata_is(ev, "module_key", module_key))
        .count()
}

fn compiler_event_module_keys(events: &[Value], event_name: &[&str]) -> BTreeSet<String> {
    events
        .iter()
        .filter(|ev| event_matches(ev, event_name))
        .filter_map(|ev| {
            ev.get("metadata")
                .and_then(|metadata| metadata.get("module_key"))
                .and_then(Value::as_str)
                .map(ToOwned::to_owned)
        })
        .collect()
}

fn compiler_phase_elapsed_ns(events: &[Value], module_key: &str, target_phase: &str) -> Vec<u64> {
    let phase_span_ids = events
        .iter()
        .filter(|ev| event_matches(ev, &["fz", "compiler", "phase"]))
        .filter(|ev| ev.get("kind").and_then(Value::as_str) == Some("span_start"))
        .filter(|ev| metadata_is(ev, "module_key", module_key))
        .filter(|ev| metadata_is(ev, "target_phase", target_phase))
        .map(span_id)
        .collect::<Vec<_>>();

    events
        .iter()
        .filter(|ev| event_matches(ev, &["fz", "compiler", "phase"]))
        .filter(|ev| ev.get("kind").and_then(Value::as_str) == Some("span_stop"))
        .filter(|ev| phase_span_ids.contains(&span_id(ev)))
        .map(|ev| measurement_u64(ev, "elapsed_ns"))
        .collect()
}

fn run_fz_with_telemetry(args: &[&Path], subcommand: &[&str], extra: &[&str]) -> (Output, Vec<Value>, PathBuf) {
    let telemetry_path = unique_path("fz-cli-telemetry", "jsonl");
    let mut cmd = Command::new(FZ_BIN);
    cmd.args(["--log-telemetry"]).arg(&telemetry_path);
    cmd.args(subcommand);
    for arg in args {
        cmd.arg(arg);
    }
    cmd.args(extra);
    let out = cmd.output().expect("spawn fz");
    let events = read_events(&telemetry_path);
    (out, events, telemetry_path)
}

fn build_with_telemetry(input: &Path) -> (Output, Vec<Value>, PathBuf, PathBuf) {
    let out_path = unique_path("fz-cli-build", "bin");
    let telemetry_path = unique_path("fz-cli-build-telemetry", "jsonl");
    let out = Command::new(FZ_BIN)
        .args(["--log-telemetry"])
        .arg(&telemetry_path)
        .arg("build")
        .arg(input)
        .arg("-o")
        .arg(&out_path)
        .output()
        .expect("spawn fz build");
    let events = read_events(&telemetry_path);
    (out, events, out_path, telemetry_path)
}

#[test]
fn dump_interfaces_parses_root_source_once_through_compiler_world() {
    let input = unique_path("fz-cli-dump", "fz");
    let source = "fn main(), do: nil\n";
    fs::write(&input, source).unwrap_or_else(|e| panic!("write {}: {e}", input.display()));

    let (out, events, telemetry_path) = run_fz_with_telemetry(&[&input], &["dump", "--emit", "interfaces"], &[]);

    let _ = fs::remove_file(&input);
    let _ = fs::remove_file(&telemetry_path);

    assert!(
        out.status.success(),
        "fz dump --emit interfaces exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );

    let module_key = input.display().to_string();
    assert_eq!(
        compiler_event_count(&events, &["fz", "compiler", "parsed"], &module_key),
        1,
        "root source should parse exactly once through the compiler world"
    );
    assert_eq!(
        compiler_event_count(&events, &["fz", "compiler", "interface_ready"], &module_key),
        1,
        "root source should collect interfaces exactly once through the compiler world"
    );

    let parsed_elapsed = compiler_phase_elapsed_ns(&events, &module_key, "parsed");
    assert_eq!(parsed_elapsed.len(), 1, "root parsed phase should stop exactly once");
    let body_surface_elapsed = compiler_phase_elapsed_ns(&events, &module_key, "body_surface_ready");
    assert_eq!(
        body_surface_elapsed.len(),
        1,
        "dump --emit interfaces should build one body surface for the root source"
    );
    assert_eq!(
        compiler_event_count(&events, &["fz", "compiler", "body_surface_ready"], &module_key),
        1,
        "interface dumping should make the root body surface ready exactly once"
    );
    assert!(
        events
            .iter()
            .filter(|ev| event_matches(ev, &["fz", "compiler", "fn_group_discovered"]))
            .any(|ev| metadata_is(ev, "module_key", &module_key)),
        "interface dumping should discover root function-groups through the compiler world"
    );
    assert_eq!(
        compiler_event_count(&events, &["fz", "compiler", "runtime_lowered"], &module_key),
        0,
        "interface dumping must not lower runtime work for the root source"
    );
    assert!(
        !events
            .iter()
            .any(|ev| event_matches(ev, &["fz", "compiler", "fn_group_lowered"])),
        "body-surface readiness must stay body-free"
    );
}

#[test]
fn run_reaches_and_parses_utf8_once_through_compiler_world() {
    let input = fs::canonicalize("fixtures/utf8_smart_constructor/input.fz")
        .unwrap_or_else(|e| panic!("canonicalize utf8 fixture: {e}"));
    let (out, events, telemetry_path) = run_fz_with_telemetry(&[&input], &["run"], &[]);
    let _ = fs::remove_file(&telemetry_path);

    assert!(
        out.status.success(),
        "fz run exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );

    assert_eq!(
        compiler_event_count(&events, &["fz", "compiler", "runtime_module_reachable"], "Utf8"),
        1,
        "Utf8 should become runtime-reachable exactly once"
    );
    assert_eq!(
        compiler_event_count(&events, &["fz", "compiler", "parsed"], "Utf8"),
        1,
        "Utf8 should parse exactly once"
    );

    let parsed_elapsed = compiler_phase_elapsed_ns(&events, "Utf8", "parsed");
    assert_eq!(parsed_elapsed.len(), 1, "Utf8 parsed phase should stop exactly once");
}

#[test]
fn build_reaches_lowers_and_plans_process_once_through_compiler_world() {
    let input = fs::canonicalize("fixtures/process_heap_stats/input.fz")
        .unwrap_or_else(|e| panic!("canonicalize Process fixture: {e}"));
    let (out, events, out_path, telemetry_path) = build_with_telemetry(&input);

    let _ = fs::remove_file(&out_path);
    let _ = fs::remove_file(out_path.with_extension("o"));
    let _ = fs::remove_file(&telemetry_path);

    assert!(
        out.status.success(),
        "fz build exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );

    assert_eq!(
        compiler_event_count(&events, &["fz", "compiler", "runtime_module_reachable"], "Process"),
        1,
        "Process should become runtime-reachable exactly once"
    );
    assert_eq!(
        compiler_event_count(&events, &["fz", "compiler", "parsed"], "Process"),
        1,
        "Process should parse exactly once"
    );
    assert_eq!(
        compiler_event_count(&events, &["fz", "compiler", "runtime_lowered"], "Process"),
        1,
        "Process should lower exactly once"
    );
    assert_eq!(
        compiler_event_count(&events, &["fz", "compiler", "runtime_planned"], "Process"),
        1,
        "Process should plan exactly once"
    );

    let parsed_elapsed = compiler_phase_elapsed_ns(&events, "Process", "parsed");
    assert_eq!(parsed_elapsed.len(), 1, "Process parsed phase should stop exactly once");
}

#[test]
fn quicksort_build_parses_only_process_and_minimal_runtime_surface() {
    let input = fs::canonicalize("fixtures/quicksort/input.fz")
        .unwrap_or_else(|e| panic!("canonicalize quicksort fixture: {e}"));
    let (out, events, out_path, telemetry_path) = build_with_telemetry(&input);

    let _ = fs::remove_file(&out_path);
    let _ = fs::remove_file(out_path.with_extension("o"));
    let _ = fs::remove_file(&telemetry_path);

    assert!(
        out.status.success(),
        "fz build quicksort exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );

    let parsed_modules = compiler_event_module_keys(&events, &["fz", "compiler", "parsed"]);
    let root_module = input
        .file_name()
        .unwrap_or_else(|| OsStr::new("input.fz"))
        .to_string_lossy()
        .to_string();

    assert!(
        parsed_modules.iter().any(|module| module.ends_with(&root_module)),
        "quicksort root source should parse once; parsed modules: {parsed_modules:?}"
    );
    assert!(parsed_modules.contains("Process"));
    assert!(parsed_modules.contains("$Prelude"));
    assert!(parsed_modules.contains("Kernel"));
    assert!(
        !parsed_modules.contains("Utf8"),
        "quicksort should not parse unrelated Utf8 runtime code; parsed modules: {parsed_modules:?}"
    );
    assert!(
        !parsed_modules.contains("Enum"),
        "quicksort should not parse unrelated Enum runtime code; parsed modules: {parsed_modules:?}"
    );
    for unexpected in ["Enumerable", "Range", "List", "Map"] {
        assert!(
            !parsed_modules.contains(unexpected),
            "quicksort should not parse unrelated core runtime module {unexpected}; parsed modules: {parsed_modules:?}"
        );
    }

    let runtime_reachable = compiler_event_module_keys(&events, &["fz", "compiler", "runtime_module_reachable"]);
    assert_eq!(
        runtime_reachable,
        BTreeSet::from(["Process".to_string()]),
        "quicksort should make only Process live at runtime"
    );
}
