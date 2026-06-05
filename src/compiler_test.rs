use super::*;
use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind, Value};

fn named_module(name: &str) -> ModuleKey {
    ModuleKey::Named(ModuleName::parse_dotted(name).expect("valid module name"))
}

fn phase_events(capture: &Capture) -> Vec<crate::telemetry::capture::OwnedEvent> {
    capture.find(&["fz", "compiler", "phase"]).into_iter().collect()
}

fn metadata_str<'a>(ev: &'a crate::telemetry::capture::OwnedEvent, key: &str) -> &'a str {
    match ev.metadata.get(key) {
        Some(Value::Str(value)) => value.as_ref(),
        other => panic!("expected string metadata `{key}`, got {other:?}"),
    }
}

fn measurement_u64(ev: &crate::telemetry::capture::OwnedEvent, key: &str) -> u64 {
    match ev.measurements.get(key) {
        Some(Value::U64(value)) => *value,
        Some(Value::I64(value)) if *value >= 0 => *value as u64,
        other => panic!("expected integer measurement `{key}`, got {other:?}"),
    }
}

#[test]
fn compiler_phase_cache_hits_skip_repeat_work_and_emit_timing_telemetry() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let module_id = compiler.discover_module(
        named_module("Process"),
        ModuleOrigin::EmbeddedRuntime,
        FileOrigin::EmbeddedRuntime("Process".to_string()),
        &tel,
    );

    let again = compiler.discover_module(
        named_module("Process"),
        ModuleOrigin::EmbeddedRuntime,
        FileOrigin::EmbeddedRuntime("Process".to_string()),
        &tel,
    );
    assert_eq!(module_id, again, "module discovery should be idempotent");

    let mut work_runs = 0;
    let advanced = compiler.ensure_module_state(module_id, ModuleState::Parsed, &tel, |_| {
        work_runs += 1;
    });
    let cached = compiler.ensure_module_state(module_id, ModuleState::Parsed, &tel, |_| {
        work_runs += 1;
    });

    assert!(advanced, "first ensure should advance the phase");
    assert!(!cached, "second ensure should hit the cache");
    assert_eq!(work_runs, 1, "cache hit must not rerun phase work");
    assert_eq!(compiler.module(module_id).state, ModuleState::Parsed);

    assert_eq!(capture.count(&["fz", "compiler", "file_registered"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "file_cache_hit"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "module_discovered"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "module_cache_hit"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "cache_miss"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "cache_hit"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "phase_advanced"]), 1);

    let phase_events = phase_events(&capture);
    assert_eq!(
        phase_events.len(),
        2,
        "one phase miss should produce one start/stop span pair"
    );
    let start = phase_events
        .iter()
        .find(|ev| ev.kind == EventKind::SpanStart)
        .expect("phase span start");
    let stop = phase_events
        .iter()
        .find(|ev| ev.kind == EventKind::SpanStop)
        .expect("phase span stop");
    assert_eq!(metadata_str(start, "target_phase"), "parsed");
    assert!(
        stop.measurements.get("elapsed_ns").is_some(),
        "phase stop event must carry elapsed_ns"
    );
}

#[test]
fn compiler_invariants_accept_consistent_world_state() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let root = compiler.discover_module(
        ModuleKey::RootPath("fixtures/quicksort/input.fz".into()),
        ModuleOrigin::RootSource,
        FileOrigin::Filesystem("fixtures/quicksort/input.fz".into()),
        &tel,
    );
    let process = compiler.discover_module(
        named_module("Process"),
        ModuleOrigin::EmbeddedRuntime,
        FileOrigin::EmbeddedRuntime("Process".to_string()),
        &tel,
    );

    compiler.ensure_module_state(root, ModuleState::InterfaceReady, &tel, |_| {});
    compiler.mark_reachable(root, ReachabilityKind::Interface, &tel);
    compiler.mark_reachable(process, ReachabilityKind::Runtime, &tel);
    compiler.ensure_module_state(process, ModuleState::RuntimeLowered, &tel, |_| {});
    compiler.ensure_module_state(process, ModuleState::RuntimePlanned, &tel, |_| {});

    compiler
        .validate_invariants()
        .expect("consistent compiler world should validate");

    assert_eq!(capture.count(&["fz", "compiler", "module_reachable"]), 2);
    let runtime_reachable = capture
        .find(&["fz", "compiler", "module_reachable"])
        .into_iter()
        .find(|ev| metadata_str(ev, "reachability") == "runtime")
        .expect("runtime reachability event");
    assert_eq!(measurement_u64(&runtime_reachable, "module_id"), process.0 as u64);
}

#[test]
fn compiler_invariants_reject_broken_module_file_links() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let module_id = compiler.discover_module(
        named_module("Process"),
        ModuleOrigin::EmbeddedRuntime,
        FileOrigin::EmbeddedRuntime("Process".to_string()),
        &tel,
    );

    compiler.modules[module_id.0 as usize].file_id = FileId(99);

    let err = compiler
        .validate_invariants()
        .expect_err("broken module/file link must fail validation");
    assert!(
        err.to_string().contains("references missing file"),
        "unexpected invariant error: {err}"
    );
}
