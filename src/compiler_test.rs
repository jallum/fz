use super::*;
use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind, Value};
use std::sync::Arc;

fn named_module(name: &str) -> ModuleKey {
    ModuleKey::Named(ModuleName::parse_dotted(name).expect("valid module name"))
}

fn state_work_events(capture: &Capture) -> Vec<crate::telemetry::capture::OwnedEvent> {
    capture
        .find(&["fz", "compiler", "state_work"])
        .into_iter()
        .collect()
}

fn state_start_events_for_target(capture: &Capture, target_state: &str) -> Vec<crate::telemetry::capture::OwnedEvent> {
    state_work_events(capture)
        .into_iter()
        .filter(|ev| ev.kind == EventKind::SpanStart)
        .filter(|ev| metadata_str(ev, "target_state") == target_state)
        .collect()
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

fn captured_str<'a>(ev: &'a crate::telemetry::capture::OwnedEvent, key: &str) -> &'a str {
    match ev.metadata.get(key) {
        Some(Value::Str(value)) => value.as_ref(),
        other => panic!("expected string metadata `{key}`, got {other:?}"),
    }
}

#[test]
fn compiler_state_cache_hits_skip_repeat_work_and_emit_timing_telemetry() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let module_id = compiler.world.register_module(
        named_module("Process"),
        ModuleOrigin::EmbeddedRuntime,
        FileOrigin::EmbeddedRuntime("Process".to_string()),
        SourceDescriptor {
            source_name: "runtime:Process".to_string(),
            text: Arc::<str>::from("defmodule Process do\nend\n"),
            parse_kind: ParseKind::Prelude,
        },
        &tel,
    );

    let again = compiler.world.register_module(
        named_module("Process"),
        ModuleOrigin::EmbeddedRuntime,
        FileOrigin::EmbeddedRuntime("Process".to_string()),
        SourceDescriptor {
            source_name: "runtime:Process".to_string(),
            text: Arc::<str>::from("defmodule Process do\nend\n"),
            parse_kind: ParseKind::Prelude,
        },
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
    assert_eq!(work_runs, 1, "cache hit must not rerun state work");
    assert_eq!(compiler.module(module_id).state, ModuleState::Parsed);

    assert_eq!(capture.count(&["fz", "compiler", "file_registered"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "file_cache_hit"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "module_discovered"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "module_cache_hit"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "cache_miss"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "cache_hit"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "state_advanced"]), 1);

    let state_events = state_work_events(&capture);
    assert_eq!(
        state_events.len(),
        2,
        "one state miss should produce one start/stop span pair"
    );
    let start = state_events
        .iter()
        .find(|ev| ev.kind == EventKind::SpanStart)
        .expect("state span start");
    let stop = state_events
        .iter()
        .find(|ev| ev.kind == EventKind::SpanStop)
        .expect("state span stop");
    assert_eq!(metadata_str(start, "target_state"), "parsed");
    assert!(
        stop.measurements.get("elapsed_ns").is_some(),
        "state stop event must carry elapsed_ns"
    );
}

#[test]
fn root_source_is_loaded_and_parsed_once_with_timing_telemetry() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let root = compiler.register_root_source("fixtures/quicksort/input.fz", "fn main(), do: nil\n".to_string(), &tel);

    let first = compiler.ensure_program(root, &tel).expect("root source should parse");
    let second = compiler
        .ensure_program(root, &tel)
        .expect("root source should come from cache");

    assert_eq!(first.program.items.len(), 1);
    assert_eq!(second.program.items.len(), 1);
    assert_eq!(compiler.module(root).state, ModuleState::Parsed);

    assert_eq!(capture.count(&["fz", "compiler", "source_loaded"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "parsed"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "cache_miss"]), 2);
    assert_eq!(capture.count(&["fz", "compiler", "cache_hit"]), 1);

    let parsed_phase_events = state_start_events_for_target(&capture, "parsed");
    assert_eq!(
        parsed_phase_events.len(),
        1,
        "one parse should produce one parsed phase start"
    );
    assert!(
        state_work_events(&capture)
            .iter()
            .any(|ev| ev.kind == EventKind::SpanStop && ev.measurements.get("elapsed_ns").is_some()),
        "compiler state timing must report elapsed_ns"
    );

    compiler
        .validate_invariants()
        .expect("parsed root source should satisfy compiler invariants");
}

#[test]
fn runtime_module_interface_is_collected_once_from_source() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let process = ModuleName::parse_dotted("Process").expect("valid module name");

    let first = compiler
        .ensure_runtime_module_interface(&process, &tel)
        .expect("Process interface should build")
        .expect("Process module should exist");
    let second = compiler
        .ensure_runtime_module_interface(&process, &tel)
        .expect("Process interface should come from cache")
        .expect("Process module should exist");

    assert_eq!(first.name, process);
    assert_eq!(second.name, process);
    assert_eq!(compiler.module_count(), 1);
    assert_eq!(compiler.file_count(), 1);

    let process_id = compiler
        .discover_runtime_module(&process, &tel)
        .expect("Process runtime module should still be discoverable");
    assert_eq!(compiler.module(process_id).state, ModuleState::InterfaceReady);

    assert_eq!(capture.count(&["fz", "compiler", "source_loaded"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "parsed"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "interface_ready"]), 1);

    let parsed_phase_events = state_start_events_for_target(&capture, "parsed");
    assert_eq!(
        parsed_phase_events.len(),
        1,
        "one runtime parse should produce one parsed phase start"
    );
    assert!(
        state_work_events(&capture)
            .iter()
            .any(|ev| ev.kind == EventKind::SpanStop && ev.measurements.get("elapsed_ns").is_some()),
        "compiler state timing must report elapsed_ns"
    );

    compiler
        .validate_invariants()
        .expect("runtime interface cache should satisfy compiler invariants");
}

#[test]
fn body_surface_is_cached_and_exposes_stable_root_group_mapping_without_lowering() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let root = compiler.register_root_source(
        "body-surface.fz",
        r#"
fn main(x), do: x
fn helper(), do: nil

defmodule Nested do
  fn local(x), do: x
end
"#
        .to_string(),
        &tel,
    );

    let first = compiler
        .ensure_body_surface(root, &tel)
        .expect("root body surface should build");
    let second = compiler
        .ensure_body_surface(root, &tel)
        .expect("root body surface should come from cache");

    assert_eq!(first.owner_module, "");
    assert_eq!(first.groups.len(), 3);
    assert_eq!(second.groups.len(), 3);
    assert_eq!(first.groups[0].qualified_name(), "main");
    assert_eq!(first.groups[0].id, FnGroupId(0));
    assert_eq!(first.groups[1].qualified_name(), "helper");
    assert_eq!(first.groups[1].id, FnGroupId(1));
    assert_eq!(first.groups[2].qualified_name(), "Nested.local");
    assert_eq!(first.groups[2].id, FnGroupId(2));
    assert_eq!(compiler.module(root).state, ModuleState::BodySurfaceReady);
    assert_eq!(capture.count(&["fz", "compiler", "body_surface_ready"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "fn_group_discovered"]), 3);
    assert_eq!(capture.count(&["fz", "compiler", "cache_hit"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "runtime_lowered"]), 0);

    compiler
        .validate_invariants()
        .expect("body-surface cache should preserve compiler invariants");
}

#[test]
fn named_source_module_body_surface_tracks_only_its_own_groups() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let root = compiler.register_root_source(
        "named-body-surface.fz",
        r#"
fn main(), do: nil

defmodule Nested do
  fn local(x), do: x
  fn helper(x, y), do: x
end
"#
        .to_string(),
        &tel,
    );

    compiler
        .ensure_source_module_interfaces(root, &tel)
        .expect("source module interfaces should build");
    let nested = ModuleName::parse_dotted("Nested").expect("valid module name");
    let nested_id = compiler
        .module_id_for_name(&nested)
        .expect("Nested module should be registered");
    let surface = compiler
        .ensure_body_surface(nested_id, &tel)
        .expect("named body surface should come from cache");

    assert_eq!(surface.owner_module, "Nested");
    assert_eq!(surface.groups.len(), 2);
    assert_eq!(surface.groups[0].qualified_name(), "Nested.local");
    assert_eq!(surface.groups[0].id, FnGroupId(0));
    assert_eq!(surface.groups[1].qualified_name(), "Nested.helper");
    assert_eq!(surface.groups[1].id, FnGroupId(1));
    assert_eq!(surface.groups[1].source.arity, 2);
    assert!(
        capture
            .find(&["fz", "compiler", "fn_group_discovered"])
            .into_iter()
            .any(|ev| captured_str(&ev, "owner_module") == "Nested"),
        "named body-surface discovery should name the owning module"
    );
    assert_eq!(capture.count(&["fz", "compiler", "runtime_lowered"]), 0);

    compiler
        .validate_invariants()
        .expect("named module body surface should preserve compiler invariants");
}

#[test]
fn compiler_invariants_accept_consistent_world_state() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let root = compiler.register_root_source("fixtures/quicksort/input.fz", "fn main(), do: nil\n".to_string(), &tel);
    compiler
        .ensure_interface_table(root, &tel)
        .expect("root interface should build");
    let process = compiler
        .discover_runtime_module(&ModuleName::parse_dotted("Process").expect("valid module name"), &tel)
        .expect("runtime module");
    compiler
        .ensure_runtime_module_interface(&ModuleName::parse_dotted("Process").expect("valid module name"), &tel)
        .expect("Process interface should build");

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
    let module_id = compiler
        .discover_runtime_module(&ModuleName::parse_dotted("Process").expect("valid module name"), &tel)
        .expect("runtime module");

    compiler.world.modules[module_id.0 as usize].file_id = FileId(99);

    let err = compiler
        .validate_invariants()
        .expect_err("broken module/file link must fail validation");
    assert!(
        err.to_string().contains("references missing file"),
        "unexpected invariant error: {err}"
    );
}

#[test]
fn source_module_macro_exports_are_registered_from_compiler_owned_source() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let root = compiler.register_root_source(
        "macro-exports.fz",
        r#"
defmacro make_const(name, value) do
  {:fn_def, name, value}
end

defmodule Macros do
  defmacro bump(x), do: quote do: unquote(x) + 1
end
"#
        .to_string(),
        &tel,
    );

    let exports = compiler
        .ensure_source_module_macro_exports(root, &tel)
        .expect("root macro exports should collect");
    let macros = ModuleName::parse_dotted("Macros").expect("valid module name");
    let macros_id = compiler
        .module_id_for_name(&macros)
        .expect("named module should be registered in compiler world");

    assert!(exports.root.contains(&("make_const".to_string(), 2)));
    assert!(
        exports
            .modules
            .get(&macros)
            .expect("Macros exports")
            .contains(&("bump".to_string(), 1))
    );
    assert_eq!(compiler.module(root).state, ModuleState::Parsed);
    assert_eq!(compiler.module(macros_id).origin, ModuleOrigin::Filesystem);
    assert!(
        compiler
            .module(macros_id)
            .macro_exports
            .as_ref()
            .expect("module record stores macro exports")
            .contains(&("bump".to_string(), 1))
    );

    compiler
        .validate_invariants()
        .expect("macro export registration should preserve compiler invariants");
}

#[test]
fn runtime_reachability_marks_only_live_runtime_modules_with_reasons() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let app = ModuleName::parse_dotted("App").expect("valid module");
    let utf8 = ModuleName::parse_dotted("Utf8").expect("valid module");
    let process = ModuleName::parse_dotted("Process").expect("valid module");
    let mut roots = BTreeMap::new();
    roots.insert(
        app.clone(),
        ModuleInterface {
            name: app,
            abi_version: crate::modules::interface::FZ_INTERFACE_ABI_VERSION,
            imports: vec![crate::modules::interface::InterfaceImport {
                module: utf8.clone(),
                only: Vec::new(),
                except: Vec::new(),
            }],
            exports: Vec::new(),
            types: Vec::new(),
            protocols: Vec::new(),
            protocol_impls: Vec::new(),
            docs: None,
            fingerprint_inputs: Vec::new(),
        },
    );

    let reachable = compiler
        .discover_runtime_reachable_modules(
            &roots,
            [RuntimeReachabilitySeed::new(
                utf8.clone(),
                "program_runtime_reference",
                None,
            )],
            &tel,
        )
        .expect("runtime reachability should succeed");

    let reachable_names = reachable
        .iter()
        .map(|id| compiler.module(*id).key.render())
        .collect::<Vec<_>>();
    assert!(reachable_names.contains(&"Utf8".to_string()));
    assert!(!reachable_names.contains(&"Process".to_string()));

    let utf8_id = compiler
        .module_id_for_name(&utf8)
        .expect("Utf8 module record should exist");
    assert!(compiler.module(utf8_id).reachability.runtime);
    assert_eq!(compiler.module(utf8_id).state, ModuleState::InterfaceReady);
    if let Some(process_id) = compiler.module_id_for_name(&process) {
        assert!(
            !compiler.module(process_id).reachability.runtime,
            "dead runtime module may be discovered incidentally, but must stay runtime-cold"
        );
    }

    let reasons = capture
        .find(&["fz", "compiler", "runtime_module_reachable"])
        .into_iter()
        .filter(|ev| captured_str(ev, "module_key") == "Utf8")
        .map(|ev| captured_str(&ev, "reason").to_string())
        .collect::<Vec<_>>();
    assert!(
        reasons.contains(&"program_import".to_string()) || reasons.contains(&"program_runtime_reference".to_string()),
        "Utf8 should become reachable from the program, reasons: {reasons:?}"
    );

    compiler
        .validate_invariants()
        .expect("runtime reachability should preserve compiler invariants");
}
