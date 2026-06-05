use super::*;
use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind, Value};
use std::sync::Arc;

fn named_module(name: &str) -> ModuleKey {
    ModuleKey::Named(ModuleName::parse_dotted(name).expect("valid module name"))
}

fn readiness_work_events(capture: &Capture) -> Vec<crate::telemetry::capture::OwnedEvent> {
    capture
        .find(&["fz", "compiler", "readiness_work"])
        .into_iter()
        .collect()
}

fn readiness_start_events_for_fact(
    capture: &Capture,
    requested_fact: &str,
) -> Vec<crate::telemetry::capture::OwnedEvent> {
    readiness_work_events(capture)
        .into_iter()
        .filter(|ev| ev.kind == EventKind::SpanStart)
        .filter(|ev| metadata_str(ev, "requested_readiness") == requested_fact)
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
fn compiler_readiness_cache_hits_skip_repeat_work_and_emit_timing_telemetry() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let module_id = compiler.world.declare_module(
        Some(named_module("Process")),
        ModuleOrigin::EmbeddedRuntime,
        FileOrigin::EmbeddedRuntime("Process".to_string()),
        SourceDescriptor {
            source_name: "runtime:Process".to_string(),
            text: Arc::<str>::from("defmodule Process do\nend\n"),
            parse_kind: ParseKind::Prelude,
        },
        &tel,
    );

    let again = compiler.world.declare_module(
        Some(named_module("Process")),
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
    let advanced = compiler.ensure_module_readiness(module_id, ModuleReadinessFact::Parsed, &tel, |_| {
        work_runs += 1;
    });
    let cached = compiler.ensure_module_readiness(module_id, ModuleReadinessFact::Parsed, &tel, |_| {
        work_runs += 1;
    });

    assert!(advanced, "first ensure should record the readiness fact");
    assert!(!cached, "second ensure should hit the cache");
    assert_eq!(work_runs, 1, "cache hit must not rerun readiness work");
    assert!(compiler.module(module_id).readiness.has(ModuleReadinessFact::Parsed));

    assert_eq!(capture.count(&["fz", "compiler", "file_registered"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "file_cache_hit"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "module_discovered"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "module_declared"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "module_cache_hit"]), 2);
    assert_eq!(capture.count(&["fz", "compiler", "cache_miss"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "cache_hit"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "readiness_recorded"]), 1);

    let readiness_events = readiness_work_events(&capture);
    assert_eq!(
        readiness_events.len(),
        2,
        "one readiness miss should produce one start/stop span pair"
    );
    let start = readiness_events
        .iter()
        .find(|ev| ev.kind == EventKind::SpanStart)
        .expect("readiness span start");
    let stop = readiness_events
        .iter()
        .find(|ev| ev.kind == EventKind::SpanStop)
        .expect("readiness span stop");
    assert_eq!(metadata_str(start, "requested_readiness"), "parsed");
    assert!(
        stop.measurements.get("elapsed_ns").is_some(),
        "readiness stop event must carry elapsed_ns"
    );
}

#[test]
fn named_module_reference_mints_one_entity_and_declaration_attaches_to_it() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let process = ModuleName::parse_dotted("Process").expect("valid module name");
    let referenced = compiler.world.reference_named_module(process.clone(), &tel);
    assert_eq!(compiler.module(referenced).origin(), None);

    let declared = compiler.world.declare_module(
        Some(ModuleKey::Named(process.clone())),
        ModuleOrigin::EmbeddedRuntime,
        FileOrigin::EmbeddedRuntime("Process".to_string()),
        SourceDescriptor {
            source_name: "runtime:Process".to_string(),
            text: Arc::<str>::from("defmodule Process do\nend\n"),
            parse_kind: ParseKind::Prelude,
        },
        &tel,
    );

    assert_eq!(
        referenced, declared,
        "declaration must attach to the referenced module entity"
    );
    assert_eq!(compiler.module(declared).origin(), Some(ModuleOrigin::EmbeddedRuntime));
    assert_eq!(compiler.module_id_for_name(&process), Some(declared));
    assert_eq!(capture.count(&["fz", "compiler", "module_discovered"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "module_declared"]), 1);
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
    assert!(compiler.module(root).readiness.has(ModuleReadinessFact::Parsed));

    assert_eq!(capture.count(&["fz", "compiler", "source_loaded"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "parsed"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "cache_miss"]), 2);
    assert_eq!(capture.count(&["fz", "compiler", "cache_hit"]), 1);

    let parsed_phase_events = readiness_start_events_for_fact(&capture, "parsed");
    assert_eq!(
        parsed_phase_events.len(),
        1,
        "one parse should produce one parsed phase start"
    );
    assert!(
        readiness_work_events(&capture)
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
    assert!(
        compiler
            .module(process_id)
            .readiness
            .has(ModuleReadinessFact::InterfaceTableReady)
    );

    assert_eq!(capture.count(&["fz", "compiler", "source_loaded"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "parsed"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "interface_ready"]), 1);

    let parsed_phase_events = readiness_start_events_for_fact(&capture, "parsed");
    assert_eq!(
        parsed_phase_events.len(),
        1,
        "one runtime parse should produce one parsed phase start"
    );
    assert!(
        readiness_work_events(&capture)
            .iter()
            .any(|ev| ev.kind == EventKind::SpanStop && ev.measurements.get("elapsed_ns").is_some()),
        "compiler state timing must report elapsed_ns"
    );

    compiler
        .validate_invariants()
        .expect("runtime interface cache should satisfy compiler invariants");
}

#[test]
fn primitive_prelude_is_prepared_once_as_compiler_owned_bootstrap_source() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = Compiler::new();
    let prelude_id = compiler.discover_primitive_prelude(&tel);

    let first = compiler
        .ensure_prepared_prelude(prelude_id, &tel)
        .expect("primitive prelude should prepare");
    let second = compiler
        .ensure_prepared_prelude(prelude_id, &tel)
        .expect("prepared primitive prelude should come from cache");

    assert!(
        first.program.items.iter().all(|item| matches!(&**item, Item::Fn(_))),
        "prepared prelude should be flattened to callable items"
    );
    assert_eq!(first.program.items.len(), second.program.items.len());
    assert_eq!(first.imports, second.imports);
    assert_eq!(
        compiler.module(prelude_id).origin(),
        Some(ModuleOrigin::PrimitivePrelude)
    );
    let prelude_parsed = capture
        .find(&["fz", "compiler", "parsed"])
        .into_iter()
        .filter(|ev| captured_str(ev, "module_origin") == "primitive_prelude")
        .count();
    assert_eq!(prelude_parsed, 1);
    assert_eq!(capture.count(&["fz", "compiler", "prelude_prepared"]), 1);
    assert_eq!(capture.count(&["fz", "compiler", "runtime_lowered"]), 0);

    compiler
        .validate_invariants()
        .expect("prepared prelude cache should preserve compiler invariants");
}

#[test]
fn primitive_prelude_registers_named_operator_functions_in_compiler_world() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let prelude_id = compiler.discover_primitive_prelude(&tel);

    compiler
        .ensure_prepared_prelude(prelude_id, &tel)
        .expect("primitive prelude should prepare");
    compiler
        .ensure_primitive_prelude_namespace(prelude_id, &tel)
        .expect("primitive prelude namespace should prepare");

    let kernel = ModuleName::parse_dotted("Kernel").expect("valid module name");
    let kernel_id = compiler
        .module_id_for_name(&kernel)
        .expect("Kernel should be registered as a compiler-owned module");

    for (name, arity) in [("+", 2), ("-", 2), ("*", 2), ("/", 2), ("%", 2), ("<>", 2)] {
        let mfa = Mfa::new(kernel_id, name, arity);
        let fn_id = compiler.fn_id_for_mfa(&mfa);
        assert!(
            fn_id.is_some(),
            "primitive prelude should register Kernel.{name}/{arity} in compiler world"
        );
        let owner = compiler
            .world
            .function(fn_id.expect("named prelude fn id"))
            .owner_module_id;
        assert_eq!(
            compiler.module(owner).key,
            Some(ModuleKey::Named(kernel.clone())),
            "primitive prelude operator functions should stay attached to the Kernel module entity"
        );
        let visible = compiler
            .world
            .visible_callable_target(prelude_id, name, arity)
            .unwrap_or_else(|| panic!("primitive prelude should expose visible alias {name}/{arity}"));
        assert_eq!(
            visible, mfa,
            "primitive prelude alias {name}/{arity} should point at Kernel.{name}/{arity}"
        );
        let alias = compiler
            .world
            .visible_callable_aliases(prelude_id)
            .into_iter()
            .find(|alias| alias.name == name && alias.arity == arity)
            .unwrap_or_else(|| panic!("primitive prelude should retain alias metadata for {name}/{arity}"));
        assert_eq!(
            alias.origin,
            crate::compiler::VisibleCallableAliasOrigin::PreludeImport {
                from_module: kernel.clone(),
            },
            "primitive prelude alias provenance should point back at Kernel.{name}/{arity}"
        );
    }
    let plus_specs = compiler
        .world
        .function_declared_interface_specs(&Mfa::new(kernel_id, "+", 2))
        .expect("Kernel.+/2 should carry declared interface specs");
    assert_eq!(plus_specs.len(), 4);
    assert_eq!(
        compiler.world.function_contract_state(&Mfa::new(kernel_id, "+", 2)),
        Some(FunctionContractState::SourceAndInterfaceReady),
        "Kernel.+/2 should advertise contract readiness once prelude preparation and source interfaces run"
    );
    let concat_specs = compiler
        .world
        .function_declared_interface_specs(&Mfa::new(kernel_id, "<>", 2))
        .expect("Kernel.<>/2 should carry declared interface specs");
    assert_eq!(concat_specs.len(), 1);

    compiler
        .validate_invariants()
        .expect("primitive prelude operator registration should preserve compiler invariants");
}

#[test]
fn prelude_bootstrap_resolve_materializes_kernel_contract_from_demands() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let prelude_id = compiler.discover_primitive_prelude(&tel);
    let parsed = compiler
        .ensure_prelude(prelude_id, &tel)
        .expect("primitive prelude should parse");
    let staged = Program {
        items: parsed.items,
        ..Program::default()
    };
    let mut t = crate::types::new();
    let resolved = compiler
        .world_mut()
        .resolve_program_from_demands(&mut t, None, staged, BTreeMap::new(), &tel);
    assert!(
        resolved.is_ok(),
        "prelude bootstrap should resolve through compiler demand loop: {resolved:?}"
    );
    let kernel = ModuleName::parse_dotted("Kernel").expect("valid module name");
    let kernel_id = compiler
        .module_id_for_name(&kernel)
        .expect("Kernel should be discovered while satisfying prelude imports");
    assert!(
        compiler.world().module_contract(kernel_id).is_some(),
        "Kernel contract should be recorded on the compiler-owned module record"
    );
}

#[test]
fn prelude_bootstrap_survives_after_root_resolution_in_same_compiler_world() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let root = compiler.register_root_source(
        "same-world.fz",
        "defmodule Local do\n  fn run(x), do: x\nend\n".to_string(),
        &tel,
    );
    let parsed = compiler.ensure_program(root, &tel).expect("root should parse");
    let mut t = crate::types::new();
    let _resolved = compiler
        .world_mut()
        .resolve_program_from_demands(&mut t, Some(root), parsed.program, BTreeMap::new(), &tel)
        .expect("root resolve should succeed");

    let prelude_id = compiler.discover_primitive_prelude(&tel);
    compiler
        .ensure_primitive_prelude_namespace(prelude_id, &tel)
        .expect("primitive prelude namespace should still build");
    let kernel = ModuleName::parse_dotted("Kernel").expect("valid module name");
    let kernel_id = compiler
        .module_id_for_name(&kernel)
        .expect("primitive prelude namespace should register Kernel");
    assert_eq!(
        compiler.world().visible_callable_target(prelude_id, "+", 2),
        Some(Mfa::new(kernel_id, "+", 2)),
        "primitive prelude namespace should expose Kernel.+/2"
    );
    let prepared = compiler.world_mut().ensure_prepared_prelude(prelude_id, &mut t, &tel);
    assert!(
        prepared.is_ok(),
        "prelude bootstrap should survive after root resolution: {prepared:?}"
    );
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
    let nested = ModuleName::parse_dotted("Nested").expect("valid module name");
    let nested_id = compiler
        .module_id_for_name(&nested)
        .expect("Nested module should be registered during body-surface discovery");

    assert_eq!(first.owner_module, "");
    assert_eq!(first.groups.len(), 3);
    assert_eq!(second.groups.len(), 3);
    assert_eq!(first.groups[0].qualified_name(), "main");
    assert_eq!(first.groups[0].id, FnGroupId(0));
    assert_eq!(first.groups[1].qualified_name(), "helper");
    assert_eq!(first.groups[1].id, FnGroupId(1));
    assert_eq!(first.groups[2].qualified_name(), "Nested.local");
    assert_eq!(first.groups[2].id, FnGroupId(2));
    assert_eq!(first.groups[0].source.module_id, root);
    assert_eq!(first.groups[1].source.module_id, root);
    assert_eq!(first.groups[2].source.module_id, nested_id);
    assert!(
        compiler
            .module(root)
            .readiness
            .has(ModuleReadinessFact::BodySurfaceReady)
    );
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
    assert_eq!(surface.groups[0].source.module_id, nested_id);
    assert_eq!(surface.groups[1].source.module_id, nested_id);
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

    let parsed = compiler
        .ensure_prelude(process, &tel)
        .expect("Process source should parse");
    let mut t = crate::types::new();
    let program = Program {
        items: parsed.items,
        ..Program::default()
    };
    compiler.mark_reachable(root, ReachabilityKind::Interface, &tel);
    compiler.mark_reachable(process, ReachabilityKind::Runtime, &tel);
    compiler
        .world
        .check_program_from_roots(
            None,
            Some(process),
            &mut t,
            program,
            parsed.sm,
            crate::frontend::resolve::InterfaceTable::new(),
            &tel,
            crate::modules::pipeline::CompileMode::Normal,
        )
        .expect("runtime unit compile should succeed");

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

    compiler.world.modules[module_id.0 as usize].declaration = Some(ModuleDeclaration {
        origin: ModuleOrigin::EmbeddedRuntime,
        file_id: FileId(99),
    });

    let err = compiler
        .validate_invariants()
        .expect_err("broken module/file link must fail validation");
    assert!(
        err.to_string().contains("references missing file"),
        "unexpected invariant error: {err}"
    );
}

#[test]
fn compiler_invariants_reject_runtime_execution_state_without_readiness_facts() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let process = compiler
        .discover_runtime_module(&ModuleName::parse_dotted("Process").expect("valid module name"), &tel)
        .expect("runtime module");
    compiler
        .ensure_runtime_module_interface(&ModuleName::parse_dotted("Process").expect("valid module name"), &tel)
        .expect("Process interface should build");
    compiler.mark_reachable(process, ReachabilityKind::Runtime, &tel);
    compiler.ensure_module_readiness(process, ModuleReadinessFact::RuntimeLowered, &tel, |_| {});

    let err = compiler
        .validate_invariants()
        .expect_err("runtime lowered state without readiness facts must fail");
    assert!(
        err.to_string().contains("recorded lowered function facts"),
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
    assert!(compiler.module(root).readiness.has(ModuleReadinessFact::Parsed));
    assert_eq!(compiler.module(macros_id).origin(), Some(ModuleOrigin::Filesystem));
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

    let utf8_id = compiler
        .discover_runtime_module(&utf8, &tel)
        .expect("Utf8 runtime module should be discoverable");
    let reachable = compiler
        .discover_runtime_reachable_modules(
            &roots,
            [RuntimeReachabilitySeed::new(utf8_id, "program_runtime_reference", None)],
            &tel,
        )
        .expect("runtime reachability should succeed");

    let reachable_names = reachable
        .iter()
        .map(|id| compiler.module(*id).key_render())
        .collect::<Vec<_>>();
    assert!(reachable_names.contains(&"Utf8".to_string()));
    assert!(!reachable_names.contains(&"Process".to_string()));

    assert!(compiler.module(utf8_id).reachability.runtime);
    assert!(
        compiler
            .module(utf8_id)
            .readiness
            .has(ModuleReadinessFact::InterfaceTableReady)
    );
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

#[test]
fn reference_fn_mints_one_id_and_declare_fn_upgrades_in_place() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let module = ModuleName::parse_dotted("Sample").expect("valid module");
    let module_id = compiler.world.declare_module(
        Some(ModuleKey::Named(module.clone())),
        ModuleOrigin::Filesystem,
        FileOrigin::Filesystem("sample.fz".into()),
        SourceDescriptor {
            source_name: "sample.fz".to_string(),
            text: Arc::<str>::from("defmodule Sample do\nend\n"),
            parse_kind: ParseKind::Program,
        },
        &tel,
    );
    compiler
        .world
        .attach_primitive_prelude_namespace(module_id, &tel)
        .expect("module should accept prelude namespace");

    let mfa = Mfa::new(module_id, "work", 1);
    let referenced = compiler.reference_fn(mfa.clone());
    let referenced_again = compiler.reference_fn(mfa.clone());
    assert_eq!(referenced, referenced_again, "reference_fn should be stable");
    assert_eq!(
        compiler.world.function_contract_state(&mfa),
        Some(FunctionContractState::Referenced)
    );

    let declared = compiler.declare_fn(mfa.clone(), true);
    assert_eq!(
        declared, referenced,
        "declaration must upgrade the referenced function record"
    );
    assert_eq!(
        compiler.world.function_contract_state(&mfa),
        Some(FunctionContractState::Declared)
    );
    assert_eq!(compiler.world.mfa_for_fn_id(declared), Some(&mfa));
    assert_eq!(
        compiler.world.visible_callable_target(module_id, "work", 1),
        Some(mfa.clone()),
        "declared functions should become visible through the module namespace"
    );
    assert!(
        compiler.world.function(declared).declared_extern.is_none(),
        "ordinary source declarations should not grow extern facts"
    );
}

#[test]
fn declare_extern_fn_reuses_referenced_id_and_records_extern_facts() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let module = ModuleName::parse_dotted("Process").expect("valid module");
    let module_id = compiler.world.declare_module(
        Some(ModuleKey::Named(module.clone())),
        ModuleOrigin::EmbeddedRuntime,
        FileOrigin::EmbeddedRuntime("Process".to_string()),
        SourceDescriptor {
            source_name: "runtime:Process".to_string(),
            text: Arc::<str>::from("defmodule Process do\nend\n"),
            parse_kind: ParseKind::Prelude,
        },
        &tel,
    );
    compiler
        .world
        .attach_primitive_prelude_namespace(module_id, &tel)
        .expect("module should accept prelude namespace");

    let mfa = Mfa::new(module_id, "heap_alloc_stats", 0);
    let referenced = compiler.reference_fn(mfa.clone());
    let any_ty = compiler.types().any();
    let declared = compiler.declare_extern_fn(
        mfa.clone(),
        ExternFunctionDecl {
            symbol: "fz_process_heap_alloc_stats".to_string(),
            params: vec![],
            variadic: false,
            ret: crate::fz_ir::ExternTy::Any,
            ret_descr: any_ty,
        },
        true,
    );

    assert_eq!(
        declared, referenced,
        "extern declaration must upgrade the referenced function record"
    );
    assert_eq!(
        compiler.world.function_contract_state(&mfa),
        Some(FunctionContractState::Declared)
    );
    assert_eq!(compiler.world.mfa_for_fn_id(declared), Some(&mfa));
    let record = compiler.world.function(declared);
    let extern_decl = record
        .declared_extern
        .as_ref()
        .expect("extern declaration should be stored on the function record");
    assert_eq!(extern_decl.symbol, "fz_process_heap_alloc_stats");
    assert_eq!(extern_decl.params, Vec::<crate::fz_ir::ExternTy>::new());
    assert_eq!(extern_decl.ret, crate::fz_ir::ExternTy::Any);
    assert_eq!(
        compiler.world.visible_callable_target(module_id, "heap_alloc_stats", 0),
        Some(mfa),
        "extern declarations should publish the function through the module namespace"
    );
}

#[test]
fn declare_anonymous_fn_allocates_in_compiler_owned_fnid_space() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler::new();
    let module = ModuleName::parse_dotted("Flow").expect("valid module");
    let module_id = compiler.world.declare_module(
        Some(ModuleKey::Named(module)),
        ModuleOrigin::Filesystem,
        FileOrigin::Filesystem("flow.fz".into()),
        SourceDescriptor {
            source_name: "flow.fz".to_string(),
            text: Arc::<str>::from("defmodule Flow do\nend\n"),
            parse_kind: ParseKind::Program,
        },
        &tel,
    );

    let first = compiler.declare_anonymous_fn(module_id, FunctionKind::Continuation, "k_after_call");
    let second = compiler.declare_anonymous_fn(module_id, FunctionKind::Lambda, "lambda_0");

    assert_ne!(first, second, "anonymous declarations must allocate distinct fn ids");
    assert_eq!(compiler.world.mfa_for_fn_id(first), None);
    assert_eq!(compiler.world.mfa_for_fn_id(second), None);

    let first_record = compiler.function(first);
    let second_record = compiler.function(second);
    assert_eq!(first_record.owner_module_id, module_id);
    assert_eq!(second_record.owner_module_id, module_id);
    assert_eq!(first_record.kind, FunctionKind::Continuation);
    assert_eq!(second_record.kind, FunctionKind::Lambda);
    assert_eq!(first_record.contract_state, FunctionContractState::Declared);
    assert_eq!(second_record.contract_state, FunctionContractState::Declared);
    assert!(matches!(first_record.key, FunctionKey::Anonymous(_)));
    assert!(matches!(second_record.key, FunctionKey::Anonymous(_)));
    assert_eq!(first_record.debug_name, "k_after_call");
    assert_eq!(second_record.debug_name, "lambda_0");
}
