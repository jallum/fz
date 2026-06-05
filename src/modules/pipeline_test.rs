use super::*;
use crate::compiler::Compiler;
use crate::ir_interp::run_main;
use crate::telemetry::{Capture, ConfiguredTelemetry, NullTelemetry, Value};
use std::env::temp_dir;
use std::fs::remove_dir_all;
use std::process;

fn compiler() -> Compiler {
    Compiler::new()
}

#[test]
fn execution_graph_loads_runtime_import_without_user_providers() {
    let mut concrete_types = crate::types::new();
    let mut compiler = compiler();
    let tel = NullTelemetry;
    let providers = ProviderInputs::new(
        temp_dir()
            .join(format!("fz-runtime-graph-{}", process::id()))
            .display()
            .to_string(),
        Vec::new(),
    );
    let source = r#"
defmodule User do
  import Utf8, only: [valid?: 1]
  fn run(bytes), do: valid?(bytes)
end
"#;

    let frontend = compile_source_with_providers(
        compiler.world_mut(),
        &mut concrete_types,
        source.to_string(),
        "user.fz".to_string(),
        &providers,
        &tel,
    )
    .unwrap_or_else(|_| panic!("frontend result"));
    let checked = checked_module_for_mode(&mut concrete_types, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    let graph = prepare_execution_graph(
        compiler.world_mut(),
        &mut concrete_types,
        checked,
        &providers,
        &tel,
        CompileMode::Normal,
    )
    .unwrap_or_else(|_| panic!("execution graph"));

    let modules = graph
        .units
        .iter()
        .filter_map(|unit| unit.module.as_ref().map(ModuleName::dotted))
        .collect::<Vec<_>>();
    assert!(modules.contains(&"User".to_string()));
    assert!(modules.contains(&"Utf8".to_string()));
    assert!(!modules.contains(&"Process".to_string()));
}

#[test]
fn execution_graph_only_lowers_and_plans_live_runtime_modules() {
    let mut concrete_types = crate::types::new();
    let mut compiler = compiler();
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());
    let providers = ProviderInputs::new(
        temp_dir()
            .join(format!("fz-runtime-live-{}", process::id()))
            .display()
            .to_string(),
        Vec::new(),
    );
    let source = r#"
defmodule User do
  import Utf8, only: [valid?: 1]
  fn run(bytes), do: valid?(bytes)
end
"#;

    let frontend = compile_source_with_providers(
        compiler.world_mut(),
        &mut concrete_types,
        source.to_string(),
        "user.fz".to_string(),
        &providers,
        &tel,
    )
    .unwrap_or_else(|_| panic!("frontend result"));
    let checked = checked_module_for_mode(&mut concrete_types, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    let graph = prepare_execution_graph(
        compiler.world_mut(),
        &mut concrete_types,
        checked,
        &providers,
        &tel,
        CompileMode::Normal,
    )
    .unwrap_or_else(|_| panic!("execution graph"));

    let modules = graph
        .units
        .iter()
        .filter_map(|unit| unit.module.as_ref().map(ModuleName::dotted))
        .collect::<Vec<_>>();
    assert!(modules.contains(&"Utf8".to_string()));
    assert!(!modules.contains(&"Process".to_string()));

    let utf8_reachable = capture
        .find(&["fz", "compiler", "runtime_module_reachable"])
        .into_iter()
        .filter(|ev| matches!(ev.metadata.get("module_key"), Some(Value::Str(m)) if m == "Utf8"))
        .count();
    assert_eq!(utf8_reachable, 1, "Utf8 should become reachable once");
    assert!(
        !capture
            .find(&["fz", "compiler", "runtime_module_reachable"])
            .into_iter()
            .any(|ev| matches!(ev.metadata.get("module_key"), Some(Value::Str(m)) if m == "Process")),
        "dead runtime module Process must stay cold"
    );
    assert!(
        capture
            .find(&["fz", "compiler", "runtime_planned"])
            .into_iter()
            .any(|ev| matches!(ev.metadata.get("module_key"), Some(Value::Str(m)) if m == "Utf8")),
        "Utf8 should be explicitly planned as live runtime work"
    );
    let utf8_lowered = capture
        .find(&["fz", "compiler", "runtime_lowered"])
        .into_iter()
        .find(|ev| matches!(ev.metadata.get("module_key"), Some(Value::Str(m)) if m == "Utf8"))
        .expect("Utf8 lowered event");
    assert!(
        matches!(utf8_lowered.measurements.get("units"), Some(Value::U64(1))),
        "Utf8 lowering should report one live unit, event: {utf8_lowered:?}"
    );
    let utf8_planned = capture
        .find(&["fz", "compiler", "runtime_planned"])
        .into_iter()
        .find(|ev| matches!(ev.metadata.get("module_key"), Some(Value::Str(m)) if m == "Utf8"))
        .expect("Utf8 planned event");
    assert!(
        matches!(utf8_planned.measurements.get("units"), Some(Value::U64(1))),
        "Utf8 planning should report one live unit, event: {utf8_planned:?}"
    );
    assert!(
        !capture
            .find(&["fz", "compiler", "runtime_planned"])
            .into_iter()
            .any(|ev| matches!(ev.metadata.get("module_key"), Some(Value::Str(m)) if m == "Process")),
        "dead runtime module Process must not be planned"
    );

    compiler
        .validate_invariants()
        .expect("execution graph must preserve runtime reachability invariants");
}

#[test]
fn protocol_impl_reduce_callback_plans_to_fixed_point() {
    let mut concrete_types = crate::types::new();
    let mut compiler = compiler();
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "planner", "planned"], capture.handler());
    let providers = ProviderInputs::new(
        temp_dir()
            .join(format!("fz-protocol-reduce-{}", process::id()))
            .display()
            .to_string(),
        Vec::new(),
    );
    let source = r#"
defprotocol Reducible do
  fn reduce(value, acc, reducer)
end

defmodule List do
  fn reduce([], {:cont, acc}, _reducer), do: {:done, acc}
  fn reduce([head | tail], {:cont, acc}, reducer), do: reduce(tail, reducer.(head, acc), reducer)
  fn reduce(_list, {:halt, acc}, _reducer), do: {:halted, acc}
end

defimpl Reducible, for: List do
  fn reduce(list, acc, reducer), do: List.reduce(list, acc, reducer)
end

fn main() do
  Reducible.reduce([1, 2, 3], {:cont, 0}, fn (x, acc) -> {:cont, x + acc} end)
end
"#;

    let frontend = compile_source_with_providers(
        compiler.world_mut(),
        &mut concrete_types,
        source.to_string(),
        "protocol_reduce.fz".to_string(),
        &providers,
        &tel,
    )
    .unwrap_or_else(|_| panic!("frontend result"));
    let checked = checked_module_for_mode(&mut concrete_types, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    prepare_execution_graph(
        compiler.world_mut(),
        &mut concrete_types,
        checked,
        &providers,
        &tel,
        CompileMode::Normal,
    )
    .unwrap_or_else(|_| panic!("execution graph"));

    let max_pops = capture
        .find(&["fz", "planner", "planned"])
        .iter()
        .filter_map(|ev| match ev.measurements.get("worklist_pops") {
            Some(Value::U64(pops)) => Some(*pops),
            _ => None,
        })
        .max()
        .unwrap_or(0);
    assert!(
        max_pops <= 100,
        "protocol reduce planning should converge without oscillating; max pops {max_pops}"
    );
}

/// Provider source whose `Contracts.Collectable.id/1` impl returns 42. The
/// fixed return makes the consumer's dispatch observable end-to-end.
const PROVIDER_SRC: &str = r#"defmodule Contracts do
  defprotocol Collectable do
fn id(value)
  end

  defimpl Collectable, for: List do
fn id(value), do: 42
  end
end
"#;

/// Consumer that calls the provider's protocol through a provider-boundary
/// call edge, then a top-level `main` to run.
const CONSUMER_SRC: &str = r#"defmodule User do
  fn run(), do: Contracts.Collectable.id([1])
end
fn main(), do: User.run()
"#;

struct StructuralProviderFixture {
    artifact_root: String,
}

impl Drop for StructuralProviderFixture {
    fn drop(&mut self) {
        let _ = remove_dir_all(&self.artifact_root);
    }
}

/// Compile `PROVIDER_SRC` through the real frontend, then emit it as a
/// STRUCTURAL `.fzo` (`from_unit_ir`, carrying the module's real source
/// files) plus its `.fzi` into a fresh temp `ArtifactStore`. This is exactly
/// the production `fz build` emit shape, so the consumer below loads the
/// provider structurally — no recompile.
fn write_structural_provider(tag: &str) -> (StructuralProviderFixture, ModuleName) {
    let mut t = crate::types::new();
    let mut compiler = compiler();
    let tel = NullTelemetry;
    let provider = compile_source_with_compiler_types(
        compiler.world_mut(),
        &mut t,
        PROVIDER_SRC.to_string(),
        "contracts.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|err| panic!("provider frontend: {:?}", err.diagnostics));
    let contracts = ModuleName::from_segments(vec!["Contracts".to_string()]);
    let interface = provider._prog.module_interfaces[&contracts].clone();

    let unit = CompiledUnit::from_ir_module_with_plan(
        provider.module,
        Some(provider.module_plan),
        Some(interface.clone()),
        Diagnostics::new(),
    );
    let sources = unit
        .code
        .referenced_files()
        .into_iter()
        .map(|fid| provider.sm.file(fid).to_portable(fid))
        .collect::<Vec<_>>();
    assert!(
        !sources.is_empty(),
        "provider module must reference at least one source file"
    );
    let fzo = FzoArtifact::from_unit_ir(&unit, sources, Vec::new());
    assert_eq!(fzo.unit_payload.format, FZO_PAYLOAD_IR_UNIT_V1);

    let artifact_root = temp_dir()
        .join(format!("fz-structural-load-{}-{}", process::id(), tag))
        .display()
        .to_string();
    let _ = remove_dir_all(&artifact_root);
    let store = ArtifactStore::new(&artifact_root);
    let mut interfaces = BTreeMap::new();
    interfaces.insert(contracts.clone(), interface);
    store.write_fzi_artifacts(&tel, &interfaces).unwrap();
    store.write_fzo_artifacts(&tel, [&fzo]).unwrap();

    (StructuralProviderFixture { artifact_root }, contracts)
}

/// Drive `CONSUMER_SRC` through the production pipeline against a structural
/// provider in `root`, returning the prepared graph and the consumer's
/// SourceMap (which the loader merges provider sources into).
fn prepare_consumer_against(root: &str, provider: &ModuleName, tel: &dyn Telemetry) -> PreparedExecutionGraph {
    let mut t = crate::types::new();
    let mut compiler = compiler();
    let providers = ProviderInputs::new(root.to_string(), vec![provider.clone()]);
    let frontend = compile_source_with_providers(
        compiler.world_mut(),
        &mut t,
        CONSUMER_SRC.to_string(),
        "user.fz".to_string(),
        &providers,
        tel,
    )
    .unwrap_or_else(|_| panic!("consumer frontend"));
    let checked = checked_module_for_mode(&mut t, frontend, tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    prepare_execution_graph(
        compiler.world_mut(),
        &mut t,
        checked,
        &providers,
        tel,
        CompileMode::Normal,
    )
    .unwrap_or_else(|err| panic!("execution graph: {err:?}"))
}

/// Gate 1: a structurally-loaded provider links and runs WITHOUT recompiling
/// from source — the consumer's protocol dispatch reaches the provider's
/// impl and returns 42.
#[test]
fn structural_provider_loads_and_runs_without_recompile() {
    let tel = NullTelemetry;
    let (fixture, provider) = write_structural_provider("run");
    let graph = prepare_consumer_against(&fixture.artifact_root, &provider, &tel);

    let module = if graph.units.len() > 1 {
        link_ir_units(&graph.units).expect("link ir units")
    } else {
        graph.units[0].code.clone()
    };
    let result = run_main(&tel, &module).expect("run linked image");
    assert_eq!(result, 42, "structural provider dispatch returns 42");
}

/// Gate 2: the provider was materialized structurally (`kind: "ir-unit"`) and
/// the frontend did NOT run for it — `fz.frontend.parsed` fires once (the
/// consumer) even though two modules are in the linked graph.
#[test]
fn structural_provider_is_materialized_without_frontend() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz"], capture.handler());

    let (fixture, provider) = write_structural_provider("no-recompile");
    let _graph = prepare_consumer_against(&fixture.artifact_root, &provider, &tel);

    let materialized = capture.find(&["fz", "module", "unit_materialized"]);
    let ir_units = materialized
        .iter()
        .filter(|ev| {
            matches!(
                ev.metadata.get("kind"),
                Some(Value::Str(kind)) if kind == "ir-unit"
            )
        })
        .filter(|ev| {
            matches!(
                ev.metadata.get("module"),
                Some(Value::Str(m)) if m == "Contracts"
            )
        })
        .count();
    assert_eq!(
        ir_units, 1,
        "Contracts must be materialized once as an ir-unit, found events: {materialized:?}"
    );
    assert!(
        !materialized.iter().any(|ev| matches!(
            ev.metadata.get("kind"),
            Some(Value::Str(kind)) if kind == "source"
        )),
        "no provider should take the source-recompile branch"
    );
    // The frontend ran exactly once — for the consumer. A recompiled
    // provider would parse a second time.
    assert_eq!(
        capture.count(&["fz", "frontend", "parsed"]),
        1,
        "frontend parses only the consumer, never the structural provider"
    );
}

/// Gate 3: provider spans render REAL diagnostics after structural load —
/// the source-merge + FileId-remap make a non-DUMMY provider span resolve
/// against the consumer's SourceMap to the provider's actual source line.
#[test]
fn structural_provider_spans_resolve_to_real_source() {
    let tel = NullTelemetry;
    let (fixture, provider) = write_structural_provider("diag");
    let graph = prepare_consumer_against(&fixture.artifact_root, &provider, &tel);

    let provider_unit = graph
        .units
        .iter()
        .find(|unit| unit.module.as_ref().is_some_and(|m| m.dotted() == "Contracts"))
        .expect("loaded provider unit present in graph");

    // A concrete, non-DUMMY span from the loaded+remapped provider module.
    let mut span = None;
    provider_unit.code.visit_spans(&mut |s| {
        if span.is_none() && !s.is_dummy() {
            span = Some(s);
        }
    });
    let span = span.expect("provider module carries a non-DUMMY span after load");

    // It resolves against the CONSUMER's SourceMap (proves the merge) to the
    // provider's real source — not DUMMY, and the snippet is provider text.
    let loc = graph.sm.locate(span);
    let snippet = &graph.sm.file(loc.file).bytes[loc.line_start as usize..loc.line_end as usize];
    assert!(
        PROVIDER_SRC.contains(snippet) && !snippet.trim().is_empty(),
        "remapped provider span resolves to a real provider source line, got: {snippet:?}"
    );
}

#[test]
fn linked_runtime_graph_keeps_cont_dispatches_for_enum_take_drop_split() {
    use crate::fz_ir::{CallsiteId, EmitSlot, Term};

    let mut t = crate::types::new();
    let mut compiler = compiler();
    let tel = NullTelemetry;
    let providers = ProviderInputs::new(
        temp_dir()
            .join(format!("fz-enum-linked-{}", process::id()))
            .display()
            .to_string(),
        Vec::new(),
    );
    let source = include_str!("../../fixtures/enum_take_drop_split/input.fz");

    let frontend = compile_source_with_providers(
        compiler.world_mut(),
        &mut t,
        source.to_string(),
        "enum_take_drop_split_input.fz".to_string(),
        &providers,
        &tel,
    )
    .unwrap_or_else(|_| panic!("frontend result"));
    let checked = checked_module_for_mode(&mut t, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    let graph = prepare_execution_graph(
        compiler.world_mut(),
        &mut t,
        checked,
        &providers,
        &tel,
        CompileMode::Normal,
    )
    .unwrap_or_else(|err| panic!("execution graph: {err:?}"));
    let linked = graph.module;
    let mt = graph.module_plan;

    for (spec_key, spec) in &mt.specs {
        let body = linked.fn_by_id(spec_key.fn_id);
        for block in &body.blocks {
            let Term::Call { ident, .. } = &block.terminator else {
                continue;
            };
            let cont_callsite = CallsiteId::new(body.id, ident, EmitSlot::Cont);
            let direct_callsite = CallsiteId::new(body.id, ident, EmitSlot::Direct);
            let direct_target = spec.local_call_target(&direct_callsite);
            assert!(
                spec.local_call_target(&cont_callsite).is_some(),
                "linked runtime graph missing Cont dispatch for {} spec {:?} at {:?}; direct target: {:?}; direct target body: {:?}; direct effective return: {:?}; available call_edges: {:?}",
                body.name,
                spec_key,
                cont_callsite,
                direct_target,
                direct_target.map(|target| linked.fn_by_id(target.fn_id).name.clone()),
                direct_target.and_then(|target| mt.effective_returns.get(&target.body_key())),
                spec.call_edges.keys().collect::<Vec<_>>()
            );
        }
    }
}

#[test]
fn linked_runtime_graph_keeps_cont_dispatches_for_spawn_with_captures() {
    use crate::fz_ir::{CallsiteId, EmitSlot, Term};

    let mut t = crate::types::new();
    let mut compiler = compiler();
    let tel = NullTelemetry;
    let providers = ProviderInputs::new(
        temp_dir()
            .join(format!("fz-spawn-linked-{}", process::id()))
            .display()
            .to_string(),
        Vec::new(),
    );
    let source = include_str!("../../fixtures/spawn_with_captures/input.fz");

    let frontend = compile_source_with_providers(
        compiler.world_mut(),
        &mut t,
        source.to_string(),
        "spawn_with_captures_input.fz".to_string(),
        &providers,
        &tel,
    )
    .unwrap_or_else(|_| panic!("frontend result"));
    let checked = checked_module_for_mode(&mut t, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    let graph = prepare_execution_graph(
        compiler.world_mut(),
        &mut t,
        checked,
        &providers,
        &tel,
        CompileMode::Normal,
    )
    .unwrap_or_else(|err| panic!("execution graph: {err:?}"));
    let linked = graph.module;
    let mt = graph.module_plan;

    for (spec_key, spec) in &mt.specs {
        let body = linked.fn_by_id(spec_key.fn_id);
        for block in &body.blocks {
            let Term::Call { ident, .. } = &block.terminator else {
                continue;
            };
            let cont_callsite = CallsiteId::new(body.id, ident, EmitSlot::Cont);
            let direct_callsite = CallsiteId::new(body.id, ident, EmitSlot::Direct);
            let direct_target = spec.local_call_target(&direct_callsite);
            assert!(
                spec.local_call_target(&cont_callsite).is_some(),
                "linked runtime graph missing Cont dispatch for {} spec {:?} at {:?}; direct target: {:?}; direct target body: {:?}; direct effective return: {:?}; available call_edges: {:?}",
                body.name,
                spec_key,
                cont_callsite,
                direct_target,
                direct_target.map(|target| linked.fn_by_id(target.fn_id).name.clone()),
                direct_target.and_then(|target| mt.effective_returns.get(&target.body_key())),
                spec.call_edges.keys().collect::<Vec<_>>()
            );
        }
    }
}
