use super::*;
use crate::compiler::Compiler;
use crate::frontend::compile_source_with_compiler_types;
use crate::telemetry::{Capture, ConfiguredTelemetry, NullTelemetry, Value};

fn compiler() -> Compiler {
    Compiler::new()
}

#[test]
fn execution_graph_loads_runtime_import_without_user_providers() {
    let mut concrete_types = crate::types::new();
    let mut compiler = compiler();
    let tel = NullTelemetry;
    let source = r#"
defmodule User do
  import Utf8, only: [valid?: 1]
  fn run(bytes), do: valid?(bytes)
end
"#;

    let frontend = compile_source_with_compiler_types(
        compiler.world_mut(),
        &mut concrete_types,
        source.to_string(),
        "user.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|_| panic!("frontend result"));
    let checked = CheckedModule::for_mode(&mut concrete_types, Ok(frontend), &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    let graph = compiler
        .world_mut()
        .prepare_execution_graph(&mut concrete_types, checked, &tel, CompileMode::Normal)
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
    let source = r#"
defmodule User do
  import Utf8, only: [valid?: 1]
  fn run(bytes), do: valid?(bytes)
end
"#;

    let frontend = compile_source_with_compiler_types(
        compiler.world_mut(),
        &mut concrete_types,
        source.to_string(),
        "user.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|_| panic!("frontend result"));
    let checked = CheckedModule::for_mode(&mut concrete_types, Ok(frontend), &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    let graph = compiler
        .world_mut()
        .prepare_execution_graph(&mut concrete_types, checked, &tel, CompileMode::Normal)
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
fn execution_graph_seeds_runtime_modules_from_nonlocal_fn_refs() {
    let mut concrete_types = crate::types::new();
    let mut compiler = compiler();
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());
    let source = r#"
fn main(), do: &Kernel.dbg/1
"#;

    let frontend = compile_source_with_compiler_types(
        compiler.world_mut(),
        &mut concrete_types,
        source.to_string(),
        "fn_ref_seed.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|_| panic!("frontend result"));
    let checked = CheckedModule::for_mode(&mut concrete_types, Ok(frontend), &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    let graph = compiler
        .world_mut()
        .prepare_execution_graph(&mut concrete_types, checked, &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("execution graph"));

    let modules = graph
        .units
        .iter()
        .filter_map(|unit| unit.module.as_ref().map(ModuleName::dotted))
        .collect::<Vec<_>>();
    assert!(modules.contains(&"Kernel".to_string()));
    assert!(
        capture
            .find(&["fz", "compiler", "runtime_module_reachable"])
            .into_iter()
            .any(|ev| matches!(ev.metadata.get("module_key"), Some(Value::Str(m)) if m == "Kernel")),
        "qualified fn refs should seed runtime reachability from root external call edges"
    );

    compiler
        .validate_invariants()
        .expect("fn-ref runtime reachability must preserve compiler invariants");
}

#[test]
fn protocol_impl_reduce_callback_plans_to_fixed_point() {
    let mut concrete_types = crate::types::new();
    let mut compiler = compiler();
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "planner", "planned"], capture.handler());
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

    let frontend = compile_source_with_compiler_types(
        compiler.world_mut(),
        &mut concrete_types,
        source.to_string(),
        "protocol_reduce.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|_| panic!("frontend result"));
    let checked = CheckedModule::for_mode(&mut concrete_types, Ok(frontend), &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    compiler
        .world_mut()
        .prepare_execution_graph(&mut concrete_types, checked, &tel, CompileMode::Normal)
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

#[test]
fn linked_runtime_graph_keeps_cont_dispatches_for_enum_take_drop_split() {
    use crate::fz_ir::{CallsiteId, EmitSlot, Term};

    let mut t = crate::types::new();
    let mut compiler = compiler();
    let tel = NullTelemetry;
    let source = include_str!("../../fixtures/enum_take_drop_split/input.fz");

    let frontend = compile_source_with_compiler_types(
        compiler.world_mut(),
        &mut t,
        source.to_string(),
        "enum_take_drop_split_input.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|_| panic!("frontend result"));
    let checked = CheckedModule::for_mode(&mut t, Ok(frontend), &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    let graph = compiler
        .world_mut()
        .prepare_execution_graph(&mut t, checked, &tel, CompileMode::Normal)
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
    let source = include_str!("../../fixtures/spawn_with_captures/input.fz");

    let frontend = compile_source_with_compiler_types(
        compiler.world_mut(),
        &mut t,
        source.to_string(),
        "spawn_with_captures_input.fz".to_string(),
        &tel,
    )
    .unwrap_or_else(|_| panic!("frontend result"));
    let checked = CheckedModule::for_mode(&mut t, Ok(frontend), &tel, CompileMode::Normal)
        .unwrap_or_else(|_| panic!("checked module"));
    let graph = compiler
        .world_mut()
        .prepare_execution_graph(&mut t, checked, &tel, CompileMode::Normal)
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
