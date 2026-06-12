use super::*;
use crate::frontend::compile_source_with_types;
use crate::ir_interp::run_main;
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};
use fz_runtime::any_value::TRUE_ATOM_ID;

// DROP: runtime module import loaded without user-side storage; old-world planner
#[test]
fn execution_graph_loads_runtime_import_without_user_storage() {
    let mut concrete_types = crate::types::new();
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let source = r#"
defmodule User do
  import Utf8, only: [valid?: 1]
  fn run(bytes), do: valid?(bytes)
end
"#;

    let frontend = compile_source_with_types(&mut concrete_types, source.to_string(), "user.fz".to_string(), &tel);
    let checked = checked_module_for_mode(&mut concrete_types, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("checked module: {err}"));
    let graph = prepare_execution_graph(&mut concrete_types, checked, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("execution graph: {err}"));

    let modules = graph
        .units
        .iter()
        .filter_map(|unit| unit.name.as_ref().map(ModuleName::dotted))
        .collect::<Vec<_>>();
    assert!(modules.contains(&"User".to_string()));
    assert!(modules.contains(&"Utf8".to_string()));
    assert!(!modules.contains(&"Process".to_string()));
}

// PICKED: recursive protocol reduce callback converges without oscillation
#[test]
fn protocol_impl_reduce_callback_plans_to_fixed_point() {
    let mut concrete_types = crate::types::new();
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

    let frontend = compile_source_with_types(
        &mut concrete_types,
        source.to_string(),
        "protocol_reduce.fz".to_string(),
        &tel,
    );
    let checked = checked_module_for_mode(&mut concrete_types, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("checked module: {err}"));
    prepare_execution_graph(&mut concrete_types, checked, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("execution graph: {err}"));

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

// DROP: old-world planner Cont dispatch edges for Enum; SpecKey/planner internals
#[test]
fn linked_runtime_graph_keeps_cont_dispatches_for_enum_take_drop_split() {
    use crate::fz_ir::{CallsiteId, EmitSlot, Term};

    let mut t = crate::types::new();
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let source = include_str!("../../fixtures/enum_take_drop_split/input.fz");

    let frontend = compile_source_with_types(
        &mut t,
        source.to_string(),
        "enum_take_drop_split_input.fz".to_string(),
        &tel,
    );
    let checked = checked_module_for_mode(&mut t, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("checked module: {err}"));
    let graph = prepare_execution_graph(&mut t, checked, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("execution graph: {err}"));
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

// DROP: old-world planner Cont dispatch edges for spawn; SpecKey/planner internals
#[test]
fn linked_runtime_graph_keeps_cont_dispatches_for_spawn_with_captures() {
    use crate::fz_ir::{CallsiteId, EmitSlot, Term};

    let mut t = crate::types::new();
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let source = include_str!("../../fixtures/spawn_with_captures/input.fz");

    let frontend = compile_source_with_types(
        &mut t,
        source.to_string(),
        "spawn_with_captures_input.fz".to_string(),
        &tel,
    );
    let checked = checked_module_for_mode(&mut t, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("checked module: {err}"));
    let graph = prepare_execution_graph(&mut t, checked, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("execution graph: {err}"));
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

// PICKED: Utf8.valid? on a valid binary returns true through linked runtime
#[test]
fn runtime_library_units_link_and_run() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut t = crate::types::new();
    let source = r#"
defmodule User do
  import Utf8, only: [valid?: 1]
  fn run(), do: valid?(<<104, 105>>)
end

fn main(), do: User.run()
"#;

    let frontend = compile_source_with_types(&mut t, source.to_string(), "user.fz".to_string(), &tel);
    let checked = checked_module_for_mode(&mut t, frontend, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("checked module: {err}"));
    let graph = prepare_execution_graph(&mut t, checked, &tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("execution graph: {err}"));

    let module = if graph.units.len() > 1 {
        link_ir_units(&graph.units).expect("link ir units")
    } else {
        graph.units[0].code.clone()
    };
    let result = run_main(&tel, &module).expect("run linked image");
    assert_eq!(
        result, TRUE_ATOM_ID as i64,
        "Utf8.valid? on a valid binary should return true"
    );
}
