use crate::fz_ir::{FnId, Module};
use crate::telemetry::{ConfiguredTelemetry, Handler};
use crate::types::ConcreteTypes;
use std::cell::RefCell;
use std::panic::AssertUnwindSafe;
use std::rc::Rc;

/// Captures the exact lowered IR module emitted by the production frontend
/// before planning begins.
struct LoweredCapture(Rc<RefCell<Option<Module>>>);

impl Handler for LoweredCapture {
    fn handle(&self, ev: &crate::telemetry::Event<'_, '_, '_>) {
        if let ["fz", "frontend", "lowered"] = ev.name {
            if let Some(module) = ev
                .metadata
                .get("module")
                .and_then(|value| value.downcast_ref::<Module>())
            {
                *self.0.borrow_mut() = Some(module.clone());
            }
        }
    }
}

/// Run the production frontend and snapshot the lowered IR module from
/// telemetry. This is the exact frontend output the planner consumes.
pub(crate) fn lower_frontend_module(src: &str) -> Module {
    let captured = Rc::new(RefCell::new(None));
    let tel = ConfiguredTelemetry::new();
    tel.attach(&["fz"], Box::new(LoweredCapture(captured.clone())));

    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let _ = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let mut t = ConcreteTypes;
        let providers = crate::modules::pipeline::ProviderInputs::new(
            crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
            Vec::new(),
        );
        let _ = crate::modules::pipeline::compile_source_with_providers(
            &mut t,
            src.to_string(),
            "test_fixture.fz".to_string(),
            &providers,
            &tel,
        );
    }));
    std::panic::set_hook(prev_hook);

    captured
        .borrow_mut()
        .take()
        .expect("frontend emitted no lowered module")
}

/// Compile a program through the production pipeline to the linked runtime IR:
/// protocol impls, runtime helpers, and execution-graph rewrites are local.
pub(crate) fn linked_runtime_graph_with_telemetry(
    t: &mut ConcreteTypes,
    src: &str,
    tel: &dyn crate::telemetry::Telemetry,
) -> crate::modules::pipeline::PreparedExecutionGraph {
    use crate::modules::pipeline::{
        CompileMode, ProviderInputs, checked_module_for_mode, compile_source_with_providers,
        prepare_execution_graph,
    };

    let providers = ProviderInputs::new(
        crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
        Vec::new(),
    );
    let frontend = compile_source_with_providers(
        t,
        src.to_string(),
        "test_fixture.fz".to_string(),
        &providers,
        tel,
    )
    .unwrap_or_else(|err| panic!("frontend: {err}"));
    let checked = checked_module_for_mode(t, frontend, tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("checked: {err}"));
    prepare_execution_graph(t, checked, &providers, tel, CompileMode::Normal)
        .unwrap_or_else(|err| panic!("execution graph: {err}"))
}

pub(crate) fn linked_runtime_graph(src: &str) -> crate::modules::pipeline::PreparedExecutionGraph {
    let mut t = ConcreteTypes;
    linked_runtime_graph_with_telemetry(&mut t, src, &crate::telemetry::NullTelemetry)
}

/// Compile a program through the production pipeline to the linked runtime IR:
/// protocol impls, runtime helpers, and execution-graph rewrites are local.
pub(crate) fn linked_runtime_module(src: &str) -> Module {
    linked_runtime_graph(src).module
}

/// Fixture tests enter through a top-level `main`.
pub(crate) fn entry_main_fn_id(module: &Module) -> FnId {
    module
        .fns
        .iter()
        .find(|f| f.name == "main")
        .expect("main fn")
        .id
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ActivationProjectionSignal {
    pub role: String,
    pub body_name: String,
    pub spec_role: String,
    pub projection_kind: String,
    pub projected_return_state: String,
    pub covered_activation_count: u64,
    pub covered_known_count: u64,
    pub exact_coverage: bool,
    pub projection_gap: bool,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MaterializedBodySignal {
    pub spec_id: u32,
    pub role: String,
    pub fn_name: String,
    pub spec_key: String,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReachableMaterializedBodySignal {
    pub spec_id: u32,
    pub fn_name: String,
    pub spec_key: String,
}

#[cfg(test)]
fn activation_projection_signals(
    cap: &crate::telemetry::Capture,
) -> Vec<ActivationProjectionSignal> {
    use crate::telemetry::Value;

    cap.find(&["fz", "planner", "activation_projection"])
        .into_iter()
        .filter_map(|event| {
            let role = match event.metadata.get("role") {
                Some(Value::Str(role)) if role == "authoritative" => role.to_string(),
                _ => return None,
            };
            let body_name = match event.metadata.get("body_name") {
                Some(Value::Str(name)) => name.to_string(),
                other => panic!("body_name missing or wrong type: {other:?}"),
            };
            let spec_role = match event.metadata.get("spec_role") {
                Some(Value::Str(role)) => role.to_string(),
                other => panic!("spec_role missing or wrong type: {other:?}"),
            };
            let projection_kind = match event.metadata.get("projection_kind") {
                Some(Value::Str(kind)) => kind.to_string(),
                other => panic!("projection_kind missing or wrong type: {other:?}"),
            };
            let projected_return_state = match event.metadata.get("projected_return_state") {
                Some(Value::Str(state)) => state.to_string(),
                other => panic!("projected_return_state missing or wrong type: {other:?}"),
            };
            let measurement = |name| match event.measurements.get(name) {
                Some(Value::U64(n)) => *n,
                other => panic!("{name} missing or wrong type: {other:?}"),
            };
            Some(ActivationProjectionSignal {
                role,
                body_name,
                spec_role,
                projection_kind,
                projected_return_state,
                covered_activation_count: measurement("covered_activation_count"),
                covered_known_count: measurement("covered_known_count"),
                exact_coverage: measurement("exact_coverage") == 1,
                projection_gap: measurement("projection_gap") == 1,
            })
        })
        .collect()
}

#[cfg(test)]
pub(crate) fn runtime_graph_planner_activation_projection_signals(
    src: &str,
) -> Vec<ActivationProjectionSignal> {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let cap = crate::telemetry::Capture::new();
    tel.attach(&[], cap.handler());

    let mut t = ConcreteTypes;
    let graph = linked_runtime_graph_with_telemetry(&mut t, src, &tel);
    cap.clear();
    let _ = crate::ir_planner::plan_module(&mut t, &graph.module, &tel);
    activation_projection_signals(&cap)
}

#[cfg(test)]
pub(crate) fn runtime_graph_codegen_materialized_body_signals(
    src: &str,
) -> Vec<MaterializedBodySignal> {
    use crate::telemetry::Value;

    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let cap = crate::telemetry::Capture::new();
    tel.attach(&[], cap.handler());

    let mut t = ConcreteTypes;
    let graph = linked_runtime_graph_with_telemetry(&mut t, src, &tel);
    cap.clear();
    crate::ir_codegen::compile_planned(&mut t, &graph.module, &graph.module_plan, &tel)
        .expect("compile planned");

    cap.find(&["fz", "planner", "body_materialized"])
        .into_iter()
        .filter_map(|event| {
            let role = match event.metadata.get("role") {
                Some(Value::Str(role)) if role == "authoritative" => role.to_string(),
                _ => return None,
            };
            let spec_id = match event.measurements.get("spec_id") {
                Some(Value::U64(id)) => *id as u32,
                other => panic!("spec_id missing or wrong type: {other:?}"),
            };
            let fn_name = match event.metadata.get("fn_name") {
                Some(Value::Str(name)) => name.to_string(),
                other => panic!("fn_name missing or wrong type: {other:?}"),
            };
            let spec_key = match event.metadata.get("spec_key") {
                Some(Value::Str(key)) => key.to_string(),
                other => panic!("spec_key missing or wrong type: {other:?}"),
            };
            Some(MaterializedBodySignal {
                spec_id,
                role,
                fn_name,
                spec_key,
            })
        })
        .collect()
}

#[cfg(test)]
pub(crate) fn runtime_graph_reachable_materialized_body_signals(
    src: &str,
) -> Vec<ReachableMaterializedBodySignal> {
    use crate::telemetry::Value;

    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let cap = crate::telemetry::Capture::new();
    tel.attach(&[], cap.handler());

    let mut t = ConcreteTypes;
    let graph = linked_runtime_graph_with_telemetry(&mut t, src, &tel);
    cap.clear();
    crate::ir_codegen::compile_planned(&mut t, &graph.module, &graph.module_plan, &tel)
        .expect("compile planned");

    let materialized = cap
        .last(&["fz", "planner", "materialized"])
        .expect("planner materialized event");
    let reachable_spec_ids = match materialized.metadata.get("reachable_specs") {
        Some(Value::StrSeq(specs)) => specs
            .iter()
            .map(|spec| spec.parse::<u32>().expect("reachable spec id"))
            .collect::<std::collections::HashSet<_>>(),
        other => panic!("reachable_specs missing or wrong type: {other:?}"),
    };

    cap.find(&["fz", "planner", "body_materialized"])
        .into_iter()
        .filter_map(|event| {
            let role = match event.metadata.get("role") {
                Some(Value::Str(role)) if role == "authoritative" => role,
                _ => return None,
            };
            let _ = role;
            let spec_id = match event.measurements.get("spec_id") {
                Some(Value::U64(id)) => *id as u32,
                other => panic!("spec_id missing or wrong type: {other:?}"),
            };
            let fn_name = match event.metadata.get("fn_name") {
                Some(Value::Str(name)) => name.to_string(),
                other => panic!("fn_name missing or wrong type: {other:?}"),
            };
            let spec_key = match event.metadata.get("spec_key") {
                Some(Value::Str(key)) => key.to_string(),
                other => panic!("spec_key missing or wrong type: {other:?}"),
            };
            Some(MaterializedBodySignal {
                spec_id,
                role: "authoritative".to_string(),
                fn_name,
                spec_key,
            })
        })
        .collect::<Vec<_>>()
        .into_iter()
        .filter(|signal| reachable_spec_ids.contains(&signal.spec_id))
        .map(|signal| ReachableMaterializedBodySignal {
            spec_id: signal.spec_id,
            fn_name: signal.fn_name,
            spec_key: signal.spec_key,
        })
        .collect()
}
