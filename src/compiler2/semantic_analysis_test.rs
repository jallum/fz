use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::time::Duration;

use super::body::{DeliveredValueSource, delivered_value_joins};
use super::{
    CallSiteKey, CallSiteSummary, CallableFlowFact, CodeSubmission, Compiler2, DriveOutcome, ExecutableKey,
    ExecutableNeed, ExecutableRuntimeDemand, FactKey, FunctionId, FunctionRef, Job, RootId, RootSubmission,
    RuntimeDemand, SelectedCallee, World,
};
use crate::telemetry::Value;
use crate::telemetry::handler::{Event, EventKind, Handler};

type FunctionDefs = Rc<RefCell<Vec<FunctionDef>>>;
type CallsiteDefs = Rc<RefCell<Vec<CallsiteDef>>>;
type RuntimeDemandDefs = Rc<RefCell<Vec<RuntimeDemandRecord>>>;

#[derive(Debug, Clone)]
struct FunctionDef {
    id: FunctionId,
    name: String,
    arity: u64,
}

#[derive(Debug, Clone)]
struct CallsiteDef {
    key: CallSiteKey,
    summary: CallSiteSummary,
}

#[derive(Debug, Clone)]
struct RuntimeDemandRecord {
    root_id: RootId,
    omitted_inputs: u64,
    direct_callable_flows: u64,
    first_class_callable_flows: u64,
    opaque_callable_demands: u64,
    runtime_demands: HashMap<ExecutableKey, ExecutableRuntimeDemand>,
}

struct FunctionCapture {
    defs: FunctionDefs,
}

struct CallsiteCapture {
    defs: CallsiteDefs,
}

struct RuntimeDemandCapture {
    defs: RuntimeDemandDefs,
}

impl FunctionCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(FunctionCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn id(&self, name: &str, arity: u64) -> FunctionId {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|def| def.name == name && def.arity == arity)
            .map(|def| def.id)
            .unwrap_or_else(|| panic!("function definition for {name}/{arity}"))
    }
}

impl CallsiteCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(CallsiteCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn all(&self) -> Vec<CallsiteDef> {
        self.defs.borrow().clone()
    }
}

impl RuntimeDemandCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(RuntimeDemandCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn last(&self, root_id: RootId) -> RuntimeDemandRecord {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|record| record.root_id == root_id)
            .cloned()
            .unwrap_or_else(|| panic!("runtime_demand.defined for root {}", root_id.as_u32()))
    }
}

struct FunctionCaptureHandler {
    defs: FunctionDefs,
}

struct CallsiteCaptureHandler {
    defs: CallsiteDefs,
}

struct RuntimeDemandCaptureHandler {
    defs: RuntimeDemandDefs,
}

impl Handler for FunctionCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.kind != EventKind::Event
            || !matches!(
                event.name,
                ["fz", "compiler2", "function", "defined"] | ["fz", "compiler2", "function", "source", "noted"]
            )
        {
            return;
        }
        let Some(id) = event
            .metadata
            .get("function_id")
            .and_then(|value| value.downcast_ref::<FunctionId>())
            .copied()
        else {
            return;
        };
        let Some(function_ref) = event
            .metadata
            .get("function_ref")
            .and_then(|value| value.downcast_ref::<FunctionRef>())
        else {
            return;
        };
        let Some(Value::U64(arity)) = event.measurements.get("arity") else {
            return;
        };
        self.defs.borrow_mut().push(FunctionDef {
            id,
            name: function_ref.name.clone(),
            arity: *arity,
        });
    }
}

impl Handler for CallsiteCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "callsite", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(key) = event
            .metadata
            .get("callsite")
            .and_then(|value| value.downcast_ref::<CallSiteKey>())
        else {
            return;
        };
        let Some(summary) = event
            .metadata
            .get("summary")
            .and_then(|value| value.downcast_ref::<CallSiteSummary>())
        else {
            return;
        };
        self.defs.borrow_mut().push(CallsiteDef {
            key: key.clone(),
            summary: summary.clone(),
        });
    }
}

impl Handler for RuntimeDemandCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "runtime_demand", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(root_id) = event
            .metadata
            .get("root_id")
            .and_then(|value| value.downcast_ref::<RootId>())
            .copied()
        else {
            return;
        };
        let Some(Value::U64(omitted_inputs)) = event.measurements.get("omitted_inputs") else {
            return;
        };
        let Some(Value::U64(direct_callable_flows)) = event.measurements.get("direct_callable_flows") else {
            return;
        };
        let Some(Value::U64(first_class_callable_flows)) = event.measurements.get("first_class_callable_flows") else {
            return;
        };
        let Some(Value::U64(opaque_callable_demands)) = event.measurements.get("opaque_callable_demands") else {
            return;
        };
        let Some(runtime_demands) = event
            .metadata
            .get("runtime_demands")
            .and_then(|value| value.downcast_ref::<HashMap<ExecutableKey, ExecutableRuntimeDemand>>())
        else {
            return;
        };
        self.defs.borrow_mut().push(RuntimeDemandRecord {
            root_id,
            omitted_inputs: *omitted_inputs,
            direct_callable_flows: *direct_callable_flows,
            first_class_callable_flows: *first_class_callable_flows,
            opaque_callable_demands: *opaque_callable_demands,
            runtime_demands: runtime_demands.clone(),
        });
    }
}

fn assert_resolved(outcome: DriveOutcome<Job, FactKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

fn drive_until_semantic_closure(world: &mut World<'_>, root: RootId, message: &str) {
    world.demand(Job::SealSemanticClosure(root));
    let mut ran = 0;
    while !world.fact_is_settled(&FactKey::SemanticClosed(root)) && ran < 10_000 {
        let Some(job) = world.work_graph.pop() else {
            break;
        };
        let effects = super::jobs::run(world, &job)
            .unwrap_or_else(|_| panic!("{message}; prerequisite job failed before semantic closure: {job:?}"));
        world.complete_job(job, effects);
        ran += 1;
    }
    assert!(
        world.fact_is_settled(&FactKey::SemanticClosed(root)),
        "{message}; semantic closure was not settled after {ran} prerequisite jobs; pending={}; unresolved={:?}",
        world.work_graph.pending_jobs(),
        world.work_graph.unresolved()
    );
}

fn summary_has_function(summary: &CallSiteSummary, function: FunctionId) -> bool {
    summary
        .targets
        .iter()
        .any(|target| target.callee == SelectedCallee::Function(function))
}

fn runtime_demand_for_function(
    record: &RuntimeDemandRecord,
    function: FunctionId,
) -> (&ExecutableKey, &ExecutableRuntimeDemand) {
    record
        .runtime_demands
        .iter()
        .find(|(key, _)| key.activation.function == function)
        .unwrap_or_else(|| panic!("runtime demand for function {}", function.as_u32()))
}

fn has_callable_flow(demand: &ExecutableRuntimeDemand, predicate: impl Fn(&CallableFlowFact) -> bool) -> bool {
    demand.callable_flows.values().any(predicate)
}

#[test]
fn compiler2_semantic_analysis_does_not_reach_continuation_after_never_return() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let callsites = CallsiteCapture::new();
    tel.attach(&["fz", "compiler2", "callsite", "defined"], callsites.handler());

    let mut world = World::new(&tel);
    world.submit_code(
        Some("never_continuation.fz".to_string()),
        r#"
fn main() do
  panic("stop")
  |> dbg()
end
"#
        .to_string(),
    );
    let root_id = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    drive_until_semantic_closure(
        &mut world,
        root_id,
        "a never-returning call should not keep its pipe continuation semantically live",
    );

    let main = functions.id("main", 0);
    let panic = functions.id("panic", 1);
    let dbg = functions.id("dbg", 1);
    let main_calls = callsites
        .all()
        .into_iter()
        .filter(|record| record.key.activation.root == root_id && record.key.activation.function == main)
        .collect::<Vec<_>>();

    assert!(
        main_calls
            .iter()
            .any(|record| summary_has_function(&record.summary, panic)),
        "main/0 should still publish the never-returning panic/1 edge",
    );
    assert!(
        main_calls
            .iter()
            .all(|record| !summary_has_function(&record.summary, dbg)),
        "main/0 should not publish a dbg/1 edge for a continuation that cannot receive a value",
    );
}

#[test]
fn compiler2_runtime_demand_leaves_an_unused_callable_input_omitted() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let runtime_demands = RuntimeDemandCapture::new();
    tel.attach(
        &["fz", "compiler2", "runtime_demand", "defined"],
        runtime_demands.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
    compiler.set_drive_timeout(Duration::from_millis(100));
    compiler.submit_code(CodeSubmission {
        name: Some("unused_callable_input.fz".to_string()),
        text: r#"
fn ignore(f), do: 1
fn main() do
  id = fn x -> x end
  ignore(id)
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "unused callable input program should settle");

    let ignore = functions.id("ignore", 1);
    let record = runtime_demands.last(root_id);
    let (_, demand) = runtime_demand_for_function(&record, ignore);
    assert_eq!(
        demand.input_demands,
        vec![RuntimeDemand::Ignore],
        "semantic inputs stay present, but an unused callable input should not claim runtime demand",
    );
    assert!(
        record.omitted_inputs >= 1,
        "runtime-demand telemetry should count omitted inputs",
    );
}

#[test]
fn compiler2_runtime_demand_records_the_exact_surface_for_a_direct_lambda_call() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let runtime_demands = RuntimeDemandCapture::new();
    tel.attach(
        &["fz", "compiler2", "runtime_demand", "defined"],
        runtime_demands.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
    compiler.set_drive_timeout(Duration::from_millis(100));
    compiler.submit_code(CodeSubmission {
        name: Some("direct_lambda_call.fz".to_string()),
        text: r#"
fn main() do
  add1 = fn x -> x + 1 end
  add1.(1)
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "direct lambda call should settle");

    let record = runtime_demands.last(root_id);
    assert!(
        record.direct_callable_flows >= 1,
        "runtime-demand telemetry should report direct callable flow",
    );
    assert!(
        record.runtime_demands.values().any(|demand| {
            has_callable_flow(demand, |flow| {
                !flow.escape && !flow.opaque && flow.direct_surfaces.len() == 1
            })
        }),
        "a directly-invoked lambda should keep one exact resolved surface",
    );
}

#[test]
#[ignore = "fz-hwn.19.2.4.8: first-class callable publication is conflated with direct surfaces/resolutions"]
fn compiler2_runtime_demand_marks_an_escaped_callable_first_class() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let runtime_demands = RuntimeDemandCapture::new();
    tel.attach(
        &["fz", "compiler2", "runtime_demand", "defined"],
        runtime_demands.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
    compiler.set_drive_timeout(Duration::from_millis(100));
    compiler.submit_code(CodeSubmission {
        name: Some("escaped_callable.fz".to_string()),
        text: r#"
fn make() do
  fn x -> x + 1 end
end
fn main(), do: make()
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "escaped callable program should settle");

    let make = functions.id("make", 0);
    let record = runtime_demands.last(root_id);
    let (_, demand) = runtime_demand_for_function(&record, make);
    assert!(
        has_callable_flow(demand, |flow| flow.escape && !flow.opaque),
        "a callable that escapes should be first-class at runtime: {demand:?}",
    );
    assert!(
        demand.callable_flows.values().any(|flow| {
            flow.escape
                && !flow.opaque
                && flow.direct_surfaces.is_empty()
                && flow.first_class_surfaces.len() == 1
                && flow.resolutions.len() == 1
        }),
        "an escaped callable with no known call surface should publish a first-class surface and canonical resolution upstream: {demand:?}",
    );
    assert!(
        record.first_class_callable_flows >= 1,
        "runtime-demand telemetry should count first-class callable flows",
    );
}

#[test]
fn compiler2_runtime_demand_keeps_a_returned_direct_callable_out_of_first_class_inventory() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let runtime_demands = RuntimeDemandCapture::new();
    tel.attach(
        &["fz", "compiler2", "runtime_demand", "defined"],
        runtime_demands.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
    compiler.set_drive_timeout(Duration::from_millis(100));
    compiler.submit_code(CodeSubmission {
        name: Some("returned_direct_callable_transport.fz".to_string()),
        text: r#"
fn apply(fun), do: fun.(41)

fn make_adder(a), do: fn x -> x + a end

fn main(), do: apply(make_adder(1))
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "a returned callable that is only ever called directly should stay out of first-class runtime inventory",
    );

    let make_adder = functions.id("make_adder", 1);
    let record = runtime_demands.last(root_id);
    let (_, demand) = runtime_demand_for_function(&record, make_adder);
    assert!(
        has_callable_flow(demand, |flow| {
            !flow.escape && !flow.opaque && !flow.direct_surfaces.is_empty()
        }),
        "make_adder/1 should still publish direct callable flow for transport",
    );
    assert!(
        !has_callable_flow(demand, |flow| flow.escape || flow.opaque),
        "direct-only returned callable transport should not require a first-class callable object",
    );
}

#[test]
fn compiler2_runtime_demand_makes_opaque_callable_use_explicit() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let runtime_demands = RuntimeDemandCapture::new();
    tel.attach(
        &["fz", "compiler2", "runtime_demand", "defined"],
        runtime_demands.handler(),
    );

    let mut world = World::new(&tel);
    world.submit_code(
        Some("opaque_callable_use.fz".to_string()),
        "fn main(f), do: f.(1)\n".to_string(),
    );
    let root_id = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    drive_until_semantic_closure(&mut world, root_id, "opaque callable use should settle");

    let main = functions.id("main", 1);
    let record = runtime_demands.last(root_id);
    let (_, demand) = runtime_demand_for_function(&record, main);
    assert!(
        matches!(
            demand.input_demands.as_slice(),
            [RuntimeDemand::Callable(callable)] if callable.opaque
                && callable.resolved.len() == 1
                && callable.resolved.iter().any(|surface| surface.inputs.len() == 1)
        ),
        "an unresolved closure call should keep opaque callable demand and its observed surface explicit: {demand:?}",
    );
    assert!(
        record.opaque_callable_demands >= 1,
        "runtime-demand telemetry should count opaque callable demands",
    );
}

#[test]
#[ignore = "fz-hwn.19.2.4.8: first-class callable publication is conflated with direct surfaces/resolutions"]
fn compiler2_runtime_demand_marks_callable_arguments_to_opaque_calls_first_class() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let runtime_demands = RuntimeDemandCapture::new();
    tel.attach(
        &["fz", "compiler2", "runtime_demand", "defined"],
        runtime_demands.handler(),
    );

    let mut world = World::new(&tel);
    world.submit_code(
        Some("opaque_call_callable_argument.fz".to_string()),
        r#"
fn main(f) do
  g = fn (x) -> x + 1 end
  f.(g)
end
"#
        .to_string(),
    );
    let root_id = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    drive_until_semantic_closure(
        &mut world,
        root_id,
        "callable argument passed to an opaque closure call should settle",
    );

    let main = functions.id("main", 1);
    let record = runtime_demands.last(root_id);
    let (_, demand) = runtime_demand_for_function(&record, main);
    assert!(
        demand.call_arg_demands.values().any(|demands| {
            matches!(
                demands.as_slice(),
                [RuntimeDemand::Callable(callable)]
                    if callable.escape && !callable.opaque && callable.resolved.is_empty()
            )
        }),
        "opaque closure-call argument demand should preserve callable escape before transport runs: {demand:?}",
    );
    assert!(
        has_callable_flow(demand, |flow| {
            flow.escape
                && !flow.opaque
                && flow.direct_surfaces.is_empty()
                && flow.first_class_surfaces.len() == 1
                && flow.resolutions.len() == 1
        }),
        "the local lambda passed through the opaque call should be a first-class runtime obligation: {demand:?}",
    );
    assert!(
        demand.callable_flows.values().any(|flow| {
            flow.escape
                && !flow.opaque
                && flow.direct_surfaces.is_empty()
                && flow.first_class_surfaces.len() == 1
                && flow.resolutions.len() == 1
        }),
        "the opaque-call argument should publish first-class callable-flow evidence before transport: {demand:?}",
    );
}

#[test]
fn compiler2_runtime_demand_marks_joined_function_refs_first_class_before_reduce_boundary() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let runtime_demands = RuntimeDemandCapture::new();
    tel.attach(
        &["fz", "compiler2", "runtime_demand", "defined"],
        runtime_demands.handler(),
    );

    let mut world = World::new(&tel);
    world.submit_code(
        Some("opaque_fn_value_join.fz".to_string()),
        include_str!("../../fixtures2/behavior/opaque_fn_value_join.fz").to_string(),
    );
    let root_id = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_until_semantic_closure(
        &mut world,
        root_id,
        "joined zero-capture function refs should settle before transport",
    );

    let main = functions.id("main", 0);
    let add_a = functions.id("add_a", 2);
    let add_b = functions.id("add_b", 2);
    let record = runtime_demands.last(root_id);
    let (main_executable, demand) = runtime_demand_for_function(&record, main);
    for function in [add_a, add_b] {
        assert!(
            demand.callable_flows.values().any(|flow| {
                flow.function == function
                    && flow.direct_surfaces.iter().any(|surface| surface.inputs.len() == 2)
                    && flow
                        .first_class_surfaces
                        .iter()
                        .any(|surface| surface.inputs.len() == 2)
                    && flow.escape
            }),
            "a branch function ref that joins before Enum.reduce must remain directly callable and also publish a first-class runtime obligation: {demand:?}",
        );
    }

    let body = world.lowered_body(main_executable.activation.function);
    let joined_value = delivered_value_joins(&body)
        .values()
        .find_map(|join| {
            let producer_functions = join
                .sources
                .iter()
                .filter_map(|source| match source {
                    DeliveredValueSource::LocalValue(value) => {
                        demand.callable_flows.get(value).map(|flow| flow.function)
                    }
                    DeliveredValueSource::CallsiteReturn(_) => None,
                })
                .collect::<Vec<_>>();
            (producer_functions.contains(&add_a) && producer_functions.contains(&add_b)).then_some(join.value)
        })
        .expect("main should have a delivered join fed by add_a/2 and add_b/2 function refs");
    let RuntimeDemand::Callable(joined_callable) = demand
        .value_demands
        .get(&joined_value)
        .unwrap_or_else(|| panic!("joined callable value {joined_value:?} should have runtime demand"))
    else {
        panic!("joined value {joined_value:?} should be callable-demanded: {demand:?}");
    };
    assert!(
        joined_callable.escape && joined_callable.resolved.iter().any(|surface| surface.inputs.len() == 2),
        "the delivered joined callable value itself must publish a first-class discriminator before downstream lowering: {joined_callable:?}",
    );
}

#[test]
fn compiler2_semantic_callsite_joins_duplicate_function_targets_before_artifact() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let callsites = CallsiteCapture::new();
    tel.attach(&["fz", "compiler2", "callsite", "defined"], callsites.handler());

    let mut world = World::new(&tel);
    world.submit_code(
        Some("opaque_fn_value_join.fz".to_string()),
        include_str!("../../fixtures2/behavior/opaque_fn_value_join.fz").to_string(),
    );
    let root_id = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_until_semantic_closure(
        &mut world,
        root_id,
        "joined reducer function refs should settle to one semantic call target before artifact",
    );

    let main = functions.id("main", 0);
    let duplicate = callsites
        .all()
        .into_iter()
        .filter(|record| record.key.activation.function == main)
        .find(|record| {
            let callees = record
                .summary
                .targets
                .iter()
                .map(|target| target.callee.clone())
                .collect::<HashSet<_>>();
            callees.len() < record.summary.targets.len()
        });
    assert!(
        duplicate.is_none(),
        "semantic callsite summaries must join repeated observations of the same callee instead of leaving artifact to dispatch by activation-key differences: {duplicate:#?}",
    );
}

#[test]
fn compiler2_runtime_demand_preserves_tuple_return_shape_for_escaped_callable_boundaries() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("runtime_demand_boundary_tuple_return.fz".to_string()),
        r#"
fn make_pairer(), do: fn (x) -> {{1, 2}, 3} end
fn main(), do: make_pairer()
"#
        .to_string(),
    );
    let root_id = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_until_semantic_closure(
        &mut world,
        root_id,
        "escaped callable tuple-return fixture should settle before transport",
    );

    let closure = world.semantic_closure(root_id);
    let tuple_return_demands = closure
        .runtime_demands
        .iter()
        .filter_map(|(executable, demand)| {
            let function_ref = world.function_ref(executable.activation.function);
            (function_ref.name.starts_with("#lambda:") && function_ref.arity == 1).then_some(&demand.return_demand)
        })
        .collect::<Vec<_>>();
    assert!(
        tuple_return_demands.iter().any(|demand| {
            matches!(
                demand,
                RuntimeDemand::TupleFields(fields)
                    if fields.len() == 2
                        && matches!(&fields[0], RuntimeDemand::TupleFields(inner) if inner.len() == 2)
                        && matches!(&fields[1], RuntimeDemand::Value)
            )
        }),
        "escaped callable boundary return demand should preserve recursive tuple fields upstream: {tuple_return_demands:?}"
    );
}

#[test]
fn compiler2_runtime_demand_records_recursive_tuple_resume_value_demand() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("runtime_demand_recursive_tuple_resume.fz".to_string()),
        r#"
fn pair_down(0), do: {0, 1}
fn pair_down(n) do
  {left, right} = pair_down(n - 1)
  {left, right}
end

fn main() do
  {left, right} = pair_down(2)
  left + right
end
"#
        .to_string(),
    );
    let root_id = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_until_semantic_closure(
        &mut world,
        root_id,
        "recursive tuple resume fixture should settle before transport",
    );

    let closure = world.semantic_closure(root_id);
    let resume_demands = closure
        .runtime_demands
        .iter()
        .filter_map(|(executable, demand)| {
            let function_ref = world.function_ref(executable.activation.function);
            (function_ref.name == "pair_down" && function_ref.arity == 1).then_some(&demand.value_demands)
        })
        .flat_map(|demands| demands.values())
        .collect::<Vec<_>>();
    assert!(
        resume_demands
            .iter()
            .any(|demand| matches!(demand, RuntimeDemand::TupleFields(fields) if fields.len() == 2)),
        "recursive call resume value should carry tuple-field demand upstream: {resume_demands:?}"
    );
}

#[test]
#[ignore = "fz-hwn.19.2.4.9: suspend continuation callable frontier is not closed before transport/ABI"]
fn compiler2_runtime_demand_preserves_reducer_surface_when_suspend_continuation_escapes() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let runtime_demands = RuntimeDemandCapture::new();
    tel.attach(
        &["fz", "compiler2", "runtime_demand", "defined"],
        runtime_demands.handler(),
    );

    let mut world = World::new(&tel);
    world.submit_code(
        Some("runtime_demand_enumerable_reduce_suspend_continuation.fz".to_string()),
        r#"
fn make() do
  fn () ->
    Enumerable.reduce([1, 2, 3], {:suspend, 0}, fn (x, acc) -> {:cont, acc + x} end)
  end
end

fn main(), do: make()
"#
        .to_string(),
    );
    let root_id = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_until_semantic_closure(
        &mut world,
        root_id,
        "suspend-shaped Enumerable.reduce fixture should settle before transport",
    );

    let closure = world.semantic_closure(root_id);
    let reducer_executables = closure
        .executables
        .iter()
        .filter(|executable| {
            let function_ref = world.function_ref(executable.activation.function);
            function_ref.name.starts_with("#lambda:")
                && function_ref.arity == 2
                && executable.activation.input.len() == 2
        })
        .collect::<Vec<_>>();
    assert!(
        !reducer_executables.is_empty(),
        "semantic closure should include the user reducer lambda executable before transport"
    );
    assert!(
        reducer_executables
            .iter()
            .all(|executable| executable.activation.input[0] == executable.activation.input[1]),
        "semantic closure should hold canonical reducer activations, not type-template inputs: {reducer_executables:?}"
    );

    let record = runtime_demands.last(root_id);
    assert!(
        record.runtime_demands.values().any(|demand| {
            has_callable_flow(demand, |flow| {
                !flow.opaque && flow.direct_surfaces.iter().any(|surface| surface.inputs.len() == 2)
            })
        }),
        "the reducer direct-call surface should be proven upstream before transport: {:?}",
        record.runtime_demands
    );
    assert!(
        record.runtime_demands.values().any(|demand| {
            demand.callable_flows.values().any(|flow| {
                flow.direct_surfaces.iter().any(|surface| surface.inputs.len() == 2)
                    && !flow.resolutions.is_empty()
                    && flow.resolutions.iter().all(|resolution| {
                        resolution.activation.input.len() == 2
                            && resolution.activation.input[0] == resolution.activation.input[1]
                    })
            })
        }),
        "the reducer callable-flow fact should carry direct surfaces and canonical executable resolutions upstream: {:?}",
        record.runtime_demands
    );
}

#[test]
fn compiler2_runtime_demand_keeps_dbg_inputs_live_when_the_return_is_ignored() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let runtime_demands = RuntimeDemandCapture::new();
    tel.attach(
        &["fz", "compiler2", "runtime_demand", "defined"],
        runtime_demands.handler(),
    );

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("heap_stats_dbg_resume.fz".to_string()),
        text: r#"
fn main() do
  stats = Process.heap_alloc_stats()
  dbg(stats)
  dbg(stats[:list_cons_allocs])
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let outcome = compiler.drive();
    assert!(
        matches!(outcome, DriveOutcome::Resolved)
            || matches!(outcome, DriveOutcome::Fatal { ref job } if *job == Job::LowerNativeProgram(root_id)),
        "heap_stats dbg-resume runtime-demand probe should either resolve or stop at the known downstream native blocker: {outcome:?}",
    );

    let dbg = functions.id("dbg", 1);
    let record = runtime_demands.last(root_id);
    let (_, demand) = runtime_demand_for_function(&record, dbg);
    assert_eq!(
        demand.input_demands,
        vec![RuntimeDemand::Value],
        "Kernel.dbg/1 must still demand its input as a runtime value even when callers ignore the returned value",
    );

    let main = functions.id("main", 0);
    let (_, main_demand) = runtime_demand_for_function(&record, main);
    assert!(
        main_demand
            .entry_capture_demands
            .values()
            .any(|demands| demands.as_slice() == [RuntimeDemand::Value]),
        "the continuation after dbg(stats) must keep one captured runtime value live for the later field access: {main_demand:?}",
    );
}
