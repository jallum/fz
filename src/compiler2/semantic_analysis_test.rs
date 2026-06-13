use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Duration;

use super::{
    CallSiteKey, CallSiteSummary, CallableMaterialization, CodeSubmission, Compiler2, DriveOutcome, ExecutableKey,
    ExecutableNeed, ExecutableRuntimeDemand, FactKey, FunctionId, FunctionRef, Job, RootId, RootSubmission,
    RuntimeDemand, SelectedCallee,
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
    direct_callable_materializations: u64,
    first_class_callable_materializations: u64,
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
        let Some(Value::U64(direct_callable_materializations)) =
            event.measurements.get("direct_callable_materializations")
        else {
            return;
        };
        let Some(Value::U64(first_class_callable_materializations)) =
            event.measurements.get("first_class_callable_materializations")
        else {
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
            direct_callable_materializations: *direct_callable_materializations,
            first_class_callable_materializations: *first_class_callable_materializations,
            opaque_callable_demands: *opaque_callable_demands,
            runtime_demands: runtime_demands.clone(),
        });
    }
}

fn assert_resolved(outcome: DriveOutcome<Job, FactKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
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

fn has_callable_materialization(
    demand: &ExecutableRuntimeDemand,
    predicate: impl Fn(&CallableMaterialization) -> bool,
) -> bool {
    demand.callable_materializations.values().any(predicate)
}

#[test]
fn compiler2_semantic_analysis_does_not_reach_continuation_after_never_return() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let callsites = CallsiteCapture::new();
    tel.attach(&["fz", "compiler2", "callsite", "defined"], callsites.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.set_drive_timeout(Duration::from_millis(100));
    compiler.submit_code(CodeSubmission {
        name: Some("never_continuation.fz".to_string()),
        text: r#"
fn main() do
  panic("stop")
  |> dbg()
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

    assert_resolved(
        compiler.drive(),
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
        record.direct_callable_materializations >= 1,
        "runtime-demand telemetry should report direct callable materialization",
    );
    assert!(
        record.runtime_demands.values().any(|demand| {
            has_callable_materialization(demand, |materialization| {
                matches!(
                    materialization,
                    CallableMaterialization::DirectOnly { surfaces } if surfaces.len() == 1
                )
            })
        }),
        "a directly-invoked lambda should keep one exact resolved surface",
    );
}

#[test]
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
        has_callable_materialization(demand, |materialization| matches!(
            materialization,
            CallableMaterialization::FirstClass { .. }
        )),
        "a callable that escapes should be first-class at runtime: {demand:?}",
    );
    assert!(
        record.first_class_callable_materializations >= 1,
        "runtime-demand telemetry should count first-class callable materialization",
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
        has_callable_materialization(demand, |materialization| {
            matches!(materialization, CallableMaterialization::DirectOnly { .. })
        }),
        "make_adder/1 should still materialize its returned closure for direct transport",
    );
    assert!(
        !has_callable_materialization(demand, |materialization| {
            matches!(materialization, CallableMaterialization::FirstClass { .. })
        }),
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

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("opaque_callable_use.fz".to_string()),
        text: "fn main(f), do: f.(1)\n".to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "opaque callable use should settle");

    let main = functions.id("main", 1);
    let record = runtime_demands.last(root_id);
    let (_, demand) = runtime_demand_for_function(&record, main);
    assert!(
        matches!(
            demand.input_demands.as_slice(),
            [RuntimeDemand::Callable(callable)] if callable.opaque
        ),
        "an unresolved closure call should keep opaque callable demand explicit: {demand:?}",
    );
    assert!(
        record.opaque_callable_demands >= 1,
        "runtime-demand telemetry should count opaque callable demands",
    );
}
