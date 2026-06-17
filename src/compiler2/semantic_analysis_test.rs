use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::time::Duration;

use super::body::{DeliveredValueSource, delivered_value_joins};
use super::{
    CallSiteKey, CallSiteSummary, CallableFlowFact, CodeSubmission, Compiler2, DriveOutcome, ExecutableKey,
    ExecutableNeed, ExecutableRuntimeDemand, FactKey, FunctionId, FunctionRef, Job, RootId, RootSubmission,
    RuntimeDemand, SelectedCallee, ShapeDemand, World,
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

/// fz-hwn.19.2.4.12: a `defimpl` nested in a module the program never reaches by
/// name (`Mini`) used to be dropped — `DefineModule` is demand-gated, nothing
/// referenced `Mini`, so its impl never registered into `Susp`'s dispatch. The
/// `Susp.run([..])` call then found an empty dispatch and waited forever on the
/// *receiver type's* module (`List`), which never grows a `Susp` arm. Three jobs
/// (`SealSemanticClosure`, `AnalyzeActivation(make)`, `DefineModule`) livelocked.
///
/// The provider index fixes this: scope time records "Mini provides Susp-for-List"
/// as resolved ids, and the protocol call demands `DefineModule(Mini)` — the real
/// provider — so the impl registers and the closure settles.
/// `drive_until_semantic_closure`'s bound trips if it ever spins again.
///
/// Scoped to the closure. fz-hwn.19.2.4.15 proves this shape drives on through
/// transport: the captured `f`'s direct-call surface is now propagated to `run`'s
/// runtime demand (see
/// `compiler2_transport_plan_proves_protocol_dispatched_escaped_continuation_capture_surface`),
/// distinct from the reduce-shaped fz-hwn.19.2.4.9.
#[test]
fn compiler2_protocol_dispatched_escaped_continuation_closes_captured_callable() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("protocol_escaped_continuation.fz".to_string()),
        r#"
defprotocol Susp do
  @spec run(t(a), (a) -> b) :: () -> b
  fn run(coll, f)
end

defmodule Mini do
  defimpl Susp, for: List do
    fn run(_list, f), do: (fn () -> f.(1) end)
  end
end

fn make(f), do: Susp.run([1, 2, 3], f)
fn main(), do: make(fn x -> x + 1 end)
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    drive_until_semantic_closure(
        &mut world,
        root,
        "protocol-dispatched escaped continuation should close its captured callable activation",
    );
    assert!(
        world.fact_is_settled(&FactKey::SemanticClosed(root)),
        "protocol-dispatched escaped continuation should close its captured callable activation"
    );
}

/// fz-hwn.19.2.4.16.1: a `defimpl Susp, for: List` lexically nested in `Mini` is
/// hoisted to its own module `Susp.List` (Elixir's `__concat__`). Dispatch on a
/// `List` receiver demands exactly that impl — `DefineModule(Susp.List)` — and
/// never the lexical host `Mini`. This is the B-model win: the impl is the unit
/// of demand, not the arbitrarily-named module it happens to sit inside.
#[test]
fn compiler2_protocol_impl_resolves_to_concat_module_not_host() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("impl_concat_module.fz".to_string()),
        r#"
defprotocol Greet do
  @spec hello(t(a)) :: a
  fn hello(x)
end

defmodule Mini do
  defimpl Greet, for: List do
    fn hello(list), do: list
  end
end

fn main(), do: Greet.hello([1, 2, 3])
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    drive_until_semantic_closure(&mut world, root, "nested defimpl should resolve via its concat module");
    assert!(
        world.fact_is_settled(&FactKey::SemanticClosed(root)),
        "semantic closure should settle"
    );

    let impl_module = world.reference_module("Greet.List".to_string());
    let host_module = world.reference_module("Mini".to_string());
    assert!(
        world.fact_is_settled(&FactKey::ModuleDefined(impl_module)),
        "the hoisted impl module `Greet.List` should be defined to resolve the call"
    );
    assert!(
        !world.has_fact(&FactKey::ModuleDefined(host_module)),
        "the lexical host `Mini` must never be defined — the impl is the unit of demand, not its host"
    );
}

/// fz-hwn.19.2.4.16.3: a `defimpl` co-located with its `defprotocol` at file root
/// (no enclosing module) registers as `Protocol.Target` when the file is scoped —
/// the same path a runtime protocol file takes when its protocol is referenced.
/// This is what lets a built-in impl ride in on its protocol's reference (T4),
/// dissolving the "scan the receiver type's module" convention.
#[test]
fn compiler2_root_colocated_protocol_impl_registers_on_scope() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("colocated_impl.fz".to_string()),
        r#"
defprotocol Greet do
  @spec hello(t(a)) :: a
  fn hello(x)
end

defimpl Greet, for: List do
  fn hello(list), do: list
end

fn main(), do: Greet.hello([1, 2, 3])
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    drive_until_semantic_closure(
        &mut world,
        root,
        "co-located defimpl should resolve via its concat module",
    );
    assert!(
        world.fact_is_settled(&FactKey::SemanticClosed(root)),
        "semantic closure should settle"
    );

    let impl_module = world.reference_module("Greet.List".to_string());
    assert!(
        world.fact_is_settled(&FactKey::ModuleDefined(impl_module)),
        "a defimpl co-located with its protocol should register as `Greet.List` and resolve the call"
    );
}

/// fz-hwn.19.2.4.11 (semantic root): a closure call to a *captured* callable
/// must return the callable's resolved result type, not blanket `any`.
///
/// `wrap(g)` returns `fn (a, b) -> g.(a, b) end`. Once captured, `g`'s type
/// erases its closure identity to the bare arrow `(α0, α1) -> α2`. When the
/// wrapper is later called with concrete `int` arguments, the closure call
/// `g.(a, b)` *does* resolve to the captured lambda and its callsite summary
/// settles to `int` — but `resolve_closure_call` discarded the resolved arrow's
/// declared return and answered the earned-`any` dynamic edge for the surface
/// clause. That stale `any` is the wrapper's return, and it cascades: `apply`
/// returns `any`, then `main` returns `any`, and the whole reduce family
/// (fold_capture_closure, operator-ref reduce) collapses to `Ty(any)` transport
/// lanes / native fatals downstream.
///
/// This is the minimal, transport-free reproduction: at semantic closure the
/// root activation's return must be `int`. The `--dump activations` view of this
/// shape shows the contradiction directly — the wrapper's sole callsite reads
/// `=> int` while its activation reads `return: any`.
#[test]
fn compiler2_captured_callable_closure_call_keeps_resolved_return() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("captured_callable_return.fz".to_string()),
        r#"
fn apply(f, x, y), do: f.(x, y)
fn wrap(g), do: (fn (a, b) -> g.(a, b) end)
fn main(), do: apply(wrap(fn (x, y) -> x + y end), 1, 2)
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    drive_until_semantic_closure(
        &mut world,
        root,
        "captured-callable closure call should close semantic analysis",
    );

    let main_activation = super::identity::ActivationKey {
        root,
        function: world.root_function(root),
        input: Vec::new(),
    };
    let main_return = world
        .activation_return(&main_activation)
        .expect("main/0 should have a settled return type at semantic closure");
    assert!(
        world.types().is_integer(&main_return),
        "a captured callable resolved to an int-returning lambda must keep its int \
         result through the wrapper; main/0 returned `{}` instead of `int`",
        world.types().display(&main_return),
    );
}

/// The provider index is reference-not-pull: an unused `defimpl` records its
/// provider mapping at scope time but must not drag the protocol or the
/// providing module into the program. A root that never dispatches `Susp`
/// closes, and neither `Mini` (the provider) nor the protocol impl is ever
/// defined — cold stays cold.
#[test]
fn compiler2_unused_protocol_impl_stays_cold() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("unused_protocol_impl.fz".to_string()),
        r#"
defprotocol Susp do
  @spec run(t(a)) :: integer
  fn run(coll)
end

defmodule Mini do
  defimpl Susp, for: List do
    fn run(_list), do: 0
  end
end

fn main(), do: 1
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    world.demand(Job::SealSemanticClosure(root));
    let outcome = world.drive_for(Some(Duration::from_secs(5)));
    assert_resolved(outcome, "a program with an unused `defimpl` must still close");
    assert!(
        world.fact_is_settled(&FactKey::SemanticClosed(root)),
        "the root that never dispatches the protocol should close"
    );
    let mini = world.reference_module("Mini".to_string());
    assert!(
        world.module_defined_revision(mini).is_none(),
        "an unused `defimpl`'s provider module must stay cold — never defined"
    );
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
        vec![RuntimeDemand::ignore()],
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
            [input] if !input.callable.is_empty()
                && input.callable.opaque
                && input.callable.resolved.len() == 1
                && input.callable.resolved.iter().any(|surface| surface.inputs.len() == 1)
        ),
        "an unresolved closure call should keep opaque callable demand and its observed surface explicit: {demand:?}",
    );
    assert!(
        record.opaque_callable_demands >= 1,
        "runtime-demand telemetry should count opaque callable demands",
    );
}

#[test]
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
                [arg] if !arg.callable.is_empty()
                    && arg.callable.escape && !arg.callable.opaque && arg.callable.resolved.is_empty()
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
    let joined_demand = demand
        .value_demands
        .get(&joined_value)
        .unwrap_or_else(|| panic!("joined callable value {joined_value:?} should have runtime demand"));
    if joined_demand.callable.is_empty() {
        panic!("joined value {joined_value:?} should be callable-demanded: {demand:?}");
    }
    let joined_callable = &joined_demand.callable;
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
            demand.callable.is_empty()
                && matches!(
                    &demand.shape,
                    ShapeDemand::TupleFields(fields)
                        if fields.len() == 2
                            && fields[0].callable.is_empty()
                            && matches!(&fields[0].shape, ShapeDemand::TupleFields(inner) if inner.len() == 2)
                            && fields[1].callable.is_empty()
                            && matches!(&fields[1].shape, ShapeDemand::Whole)
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
        resume_demands.iter().any(|demand| {
            demand.callable.is_empty() && matches!(&demand.shape, ShapeDemand::TupleFields(fields) if fields.len() == 2)
        }),
        "recursive call resume value should carry tuple-field demand upstream: {resume_demands:?}"
    );
}

#[test]
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
        vec![RuntimeDemand::whole()],
        "Kernel.dbg/1 must still demand its input as a runtime value even when callers ignore the returned value",
    );

    let main = functions.id("main", 0);
    let (_, main_demand) = runtime_demand_for_function(&record, main);
    assert!(
        main_demand
            .entry_capture_demands
            .values()
            .any(|demands| demands.as_slice() == [RuntimeDemand::whole()]),
        "the continuation after dbg(stats) must keep one captured runtime value live for the later field access: {main_demand:?}",
    );
}

/// Lattice-algebra properties of the split [`RuntimeDemand`] product.
///
/// These pin the single reason the data-shape axis and the callable-usage axis
/// were split apart: the join must be a monotone join-semilattice so the demand
/// fixpoint has a unique, schedule-independent least solution. In particular,
/// the callable `opaque`/`escape` bits must only ever rise — the pre-split
/// `Value ⊔ Callable → Value` collapse could erase them and a boundary
/// re-grounding could then non-monotonically reintroduce `opaque:false`.
mod demand_lattice {
    use super::super::{CallableDemand, CallableSurface, RuntimeDemand, ShapeDemand};

    fn product(shape: ShapeDemand, callable: CallableDemand) -> RuntimeDemand {
        RuntimeDemand { shape, callable }
    }

    fn sample() -> Vec<RuntimeDemand> {
        let mut surface_resolved = CallableDemand::default();
        surface_resolved.resolved.insert(CallableSurface::new(vec![]));
        vec![
            RuntimeDemand::ignore(),
            RuntimeDemand::whole(),
            RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole()]),
            RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(), RuntimeDemand::whole()]),
            RuntimeDemand::tuple_fields(vec![RuntimeDemand::ignore(), RuntimeDemand::whole()]),
            RuntimeDemand::callable(CallableDemand::opaque()),
            RuntimeDemand::callable(CallableDemand::escaped()),
            RuntimeDemand::callable(surface_resolved),
            product(ShapeDemand::Whole, CallableDemand::escaped()),
            product(ShapeDemand::Whole, CallableDemand::opaque()),
        ]
    }

    #[test]
    fn join_is_commutative_idempotent_and_associative() {
        let sample = sample();
        for a in &sample {
            assert_eq!(a.join(a), *a, "join is idempotent on normalized demands: {a:?}");
            for b in &sample {
                assert_eq!(a.join(b), b.join(a), "join is commutative: {a:?} vs {b:?}");
                for c in &sample {
                    assert_eq!(
                        a.join(b).join(c),
                        a.join(&b.join(c)),
                        "join is associative: {a:?}, {b:?}, {c:?}",
                    );
                }
            }
        }
    }

    #[test]
    fn callable_soundness_bits_only_rise_under_join() {
        let sample = sample();
        for a in &sample {
            for b in &sample {
                let joined = a.join(b);
                assert!(
                    joined.callable.opaque >= (a.callable.opaque || b.callable.opaque),
                    "opaque must subsume both operands: {a:?} ⊔ {b:?} = {joined:?}",
                );
                assert!(
                    joined.callable.escape >= (a.callable.escape || b.callable.escape),
                    "escape must subsume both operands: {a:?} ⊔ {b:?} = {joined:?}",
                );
                assert!(
                    a.callable.resolved.is_subset(&joined.callable.resolved)
                        && b.callable.resolved.is_subset(&joined.callable.resolved),
                    "resolved surfaces only grow: {a:?} ⊔ {b:?} = {joined:?}",
                );
            }
        }
    }

    /// The exact regression the split exists to kill: a whole-representation
    /// demand meeting an opaque-callable demand must keep the value's data shape
    /// AND its callable obligation — the shape axis cannot erase the callable
    /// axis, so `opaque` survives instead of being collapsed and later
    /// re-grounded to `opaque:false`.
    #[test]
    fn whole_demand_never_erases_callable_opacity() {
        let joined = RuntimeDemand::whole().join(&RuntimeDemand::callable(CallableDemand::opaque()));
        assert_eq!(joined.shape, ShapeDemand::Whole, "shape axis is preserved: {joined:?}");
        assert!(joined.callable.opaque, "callable opacity is preserved: {joined:?}");
        assert!(
            !joined.callable.is_empty(),
            "the callable obligation survives: {joined:?}"
        );
    }
}
