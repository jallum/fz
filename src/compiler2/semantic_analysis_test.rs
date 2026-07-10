use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

use super::drive_test::{CallsiteCapture, FunctionCapture, assert_resolved, function_id};
use super::job_budget_guard::JobBudgetGuard;
use super::{CallSiteSummary, ExecutableKey, ExecutableNeed, FactKey, FunctionId, Job, RootId, SelectedCallee, World};
use crate::telemetry::handler::{Event, EventKind, Handler};

/// Captures the executable behind every `executable_transport.projected`
/// event: the set of executables whose transport component was freshly
/// materialized by a drive (a cache-served pull emits nothing). `clear()`
/// between drives isolates one drive's blast radius from the next. This is
/// the product-path successor to the legacy `executable_transport.derived`
/// signal (native cutover moved off that spine; see fz-go4.18.11).
struct TransportProjectedCapture {
    executables: Rc<RefCell<Vec<ExecutableKey>>>,
}

impl TransportProjectedCapture {
    fn new() -> Self {
        Self {
            executables: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(TransportProjectedCaptureHandler {
            executables: self.executables.clone(),
        })
    }

    fn clear(&self) {
        self.executables.borrow_mut().clear();
    }

    fn executables(&self) -> Vec<ExecutableKey> {
        self.executables.borrow().clone()
    }
}

struct TransportProjectedCaptureHandler {
    executables: Rc<RefCell<Vec<ExecutableKey>>>,
}

impl Handler for TransportProjectedCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "executable_transport", "projected"] || event.kind != EventKind::Event {
            return;
        }
        let Some(executable) = event
            .metadata
            .get("executable")
            .and_then(|value| value.downcast_ref::<ExecutableKey>())
        else {
            return;
        };
        self.executables.borrow_mut().push(executable.clone());
    }
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

/// A protocol impl-target classification must come from the `StructDefined`
/// fact, not from matching the target module's last name segment against the
/// compiler's built-in ground value families. `Shadow.List` is a genuine
/// struct whose *last segment* happens to collide with the built-in `List`
/// family name. A string-driven classifier (matching `"List"` before ever
/// checking for a struct) would misclassify this target as "list of any":
/// the receiver (a `Shadow.List` struct) would then never overlap the
/// (wrong) list-shaped target type, `Peek.first` would never find a
/// matching arm, and `main` would never settle. The fact-backed classifier
/// checks `StructDefined(Shadow.List)` first, so the struct's own declared
/// field types (nominal identity + tuple/map evidence) reach the dispatch,
/// and `l.head`'s field access resolves to the declared `integer` — not
/// `any`.
#[test]
fn compiler2_protocol_impl_target_struct_is_not_classified_by_last_segment_name() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("impl_target_struct_not_stringly.fz".to_string()),
        r#"
defprotocol Peek do
  @spec first(t(a)) :: a
  fn first(x)
end

defmodule Shadow do
  defmodule List do
    defstruct [:head, :tail]
    @type t :: %List{head: integer, tail: integer}

    fn new(head, tail), do: %List{head: head, tail: tail}
  end

  defimpl Peek, for: List do
    fn first(l), do: l.head
  end
end

fn main(), do: Peek.first(Shadow.List.new(1, 2))
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    drive_until_semantic_closure(
        &mut world,
        root,
        "a struct target whose last segment shadows a built-in family name should still \
         dispatch: fact-backed classification must not misroute it to the built-in list shape",
    );

    let global_list = world.reference_module("List");
    let shadow_list = world.reference_module("Shadow.List".to_string());
    assert_ne!(
        global_list, shadow_list,
        "the nested struct and the built-in runtime List module must be distinct identities"
    );

    let protocol = world.reference_module("Peek");
    let dispatch = world
        .protocol_dispatch(protocol)
        .expect("Peek should publish a dispatch fact for its single defimpl");
    assert_eq!(
        dispatch.arms.len(),
        1,
        "one defimpl should contribute exactly one dispatch arm"
    );
    assert_eq!(
        dispatch.arms[0].target, shadow_list,
        "the impl target should resolve to the nested Shadow.List struct module, not the built-in List"
    );

    let main_function = world.root_function(root);
    let main_activation = super::identity::ActivationKey::from_inputs(root, main_function, &[], world.types_mut());
    let main_return = world
        .activation_return(&main_activation)
        .expect("main/0 should have a settled return type at semantic closure");
    assert!(
        world.types().is_integer(&main_return),
        "Peek.first(l) should resolve through Shadow.List's declared struct field types and \
         return the `head` field's declared `integer` type, not `any`; main/0 returned `{}`",
        world.types().display(&main_return),
    );
}

/// A protocol impl target forward-referenced before its `defstruct` settles must
/// reclassify from nominal to struct once `StructDefined` publishes — the
/// classifier's dependency on the struct fact is registered even when the fact
/// is absent at read time, so a later publication re-wakes and re-types it.
///
/// This is the out-of-order sibling of the same-order shadow test above, and it
/// is the one that pins the *subscription*. The classification of `for: Boxy`
/// DEPENDS on whether `Boxy` is a struct: a classifier that recorded the
/// `StructDefined(Boxy)` dependency only in the branch where the struct is
/// already defined would leave a forward-referenced target permanently
/// mis-typed — nothing would re-wake the reader that concluded on the absent
/// fact. The construction forces exactly that ordering:
///
/// * `main(x)` dispatches `Peek.first(x)` on its `any` parameter — a receiver
///   that overlaps the impl target in *either* classification (both share the
///   `impl-target::Boxy` runtime predicate; the difference between nominal and
///   struct lives only in the *intersected* type, not in whether a match
///   fires). The callback `first(b), do: b` returns that intersected receiver
///   unchanged, so `main`'s settled return type IS the impl target's shape.
/// * `Boxy` is forward-referenced only as the impl target in unit 1, and its
///   `defstruct` lands in a second unit pulled by an unrelated `probe` root.
///
/// So `main` resolves in *both* drives, and the observable is the *shape* of
/// its return: a bare opaque `impl-target::Boxy` while `Boxy` is nominal, versus
/// one carrying tuple/map field evidence once it is a struct. We probe that with
/// `intersect(main_return, %{val: any})`: empty against the opaque nominal tag
/// (a struct value keeps its nominal identity out of the plain-map kind), and
/// non-empty against the struct's map evidence.
///
/// Non-vacuous: against a classifier that pushed `StructDefined(Boxy)` only in
/// the struct-present branch, `main`'s drive-1 conclusion (nominal target,
/// return intersects no map) records no subscription on `StructDefined(Boxy)`,
/// so drive 2's publication has no subscriber to re-wake — `main`'s return
/// stays the opaque nominal shape and the final `non-empty` assertion fails.
/// `ProtocolImplProviders(Peek)` is settled in drive 1 and unchanged in drive 2,
/// so it is not an alternate re-wake path.
#[test]
fn compiler2_forward_referenced_struct_impl_target_reclassifies_when_structdefined_lands() {
    use super::super::types::MapKey;

    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut world = World::new(&tel);

    // A `%{val: any}` probe type: disjoint from a struct's opaque nominal tag,
    // overlapping its structural map evidence. This is what tells the two
    // classifications apart in `main`'s settled return.
    let any = world.types_mut().any();
    let map_probe = world.types_mut().map(&[(MapKey::Atom("val".to_string()), any)]);

    // Unit 1: the protocol, its impl for a not-yet-defined `Boxy`, and a caller
    // that dispatches on its own `any` parameter — nothing here defines `Boxy`.
    world.submit_code(
        Some("forward_ref_impl.fz".to_string()),
        r#"
defprotocol Peek do
  @spec first(t(a)) :: a
  fn first(x)
end

defimpl Peek, for: Boxy do
  fn first(b), do: b
end

fn main(x), do: Peek.first(x)
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    assert_resolved(
        world.drive(),
        "drive 1: the protocol and caller settle even though Boxy's defstruct has not landed",
    );

    let main_function = world.root_function(root);
    let main_activation = super::identity::ActivationKey::from_inputs(root, main_function, &[any], world.types_mut());
    let drive1_return = world
        .activation_return(&main_activation)
        .expect("drive 1: main resolves — the any receiver matches the nominal impl target");
    let drive1_map_overlap = world.types_mut().intersect(drive1_return, map_probe);
    assert!(
        world.types().is_empty(&drive1_map_overlap),
        "drive 1: Boxy is only forward-referenced, so its impl target is the opaque nominal tag; \
         main's return carries no struct map evidence (intersect with %{{val: any}} is empty), got `{}`",
        world.types().display(&drive1_return),
    );

    // Unit 2: `Boxy`'s real definition (defstruct + declared field types), pulled
    // into the program by an unrelated root that calls one of its functions —
    // this is the independent event that publishes `StructDefined(Boxy)`.
    world.submit_code(
        Some("boxy_defstruct.fz".to_string()),
        r#"
defmodule Boxy do
  defstruct [:val]
  @type t :: %Boxy{val: integer}

  fn ident(x), do: x
end

fn probe(), do: Boxy.ident(1)
"#
        .to_string(),
    );
    world.submit_root(None, "probe".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(
        world.drive(),
        "drive 2: defining Boxy publishes StructDefined(Boxy), which must re-wake main's classifier",
    );

    let drive2_return = world
        .activation_return(&main_activation)
        .expect("drive 2: main still resolves after Boxy is defined");
    let drive2_map_overlap = world.types_mut().intersect(drive2_return, map_probe);
    assert!(
        !world.types().is_empty(&drive2_map_overlap),
        "drive 2: the standing StructDefined(Boxy) subscription must have re-woken main's analysis, \
         reclassifying the impl target from nominal to struct so main's return now carries the \
         struct's tuple/map field evidence (intersect with %{{val: any}} is non-empty), got `{}`",
        world.types().display(&drive2_return),
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

    let main_function = world.root_function(root);
    let main_activation = super::identity::ActivationKey::from_inputs(root, main_function, &[], world.types_mut());
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

    drive_until_semantic_closure(&mut world, root, "a program with an unused `defimpl` must still close");
    let mini = world.reference_module("Mini".to_string());
    assert!(
        world.module_defined_revision(mini).is_none(),
        "an unused `defimpl`'s provider module must stay cold — never defined"
    );
}

/// Drives the root's whole closure to settlement through the backend product,
/// the demand-driven pull that now stands where the legacy seal did: its
/// internal pull loop settles every reachable activation's analysis before it
/// packages the product, so a resolved drive proves the closure converged.
fn drive_until_semantic_closure(world: &mut World<'_>, root: RootId, message: &str) {
    world.demand(Job::BuildBackendProduct(root));
    assert_resolved(world.drive(), message);
}

fn summary_has_function(summary: &CallSiteSummary, function: FunctionId) -> bool {
    summary
        .targets
        .iter()
        .any(|target| target.callee == SelectedCallee::Function(function))
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

    let main = function_id(&functions, "main", 0);
    let panic = function_id(&functions, "panic", 1);
    let dbg = function_id(&functions, "dbg", 1);
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
/// A callsite whose two incoming branches disagree on `cap`'s type (`int`
/// on one arm, `string` on the other) is observed twice by
/// `coalesce_call_emissions` before it settles into one published target,
/// so that target gets rebuilt (`rebuild_coalesced_call_emission`). The
/// callee here is a zero-argument closure that only ever reads its capture
/// -- its real activation is one input wide (the capture slot alone), even
/// though its declared (capture-free) surface is zero wide. Rebuilding from
/// that zero-wide surface instead of the activation's own `.inputs()` used
/// to mint a truncated, zero-input activation, and derive_executable_runtime_demand's
/// per-clause live-demand pass indexed the (nonexistent) capture slot on it
/// and panicked. This test proves the whole backend product settles without
/// truncating the activation.
#[test]
fn compiler2_coalesced_closure_target_keeps_its_capture_slot() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("coalesced_closure_capture.fz".to_string()),
        r#"
fn main() do
  cap = if true, do: 1, else: "s"
  f = fn () -> cap end
  f.()
end
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    drive_until_semantic_closure(
        &mut world,
        root,
        "a closure capturing a branch-joined value must settle without truncating its activation",
    );

    let main_function = world.root_function(root);
    let main_activation = super::identity::ActivationKey::from_inputs(root, main_function, &[], world.types_mut());
    let main_return = world
        .activation_return(&main_activation)
        .expect("main/0 should have a settled return type at semantic closure");
    let displayed = world.types().display(&main_return);
    assert!(
        displayed.contains("int") && displayed.contains("binary"),
        "main/0 should return the captured branch-joined union of int and string, got `{displayed}`",
    );
}

#[test]
fn compiler2_adding_a_defimpl_reprojects_only_the_cone_its_dispatch_reaches() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let transport = TransportProjectedCapture::new();
    tel.attach(
        &["fz", "compiler2", "executable_transport", "projected"],
        transport.handler(),
    );
    // Livelock backstop: if cone-scoped re-derivation ever loops, this names the
    // runaway job kind instead of hanging the drive.
    let job_guard = JobBudgetGuard::new();
    tel.attach(&["fz", "compiler2", "job"], job_guard.handler());

    let mut world = World::new(&tel);
    world.submit_code(
        Some("blast_radius_v1.fz".to_string()),
        r#"
defprotocol Shout do
  @spec say(t(a)) :: a
  fn say(x)
end

defimpl Shout, for: Integer do
  fn say(n), do: n
end

fn lonely(a, b), do: a + b

fn quiet(), do: lonely(3, 4)

fn shouty() do
  picked = if true, do: 1, else: "two"
  Shout.say(picked)
end

fn main() do
  shouty()
  quiet()
end
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    world.demand(Job::LowerNativeProgram(root));
    assert_resolved(
        world.drive(),
        "drive 1 with one Shout impl should settle the transport plan",
    );

    let lonely_id = function_id(&functions, "lonely", 2);
    let s1 = transport.executables();
    assert!(
        s1.iter().any(|executable| executable.activation.function == lonely_id),
        "lonely's transport must be derived on the first drive; saw {s1:?}",
    );

    transport.clear();
    world.submit_code(
        Some("blast_radius_v2.fz".to_string()),
        r#"
defimpl Shout, for: String do
  fn say(s), do: s
end
"#
        .to_string(),
    );
    world.demand(Job::LowerNativeProgram(root));
    assert_resolved(
        world.drive(),
        "drive 2 adding the String impl should re-settle the transport plan",
    );

    let s2 = transport.executables();
    assert!(
        !s2.iter().any(|executable| executable.activation.function == lonely_id),
        "bounded blast radius: adding an unrelated defimpl must NOT re-derive lonely's transport; re-derived {s2:?}",
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

    let main = function_id(&functions, "main", 0);
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
