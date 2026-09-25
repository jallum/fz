//! What a function's static shape says before any activation exists.
//!
//! Source skeletons are read off a body the ordinary lowering produced --
//! the source is submitted and driven until its bodies exist, exactly as the
//! compiler drives them -- so a shape asserted here is a shape keying will
//! actually see. Algebra tests also bind these shapes through small frame
//! graphs, without constructing activations or concrete type histories.

use std::collections::{BTreeMap, HashMap};

use super::*;
use crate::compiler2::canon::function_label;
use crate::compiler2::drive::{FactKey, Job};
use crate::compiler2::world::World;
use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

#[test]
fn a_branch_result_passed_to_a_call_is_a_union_argument() {
    let all = skeletons(
        "branch_union_argument.fz",
        "def target(value), do: value\n\
         def relay(flag, x, y) do\n\
           value = if flag, do: x, else: y\n\
           target(value)\n\
         end\n\
         def main(), do: relay(true, :left, :right)\n",
    );
    let relay = all.get("relay/3");
    let call = relay
        .invocations
        .iter()
        .find(|(site, _)| all.callee(relay, **site) == "target/1")
        .expect("relay invokes target")
        .1;
    let [Skeleton::Union(branches)] = call.arguments.as_slice() else {
        panic!("a delivered branch join is a union argument: {:?}", call.arguments);
    };
    assert_eq!(branches.len(), 2);
    assert!(branches.contains(&Skeleton::Input(1)));
    assert!(branches.contains(&Skeleton::Input(2)));
}

#[test]
fn whole_row_unfolds_one_recursive_constructor_and_joint_projection_returns_to_its_family() {
    let identity = Substitution::in_frame(0, &[Skeleton::Input(0), Skeleton::Input(1)]);
    let wrapped = Substitution::in_frame(
        0,
        &[
            Skeleton::Tuple(vec![Skeleton::Input(0)]),
            Skeleton::Tuple(vec![Skeleton::Input(1)]),
        ],
    );
    let projected = Substitution::in_frame(
        0,
        &[
            Skeleton::project(Skeleton::Input(0), ProjectStep::TupleField(0)),
            Skeleton::project(Skeleton::Input(1), ProjectStep::TupleField(0)),
        ],
    );
    let mut rebind = |_: &u32, _: &Substitution<u32>| panic!("these spines substitute directly");
    assert_eq!(identity.apply_once(&0, &wrapped, &mut rebind), wrapped);
    assert_eq!(projected.apply_once(&0, &wrapped, &mut rebind), identity);
    let twice = BoundSkeleton::new(
        0,
        Skeleton::project(projected.arguments[0].shape.clone(), ProjectStep::TupleField(0)),
    );
    assert_eq!(
        twice.apply_once(&0, &wrapped, &mut rebind),
        projected.arguments[0],
        "one outer unfold does not choose the newly exposed inner recursive family again"
    );
}

#[test]
fn whole_row_application_rebinds_original_local_operations_but_preserves_inserted_producers() {
    let ground = Skeleton::Ground(ValueId::from_u32(7));
    let result = Skeleton::Result {
        callsite: CallSiteId::from_u32(2),
        value: ValueId::from_u32(3),
    };
    let replacement = Substitution {
        arguments: vec![BoundSkeleton::new(2, ground.clone())],
    };
    let mut rebind = |frame: &u32, row: &Substitution<u32>| {
        assert_eq!(*frame, 0);
        assert_eq!(*row, replacement);
        1
    };
    let original = Substitution::in_frame(0, &[Skeleton::Input(0), ground.clone(), result.clone()]);
    assert_eq!(
        original.apply_once(&0, &replacement, &mut rebind).arguments,
        vec![
            replacement.arguments[0].clone(),
            BoundSkeleton::new(1, ground.clone()),
            BoundSkeleton::new(1, result)
        ]
    );
    let tuple = BoundSkeleton::new(0, Skeleton::Tuple(vec![Skeleton::Input(0), ground.clone()]));
    let rebound = tuple.apply_once(&0, &replacement, &mut rebind);
    assert_eq!(rebound, BoundSkeleton::new(1, tuple.shape.clone()));
    let mut lookup = |frame: &u32, slot: usize| (*frame == 1).then(|| replacement.arguments[slot].clone());
    assert_eq!(
        rebound.project(ProjectStep::TupleField(0), &mut lookup),
        replacement.arguments[0]
    );
    assert_eq!(
        rebound.project(ProjectStep::TupleField(1), &mut lookup),
        BoundSkeleton::new(1, ground)
    );
    assert_eq!(
        BoundSkeleton::new(2, Skeleton::Input(0)).apply_once(&0, &replacement, &mut rebind),
        BoundSkeleton::new(2, Skeleton::Input(0)),
        "another source frame is not rebound"
    );
}

#[test]
fn one_source_first_equation_binds_to_each_calls_own_first_argument() {
    let all = skeletons(
        "bound_first.fz",
        "def first(x, y), do: x\n\
         def main() do\n first(2, :left)\n first(1.0, :right)\nend\n",
    );
    let first = all.get("first/2");
    let calls: Vec<_> = all.get("main/0").invocations.values().collect();
    assert_eq!(calls.len(), 2);
    let arguments: Vec<_> = calls
        .iter()
        .map(|call| Substitution::in_frame(0, &call.arguments))
        .collect();
    let mut lookup = |frame: &usize, slot: usize| match *frame {
        1 | 2 => Some(arguments[*frame - 1].arguments[slot].clone()),
        _ => None,
    };
    let left = BoundSkeleton::new(1, joined(first)).resolve(&mut lookup);
    let right = BoundSkeleton::new(2, joined(first)).resolve(&mut lookup);
    assert_eq!(left, arguments[0].arguments[0]);
    assert_eq!(right, arguments[1].arguments[0]);
    assert_ne!(left, right, "one definition does not merge its distinct bound uses");
}

#[test]
fn ordered_substitution_composes_swap_with_swap_to_identity() {
    let swap = [Skeleton::Input(1), Skeleton::Input(0)];
    let first = Substitution::in_frame(0, &swap);
    let second = Substitution::in_frame(1, &swap);
    let composed = second.compose(&mut |frame, slot| (*frame == 1).then(|| first.arguments[slot].clone()));
    assert_eq!(
        composed,
        Substitution::in_frame(0, &[Skeleton::Input(0), Skeleton::Input(1)])
    );
    assert_eq!(
        first.apply_once(&0, &first, &mut |_, _| panic!("a permutation only replaces inputs")),
        composed,
        "simultaneous application composes a permutation without chasing its newly inserted slots"
    );
}

#[test]
fn bound_projection_cancels_a_constructor_without_changing_its_producers_frame() {
    let producer = BoundSkeleton::new(0, Skeleton::Ground(ValueId::from_u32(7)));
    let mut lookup = |frame: &u32, slot| match (*frame, slot) {
        (2, 0) => Some(BoundSkeleton::new(1, Skeleton::Tuple(vec![Skeleton::Input(0)]))),
        (1, 0) => Some(producer.clone()),
        _ => None,
    };
    assert_eq!(
        BoundSkeleton::new(2, Skeleton::Input(0)).project(ProjectStep::TupleField(0), &mut lookup),
        producer
    );
}

#[test]
fn bound_source_leaves_and_distinct_use_results_keep_their_frames() {
    let result = Skeleton::Result {
        callsite: CallSiteId::from_u32(2),
        value: ValueId::from_u32(4),
    };
    let left = BoundSkeleton::new(0, result.clone());
    let right = BoundSkeleton::new(1, result);
    assert_ne!(left, right, "a source result port belongs to one bound use");
    let supplied = Substitution {
        arguments: vec![
            left.clone(),
            right.clone(),
            BoundSkeleton::new(0, Skeleton::Ground(ValueId::from_u32(4))),
        ],
    };
    assert_eq!(
        Substitution::in_frame(2, &[Skeleton::Input(1), Skeleton::Input(0), Skeleton::Input(2)])
            .compose(&mut |frame, slot| (*frame == 2).then(|| supplied.arguments[slot].clone()))
            .arguments,
        vec![right, left, supplied.arguments[2].clone()]
    );
}

#[test]
fn recursive_substitution_references_stay_finite_and_keep_their_anchor() {
    let original = BoundSkeleton::new(0, Skeleton::Input(0));
    let mut lookup = |frame: &u32, _slot| Some(BoundSkeleton::new(1 - *frame, Skeleton::Input(0)));
    assert_eq!(original.resolve(&mut lookup), original);
    let projected = BoundSkeleton::new(0, Skeleton::project(Skeleton::Input(0), ProjectStep::TupleField(0)));
    assert_eq!(projected.resolve(&mut lookup), projected);
    assert_eq!(
        original.resolve(&mut |_, _| Some(projected.clone())),
        original,
        "a cyclic projected reference also stays anchored rather than growing a projection history"
    );
}

#[test]
fn substitution_is_lazy_under_constructors_and_does_not_claim_execution_completion() {
    let shape = Skeleton::Tuple(vec![Skeleton::Input(0), Skeleton::Ground(ValueId::from_u32(3))]);
    let bound = BoundSkeleton::new(0, shape.clone());
    assert_eq!(
        bound.resolve(&mut |_, _| panic!("constructor children remain source references")),
        bound
    );
    assert_eq!(
        bound.project(ProjectStep::TupleField(0), &mut |_, _| None),
        BoundSkeleton::new(0, Skeleton::Input(0))
    );
    assert_eq!(
        bound.shape, shape,
        "value projection does not rewrite the source prerequisites"
    );
}

#[test]
fn invocation_equation_distinguishes_which_input_is_called() {
    let all = skeletons(
        "invocation_operand.fz",
        "def first(f, g, x), do: f.(x)\n\
         def second(f, g, x), do: g.(x)\n\
         def main() do\n\
           first(fn (x) -> x end, fn (x) -> :other end, 1)\n\
           second(fn (x) -> x end, fn (x) -> :other end, 1)\n\
         end\n",
    );
    let first = all.get("first/3");
    let second = all.get("second/3");
    assert_eq!(
        first.invocations[&sole_result(&joined(first))].arguments,
        vec![Skeleton::Input(2)]
    );
    assert_eq!(
        second.invocations[&sole_result(&joined(second))].arguments,
        vec![Skeleton::Input(2)]
    );
    assert_ne!(
        first.invocations.values().map(|call| &call.callee).collect::<Vec<_>>(),
        second.invocations.values().map(|call| &call.callee).collect::<Vec<_>>(),
        "f.(x) and g.(x) are different equations: the callable operand must survive source lowering"
    );
}

#[test]
fn repeated_and_composed_invocations_retain_their_ordered_result_dependencies() {
    let all = skeletons(
        "invocation_dependencies.fz",
        "def twice(f, x), do: f.(f.(x))\n\
         def compose(f, g, x), do: f.(g.(x))\n\
         def main() do\n\
           twice(fn x -> x end, 1)\n\
           compose(fn x -> x end, fn x -> x end, 1)\n\
         end\n",
    );
    for (name, inner_callee, input) in [("twice/2", 0, 1), ("compose/3", 1, 2)] {
        let skeleton = all.get(name);
        assert_eq!(skeleton.invocations.len(), 2);
        let outer_site = sole_result(&joined(skeleton));
        let outer = &skeleton.invocations[&outer_site];
        assert_eq!(outer.callee, InvocationCallee::Value(Skeleton::Input(0)));
        let [
            Skeleton::Result {
                callsite: inner_site, ..
            },
        ] = outer.arguments.as_slice()
        else {
            panic!("{name}: outer invocation must read the inner invocation's result");
        };
        assert_ne!(
            *inner_site, outer_site,
            "successive calls are distinct source positions"
        );
        let inner = &skeleton.invocations[inner_site];
        assert_eq!(inner.callee, InvocationCallee::Value(Skeleton::Input(inner_callee)));
        assert_eq!(inner.arguments, vec![Skeleton::Input(input)]);
        assert_eq!(inner.destination, ControlDestination::Deliver(outer.entry));
        assert_eq!(outer.destination, ControlDestination::Return);
        assert_ne!(inner.result, outer.result);
    }
}

#[test]
fn invocation_retains_a_projected_or_returned_callee_and_duplicate_arguments() {
    let all = skeletons(
        "invocation_operands.fz",
        "def projected(pair, x, y) do\n\
           {_, f} = pair\n\
           f.(y, x, y)\n\
         end\n\
         def returned(maker, x) do\n f = maker.()\n f.(x)\nend\n\
         def main() do\n\
           projected({:unused, fn (a, b, c) -> {a, b, c} end}, 1, :ok)\n\
           returned(fn () -> fn x -> x end end, 2)\n\
         end\n",
    );
    let projected = all.get("projected/3");
    let call = &projected.invocations[&sole_result(&joined(projected))];
    assert_eq!(
        call.callee,
        InvocationCallee::Value(Skeleton::project(Skeleton::Input(0), ProjectStep::TupleField(1)))
    );
    assert_eq!(
        call.arguments,
        vec![Skeleton::Input(2), Skeleton::Input(1), Skeleton::Input(2)]
    );

    let returned = all.get("returned/2");
    let outer_site = sole_result(&joined(returned));
    let outer = &returned.invocations[&outer_site];
    let InvocationCallee::Value(Skeleton::Result { callsite, .. }) = &outer.callee else {
        panic!("invoking a returned callable must retain its producing invocation");
    };
    let inner = &returned.invocations[callsite];
    assert_eq!(inner.callee, InvocationCallee::Value(Skeleton::Input(0)));
    assert!(inner.arguments.is_empty());
    assert_eq!(outer.arguments, vec![Skeleton::Input(1)]);
    assert_eq!(inner.destination, ControlDestination::Deliver(outer.entry));
}

#[test]
fn a_discarded_invocation_keeps_its_result_and_control_destination() {
    let all = skeletons(
        "discarded_invocation.fz",
        "def discard(f, x) do\n f.(x)\n :ok\nend\n\
         def main(), do: discard(fn x -> x end, 1)\n",
    );
    let discarded = all.get("discard/2");
    assert_eq!(discarded.invocations.len(), 1);
    let invocation = discarded.invocations.values().next().unwrap();
    assert_eq!(invocation.callee, InvocationCallee::Value(Skeleton::Input(0)));
    assert_eq!(invocation.arguments, vec![Skeleton::Input(1)]);
    let ControlDestination::Deliver(successor) = invocation.destination else {
        panic!("the discarded call must still precede the literal suffix");
    };
    let Returns::Entries(returns) = &discarded.returns else {
        panic!("source body has return entries");
    };
    assert!(returns.contains_key(&successor));
    assert!(!returns.contains_key(&invocation.entry));
    let LoweredBody::Clauses { entries, .. } = discarded.body.as_deref().unwrap() else {
        panic!("the relation retains its source control graph");
    };
    assert_eq!(
        entries[invocation.entry.as_u32() as usize].tail.child_entries(),
        [successor],
        "the suffix is reached through the discarded call's completion edge"
    );
}

#[test]
fn source_operations_keep_computed_arguments_and_lambda_capture_producers() {
    let all = skeletons(
        "source_operations.fz",
        "def apply_not(f, x), do: f.(not x)\n\
         def wrap(f), do: fn x -> f.(x) end\n\
         def main() do\n apply_not(fn x -> x end, true)\n wrap(fn x -> x end)\nend\n",
    );
    let applied = all.get("apply_not/2");
    let body = applied
        .body
        .as_deref()
        .expect("a definition owns its source operations");
    let LoweredBody::Clauses { clauses, .. } = body else {
        panic!("apply_not has source clauses");
    };
    let call = applied.invocations.values().next().unwrap();
    let [Skeleton::Ground(argument)] = call.arguments.as_slice() else {
        panic!("the structural view addresses the computed argument by its result value");
    };
    let site = body.value_definition_site(*argument).unwrap();
    assert_eq!(
        body.step_at(site),
        &LoweredStep::UnaryOp {
            value: *argument,
            op: crate::ast::UnOp::Not,
            input: clauses[0].params[1],
        },
        "the address must retain its operation and connection to the input, before observing a type"
    );

    let wrapped = all.get("wrap/1");
    let body = wrapped.body.as_deref().unwrap();
    let LoweredBody::Clauses { clauses, .. } = body else {
        panic!("wrap has source clauses");
    };
    let Skeleton::Ground(result) = joined(wrapped) else {
        panic!("the returned lambda has a local construction position");
    };
    let LoweredStep::Lambda { function, captures, .. } = body.value_definition(result).unwrap() else {
        panic!("the returned value must retain its lambda construction");
    };
    assert_eq!(captures, &clauses[0].params);
    assert!(
        all.labels.contains_key(function),
        "the construction keeps its generated definition reference"
    );
}

#[test]
fn a_source_assertion_remains_a_prerequisite_without_defining_a_value() {
    let all = skeletons(
        "source_assertion.fz",
        "def same(first, second) do\n ^first = second\n :ok\nend\n\
         def main(), do: same(1, :other)\n",
    );
    let equation = all.get("same/2");
    let LoweredBody::Clauses { clauses, entries, .. } = equation.body.as_deref().unwrap() else {
        panic!("same has source clauses");
    };
    let entry = &entries[clauses[0].entry.as_u32() as usize];
    let assertion = entry
        .steps
        .iter()
        .position(|step| matches!(step, LoweredStep::AssertSame { .. }))
        .unwrap();
    let step = &entry.steps[assertion];
    assert_eq!(crate::compiler2::body::step_defined_values(step).count(), 0);
    let mut operands = Vec::new();
    crate::compiler2::body::step_used_values(step, &mut operands);
    assert_eq!(operands.len(), 2);
    assert!(clauses[0].params.iter().all(|input| operands.contains(input)));
    let suffix = entry
        .steps
        .iter()
        .position(|step| {
            matches!(step,
                LoweredStep::Const { literal: GroundValue::Atom(atom), .. } if atom == "ok"
            )
        })
        .unwrap();
    assert!(
        assertion < suffix,
        "the assertion must precede the literal even though no value depends on it"
    );
    assert!(matches!(
        entry.tail,
        LoweredTail::Value {
            dest: ControlDestination::Return,
            ..
        }
    ));
}

#[test]
fn source_destructuring_keeps_every_output_of_one_operation() {
    let all = skeletons(
        "source_destructuring.fz",
        "def list_parts(xs) do\n [head | tail] = xs\n {head, tail}\nend\n\
         def binary_parts(xs) do\n <<head, rest :: binary>> = xs\n {head, rest}\nend\n\
         def main() do\n list_parts([1, 2])\n binary_parts(<<1, 2>>)\nend\n",
    );
    for (label, output_count) in [("list_parts/1", 2), ("binary_parts/1", 3)] {
        let body = all.get(label).body.as_deref().unwrap();
        let LoweredBody::Clauses { clauses, entries, .. } = body else {
            panic!("destructuring has source clauses");
        };
        let operations = clauses
            .iter()
            .flat_map(|clause| &clause.projections)
            .chain(entries.iter().flat_map(|entry| &entry.steps))
            .filter(|step| {
                matches!(
                    (output_count, step),
                    (2, LoweredStep::SplitList { .. }) | (3, LoweredStep::BitstringRead { .. })
                )
            })
            .collect::<Vec<_>>();
        assert!(!operations.is_empty(), "{label} must exercise a multi-output operation");
        for operation in operations {
            let outputs = crate::compiler2::body::step_defined_values(operation).collect::<Vec<_>>();
            assert_eq!(outputs.len(), output_count);
            let site = body.value_definition_site(outputs[0]).unwrap();
            for output in outputs {
                assert_eq!(body.value_definition_site(output), Some(site));
                assert!(std::ptr::eq(body.value_definition(output).unwrap(), operation));
            }
        }
    }
}

/// Submits one source and requests its reachable definition facts without
/// requesting runtime activation analysis. Definition macros may execute
/// during lowering; the examined functions need no concrete call bindings.
fn skeletons(name: &str, source: &str) -> Skeletons {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some(name.to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let entry = compiler.root_function(root);
    let mut reached = vec![entry];
    let mut next = 0;
    let mut out = Skeletons::default();
    while next < reached.len() {
        let function = reached[next];
        next += 1;
        compiler.demand(Job::LowerFunction(function));
        compiler.demand(Job::DeriveStaticCallees(function));
        compiler.demand(Job::DeriveReturnSkeleton(function));
        compiler.drive();
        let world: &World = compiler.world();
        if !world.has_fact(&FactKey::LoweredBody(function)) || !world.has_fact(&FactKey::StaticCallees(function)) {
            continue;
        }
        let label = function_label(world, function);
        out.labels.insert(function, label.clone());
        out.by_label.insert(
            label,
            world
                .return_skeleton(function)
                .expect("a lowered definition publishes its source relationship")
                .as_ref()
                .clone(),
        );
        for callee in world.static_callees(function).iter().copied() {
            if !reached.contains(&callee) {
                reached.push(callee);
            }
        }
    }
    out
}

/// Every skeleton one source produced, beside the names its functions go by,
/// so a test can say which function a call site names without hard-coding an
/// id the lowering chose.
#[derive(Default)]
struct Skeletons {
    by_label: BTreeMap<String, FunctionSkeleton>,
    labels: HashMap<FunctionId, String>,
}

impl Skeletons {
    fn get(&self, label: &str) -> &FunctionSkeleton {
        self.by_label
            .get(label)
            .unwrap_or_else(|| panic!("expected a skeleton for {label}, have {:?}", self.by_label.keys()))
    }

    /// The function a call site of `caller` names, by label.
    fn callee(&self, caller: &FunctionSkeleton, callsite: CallSiteId) -> &str {
        let function = caller.invocations[&callsite]
            .callee
            .named()
            .unwrap_or_else(|| panic!("call site {callsite:?} names no callee"));
        self.labels
            .get(&function)
            .map(String::as_str)
            .unwrap_or_else(|| panic!("no label for {function:?}"))
    }
}

const WRAP_NEST: &str = "\
def nest([]), do: 0
def nest([_ | rest]), do: wrap(nest(rest))
def wrap(v), do: [v]

def main() do
  dbg(nest([1, 2]))
end
";

const REVERSE_NEST: &str = "\
def value([:open | rest]), do: array(rest, [])
def value([x | rest]), do: {:ok, x, rest}

def array([:close | rest], acc), do: {:ok, reverse(acc, []), rest}
def array(input, acc) do
  {:ok, v, rest} = value(input)
  array(rest, [v | acc])
end

def reverse([], out), do: out
def reverse([h | t], out), do: reverse(t, [h | out])

def main(), do: dbg(value([:open, 1, :open, 2, :close, :close]))
";

/// The shapes a body's returning control entries contribute, in entry
/// order. A declared return has no entries at all, so asking for them says
/// so rather than answering something else.
fn entry_shapes(skeleton: &FunctionSkeleton) -> Vec<Skeleton> {
    match &skeleton.returns {
        Returns::Entries(entries) => entries.values().cloned().collect(),
        Returns::Declared(ty) => panic!("expected walked entries, found a declared return {ty:?}"),
        Returns::Opaque => panic!("expected walked entries, found an opaque provider return"),
    }
}

/// Everything a function can hand back, as one join -- which is what an
/// activation that reaches every entry would see.
fn joined(skeleton: &FunctionSkeleton) -> Skeleton {
    entry_shapes(skeleton)
        .into_iter()
        .fold(Skeleton::Bottom, Skeleton::union)
}

/// Every alternative a skeleton joins, with a lone alternative counting as
/// its own one-element join.
fn branches(skeleton: &Skeleton) -> Vec<Skeleton> {
    match skeleton {
        Skeleton::Union(members) => members.clone(),
        other => vec![other.clone()],
    }
}

/// The one call-site result a skeleton names, for a test that wants to reach
/// through to that site's own arguments without hard-coding a call-site id.
fn sole_result(skeleton: &Skeleton) -> CallSiteId {
    let results: Vec<CallSiteId> = branches(skeleton)
        .iter()
        .filter_map(|branch| match branch {
            Skeleton::Result { callsite, .. } => Some(*callsite),
            _ => None,
        })
        .collect();
    assert_eq!(results.len(), 1, "expected exactly one call result in {skeleton:?}");
    results[0]
}

/// A clause that answers outright is an alternative like any other. `nest`
/// hands back either the `0` of its base clause or whatever its helper call
/// yields, and BOTH have to survive into the skeleton: a join that quietly
/// swallowed the base case would leave the recursive alternative standing
/// alone, and a solve reading it would never see where the recursion
/// bottoms out.
#[test]
fn a_base_clause_survives_the_join_beside_the_recursive_one() {
    let all = skeletons("wrap_nest.fz", WRAP_NEST);
    let nest = all.get("nest/1");
    let alternatives = branches(&joined(nest));
    assert_eq!(
        alternatives.len(),
        2,
        "nest returns exactly two alternatives, found {alternatives:?}",
    );
    assert!(
        alternatives.iter().any(|branch| matches!(branch, Skeleton::Ground(_))),
        "the base clause's own value is one of them: {alternatives:?}",
    );
    assert!(
        alternatives
            .iter()
            .any(|branch| matches!(branch, Skeleton::Result { .. })),
        "the helper call's result is the other: {alternatives:?}",
    );
}

/// The point of the skeleton: a helper that wraps what it is handed has a
/// return that GUARDS its own input slot, and that guard is visible with no
/// activation, no evidence and no key anywhere in sight.
#[test]
fn a_wrapping_helper_guards_its_own_slot() {
    let all = skeletons("wrap_nest.fz", WRAP_NEST);
    assert_eq!(
        joined(all.get("wrap/1")),
        Skeleton::List {
            element: Box::new(Skeleton::Input(0)),
            non_empty: true,
        },
        "wrap's return is a one-element list of its own slot 0",
    );
    assert!(
        all.get("wrap/1").invocations.is_empty(),
        "wrap calls nothing, so it hands no arguments to anyone",
    );
}

/// The recursive side of the same cycle: the argument `nest` hands its
/// helper is `nest`'s own recursive result, and the argument that recursive
/// call is handed is the tail of `nest`'s own input. Those two facts, with
/// `wrap`'s guard, are the whole cycle.
#[test]
fn a_recursive_return_names_the_call_that_produced_it() {
    let all = skeletons("wrap_nest.fz", WRAP_NEST);
    let nest = all.get("nest/1");
    let wrap_call = sole_result(&joined(nest));
    let inner = inner_call(nest, wrap_call);
    assert_eq!(
        nest.invocations.get(&wrap_call).map(|invocation| invocation
            .arguments
            .iter()
            .map(result_callsite)
            .collect::<Vec<_>>()),
        Some(vec![Some(inner)]),
        "the helper is handed the result of nest's own recursive call",
    );
    assert_eq!(
        nest.invocations.get(&inner).map(|call| call.arguments.as_slice()),
        Some([Skeleton::project(Skeleton::Input(0), ProjectStep::ListTail)].as_slice()),
        "the recursive call is handed the tail of nest's own slot 0",
    );
}

/// The call site a skeleton names, when what it stands for is a call result
/// at all.
fn result_callsite(skeleton: &Skeleton) -> Option<CallSiteId> {
    match skeleton {
        Skeleton::Result { callsite, .. } => Some(*callsite),
        _ => None,
    }
}

/// `nest`'s other call site: the one whose result the helper call consumes.
fn inner_call(nest: &FunctionSkeleton, wrap_call: CallSiteId) -> CallSiteId {
    let sites: Vec<CallSiteId> = nest
        .invocations
        .keys()
        .copied()
        .filter(|callsite| *callsite != wrap_call)
        .collect();
    assert_eq!(sites.len(), 1, "nest has exactly two call sites, found {sites:?}");
    sites[0]
}

/// The parser loop's shape, which is where the two halves of one returned
/// tuple part company: field 1 is built from a call still being solved and
/// field 2 is a projection of a slot that never moves.
#[test]
fn a_parser_tuple_separates_its_solved_field_from_its_carried_one() {
    let all = skeletons("reverse_nest.fz", REVERSE_NEST);
    let array = all.get("array/2");
    let returns = joined(array);
    let tuples: Vec<Skeleton> = branches(&returns)
        .into_iter()
        .filter(|branch| matches!(branch, Skeleton::Tuple(_)))
        .collect();
    assert_eq!(tuples.len(), 1, "array returns one tuple shape: {returns:?}");
    let Skeleton::Tuple(fields) = &tuples[0] else {
        unreachable!("filtered to tuples");
    };
    assert_eq!(fields.len(), 3, "the parser's answer is a three-field tuple");
    assert!(
        matches!(fields[1], Skeleton::Result { .. }),
        "field 1 is what the reverse call yields: {:?}",
        fields[1],
    );
    assert_eq!(
        fields[2],
        Skeleton::project(Skeleton::Input(0), ProjectStep::ListTail),
        "field 2 is the unconsumed rest of array's own input",
    );
}

/// A join is a set operation. One entry's shape is folded into the union
/// pairwise, and the same branch arrives again whenever a shape is rebuilt.
/// If each arrival appended another copy, a function's returns would grow
/// without bound while denoting exactly the same thing, and nothing reading
/// them could tell a genuinely new alternative from the same one counted
/// twice.
#[test]
fn joining_a_shape_with_something_it_already_names_changes_nothing() {
    let element = Skeleton::Ground(ValueId::from_u32(0));
    let listed = Skeleton::List {
        element: Box::new(element.clone()),
        non_empty: false,
    };

    assert_eq!(
        Skeleton::union(element.clone(), element.clone()),
        element,
        "joining a shape with itself is that shape",
    );
    let pair = Skeleton::union(element.clone(), listed.clone());
    assert_eq!(
        pair,
        Skeleton::Union(vec![element.clone(), listed.clone()]),
        "two distinct alternatives join into one flat list in the order they arrived",
    );
    assert_eq!(
        Skeleton::union(pair.clone(), element.clone()),
        pair,
        "a member the list already holds adds nothing",
    );
    assert_eq!(
        Skeleton::union(pair.clone(), listed),
        pair,
        "and neither does the other one",
    );
    assert_eq!(
        Skeleton::union(pair.clone(), pair.clone()),
        pair,
        "nor does the whole list joined with itself",
    );
    assert_eq!(
        Skeleton::union(Skeleton::Bottom, element.clone()),
        element,
        "bottom is the identity, and never wraps a lone member in a union",
    );
}

/// A guarded self call: the recursive alternative is a list built around the
/// call's own result, and the site it reads through names the function
/// itself. Nothing about this depends on an activation existing -- the shape
/// is the function's, and every activation of it reads the same one.
#[test]
fn a_guarded_self_call_is_named_under_the_constructor_that_guards_it() {
    let all = skeletons(
        "self_guarded_nest.fz",
        include_str!("../../fixtures2/behavior/self_guarded_nest.fz"),
    );
    let nest = all.get("nest/1");
    let alternatives = branches(&joined(nest));
    assert_eq!(alternatives.len(), 2, "nest/1 has two clauses: {alternatives:?}");
    assert!(
        matches!(alternatives[0], Skeleton::Ground(_)),
        "nest(0) -> 0 answers with a value of its own, no call involved: {:?}",
        alternatives[0],
    );
    let Skeleton::List { element, non_empty } = &alternatives[1] else {
        panic!("nest(n) -> [nest(n - 1)] builds a list: {:?}", alternatives[1]);
    };
    assert!(non_empty, "a flat literal is provably non-empty on its own");
    let Skeleton::Result { callsite, .. } = element.as_ref() else {
        panic!("the list's one element is the recursive call's result: {element:?}");
    };
    assert_eq!(
        all.callee(nest, *callsite),
        "nest/1",
        "the guarded call reads straight back through nest",
    );
}

/// Embedding a DIFFERENT function's result under a tuple is not a recursive
/// edge. The skeleton has to keep the two apart by the site each result
/// reads through, or a solver would fold `leaf`'s answer into `f`'s own
/// cycle and invent a recursion the program does not have.
#[test]
fn an_embedded_call_names_the_callee_it_actually_reads() {
    let all = skeletons(
        "false_embedding.fz",
        include_str!("../../fixtures2/behavior/false_embedding.fz"),
    );
    let f = all.get("f/1");
    let alternatives = branches(&joined(f));
    assert_eq!(alternatives.len(), 3, "f/1 has three clauses: {alternatives:?}");
    assert!(
        matches!(alternatives[0], Skeleton::Ground(_)),
        "f(0) -> 0 answers with a value of its own: {:?}",
        alternatives[0],
    );
    let Skeleton::Tuple(fields) = &alternatives[1] else {
        panic!("f(1) -> {{:ok, leaf(1)}} builds a tuple: {:?}", alternatives[1]);
    };
    assert_eq!(fields.len(), 2, "the tuple has two fields: {fields:?}");
    assert!(
        matches!(fields[0], Skeleton::Ground(_)),
        ":ok is a literal atom, no call involved: {:?}",
        fields[0],
    );
    let Skeleton::Result { callsite, .. } = &fields[1] else {
        panic!("field 1 is what the leaf call yields: {:?}", fields[1]);
    };
    assert_eq!(
        all.callee(f, *callsite),
        "leaf/1",
        "the embedded call reads through leaf, the callee it names",
    );
    let Skeleton::Result { callsite, .. } = &alternatives[2] else {
        panic!(
            "f(n) -> f(n - 1) hands back the call's own result: {:?}",
            alternatives[2]
        );
    };
    assert_eq!(all.callee(f, *callsite), "f/1", "the self call reads back through f",);
}

/// Mutual recursion is the same statement one step further out: `even`'s
/// recursive alternative reads through a site that names `odd`, so the cycle
/// is visible in the static shapes alone.
#[test]
fn a_mutual_call_names_its_partner() {
    let all = skeletons(
        "mutual_tuple_states.fz",
        include_str!("../../fixtures2/behavior/mutual_tuple_states.fz"),
    );
    let even = all.get("even/1");
    let alternatives = branches(&joined(even));
    assert_eq!(alternatives.len(), 2, "even/1 has two clauses: {alternatives:?}");
    let Skeleton::Tuple(base) = &alternatives[0] else {
        panic!("even([]) -> {{:even, 0}} builds a tuple: {:?}", alternatives[0]);
    };
    assert!(
        base.iter().all(|field| matches!(field, Skeleton::Ground(_))),
        "both of the base tuple's fields are literals: {base:?}",
    );
    let Skeleton::Tuple(step) = &alternatives[1] else {
        panic!("even([_ | t]) -> {{:e, odd(t)}} builds a tuple: {:?}", alternatives[1]);
    };
    assert_eq!(step.len(), 2, "the tuple has two fields: {step:?}");
    let Skeleton::Result { callsite, .. } = &step[1] else {
        panic!("field 1 is what the odd call yields: {:?}", step[1]);
    };
    assert_eq!(
        all.callee(even, *callsite),
        "odd/1",
        "the mutual call reads through odd, its actual callee",
    );
}

/// A tail call hands back its callee's result whole: there is no constructor
/// around it, so the alternative IS the call's result, and the accumulator a
/// base clause hands back is a slot the caller filled.
#[test]
fn a_tail_call_hands_back_its_callee_s_result_whole() {
    let all = skeletons(
        "alias_cycle_with_entry.fz",
        include_str!("../../fixtures2/behavior/alias_cycle_with_entry.fz"),
    );
    let cont = all.get("cont/2");
    let alternatives = branches(&joined(cont));
    assert_eq!(alternatives.len(), 2, "cont/2 has two clauses: {alternatives:?}");
    let Skeleton::Tuple(fields) = &alternatives[0] else {
        panic!("cont([], acc) -> {{:done, acc}} builds a tuple: {:?}", alternatives[0]);
    };
    assert_eq!(
        fields[1],
        Skeleton::Input(1),
        "acc is the slot the caller filled, not a call result: {:?}",
        fields[1],
    );
    let Skeleton::Result { callsite, .. } = &alternatives[1] else {
        panic!(
            "cont([h | t], acc) -> step(...) tail-calls step, so the whole clause is that \
             call's result: {:?}",
            alternatives[1]
        );
    };
    assert_eq!(
        all.callee(cont, *callsite),
        "step/2",
        "the tail call reads through step, its actual callee",
    );
}

/// A map update has no shape of its own: its result is a refinement of the
/// base's real type, not a fold over the base's shape. So the update clause
/// answers with its own value even though its base is a still-open recursive
/// call, and a solve never has to close that call to read this clause.
#[test]
fn a_map_update_answers_with_its_own_value() {
    let all = skeletons(
        "map_update_on_a_local.fz",
        "\
def f(0), do: %{count: 0}
def f(n), do: %{f(n - 1) | count: n}

def main() do
  dbg(f(2))
end
",
    );
    let f = all.get("f/1");
    let alternatives = branches(&joined(f));
    assert_eq!(alternatives.len(), 2, "f/1 has two clauses: {alternatives:?}");
    assert!(
        matches!(alternatives[1], Skeleton::Ground(_)),
        "the map update answers with its own value, independent of its still-open base: {:?}",
        alternatives[1],
    );
}
