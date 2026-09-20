//! Which positions the static skeletons say the fixpoint is still solving.
//!
//! Every answer here is read with no activation in existence: the source is
//! submitted and driven only far enough for its bodies to be lowered. That is
//! the point of the fact -- keying asks it in its first round, before there is
//! any evidence to read, so a test that had to analyse an activation first
//! would be testing something else.

use std::collections::BTreeMap;
use std::rc::Rc;

use super::*;
use crate::compiler2::canon::function_label;
use crate::compiler2::drive::{FactKey, Job};
use crate::compiler2::return_skeleton::{FunctionSkeleton, lower};
use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

/// Every reachable function's static unknowns, by canonical label.
fn unknowns(name: &str, source: &str) -> BTreeMap<String, FunctionUnknowns> {
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
    let mut skeletons: HashMap<FunctionId, Rc<FunctionSkeleton>> = HashMap::new();
    let mut labels = BTreeMap::new();
    while next < reached.len() {
        let function = reached[next];
        next += 1;
        compiler.demand(Job::LowerFunction(function));
        compiler.demand(Job::DeriveStaticCallees(function));
        compiler.drive();
        let world = compiler.world();
        if !world.has_fact(&FactKey::LoweredBody(function)) || !world.has_fact(&FactKey::StaticCallees(function)) {
            continue;
        }
        let skeleton = Rc::new(lower(&world.lowered_body(function)));
        labels.insert(function, function_label(world, function));
        skeletons.insert(function, skeleton);
        for callee in world.static_callees(function).iter().copied() {
            if !reached.contains(&callee) {
                reached.push(callee);
            }
        }
    }
    labels
        .into_iter()
        // No activation exists here, so no call made through a value has
        // resolved a target: this harness answers the part of the question
        // the bodies alone decide.
        .map(|(function, label)| (label, derive(&skeletons, function)))
        .collect()
}

const WRAP_NEST: &str = "\
def nest([]), do: 0
def nest([_ | rest]), do: wrap(nest(rest))
def wrap(v), do: [v]

def main() do
  dbg(nest([1, 2]))
end
";

const DISPATCH_INTO_UNKNOWN: &str = "\
def nest([]), do: 0
def nest([_ | rest]), do: step(nest(rest))

def step([h | _]), do: [[h]]
def step(n), do: [n]

def main(), do: dbg(nest([1, 2]))
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

fn of<'a>(all: &'a BTreeMap<String, FunctionUnknowns>, label: &str) -> &'a FunctionUnknowns {
    all.get(label)
        .unwrap_or_else(|| panic!("expected unknowns for {label}, have {:?}", all.keys()))
}

/// Every argument shape one function hands out, flattened, so a test can say
/// what a body passes without naming a call-site id.
fn argument_shapes(unknowns: &FunctionUnknowns) -> Vec<KeyShape> {
    unknowns
        .callsites
        .values()
        .flat_map(|site| site.arguments.iter())
        .cloned()
        .collect()
}

/// How many of a function's call sites yield a value the fixpoint is still
/// solving.
fn unsolved_results(unknowns: &FunctionUnknowns) -> usize {
    unknowns.callsites.values().filter(|site| site.result).count()
}

/// The heart of the whole arrangement: `nest` returns through a helper that
/// wraps what it is handed, so `nest`'s own return is a position being
/// solved and the argument it passes the helper is one too -- both decided
/// with no activation, no evidence and no key anywhere in sight.
#[test]
fn a_return_through_a_wrapping_helper_is_being_solved() {
    let all = unknowns("wrap_nest.fz", WRAP_NEST);
    assert!(of(&all, "nest/1").returns, "nest's return sits on a productive cycle");
    assert!(
        argument_shapes(of(&all, "nest/1")).contains(&KeyShape::Unknown),
        "nest hands the helper a value the fixpoint is still solving: {:?}",
        of(&all, "nest/1").callsites,
    );
}

/// The other half of the same answer: what `nest` hands ITSELF is the tail of
/// its own input, a value entirely fixed by what entered the cycle from
/// outside it. Keying that verbatim is ordinary specialization, and dispatch
/// needs it.
#[test]
fn a_tail_of_an_arriving_list_is_settled() {
    let all = unknowns("wrap_nest.fz", WRAP_NEST);
    let shapes = argument_shapes(of(&all, "nest/1"));
    assert!(
        shapes.contains(&KeyShape::Settled),
        "the recursive call's own argument is settled: {shapes:?}",
    );
    assert!(
        argument_shapes(of(&all, "main/0")).iter().all(KeyShape::is_settled),
        "a literal list handed in from outside is settled",
    );
}

/// A helper that DISPATCHES on the value it is handed is answered the same
/// way: what it is handed is still being solved, so it is keyed on its
/// address and the clause question is answered from the evidence instead.
#[test]
fn a_dispatching_helper_is_still_handed_an_unsolved_value() {
    let all = unknowns("dispatch_into_unknown.fz", DISPATCH_INTO_UNKNOWN);
    assert!(of(&all, "nest/1").returns, "nest's return sits on a productive cycle");
    assert!(
        argument_shapes(of(&all, "nest/1")).contains(&KeyShape::Unknown),
        "the dispatching helper is handed a value being solved: {:?}",
        of(&all, "nest/1").callsites,
    );
}

/// The parser loop, where one returned tuple carries both kinds at once: the
/// accumulator handed to `reverse` is being solved, while the token list
/// `array` hands its own recursive call is a projection of what arrived and
/// never moves.
#[test]
fn a_parser_separates_its_accumulator_from_its_input() {
    let all = unknowns("reverse_nest.fz", REVERSE_NEST);
    let array = of(&all, "array/2");
    assert!(array.returns, "array's return sits on a productive cycle");
    let shapes = argument_shapes(array);
    assert!(
        shapes.iter().any(|shape| !shape.is_settled()),
        "array hands on something being solved: {shapes:?}",
    );
    assert!(
        shapes.contains(&KeyShape::Settled),
        "array also hands on the token list it was given, which never moves: {shapes:?}",
    );
}

const RETURN_TUPLE_LADDER: &str = "\
def build(0), do: :start
def build(n), do: {n, build(n - 1)}

def main(), do: dbg(build(3))
";

const MUTUAL_TUPLE_STATES: &str = "\
def even([]), do: {:even, 0}
def even([_ | t]), do: {:e, odd(t)}

def odd([]), do: {:odd, 0}
def odd([_ | t]), do: {:o, even(t)}

def main(), do: dbg(even([1, 2]))
";

/// A call site yields as well as hands on, and both answers live in one
/// record because membership asks them as one question. `nest` hands its
/// helper a value being solved AND takes back a result being solved, so both
/// of its calls carry both marks.
#[test]
fn a_call_site_reports_what_it_yields_beside_what_it_hands_on() {
    let all = unknowns("wrap_nest.fz", WRAP_NEST);
    let nest = of(&all, "nest/1");
    assert!(
        nest.callsites.values().all(|site| site.result),
        "both of nest's calls yield a value on the productive cycle: {:?}",
        nest.callsites,
    );
}

/// The parser's accumulator is consed together out of a field of another
/// member's return, so the guard sits under a union inside the list. Every
/// call `array` makes is part of the one system: it yields `reverse`'s
/// return, `value`'s return and its own, and all three are being solved.
#[test]
fn a_guard_under_a_union_inside_a_constructor_still_names_the_system() {
    let all = unknowns("reverse_nest.fz", REVERSE_NEST);
    let array = of(&all, "array/2");
    assert_eq!(
        unsolved_results(array),
        array.callsites.len(),
        "every call array makes yields a value of the system being solved: {:?}",
        array.callsites,
    );
}

/// The case the argument side alone cannot see: `build` hands its recursive
/// call an arithmetic value, which is settled by construction, and the cycle
/// exists only because the tuple it wraps around the RESULT comes back as
/// its own return. Nothing about the argument says these solve together; the
/// result says it alone.
#[test]
fn a_cycle_that_runs_only_through_returns_is_named_by_the_result() {
    let all = unknowns("return_tuple_ladder.fz", RETURN_TUPLE_LADDER);
    let build = of(&all, "build/1");
    assert!(build.returns, "build's return sits on a productive cycle");
    assert!(
        argument_shapes(build).iter().all(KeyShape::is_settled),
        "every argument build hands on is ground arithmetic: {:?}",
        build.callsites,
    );
    assert_eq!(
        unsolved_results(build),
        1,
        "and exactly one of its calls -- the recursive one -- takes back a value \
         the fixpoint is still solving: {:?}",
        build.callsites,
    );
}

/// The same shape spread over two functions: `even` and `odd` hand each
/// other tails of their own input -- settled, and dispatch needs them keyed
/// verbatim -- while each wraps a tuple around what the other returns. Again
/// only the result names the system.
#[test]
fn mutually_recursive_returns_are_named_by_their_results_too() {
    let all = unknowns("mutual_tuple_states.fz", MUTUAL_TUPLE_STATES);
    let even = of(&all, "even/1");
    assert!(even.returns, "even's return sits on a productive cycle");
    assert_eq!(
        argument_shapes(even),
        vec![KeyShape::Settled],
        "the tail of an arriving list is settled",
    );
    assert_eq!(
        unsolved_results(even),
        1,
        "what odd yields at even's one call is being solved: {:?}",
        even.callsites,
    );
}

/// One constructor makes an edge guarded; a second one around it changes
/// nothing about that. `wrap` returns `{:ok, [v]}`, so the reference to `v`
/// sits two constructors deep, and the walk has to descend through the inner
/// list to find it. Stopping at the outer tuple loses the guard and the whole
/// cycle reads as a chain of aliases.
#[test]
fn a_guard_two_constructors_deep_is_still_a_guard() {
    let all = unknowns(
        "wrap_nest_nested_ctor.fz",
        include_str!("../../fixtures2/behavior/wrap_nest_nested_ctor.fz"),
    );
    let nest = of(&all, "nest/1");
    assert!(
        nest.returns,
        "nest's return is wrapped by a tuple around a list around itself: {:?}",
        nest.callsites,
    );
    let wrap = of(&all, "wrap/1");
    assert!(
        wrap.returns,
        "wrap is on the same productive cycle, through the value it is handed",
    );
}

/// A union inside a constructor is not another constructor: it is a choice
/// between what its alternatives denote, all held at the same place. So each
/// alternative is guarded by the constructor holding them, and a walk that
/// treats the union as an opaque value loses every one of them.
#[test]
fn a_guard_under_a_union_inside_a_constructor_holds_for_each_alternative() {
    let all = unknowns(
        "wrap_nest_union_field.fz",
        include_str!("../../fixtures2/behavior/wrap_nest_union_field.fz"),
    );
    let nest = of(&all, "nest/1");
    assert!(
        nest.returns,
        "one clause of wrap holds nest's value directly and the other holds it under a tag; \
         both are guarded, so nest's return is being solved: {:?}",
        nest.callsites,
    );
    let wrap = of(&all, "wrap/2");
    assert!(
        wrap.returns,
        "wrap is on the cycle it guards, whichever alternative it takes",
    );
}
