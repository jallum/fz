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
use crate::compiler2::body::{CallInputMode, CallSiteId, ControlEntryId, ValueId};
use crate::compiler2::canon::function_label;
use crate::compiler2::drive::{FactKey, Job};
use crate::compiler2::return_skeleton::{FunctionSkeleton, Returns, Skeleton, lower};
use crate::compiler2::types::Types;
use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

/// The static answers of one program, kept beside the skeletons they were
/// derived from so a test can also ask WHERE an argument lands.
struct Statics {
    skeletons: HashMap<FunctionId, Rc<FunctionSkeleton>>,
    labels: BTreeMap<FunctionId, String>,
    answers: BTreeMap<FunctionId, FunctionUnknowns>,
}

impl Statics {
    /// The keying answer given about one callee slot, one per call site that
    /// feeds it, in caller order: what coordinate each caller says the slot
    /// gets.
    fn feeding(&self, callee_label: &str, slot: usize) -> Vec<KeyShape> {
        self.feeds(callee_label, slot)
            .into_iter()
            .map(|(site, index)| site.destinations[index].clone())
            .collect()
    }

    /// What each of those call sites HANDS the slot, which is a different
    /// question: unknown-ness inside the one value that site writes.
    fn handing(&self, callee_label: &str, slot: usize) -> Vec<KeyShape> {
        self.feeds(callee_label, slot)
            .into_iter()
            .map(|(site, index)| site.arguments[index].clone())
            .collect()
    }

    /// Every call site feeding one callee slot, paired with the positional
    /// index that lands there, in caller order.
    fn feeds(&self, callee_label: &str, slot: usize) -> Vec<(&CallSiteUnknowns, usize)> {
        let callee = *self
            .labels
            .iter()
            .find(|(_, label)| *label == callee_label)
            .unwrap_or_else(|| panic!("expected a function labelled {callee_label}"))
            .0;
        let input_len = self.skeletons[&callee].input_len;
        let mut callers: Vec<FunctionId> = self.skeletons.keys().copied().collect();
        callers.sort_by_key(|function| function.as_u32());
        let mut feeds = Vec::new();
        for caller in callers {
            let skeleton = &self.skeletons[&caller];
            for (callsite, (named, mode)) in &skeleton.callees {
                if *named != callee {
                    continue;
                }
                let (Some(arguments), Some(site)) = (
                    skeleton.arguments.get(callsite),
                    self.answers[&caller].callsite(*callsite),
                ) else {
                    continue;
                };
                for index in 0..arguments.len() {
                    if mode.semantic_index(input_len, arguments.len(), index) == Some(slot) {
                        feeds.push((site, index));
                    }
                }
            }
        }
        feeds
    }
}

/// Every reachable function's static unknowns, by canonical label.
fn unknowns(name: &str, source: &str) -> BTreeMap<String, FunctionUnknowns> {
    let statics = statics(name, source);
    statics
        .labels
        .iter()
        .map(|(function, label)| (label.clone(), statics.answers[function].clone()))
        .collect()
}

/// Which skeletons one function's answer is derived from.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Universe {
    /// Every function the program defines, whoever can call it.
    WholeProgram,
    /// The function's own static callees, transitively -- what the job that
    /// publishes the fact hands `derive`. A cycle a position of this function
    /// sits on runs through calls this function makes, so it lies inside this
    /// reach; a cycle through a sibling CALLER of a shared helper does not,
    /// and this function is not on it.
    OwnReach,
}

fn statics(name: &str, source: &str) -> Statics {
    statics_over(name, source, Universe::WholeProgram)
}

/// The answers each function is given in a running compiler, where nothing it
/// cannot call is in its universe.
fn reached_statics(name: &str, source: &str) -> Statics {
    statics_over(name, source, Universe::OwnReach)
}

fn statics_over(name: &str, source: &str, universe: Universe) -> Statics {
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
        let skeleton = Rc::new(lower(&world.lowered_body(function), world.types()));
        labels.insert(function, function_label(world, function));
        skeletons.insert(function, skeleton);
        for callee in world.static_callees(function).iter().copied() {
            if !reached.contains(&callee) {
                reached.push(callee);
            }
        }
    }
    // No activation exists here, so no call made through a value has
    // resolved a target: this harness answers the part of the question the
    // bodies alone decide.
    let answers = labels
        .keys()
        .map(|function| {
            let within = match universe {
                Universe::WholeProgram => skeletons.clone(),
                Universe::OwnReach => reach(&skeletons, *function),
            };
            (*function, derive(&within, *function))
        })
        .collect();
    Statics {
        skeletons,
        labels,
        answers,
    }
}

/// The skeletons one function can reach through its own static callees,
/// transitively, itself among them.
fn reach(
    skeletons: &HashMap<FunctionId, Rc<FunctionSkeleton>>,
    function: FunctionId,
) -> HashMap<FunctionId, Rc<FunctionSkeleton>> {
    let mut reached = vec![function];
    let mut next = 0;
    let mut within = HashMap::new();
    while next < reached.len() {
        let reached_function = reached[next];
        next += 1;
        let Some(skeleton) = skeletons.get(&reached_function).cloned() else {
            continue;
        };
        for (callee, _) in skeleton.callees.values().copied() {
            if !reached.contains(&callee) {
                reached.push(callee);
            }
        }
        within.insert(reached_function, skeleton);
    }
    within
}

/// The generic missing-body question behind the protocol symptom. A missing
/// callee cannot prove that it discards the caller's input, whereas a known
/// body that returns a ground constant can. This evaluates conservative
/// missing-body flow independently of protocols.
#[test]
fn a_missing_static_callee_return_is_conservative_but_a_known_discard_is_not() {
    let caller = FunctionId::from_coordinate(11);
    let callee = FunctionId::from_coordinate(12);
    let callsite = CallSiteId::from_u32(30);
    let entry = ControlEntryId::from_u32(0);
    let caller_skeleton = FunctionSkeleton {
        returns: Returns::Entries(BTreeMap::from([(
            entry,
            Skeleton::Result {
                callsite,
                value: ValueId::from_u32(0),
            },
        )])),
        arguments: BTreeMap::from([(callsite, vec![Skeleton::Input(0)])]),
        callees: BTreeMap::from([(callsite, (callee, CallInputMode::Direct))]),
        input_len: 2,
    };
    let known_discard = FunctionSkeleton {
        returns: Returns::Entries(BTreeMap::from([(entry, Skeleton::Ground(ValueId::from_u32(1)))])),
        input_len: 1,
        ..FunctionSkeleton::default()
    };
    let known = HashMap::from([
        (caller, Rc::new(caller_skeleton.clone())),
        (callee, Rc::new(known_discard)),
    ]);
    assert!(
        !derive(&known, caller).returns_input(0),
        "a known constant-returning body proves the argument is not observable",
    );
    assert!(
        !derive(&known, caller).returns_input(1),
        "a caller input it never passes is not observable through a known discard",
    );

    let missing = HashMap::from([(caller, Rc::new(caller_skeleton))]);
    assert!(
        derive(&missing, caller).returns_input(0),
        "a missing static callee cannot prove that the caller's argument is unobservable",
    );
    assert!(
        !derive(&missing, caller).returns_input(1),
        "conservative missing-callee flow is limited to the argument actually passed",
    );
}

#[test]
fn opaque_return_may_flow_is_precise_and_not_a_known_empty_or_declared_return() {
    let caller = FunctionId::from_coordinate(31);
    let callee = FunctionId::from_coordinate(32);
    let callsite = CallSiteId::from_u32(50);
    let entry = ControlEntryId::from_u32(0);
    let caller_skeleton = FunctionSkeleton {
        returns: Returns::Entries(BTreeMap::from([(
            entry,
            Skeleton::Result {
                callsite,
                value: ValueId::from_u32(0),
            },
        )])),
        arguments: BTreeMap::from([(callsite, vec![Skeleton::Tuple(vec![Skeleton::Input(0)])])]),
        callees: BTreeMap::from([(callsite, (callee, CallInputMode::Direct))]),
        input_len: 2,
    };
    let opaque = FunctionSkeleton {
        returns: Returns::Opaque,
        input_len: 1,
        ..FunctionSkeleton::default()
    };
    let opaque_graph = HashMap::from([(caller, Rc::new(caller_skeleton.clone())), (callee, Rc::new(opaque))]);
    assert!(derive(&opaque_graph, callee).returns_input(0));
    let opaque_answer = derive(&opaque_graph, caller);
    assert!(opaque_answer.returns_input(0));
    assert!(
        !opaque_answer.returns_input(1),
        "opaque flow reaches only positions referenced by an actual argument"
    );

    let known_empty = FunctionSkeleton {
        returns: Returns::Entries(BTreeMap::new()),
        input_len: 1,
        ..FunctionSkeleton::default()
    };
    let empty_graph = HashMap::from([
        (caller, Rc::new(caller_skeleton.clone())),
        (callee, Rc::new(known_empty)),
    ]);
    assert!(!derive(&empty_graph, caller).returns_input(0));

    let mut types = Types::new();
    let declared = FunctionSkeleton {
        returns: Returns::Declared(types.int()),
        input_len: 1,
        ..FunctionSkeleton::default()
    };
    let declared_graph = HashMap::from([(caller, Rc::new(caller_skeleton)), (callee, Rc::new(declared))]);
    assert!(!derive(&declared_graph, caller).returns_input(0));
}

/// A broad `Input(0)` missing-body fallback is not a safe replacement for a
/// real return skeleton. On paper this is
/// `loop(0, acc) = acc; loop(n, acc) = loop(n - 1, [opaque(acc)])`, where
/// `opaque(_) = :fixed`. The real opaque return keeps the recursive
/// accumulator settled. Pretending it returns its input manufactures a
/// guarded cycle through `[opaque(acc)]` and changes the recursive call's
/// destination key to `List(Unknown)`.
#[test]
fn an_input_fallback_for_a_missing_body_can_manufacture_a_productive_cycle() {
    let loop_function = FunctionId::from_coordinate(21);
    let opaque = FunctionId::from_coordinate(22);
    let recurse = CallSiteId::from_u32(40);
    let opaque_call = CallSiteId::from_u32(41);
    let base_entry = ControlEntryId::from_u32(0);
    let recursive_entry = ControlEntryId::from_u32(1);
    let loop_skeleton = FunctionSkeleton {
        returns: Returns::Entries(BTreeMap::from([
            (base_entry, Skeleton::Input(1)),
            (
                recursive_entry,
                Skeleton::Result {
                    callsite: recurse,
                    value: ValueId::from_u32(0),
                },
            ),
        ])),
        arguments: BTreeMap::from([
            (
                recurse,
                vec![
                    Skeleton::Ground(ValueId::from_u32(1)),
                    Skeleton::List {
                        element: Box::new(Skeleton::Result {
                            callsite: opaque_call,
                            value: ValueId::from_u32(2),
                        }),
                        non_empty: true,
                    },
                ],
            ),
            (opaque_call, vec![Skeleton::Input(1)]),
        ]),
        callees: BTreeMap::from([
            (recurse, (loop_function, CallInputMode::Direct)),
            (opaque_call, (opaque, CallInputMode::Direct)),
        ]),
        input_len: 2,
    };
    let actual_constant = FunctionSkeleton {
        returns: Returns::Entries(BTreeMap::from([(base_entry, Skeleton::Ground(ValueId::from_u32(3)))])),
        input_len: 1,
        ..FunctionSkeleton::default()
    };
    let actual = HashMap::from([
        (loop_function, Rc::new(loop_skeleton.clone())),
        (opaque, Rc::new(actual_constant)),
    ]);
    assert_eq!(
        derive(&actual, loop_function)
            .callsite(recurse)
            .expect("recursive callsite is described")
            .destinations[1],
        KeyShape::Settled,
        "the actual constant return breaks the accumulator cycle",
    );

    let opaque_boundary = FunctionSkeleton {
        returns: Returns::Opaque,
        input_len: 1,
        ..FunctionSkeleton::default()
    };
    let opaque_graph = HashMap::from([
        (loop_function, Rc::new(loop_skeleton.clone())),
        (opaque, Rc::new(opaque_boundary)),
    ]);
    assert_eq!(
        derive(&opaque_graph, loop_function)
            .callsite(recurse)
            .expect("recursive callsite is described")
            .destinations[1],
        KeyShape::Settled,
        "opaque may-flow does not participate in the recursive constructor equation",
    );

    let input_fallback = FunctionSkeleton {
        returns: Returns::Entries(BTreeMap::from([(base_entry, Skeleton::Input(0))])),
        input_len: 1,
        ..FunctionSkeleton::default()
    };
    let fabricated = HashMap::from([
        (loop_function, Rc::new(loop_skeleton)),
        (opaque, Rc::new(input_fallback)),
    ]);
    assert_eq!(
        derive(&fabricated, loop_function)
            .callsite(recurse)
            .expect("recursive callsite is described")
            .destinations[1],
        KeyShape::List(Box::new(KeyShape::Unknown)),
        "an input fallback would invent a productive list cycle the actual opaque body does not have",
    );
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

/// The parser loop, where one returned tuple carries both kinds at once. The
/// accumulator keeps its LIST structure -- only the value consed into it is
/// still being solved, so it keys as a list of the variable at its element
/// address -- while the token list threaded round the loop is a position of
/// the whole system and is addressed entire. Separating those two is what
/// keeps a `[h | t]` question answerable while the values inside climb.
#[test]
fn a_parser_separates_its_accumulator_from_its_input() {
    let statics = statics("reverse_nest.fz", REVERSE_NEST);
    let all = unknowns("reverse_nest.fz", REVERSE_NEST);
    let array = of(&all, "array/2");
    assert!(array.returns, "array's return sits on a productive cycle");
    let shapes = argument_shapes(array);
    assert!(
        shapes.iter().any(|shape| !shape.is_settled()),
        "array hands on something being solved: {shapes:?}",
    );
    assert_eq!(
        statics.feeding("array/2", 1),
        vec![KeyShape::List(Box::new(KeyShape::Unknown)); 2],
        "the accumulator keeps the structure the skeleton exposes, and the seed call \
         that starts it says so as loudly as the ascent call that grows it",
    );
    assert_eq!(
        statics.feeding("array/2", 0),
        vec![KeyShape::Unknown; 2],
        "while the token list is a position of the system and is addressed whole",
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

const SEEDED_ACCUMULATOR: &str = "\
def build([], acc), do: acc
def build([h | t], acc), do: build(t, [h | acc])

def main(), do: dbg(build([1, 2], []))
";

const WRAPPED_RECURSIVE_SCALAR: &str = "\
def wrap(v), do: {v}

def dup(0), do: 0
def dup(n), do: wrap(dup(n - 1))

def main(), do: dbg(dup(1))
";

/// Two chains through one shared helper. `climb` hands `hold` the
/// accumulator it grows by consing -- a value still climbing -- but nothing
/// `climb` reaches sends `hold`'s return back into `hold`'s slot. `loopy`
/// does: what it hands `hold` is a list built around `hold`'s own result, so
/// `hold`'s slot sits on a cycle that crosses that constructor.
const SHARED_HELPER_ONE_CYCLE: &str = "\
def hold(v), do: v

def climb([], acc), do: hold(acc)
def climb([h | t], acc), do: climb(t, [h | acc])

def loopy([]), do: []
def loopy(l), do: loopy([hold(l)])

def main() do
  dbg(climb([1, 2], []))
  dbg(loopy([3]))
end
";

/// A slot keys on its own cycle, not on its argument's. The address variable
/// a slot is named by is ONE coordinate shared by every caller in the
/// program, so answering it from a climbing ARGUMENT merges chains that have
/// no cycle in common: `climb`'s integers and `loopy`'s list would become one
/// activation of `hold` whose input is the union of both, and every consumer
/// downstream of either chain would be handed the other's type.
///
/// So the two questions come apart here, and both answers are read at once:
/// `climb` HANDS `hold` a value the fixpoint is still solving, and still says
/// the slot it lands in is settled, because the only cycle `climb` reaches
/// through that value is its own accumulator's -- `hold` reads it and hands
/// it back, never round again. `loopy` reaches a cycle through the slot
/// itself and names it by its address.
#[test]
fn a_slot_keys_on_its_own_cycle_not_on_the_climb_that_reaches_it() {
    let statics = reached_statics("shared_helper_one_cycle.fz", SHARED_HELPER_ONE_CYCLE);
    assert_eq!(
        statics.handing("hold/1", 0),
        vec![KeyShape::Unknown, KeyShape::Unknown],
        "both callers hand hold a value the fixpoint is still solving: climb's accumulator \
         and the list loopy builds around hold's own result",
    );
    assert_eq!(
        statics.feeding("hold/1", 0),
        vec![KeyShape::Settled, KeyShape::Unknown],
        "but only loopy's walk reaches a cycle through the slot, so only loopy names it by \
         its address; climb keys on the integers it observed there",
    );
}

/// One slot gets one coordinate rule. `main` seeds the accumulator with `[]`
/// and `build` grows it with `[h | acc]`; both land in slot 1, so if the two
/// call sites answered differently the seed would key apart from every round
/// after it and the ascent would be back. The agreement is what makes an
/// answer written per call site still a fact about the slot.
#[test]
fn every_call_site_that_feeds_one_slot_names_it_the_same_way() {
    let statics = statics("seeded_accumulator.fz", SEEDED_ACCUMULATOR);
    let shapes = statics.feeding("build/2", 1);
    assert_eq!(
        shapes.len(),
        2,
        "the seed call and the ascent call both feed the accumulator: {shapes:?}",
    );
    assert!(
        shapes.iter().all(|shape| *shape == shapes[0]),
        "a seed handing `[]` and an ascent handing `[h | acc]` name one position, \
         so they have to name it the same way: {shapes:?}",
    );
    assert_eq!(
        shapes[0],
        KeyShape::List(Box::new(KeyShape::Unknown)),
        "and what they name it is what the skeleton exposes: a list whose element the \
         fixpoint is still solving, which keys the seed's `[]` and every later round alike",
    );
}

/// The same rule where the input never moves: `build`'s own token list is a
/// projection of what arrived and `main` hands it a literal, so slot 0 is
/// settled at both call sites and keeps its ordinary specialization.
#[test]
fn a_slot_nothing_is_solving_stays_settled_at_every_call_site() {
    let statics = statics("seeded_accumulator.fz", SEEDED_ACCUMULATOR);
    let shapes = statics.feeding("build/2", 0);
    assert_eq!(
        shapes,
        vec![KeyShape::Settled, KeyShape::Settled],
        "the arriving list and the tail read out of it are both fixed by what entered \
         the cycle from outside it",
    );
}

/// `wrap` reaches nothing at all, so nothing in its own skeletons can say
/// that the only value it is ever handed is a recursive result still
/// climbing. `dup` can say it, and does: the answer belongs to the caller
/// that writes the argument.
#[test]
fn a_caller_answers_for_the_climbing_value_it_hands_a_wrapper() {
    let statics = statics("wrapped_recursive_return_scalar.fz", WRAPPED_RECURSIVE_SCALAR);
    assert_eq!(
        statics.feeding("wrap/1", 0),
        vec![KeyShape::Unknown],
        "dup hands wrap its own recursive result, which the fixpoint is still solving",
    );
    assert_eq!(
        statics.feeding("dup/1", 0),
        vec![KeyShape::Settled, KeyShape::Settled],
        "while the counter handed to dup -- a literal from main, arithmetic from dup -- \
         is settled at both call sites",
    );
}

/// A `CallSiteId` carries the span it was lowered from, and a span names the
/// source VERSION it came from. Re-submitting byte-identical text mints ids
/// that differ from the ones this answer was derived with, so an answer
/// looked up by the whole id would miss every site and every argument would
/// key as it arrived -- one activation per rung of an ascent, from nothing
/// but a re-submission. A call site is where it sits in its body, and the
/// answer is already about one body, so that is what identifies it.
#[test]
fn a_call_site_is_found_by_where_it_sits_not_by_the_source_it_came_from() {
    let statics = statics("wrapped_recursive_return_scalar.fz", WRAPPED_RECURSIVE_SCALAR);
    let dup = *statics
        .labels
        .iter()
        .find(|(_, label)| *label == "dup/1")
        .expect("dup/1 is reachable")
        .0;
    let lowered: Vec<CallSiteId> = statics.skeletons[&dup].arguments.keys().copied().collect();
    assert!(!lowered.is_empty(), "dup/1 calls wrap and itself");
    for callsite in lowered {
        let from_another_version = CallSiteId::new(callsite.as_u32(), crate::source::Span::DUMMY);
        assert_ne!(
            from_another_version, callsite,
            "the two ids differ, which is exactly the condition this guards",
        );
        assert_eq!(
            statics.answers[&dup].callsite(from_another_version),
            statics.answers[&dup].callsite(callsite),
            "and they name the same call, so they must find the same answer",
        );
    }
}
