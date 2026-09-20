//! What a function's static shape says before any activation exists.
//!
//! Every skeleton here is read off a body the ordinary lowering produced --
//! the source is submitted and driven until its bodies exist, exactly as the
//! compiler drives them -- so a shape asserted here is a shape keying will
//! actually see.

use std::collections::{BTreeMap, HashMap};

use super::*;
use crate::compiler2::canon::function_label;
use crate::compiler2::drive::{FactKey, Job};
use crate::compiler2::world::World;
use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

/// Submits one source and drives only far enough for every reachable body to
/// be lowered: no activation is ever analysed, so this harness answers the
/// static question with none of the fixpoint's machinery running.
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
        compiler.drive();
        let world: &World = compiler.world();
        if !world.has_fact(&FactKey::LoweredBody(function)) || !world.has_fact(&FactKey::StaticCallees(function)) {
            continue;
        }
        let label = function_label(world, function);
        out.labels.insert(function, label.clone());
        out.by_label
            .insert(label, lower(&world.lowered_body(function), world.types()));
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
        let (function, _) = caller
            .callees
            .get(&callsite)
            .unwrap_or_else(|| panic!("call site {callsite:?} names no callee"));
        self.labels
            .get(function)
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
        all.get("wrap/1").arguments.is_empty(),
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
        nest.arguments
            .get(&wrap_call)
            .map(|arguments| arguments.iter().map(result_callsite).collect::<Vec<_>>()),
        Some(vec![Some(inner)]),
        "the helper is handed the result of nest's own recursive call",
    );
    assert_eq!(
        nest.arguments.get(&inner).map(Vec::as_slice),
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
        .arguments
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
