//! What a function's static shape says before any activation exists.
//!
//! Every skeleton here is read off a body the ordinary lowering produced --
//! the source is submitted and driven until its bodies exist, exactly as the
//! compiler drives them -- so a shape asserted here is a shape keying will
//! actually see.

use std::collections::BTreeMap;

use super::*;
use crate::compiler2::canon::function_label;
use crate::compiler2::drive::{FactKey, Job};
use crate::compiler2::world::World;
use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

/// Submits one source and drives only far enough for every reachable body to
/// be lowered: no activation is ever analysed, so this harness answers the
/// static question with none of the fixpoint's machinery running.
fn skeletons(name: &str, source: &str) -> BTreeMap<String, FunctionSkeleton> {
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
    let mut out = BTreeMap::new();
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
        out.insert(function_label(world, function), lower(&world.lowered_body(function)));
        for callee in world.static_callees(function).iter().copied() {
            if !reached.contains(&callee) {
                reached.push(callee);
            }
        }
    }
    out
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

fn skeleton_of<'a>(all: &'a BTreeMap<String, FunctionSkeleton>, label: &str) -> &'a FunctionSkeleton {
    all.get(label)
        .unwrap_or_else(|| panic!("expected a skeleton for {label}, have {:?}", all.keys()))
}

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
    let nest = skeleton_of(&all, "nest/1");
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
        joined(skeleton_of(&all, "wrap/1")),
        Skeleton::List {
            element: Box::new(Skeleton::Input(0)),
            non_empty: true,
        },
        "wrap's return is a one-element list of its own slot 0",
    );
    assert!(
        skeleton_of(&all, "wrap/1").arguments.is_empty(),
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
    let nest = skeleton_of(&all, "nest/1");
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
    let array = skeleton_of(&all, "array/2");
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
