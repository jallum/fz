//! `SolveReturnComponent` exercised end to end, through the same production
//! drive every door pulls a program through -- `Compiler2::submit_code` /
//! `submit_root` / `drive_root_to_dump_stage(.., DumpStage::Backend)`, the
//! exact path `drive_test.rs`'s `RETURN_LADDERS` acceptance measurements use.
//!
//! The lighter `World`-level `ExecutionContext::drive` (the semantic-only
//! pass `jobs/semantic_test.rs` drives) never issues a genuine `wait` on a
//! component member's `ReturnType` -- every external reference to another
//! activation's `ReturnType` is a non-blocking `read`, by design, so nothing
//! in that pass alone ever pulls `SolveReturnComponent` into existence. Only
//! the backend/codegen product drive issues real waits on member return
//! types, so this is the harness that actually exercises the solver.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::*;
use crate::compiler2::dump::DumpStage;
use crate::compiler2::identity::ModuleId;
use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, FunctionId, RootId, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

/// The set of activations one `drive_fixture` telemetry hook accumulates --
/// shared shape for both the settled-`ReturnType` and the ever-analyzed hook.
type ActivationKeySet = Rc<RefCell<HashSet<ActivationKey>>>;

/// Drives one fixture to its backend product, the way every door does, while
/// recording every `ActivationKey` a `ReturnType` was ever defined for (the
/// analysis-order companion set every non-degenerate test below reads) and
/// every `ActivationKey` compiler2 ever analyzed (fires for every activation
/// `AnalyzeActivation` walks, whether or not its `ReturnType` ever settles --
/// a strict superset, the one way to find a bottom activation's own key).
fn drive_fixture(name: &str, source: &str) -> (Compiler2<ConfiguredTelemetry>, ActivationKeySet, ActivationKeySet) {
    let tel = ConfiguredTelemetry::new();
    let settled: Rc<RefCell<HashSet<ActivationKey>>> = Rc::new(RefCell::new(HashSet::new()));
    let settled_sink = Rc::clone(&settled);
    tel.attach_raw_event2::<World, ActivationKey, _>(
        &["fz", "compiler2", "return_type", "defined"],
        move |_, _, _, _, activation| {
            settled_sink.borrow_mut().insert(activation.clone());
        },
    );
    let analyzed: Rc<RefCell<HashSet<ActivationKey>>> = Rc::new(RefCell::new(HashSet::new()));
    let analyzed_sink = Rc::clone(&analyzed);
    tel.attach_raw_event2::<World, ActivationKey, _>(
        &["fz", "compiler2", "activation_analysis", "defined"],
        move |_, _, _, _, activation| {
            analyzed_sink.borrow_mut().insert(activation.clone());
        },
    );

    let mut compiler = Compiler2::new(tel);
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
    compiler
        .drive_root_to_dump_stage(root, DumpStage::Backend)
        .unwrap_or_else(|error| panic!("{name} should reach a backend program: {error}"));
    (compiler, settled, analyzed)
}

/// The one `ActivationKey` a function's own calls collapsed to, out of a set
/// of activations the caller has already picked -- every settled key, to
/// find the sole key a recursive function's calls share.
fn sole_activation(seen: &HashSet<ActivationKey>, function: FunctionId, label: &str) -> ActivationKey {
    let matches: Vec<&ActivationKey> = seen.iter().filter(|key| key.function == function).collect();
    assert_eq!(
        matches.len(),
        1,
        "{label} should collapse to exactly one shared activation across its recursive calls, found {matches:?}",
    );
    matches[0].clone()
}

/// Every settled activation of `function` whose component includes
/// `partner`, in semantic order.
///
/// A function specialized on more than one input shape settles more than one
/// `ActivationKey`, and each of them joins the system it hands an unsolved
/// argument to -- membership is a connected component of that relation, not
/// a question of which specialization the cycle reaches back into.
fn cycle_partner_activations(
    world: &mut World,
    seen: &HashSet<ActivationKey>,
    function: FunctionId,
    partner: &ActivationKey,
    label: &str,
) -> Vec<ActivationKey> {
    let mut matches: Vec<ActivationKey> = seen
        .iter()
        .filter(|key| key.function == function)
        .filter(|key| {
            world
                .return_component(key)
                .is_some_and(|component| component.members.contains(partner))
        })
        .cloned()
        .collect();
    assert!(
        !matches.is_empty(),
        "{label} should share a component with its cycle partner",
    );
    let types = world.types();
    matches.sort_by(|left, right| left.semantic_cmp(right, types));
    matches
}

/// A self call closed through a resolved value (`f.(f, n - 1)`, `f` bound to
/// `&loop/2`) with NOTHING built across it.
///
/// Every edge on that cycle is a bare alias, so the return is the plain
/// union of what the branches contribute and the ordinary join names it.
/// Only a cycle with a constructor across it -- the `value_call_guarded`
/// witness below -- needs a component solve, and asking for one here would
/// be work with no question behind it.
#[test]
fn a_bare_value_call_cycle_needs_no_component() {
    let (mut compiler, settled, _analyzed) = drive_fixture(
        "value_call_self_cycle.fz",
        include_str!("../../../fixtures2/behavior/value_call_self_cycle.fz"),
    );
    let world = compiler.world_mut();

    let loop_fn = world.reference_function(ModuleId::GLOBAL, "loop", 2);
    let activation = sole_activation(&settled.borrow(), loop_fn, "loop/2");

    assert!(
        world.return_component(&activation).is_none(),
        "loop/2's cycle carries nothing across it, so its return is an ordinary union, not a system to solve",
    );
    let returned = world.activation_return(&activation).expect("loop/2 returns");
    assert_eq!(
        world.types().display(&returned),
        ":done",
        "the only branch that contributes anything is the base case",
    );
}

/// `cont/2` and `step/2` alias each other with no base case of their own
/// (`enter/1` supplies the only entry, from outside the cycle). Both
/// directions of the query must agree on the same component -- the owner is
/// the canonical first member in semantic order, not whichever activation
/// happened to ask.
///
/// `cont/2` settles two specializations, `enter/1`'s own entry call
/// `cont(xs, [])` and the general recursive call `cont(t, {:cont, acc})`.
/// Both hand `step/2` the accumulator the fixpoint is still solving, so both
/// are in the one system: membership is the connected component of that
/// relation, and handing on an unsolved value joins it whether or not the
/// cycle ever reaches back. `enter/1` hands on `[]`, which is settled, so it
/// stays outside.
#[test]
fn alias_cycle_component_is_canonical_under_member_permutation() {
    let (mut compiler, settled, _analyzed) = drive_fixture(
        "alias_cycle_with_entry.fz",
        include_str!("../../../fixtures2/behavior/alias_cycle_with_entry.fz"),
    );
    let world = compiler.world_mut();

    let enter_fn = world.reference_function(ModuleId::GLOBAL, "enter", 1);
    let cont_fn = world.reference_function(ModuleId::GLOBAL, "cont", 2);
    let step_fn = world.reference_function(ModuleId::GLOBAL, "step", 2);
    let enter_activation = sole_activation(&settled.borrow(), enter_fn, "enter/1");
    let step_activation = sole_activation(&settled.borrow(), step_fn, "step/2");
    let cont_activations = {
        let seen = settled.borrow().clone();
        cycle_partner_activations(world, &seen, cont_fn, &step_activation, "cont/2")
    };
    let settled_cont: Vec<ActivationKey> = settled
        .borrow()
        .iter()
        .filter(|key| key.function == cont_fn)
        .cloned()
        .collect();
    assert_eq!(
        cont_activations.len(),
        settled_cont.len(),
        "every cont/2 specialization hands step/2 the accumulator the fixpoint is still solving, so every one of them \
         is in the system: {settled_cont:?}",
    );
    let cont_activation = cont_activations[0].clone();

    let from_cont = world
        .return_component(&cont_activation)
        .expect("cont/2 reaches step/2 and back, a genuine mutual cycle");
    let from_step = world
        .return_component(&step_activation)
        .expect("step/2 reaches cont/2 and back, the same cycle queried from its other member");
    assert_eq!(
        from_cont.owner, from_step.owner,
        "the same component must name the same canonical owner from either member",
    );
    assert_eq!(
        from_cont.members, from_step.members,
        "the same component must list the same members in the same order from either member",
    );
    assert_eq!(
        from_cont.members.len(),
        cont_activations.len() + 1,
        "the system is every cont/2 specialization plus step/2, and nothing else: {:?}",
        from_cont.members,
    );
    assert!(
        from_cont.members.contains(&cont_activation),
        "cont/2 must be a member of its own cycle"
    );
    assert!(
        from_cont.members.contains(&step_activation),
        "step/2 must be a member of the cycle it aliases with"
    );

    assert!(
        world.return_component(&enter_activation).is_none(),
        "enter/1 reaches into the cycle but nothing in the cycle reaches back to enter/1, so it owns its own return",
    );
}

/// `f/1` tail-calls itself and, on one clause only, embeds `leaf/1`'s result
/// under a tuple with no recursive edge of its own there.
///
/// Nothing is built across `f/1`'s own cycle -- the tuple is built around
/// `leaf/1`, which never calls back -- so `f/1` needs no solve at all, while
/// `leaf/1` builds a list around itself and is a system of one. Naming them
/// apart is what keeps `f/1`'s answer a type that MENTIONS `leaf/1`'s type
/// rather than a false recursion in `f/1` itself.
#[test]
fn false_embedding_solves_leaf_1_alone() {
    let (mut compiler, settled, _analyzed) = drive_fixture(
        "false_embedding.fz",
        include_str!("../../../fixtures2/behavior/false_embedding.fz"),
    );
    let world = compiler.world_mut();

    let f_fn = world.reference_function(ModuleId::GLOBAL, "f", 1);
    let leaf_fn = world.reference_function(ModuleId::GLOBAL, "leaf", 1);
    let f_activation = sole_activation(&settled.borrow(), f_fn, "f/1");
    let leaf_activation = sole_activation(&settled.borrow(), leaf_fn, "leaf/1");

    assert!(
        world.return_component(&f_activation).is_none(),
        "f/1's cycle is a bare tail call with nothing built across it, so its return is an ordinary union",
    );
    let leaf_component = world
        .return_component(&leaf_activation)
        .expect("leaf/1 builds a list of itself, a self edge");
    assert_eq!(
        leaf_component.members,
        vec![leaf_activation.clone()],
        "leaf/1's self cycle is its own component, separate from f/1's: {:?}",
        leaf_component.members,
    );

    let leaf_ty = world
        .activation_return(&leaf_activation)
        .expect("leaf/1 has a base case (leaf(0) -> 0), so it publishes a type");
    let f_ty = world
        .activation_return(&f_activation)
        .expect("f/1 has a base case (f(0) -> 0), so it publishes a type");

    let types = world.types_mut();
    let int_ty = types.int();
    let ok_ty = types.atom_lit("ok");
    let ok_tuple = types.tuple(&[ok_ty, leaf_ty]);
    let expected = types.union(int_ty, ok_tuple);
    assert!(
        world.types().is_equivalent(&f_ty, &expected),
        "f/1 must be exactly `int | {{:ok, leaf_ty}}`, naming leaf/1's own solved type as a value, \
         never a type recursive in f/1 itself",
    );
}

/// `a` and `b` alternate wrapping each other's result in `{:wrap, ...}`
/// forever, with no base case on either side -- the shape source text cannot
/// reach without diverging at runtime (any live call genuinely loops
/// forever), so this exercises [`solve`] directly, the same algorithm
/// `solve_return_component` calls after binding a real component's static
/// skeletons to what its members' walks observed. Every branch is guarded
/// (a real, flattened branch, unlike a bare unguarded alias), so this is not
/// the no-evidence bottom case (`unproductive_spin`'s shape, source-level
/// tested in `fixtures2/behavior/unproductive_spin.fz`): each branch names a
/// member, and that member's own branches all fail to contribute in turn, so
/// the least fixed point is the empty type -- a real, computed `none`,
/// published as a fact for every member, never the absence of one.
#[test]
fn productive_cycle_with_no_base_case_publishes_none() {
    let mut types = Types::new();
    let wrap_tag = types.atom_lit("wrap");

    let a = ActivationKey::from_inputs(RootId::for_test(0), FunctionId::from_coordinate(0), &[], &mut types);
    let b = ActivationKey::from_inputs(RootId::for_test(0), FunctionId::from_coordinate(1), &[], &mut types);
    let members = vec![a.clone(), b.clone()];
    let member_set: HashSet<ActivationKey> = members.iter().cloned().collect();

    // Each member's static shape: `{tag, <what my one call yields>}`. The
    // tag is a ground value, answered by what the walk observed at it; the
    // call is answered by the activation its call site addressed.
    let tag = ValueId::from_u32(0);
    let result = ValueId::from_u32(1);
    let callsite = CallSiteId::from_u32(0);
    let wrapping = |activation: &ActivationKey| {
        Term::Shape(
            activation.clone(),
            Skeleton::Tuple(vec![
                Skeleton::Ground(tag),
                Skeleton::Result {
                    callsite,
                    value: result,
                },
            ]),
        )
    };
    let bindings = Bindings {
        value_types: HashMap::from([
            (a.clone(), HashMap::from([(tag, wrap_tag)])),
            (b.clone(), HashMap::from([(tag, wrap_tag)])),
        ]),
        results: HashMap::from([
            ((a.clone(), callsite), vec![Term::Return(b.clone())]),
            ((b.clone(), callsite), vec![Term::Return(a.clone())]),
        ]),
        returns: HashMap::from([(a.clone(), vec![wrapping(&a)]), (b.clone(), vec![wrapping(&b)])]),
        ..Bindings::default()
    };

    let solved = solve(&members, &member_set, &bindings, &[], &mut types);

    assert_eq!(
        solved.returns.len(),
        2,
        "both a and b publish a fact, not just one: {solved:?}"
    );
    let a_ty = solved
        .returns
        .get(&a)
        .expect("a's productive cycle with no base case still publishes a fact, the empty type, not bottom");
    let b_ty = solved
        .returns
        .get(&b)
        .expect("b publishes the same computed emptiness as its cycle partner");
    assert!(
        types.is_empty(a_ty),
        "a's least fixed point is the empty type: no value ever reaches a base case"
    );
    assert!(
        types.is_empty(b_ty),
        "b's least fixed point is the empty type: no value ever reaches a base case"
    );
}

/// `spin/1` calls itself with no other branch at all -- a bare, unguarded
/// self-reference. Nothing is built across the cycle and no branch
/// contributes anything, so there is no unknown to name: no evidence, not
/// even a computed empty type. The call sits behind a statically dead
/// `if false`, so nothing ever demands its `ReturnType`, but
/// `AnalyzeActivation` still walks it (it is a real function in the call
/// graph), so its key exists and its component can still be queried
/// directly.
#[test]
fn local_only_recursion_with_no_productive_branch_stays_bottom() {
    let (mut compiler, settled, analyzed) = drive_fixture(
        "unproductive_spin.fz",
        include_str!("../../../fixtures2/behavior/unproductive_spin.fz"),
    );
    let world = compiler.world_mut();

    let spin_fn = world.reference_function(ModuleId::GLOBAL, "spin", 1);
    let spin_activation = sole_activation(&analyzed.borrow(), spin_fn, "spin/1");

    assert!(
        !settled.borrow().contains(&spin_activation),
        "spin/1's ReturnType must never settle: nothing in the dead branch ever demands it",
    );
    assert!(
        world.activation_return(&spin_activation).is_none(),
        "a local-only self cycle with no other branch has no evidence at all, not even a computed empty type",
    );
    assert!(
        world.return_component(&spin_activation).is_none(),
        "a cycle with nothing built across it is not an unknown, so no solve is asked for one that would answer nothing",
    );
}

/// `Enum.reverse([1])` is the stdlib witness named in the proposal: it drives
/// `List.reduce`'s protocol dispatch into the mutually recursive
/// `reduce_cont`/`reduce_step` pair (see `lib/list.fz`), with the entry call
/// from `List.reduce` itself sitting outside the cycle -- the same
/// entry-outside-the-loop shape as `enter/1` in `alias_cycle_with_entry.fz`.
///
/// `reduce_cont/3` specializes on more than one accumulator shape, and each
/// specialization hands the pair the accumulator the fixpoint is still
/// solving, so each is in the one system -- the same rule
/// `alias_cycle_component_is_canonical_under_member_permutation` states. The
/// reducer lambda is in it too: `reducer.(head, acc)` hands it that same
/// accumulator, and it is what BUILDS the next one, so the system that names
/// the accumulator's type cannot be drawn without it.
#[test]
#[ignore = "red-worklist: triage + re-enable"]
fn enum_reverse_drives_list_reduce_cont_step_into_one_component() {
    let (mut compiler, settled, _analyzed) = drive_fixture(
        "enum_reverse_reduce_cycle.fz",
        include_str!("../../../fixtures2/behavior/enum_reverse_reduce_cycle.fz"),
    );
    let world = compiler.world_mut();

    let list_module = world.reference_module(crate::modules::identity::ModuleName::parse_dotted("List").unwrap());
    let reduce_cont_fn = world.reference_function(list_module, "reduce_cont", 3);
    let reduce_step_fn = world.reference_function(list_module, "reduce_step", 3);

    let step_activation = sole_activation(&settled.borrow(), reduce_step_fn, "reduce_step/3");
    let cont_activations = {
        let seen = settled.borrow().clone();
        cycle_partner_activations(world, &seen, reduce_cont_fn, &step_activation, "reduce_cont/3")
    };
    let cont_activation = cont_activations[0].clone();

    let component = world
        .return_component(&cont_activation)
        .expect("reduce_cont/reduce_step form a component together");
    let mut member_labels: Vec<String> = component
        .members
        .iter()
        .map(|member| crate::compiler2::canon::function_label(world, member.function))
        .collect();
    member_labels.sort();
    assert_eq!(
        member_labels,
        vec![
            "Enum.reduce/3#lambda@0/2".to_string(),
            "List.reduce_cont/3".to_string(),
            "List.reduce_cont/3".to_string(),
            "List.reduce_step/3".to_string(),
        ],
        "the system is every activation that handles the accumulator being solved: both reduce_cont \
         specializations, reduce_step, and the reducer lambda that BUILDS the next accumulator",
    );
    assert_eq!(
        cont_activations.len(),
        2,
        "both reduce_cont specializations hand the accumulator on, so both are in the system",
    );
    assert!(
        component.members.contains(&cont_activation),
        "reduce_cont's activation is a member"
    );
    assert!(
        component.members.contains(&step_activation),
        "reduce_step's activation is a member"
    );

    let reduce_fn = world.reference_function(list_module, "reduce", 3);
    let reduce_activations: Vec<ActivationKey> = settled
        .borrow()
        .iter()
        .filter(|key| key.function == reduce_fn)
        .cloned()
        .collect();
    assert!(
        !reduce_activations.is_empty(),
        "List.reduce/3 itself should have settled at least one activation"
    );
    for entry in &reduce_activations {
        assert!(
            world.return_component(entry).is_none(),
            "List.reduce/3's own entry dispatch sits outside the cont/step cycle it drives into"
        );
    }
}

/// `nest` returns `0` or `wrap(nest(rest))`, and `wrap(v)` returns `[v]`. On
/// paper that is `N = int | W(N)` with `W(v) = [v]`, so `N = mu X. int | [X]`
/// and `wrap` has ONE activation, `X -> [X]`, whatever the ascent would have
/// observed on its way there.
///
/// `wrap` is not on the call graph's cycle -- it calls nothing -- but its own
/// return is a function of `nest`'s, because the value it is handed IS
/// `nest`'s return. Both facts follow from the one rule: an argument whose
/// companion names a return the component has not settled carries an iterate,
/// so the callee is keyed on the variable addressing that slot rather than on
/// how far the ascent has climbed, and the slot's evidence becomes one more
/// unknown of the same equation system.
#[test]
fn wrap_nest_solves_through_its_non_recursive_helper() {
    let (mut compiler, settled, analyzed) =
        drive_fixture("wrap_nest.fz", include_str!("../../../fixtures2/behavior/wrap_nest.fz"));
    let world = compiler.world_mut();

    let nest_fn = world.reference_function(ModuleId::GLOBAL, "nest", 1);
    let wrap_fn = world.reference_function(ModuleId::GLOBAL, "wrap", 1);
    let nest_activation = sole_activation(&settled.borrow(), nest_fn, "nest/1");
    let wrap_activation = sole_activation(&analyzed.borrow(), wrap_fn, "wrap/1");

    let component = world
        .return_component(&nest_activation)
        .expect("nest/1 calls itself, a self edge");
    assert!(
        component.members.contains(&wrap_activation),
        "wrap/1's return is a function of nest/1's, so it solves with it: {:?}",
        component.members,
    );

    let nest_ty = world
        .activation_return(&nest_activation)
        .expect("nest/1 has a base case, so it publishes a type");
    let wrap_ty = world
        .activation_return(&wrap_activation)
        .expect("wrap/1 returns a list of whatever it is handed");

    let types = world.types_mut();
    let int = types.int();
    let nested = types.non_empty_list(nest_ty);
    let expected = types.union(int, nested);
    assert_eq!(
        nest_ty, expected,
        "nest/1's return is the fixed point of its own two clauses, int | [nest]",
    );
    assert_eq!(
        wrap_ty,
        types.non_empty_list(nest_ty),
        "wrap/1 returns a list of exactly what nest/1 returns",
    );
}

/// `go(list, acc)` folds a list of integers into an integer accumulator. Its
/// slot evidence is the component's own to solve, and the component publishes
/// only what it solved: a member's activation KEY carries addressed variables
/// (`[a0_e]`), which name a position rather than describe a value, so handing
/// one back as input evidence would widen the slot to `any` and every callee
/// keyed off it with it -- `Kernel.+/2` reached at `any` answers `int | float`,
/// and an integer fold reads back as `int | float`.
#[test]
fn a_ground_accumulator_never_reads_back_its_own_key_coordinate() {
    let (mut compiler, settled, _analyzed) = drive_fixture(
        "ground_accumulator.fz",
        include_str!("../../../fixtures2/behavior/ground_accumulator.fz"),
    );
    let world = compiler.world_mut();

    let go_fn = world.reference_function(ModuleId::GLOBAL, "go", 2);
    let go_activation = sole_activation(&settled.borrow(), go_fn, "go/2");
    let go_ty = world
        .activation_return(&go_activation)
        .expect("go/2 returns its accumulator on the empty clause");

    let types = world.types_mut();
    let int = types.int();
    assert_eq!(go_ty, int, "summing integers yields an integer, not int | float");
}

/// `step/1` wraps its own result in a list on one clause, so the STATIC
/// answer is that every activation of it owes its return to a solve. The one
/// activation this program has reaches the other clause only: it makes no
/// call at all, so no call edge joins it to anything. The system it belongs
/// to is therefore itself alone, and the solve still has to happen -- if
/// membership were drawn from call edges alone, nothing would own this
/// return and the activation would wait on a publisher that never comes.
#[test]
fn a_guard_dispatch_never_reaches_still_names_a_system_of_one() {
    let (mut compiler, settled, _analyzed) = drive_fixture(
        "unreached_guard.fz",
        include_str!("../../../fixtures2/behavior/unreached_guard.fz"),
    );
    let world = compiler.world_mut();

    let step_fn = world.reference_function(ModuleId::GLOBAL, "step", 1);
    let activation = sole_activation(&settled.borrow(), step_fn, "step/1");

    let component = world
        .return_component(&activation)
        .expect("step/1's return is being solved statically, so its activation belongs to a system");
    assert_eq!(
        component.members,
        vec![activation.clone()],
        "nothing else is on this system: the one activation makes no call",
    );
    assert_eq!(component.owner, activation, "a one-member system owns itself");

    let returned = world
        .activation_return(&activation)
        .expect("the solve publishes the reached clause's own value");
    assert_eq!(
        world.types().display(&returned),
        ":done",
        "the unreached clause contributes nothing, so the answer is the clause that runs",
    );
}
