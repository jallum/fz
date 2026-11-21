//! A guard helper called with a literal is planned at that literal.

use super::*;
use crate::ast::CallableName;
use crate::compiler2::drive_harness::{Drive, EntryDispatchCapture, Settled, latest_entry_dispatch};
use crate::compiler2::dump::DumpStage;

/// `fold` asks `is_function(f, 2)`; `typed` asks the same of `f` in its head.
const PROBE: &str = "
def fold([], acc, _f), do: acc
def fold([h | t], acc, f) when is_function(f, 2), do: fold(t, f.(h, acc), f)
def typed([], acc, _f), do: acc
def typed([h | t], acc, f :: (any, any -> any)), do: typed(t, f.(h, acc), f)
def main(), do: {fold([1, 2, 3], 0, fn x, a -> x + a end), typed([1, 2, 3], 0, fn x, a -> x + a end)}
";

fn probed() -> (Settled, EntryDispatchCapture) {
    let drive = Drive::source("is_function_arity_guard.fz", PROBE);
    let plans = EntryDispatchCapture::new();
    plans.install(drive.telemetry());
    (drive.dump_stage(DumpStage::Backend), plans)
}

#[test]
fn a_guard_that_asks_for_an_arity_builds_no_wrapper_and_narrows_the_callable_as_a_head_annotation_does() {
    let (settled, plans) = probed();
    let plan_of = |name| latest_entry_dispatch(&plans, settled.function(name, 3));
    let (guarded, typed) = (plan_of("fold"), plan_of("typed"));

    assert_eq!(
        settled.backend_program().construction_wrappers().len(),
        0,
        "asking a callable's arity is a question about its class, so no callable crosses the boxed seam"
    );
    assert!(
        guarded.guards.is_empty(),
        "is_function(f, 2) is a type question, not a guard"
    );
    assert_eq!(
        guarded.graph, typed.graph,
        "fold/3 narrows f to the arity-2 arrow exactly as typed/3's annotation does"
    );
}

/// The residue of `is_function/2` at `literal`, planned from the clauses that
/// can still win: what it asks of its first argument, when that is all it asks.
fn first_argument_asked_at(settled: &mut Settled, literal: GroundValue) -> Option<Ty> {
    let main = settled.function("main", 0);
    let namespace = settled.world().function_definition(main).0.namespace;
    let callee = Callee::Name(CallableName::source("is_function"));
    let mut plans = LiteralGuardPlans::default();
    let planned = plans
        .callee(
            settled.compiler_mut().world_mut(),
            namespace,
            &callee,
            2,
            &[None, Some(literal)],
        )
        .expect("is_function/2 plans at a literal");
    let GuardCallee::Helper(helper) = planned else {
        panic!("is_function/2 is a helper, not an extern");
    };
    helper.type_predicate.as_ref().map(|asked| {
        let [(0, ty)] = asked[..] else {
            panic!("a predicate of is_function/2 asks one type of the first argument: {asked:?}")
        };
        ty
    })
}

#[test]
fn is_function_at_an_arity_is_the_type_test_of_the_arrows_that_take_that_many_arguments() {
    let (mut settled, _) = probed();
    for arity in 0..=3usize {
        let asked = first_argument_asked_at(&mut settled, GroundValue::Int(arity as i64))
            .unwrap_or_else(|| panic!("is_function(_, {arity}) is a type test"));
        let types = settled.compiler_mut().world_mut().types_mut();
        let any = types.any();
        let arrow = types.arrow(&vec![any; arity], any);
        let annotation = types.runtime_type_test_envelope(arrow);
        assert!(
            types.is_subtype(&asked, &annotation) && types.is_subtype(&annotation, &asked),
            "is_function(_, {arity}) asks what the annotation of {arity} `any` and an `any` result asks"
        );
    }
}

#[test]
fn is_function_at_a_bad_arity_stays_the_helper_that_raises() {
    let (mut settled, _) = probed();
    for bad in [
        GroundValue::Int(-1),
        GroundValue::Atom("two".to_string()),
        GroundValue::Float(2.0f64.to_bits()),
    ] {
        assert_eq!(
            first_argument_asked_at(&mut settled, bad.clone()),
            None,
            "is_function(_, {bad:?}) is no type test: its raising clause wins"
        );
    }
}

#[test]
fn a_call_that_hands_no_literal_reaches_the_helper_as_reified() {
    let (mut settled, _) = probed();
    let main = settled.function("main", 0);
    let namespace = settled.world().function_definition(main).0.namespace;
    let callee = Callee::Name(CallableName::source("is_function"));
    let mut plans = LiteralGuardPlans::default();
    let world = settled.compiler_mut().world_mut();
    let called = plans
        .callee(world, namespace, &callee, 2, &[None, None])
        .expect("is_function/2 plans");
    let function = resolve_guard_callee_checked(world, namespace, &callee, 2);
    assert_eq!(called, world.guard_callee(function), "no literal decides nothing");
    assert!(plans.plans.is_empty(), "so no plan of its own is built");
}
