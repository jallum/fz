//! The closure-call form is one answer with three states, so each state is
//! reachable from a callee layout and a callsite summary alone.

use super::transport::{ClosureCallForm, closure_call_form};
use crate::compiler2::artifact::ClosureCallEdge;
use crate::compiler2::identity::{ExecutableNeed, ModuleId, RootId};
use crate::compiler2::pull::TransportLayout;
use crate::compiler2::semantic::{CallSiteSummary, CallTargetSummary, SelectedCallee};
use crate::compiler2::transport::{CallableDescr, LaneDescr, ShapeDescr, TransportCarrier, TransportClass};
use crate::compiler2::{ActivationKey, FunctionId, Ty, World};

/// A target that takes `captures` values beyond the arity its source was
/// written with, and a callsite summary naming exactly that target.
fn one_target(world: &mut World, name: &str, surface_arity: usize, captures: usize) -> (FunctionId, CallSiteSummary) {
    let int = world.types_mut().int();
    let function = world.reference_function(ModuleId::GLOBAL, name, surface_arity);
    let inputs = vec![int; surface_arity + captures];
    let activation = ActivationKey::from_inputs(RootId::for_test(1), function, &inputs, world.types_mut());
    assert_eq!(world.activation_capture_count(&activation), captures);
    let summary = CallSiteSummary {
        targets: vec![CallTargetSummary {
            callee: SelectedCallee::Function(function),
            surface_inputs: vec![int; surface_arity],
            activation: Some(activation),
            activation_inputs: None,
            extern_params: None,
            return_ty: Some(int),
        }],
        return_ty: Some(int),
    };
    (function, summary)
}

/// A callable carrier naming `function` and holding `captures` capture lanes.
fn callable_layout(world: &mut World, function: Option<FunctionId>, captures: usize) -> TransportLayout {
    let int = world.types_mut().int();
    let lane = world.intern_lane(LaneDescr {
        ty: int,
        class: TransportClass::Value,
    });
    let capture = TransportLayout::structural(world.intern_shape(ShapeDescr::Lane(lane)));
    let callable = world.intern_callable(CallableDescr {
        function,
        arity: 0,
        capture_layouts: vec![capture; captures].into_boxed_slice(),
    });
    TransportLayout::structural(world.intern_shape(ShapeDescr::Callable(callable)))
}

fn lane_layout(world: &mut World, ty: Ty) -> TransportLayout {
    let lane = world.intern_lane(LaneDescr {
        ty,
        class: TransportClass::Value,
    });
    TransportLayout::structural(world.intern_shape(ShapeDescr::Lane(lane)))
}

/// The caller holds the target's captures, so it calls the target directly and
/// hands it those captures as ordinary arguments.
#[test]
fn a_callable_holding_the_targets_captures_calls_it_directly() {
    let mut world = World::new();
    let (function, summary) = one_target(&mut world, "adds", 1, 1);
    let callee = callable_layout(&mut world, Some(function), 1);

    let form = closure_call_form(&mut world, callee, Some(&summary), ExecutableNeed::Value);

    let ClosureCallForm::Direct {
        edge: ClosureCallEdge::Direct { target, capture_count },
        target: row,
    } = form
    else {
        panic!("a callable carrying the target's one capture should call it directly");
    };
    assert_eq!(target.activation.function, function);
    assert_eq!(capture_count, 1);
    assert!(
        matches!(row.callee, SelectedCallee::Function(named) if named == function),
        "the answer carries the summary row it was decided from, so lowering asks nothing twice"
    );
}

/// A target that declares no captures asks the caller for nothing, so a
/// capture-free callable still calls it directly.
#[test]
fn a_capture_free_target_is_called_directly_with_no_captures() {
    let mut world = World::new();
    let (function, summary) = one_target(&mut world, "plain", 1, 0);
    let callee = callable_layout(&mut world, Some(function), 0);

    let form = closure_call_form(&mut world, callee, Some(&summary), ExecutableNeed::Value);

    assert!(
        matches!(
            form,
            ClosureCallForm::Direct {
                edge: ClosureCallEdge::Direct { capture_count: 0, .. },
                ..
            }
        ),
        "a target declaring no captures is still a direct call"
    );
}

/// A value travelling in the boxed carrier is one word the caller cannot take
/// apart, so the call goes through the apply seam however well the callsite
/// knows its target.
#[test]
fn a_value_ref_carrier_calls_through_the_seam_even_with_one_named_target() {
    let mut world = World::new();
    let (function, summary) = one_target(&mut world, "adds", 1, 1);
    let lane = {
        let int = world.types_mut().int();
        world.intern_lane(LaneDescr {
            ty: int,
            class: TransportClass::Value,
        })
    };
    let mut callee = callable_layout(&mut world, Some(function), 1);
    callee.carrier = TransportCarrier::ValueRef(lane);

    let form = closure_call_form(&mut world, callee, Some(&summary), ExecutableNeed::Value);

    assert!(matches!(form, ClosureCallForm::Seam));
}

/// A bare lane holding a fun is the same word by another spelling: a callable
/// has no raw representation, so its lane IS the closure pointer.
#[test]
fn a_bare_fun_lane_calls_through_the_seam() {
    let mut world = World::new();
    let fun = {
        let int = world.types_mut().int();
        world.types_mut().arrow(&[int], int)
    };
    let callee = lane_layout(&mut world, fun);

    let form = closure_call_form(&mut world, callee, None, ExecutableNeed::Value);

    assert!(matches!(form, ClosureCallForm::Seam));
}

/// No word to call through and no evidence that anything could be called: the
/// call never happens, and the form says so rather than inventing a target.
#[test]
fn a_callee_with_neither_a_word_nor_evidence_is_a_dead_call() {
    let mut world = World::new();
    let nothing = world.intern_shape(ShapeDescr::Nothing);

    let form = closure_call_form(
        &mut world,
        TransportLayout::structural(nothing),
        None,
        ExecutableNeed::Value,
    );

    assert!(matches!(form, ClosureCallForm::Dead));
}

/// The callsite summary names a target that declares a capture, and transport
/// delivered a callee carrying neither that capture nor a word the seam could
/// open. Two authorities have contradicted each other about one value, which
/// is a compiler defect and stops as one.
///
/// The expected text is pinned because the calculator reads interned ids out
/// of the world, and a malformed one would panic somewhere else entirely.
#[test]
#[should_panic(expected = "carries neither the captures of the 1 target(s) its callsite names")]
fn a_callee_supplying_neither_captures_nor_a_word_is_a_contradiction() {
    let mut world = World::new();
    let (_function, summary) = one_target(&mut world, "needs_capture", 1, 1);
    let callee = callable_layout(&mut world, None, 0);

    let _ = closure_call_form(&mut world, callee, Some(&summary), ExecutableNeed::Value);
}
