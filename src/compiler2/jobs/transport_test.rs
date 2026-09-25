//! The closure-call form is one answer with three states, so each state is
//! reachable from a callee layout and a callsite summary alone.

use super::super::transport::{ClosureCallForm, closure_call_form};
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

#[cfg(test)]
mod tests {
    use super::super::*;

    #[test]
    fn same_source_capture_requirements_retain_concrete_zero_lane_children() {
        let mut world = World::new();
        let module = super::super::super::super::identity::ModuleId::GLOBAL;
        let function = world.reference_function(module, "holder", 0);
        let captured = world.reference_function(module, "captured", 0);
        let nothing = TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing));
        let captured = world.intern_callable(CallableDescr {
            function: Some(captured),
            arity: 0,
            capture_layouts: Box::default(),
        });
        let captured = TransportLayout::structural(world.intern_shape(ShapeDescr::Callable(captured)));
        let left = CallableDescr {
            function: Some(function),
            arity: 0,
            capture_layouts: Box::new([tuple_layout(&mut world, &[nothing, captured])]),
        };
        let right = CallableDescr {
            capture_layouts: Box::new([tuple_layout(&mut world, &[captured, nothing])]),
            ..left.clone()
        };
        let expected = CallableDescr {
            capture_layouts: Box::new([tuple_layout(&mut world, &[captured, captured])]),
            ..left.clone()
        };
        for (left, right) in [(&left, &right), (&right, &left)] {
            let combined = combine_callable_requirements(&mut world, left, right)
                .expect("one activation's unused slot does not erase another activation's concrete child");
            assert_eq!(combined, expected);
            assert!(world.layout_physical_lanes(combined.capture_layouts[0]).is_empty());
        }
    }

    #[test]
    fn incompatible_capture_requirements_do_not_invent_a_source_payload() {
        let mut world = World::new();
        let function = world.reference_function(super::super::super::super::identity::ModuleId::GLOBAL, "capturing", 0);
        let int = world.types_mut().int();
        let float = world.types_mut().float();
        let left = CallableDescr {
            function: Some(function),
            arity: 0,
            capture_layouts: Box::new([TransportLayout::structural(value_lane_shape(&mut world, int))]),
        };
        let right = CallableDescr {
            capture_layouts: Box::new([TransportLayout::structural(value_lane_shape(&mut world, float))]),
            ..left.clone()
        };
        assert!(
            combine_callable_requirements(&mut world, &left, &right).is_none(),
            "target requirements alone do not prove that the source retained a whole boxed payload"
        );
    }

    #[test]
    fn exact_callable_owner_keeps_typed_target_evidence_from_a_generic_source() {
        let mut world = World::new();
        let function = world.reference_function(super::super::super::super::identity::ModuleId::GLOBAL, "target", 0);
        let ty = world
            .types_mut()
            .fn_ref_lit(crate::types::ClosureTarget(function.as_u32()), 0);
        let activation = super::super::super::super::ActivationKey::from_inputs(
            super::super::super::super::RootId::for_test(0),
            function,
            &[],
            world.types_mut(),
        );
        let executable = ExecutableKey {
            activation: activation.clone(),
            need: ExecutableNeed::Value,
        };
        let resolution = executable_symbol(&executable, world.types());
        let surface = CallableSurface::new(Vec::new(), world.types_mut());
        let demand = RuntimeDemand::callable(CallableDemand {
            resolved: BTreeSet::from([surface.clone()]),
            targets: BTreeSet::from([CallableTarget {
                surface,
                activation,
                activation_inputs: Vec::new(),
                need: ExecutableNeed::Value,
            }]),
            opaque: false,
            escape: false,
        });
        let generic = world.intern_callable(CallableDescr {
            function: None,
            arity: 0,
            capture_layouts: Box::default(),
        });
        let exact = world.intern_callable(CallableDescr {
            function: Some(function),
            arity: 0,
            capture_layouts: Box::default(),
        });
        let layout = TransportLayout::structural(world.intern_shape(ShapeDescr::Callable(exact)));
        let position = TransportPosition::Value {
            executable: resolution.clone(),
            value: ValueId::from_u32(0),
        };
        let mut source = TransportFactsBuilder::default();
        source.record_callable(generic, vec![resolution.clone()], Vec::new(), Vec::new(), Vec::new());

        let owner = project_owner_answer(&mut world, &source, layout, ty, &demand, &position);

        assert_eq!(
            owner.layout, layout,
            "projection preserves the consumer's exact zero-lane layout"
        );
        assert_eq!(
            owner.callable_facts.len(),
            1,
            "the owner publishes only its own callable descriptor"
        );
        assert_eq!(
            owner.callable_facts[&exact].resolutions.as_ref(),
            &[resolution],
            "typed target evidence survives a generic-to-exact representation change"
        );
        assert!(owner.construction.is_none());
        assert!(
            owner.boundary_facts.is_empty(),
            "a direct-only consumer creates no runtime boundary"
        );
    }

    #[test]
    fn tuple_carrier_comes_from_the_composite_demand_not_its_child_lanes() {
        let mut world = World::new();
        let atom = world.types_mut().atom();
        let any = world.types_mut().any();
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let atom_lane = value_lane_shape(&mut world, atom);
        let any_lane_id = value_lane(&mut world, any);
        let any_lane = world.intern_shape(ShapeDescr::Lane(any_lane_id));
        let child = TransportLayout {
            structural: any_lane,
            carrier: TransportCarrier::ValueRef(any_lane_id),
        };
        let partial_layout = tuple_layout(&mut world, &[TransportLayout::structural(nothing), child]);
        assert_eq!(partial_layout.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(partial_layout.structural) else {
            panic!("the partial composite should retain its tuple field positions")
        };
        assert_eq!(fields.as_ref(), &[TransportLayout::structural(nothing), child]);

        let complete_fields = [TransportLayout::structural(atom_lane), child];
        let whole = tuple_layout(&mut world, &complete_fields);
        assert_eq!(whole.carrier, TransportCarrier::Absent);
        assert_eq!(
            world.shape(whole.structural),
            &ShapeDescr::Tuple(Box::new([TransportLayout::structural(atom_lane), child,]))
        );

        assert!(
            !tuple_layout(&mut world, &complete_fields).carrier.is_value_ref(),
            "tuple composition never manufactures the composite carrier",
        );
    }

    #[test]
    fn tuple_child_carrier_lane_must_cover_its_field_type() {
        let mut world = World::new();
        let atom = world.types_mut().atom();
        let int = world.types_mut().int();
        let any = world.types_mut().any();
        let tuple_ty = world.types_mut().tuple(&[atom]);
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let int_lane = value_lane(&mut world, int);
        let any_lane = value_lane(&mut world, any);
        let mismatched = world.intern_shape(ShapeDescr::Tuple(Box::new([TransportLayout {
            structural: nothing,
            carrier: TransportCarrier::ValueRef(int_lane),
        }])));
        let covering = world.intern_shape(ShapeDescr::Tuple(Box::new([TransportLayout {
            structural: nothing,
            carrier: TransportCarrier::ValueRef(any_lane),
        }])));

        assert!(!shape_carries(&mut world, mismatched, tuple_ty));
        assert!(shape_carries(&mut world, covering, tuple_ty));
    }

    #[test]
    fn same_arity_tuple_join_keeps_a_child_carrier_local() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let tuple_ty = world.types_mut().tuple(&[int]);
        let lane = value_lane(&mut world, int);
        let scalar = world.intern_shape(ShapeDescr::Lane(lane));
        let structural_child = TransportLayout::structural(scalar);
        let carried_child = TransportLayout {
            structural: scalar,
            carrier: TransportCarrier::ValueRef(lane),
        };
        let structural_tuple = tuple_layout(&mut world, &[structural_child]);
        let carried_tuple = tuple_layout(&mut world, &[carried_child]);
        let joined = derived_transport_layout(
            &mut world,
            tuple_ty,
            &RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole()]),
            &[structural_tuple, carried_tuple],
        );

        assert_eq!(joined.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(joined.structural) else {
            panic!("same-arity tuple alternatives should join field by field")
        };
        assert_eq!(fields.as_ref(), &[carried_child]);
    }

    #[test]
    fn generic_tuple_layout_retains_a_nested_first_class_carrier() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let callable_ty = world.types_mut().fn_ref_lit(crate::types::ClosureTarget(7), 1);
        let tuple_ty = world.types_mut().tuple(&[int, callable_ty]);
        let demand = RuntimeDemand::tuple_fields(vec![
            RuntimeDemand::whole(),
            RuntimeDemand::callable(CallableDemand::escaped()),
        ]);
        let layout = derived_transport_layout(&mut world, tuple_ty, &demand, &[]);

        assert_eq!(layout.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(layout.structural) else {
            panic!("the exact tuple demand should produce a recursive tuple layout")
        };
        assert!(fields[1].carrier.is_value_ref());
        assert!(matches!(world.shape(fields[1].structural), ShapeDescr::Callable(_)));
    }

    #[test]
    fn generic_whole_exact_tuple_stays_complete_and_decomposed() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let tuple_ty = world.types_mut().tuple(&[int, int]);
        let layout = derived_transport_layout(&mut world, tuple_ty, &RuntimeDemand::whole(), &[]);

        assert_eq!(layout.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(layout.structural) else {
            panic!("Whole over an exact tuple must retain complete field layouts")
        };
        assert_eq!(fields.len(), 2);
        assert!(fields.iter().all(|field| field.carrier == TransportCarrier::Absent));
        assert!(
            fields
                .iter()
                .all(|field| matches!(world.shape(field.structural), ShapeDescr::Lane(_)))
        );
    }

    #[test]
    fn generic_partial_exact_tuple_fills_omitted_trailing_fields_with_nothing() {
        let mut world = World::new();
        let atom = world.types_mut().atom();
        let int = world.types_mut().int();
        let tuple_ty = world.types_mut().tuple(&[atom, atom, int, atom]);
        let demand = RuntimeDemand::tuple_fields(vec![
            RuntimeDemand::ignore(),
            RuntimeDemand::ignore(),
            RuntimeDemand::whole(),
        ]);
        let layout = derived_transport_layout(&mut world, tuple_ty, &demand, &[]);

        assert_eq!(layout.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(layout.structural) else {
            panic!("a tuple demand prefix must retain the exact tuple's positions")
        };
        assert_eq!(fields.len(), 4);
        assert!(matches!(world.shape(fields[0].structural), ShapeDescr::Nothing));
        assert!(matches!(world.shape(fields[1].structural), ShapeDescr::Nothing));
        assert!(matches!(world.shape(fields[2].structural), ShapeDescr::Lane(_)));
        assert!(matches!(world.shape(fields[3].structural), ShapeDescr::Nothing));

        // A demand vector longer than the tuple it is read against describes a
        // DIFFERENT tuple -- one clause of a value spanning arities read
        // further than this one has fields. The surplus names no field here and
        // is dropped; the fields that do exist keep their own lanes rather than
        // boxing the whole value over a position it never had.
        let overlong = RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(); 5]);
        let layout = derived_transport_layout(&mut world, tuple_ty, &overlong, &[]);

        assert_eq!(layout.carrier, TransportCarrier::Absent);
        let ShapeDescr::Tuple(fields) = world.shape(layout.structural) else {
            panic!("a surplus field demand must not box the positions the tuple does have")
        };
        assert_eq!(fields.len(), 4);
        assert!(
            fields
                .iter()
                .all(|field| matches!(world.shape(field.structural), ShapeDescr::Lane(_)))
        );
    }

    #[test]
    fn equal_layout_join_returns_without_minting_a_generic_alternative() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let exact = TransportLayout::structural(nothing);
        let before = (world.shape_count(), world.lane_count());

        let joined = derived_transport_layout(&mut world, int, &RuntimeDemand::whole(), &[exact, exact]);

        assert_eq!(joined, exact);
        assert_eq!(
            (world.shape_count(), world.lane_count()),
            before,
            "an exact concordant join must not construct an unused generic layout",
        );
    }
}
