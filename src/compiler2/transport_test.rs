//! Unit tests for the transport descriptor vocabulary: the interners (shapes,
//! lanes, callables, boundaries) and the [`ShapeAgreement`] lattice. Behavioral
//! tests of a projected [`TransportPlan`] live in `transport_contract_test`.

use super::ExecutableNeed;
use super::body::ValueId;
use super::identity::{FunctionMap, ModuleId};
use super::transport::{
    ActivationSymbol, BoundaryDescr, CallableDescr, ExecutableSymbol, LaneDescr, ShapeAgreement, ShapeDescr, ShapeId,
    TransportClass, TransportInterners, TransportPosition, TransportStore,
};
use super::types::Types;

fn two_distinct_shapes() -> (ShapeId, ShapeId) {
    let mut types = Types::new();
    let int = types.int();
    let bool_ty = types.bool();
    let mut interners = TransportInterners::default();
    let int_lane = interners.intern_lane(LaneDescr {
        ty: int,
        class: TransportClass::Value,
    });
    let bool_lane = interners.intern_lane(LaneDescr {
        ty: bool_ty,
        class: TransportClass::Value,
    });
    let a = interners.intern_shape(ShapeDescr::Lane(int_lane));
    let b = interners.intern_shape(ShapeDescr::Lane(bool_lane));
    assert_ne!(a, b);
    (a, b)
}

#[test]
fn shape_agreement_ascends_unbound_to_agreed_to_conflicted() {
    // Intent: the lattice only ever climbs. One caller binds a shape; a
    // second caller carrying a different shape forces the sticky top.
    let (a, b) = two_distinct_shapes();

    assert_eq!(ShapeAgreement::BOTTOM, ShapeAgreement::Unbound);
    assert_eq!(ShapeAgreement::Unbound.agreed(), None);

    let one = ShapeAgreement::Unbound.join(ShapeAgreement::of(a));
    assert_eq!(one, ShapeAgreement::Agreed(a));
    assert_eq!(one.agreed(), Some(a));

    let still_one = one.join(ShapeAgreement::of(a));
    assert_eq!(still_one, ShapeAgreement::Agreed(a), "idempotent on agreement");

    let conflict = one.join(ShapeAgreement::of(b));
    assert_eq!(conflict, ShapeAgreement::Conflicted);
    assert_eq!(conflict.agreed(), None);
    assert!(conflict.is_conflicted());
}

#[test]
fn shape_agreement_join_is_order_independent() {
    // Intent: contributors arrive in any order; the joined result must not
    // depend on arrival order.
    let (a, b) = two_distinct_shapes();
    let contributions = [ShapeAgreement::of(a), ShapeAgreement::Unbound, ShapeAgreement::of(a)];
    let forward = contributions
        .iter()
        .copied()
        .fold(ShapeAgreement::BOTTOM, ShapeAgreement::join);
    let backward = contributions
        .iter()
        .rev()
        .copied()
        .fold(ShapeAgreement::BOTTOM, ShapeAgreement::join);
    assert_eq!(forward, ShapeAgreement::Agreed(a));
    assert_eq!(forward, backward);

    let with_conflict = [ShapeAgreement::of(b), ShapeAgreement::of(a)];
    assert_eq!(
        with_conflict
            .iter()
            .copied()
            .fold(ShapeAgreement::BOTTOM, ShapeAgreement::join),
        with_conflict
            .iter()
            .rev()
            .copied()
            .fold(ShapeAgreement::BOTTOM, ShapeAgreement::join),
    );
}

#[test]
fn shape_agreement_conflict_is_sticky_and_distinct_from_unbound() {
    // Intent: Conflicted is top -- nothing lowers it, not even Unbound --
    // and Unbound (nobody yet) is never mistaken for a resolved shape.
    let (a, _b) = two_distinct_shapes();
    let top = ShapeAgreement::Conflicted;
    assert_eq!(top.join(ShapeAgreement::Unbound), ShapeAgreement::Conflicted);
    assert_eq!(top.join(ShapeAgreement::of(a)), ShapeAgreement::Conflicted);
    assert_eq!(top.join(ShapeAgreement::Conflicted), ShapeAgreement::Conflicted);

    assert_ne!(ShapeAgreement::Unbound, ShapeAgreement::Conflicted);
    assert_eq!(ShapeAgreement::Unbound.agreed(), ShapeAgreement::Conflicted.agreed());
}

#[test]
fn transport_shape_interner_hashes_recursive_children_by_id() {
    let mut types = Types::new();
    let int = types.int();
    let mut interners = TransportInterners::default();

    let lane = interners.intern_lane(LaneDescr {
        ty: int,
        class: TransportClass::Value,
    });
    let scalar = interners.intern_shape(ShapeDescr::Lane(lane));
    let tuple = interners.intern_shape(ShapeDescr::Tuple(vec![scalar].into_boxed_slice()));
    let tuple_again = interners.intern_shape(ShapeDescr::Tuple(vec![scalar].into_boxed_slice()));
    let nested = interners.intern_shape(ShapeDescr::Tuple(vec![tuple].into_boxed_slice()));

    assert_eq!(lane.as_u32(), 0);
    assert_eq!(scalar.as_u32(), 0);
    assert_eq!(tuple, tuple_again);
    assert_ne!(tuple, nested);
    assert_eq!(interners.shape_count(), 3);
    assert_eq!(
        interners.shape(tuple),
        &ShapeDescr::Tuple(vec![scalar].into_boxed_slice()),
        "tuple descriptors store child ShapeIds, not child descriptors"
    );
}

#[test]
fn transport_descriptors_share_across_root_positions() {
    let mut types = Types::new();
    let int = types.int();
    let mut functions = FunctionMap::new();
    let add = functions.reference(ModuleId::GLOBAL, "add", 2);
    let mut store = TransportStore::new();
    let interners = store.interners_mut();

    let lane = interners.intern_lane(LaneDescr {
        ty: int,
        class: TransportClass::Value,
    });
    let shape = interners.intern_shape(ShapeDescr::Lane(lane));
    let executable = ExecutableSymbol {
        activation: ActivationSymbol {
            function: add,
            input: vec![int, int].into_boxed_slice(),
        },
        need: ExecutableNeed::Value,
    };
    let first_position = TransportPosition::ExecutableInput {
        executable: executable.clone(),
        semantic_index: 0,
    };
    let second_position = TransportPosition::Value {
        executable,
        value: ValueId::from_u32(7),
    };
    let callable = interners.intern_callable(CallableDescr {
        function: Some(add),
        capture_shapes: vec![shape].into_boxed_slice(),
        capture_lanes: vec![lane].into_boxed_slice(),
    });
    let same_callable = interners.intern_callable(CallableDescr {
        function: Some(add),
        capture_shapes: vec![shape].into_boxed_slice(),
        capture_lanes: vec![lane].into_boxed_slice(),
    });
    let callable_shape = interners.intern_shape(ShapeDescr::Callable(callable));
    let same_callable_shape = interners.intern_shape(ShapeDescr::Callable(same_callable));

    assert_ne!(first_position, second_position);
    assert_eq!(callable, same_callable);
    assert_eq!(callable_shape, same_callable_shape);
    assert_eq!(interners.callable_count(), 1);
    assert_eq!(interners.shape_count(), 2);
    assert_eq!(
        interners.callable(callable),
        &CallableDescr {
            function: Some(add),
            capture_shapes: vec![shape].into_boxed_slice(),
            capture_lanes: vec![lane].into_boxed_slice(),
        },
        "callable descriptors are independent of root-scoped positions"
    );
}

#[test]
fn transport_boundary_descriptors_are_interned_contracts() {
    let mut types = Types::new();
    let int = types.int();
    let mut functions = FunctionMap::new();
    let add = functions.reference(ModuleId::GLOBAL, "add", 2);
    let mut interners = TransportInterners::default();

    let lane = interners.intern_lane(LaneDescr {
        ty: int,
        class: TransportClass::Value,
    });
    let shape = interners.intern_shape(ShapeDescr::Lane(lane));
    let callable = interners.intern_callable(CallableDescr {
        function: Some(add),
        capture_shapes: vec![shape].into_boxed_slice(),
        capture_lanes: vec![lane].into_boxed_slice(),
    });
    let boundary = BoundaryDescr {
        callable,
        surface_arg_shapes: vec![shape].into_boxed_slice(),
        published_value_lane: lane,
        published_capture_lanes: vec![lane].into_boxed_slice(),
        published_arg_lanes: vec![lane].into_boxed_slice(),
        published_return_shape: shape,
        published_return_lanes: vec![lane].into_boxed_slice(),
    };

    let first = interners.intern_boundary(boundary.clone());
    let second = interners.intern_boundary(boundary.clone());

    assert_eq!(first, second);
    assert_eq!(interners.boundary_count(), 1);
    assert_eq!(interners.boundary(first), &boundary);
}

#[test]
fn transport_callable_descriptors_include_ordered_capture_lane_payload() {
    let mut types = Types::new();
    let int = types.int();
    let atom = types.atom();
    let mut functions = FunctionMap::new();
    let add = functions.reference(ModuleId::GLOBAL, "add", 2);
    let mut interners = TransportInterners::default();

    let int_lane = interners.intern_lane(LaneDescr {
        ty: int,
        class: TransportClass::Value,
    });
    let atom_lane = interners.intern_lane(LaneDescr {
        ty: atom,
        class: TransportClass::Value,
    });
    let shared_callable = interners.intern_callable(CallableDescr {
        function: None,
        capture_shapes: Box::default(),
        capture_lanes: Box::default(),
    });
    let shared_shape = interners.intern_shape(ShapeDescr::Callable(shared_callable));
    let int_payload = interners.intern_callable(CallableDescr {
        function: Some(add),
        capture_shapes: vec![shared_shape].into_boxed_slice(),
        capture_lanes: vec![int_lane].into_boxed_slice(),
    });
    let atom_payload = interners.intern_callable(CallableDescr {
        function: Some(add),
        capture_shapes: vec![shared_shape].into_boxed_slice(),
        capture_lanes: vec![atom_lane].into_boxed_slice(),
    });

    assert_ne!(
        int_payload, atom_payload,
        "one CallableId cannot key two different ordered capture-lane payloads"
    );
}
