//! Unit tests for the transport descriptor vocabulary: the interners for
//! shapes, lanes, callables, and boundaries. Behavioral tests of a projected
//! [`TransportPlan`] live in `transport_contract_test`.

use super::ExecutableNeed;
use super::body::ValueId;
use super::identity::{FunctionMap, ModuleId};
use super::transport::{
    ActivationSymbol, BoundaryDescr, CallableDescr, ExecutableSymbol, LaneDescr, ShapeDescr, TransportClass,
    TransportInterners, TransportPosition, TransportStore,
};
use super::types::Types;

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
