//! Unit tests for the transport descriptor vocabulary: the interners for
//! shapes, lanes, callables, and boundaries. Behavioral tests of the
//! product-path transport plan live in `transport_contract_test`.

use super::body::ValueId;
use super::identity::{FunctionMap, ModuleId};
use super::pull::ProductKey;
use super::semantic::SemanticOrd;
use super::transport::{
    ActivationSymbol, BoundaryDescr, CallableDescr, ExecutableSymbol, LaneDescr, ShapeDescr, TransportClass,
    TransportInterners, TransportPosition, TransportStore,
};
use super::types::Types;
use super::{ActivationKey, ExecutableKey, ExecutableNeed, RootId};

const ORDERING_METHODS: [&str; 9] = [
    ".sort(",
    ".sort_unstable(",
    ".sort_by(",
    ".sort_by_key(",
    ".sort_by_cached_key(",
    ".sort_unstable_by(",
    ".sort_unstable_by_key(",
    ".min_by(",
    ".min_by_key(",
];

const PRESENTATION_ORDER_TOKENS: [&str; 11] = [
    "display",
    "TyCanon",
    "format!",
    "format_args!",
    "Debug",
    "debug",
    "canonical_",
    "canon_",
    "render",
    "to_string",
    "stable_sort_key",
];

fn presentation_order_violation(source: &str) -> Option<(&'static str, &str)> {
    ORDERING_METHODS
        .into_iter()
        .flat_map(|method| source.match_indices(method).map(move |(offset, _)| (offset, method)))
        .find_map(|(offset, method)| {
            let open = offset + method.len() - 1;
            let mut depth = 0;
            let end = source[open..]
                .char_indices()
                .find_map(|(relative, character)| match character {
                    '(' => {
                        depth += 1;
                        None
                    }
                    ')' => {
                        depth -= 1;
                        (depth == 0).then_some(open + relative + 1)
                    }
                    _ => None,
                })
                .unwrap_or(source.len());
            let expression = &source[offset..end];
            PRESENTATION_ORDER_TOKENS
                .into_iter()
                .find(|forbidden| expression.contains(forbidden))
                .map(|forbidden| (forbidden, expression))
        })
}

#[test]
fn transport_consumers_share_one_typed_semantic_order() {
    let mut types = Types::new();
    let int = types.int();
    let list = types.list(int);
    let non_empty = types.non_empty_list(int);
    let mut functions = FunctionMap::new();
    let function = functions.reference(ModuleId::GLOBAL, "ordered", 1);
    let root = RootId::for_test(0);
    let keys = [list, non_empty].map(|input| ExecutableKey {
        activation: ActivationKey::from_inputs(root, function, &[input], &mut types),
        need: ExecutableNeed::Value,
    });
    let symbols = keys.each_ref().map(|key| ExecutableSymbol {
        activation: ActivationSymbol {
            function: key.activation.function,
            arrow: key.activation.arrow,
            input: key.activation.inputs(&types).into_boxed_slice(),
        },
        need: key.need,
    });
    let positions = symbols.each_ref().map(|executable| TransportPosition::ExecutableInput {
        executable: executable.clone(),
        semantic_index: 0,
    });

    let key_order = keys[0].semantic_cmp(&keys[1], &types);
    assert_ne!(key_order, std::cmp::Ordering::Equal);
    assert_eq!(symbols[0].semantic_cmp(&symbols[1], &types), key_order);
    assert_eq!(positions[0].semantic_cmp(&positions[1], &types), key_order);
    assert_eq!(
        ProductKey::TransportShape(positions[0].clone())
            .semantic_cmp(&ProductKey::TransportShape(positions[1].clone()), &types),
        key_order,
        "product publication and transport packaging must delegate to the same position order",
    );
}

#[test]
fn production_activation_order_has_one_typed_nontextual_authority() {
    let transport = include_str!("transport.rs");
    let production_order_owners = [
        include_str!("drive.rs"),
        include_str!("deps.rs"),
        include_str!("scheduler.rs"),
        include_str!("pull.rs"),
        include_str!("product_drive.rs"),
        include_str!("semantic.rs"),
        transport,
        include_str!("world.rs"),
        include_str!("dump.rs"),
        include_str!("fixture_facts.rs"),
        include_str!("jobs/artifact.rs"),
        include_str!("jobs/backend.rs"),
        include_str!("jobs/runtime_demand.rs"),
        include_str!("jobs/transport.rs"),
        include_str!("types/addressed.rs"),
        include_str!("types/mod.rs"),
        include_str!("types/order.rs"),
        include_str!("../telemetry/jsonl.rs"),
    ];
    for authority in [
        "impl SemanticOrd<Types> for Job",
        "impl SemanticOrd<Types> for FactKey",
        "impl SemanticOrd<Types> for ExecutableSymbol",
        "impl SemanticOrd<Types> for TransportPosition",
    ] {
        assert_eq!(
            production_order_owners
                .iter()
                .map(|source| source.matches(authority).count())
                .sum::<usize>(),
            1,
            "typed ordering authority must have exactly one production definition: {authority}",
        );
    }
    for forbidden in [
        "StableSortKey",
        "stable_sort_key",
        "canonical_activation_arrow_key",
        "display_with_callable_labels",
        "publish_product_ordered_by",
        "publish_product_ordered",
        "ordered_effect_scc_members",
        "compare_products",
        "compare_executable_keys",
        "compare_transport_positions",
        "compare_product_executable_symbol",
        "cmp_product_transport_position",
    ] {
        assert!(
            production_order_owners.iter().all(|source| !source.contains(forbidden)),
            "superseded production ordering API remains: {forbidden}",
        );
    }

    for source in production_order_owners {
        if let Some((forbidden, expression)) = presentation_order_violation(source) {
            panic!("production ordering expression consults presentation text `{forbidden}`: {expression}");
        }
    }
    for hostile in [
        "items.sort_by_cached_key(|item| format!(\"{item:?}\"));",
        "items.sort_by_key(rendered_activation_key);",
        "items.sort_unstable_by(|left, right| format!(\"{left:?}\").cmp(&format!(\"{right:?}\")));",
        "items.sort_unstable_by_key(display_activation_key);",
        "items.min_by(|left, right| TyCanon::new().cmp(left, right));",
    ] {
        assert!(
            presentation_order_violation(hostile).is_some(),
            "static proof must reject presentation ordering independent of sort syntax: {hostile}",
        );
    }
    assert!(
        presentation_order_violation("items.sort_by(|left, right| left.semantic_cmp(right, types));").is_none(),
        "the static proof must accept the typed semantic relation",
    );
    assert!(
        !include_str!("types/mod.rs").contains("fn cmp_tys"),
        "storage-canonical type order must not be exposed as an activation-order API",
    );
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
            arrow: int,
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
        arity: 0,
        capture_tys: Box::default(),
        capture_shapes: vec![shape].into_boxed_slice(),
        capture_lanes: vec![lane].into_boxed_slice(),
    });
    let same_callable = interners.intern_callable(CallableDescr {
        function: Some(add),
        arity: 0,
        capture_tys: Box::default(),
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
            arity: 0,
            capture_tys: Box::default(),
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
        arity: 0,
        capture_tys: Box::default(),
        capture_shapes: vec![shape].into_boxed_slice(),
        capture_lanes: vec![lane].into_boxed_slice(),
    });
    let boundary = BoundaryDescr {
        callable,
        surface_arg_shapes: vec![shape].into_boxed_slice(),
        published_value_lane: lane,
        published_capture_lanes: vec![lane].into_boxed_slice(),
        published_arg_lanes: vec![lane].into_boxed_slice(),
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
        arity: 0,
        capture_tys: Box::default(),
        capture_shapes: Box::default(),
        capture_lanes: Box::default(),
    });
    let shared_shape = interners.intern_shape(ShapeDescr::Callable(shared_callable));
    let int_payload = interners.intern_callable(CallableDescr {
        function: Some(add),
        arity: 0,
        capture_tys: Box::default(),
        capture_shapes: vec![shared_shape].into_boxed_slice(),
        capture_lanes: vec![int_lane].into_boxed_slice(),
    });
    let atom_payload = interners.intern_callable(CallableDescr {
        function: Some(add),
        arity: 0,
        capture_tys: Box::default(),
        capture_shapes: vec![shared_shape].into_boxed_slice(),
        capture_lanes: vec![atom_lane].into_boxed_slice(),
    });

    assert_ne!(
        int_payload, atom_payload,
        "one CallableId cannot key two different ordered capture-lane payloads"
    );
}

#[test]
fn transport_callable_descriptors_keep_elided_capture_groundings_distinct() {
    let mut types = Types::new();
    let int = types.int();
    let atom = types.atom();
    let mut functions = FunctionMap::new();
    let apply = functions.reference(ModuleId::GLOBAL, "apply", 1);
    let mut interners = TransportInterners::default();

    let int_capture = interners.intern_callable(CallableDescr {
        function: Some(apply),
        arity: 0,
        capture_tys: vec![int].into_boxed_slice(),
        capture_shapes: Box::default(),
        capture_lanes: Box::default(),
    });
    let atom_capture = interners.intern_callable(CallableDescr {
        function: Some(apply),
        arity: 0,
        capture_tys: vec![atom].into_boxed_slice(),
        capture_shapes: Box::default(),
        capture_lanes: Box::default(),
    });

    assert_ne!(
        int_capture, atom_capture,
        "eliding physical capture lanes must not pool distinct settled capture groundings"
    );
}
