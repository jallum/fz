use std::cell::RefCell;
use std::rc::Rc;

use super::transport::{
    BoundaryDescr, CodegenLaneRepr, CodegenSeam, LaneId, ShapeDescr, ShapeId, TransportPlan, TransportPosition,
};
use super::{DriveOutcome, ExecutableNeed, World};
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

const EVENT_NAME: &[&str] = &["fz", "compiler2", "transport_flow", "defined"];

const MEASUREMENT_FIELDS: &[&str] = &[
    "root_id",
    "semantic_revision",
    "executable_count",
    "transport_position_count",
    "shape_descriptor_count",
    "lane_descriptor_count",
    "callable_descriptor_count",
    "boundary_descriptor_count",
    "nothing_shape_count",
    "tuple_shape_count",
    "callable_shape_count",
    "direct_callable_count",
    "first_class_callable_count",
    "boundary_publication_count",
    "codegen_seam_fact_count",
    "codegen_function_entry_seam_fact_count",
    "codegen_block_param_seam_fact_count",
    "codegen_return_delivery_seam_fact_count",
    "codegen_continuation_entry_seam_fact_count",
    "codegen_tail_call_seam_fact_count",
    "codegen_callable_boundary_seam_fact_count",
    "codegen_extern_boundary_seam_fact_count",
    "codegen_first_class_publication_seam_fact_count",
];

const METADATA_FIELDS: &[&str] = &[
    "entry_executable_symbol",
    "executable_membership",
    "transport_positions",
    "shape_descriptors",
    "lane_descriptors",
    "callable_facts",
    "boundary_facts",
    "seam_facts",
];

const SHAPE_DESCRIPTORS: &[(&str, &str)] = &[
    ("S_nothing", "Nothing"),
    ("S_int", "Lane(L_int)"),
    ("S_direct_callable", "Callable(C_direct)"),
    ("S_pair_return", "Tuple([S_int, S_direct_callable])"),
    ("S_pub_callable", "Callable(C_pub)"),
];

const LANE_DESCRIPTORS: &[(&str, &str)] = &[("L_int", "LaneDescr { ty: int, transport_class: value }")];

const CALLABLE_FACTS: &[(&str, &str)] = &[
    (
        "C_direct",
        "target E_add; capture_shapes [S_int]; direct_surfaces [[S_int]]; boundary_ids []",
    ),
    (
        "C_pub",
        "target E_add; capture_shapes [S_int]; direct_surfaces []; boundary_ids [B_pub]",
    ),
];

const BOUNDARY_FACTS: &[(&str, &str)] = &[(
    "B_pub",
    "callable C_pub; surface_arg_shapes [S_int]; published_capture_lanes [L_int]; \
     published_arg_lanes [L_int]; published_return_shape S_int; published_return_lanes [L_int]",
)];

const ROOT_PLAN_MEMBERSHIP: &[&str] = &["E_main", "E_pair", "E_add"];

const TRANSPORT_POSITIONS: &[(&str, &str)] = &[
    ("Pos(E_pair.input[0])", "S_int"),
    ("Pos(E_pair.return)", "S_pair_return"),
    ("Pos(E_main.resume(pair call))", "S_pair_return"),
    ("Pos(E_add.input[0])", "S_int"),
    ("Pos(E_add.input[1])", "S_int"),
    ("Pos(E_add.return)", "S_int"),
    ("Pos(E_main.value(pub))", "S_pub_callable"),
];

const SEAM_FACTS: &[(&str, &str)] = &[];

#[test]
fn compiler2_transport_flow_contract_separates_shared_descriptors_from_root_plan() {
    assert_eq!(
        ROOT_PLAN_MEMBERSHIP,
        ["E_main", "E_pair", "E_add"],
        "RootId owns executable membership; executable symbols stay shareable"
    );
    assert_eq!(
        TRANSPORT_POSITIONS.len(),
        7,
        "the worked example should pin every root-scoped transport position"
    );
    assert_eq!(
        shape("S_pair_return"),
        Some("Tuple([S_int, S_direct_callable])"),
        "pair/1 returns the same tuple shape that main/0 resumes from"
    );
    assert_eq!(
        position_shape("Pos(E_pair.return)"),
        position_shape("Pos(E_main.resume(pair call))"),
        "producer return and consumer resume must share one ShapeId"
    );
    assert_eq!(
        callable("C_direct"),
        Some("target E_add; capture_shapes [S_int]; direct_surfaces [[S_int]]; boundary_ids []"),
        "direct callable identity is separate from boundary publication"
    );
    assert_eq!(
        callable("C_pub"),
        Some("target E_add; capture_shapes [S_int]; direct_surfaces []; boundary_ids [B_pub]"),
        "the escaped callable shares the target but publishes an explicit boundary fact"
    );
    assert_eq!(
        boundary("B_pub"),
        Some(
            "callable C_pub; surface_arg_shapes [S_int]; published_capture_lanes [L_int]; \
             published_arg_lanes [L_int]; published_return_shape S_int; published_return_lanes [L_int]"
        ),
        "boundary publication is contextual and points at shared lane/shape ids"
    );

    for (name, descr) in SHAPE_DESCRIPTORS.iter().chain(LANE_DESCRIPTORS) {
        assert_descriptor_is_shareable(name, descr);
    }
    for (position, shape) in TRANSPORT_POSITIONS {
        assert!(
            position.starts_with("Pos(") && shape.starts_with("S_"),
            "root plan positions map semantic seams to shape ids: {position} -> {shape}"
        );
    }
    assert_no_trash_authority(all_contract_strings());
}

#[test]
fn compiler2_transport_flow_telemetry_contract_names_the_output_signal() {
    assert_eq!(
        EVENT_NAME.join("."),
        "fz.compiler2.transport_flow.defined",
        "transport-flow construction should emit one plan-defined signal"
    );
    assert_eq!(
        MEASUREMENT_FIELDS,
        [
            "root_id",
            "semantic_revision",
            "executable_count",
            "transport_position_count",
            "shape_descriptor_count",
            "lane_descriptor_count",
            "callable_descriptor_count",
            "boundary_descriptor_count",
            "nothing_shape_count",
            "tuple_shape_count",
            "callable_shape_count",
            "direct_callable_count",
            "first_class_callable_count",
            "boundary_publication_count",
            "codegen_seam_fact_count",
            "codegen_function_entry_seam_fact_count",
            "codegen_block_param_seam_fact_count",
            "codegen_return_delivery_seam_fact_count",
            "codegen_continuation_entry_seam_fact_count",
            "codegen_tail_call_seam_fact_count",
            "codegen_callable_boundary_seam_fact_count",
            "codegen_extern_boundary_seam_fact_count",
            "codegen_first_class_publication_seam_fact_count",
        ],
        "measurements should make sharing, shape inventory, and seam coverage visible"
    );
    assert_eq!(
        METADATA_FIELDS,
        [
            "entry_executable_symbol",
            "executable_membership",
            "transport_positions",
            "shape_descriptors",
            "lane_descriptors",
            "callable_facts",
            "boundary_facts",
            "seam_facts",
        ],
        "metadata should carry inspectable facts, not reconstructed layout trees"
    );
    assert_no_trash_authority(
        EVENT_NAME
            .iter()
            .chain(MEASUREMENT_FIELDS)
            .chain(METADATA_FIELDS)
            .copied()
            .collect(),
    );
}

#[test]
fn compiler2_transport_flow_worked_example_is_emitted_by_the_production_boundary() {
    let source = r#"
fn add(x), do: fn (y) -> x + y end
fn apply1(f, x), do: f.(x)
fn pair(x), do: {x, add(x)}

fn main() do
  {n, f} = pair(41)
  apply1(f, n)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    let metadata_keys = Rc::new(RefCell::new(Vec::<Vec<&'static str>>::new()));
    let metadata_keys_in = metadata_keys.clone();
    tel.attach(EVENT_NAME, capture.handler());
    tel.attach(
        EVENT_NAME,
        Box::new(move |event: &crate::telemetry::handler::Event<'_, '_, '_>| {
            metadata_keys_in
                .borrow_mut()
                .push(event.metadata.iter().map(|(key, _)| *key).collect::<Vec<_>>());
        }),
    );
    let mut world = World::new(&tel);
    world.submit_code(Some("transport_worked_example.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "worked example should settle");

    let event = capture
        .last(EVENT_NAME)
        .unwrap_or_else(|| panic!("{} should be emitted", EVENT_NAME.join(".")));
    assert_eq!(
        event.name, EVENT_NAME,
        "worked example should emit the production transport-flow signal"
    );
    assert!(
        matches!(event.measurements.get("transport_position_count"), Some(Value::U64(count)) if *count >= 1),
        "worked example should report concrete transport positions: {:?}",
        event.measurements
    );
    assert!(
        matches!(event.measurements.get("codegen_seam_fact_count"), Some(Value::U64(_))),
        "transport derivation should report the seam fact count field: {:?}",
        event.measurements
    );
    let seen_keys = metadata_keys
        .borrow()
        .last()
        .cloned()
        .expect("worked example should record one transport-flow event");
    for field in METADATA_FIELDS {
        assert!(
            seen_keys.contains(field),
            "worked example transport metadata should include {field}"
        );
    }

    let plan = transport_plan(&world, root);
    let pair = executable_for(&world, &plan, "pair", 1);
    let main = executable_for(&world, &plan, "main", 0);
    let pair_return = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: pair });
    let main_resume = resume_shapes_for(&plan, &main)
        .into_iter()
        .find(|shape| *shape == pair_return)
        .unwrap_or_else(|| panic!("main should resume the tuple returned by pair/1: {:?}", plan.positions));
    assert_eq!(
        pair_return, main_resume,
        "pair/1 return and main/0 resume should share one ShapeId"
    );
    let ShapeDescr::Tuple(items) = shape_descr(&world, pair_return) else {
        panic!("pair/1 should return a tuple transport shape")
    };
    assert_eq!(items.len(), 2, "pair/1 should return two tuple fields");
}

#[test]
fn compiler2_transport_flow_publishes_seam_specific_codegen_facts() {
    let source = r#"
fn inc(x), do: x + 1.0

fn main() do
  y = inc(1.0)
  y + 2.0
end
"#;

    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    let seam_facts = Rc::new(RefCell::new(Vec::<String>::new()));
    let seam_facts_in = seam_facts.clone();
    tel.attach(EVENT_NAME, capture.handler());
    tel.attach(
        EVENT_NAME,
        Box::new(move |event: &crate::telemetry::handler::Event<'_, '_, '_>| {
            if let Some(Value::StrSeq(facts)) = event.metadata.get("seam_facts") {
                *seam_facts_in.borrow_mut() = facts.iter().cloned().collect();
            } else if let Some(facts) = event
                .metadata
                .get("seam_facts")
                .and_then(|value| value.downcast_ref::<Vec<String>>())
            {
                *seam_facts_in.borrow_mut() = facts.clone();
            }
        }),
    );
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_codegen_seam_float_resume.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "codegen seam fixture should settle");

    let event = capture
        .last(EVENT_NAME)
        .unwrap_or_else(|| panic!("{} should be emitted", EVENT_NAME.join(".")));
    assert!(
        matches!(event.measurements.get("codegen_seam_fact_count"), Some(Value::U64(count)) if *count > 0),
        "transport flow should report seam facts once fz-hwn.20.5 publishes them: {:?}",
        event.measurements
    );
    assert!(
        matches!(event.measurements.get("codegen_function_entry_seam_fact_count"), Some(Value::U64(count)) if *count > 0),
        "transport flow should count function-entry seam facts by kind: {:?}",
        event.measurements
    );
    assert!(
        matches!(event.measurements.get("codegen_block_param_seam_fact_count"), Some(Value::U64(count)) if *count > 0),
        "transport flow should count block-param seam facts by kind: {:?}",
        event.measurements
    );
    assert!(
        matches!(event.measurements.get("codegen_return_delivery_seam_fact_count"), Some(Value::U64(count)) if *count > 0),
        "transport flow should count return-delivery seam facts by kind: {:?}",
        event.measurements
    );
    assert!(
        matches!(event.measurements.get("codegen_continuation_entry_seam_fact_count"), Some(Value::U64(count)) if *count > 0),
        "transport flow should count continuation-entry seam facts by kind: {:?}",
        event.measurements
    );
    let plan = transport_plan(&world, root);
    let function_entry = plan
        .codegen_seam_facts
        .iter()
        .find(|fact| matches!(fact.seam, CodegenSeam::FunctionEntry { .. }) && fact.repr == CodegenLaneRepr::RawF64)
        .unwrap_or_else(|| {
            panic!(
                "float function-entry seam should use RawF64: {:?}",
                plan.codegen_seam_facts
            )
        });
    let block_param = plan
        .codegen_seam_facts
        .iter()
        .find(|fact| matches!(fact.seam, CodegenSeam::BlockParam { .. }) && fact.repr == CodegenLaneRepr::ValueRef)
        .unwrap_or_else(|| {
            panic!(
                "float block-param seam should use ValueRef: {:?}",
                plan.codegen_seam_facts
            )
        });
    assert_eq!(
        function_entry.lane, block_param.lane,
        "the same float LaneId should have seam-specific reprs without forking lane identity"
    );
    assert!(
        plan.codegen_seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::ReturnDelivery { .. }) && fact.repr == CodegenLaneRepr::RawF64),
        "a float-returning producer should publish a RawF64 return-delivery seam: {:?}",
        plan.codegen_seam_facts
    );
    assert!(
        plan.codegen_seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::ContinuationEntry { .. })
                && fact.repr == CodegenLaneRepr::ValueRef),
        "a non-tail float call should publish a ValueRef continuation-entry seam: {:?}",
        plan.codegen_seam_facts
    );
    let facts = seam_facts.borrow();
    assert!(
        facts
            .iter()
            .any(|fact| fact.contains("FunctionEntry") && fact.contains("RawF64")),
        "telemetry should expose the function-entry seam fact: {facts:?}"
    );
    assert!(
        facts
            .iter()
            .any(|fact| fact.contains("BlockParam") && fact.contains("ValueRef")),
        "telemetry should expose the block-param seam fact: {facts:?}"
    );
}

#[test]
fn compiler2_transport_flow_publishes_tail_call_codegen_seams() {
    let source = r#"
fn inc(x), do: x + 1.0
fn main(), do: inc(1.0)
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_codegen_seam_tail_call.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "tail-call seam fixture should settle");

    let plan = transport_plan(&world, root);
    assert!(
        plan.codegen_seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::TailCall { .. }) && fact.repr == CodegenLaneRepr::RawF64),
        "a tail float call should publish a RawF64 tail-call seam: {:?}",
        plan.codegen_seam_facts
    );
}

#[test]
fn compiler2_transport_flow_publishes_callable_boundary_codegen_seams() {
    let source = r#"
fn make(), do: fn (x) -> x + 1.0 end
fn main(), do: make()
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_codegen_seam_callable_boundary.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "callable-boundary seam fixture should settle");

    let plan = transport_plan(&world, root);
    assert!(
        plan.codegen_seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::CallableBoundary { .. })
                && fact.repr == CodegenLaneRepr::ValueRef),
        "a published callable boundary should expose ValueRef callable-boundary lane facts: {:?}",
        plan.codegen_seam_facts
    );
    assert!(
        plan.codegen_seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::FirstClassPublication { .. })
                && fact.repr == CodegenLaneRepr::ValueRef),
        "an escaped callable should expose ValueRef first-class-publication lane facts: {:?}",
        plan.codegen_seam_facts
    );
}

#[test]
fn compiler2_transport_flow_publishes_extern_boundary_codegen_seams() {
    let source = r#"
extern "C" fn fz_float_id(float) :: float
fn main(), do: fz_float_id(1.0)
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_codegen_seam_extern_boundary.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "extern-boundary seam fixture should settle");

    let plan = transport_plan(&world, root);
    assert!(
        plan.codegen_seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::ExternBoundary { .. }) && fact.repr == CodegenLaneRepr::RawF64),
        "a float extern should publish RawF64 extern-boundary lane facts: {:?}",
        plan.codegen_seam_facts
    );
}

#[test]
fn compiler2_transport_flow_publishes_tuple_codegen_seams_for_leaf_lanes() {
    let source = r#"
fn pair(x, y), do: {x, y}

fn main() do
  {left, right} = pair(1.0, 2)
  {left, right}
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_codegen_seam_tuple_leaf_lanes.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    assert_resolved(world.drive_for(None), "tuple seam fixture should settle");

    let plan = transport_plan(&world, root);
    let pair = executable_for(&world, &plan, "pair", 2);
    let pair_return = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableReturn {
            executable: pair.clone(),
        },
    );
    let leaf_lanes = shape_leaf_lanes(&world, pair_return);
    assert_eq!(
        leaf_lanes.len(),
        2,
        "the worked example should return a two-leaf tuple shape: {:?}",
        shape_descr(&world, pair_return)
    );

    assert_seam_fact(
        &plan,
        |seam| matches!(seam, CodegenSeam::ReturnDelivery { executable } if executable == &pair),
        Some(leaf_lanes[0].0),
        leaf_lanes[0].1,
        CodegenLaneRepr::RawF64,
        "float tuple leaves should publish raw return-delivery seam facts",
    );
    assert_seam_fact(
        &plan,
        |seam| matches!(seam, CodegenSeam::ReturnDelivery { executable } if executable == &pair),
        Some(leaf_lanes[1].0),
        leaf_lanes[1].1,
        CodegenLaneRepr::RawInt,
        "integer tuple leaves should publish raw return-delivery seam facts",
    );

    let main = executable_for(&world, &plan, "main", 0);
    assert_seam_fact(
        &plan,
        |seam| matches!(seam, CodegenSeam::BlockParam { executable, .. } if executable == &main),
        Some(leaf_lanes[0].0),
        leaf_lanes[0].1,
        CodegenLaneRepr::ValueRef,
        "float tuple leaves should enter continuation blocks as ValueRef",
    );
    assert_seam_fact(
        &plan,
        |seam| matches!(seam, CodegenSeam::BlockParam { executable, .. } if executable == &main),
        Some(leaf_lanes[1].0),
        leaf_lanes[1].1,
        CodegenLaneRepr::RawInt,
        "integer tuple leaves should enter continuation blocks as RawInt",
    );
}

#[test]
fn compiler2_transport_flow_publishes_integer_and_atom_codegen_reprs() {
    let source = r#"
fn id_int(x), do: x + 1
fn id_atom(x), do: x

fn main() do
  int_value = id_int(41)
  atom_value = id_atom(:ok)
  {int_value, atom_value}
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_codegen_seam_int_atom_reprs.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    assert_resolved(world.drive_for(None), "integer/atom seam fixture should settle");

    let plan = transport_plan(&world, root);
    let id_int = executable_for(&world, &plan, "id_int", 1);
    let id_atom = executable_for(&world, &plan, "id_atom", 1);

    assert!(
        plan.codegen_seam_facts.iter().any(|fact| matches!(
            &fact.seam,
            CodegenSeam::FunctionEntry { executable, .. } if executable == &id_int
        ) && fact.repr == CodegenLaneRepr::RawInt),
        "integer function entries should publish RawInt seam facts: {:?}",
        plan.codegen_seam_facts
    );
    assert!(
        plan.codegen_seam_facts.iter().any(|fact| matches!(
            &fact.seam,
            CodegenSeam::ReturnDelivery { executable } if executable == &id_int
        ) && fact.repr == CodegenLaneRepr::RawInt),
        "integer returns should publish RawInt seam facts: {:?}",
        plan.codegen_seam_facts
    );
    assert!(
        plan.codegen_seam_facts.iter().any(|fact| matches!(
            &fact.seam,
            CodegenSeam::FunctionEntry { executable, .. } if executable == &id_atom
        ) && fact.repr == CodegenLaneRepr::RawAtom),
        "atom function entries should publish RawAtom seam facts: {:?}",
        plan.codegen_seam_facts
    );
    assert!(
        plan.codegen_seam_facts.iter().any(|fact| matches!(
            &fact.seam,
            CodegenSeam::ReturnDelivery { executable } if executable == &id_atom
        ) && fact.repr == CodegenLaneRepr::RawAtom),
        "atom returns should publish RawAtom seam facts: {:?}",
        plan.codegen_seam_facts
    );
}

#[test]
fn compiler2_transport_flow_publishes_value_ref_codegen_reprs_for_boxed_internal_lanes() {
    let source = r#"
fn id_box(x), do: x

fn main() do
  y = id_box("hello")
  {y, 1}
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_codegen_seam_boxed_internal_reprs.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    assert_resolved(world.drive_for(None), "boxed internal seam fixture should settle");

    let plan = transport_plan(&world, root);
    let id_box = executable_for(&world, &plan, "id_box", 1);
    let id_box_return = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableReturn {
            executable: id_box.clone(),
        },
    );
    let leaf_lanes = shape_leaf_lanes(&world, id_box_return);
    let [(leaf_shape, lane)] = leaf_lanes.as_slice() else {
        panic!(
            "id_box/1 should return one boxed leaf lane, got {:?}",
            shape_descr(&world, id_box_return)
        )
    };

    assert_seam_fact(
        &plan,
        |seam| matches!(seam, CodegenSeam::FunctionEntry { executable, .. } if executable == &id_box),
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::ValueRef,
        "boxed function-entry lanes should publish ValueRef seam facts",
    );
    assert_seam_fact(
        &plan,
        |seam| matches!(seam, CodegenSeam::ReturnDelivery { executable } if executable == &id_box),
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::ValueRef,
        "boxed return-delivery lanes should publish ValueRef seam facts",
    );

    let main = executable_for(&world, &plan, "main", 0);
    assert_seam_fact(
        &plan,
        |seam| matches!(seam, CodegenSeam::BlockParam { executable, .. } if executable == &main),
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::ValueRef,
        "boxed continuation block params should publish ValueRef seam facts",
    );
    assert_seam_fact(
        &plan,
        |seam| matches!(seam, CodegenSeam::ContinuationEntry { executable, .. } if executable == &main),
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::ValueRef,
        "boxed continuation entries should publish ValueRef seam facts",
    );
}

#[test]
fn compiler2_transport_flow_publishes_value_ref_codegen_reprs_for_boxed_tail_and_extern_lanes() {
    let source = r#"
extern "C" fn fz_binary_id(binary) :: binary
fn main(), do: fz_binary_id("hello")
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_codegen_seam_boxed_tail_extern_reprs.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "boxed tail/extern seam fixture should settle");

    let plan = transport_plan(&world, root);
    let extern_id = executable_for(&world, &plan, "fz_binary_id", 1);
    let extern_return = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableReturn {
            executable: extern_id.clone(),
        },
    );
    let leaf_lanes = shape_leaf_lanes(&world, extern_return);
    let [(leaf_shape, lane)] = leaf_lanes.as_slice() else {
        panic!(
            "fz_binary_id/1 should return one boxed leaf lane, got {:?}",
            shape_descr(&world, extern_return)
        )
    };

    assert_seam_fact(
        &plan,
        |seam| matches!(seam, CodegenSeam::TailCall { .. }),
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::ValueRef,
        "boxed tail-call lanes should publish ValueRef seam facts",
    );
    assert_seam_fact(
        &plan,
        |seam| matches!(seam, CodegenSeam::ExternBoundary { executable } if executable == &extern_id),
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::ValueRef,
        "boxed extern-boundary lanes should publish ValueRef seam facts",
    );
}

#[test]
fn compiler2_transport_plan_maps_ignored_returns_to_nothing_once() {
    let source = r#"
fn ping(x), do: x + 1

fn main() do
  ping(41)
  :ok
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(Some("transport_ignore.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "ignored-return fixture should settle");

    let plan = transport_plan(&world, root);
    let ping = executable_for(&world, &plan, "ping", 1);
    let ping_return = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: ping });
    assert!(
        matches!(shape_descr(&world, ping_return), ShapeDescr::Nothing),
        "ignored callee returns should collapse to Shape::Nothing at transport derivation"
    );
}

#[test]
fn compiler2_transport_plan_shares_direct_callable_return_and_resume_shapes() {
    let source = r#"
fn apply1(f, x), do: f.(x)
fn make_adder(a), do: fn (x) -> x + a end

fn main() do
  f = make_adder(1)
  apply1(f, 41)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(Some("transport_direct_callable.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "direct-callable fixture should settle");

    let plan = transport_plan(&world, root);
    let make_adder = executable_for(&world, &plan, "make_adder", 1);
    let main = executable_for(&world, &plan, "main", 0);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: make_adder });
    let resumed = resume_shapes_for(&plan, &main)
        .into_iter()
        .find(|shape| *shape == returned)
        .unwrap_or_else(|| panic!("main should resume the direct callable returned by make_adder/1"));
    assert_eq!(
        returned, resumed,
        "direct callable return and resume positions should share one ShapeId"
    );
    assert!(
        matches!(shape_descr(&world, returned), ShapeDescr::Callable(_)),
        "direct callable return should materialize as a callable shape"
    );
}

#[test]
fn compiler2_transport_plan_keeps_unused_callable_construction_out_of_boundary_inventory() {
    let source = r#"
fn make(), do: fn (x) -> x + 1 end

fn main() do
  make()
  :ok
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(Some("transport_unused_callable.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "unused callable fixture should settle");

    let plan = transport_plan(&world, root);
    assert_eq!(
        plan.boundaries.len(),
        0,
        "a constructed-but-unused callable should not publish any boundary contract"
    );
}

#[test]
fn compiler2_transport_plan_tracks_direct_lambda_use_without_boundary_publication() {
    let source = r#"
fn main() do
  add1 = fn (x) -> x + 1 end
  add1.(1)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(Some("transport_direct_lambda_use.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "direct lambda fixture should settle");

    let plan = transport_plan(&world, root);
    let main = executable_for(&world, &plan, "main", 0);
    let callable_shapes = plan
        .positions
        .iter()
        .filter_map(|(position, shape)| match position {
            TransportPosition::Value {
                executable: candidate, ..
            } if candidate == &main && matches!(shape_descr(&world, *shape), ShapeDescr::Callable(_)) => Some(*shape),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        !callable_shapes.is_empty(),
        "direct lambda use should keep a callable shape in the root plan"
    );
    assert_eq!(
        plan.boundaries.len(),
        0,
        "a direct-only lambda path should not publish a first-class boundary"
    );
}

#[test]
fn compiler2_transport_plan_requires_a_boundary_for_an_escaped_lambda() {
    let source = r#"
fn make(), do: fn (x) -> x + 1 end
fn main(), do: make()
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(Some("transport_escaped_lambda.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "escaped lambda fixture should settle");

    let plan = transport_plan(&world, root);
    let make = executable_for(&world, &plan, "make", 0);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: make });
    assert!(
        matches!(shape_descr(&world, returned), ShapeDescr::Callable(_)),
        "escaped lambda should still be a callable shape in the transport plan"
    );
    assert_eq!(
        plan.boundaries.len(),
        1,
        "escaping a lambda as a returned callable should publish exactly one boundary contract"
    );
}

#[test]
fn compiler2_transport_plan_requires_a_boundary_for_an_opaque_callable_input() {
    let source = "fn main(f), do: f.(1)\n";

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_opaque_callable_input.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "opaque callable input fixture should settle");

    let plan = transport_plan(&world, root);
    let main = executable_for(&world, &plan, "main", 1);
    let input_shape = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableInput {
            executable: main,
            semantic_index: 0,
        },
    );
    assert!(
        matches!(shape_descr(&world, input_shape), ShapeDescr::Callable(_)),
        "a callable input with opaque closure-call demand should stay callable-shaped, not collapse to a value lane"
    );
    assert_eq!(
        plan.boundaries.len(),
        1,
        "an opaque callable input should publish one explicit boundary contract"
    );
}

#[test]
fn compiler2_transport_plan_keeps_opaque_callable_contracts_distinct_by_surface() {
    let source = r#"
fn main(f, g) do
  f.(1)
  g.({1, 2})
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_distinct_opaque_callable_surfaces.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 2, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "distinct opaque-callable fixture should settle");

    let plan = transport_plan(&world, root);
    let main = executable_for(&world, &plan, "main", 2);
    let first = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableInput {
            executable: main.clone(),
            semantic_index: 0,
        },
    );
    let second = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableInput {
            executable: main,
            semantic_index: 1,
        },
    );
    let ShapeDescr::Callable(first_callable) = shape_descr(&world, first) else {
        panic!("first opaque input should be callable-shaped")
    };
    let ShapeDescr::Callable(second_callable) = shape_descr(&world, second) else {
        panic!("second opaque input should be callable-shaped")
    };
    assert_ne!(
        first_callable, second_callable,
        "opaque callable contracts with different observed surfaces must not merge into one CallableId"
    );
}

#[test]
fn compiler2_transport_plan_distinguishes_same_surface_callables_by_capture_obligation() {
    let source = r#"
fn make1(a), do: fn (x) -> x + a end
fn make2(a, b), do: fn (x) -> x + a + b end

fn main(), do: {make1(1), make2(1, 2)}
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_same_surface_distinct_captures.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    assert_resolved(world.drive_for(None), "same-surface callable fixture should settle");

    let plan = transport_plan(&world, root);
    let main = executable_for(&world, &plan, "main", 0);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: main });
    let ShapeDescr::Tuple(items) = shape_descr(&world, returned) else {
        panic!("main/0 should return a tuple of callable values")
    };
    let [left, right] = items.as_ref() else {
        panic!("main/0 should return exactly two callable tuple fields")
    };
    let ShapeDescr::Callable(left) = shape_descr(&world, *left) else {
        panic!("first tuple field should be callable-shaped")
    };
    let ShapeDescr::Callable(right) = shape_descr(&world, *right) else {
        panic!("second tuple field should be callable-shaped")
    };
    assert_ne!(
        left, right,
        "two same-surface callables with different capture obligations must stay distinguishable"
    );
}

#[test]
fn compiler2_transport_plan_publishes_callable_argument_lanes_at_boundaries() {
    let source = r#"
fn main(f) do
  g = fn (x) -> x + 1 end
  f.(g)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_boundary_callable_arg.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    drive_until_transport_plan(
        &mut world,
        root,
        "callable boundary-arg fixture should produce a transport plan",
    );

    let plan = transport_plan(&world, root);
    let boundary = boundary_with_callable_arg(&world, &plan);
    let [arg_shape] = boundary.surface_arg_shapes.as_ref() else {
        panic!("f/1 boundary should publish one surface argument shape")
    };
    assert!(
        matches!(shape_descr(&world, *arg_shape), ShapeDescr::Callable(_)),
        "the published boundary argument should preserve the callable shape"
    );
    assert_eq!(
        boundary.published_arg_lanes.len(),
        1,
        "a callable argument crossing a boundary should be boxed into one published lane"
    );
}

#[test]
fn compiler2_transport_plan_preserves_tuple_return_contracts_at_boundaries() {
    let source = r#"
fn make_pairer(), do: fn (x) -> {{1, 2}, 3} end
fn main(), do: make_pairer()
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_boundary_tuple_return.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "tuple-return boundary fixture should settle");

    let plan = transport_plan(&world, root);
    let boundary = single_boundary_descr(&world, &plan);
    let ShapeDescr::Tuple(items) = shape_descr(&world, boundary.published_return_shape) else {
        panic!(
            "a callable returning a tuple should publish the return ShapeId, got {:?}",
            shape_descr(&world, boundary.published_return_shape)
        );
    };
    let [left, right] = items.as_ref() else {
        panic!("the boundary return should preserve the outer two-field tuple")
    };
    assert!(
        matches!(shape_descr(&world, *left), ShapeDescr::Tuple(inner) if inner.len() == 2),
        "the boundary return shape should preserve nested tuple structure instead of flattening lanes: {:?}",
        shape_descr(&world, boundary.published_return_shape)
    );
    assert!(
        matches!(shape_descr(&world, *right), ShapeDescr::Lane(_)),
        "the second outer field should remain a scalar shape: {:?}",
        shape_descr(&world, boundary.published_return_shape)
    );
    assert_eq!(
        boundary.published_return_lanes.len(),
        3,
        "the separate lane fact should flatten the three scalar leaves without becoming the return structure"
    );
}

#[test]
fn compiler2_transport_plan_keeps_direct_surfaces_when_a_callable_also_escapes() {
    let source = r#"
fn main() do
  add1 = fn (x) -> x + 1 end
  add1.(1)
  add1
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_direct_and_escaped_callable.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(
        world.drive_for(None),
        "direct-and-escaped callable fixture should settle",
    );

    let plan = transport_plan(&world, root);
    let main = executable_for(&world, &plan, "main", 0);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: main });
    let ShapeDescr::Callable(callable) = shape_descr(&world, returned) else {
        panic!("main/0 should return the callable value it also invoked directly")
    };
    let facts = plan
        .callables
        .get(callable)
        .unwrap_or_else(|| panic!("returned callable facts should be present"));
    assert!(
        !facts.direct_surfaces.is_empty(),
        "direct-call surfaces must remain visible even when the same callable also escapes"
    );
    assert!(
        !facts.boundary_ids.is_empty(),
        "the escaped callable should still publish a first-class boundary"
    );
}

#[test]
fn compiler2_transport_plan_shapes_callable_captures_from_settled_callable_demand() {
    let source = r#"
fn main() do
  add1 = fn (x) -> x + 1 end
  outer = fn (y) -> add1.(y) end
  outer.(41)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_callable_capture_demand.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_until_transport_plan(&mut world, root, "callable capture-demand fixture should settle");

    let plan = transport_plan(&world, root);
    let captured_callable = plan
        .callables
        .iter()
        .find_map(|(outer, _)| {
            let outer_descr = world.transport().interners().callable(*outer);
            let [capture_shape] = outer_descr.capture_shapes.as_ref() else {
                return None;
            };
            let ShapeDescr::Callable(captured) = shape_descr(&world, *capture_shape) else {
                return None;
            };
            Some(*captured)
        })
        .unwrap_or_else(|| {
            panic!(
                "outer direct callable should capture add1 as a callable shape: {:?}",
                plan.callables
            )
        });
    let captured_facts = plan
        .callables
        .get(&captured_callable)
        .unwrap_or_else(|| panic!("captured callable facts should be present"));
    assert!(
        !captured_facts.direct_surfaces.is_empty(),
        "the captured callable should keep its direct-call surface"
    );
    assert!(
        captured_facts.boundary_ids.is_empty(),
        "a callable captured for direct use must not be upgraded to a first-class boundary"
    );
}

#[test]
fn compiler2_transport_plan_preserves_recursive_callable_return_identity() {
    let source = r#"
fn make(0), do: fn (x) -> x + 1 end
fn make(n), do: make(n - 1)

fn main() do
  f = make(2)
  f.(41)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_recursive_callable_return.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_until_transport_plan(
        &mut world,
        root,
        "recursive callable-return fixture should produce a transport plan",
    );

    let plan = transport_plan(&world, root);
    let make = executable_for(&world, &plan, "make", 1);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: make });
    let ShapeDescr::Callable(callable) = shape_descr(&world, returned) else {
        panic!("recursive make/1 should return a callable shape")
    };
    let facts = plan
        .callables
        .get(callable)
        .unwrap_or_else(|| panic!("recursive callable return facts should be present"));
    assert!(
        !facts.resolutions.is_empty(),
        "recursive callable return should keep the resolved local callable target instead of falling back to a generic opaque callable"
    );
}

#[test]
fn compiler2_transport_plan_preserves_capture_lane_order_and_duplicates() {
    let source = r#"
fn make(a, b), do: fn (x) -> a + b + x end
fn main(), do: make(1, 2)
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_duplicate_capture_lanes.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "duplicate capture-lane fixture should settle");

    let plan = transport_plan(&world, root);
    let make = executable_for(&world, &plan, "make", 2);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: make });
    let ShapeDescr::Callable(callable) = shape_descr(&world, returned) else {
        panic!("make/2 should return a callable shape")
    };
    let facts = plan
        .callables
        .get(callable)
        .unwrap_or_else(|| panic!("returned callable facts should be present"));
    assert_eq!(
        facts.capture_lanes.len(),
        2,
        "two same-typed captures are two ordered payload lanes, not one deduplicated lane"
    );
    let boundary = single_boundary_descr(&world, &plan);
    assert_eq!(
        boundary.published_capture_lanes.as_ref(),
        facts.capture_lanes.as_ref(),
        "published capture lanes must preserve the callable capture payload sequence exactly"
    );
}

#[test]
fn compiler2_transport_plan_does_not_publish_synthetic_boundary_positions() {
    let source = r#"
fn main(f) do
  g = fn (x) -> x + 1 end
  f.(g)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_no_synthetic_boundary_position.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    drive_until_transport_plan(
        &mut world,
        root,
        "callable boundary-arg fixture should produce a transport plan",
    );

    let plan = transport_plan(&world, root);
    for facts in plan.boundaries.values() {
        for publication in facts.publications.iter() {
            assert!(
                transport_position_is_semantic(publication),
                "boundary publications must name semantic positions, not synthetic self-positions: {publication:?}"
            );
        }
    }
}

#[test]
fn compiler2_transport_plan_is_rederived_when_missing_after_unchanged_semantic_closure() {
    let source = "fn main(), do: 41\n";

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_missing_plan_rederive.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "missing-plan fixture should initially settle");
    assert!(
        world.transport().plans().get(root).is_some(),
        "initial drive should produce a transport plan"
    );

    world.transport_mut().plans_mut().remove(root);
    world.demand(super::Job::SealSemanticClosure(root));
    assert_resolved(
        world.drive_for(None),
        "unchanged semantic closure should still rederive a missing transport plan",
    );
    assert!(
        world.transport().plans().get(root).is_some(),
        "transport plan should be restored even when SemanticClosed did not change"
    );
}

#[test]
fn compiler2_transport_plan_publishes_boundary_returns_per_surface() {
    let source = r#"
fn main() do
  id = fn (x) -> x end
  id.(1)
  id.({1, 2})
  id
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_surface_specific_boundary_returns.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(
        world.drive_for(None),
        "surface-specific boundary-return fixture should settle",
    );

    let plan = transport_plan(&world, root);
    assert_eq!(
        plan.boundaries.len(),
        2,
        "one escaped callable used at two surfaces should publish one boundary contract per surface"
    );
    let mut has_scalar_return = false;
    let mut has_tuple_return = false;
    for boundary in boundary_descrs(&world, &plan) {
        match shape_descr(&world, boundary.published_return_shape) {
            ShapeDescr::Lane(_) => has_scalar_return = true,
            ShapeDescr::Tuple(items) if items.len() == 2 => has_tuple_return = true,
            other => panic!("unexpected boundary return shape for surface-specific fixture: {other:?}"),
        }
    }
    assert!(
        has_scalar_return && has_tuple_return,
        "boundary return shape must follow each surface instead of joining all surfaces into one fallback"
    );
}

#[test]
fn compiler2_transport_plan_shares_recursive_return_and_resume_shapes() {
    let source = r#"
fn pair_down(0), do: {0, 1}
fn pair_down(n) do
  {left, right} = pair_down(n - 1)
  {left, right}
end

fn main() do
  {left, right} = pair_down(2)
  left + right
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_recursive_tuple_return.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive_for(None), "recursive tuple-return fixture should settle");

    let plan = transport_plan(&world, root);
    let pair_down = executable_for(&world, &plan, "pair_down", 1);
    let returned = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableReturn {
            executable: pair_down.clone(),
        },
    );
    let recursive_resume = resume_shapes_for(&plan, &pair_down)
        .into_iter()
        .find(|shape| *shape == returned)
        .unwrap_or_else(|| panic!("recursive pair_down/1 call should resume the same shape it returns"));
    assert_eq!(
        returned, recursive_resume,
        "recursive producer return and recursive consumer resume should share one ShapeId"
    );
    assert!(
        matches!(shape_descr(&world, returned), ShapeDescr::Tuple(items) if items.len() == 2),
        "settled recursive tuple demand should remain a tuple transport shape"
    );
}

#[test]
fn compiler2_transport_plan_keeps_enum_reduce_operator_refs_direct_callable() {
    let source = r#"
fn main() do
  {
    Enum.reduce([1, 2, 3], 0, &Kernel.+/2),
    Enum.reduce([1, 2, 3], 0, &+/2)
  }
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_enum_reduce_operator_refs.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    drive_until_transport_plan(
        &mut world,
        root,
        "Enum.reduce operator-ref fixture should produce a transport plan",
    );

    let plan = transport_plan(&world, root);
    let kernel_plus = executable_for(&world, &plan, "+", 2);
    let plus_callables = callable_facts_for_function(&world, &plan, "+", 2);
    assert!(
        !plus_callables.is_empty(),
        "qualified and bare operator refs should produce callable facts for Kernel.+/2"
    );
    assert!(
        plus_callables
            .iter()
            .any(|(_, facts)| facts.resolutions.iter().any(|resolution| resolution == &kernel_plus)),
        "operator refs should resolve to the Kernel.+/2 executable, not a boxed value lane: {:?}",
        plan.callables
    );
    assert!(
        plus_callables
            .iter()
            .any(|(_, facts)| facts.direct_surfaces.iter().any(|surface| surface.len() == 2)),
        "Enum.reduce should demand the reducer as a direct two-argument callable surface: {:?}",
        plan.callables
    );
    assert!(
        plus_callables.iter().all(|(_, facts)| facts.boundary_ids.is_empty()),
        "operator refs used only as Enum.reduce reducers should not publish first-class boundaries"
    );

    let main = executable_for(&world, &plan, "main", 0);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: main });
    let ShapeDescr::Tuple(items) = shape_descr(&world, returned) else {
        panic!("main/0 should return the two reduced integer results as a tuple")
    };
    assert_eq!(items.len(), 2, "main/0 should return one field per reduce call");
    assert!(
        shape_leaf_lanes(&world, returned)
            .iter()
            .all(|(_, lane)| world.types().is_integer(&world.transport().interners().lane(*lane).ty)),
        "both reduce results should stay on integer transport lanes"
    );
}

#[test]
fn compiler2_transport_plan_keeps_joined_enum_reduce_reducer_callable_shaped() {
    let source = r#"
fn add_a(x, acc), do: acc + x
fn add_b(x, acc), do: acc + x

fn main(flag) do
  reducer = case flag do
    true -> add_a
    _ -> add_b
  end

  Enum.reduce([1, 2, 3], 0, reducer)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_enum_reduce_joined_reducer.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    drive_until_transport_plan(
        &mut world,
        root,
        "joined Enum.reduce reducer fixture should produce a transport plan",
    );

    let plan = transport_plan(&world, root);
    assert!(
        plan.executable_membership.iter().any(|executable| function_is(
            &world,
            executable.activation.function,
            "add_a",
            2
        )),
        "the joined reducer frontier should keep add_a/2 live"
    );
    assert!(
        plan.executable_membership.iter().any(|executable| function_is(
            &world,
            executable.activation.function,
            "add_b",
            2
        )),
        "the joined reducer frontier should keep add_b/2 live"
    );

    let reducer_arg_shapes = plan
        .positions
        .iter()
        .filter_map(|(position, shape)| match position {
            TransportPosition::CallArg { semantic_index: 2, .. }
                if matches!(shape_descr(&world, *shape), ShapeDescr::Callable(_)) =>
            {
                Some(*shape)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        !reducer_arg_shapes.is_empty(),
        "the third Enum.reduce argument should be transported as a callable shape, not a scalar lane: {:?}",
        plan.positions
    );
    assert!(
        reducer_arg_shapes.iter().any(|shape| {
            let ShapeDescr::Callable(callable) = shape_descr(&world, *shape) else {
                return false;
            };
            plan.callables.get(callable).is_some_and(|facts| {
                facts.direct_surfaces.iter().any(|surface| surface.len() == 2) && facts.boundary_ids.is_empty()
            })
        }),
        "the joined reducer should retain a direct two-argument callable surface without becoming a boundary"
    );
}

#[test]
fn compiler2_transport_plan_preserves_callable_capture_inside_enum_style_reducer() {
    let source = r#"
fn reduce_plain([], acc, _reducer), do: acc
fn reduce_plain([head | tail], acc, reducer), do: reduce_plain(tail, reducer.(head, acc), reducer)

fn count_via_param(enumerable, fun) do
  reduce_plain(enumerable, 0, fn (entry, acc) ->
    if fun.(entry), do: acc + 1, else: acc
  end)
end

fn main() do
  predicate = fn (x) -> x > 2 end
  count_via_param([1, 2, 3, 4], predicate)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_enum_style_reducer_captures_callable.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    drive_until_transport_plan(
        &mut world,
        root,
        "enum-style reducer callable-capture fixture should produce a transport plan",
    );

    let plan = transport_plan(&world, root);
    let captured_callable = plan.callables.iter().find_map(|(outer, facts)| {
        let outer_descr = world.transport().interners().callable(*outer);
        let [capture_shape] = outer_descr.capture_shapes.as_ref() else {
            return None;
        };
        let ShapeDescr::Callable(captured) = shape_descr(&world, *capture_shape) else {
            return None;
        };
        (!facts.direct_surfaces.is_empty() && facts.capture_lanes.len() == 1).then_some(*captured)
    });
    let captured_callable =
        captured_callable.unwrap_or_else(|| panic!("the reducer lambda should capture predicate as a callable shape"));
    let captured_facts = plan
        .callables
        .get(&captured_callable)
        .unwrap_or_else(|| panic!("captured predicate callable facts should be present"));
    assert!(
        captured_facts.direct_surfaces.iter().any(|surface| surface.len() == 1),
        "the captured predicate should retain its direct one-argument callable surface"
    );
    assert!(
        captured_facts.boundary_ids.is_empty(),
        "a predicate captured for direct reducer use should not be upgraded to a first-class boundary"
    );
}

fn assert_resolved(outcome: DriveOutcome<super::Job, super::FactKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

fn drive_until_transport_plan(world: &mut World<'_>, root: super::RootId, message: &str) {
    world.demand(super::Job::DeriveTransportPlan(root));
    let mut ran = 0;
    while world.transport().plans().get(root).is_none() && ran < 10_000 {
        let Some(job) = world.work_graph.pop() else {
            break;
        };
        if is_post_transport_consumer_for_root(&job, root) {
            continue;
        }
        let effects = super::jobs::run(world, &job).unwrap_or_else(|_| {
            panic!("{message}; prerequisite job failed before transport plan was derived: {job:?}")
        });
        world.complete_job(job, effects);
        ran += 1;
    }
    assert!(
        world.transport().plans().get(root).is_some(),
        "{message}; transport plan was not produced after {ran} prerequisite jobs; pending={}; unresolved={:?}",
        world.work_graph.pending_jobs(),
        world.work_graph.unresolved()
    );
}

fn is_post_transport_consumer_for_root(job: &super::Job, root: super::RootId) -> bool {
    matches!(
        job,
        super::Job::MaterializeRoot(candidate)
            | super::Job::DeriveAbiReady(candidate)
            | super::Job::DeriveEmissionReady(candidate)
            | super::Job::LowerBackendProgram(candidate)
            | super::Job::LowerNativeProgram(candidate)
            if *candidate == root
    )
}

fn executable_for(
    world: &World<'_>,
    plan: &TransportPlan,
    name: &str,
    arity: usize,
) -> super::transport::ExecutableSymbol {
    plan.executable_membership
        .iter()
        .find(|symbol| {
            let function_ref = world.function_ref(symbol.activation.function);
            function_ref.name == name && function_ref.arity == arity
        })
        .cloned()
        .unwrap_or_else(|| panic!("transport plan executable {name}/{arity}"))
}

fn callable_facts_for_function<'a>(
    world: &'a World<'_>,
    plan: &'a TransportPlan,
    name: &str,
    arity: usize,
) -> Vec<(super::transport::CallableId, &'a super::transport::CallableFacts)> {
    plan.callables
        .iter()
        .filter_map(|(callable, facts)| {
            let descr = world.transport().interners().callable(*callable);
            let function = descr.function?;
            function_is(world, function, name, arity).then_some((*callable, facts))
        })
        .collect()
}

fn function_is(world: &World<'_>, function: super::FunctionId, name: &str, arity: usize) -> bool {
    let function_ref = world.function_ref(function);
    function_ref.name == name && function_ref.arity == arity
}

fn transport_plan(world: &World<'_>, root: super::RootId) -> TransportPlan {
    world
        .transport()
        .plans()
        .get(root)
        .cloned()
        .unwrap_or_else(|| panic!("transport plan for root {}", root.as_u32()))
}

fn resume_shapes_for(plan: &TransportPlan, executable: &super::transport::ExecutableSymbol) -> Vec<ShapeId> {
    plan.positions
        .iter()
        .filter_map(|(position, shape)| match position {
            TransportPosition::ResumePayload {
                executable: candidate, ..
            } if candidate == executable => Some(*shape),
            _ => None,
        })
        .collect()
}

fn plan_shape_at(plan: &TransportPlan, position: &TransportPosition) -> ShapeId {
    *plan
        .positions
        .get(position)
        .unwrap_or_else(|| panic!("transport position should exist: {position:?}"))
}

fn shape_descr<'a>(world: &'a World<'_>, shape: ShapeId) -> &'a ShapeDescr {
    world.transport().interners().shape(shape)
}

fn shape_leaf_lanes(world: &World<'_>, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
    match shape_descr(world, shape) {
        ShapeDescr::Nothing | ShapeDescr::Callable(_) => Vec::new(),
        ShapeDescr::Lane(lane) => vec![(shape, *lane)],
        ShapeDescr::Tuple(items) => items
            .iter()
            .copied()
            .flat_map(|item| shape_leaf_lanes(world, item))
            .collect(),
    }
}

fn assert_seam_fact(
    plan: &TransportPlan,
    seam_matches: impl Fn(&CodegenSeam) -> bool,
    shape: Option<ShapeId>,
    lane: LaneId,
    repr: CodegenLaneRepr,
    intent: &str,
) {
    assert!(
        plan.codegen_seam_facts
            .iter()
            .any(|fact| { seam_matches(&fact.seam) && fact.shape == shape && fact.lane == lane && fact.repr == repr }),
        "{intent}: expected shape {shape:?}, lane {lane:?}, repr {repr:?}; facts: {:?}",
        plan.codegen_seam_facts
    );
}

fn transport_position_is_semantic(position: &TransportPosition) -> bool {
    match position {
        TransportPosition::ExecutableInput { .. }
        | TransportPosition::ExecutableReturn { .. }
        | TransportPosition::ResumePayload { .. }
        | TransportPosition::CallArg { .. }
        | TransportPosition::EntryCapture { .. }
        | TransportPosition::Value { .. } => true,
    }
}

fn single_boundary_descr<'a>(world: &'a World<'_>, plan: &TransportPlan) -> &'a BoundaryDescr {
    let boundaries = plan.boundaries.keys().copied().collect::<Vec<_>>();
    let [boundary] = boundaries.as_slice() else {
        panic!(
            "fixture should publish exactly one boundary contract: {:?}",
            plan.boundaries
        )
    };
    world.transport().interners().boundary(*boundary)
}

fn boundary_with_callable_arg<'a>(world: &'a World<'_>, plan: &TransportPlan) -> &'a BoundaryDescr {
    plan.boundaries
        .keys()
        .map(|boundary| world.transport().interners().boundary(*boundary))
        .find(|boundary| {
            boundary
                .surface_arg_shapes
                .iter()
                .any(|shape| matches!(shape_descr(world, *shape), ShapeDescr::Callable(_)))
        })
        .unwrap_or_else(|| {
            panic!(
                "fixture should publish a boundary with a callable argument: {:?}",
                plan.boundaries
            )
        })
}

fn boundary_descrs<'a>(world: &'a World<'_>, plan: &TransportPlan) -> Vec<&'a BoundaryDescr> {
    plan.boundaries
        .keys()
        .map(|boundary| world.transport().interners().boundary(*boundary))
        .collect()
}

fn shape(id: &str) -> Option<&'static str> {
    SHAPE_DESCRIPTORS
        .iter()
        .find_map(|(candidate, descr)| (*candidate == id).then_some(*descr))
}

fn callable(id: &str) -> Option<&'static str> {
    CALLABLE_FACTS
        .iter()
        .find_map(|(candidate, facts)| (*candidate == id).then_some(*facts))
}

fn boundary(id: &str) -> Option<&'static str> {
    BOUNDARY_FACTS
        .iter()
        .find_map(|(candidate, facts)| (*candidate == id).then_some(*facts))
}

fn position_shape(position: &str) -> Option<&'static str> {
    TRANSPORT_POSITIONS
        .iter()
        .find_map(|(candidate, shape)| (*candidate == position).then_some(*shape))
}

fn assert_descriptor_is_shareable(name: &str, descr: &str) {
    for forbidden in ["Root(", "ValueId", "callsite", "resume"] {
        assert!(
            !name.contains(forbidden) && !descr.contains(forbidden),
            "descriptor identity must not contain root-relative evidence: {name} = {descr}"
        );
    }
}

fn assert_no_trash_authority(facts: Vec<&str>) {
    for fact in facts {
        assert!(
            !fact.contains("Trash") && !fact.contains("ArgRepr"),
            "the pure transport contract must not depend on old layout or repr authority: {fact}"
        );
    }
}

fn all_contract_strings() -> Vec<&'static str> {
    let mut out = Vec::new();
    out.extend(EVENT_NAME.iter().copied());
    out.extend(MEASUREMENT_FIELDS.iter().copied());
    out.extend(METADATA_FIELDS.iter().copied());
    out.extend(SHAPE_DESCRIPTORS.iter().flat_map(|(name, descr)| [*name, *descr]));
    out.extend(LANE_DESCRIPTORS.iter().flat_map(|(name, descr)| [*name, *descr]));
    out.extend(CALLABLE_FACTS.iter().flat_map(|(name, facts)| [*name, *facts]));
    out.extend(BOUNDARY_FACTS.iter().flat_map(|(name, facts)| [*name, *facts]));
    out.extend(ROOT_PLAN_MEMBERSHIP.iter().copied());
    out.extend(
        TRANSPORT_POSITIONS
            .iter()
            .flat_map(|(position, shape)| [*position, *shape]),
    );
    out.extend(SEAM_FACTS.iter().flat_map(|(seam, facts)| [*seam, *facts]));
    out
}
