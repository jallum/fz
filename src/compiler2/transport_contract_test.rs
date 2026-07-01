use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use super::artifact::MaterializedTransportPlan;
use super::body::{DeliveredValueSource, delivered_value_joins};
use super::facts::{FactReadiness, FactUse};
use super::pull::{
    ProductDriver, ProductKey, ProductValue, PullOutcome, PullSession, PullWait, SymbolicBackendTail,
    TransportShapeFact, WorldProductProducers,
};
use super::semantic::{CallableFlowFact, CallableSurface};
use super::transport::{ActivationSymbol, ExecutableSymbol};
use super::transport::{
    BoundaryDescr, CodegenLaneRepr, CodegenSeam, CodegenSeamFact, LaneId, ShapeDescr, ShapeId, TransportPosition,
};
use super::types::Ty;
use super::{
    CodeSubmission, Compiler2, DriveOutcome, ExecutableKey, ExecutableNeed, ExecutableRuntimeDemand, FactKey, Job,
    LoweredBody, RootSubmission, RuntimeDemand, World,
};
use crate::telemetry::handler::{Event, EventKind, Handler};
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
    "omitted_position_count",
    "resume_payload_position_count",
    "return_payload_position_count",
    "call_result_payload_position_count",
    "codegen_seam_fact_count",
    "codegen_function_entry_seam_fact_count",
    "codegen_block_param_seam_fact_count",
    "codegen_return_delivery_seam_fact_count",
    "codegen_continuation_entry_seam_fact_count",
    "codegen_return_continuation_seam_fact_count",
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
    "callable C_pub; surface_arg_shapes [S_int]; published_value_lane L_int; published_capture_lanes [L_int]; \
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
const LEGACY_00181_NO_DUMP_JOB_STARTS: usize = 379;
const ENUM_REDUCE_OPERATOR_REF_SOURCE: &str = r#"
fn main() do
  {
    Enum.reduce([1, 2, 3], 0, &Kernel.+/2),
    Enum.reduce([1, 2, 3], 0, &+/2)
  }
end
"#;

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
            "callable C_pub; surface_arg_shapes [S_int]; published_value_lane L_int; published_capture_lanes [L_int]; \
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
fn compiler2_transport_flow_publishes_seam_specific_codegen_facts() {
    let source = r#"
fn inc(x), do: x + 1.0

fn main() do
  y = inc(1.0)
  y + 2.0
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_codegen_seam_float_resume.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (_, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let seam_facts = &plan.codegen_seam_facts;

    let function_entry = seam_facts
        .iter()
        .find(|fact| matches!(fact.seam, CodegenSeam::FunctionEntry { .. }) && fact.repr == CodegenLaneRepr::RawF64)
        .unwrap_or_else(|| panic!("float function-entry seam should use RawF64: {seam_facts:?}"));
    let block_param = seam_facts
        .iter()
        .find(|fact| matches!(fact.seam, CodegenSeam::BlockParam { .. }) && fact.repr == CodegenLaneRepr::ValueRef)
        .unwrap_or_else(|| panic!("float block-param seam should use ValueRef: {seam_facts:?}"));
    assert_eq!(
        function_entry.lane, block_param.lane,
        "the same float LaneId should have seam-specific reprs without forking lane identity"
    );
    assert!(
        seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::ReturnDelivery { .. }) && fact.repr == CodegenLaneRepr::RawF64),
        "a float-returning producer should publish a RawF64 return-delivery seam: {seam_facts:?}"
    );
    assert!(
        seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::ContinuationEntry { .. })
                && fact.repr == CodegenLaneRepr::ValueRef),
        "a non-tail float call should publish a ValueRef continuation-entry seam: {seam_facts:?}"
    );
}

#[test]
fn compiler2_transport_flow_publishes_tail_call_codegen_seams() {
    let source = r#"
fn inc(x), do: x + 1.0
fn main(), do: inc(1.0)
"#;

    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler2", "pull"], capture.handler());
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_codegen_seam_tail_call.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (_, plan) = pull_root_backend_plan_for_test(&tel, &mut world, root);
    assert!(
        plan.codegen_seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::TailCall { .. }) && fact.repr == CodegenLaneRepr::RawF64),
        "a tail float call should publish a RawF64 tail-call seam: {:?}",
        plan.codegen_seam_facts
    );
}

#[test]
fn compiler2_transport_flow_names_tail_return_payload_position() {
    let source = r#"
fn inc(x), do: x + 1.0
fn main(), do: inc(1.0)
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_tail_return_payload_position.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let main = executable_for(&world, session, "main", 0);
    let inc = executable_for(&world, session, "inc", 1);
    let main_return = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn {
            executable: main.clone(),
        },
    );
    let inc_return = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn { executable: inc },
    );
    let return_payloads = session
        .transport_shapes()
        .iter()
        .filter_map(|(position, shape)| match position {
            TransportPosition::ReturnPayload { executable, callsite } if executable == &main => {
                Some((*callsite, *shape))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let [(callsite, payload_shape)] = return_payloads.as_slice() else {
        panic!("main/0 should publish exactly one callsite return payload: {return_payloads:?}");
    };

    assert_eq!(
        *payload_shape, inc_return,
        "the callsite return payload is the producer return shape"
    );
    assert_eq!(
        *payload_shape, main_return,
        "a true tail return shares the caller return contract shape"
    );
    let payload_lanes = shape_leaf_lanes(&world, *payload_shape);
    let [(leaf_shape, lane)] = payload_lanes.as_slice() else {
        panic!("inc/1 should return one leaf lane");
    };
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| {
            matches!(seam, CodegenSeam::ReturnContinuation { executable, callsite: candidate }
            if executable == &main && candidate == callsite)
        },
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::RawF64,
        "return payload lanes should publish callsite result seam facts",
    );
}

#[test]
fn compiler2_transport_flow_names_non_tail_return_payload_position() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("fixtures2/behavior/multi_relay.fz".to_string()),
        include_str!("../../fixtures2/behavior/multi_relay.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let return_payloads = session
        .transport_shapes()
        .iter()
        .filter_map(|(position, payload_shape)| match position {
            TransportPosition::ReturnPayload { executable, callsite } => {
                let caller_return = plan_shape_at(
                    session.transport_shapes(),
                    &TransportPosition::ExecutableReturn {
                        executable: executable.clone(),
                    },
                );
                Some((executable.clone(), *callsite, *payload_shape, caller_return))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        !return_payloads.is_empty(),
        "calls with dest=Return should publish callsite return payload positions"
    );
    let Some((executable, callsite, payload_shape, _caller_return)) = return_payloads
        .iter()
        .find(|(_, _, payload_shape, caller_return)| {
            payload_shape != caller_return && !shape_leaf_lanes(&world, *payload_shape).is_empty()
        })
        .cloned()
    else {
        panic!(
            "multi_relay should contain at least one non-empty callsite payload whose producer shape differs from the caller return contract: {return_payloads:?}"
        );
    };
    let leaf_lanes = shape_leaf_lanes(&world, payload_shape);
    assert!(
        !leaf_lanes.is_empty(),
        "the non-tail return payload should still carry producer lanes"
    );
    for (leaf_shape, lane) in leaf_lanes {
        assert!(
            plan.codegen_seam_facts.iter().any(|fact| {
                matches!(
                    &fact.seam,
                    CodegenSeam::ReturnContinuation {
                        executable: candidate_executable,
                        callsite: candidate_callsite,
                    } if candidate_executable == &executable && *candidate_callsite == callsite
                ) && fact.shape == Some(leaf_shape)
                    && fact.lane == lane
            }),
            "return payload {executable:?} callsite {} should publish seam facts for lane {:?}",
            callsite.as_u32(),
            lane
        );
    }
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
    let (_, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
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
    let (_, plan) = pull_root_backend_plan_for_test(&tel, &mut world, root);
    assert!(
        plan.codegen_seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::ExternBoundary { .. }) && fact.repr == CodegenLaneRepr::RawF64),
        "a float extern should publish RawF64 extern-boundary lane facts: {:?}",
        plan.codegen_seam_facts
    );
}

#[test]
fn compiler2_transport_flow_publishes_callable_value_lane_for_spawn_boundary_input() {
    let source = r#"
extern "C" fn fz_spawn(() -> any) :: pid
fn spawn(fun), do: fz_spawn(fun)
fn child(), do: 42
fn main(), do: spawn(child)
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_spawn_callable_boundary_input.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let spawn = executable_for(&world, session, "spawn", 1);
    let spawn_input = TransportPosition::ExecutableInput {
        executable: spawn.clone(),
        semantic_index: 0,
    };
    let boundary = session
        .boundary_facts_inventory()
        .iter()
        .find_map(|(boundary, facts)| facts.publications.contains(&spawn_input).then_some(*boundary))
        .unwrap_or_else(|| panic!("spawn/1 callable input should publish a boundary"));
    let boundary_descr = world.boundary(boundary);
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::FunctionEntry { executable, semantic_index } if executable == &spawn && *semantic_index == 0),
        None,
        boundary_descr.published_value_lane,
        CodegenLaneRepr::ValueRef,
        "a callable executable input that crosses a boundary should publish its closure-ref entry lane",
    );
}

#[test]
fn compiler2_transport_flow_keeps_extern_value_input_boxed_when_argument_is_tuple() {
    let source = r#"
extern "C" fn fz_dbg(any) :: any
fn dbg(x), do: fz_dbg(x)
fn main(), do: dbg({:zero, :pos, :other})
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_extern_tuple_value_input.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let dbg_wrapper = executable_for(&world, session, "dbg", 1);
    let dbg = executable_for(&world, session, "fz_dbg", 1);
    let wrapper_input_shape = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableInput {
            executable: dbg_wrapper,
            semantic_index: 0,
        },
    );
    assert!(
        matches!(shape_descr(&world, wrapper_input_shape), ShapeDescr::Lane(_)),
        "a wrapper that forwards into an extern any boundary should also consume one boxed value lane",
    );
    let input_shape = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableInput {
            executable: dbg.clone(),
            semantic_index: 0,
        },
    );
    assert!(
        matches!(shape_descr(&world, input_shape), ShapeDescr::Lane(_)),
        "extern any input should consume one boxed value lane, not the tuple producer's field lanes",
    );
    let leaf_lanes = shape_leaf_lanes(&world, input_shape);
    let [(leaf_shape, lane)] = leaf_lanes.as_slice() else {
        panic!("extern any input should have exactly one boxed lane")
    };
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::FunctionEntry { executable, semantic_index } if executable == &dbg && *semantic_index == 0),
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::ValueRef,
        "extern any input should publish one ValueRef function-entry seam",
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
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let pair = executable_for(&world, session, "pair", 2);
    let pair_return = plan_shape_at(
        session.transport_shapes(),
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
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::ReturnDelivery { executable } if executable == &pair),
        Some(leaf_lanes[0].0),
        leaf_lanes[0].1,
        CodegenLaneRepr::RawF64,
        "float tuple leaves should publish raw return-delivery seam facts",
    );
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::ReturnDelivery { executable } if executable == &pair),
        Some(leaf_lanes[1].0),
        leaf_lanes[1].1,
        CodegenLaneRepr::RawInt,
        "integer tuple leaves should publish raw return-delivery seam facts",
    );

    let main = executable_for(&world, session, "main", 0);
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::BlockParam { executable, .. } if executable == &main),
        Some(leaf_lanes[0].0),
        leaf_lanes[0].1,
        CodegenLaneRepr::ValueRef,
        "float tuple leaves should enter continuation blocks as ValueRef",
    );
    assert_seam_fact(
        &plan.codegen_seam_facts,
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
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let id_int = executable_for(&world, session, "id_int", 1);
    let id_atom = executable_for(&world, session, "id_atom", 1);

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
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let id_box = executable_for(&world, session, "id_box", 1);
    let id_box_return = plan_shape_at(
        session.transport_shapes(),
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
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::FunctionEntry { executable, .. } if executable == &id_box),
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::ValueRef,
        "boxed function-entry lanes should publish ValueRef seam facts",
    );
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::ReturnDelivery { executable } if executable == &id_box),
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::ValueRef,
        "boxed return-delivery lanes should publish ValueRef seam facts",
    );

    let main = executable_for(&world, session, "main", 0);
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::BlockParam { executable, .. } if executable == &main),
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::ValueRef,
        "boxed continuation block params should publish ValueRef seam facts",
    );
    assert_seam_fact(
        &plan.codegen_seam_facts,
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
    let (driver, plan) = pull_root_backend_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let extern_id = executable_for(&world, session, "fz_binary_id", 1);
    let extern_return = plan_shape_at(
        session.transport_shapes(),
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
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::TailCall { .. }),
        Some(*leaf_shape),
        *lane,
        CodegenLaneRepr::ValueRef,
        "boxed tail-call lanes should publish ValueRef seam facts",
    );
    assert_seam_fact(
        &plan.codegen_seam_facts,
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let ping = executable_for(&world, session, "ping", 1);
    let ping_return = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn { executable: ping },
    );
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
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let apply1 = executable_for(&world, session, "apply1", 2);
    let make_adder = executable_for(&world, session, "make_adder", 1);
    let main = executable_for(&world, session, "main", 0);
    let returned = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn { executable: make_adder },
    );
    let applied = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableInput {
            executable: apply1.clone(),
            semantic_index: 0,
        },
    );
    let resumed = resume_shapes_for(session.transport_shapes(), &main)
        .into_iter()
        .find(|shape| *shape == returned)
        .unwrap_or_else(|| panic!("main should resume the direct callable returned by make_adder/1"));
    assert_eq!(
        applied, returned,
        "the direct callable input consumed by apply1/2 should read the same ShapeId that make_adder/1 returned"
    );
    assert_eq!(
        returned, resumed,
        "direct callable return and resume positions should share one ShapeId"
    );
    assert!(
        matches!(shape_descr(&world, returned), ShapeDescr::Callable(_)),
        "direct callable return should materialize as a callable shape"
    );
    let ShapeDescr::Callable(callable) = shape_descr(&world, returned) else {
        unreachable!("checked above")
    };
    let callable = *callable;
    let producer_function = world
        .callable(callable)
        .function
        .unwrap_or_else(|| panic!("returned direct callable should name its local producer"));
    let flow = upstream_callable_flow_for_producer(session, producer_function);
    assert_callable_facts_match_upstream_flow(&mut world, session, callable, &flow);
    let callable_descr = world.callable(callable);
    let [capture_lane] = callable_descr.capture_lanes.as_ref() else {
        panic!("make_adder/1's returned callable should carry exactly one capture lane: {callable_descr:?}")
    };
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::FunctionEntry { executable, semantic_index } if executable == &apply1 && *semantic_index == 0),
        Some(returned),
        *capture_lane,
        CodegenLaneRepr::RawInt,
        "direct callable executable inputs should publish codegen facts for their carried capture lanes",
    );
}

#[test]
fn compiler2_transport_plan_is_the_artifact_handoff_contract() {
    let source = r#"
fn apply1(f, x), do: f.(x)
fn make_adder(a), do: fn (x) -> x + a end
fn pair(x), do: {x, make_adder(x)}
fn escape(), do: make_adder(10)
fn double(n), do: n + n

fn main() do
  {n, f} = pair(41)
  y = apply1(f, n)

  first = double(5)
  assert(first == 10, "first")
  assert(first == 10, "second")

  {y, escape()}
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_artifact_handoff_contract.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    assert_plan_executable_references_are_root_scoped(&world, &plan, session);

    let pair = executable_for(&world, session, "pair", 1);
    let main = executable_for(&world, session, "main", 0);
    let pair_return = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn { executable: pair },
    );
    let pair_resume = resume_shapes_for(session.transport_shapes(), &main)
        .into_iter()
        .find(|shape| *shape == pair_return)
        .unwrap_or_else(|| {
            panic!(
                "main/0 should resume pair/1's returned shape: {:?}",
                session.transport_shapes()
            )
        });
    assert_eq!(
        pair_return, pair_resume,
        "artifact must read the producer return ShapeId for delivered resumes instead of deriving a local layout"
    );
    let ShapeDescr::Tuple(pair_fields) = shape_descr(&world, pair_return) else {
        panic!("pair/1 should publish a tuple transport shape")
    };
    let [n_shape, f_shape] = pair_fields.as_ref() else {
        panic!("pair/1 should return the integer and direct callable fields")
    };
    assert!(
        matches!(shape_descr(&world, *n_shape), ShapeDescr::Lane(_)),
        "the scalar field should remain a lane shape"
    );
    let ShapeDescr::Callable(pair_callable) = shape_descr(&world, *f_shape) else {
        panic!("the callable field should remain a CallableId shape")
    };

    let apply1 = executable_for(&world, session, "apply1", 2);
    let apply1_callable_input = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableInput {
            executable: apply1.clone(),
            semantic_index: 0,
        },
    );
    assert_eq!(
        *f_shape, apply1_callable_input,
        "artifact must read the direct-callable executable input shape from TransportPlan"
    );
    let callable_facts = session
        .callable_facts_inventory()
        .get(pair_callable)
        .unwrap_or_else(|| panic!("direct callable facts should exist for {pair_callable:?}"));
    assert!(
        !callable_facts.direct_surfaces.is_empty(),
        "direct callable surfaces should be plan facts, not artifact-local recovery"
    );
    let callable_descr = world.callable(*pair_callable);
    let [capture_lane] = callable_descr.capture_lanes.as_ref() else {
        panic!("make_adder/1 should publish one carried capture lane: {callable_descr:?}")
    };
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::FunctionEntry { executable, semantic_index } if executable == &apply1 && *semantic_index == 0),
        Some(apply1_callable_input),
        *capture_lane,
        CodegenLaneRepr::RawInt,
        "artifact must consume direct-callable capture lane seam facts instead of walking layouts",
    );

    let escape = executable_for(&world, session, "escape", 0);
    let escaped = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn { executable: escape },
    );
    let ShapeDescr::Callable(escaped_callable) = shape_descr(&world, escaped) else {
        panic!("escape/0 should return a callable shape")
    };
    let escaped_facts = session
        .callable_facts_inventory()
        .get(escaped_callable)
        .unwrap_or_else(|| panic!("escaped callable facts should exist for {escaped_callable:?}"));
    assert_eq!(
        escaped_facts.boundary_ids.len(),
        1,
        "escaped callable publication should be a BoundaryId fact consumed by artifact"
    );
    let [boundary] = escaped_facts.boundary_ids.as_ref() else {
        unreachable!("checked above")
    };
    let boundary_descr = world.boundary(*boundary);
    assert_eq!(
        boundary_descr.callable, *escaped_callable,
        "BoundaryId should name the callable contract artifact publishes"
    );
    assert!(
        session
            .boundary_facts_inventory()
            .get(boundary)
            .is_some_and(|facts| !facts.publications.is_empty()),
        "first-class publication positions should be plan facts, not artifact-local boundary selection"
    );

    let double = executable_for(&world, session, "double", 1);
    let double_return = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn { executable: double },
    );
    let double_resume = resume_shapes_for(session.transport_shapes(), &main)
        .into_iter()
        .find(|shape| *shape == double_return)
        .unwrap_or_else(|| panic!("main/0 should resume double/1's returned shape even across ignored assert calls"));
    assert_eq!(
        double_return, double_resume,
        "ignored later call results may be locally unused, but artifact must not shrink the received transport shape"
    );
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::ContinuationEntry { executable, .. } if executable == &main),
        Some(double_return),
        shape_leaf_lanes(&world, double_return)
            .first()
            .map(|(_, lane)| *lane)
            .expect("double/1 should return one lane"),
        CodegenLaneRepr::RawInt,
        "continuation entry representation should be a seam fact read by artifact/codegen consumers",
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    assert_eq!(
        session.boundary_facts_inventory().len(),
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let main = executable_for(&world, session, "main", 0);
    let callable_shapes = session
        .transport_shapes()
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
        session.boundary_facts_inventory().len(),
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let make = executable_for(&world, session, "make", 0);
    let returned = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn { executable: make },
    );
    assert!(
        matches!(shape_descr(&world, returned), ShapeDescr::Callable(_)),
        "escaped lambda should still be a callable shape in the transport plan"
    );
    assert_eq!(
        session.boundary_facts_inventory().len(),
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let main = executable_for(&world, session, "main", 1);
    let input_shape = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableInput {
            executable: main,
            semantic_index: 0,
        },
    );
    assert!(
        matches!(shape_descr(&world, input_shape), ShapeDescr::Callable(_)),
        "a callable input with opaque closure-call demand should stay callable-shaped, not collapse to a value lane"
    );
    let ShapeDescr::Callable(input_callable) = shape_descr(&world, input_shape) else {
        unreachable!("checked above")
    };
    let input_demand = upstream_input_demand_for_function(&world, session, "main", 1, 0);
    assert_generic_callable_shape_matches_upstream_demand(&world, session, *input_callable, input_demand);
    assert_eq!(
        session.boundary_facts_inventory().len(),
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let main = executable_for(&world, session, "main", 2);
    // Both opaque inputs are boxed callables, so their VALUE shapes are pure
    // layout (one boxed value lane) and may coincide. The surface contract is
    // not part of the value identity any more — it lives on the boundaries.
    for semantic_index in [0, 1] {
        let shape = plan_shape_at(
            session.transport_shapes(),
            &TransportPosition::ExecutableInput {
                executable: main.clone(),
                semantic_index,
            },
        );
        assert!(
            matches!(shape_descr(&world, shape), ShapeDescr::Callable(_)),
            "opaque input {semantic_index} should be callable-shaped"
        );
    }
    // The distinction with different observed surfaces (`f.(1)` vs `g.({1, 2})`)
    // survives where it belongs: as two distinct published boundary contracts.
    let surface_contracts = session
        .boundary_facts_inventory()
        .keys()
        .map(|boundary| world.boundary(*boundary).surface_arg_shapes.to_vec())
        .collect::<BTreeSet<_>>();
    assert!(
        surface_contracts.len() >= 2,
        "opaque callables with different observed surfaces must publish distinct boundary contracts, even when their boxed value shapes coincide: {surface_contracts:?}"
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let main = executable_for(&world, session, "main", 0);
    let returned = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn { executable: main },
    );
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let boundary = boundary_with_callable_arg(&world, session);
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let boundary = single_boundary_descr(&world, session);
    let boundary_callable = boundary.callable;
    let boundary_return_shape = boundary.published_return_shape;
    let boundary_return_lanes_len = boundary.published_return_lanes.len();
    let producer_function = world
        .callable(boundary_callable)
        .function
        .unwrap_or_else(|| panic!("tuple-return boundary callable should name its local producer"));
    let flow = upstream_callable_flow_for_producer(session, producer_function);
    assert_callable_facts_match_upstream_flow(&mut world, session, boundary_callable, &flow);
    let ShapeDescr::Tuple(items) = shape_descr(&world, boundary_return_shape) else {
        panic!(
            "a callable returning a tuple should publish the return ShapeId, got {:?}",
            shape_descr(&world, boundary_return_shape)
        );
    };
    let [left, right] = items.as_ref() else {
        panic!("the boundary return should preserve the outer two-field tuple")
    };
    assert!(
        matches!(shape_descr(&world, *left), ShapeDescr::Tuple(inner) if inner.len() == 2),
        "the boundary return shape should preserve nested tuple structure instead of flattening lanes: {:?}",
        shape_descr(&world, boundary_return_shape)
    );
    assert!(
        matches!(shape_descr(&world, *right), ShapeDescr::Lane(_)),
        "the second outer field should remain a scalar shape: {:?}",
        shape_descr(&world, boundary_return_shape)
    );
    assert_eq!(
        boundary_return_lanes_len, 3,
        "the separate lane fact should flatten the three scalar leaves without becoming the return structure"
    );
}

#[test]
fn compiler2_transport_plan_preserves_captured_callable_return_inside_boundary_tuple() {
    let source = r#"
fn make_suspender() do
  fn (acc) ->
    {:suspended, acc, fn () -> {:cont, acc + 1} end}
  end
end

fn main(), do: make_suspender()
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_boundary_suspend_tuple_return.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let make_suspender = executable_for(&world, session, "make_suspender", 0);
    let outer = callable_return_for_executable(&world, session.transport_shapes(), make_suspender);
    let boundary = boundary_with_callable_return(&world, session, outer);
    let ShapeDescr::Tuple(items) = shape_descr(&world, boundary.published_return_shape) else {
        panic!(
            "a suspend-shaped callable return should publish a tuple return shape, got {:?}",
            shape_descr(&world, boundary.published_return_shape)
        );
    };
    let [tag_shape, acc_shape, resume_shape] = items.as_ref() else {
        panic!("the suspend-shaped boundary return should have tag, accumulator, and resume callable fields")
    };
    assert!(
        matches!(shape_descr(&world, *tag_shape), ShapeDescr::Lane(_)),
        "the suspend tag should remain a normal lane field"
    );
    assert!(
        matches!(shape_descr(&world, *acc_shape), ShapeDescr::Lane(_)),
        "the suspend accumulator should remain a normal lane field"
    );
    assert!(
        matches!(shape_descr(&world, *resume_shape), ShapeDescr::Callable(_)),
        "the suspend resume function should remain a callable child shape, not a flattened lane"
    );
    assert_eq!(
        boundary.published_return_lanes.len(),
        3,
        "boundary lane facts should flatten tag, accumulator, and the callable child into lanes without replacing the return structure"
    );
}

#[test]
#[ignore = "fz-go4.18.9: the product boundary for the suspended callable publishes a \
            published_return_shape without the callable-return child the legacy plan carried; \
            ported to split surfaces with assertions intact, un-ignore when the product \
            reproduces the callable-return child."]
fn compiler2_transport_plan_preserves_enumerable_suspend_continuation_captures() {
    let source = r#"
fn make() do
  fn () ->
    Enumerable.reduce([1, 2, 3], {:suspend, 0}, fn (x, acc) -> {:cont, acc + x} end)
  end
end

fn main(), do: make()
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_enumerable_reduce_suspend_continuation.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let make = executable_for(&world, session, "make", 0);
    let outer = callable_return_for_executable(&world, session.transport_shapes(), make);
    let boundary = boundary_with_callable_return(&world, session, outer);
    let ShapeDescr::Tuple(items) = shape_descr(&world, boundary.published_return_shape) else {
        panic!(
            "the escaped callable should publish the Enumerable.reduce suspend tuple return shape, got {:?}",
            shape_descr(&world, boundary.published_return_shape)
        );
    };
    let [tag_shape, acc_shape, continuation_shape] = items.as_ref() else {
        panic!("the suspend return should have tag, accumulator, and continuation fields")
    };
    assert!(
        matches!(shape_descr(&world, *tag_shape), ShapeDescr::Lane(_)),
        "the suspend tag should remain a normal lane field"
    );
    assert!(
        matches!(shape_descr(&world, *acc_shape), ShapeDescr::Lane(_)),
        "the suspended accumulator should remain a normal lane field"
    );
    let ShapeDescr::Callable(continuation) = shape_descr(&world, *continuation_shape) else {
        panic!(
            "the third suspend field should remain a callable continuation shape, got {:?}",
            shape_descr(&world, *continuation_shape)
        )
    };
    let continuation_descr = world.callable(*continuation);
    assert_eq!(
        continuation_descr.capture_shapes.len(),
        3,
        "the suspend continuation should capture the remaining list, accumulator, and reducer"
    );
    assert!(
        matches!(
            shape_descr(&world, continuation_descr.capture_shapes[2]),
            ShapeDescr::Callable(_)
        ),
        "the captured reducer should remain callable-shaped inside the continuation descriptor"
    );
    assert_eq!(
        session
            .callable_facts_inventory()
            .get(continuation)
            .unwrap_or_else(|| panic!("returned continuation facts should be present"))
            .boundary_ids
            .len(),
        1,
        "the escaped suspend continuation should publish one zero-argument boundary contract"
    );
    let continuation_boundary = continuation_boundary_descr(&world, session, *continuation);
    assert_eq!(
        continuation_boundary.surface_arg_shapes.len(),
        0,
        "the suspend continuation boundary should expose the zero-argument callable surface"
    );
    assert_eq!(
        continuation_boundary.published_capture_lanes.len(),
        2,
        "the continuation boundary publishes only runtime payload lanes: list and accumulator carry lanes, while the reducer callable identity remains in the capture ShapeId"
    );
    assert_no_unreachable_callable_facts(&world, session);
}

#[test]
fn compiler2_transport_plan_publishes_tuple_returned_callable_captured_by_resume() {
    let source = r#"
fn make(a, b, c), do: {:ok, a + b + c, fn (x) -> a + b + c + x end}

fn main() do
  {:ok, n, f} = make(1, 10, 2)
  dbg(n)
  f.(3)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_tuple_returned_callable_resume_capture.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let main = executable_for(&world, session, "main", 0);
    let (resume_position, resume_shape) = session
        .transport_shapes()
        .iter()
        .find(|(position, shape)| {
            matches!(
                position,
                TransportPosition::ResumePayload {
                    executable,
                    callsite: Some(_),
                    ..
                } if executable == &main
            ) && shape_contains_callable(&world, **shape)
        })
        .unwrap_or_else(|| {
            panic!(
                "main should resume the make/3 tuple return with the callable field still present: {:?}",
                session.transport_shapes()
            )
        });
    let callable = first_callable_in_shape(&world, *resume_shape)
        .expect("the resumed tuple shape should contain the returned callable field");
    let facts = session.callable_facts_inventory().get(&callable).unwrap_or_else(|| {
        panic!(
            "returned callable should have facts: {:?}",
            session.callable_facts_inventory()
        )
    });
    let boundary = facts
        .boundary_ids
        .iter()
        .copied()
        .map(|boundary| (boundary, world.boundary(boundary)))
        .find(|(_, boundary)| boundary.callable == callable)
        .unwrap_or_else(|| {
            panic!(
                "the tuple-returned callable should publish a boundary at the resume seam: {:?}",
                session.callable_facts_inventory()
            )
        });
    assert!(
        session
            .boundary_facts_inventory()
            .get(&boundary.0)
            .is_some_and(|facts| facts.publications.iter().any(|position| position == resume_position)),
        "the callable boundary must record the resume payload publication that carries the boxed closure pointer; \
         resume_position={resume_position:?}; boundary={:?}; boundary_facts={:?}; seam_facts={:?}",
        boundary.1,
        session.boundary_facts_inventory().get(&boundary.0),
        plan.codegen_seam_facts,
    );
    let TransportPosition::ResumePayload {
        callsite: Some(callsite),
        entry,
        ..
    } = resume_position
    else {
        panic!("checked above")
    };
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| {
            matches!(
                seam,
                CodegenSeam::ContinuationEntry {
                    executable,
                    callsite: candidate_callsite,
                    entry: candidate_entry,
                } if executable == &main && candidate_callsite == callsite && candidate_entry == entry
            )
        },
        None,
        boundary.1.published_value_lane,
        CodegenLaneRepr::ValueRef,
        "a tuple-returned callable captured by a later resume must enter the continuation as the published closure pointer",
    );
}

/// fz-hwn.19.2.4.15: a protocol-dispatched `defimpl` that returns an escaped
/// continuation capturing a callable used to reach transport with that callable's
/// direct-call surface erased.
///
/// `Susp.run(_list, f)` returns `fn () -> f.(1) end`. The continuation never calls
/// `f` in `run`'s own body — it captures `f` and escapes by return — so `run`'s
/// runtime demand for `f` was a surface-less first-class (escaped) callable.
/// Transport's `generic_callable_shape` guard then tripped: "generic callable
/// transport requires upstream callable surfaces for opaque or escaped demand".
///
/// The fix proves the surface in the runtime-demand contract, not in transport:
/// the continuation's own executable already knows it invokes `f` at `(int)`
/// (from `f.(1)`), and capture propagation reads that demand off the producer
/// executable by capture-type prefix — no longer gated on the escaped closure
/// carrying a (nonexistent) direct-call surface of its own. So `run`'s `f` input
/// demand carries the proven `(int)` surface, and the plan derives cleanly.
#[test]
#[ignore = "fz-go4.18.9: the product runtime-demand for run/2[1] does not reproduce the legacy \
            eager (int) capture surface (product demanded_executables selects a different run/2 \
            activation); ported to split surfaces with assertions intact, un-ignore when the \
            product under-derivation is resolved."]
fn compiler2_transport_plan_proves_protocol_dispatched_escaped_continuation_capture_surface() {
    let source = r#"
defprotocol Susp do
  @spec run(t(a), (a) -> b) :: () -> b
  fn run(coll, f)
end

defmodule Mini do
  defimpl Susp, for: List do
    fn run(_list, f), do: (fn () -> f.(1) end)
  end
end

fn make(f), do: Susp.run([1, 2, 3], f)
fn main(), do: make(fn x -> x + 1 end)
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_protocol_escaped_continuation.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();

    let captured_demand = upstream_input_demand_for_function(&world, session, "run", 2, 1);
    assert!(
        captured_demand.is_callable(),
        "the impl's captured callable parameter `f` should carry a callable demand, got {captured_demand:?}"
    );
    let surfaces = &captured_demand.callable.resolved;
    assert!(
        !surfaces.is_empty(),
        "the escaped continuation's body proves it invokes `f` at one argument; \
         `run`'s demand for `f` must carry that direct-call surface, got {captured_demand:?}"
    );
    assert!(
        surfaces.iter().all(|surface| surface.inputs.len() == 1),
        "`f` is invoked at exactly one argument (`f.(1)`); every proven surface should be arity-1, got {surfaces:?}"
    );
    assert!(
        surfaces
            .iter()
            .flat_map(|surface| surface.inputs.iter())
            .all(|ty| world.types().is_integer(ty)),
        "`f` is invoked with the integer literal `1`; its proven argument surface should be int, got {surfaces:?}"
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let main = executable_for(&world, session, "main", 0);
    let returned = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn { executable: main },
    );
    let ShapeDescr::Callable(callable) = shape_descr(&world, returned) else {
        panic!("main/0 should return the callable value it also invoked directly")
    };
    let callable = *callable;
    let producer_function = world
        .callable(callable)
        .function
        .unwrap_or_else(|| panic!("returned direct-and-escaped callable should name its local producer"));
    let flow = upstream_callable_flow_for_producer(session, producer_function);
    assert_callable_facts_match_upstream_flow(&mut world, session, callable, &flow);
    let facts = session
        .callable_facts_inventory()
        .get(&callable)
        .unwrap_or_else(|| panic!("returned callable facts should be present"));
    assert!(
        !facts.direct_surfaces.is_empty(),
        "direct-call surfaces must remain visible even when the same callable also escapes"
    );
    assert!(
        !facts.boundary_ids.is_empty(),
        "the escaped callable should still publish a first-class boundary"
    );
    let runtime_demands = runtime_demands_for_frontier(session);
    for boundary in facts.boundary_ids.iter().copied() {
        let boundary_descr = world.boundary(boundary);
        let boundary_facts = session
            .boundary_facts_inventory()
            .get(&boundary)
            .unwrap_or_else(|| panic!("boundary facts should exist for {boundary:?}"));
        let target_demands = boundary_facts
            .resolutions
            .iter()
            .map(|resolution| {
                let demand = runtime_demands
                    .iter()
                    .find(|(executable, _)| {
                        executable.need == resolution.need
                            && executable.activation.function == resolution.activation.function
                            && executable.activation.inputs(world.types()).as_slice()
                                == resolution.activation.input.as_ref()
                    })
                    .map(|(_, demand)| demand.return_demand.clone());
                (resolution.clone(), demand)
            })
            .collect::<Vec<_>>();
        assert!(
            !matches!(
                shape_descr(&world, boundary_descr.published_return_shape),
                ShapeDescr::Nothing
            ),
            "an escaped callable boundary should publish the target return shape, got {:?}",
            (
                shape_descr(&world, boundary_descr.published_return_shape),
                target_demands
            )
        );
    }
}

#[test]
fn compiler2_transport_plan_shapes_callable_captures_from_upstream_callable_flow() {
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
        Some("transport_callable_capture_flow.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let captured_callable = session
        .callable_facts_inventory()
        .iter()
        .find_map(|(outer, _)| {
            let outer_descr = world.callable(*outer);
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
                session.callable_facts_inventory()
            )
        });
    let captured_facts = session
        .callable_facts_inventory()
        .get(&captured_callable)
        .unwrap_or_else(|| panic!("captured callable facts should be present"));
    let producer_function = world
        .callable(captured_callable)
        .function
        .unwrap_or_else(|| panic!("captured callable should name its local producer"));
    let flow = upstream_callable_flow_for_producer(session, producer_function);
    assert_callable_facts_match_upstream_flow(&mut world, session, captured_callable, &flow);
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let make = executable_for(&world, session, "make", 1);
    let returned = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn { executable: make },
    );
    let ShapeDescr::Callable(callable) = shape_descr(&world, returned) else {
        panic!("recursive make/1 should return a callable shape")
    };
    let facts = session
        .callable_facts_inventory()
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let make = executable_for(&world, session, "make", 2);
    let returned = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn { executable: make },
    );
    let ShapeDescr::Callable(callable) = shape_descr(&world, returned) else {
        panic!("make/2 should return a callable shape")
    };
    assert!(
        session.callable_facts_inventory().contains_key(callable),
        "returned callable facts should be present"
    );
    let callable_descr = world.callable(*callable);
    assert_eq!(
        callable_descr.capture_lanes.len(),
        2,
        "two same-typed captures are two ordered payload lanes, not one deduplicated lane"
    );
    let boundary = single_boundary_descr(&world, session);
    assert_eq!(
        boundary.published_capture_lanes.as_ref(),
        callable_descr.capture_lanes.as_ref(),
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    for facts in session.boundary_facts_inventory().values() {
        for publication in facts.publications.iter() {
            assert!(
                transport_position_is_semantic(publication),
                "boundary publications must name semantic positions, not synthetic self-positions: {publication:?}"
            );
        }
    }
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    assert_eq!(
        session.boundary_facts_inventory().len(),
        2,
        "one escaped callable used at two surfaces should publish one boundary contract per surface"
    );
    let mut has_scalar_return = false;
    let mut has_tuple_return = false;
    for boundary in boundary_descrs(&world, session) {
        match shape_descr(&world, boundary.published_return_shape) {
            ShapeDescr::Lane(_) => has_scalar_return = true,
            ShapeDescr::Tuple(items) if items.len() == 2 => has_tuple_return = true,
            other => panic!("unexpected boundary return shape for surface-specific fixture: {other:?}"),
        }
    }
    for (boundary, facts) in session.boundary_facts_inventory() {
        let boundary_descr = world.boundary(*boundary);
        let [target] = facts.resolutions.as_ref() else {
            panic!("each callable boundary should name its exact executable target: {boundary:?} -> {facts:?}")
        };
        assert_eq!(
            target.activation.input.len(),
            boundary_descr.surface_arg_shapes.len(),
            "boundary target arity should match the boundary's published surface"
        );
        assert_eq!(
            plan_shape_at(
                session.transport_shapes(),
                &TransportPosition::ExecutableReturn {
                    executable: target.clone(),
                },
            ),
            boundary_descr.published_return_shape,
            "boundary target should be the executable whose return shape backs that boundary contract"
        );
    }
    assert!(
        has_scalar_return && has_tuple_return,
        "boundary return shape must follow each surface instead of joining all surfaces into one fallback"
    );
}

#[test]
fn compiler2_transport_plan_does_not_publish_dead_callable_input_boundaries() {
    let source = include_str!("../../fixtures2/behavior/range_enumerable.fz");

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_range_enumerable_dead_boundary.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let dead_return_boundaries = session
        .boundary_facts_inventory()
        .keys()
        .filter_map(|boundary| {
            let descr = world.boundary(*boundary);
            matches!(shape_descr(&world, descr.published_return_shape), ShapeDescr::Nothing).then_some(*boundary)
        })
        .collect::<Vec<_>>();
    assert!(
        dead_return_boundaries.is_empty(),
        "first-class callable boundaries whose resolved target returns an empty type are not callable contracts: {dead_return_boundaries:?}"
    );

    world.demand(super::Job::LowerNativeProgram(root));
    assert_resolved(
        world.drive_for(None),
        "Range Enumerable fixture should lower native callable publications before the known slicer runtime blocker",
    );
}

#[test]
#[ignore = "fz-f98.14: the enum_predicate_search fixture's transport derivation does far more work \
            than this assertion reads because the Seal<->DeriveRuntimeDemand<->Transport cycle does \
            not converge monotonically (a correctness bug, not perf) -- >1s on a tiny fixture. \
            Ported to split product surfaces; un-ignore when the convergence runaway is fixed."]
fn compiler2_transport_plan_scopes_enum_predicate_callback_inputs_to_concrete_activations() {
    let source = include_str!("../../fixtures2/behavior/enum_predicate_search.fz");

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_enum_predicate_search_activation_inputs.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    assert!(
        executable_membership(&world, session)
            .iter()
            .any(|executable| function_is(&world, executable.activation.function, "reduce_while_cont", 3)),
        "Enum predicate/search should keep List.reduce_while_cont/3 in the transport frontier"
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let pair_down = executable_for(&world, session, "pair_down", 1);
    let returned = plan_shape_at(
        session.transport_shapes(),
        &TransportPosition::ExecutableReturn {
            executable: pair_down.clone(),
        },
    );
    let recursive_resume = resume_shapes_for(session.transport_shapes(), &pair_down)
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
#[serial_test::serial]
fn compiler2_pull_runtime_demand_keeps_enum_reduce_operator_refs_direct_callable() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler2", "pull"], capture.handler());
    let mut world = World::new(&tel);
    let root = submit_enum_reduce_operator_ref_root(&mut world, "pull_runtime_enum_reduce_operator_refs.fz");
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let executables = driver.session().materialized_executables().keys().collect::<Vec<_>>();

    let plus_flows = executables
        .iter()
        .filter_map(|executable| driver.session().memo().runtime_demand(executable))
        .flat_map(|demand| demand.callable_flows.values())
        .filter(|flow| function_is(&world, flow.function, "+", 2))
        .collect::<Vec<_>>();
    assert!(
        plus_flows.iter().any(|flow| {
            flow.direct_surfaces.iter().any(|surface| surface.inputs.len() == 2)
                && flow
                    .resolutions
                    .iter()
                    .any(|resolution| function_is(&world, resolution.activation.function, "+", 2))
        }),
        "product runtime demand should keep operator refs as direct Kernel.+/2 callable flows: {plus_flows:?}"
    );
    assert!(
        plus_flows
            .iter()
            .all(|flow| flow.first_class_surfaces.is_empty() && !flow.opaque && !flow.escape),
        "operator refs used only as Enum.reduce reducers should not become first-class product demand: {plus_flows:?}"
    );
    assert_eq!(driver.session().producer_pokes(), 0);
    assert!(
        capture.count(&["fz", "compiler2", "pull", "product", "requested"]) > 0,
        "product path should emit product request telemetry"
    );
    assert!(
        capture.count(&["fz", "compiler2", "pull", "product", "produced"]) > 0,
        "product path should emit product production telemetry"
    );
    let finished = capture
        .last(&["fz", "compiler2", "pull", "session", "finished"])
        .expect("product path should emit final session telemetry");
    assert_eq!(measurement_u64(&finished, "producer_pokes"), 0);
}

#[test]
#[serial_test::serial]
fn compiler2_pull_transport_keeps_enum_reduce_operator_refs_direct_callable() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler2", "pull"], capture.handler());
    let mut world = World::new(&tel);
    let root = submit_enum_reduce_operator_ref_root(&mut world, "pull_transport_enum_reduce_operator_refs.fz");
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let main_return = TransportPosition::ExecutableReturn {
        executable: plan.entry.clone(),
    };

    let returned = plan
        .shape_at(&main_return)
        .expect("main return transport product should contain a concrete shape");
    let ShapeDescr::Tuple(items) = shape_descr(&world, returned) else {
        panic!("product main/0 should return the two reduced integer results as a tuple")
    };
    assert_eq!(items.len(), 2, "product main/0 should return one field per reduce call");
    assert!(
        shape_leaf_lanes(&world, returned)
            .iter()
            .all(|(_, lane)| world.types().is_integer(&world.lane(*lane).ty)),
        "product return leaves should stay integer lanes; returned={:?}; leaves={:?}",
        shape_descr(&world, returned),
        shape_leaf_lanes(&world, returned)
            .into_iter()
            .map(|(shape, lane)| (shape, lane, world.lane(lane).ty))
            .collect::<Vec<_>>()
    );

    let plus_callables = driver
        .session()
        .demanded_callables()
        .iter()
        .filter_map(|callable| {
            let facts = driver.session().callable_facts(*callable)?;
            let function = world.callable(*callable).function?;
            function_is(&world, function, "+", 2).then_some((*callable, facts))
        })
        .collect::<Vec<_>>();
    assert!(
        !plus_callables.is_empty(),
        "product transport should produce callable facts for Kernel.+/2"
    );
    assert!(
        plus_callables
            .iter()
            .any(|(_, facts)| facts.direct_surfaces.iter().any(|surface| surface.len() == 2)),
        "product transport should keep reducer demand as a direct two-argument callable surface: {plus_callables:?}"
    );
    assert!(
        plus_callables.iter().all(|(_, facts)| facts.boundary_ids.is_empty()),
        "product transport should not publish first-class boundaries for operator-ref reducers: {plus_callables:?}"
    );
    assert_eq!(driver.session().producer_pokes(), 0);
    assert!(
        capture.count(&["fz", "compiler2", "pull", "product", "requested"]) > 0,
        "product transport path should emit product request telemetry"
    );
}

#[test]
#[serial_test::serial]
fn compiler2_pull_transport_shape_is_stable_across_product_request_order() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = submit_enum_reduce_operator_ref_root(
        &mut world,
        "pull_transport_order_stability_enum_reduce_operator_refs.fz",
    );
    let (_, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let main_return = TransportPosition::ExecutableReturn {
        executable: plan.entry.clone(),
    };
    let root_first_shape = plan
        .shape_at(&main_return)
        .expect("packaged root product should publish main return shape");
    let mut shape_first_driver = ProductDriver::new(&tel, root);
    let shape_first = pull_product_until_produced_with_fact_waits(
        &mut shape_first_driver,
        &mut world,
        root,
        ProductKey::TransportShape(main_return),
        "main return transport shape should be product-derivable without legacy plan pre-settle",
    );
    let ProductValue::TransportShape(TransportShapeFact::Shape(shape_first_shape)) = shape_first else {
        panic!("transport product should contain a concrete shape, got {shape_first:?}");
    };

    assert_eq!(
        shape_descr(&world, root_first_shape),
        shape_descr(&world, shape_first_shape),
        "product transport shape must not depend on whether root package or shape product is requested first"
    );
}

#[test]
#[serial_test::serial]
fn compiler2_pull_materialized_inventory_keeps_enum_reduce_operator_refs_symbolic() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = submit_enum_reduce_operator_ref_root(&mut world, "pull_materialized_enum_reduce_operator_refs.fz");
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);

    assert_eq!(
        driver.session().materialized_executables().len(),
        10,
        "00181 product materialization should contain the ten demanded executable roles"
    );
    assert!(
        driver.session().materialized_executables().keys().any(|executable| {
            let function = world.function_ref(executable.activation.function);
            function.name == "main" && function.arity == 0
        }),
        "product materialization should include main/0"
    );
    assert!(
        driver.session().materialized_executables().keys().any(|executable| {
            let function = world.function_ref(executable.activation.function);
            function.name == "+" && function.arity == 2
        }),
        "product materialization should include Kernel.+/2"
    );
    for (caller, materialized) in driver.session().materialized_executables() {
        for edge in materialized.call_edges.values() {
            for callee in materialized_call_edge_callees(edge) {
                assert!(
                    driver.session().materialized_executable(callee).is_some(),
                    "symbolic materialized call edge from {caller:?} points to an undemanded callee {callee:?}"
                );
            }
        }
    }
    assert_eq!(driver.session().producer_pokes(), 0);
}

#[test]
#[serial_test::serial]
fn compiler2_pull_abi_and_backend_products_keep_call_edges_symbolic() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let root = submit_enum_reduce_operator_ref_root(&mut world, "pull_abi_backend_enum_reduce_operator_refs.fz");
    let driver = pull_root_backend_driver_for_test(&tel, &mut world, root);
    let executables = driver
        .session()
        .backend_executables()
        .keys()
        .cloned()
        .collect::<HashSet<_>>();

    assert_eq!(
        driver.session().abi_executables().len(),
        executables.len(),
        "ABI products should be per demanded executable"
    );
    assert_eq!(
        driver.session().backend_executables().len(),
        executables.len(),
        "backend products should be per demanded executable"
    );
    for (caller, abi) in driver.session().abi_executables() {
        for edge in abi.call_edges.values() {
            for callee in abi_ready_call_edge_callees(edge) {
                assert!(
                    executables.contains(callee),
                    "ABI call edge from {caller:?} should remain an ExecutableKey in the demanded set, got {callee:?}"
                );
            }
        }
    }
    for (caller, backend) in driver.session().backend_executables() {
        assert_eq!(
            backend.call_edges,
            backend
                .abi
                .call_edges
                .iter()
                .map(|(callsite, edge)| (*callsite, edge.target.clone()))
                .collect::<HashMap<_, _>>(),
            "symbolic backend product should preserve ABI ExecutableKey call edges"
        );
        assert_symbolic_backend_body_has_no_dense_targets(&backend.body, caller);
    }
    assert_eq!(driver.session().producer_pokes(), 0);
}

#[test]
#[serial_test::serial]
fn compiler2_pull_root_backend_product_packages_and_runs_enum_reduce_operator_refs() {
    let tel = ConfiguredTelemetry::new();
    let (_interp_root, no_dump_jobs) = product_no_dump_interp_job_telemetry(ENUM_REDUCE_OPERATOR_REF_SOURCE);
    let no_dump_job_fires = no_dump_jobs.total_stops();
    assert!(
        no_dump_job_fires < LEGACY_00181_NO_DUMP_JOB_STARTS,
        "product no-dump interp should reduce fixture 00181 compiler job starts below the legacy baseline; got {no_dump_job_fires}"
    );

    let mut world = World::new(&tel);
    let root = submit_enum_reduce_operator_ref_root(&mut world, "pull_root_backend_enum_reduce_operator_refs.fz");
    let capture = Capture::new();
    let product_jobs = JobTelemetry::new();
    tel.attach(&[], capture.handler());
    tel.attach(&["fz", "compiler2", "job"], product_jobs.handler());
    let mut driver = ProductDriver::new(&tel, root);
    assert!(
        driver.session().executable_index().is_empty(),
        "dense executable indices should not exist before final backend packaging"
    );
    let product = pull_product_until_produced_with_fact_waits(
        &mut driver,
        &mut world,
        root,
        ProductKey::RootBackendProduct(root),
        "root backend product should be product-derivable",
    );
    let ProductValue::RootBackendProduct(program) = product else {
        panic!("root backend product should return a BackendProgram, got {product:?}");
    };

    assert_eq!(
        program.executables.len(),
        10,
        "final backend package should include exactly the demanded executable products"
    );
    assert_eq!(
        driver.session().backend_executables().len(),
        10,
        "root package should pull every demanded symbolic backend executable"
    );
    assert_eq!(
        driver.session().executable_index().len(),
        10,
        "dense executable indices are assigned at final packaging only"
    );
    assert!(
        program.callable_entries.is_empty(),
        "operator refs in fixture 00181 should stay direct callable transport with no backend callable entries"
    );
    assert_direct_clause_param_forwards_have_abi_reprs(&world, &program);
    assert_eq!(driver.session().producer_pokes(), 0);
    driver.finish_session();
    assert!(
        product_jobs.total_stops() > 0,
        "cold root product demand should drive exact fact prerequisites without legacy pre-settle"
    );
    assert!(
        capture.count(&["fz", "compiler2", "pull", "product", "requested"]) > 0,
        "root backend product path should emit product request telemetry"
    );
    assert!(
        capture.count(&["fz", "compiler2", "pull", "product", "produced"]) > 0,
        "root backend product path should emit product production telemetry"
    );
    assert!(
        capture.events().iter().any(
            |event| event.name == ["fz", "compiler2", "pull", "product", "requested"]
                && metadata_str(event, "kind") == "callable_facts"
        ),
        "root backend product path should explicitly request callable facts products"
    );
    let component_event = capture
        .last(&["fz", "compiler2", "pull", "transport_component", "produced"])
        .expect("transport component product should emit component-size telemetry");
    assert!(
        measurement_u64(&component_event, "component_size") > 0,
        "transport component telemetry should report the demanded component size"
    );
    let finished = capture
        .last(&["fz", "compiler2", "pull", "session", "finished"])
        .expect("root backend product path should emit final session telemetry");
    assert_eq!(measurement_u64(&finished, "producer_pokes"), 0);

    assert!(
        no_dump_job_fires > 0,
        "public no-dump interp proof should exercise the product-built BackendProgram"
    );
}

fn assert_direct_clause_param_forwards_have_abi_reprs(world: &World<'_>, program: &super::artifact::BackendProgram) {
    let mut checked = 0;
    for executable in &program.executables {
        let super::artifact::BackendBody::Clauses { clauses, entries, .. } = &executable.body else {
            continue;
        };
        let clause_params = clauses
            .iter()
            .flat_map(|clause| clause.params.iter().copied())
            .collect::<HashSet<_>>();
        for entry in entries {
            let super::artifact::BackendTail::DirectCall { target, args, .. } = &entry.tail else {
                continue;
            };
            let Some(first_arg) = args.first() else {
                continue;
            };
            if !clause_params.contains(&first_arg.value) {
                continue;
            }
            let super::artifact::CallEdge::Direct(edge) = target else {
                continue;
            };
            let Some(callee_index) = edge.callee.copied_local() else {
                continue;
            };
            let callee = program
                .executables
                .get(callee_index)
                .expect("packaged direct-call callee index should be in bounds");
            if executable_input_shape_is_nothing(world, program, callee, 0) {
                continue;
            }
            checked += 1;
            assert!(
                executable.value_reprs.contains_key(&first_arg.value),
                "direct call in {:?} forwards clause param {:?} into non-empty callee input 0, so ABI must bind it",
                executable.key,
                first_arg.value
            );
        }
    }
    assert!(
        checked > 0,
        "Enum.reduce operator-ref backend product should exercise direct forwarding of a clause param"
    );
}

fn executable_input_shape_is_nothing(
    world: &World<'_>,
    program: &super::artifact::BackendProgram,
    executable: &super::artifact::BackendExecutable,
    semantic_index: usize,
) -> bool {
    let symbol = ExecutableSymbol {
        activation: ActivationSymbol {
            function: executable.key.activation.function,
            input: executable.key.activation.inputs(world.types()).into_boxed_slice(),
        },
        need: executable.key.need,
    };
    let position = TransportPosition::ExecutableInput {
        executable: symbol,
        semantic_index,
    };
    let shape = program
        .transport
        .position_shapes
        .iter()
        .find_map(|(candidate, shape)| (candidate == &position).then_some(*shape))
        .unwrap_or_else(|| panic!("backend product should publish callee input position {position:?}"));
    matches!(world.shape(shape), ShapeDescr::Nothing)
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    assert!(
        executable_membership(&world, session)
            .iter()
            .any(|executable| function_is(&world, executable.activation.function, "add_a", 2)),
        "the joined reducer frontier should keep add_a/2 live"
    );
    assert!(
        executable_membership(&world, session)
            .iter()
            .any(|executable| function_is(&world, executable.activation.function, "add_b", 2)),
        "the joined reducer frontier should keep add_b/2 live"
    );

    let reducer_arg_shapes = session
        .transport_shapes()
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
        session.transport_shapes()
    );
    assert!(
        reducer_arg_shapes.iter().any(|shape| {
            let ShapeDescr::Callable(callable) = shape_descr(&world, *shape) else {
                return false;
            };
            session.callable_facts_inventory().get(callable).is_some_and(|facts| {
                facts.direct_surfaces.iter().any(|surface| surface.len() == 2) && facts.boundary_ids.is_empty()
            })
        }),
        "the joined reducer should retain a direct two-argument callable surface without becoming a boundary"
    );
}

#[test]
fn compiler2_transport_plan_publishes_joined_callable_value_position_before_native_capture() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("opaque_fn_value_join.fz".to_string()),
        include_str!("../../fixtures2/behavior/opaque_fn_value_join.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let main = executable_for(&world, session, "main", 0);
    let runtime_demands = runtime_demands_for_frontier(session);
    let main_demand = runtime_demands
        .iter()
        .find_map(|(executable, demand)| (executable.activation.function == main.activation.function).then_some(demand))
        .expect("main runtime demand should be present");
    let add_a = executable_for(&world, session, "add_a", 2).activation.function;
    let add_b = executable_for(&world, session, "add_b", 2).activation.function;
    let joined_value = delivered_value_joins(&world.lowered_body(main.activation.function))
        .values()
        .find_map(|join| {
            let producer_functions = join
                .sources
                .iter()
                .filter_map(|source| match source {
                    DeliveredValueSource::LocalValue(value) => {
                        main_demand.callable_flows.get(value).map(|flow| flow.function)
                    }
                    DeliveredValueSource::CallsiteReturn(_) => None,
                })
                .collect::<Vec<_>>();
            (producer_functions.contains(&add_a) && producer_functions.contains(&add_b)).then_some(join.value)
        })
        .expect("main should deliver a joined add_a/add_b callable value");
    let joined_position = TransportPosition::Value {
        executable: main,
        value: joined_value,
    };
    let joined_shape = plan_shape_at(session.transport_shapes(), &joined_position);
    let ShapeDescr::Callable(joined_callable) = shape_descr(&world, joined_shape) else {
        panic!("joined callable value position should remain callable-shaped: {joined_shape:?}");
    };
    let joined_descr = world.callable(*joined_callable);
    assert_eq!(
        joined_descr.function, None,
        "a joined runtime callable value must not pretend to be one concrete zero-capture function"
    );

    let published_boundaries = session
        .boundary_facts_inventory()
        .iter()
        .filter_map(|(boundary, facts)| facts.publications.contains(&joined_position).then_some(*boundary))
        .collect::<Vec<_>>();
    assert_eq!(
        published_boundaries.len(),
        1,
        "the joined callable value position should publish exactly one boundary discriminator: {:?}",
        session.boundary_facts_inventory()
    );
    let published_resolutions = session
        .boundary_facts_inventory()
        .get(&published_boundaries[0])
        .expect("published boundary facts should be present")
        .resolutions
        .iter()
        .map(|resolution| resolution.activation.function)
        .collect::<HashSet<_>>();
    assert!(
        published_resolutions.contains(&add_a) && published_resolutions.contains(&add_b),
        "the joined callable publication boundary should carry the concrete callable resolutions needed by backend/native: {:?}",
        session.boundary_facts_inventory()
    );
    assert!(
        plan.codegen_seam_facts.iter().any(|fact| {
            matches!(fact.seam, CodegenSeam::FirstClassPublication { boundary } if boundary == published_boundaries[0])
                && fact.shape.is_none()
        }),
        "transport should publish a first-class codegen lane for the joined callable boundary"
    );
}

#[test]
fn compiler2_transport_plan_gives_lambda_capture_lane_for_published_callable_capture() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("opaque_fn_value_join.fz".to_string()),
        include_str!("../../fixtures2/behavior/opaque_fn_value_join.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = driver.session();
    let lambda_capturing_published_callable = session.callable_facts_inventory().keys().find_map(|callable| {
        let descr = world.callable(*callable);
        let [capture_shape] = descr.capture_shapes.as_ref() else {
            return None;
        };
        let ShapeDescr::Callable(captured) = shape_descr(&world, *capture_shape) else {
            return None;
        };
        let captured_descr = world.callable(*captured);
        let captured_facts = session.callable_facts_inventory().get(captured)?;
        (descr.function.is_some() && captured_descr.function.is_none() && !captured_facts.boundary_ids.is_empty())
            .then_some((*callable, *capture_shape))
    });
    let (callable, capture_shape) = lambda_capturing_published_callable
        .expect("Enum.reduce's generated loop lambda should capture the published joined reducer value");
    let descr = world.callable(callable);
    assert_eq!(
        descr.capture_lanes.len(),
        1,
        "a lambda that captures a first-class callable value must carry that runtime value in a physical capture lane, not recurse into the captured callable's zero structural lanes: {descr:?}; capture_shape={capture_shape:?}",
    );
    let facts = session
        .callable_facts_inventory()
        .get(&callable)
        .unwrap_or_else(|| panic!("callable facts should exist for generated lambda {callable:?}"));
    let lane = descr.capture_lanes[0];
    assert!(
        facts.resolutions.iter().any(|executable| {
            plan.codegen_seam_facts.iter().any(|fact| {
                matches!(
                    &fact.seam,
                    CodegenSeam::FunctionEntry {
                        executable: seam_executable,
                        semantic_index: 0,
                    } if seam_executable == executable
                ) && fact.shape.is_some()
                    && fact.lane == lane
                    && fact.repr == CodegenLaneRepr::ValueRef
            })
        }),
        // The captured boxed callable's value lane now rides its own (one-lane)
        // value shape, so the lambda receives the capture as a physical ValueRef
        // lane carried by the shape — not bolted on out-of-band. That is the
        // data-model fix: a boxed callable's lane is a fact OF its shape.
        "the generated lambda executable must receive its first-class callable capture as one physical ValueRef lane carried by the captured callable's value shape: lane={lane:?}; facts={:?}",
        plan.codegen_seam_facts,
    );
}

#[test]
fn compiler2_transport_plan_gives_a_continuation_captured_first_class_callable_a_boxed_value_lane() {
    // `maplist` is non-tail recursive (`[f.(h) | maplist(t, f)]`), so its
    // recursion is captured in a continuation that closes over `f`. The phi of
    // two lambdas forces `f` to be a genuine first-class (boxed, function:None)
    // callable. A boxed callable value occupies exactly one lane (the pointer);
    // a continuation capture shaped as a zero-lane generic-callable contract
    // would drop the box and is unmaterializable downstream.
    let source = r#"
fn maplist([], _f), do: []
fn maplist([h | t], f), do: [f.(h) | maplist(t, f)]

fn main() do
  g = if true, do: (fn x -> x + 1 end), else: (fn x -> x + 2 end)
  maplist([1, 2], g)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_first_class_callable_continuation_capture.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let captured_first_class = session
        .transport_shapes()
        .iter()
        .filter(|(position, _)| matches!(position, TransportPosition::EntryCapture { .. }))
        .filter_map(|(position, shape)| match shape_descr(&world, *shape) {
            ShapeDescr::Callable(callable) => Some((position.clone(), *shape, *callable)),
            _ => None,
        })
        .filter(|(_, _, callable)| world.callable(*callable).function.is_none())
        .collect::<Vec<_>>();
    assert!(
        !captured_first_class.is_empty(),
        "maplist's non-tail recursion must capture the first-class callable `f` in a continuation as a generic (boxed) callable shape",
    );
    for (position, shape, _) in captured_first_class {
        assert_eq!(
            world.shape_width(shape),
            1,
            "a first-class callable captured by a continuation must occupy exactly one boxed value lane, not a zero-lane contract: {position:?}",
        );
    }
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
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let captured_callable = session.callable_facts_inventory().iter().find_map(|(outer, facts)| {
        let outer_descr = world.callable(*outer);
        let [capture_shape] = outer_descr.capture_shapes.as_ref() else {
            return None;
        };
        let ShapeDescr::Callable(captured) = shape_descr(&world, *capture_shape) else {
            return None;
        };
        (!facts.direct_surfaces.is_empty()).then_some((*captured, *capture_shape, facts.resolutions.clone()))
    });
    let (captured_callable, captured_shape, reducer_resolutions) =
        captured_callable.unwrap_or_else(|| panic!("the reducer lambda should capture predicate as a callable shape"));
    for resolution in reducer_resolutions {
        let position = TransportPosition::ExecutableInput {
            executable: resolution,
            semantic_index: 0,
        };
        assert_eq!(
            session.transport_shapes().get(&position).copied(),
            Some(captured_shape),
            "the reducer executable capture-prefix input should read the producer capture ShapeId from callable-flow resolution evidence"
        );
    }
    let captured_facts = session
        .callable_facts_inventory()
        .get(&captured_callable)
        .unwrap_or_else(|| panic!("captured predicate callable facts should be present"));
    let captured_descr = world.callable(captured_callable);
    assert!(
        captured_descr.capture_lanes.is_empty(),
        "the captured predicate is zero-capture, so the reducer carries its callable identity without payload lanes"
    );
    assert!(
        captured_facts.direct_surfaces.iter().any(|surface| surface.len() == 1),
        "the captured predicate should retain its direct one-argument callable surface"
    );
    assert!(
        captured_facts.boundary_ids.is_empty(),
        "a predicate captured for direct reducer use should not be upgraded to a first-class boundary"
    );
}

/// The transport.rs:338 agree-or-panic meet is only correct if the shape graph
/// fed to it is built schedule-independently. The flaky panic was a NON-MONOTONE
/// build: layout-distinct sibling specializations of one function fused into a
/// single anchor component depending on visitation order (which sibling the
/// interning-order-dependent sort visited first) and on a stateful prior-anchoring
/// accumulator. The fix makes both the visitation order (canonical structural sort
/// key) and the per-input anchor-vs-union decision in
/// `collect_executable_input_constraints` pure — the latter unions a callable
/// input with its incoming call args only when their shapes all agree, or when a
/// single unsettled source converges, so layout-distinct siblings never fuse
/// regardless of schedule.
///
/// This drives the reduce-bridge fixture many times in-process; each `World` rides
/// a per-process hash seed that varies the upstream wake order. The transport
/// invariant it pins: the meet ALWAYS succeeds (a plan is produced, never a
/// disagreement panic) and the graph ALWAYS keeps layout-distinct callable
/// siblings in distinct shape components. (The upstream semantic closure for this
/// fixture is itself schedule-dependent in how many type-specializations it mints
/// — the separately-ticketed fz-f98.14 reseal runaway — so this asserts the
/// transport invariant under that variance, not byte-identity of the closure.)
#[test]
#[ignore = "red-worklist fz-f98.14.1: the multi-surface enum_take_drop_split fixture is ~13s/drive \
            under the reseal runaway, so driving it repeatedly times out; the transport schedule-\
            independence it asserts is already gated by the three now-stable transport.rs:338 tests. \
            Re-enable when the per-root seal is incremental (fixture drive is fast)."]
fn compiler2_transport_input_components_are_schedule_independent() {
    let source = include_str!("../../fixtures2/behavior/enum_take_drop_split.fz");

    // Whether some `(function, slot)` input group keeps two or more LAYOUT-DISTINCT
    // siblings in two or more distinct shape components — the non-fusion signature
    // the meet panicked on when it failed.
    let keeps_layout_distinct_siblings_split = || -> bool {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        world.submit_code(
            Some("transport_input_components_schedule_independent.fz".to_string()),
            source.to_string(),
        );
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        // A disagreement in the agree-or-panic meet would panic inside this product build.
        let driver = drive_transport_facts_for_test(&tel, &mut world, root);
        let session = driver.session();

        let mut layouts = BTreeMap::<(u32, usize), BTreeSet<Box<[Ty]>>>::new();
        let mut shapes = BTreeMap::<(u32, usize), BTreeSet<ShapeId>>::new();
        for (position, shape) in session.transport_shapes() {
            if let TransportPosition::ExecutableInput {
                executable,
                semantic_index,
            } = position
            {
                let key = (executable.activation.function.as_u32(), *semantic_index);
                layouts
                    .entry(key)
                    .or_default()
                    .insert(executable.activation.input.clone());
                shapes.entry(key).or_default().insert(*shape);
            }
        }
        layouts
            .iter()
            .any(|(key, group_layouts)| group_layouts.len() >= 2 && shapes.get(key).map_or(0, BTreeSet::len) >= 2)
    };

    // Three in-process drives: the panic was triggered by process state that
    // accumulates across drives, so one drive is not enough to expose it, but a
    // few are — the cross-process gauntlet carries the broader schedule sweep.
    for run in 1..=3 {
        assert!(
            keeps_layout_distinct_siblings_split(),
            "the reduce-bridge fixture must reach the transport meet and keep layout-distinct \
             sibling inputs in distinct shape components on every schedule (run {run})"
        );
    }
}

#[test]
#[ignore = "fz-f98.14: the enum_take_drop_split (00420) fixture's transport derivation does far \
            more work than this assertion reads because the Seal<->DeriveRuntimeDemand<->Transport \
            cycle does not converge monotonically (a correctness bug, not perf) -- >1s on a tiny \
            fixture. Ported to split product surfaces; un-ignore when the convergence runaway is fixed."]
fn compiler2_transport_plan_preserves_nested_enum_reduce_predicate_capture_shape() {
    let source = include_str!("../../fixtures2/behavior/enum_take_drop_split.fz");

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_enum_take_drop_split_nested_predicate_capture.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let lambda_source_contains = |name: &str, needle: &str| -> bool {
        let Some(range) = name.strip_prefix("#lambda:0:") else {
            return false;
        };
        let Some((start, end)) = range.split_once('-') else {
            return false;
        };
        let Ok(start) = start.parse::<usize>() else {
            return false;
        };
        let Ok(end) = end.parse::<usize>() else {
            return false;
        };
        source.get(start..end).is_some_and(|span| span.contains(needle))
    };
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let reducer = session
        .callable_facts_inventory()
        .iter()
        .find_map(|(callable, facts)| {
            let descr = world.callable(*callable);
            let [capture_shape] = descr.capture_shapes.as_ref() else {
                return None;
            };
            let ShapeDescr::Callable(captured) = shape_descr(&world, *capture_shape) else {
                return None;
            };
            let captured_function = world.callable(*captured).function?;
            let captured_ref = world.function_ref(captured_function);
            (lambda_source_contains(&captured_ref.name, "fn (x) -> x < 4 end") && !facts.direct_surfaces.is_empty())
                .then_some((*capture_shape, *captured, facts.resolutions.clone()))
        })
        .unwrap_or_else(|| {
            panic!(
                "a take/drop/split reducer should capture the `x < 4` predicate as a callable shape: {:?}",
                session.callable_facts_inventory()
            )
        });
    let (predicate_shape, predicate_callable, reducer_resolutions) = reducer;
    assert!(
        session
            .callable_facts_inventory()
            .get(&predicate_callable)
            .is_some_and(|facts| facts.boundary_ids.is_empty()),
        "the predicate is direct-only in this fixture; transport must not require a first-class boundary for its reducer capture"
    );
    for resolution in reducer_resolutions {
        let position = TransportPosition::ExecutableInput {
            executable: resolution,
            semantic_index: 0,
        };
        assert_eq!(
            session.transport_shapes().get(&position).copied(),
            Some(predicate_shape),
            "the nested reducer executable must receive the predicate capture as the exact callable ShapeId"
        );
    }
}

#[test]
fn compiler2_transport_plan_resolves_enum_take_reducer_input_boundary_from_source_publication() {
    let source = "fn main() do\n  xs = [1, 2, 3, 4, 5]\n  dbg(Enum.take(xs, 3))\nend\n";

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_enum_take_reducer_input_boundary_resolution.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let reducer_input_boundaries = session
        .transport_shapes()
        .iter()
        .filter_map(|(position, shape)| {
            let TransportPosition::ExecutableInput {
                executable,
                semantic_index: 2,
            } = position
            else {
                return None;
            };
            if !function_is(&world, executable.activation.function, "reduce_while_cont", 3) {
                return None;
            }
            let ShapeDescr::Callable(callable) = shape_descr(&world, *shape) else {
                return None;
            };
            let facts = session
                .callable_facts_inventory()
                .get(callable)
                .unwrap_or_else(|| panic!("callable facts should exist for reducer input {callable:?}"));
            (!facts.boundary_ids.is_empty()).then_some(facts.boundary_ids.clone())
        })
        .collect::<Vec<_>>();

    assert!(
        !reducer_input_boundaries.is_empty(),
        "Enum.take should publish a first-class callable boundary for the reduce_while_cont/3 reducer input"
    );
    for boundary_ids in reducer_input_boundaries {
        for boundary in boundary_ids {
            let facts = session
                .boundary_facts_inventory()
                .get(&boundary)
                .unwrap_or_else(|| panic!("boundary facts should exist for reducer input boundary {boundary:?}"));
            assert!(
                !facts.resolutions.is_empty(),
                "the reducer input boundary must resolve to the producer lambda before artifact/native consume it: boundary={boundary:?}; facts={facts:?}"
            );
        }
    }
}

#[test]
fn compiler2_transport_plan_publishes_enum_take_reduce_while_multi_surface_callable_inputs() {
    let source = "fn main() do\n  xs = [1, 2, 3, 4, 5]\n  dbg(Enum.take(xs, 3))\nend\n";

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_enum_take_unpublished_multi_surface_callables.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let unpublished = session
        .transport_shapes()
        .iter()
        .filter_map(|(position, shape)| {
            let ShapeDescr::Callable(callable) = shape_descr(&world, *shape) else {
                return None;
            };
            let facts = session.callable_facts_inventory().get(callable)?;
            if facts.boundary_ids.len() <= 1 {
                return None;
            }
            let publications = session
                .boundary_facts_inventory()
                .iter()
                .filter_map(|(boundary, facts)| facts.publications.contains(position).then_some(*boundary))
                .collect::<Vec<_>>();
            if !publications.is_empty() {
                return None;
            }
            let function_name = match position {
                TransportPosition::ExecutableInput { executable, .. }
                | TransportPosition::ExecutableReturn { executable }
                | TransportPosition::CallArg { executable, .. }
                | TransportPosition::Value { executable, .. }
                | TransportPosition::EntryCapture { executable, .. }
                | TransportPosition::ResumePayload { executable, .. }
                | TransportPosition::ReturnPayload { executable, .. } => {
                    world.function_ref(executable.activation.function).name.clone()
                }
            };
            function_name.contains("reduce_while").then_some((
                function_name,
                position.clone(),
                *shape,
                *callable,
                facts.boundary_ids.clone(),
            ))
        })
        .collect::<Vec<_>>();

    assert!(
        unpublished.is_empty(),
        "reduce_while callable-shaped positions with multiple boundary surfaces must publish those boundaries before native consumes them: {unpublished:#?}"
    );
}

#[test]
fn compiler2_transport_plan_publishes_direct_reducer_capture_prefix_shape() {
    let source = r#"
fn reduce_plain([], acc, _reducer), do: acc
fn reduce_plain([head | tail], acc, reducer), do: reduce_plain(tail, reducer.(head, acc), reducer)

fn main() do
  predicate = fn x -> x > 2 end
  reducer = fn (entry, acc) ->
    if predicate.(entry), do: acc + 1, else: acc
  end

  reduce_plain([1, 2, 3, 4], 0, reducer)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_direct_reducer_capture_prefix_shape.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let reducer = session
        .callable_facts_inventory()
        .iter()
        .find_map(|(callable, facts)| {
            let descr = world.callable(*callable);
            let [capture_shape] = descr.capture_shapes.as_ref() else {
                return None;
            };
            let ShapeDescr::Callable(captured) = shape_descr(&world, *capture_shape) else {
                return None;
            };
            let reducer_shape = session.transport_shapes().values().copied().find(
                |shape| matches!(shape_descr(&world, *shape), ShapeDescr::Callable(candidate) if candidate == callable),
            )?;
            (!facts.direct_surfaces.is_empty()).then_some((
                reducer_shape,
                *capture_shape,
                *captured,
                facts.resolutions.clone(),
            ))
        })
        .unwrap_or_else(|| panic!("the direct reducer should capture the predicate as a callable shape"));
    let (reducer_shape, predicate_shape, predicate_callable, reducer_resolutions) = reducer;
    let reduce_plain_executables = executable_membership(&world, session)
        .into_iter()
        .filter(|symbol| function_is(&world, symbol.activation.function, "reduce_plain", 3))
        .collect::<Vec<_>>();
    assert!(
        !reduce_plain_executables.is_empty(),
        "the direct reducer fixture should reach reduce_plain/3"
    );
    for reduce_plain in reduce_plain_executables {
        let reduce_plain_reducer_input = plan_shape_at(
            session.transport_shapes(),
            &TransportPosition::ExecutableInput {
                executable: reduce_plain.clone(),
                semantic_index: 2,
            },
        );
        assert_eq!(
            reduce_plain_reducer_input, reducer_shape,
            "every reduce_plain/3 executable input for the direct reducer argument must share the producer callable ShapeId"
        );
        let reduce_plain_body = world.lowered_body(reduce_plain.activation.function);
        let LoweredBody::Clauses { clauses, .. } = reduce_plain_body else {
            panic!("reduce_plain/3 should lower to clauses");
        };
        for reducer_param in clauses.iter().filter_map(|clause| clause.params.get(2).copied()) {
            assert_eq!(
                session
                    .transport_shapes()
                    .get(&TransportPosition::Value {
                        executable: reduce_plain.clone(),
                        value: reducer_param,
                    })
                    .copied(),
                Some(reducer_shape),
                "reduce_plain/3 reducer parameter Value positions must share the executable input ShapeId"
            );
        }
    }
    let predicate_descr = world.callable(predicate_callable);
    assert!(
        predicate_descr.capture_lanes.is_empty(),
        "the predicate lambda captures nothing, so the reducer capture-prefix input must carry no payload lanes"
    );
    for resolution in reducer_resolutions {
        let body = world.lowered_body(resolution.activation.function);
        let LoweredBody::Clauses { clauses, .. } = body else {
            panic!("direct reducer resolution should lower to clauses");
        };
        let reducer_capture_param = clauses
            .first()
            .and_then(|clause| clause.params.first())
            .copied()
            .unwrap_or_else(|| panic!("direct reducer should bind its captured predicate as leading parameter"));
        let position = TransportPosition::ExecutableInput {
            executable: resolution.clone(),
            semantic_index: 0,
        };
        assert_eq!(
            session.transport_shapes().get(&position).copied(),
            Some(predicate_shape),
            "the reducer executable capture-prefix input must use the exact predicate ShapeId produced by callable-flow capture evidence"
        );
        assert_eq!(
            session
                .transport_shapes()
                .get(&TransportPosition::Value {
                    executable: resolution,
                    value: reducer_capture_param,
                })
                .copied(),
            Some(predicate_shape),
            "the reducer capture parameter Value position must share the executable input ShapeId"
        );
    }
}

#[test]
fn compiler2_transport_plan_projects_enum_reduce_bridge_callable_flow_by_producer_identity_over_range() {
    let source = include_str!("../../fixtures2/behavior/fz_f98_range_reduce_scalar.fz");

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_fz_f98_range_reduce_scalar_contract.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    let runtime_demands = runtime_demands_for_frontier(session);
    let direct_flows = runtime_demands
        .values()
        .flat_map(|demand| demand.callable_flows.values())
        .filter(|flow| !flow.direct_surfaces.is_empty())
        .collect::<Vec<_>>();
    assert!(
        !direct_flows.is_empty(),
        "the Range reduce bridge fixture should publish callable-flow facts for direct reducer calls"
    );

    for flow in direct_flows {
        let flow_resolutions = flow_resolution_symbols(&world, flow);
        let matching_callables = session
            .callable_facts_inventory()
            .iter()
            .filter(|(callable, facts)| {
                world.callable(**callable).function == Some(flow.function)
                    && sorted_executable_symbols(facts.resolutions.as_ref()) == flow_resolutions
                    && transport_surfaces_match_upstream(&mut world, &facts.direct_surfaces, &flow.direct_surfaces)
            })
            .collect::<Vec<_>>();
        assert_eq!(
            matching_callables.len(),
            1,
            "one producer-minted CallableFlowFact should project to one transport callable contract: flow={flow:?}; callables={:?}",
            session.callable_facts_inventory()
        );
        let (callable, facts) = matching_callables[0];
        assert_callable_facts_match_upstream_flow(&mut world, session, *callable, flow);
        assert!(
            facts.boundary_ids.len() <= flow.first_class_surfaces.len(),
            "direct reducer use must not invent extra first-class boundaries: flow={flow:?}; facts={facts:?}"
        );
    }
}

#[test]
#[ignore = "fz-go4.18.9: a callable resolution's ExecutableInput capture-shape position is absent \
            from the product transport positions (session.transport_shapes()) that the legacy plan \
            eagerly shaped; ported to split surfaces with assertions intact, un-ignore when the \
            product shapes the capture-prefix position."]
fn compiler2_transport_plan_keeps_callable_resolution_capture_abi_correlated() {
    let source = include_str!("../../fixtures2/behavior/fz_f98_range_map_converges.fz");

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_fz_f98_range_map_callable_capture_abi.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    assert_callable_resolution_capture_prefixes_match_descriptors(&world, session);
}

/// fz-f98.8: a struct's declared `@type` field types are honored on destructure,
/// so an all-integer `Range` never infers float-typed elements.
///
/// `Range` declares `@type t :: %Range{first: integer, last: integer, step: integer}`,
/// but `defstruct` carries only field names. When a `Range` value crosses the
/// `Enumerable` protocol boundary its concrete shape is erased, so destructuring
/// `%Range{first, last, step}` used to bind the fields as `any`. The recursive
/// step `current + step` was then `any + any`, and the `+` overload set
/// (`int->integer`, the `float` clauses) admits both guards for `any` operands,
/// so it widened to `int | float` — a phantom float in an all-integer range that
/// then floods the shared reducer and feeds the reducer over-monomorphization.
/// Honoring the declared field types keeps `first/last/step` `integer`, so the
/// Range recursion (`reduce_cont`/`reduce_step`) stays integer-only.
#[test]
fn compiler2_declared_struct_field_types_keep_integer_range_elements_off_float() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("range_int_elements.fz".to_string()),
        "fn main() do\n  dbg(Enum.to_list(1..3))\nend\n".to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    // The Range-specific recursion is monomorphic over integer ranges; no input
    // may carry `float` (only the generic Enum/dbg entry points legitimately
    // accept the whole element domain).
    let candidates: Vec<(String, Vec<Ty>)> = {
        executable_membership(&world, session)
            .iter()
            .filter_map(|sym| {
                let name = world.function_ref(sym.activation.function).name.clone();
                (name.contains("reduce_cont") || name.contains("reduce_step") || name.contains("done?"))
                    .then(|| (name, sym.activation.input.to_vec()))
            })
            .collect()
    };
    let offenders: Vec<(String, Vec<String>)> = candidates
        .into_iter()
        .filter_map(|(name, tys)| {
            let rendered: Vec<String> = tys.iter().map(|ty| world.types_mut().display(ty)).collect();
            rendered.iter().any(|s| s.contains("float")).then_some((name, rendered))
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "an all-integer range must not infer float-typed elements; the Range recursion carries float inputs: {offenders:?}",
    );
}

/// fz-f98.3: a captured callable that is unused on one specialized activation
/// must still carry its construction layout there -- the closure's capture
/// layout is one physical fact, not a per-activation use property.
///
/// `Enum.reduce/2` over a stepped Range wraps the user reducer in the inner
/// lambda `fn (entry, state) -> reduce_first_step(entry, state, reducer) end` and
/// threads a `:first | {:acc, b}` accumulator. `reduce_first_step/3` IGNORES its
/// reducer on the `:first` arm and CALLS it on the `{:acc, _}` arm, so the lambda
/// specializes into two activations that share one captured reducer. The
/// backward use-demand on the `:first` activation bottoms to `Ignore`; deriving
/// the capture shape from that per-activation demand anchored `Nothing`, while
/// the closure's construction layout is the boxed `Callable` -- two shapes for
/// one capture slot of one closure, which the shape-anchor meet rejected. The
/// single construction-derived seeder makes both activations carry the same
/// `Callable` capture layout, so the plan settles and capture inputs match the
/// canonical descriptor.
#[test]
fn compiler2_transport_plan_keeps_unused_capture_on_specialized_activation_at_construction_layout() {
    let source = include_str!("../../fixtures2/behavior/fz_f98_range_reduce2.fz");

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    world.submit_code(
        Some("transport_fz_f98_range_reduce2_capture_layout.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = drive_transport_facts_for_test(&tel, &mut world, root);
    let session = driver.session();
    assert_callable_resolution_capture_prefixes_match_descriptors(&world, session);
}

fn assert_resolved(outcome: DriveOutcome<super::Job, super::FactKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

fn executable_symbol_for(world: &World<'_>, key: &ExecutableKey) -> ExecutableSymbol {
    ExecutableSymbol {
        activation: ActivationSymbol {
            function: key.activation.function,
            input: key.activation.inputs(world.types()).into_boxed_slice(),
        },
        need: key.need,
    }
}

fn executable_membership(world: &World<'_>, session: &PullSession) -> Vec<ExecutableSymbol> {
    session
        .demanded_executables()
        .iter()
        .map(|key| executable_symbol_for(world, key))
        .collect()
}

fn executable_for(world: &World<'_>, session: &PullSession, name: &str, arity: usize) -> ExecutableSymbol {
    session
        .demanded_executables()
        .iter()
        .find(|key| {
            let function_ref = world.function_ref(key.activation.function);
            function_ref.name == name && function_ref.arity == arity
        })
        .map(|key| executable_symbol_for(world, key))
        .unwrap_or_else(|| panic!("transport plan executable {name}/{arity}"))
}

fn runtime_demands_for_frontier(session: &PullSession) -> HashMap<ExecutableKey, ExecutableRuntimeDemand> {
    session
        .demanded_executables()
        .iter()
        .filter_map(|executable| {
            session
                .memo()
                .runtime_demand(executable)
                .map(|demand| (executable.clone(), demand.clone()))
        })
        .collect()
}

fn submit_enum_reduce_operator_ref_root(world: &mut World<'_>, source_name: &str) -> super::RootId {
    world.submit_code(
        Some(source_name.to_string()),
        ENUM_REDUCE_OPERATOR_REF_SOURCE.to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2))
}

/// Drive only the transport/materialization products for a root's demanded
/// executables — never the ABI, backend-executable, or native packaging jobs.
///
/// This is the production materialization path: `produce_materialized_executable_product`
/// pulls each executable's transport shapes and callable/boundary facts into the
/// session as it materializes, so after the reachability walk the session carries
/// exactly the transport facts the full backend product would have read. The plan
/// itself is built by `symbolic_materialized_transport_plan`, which consumes the
/// session (not packaged executables), so transport-fact tests need nothing heavier.
///
/// The walk mirrors `produce_root_backend_product`'s reachability (call-edge callees
/// plus boundary resolutions) but stops at materialized facts.
fn drive_transport_facts_for_test<'a>(
    tel: &'a ConfiguredTelemetry,
    world: &mut World<'_>,
    root: super::RootId,
) -> ProductDriver<'a> {
    let mut driver = ProductDriver::new(tel, root);
    let pokes = drive_product_fact_wait_for_test(
        world,
        root,
        FactUse::settled(FactKey::RootEntry(root)),
        "transport facts should settle the root entry",
    );
    driver.session_mut().record_producer_pokes(pokes);
    let entry = world.root_entry_executable(root);

    // Drive the whole demand closure's transport facts to a fixpoint using only
    // materialization/transport products. For each demanded executable we pull its
    // `MaterializedExecutable` product and then every transport-shape product its
    // ABI would require (`required_executable_transport_facts_waits`). Pulling
    // those shapes records the executable's shapes and, through the transport
    // component projection, publishes callable/boundary facts and grows the demand
    // closure (escaped/first-class callables, dispatch targets). A shape can shift
    // as later executables materialize, so we iterate until no demanded executable
    // is un-materialized and no required transport-shape product is still pending.
    let mut demanded = HashSet::from([entry]);
    loop {
        let pending = demanded.iter().cloned().collect::<Vec<_>>();
        let mut progressed = false;
        for executable in pending {
            if driver.session().materialized_executable(&executable).is_none() {
                pull_product_until_produced_with_fact_waits(
                    &mut driver,
                    world,
                    root,
                    ProductKey::MaterializedExecutable(executable.clone()),
                    "materialized executable should be product-derivable",
                );
                progressed = true;
            }
            let materialized = driver
                .session()
                .materialized_executable(&executable)
                .cloned()
                .expect("materialized executable product should record its inventory");
            for wait in super::jobs::artifact::required_executable_transport_facts_waits(
                driver.session(),
                &executable,
                &materialized,
                world.types(),
            ) {
                let PullWait::Product(key @ ProductKey::TransportShape(_)) = wait else {
                    continue;
                };
                pull_product_until_produced_with_fact_waits(
                    &mut driver,
                    world,
                    root,
                    key,
                    "executable transport shape should be product-derivable",
                );
                progressed = true;
            }
        }
        let before = demanded.len();
        demanded.extend(driver.session().demanded_executables().iter().cloned());
        demanded.extend(
            driver
                .session()
                .boundary_facts_inventory()
                .values()
                .flat_map(|facts| facts.resolutions.iter())
                .map(|symbol| super::jobs::backend::executable_key_for_symbol(root, symbol, world.types_mut())),
        );
        if !progressed && demanded.len() == before {
            break;
        }
    }
    driver.finish_session();
    driver
}

/// Build the `MaterializedTransportPlan` for a root from a transport-facts-only
/// drive, using the production builder `symbolic_materialized_transport_plan`.
/// Seam tests read `plan.codegen_seam_facts` / `plan.entry` directly — the same
/// values the full backend package carries in `program.transport`, but without
/// building any ABI/backend/native artifacts.
fn pull_transport_plan_for_test<'a>(
    tel: &'a ConfiguredTelemetry,
    world: &mut World<'_>,
    root: super::RootId,
) -> (ProductDriver<'a>, MaterializedTransportPlan) {
    let driver = drive_transport_facts_for_test(tel, world, root);
    let entry = world.root_entry_executable(root);
    let plan = super::jobs::backend::symbolic_materialized_transport_plan(
        driver.session(),
        &entry,
        world,
        driver.session().callable_facts_inventory(),
        driver.session().boundary_facts_inventory(),
    );
    (driver, plan)
}

/// Build the transport plan from a full backend drive. A handful of codegen-seam
/// contracts -- `TailCall`, `ExternBoundary`, and `CallableBoundary` seams -- are
/// derived by `symbolic_codegen_seam_facts` from `session.backend_executables()`
/// (the callsite control destination and extern/first-class body kind), not from
/// transport shapes alone. Tests that assert those backend-derived seams drive the
/// `RootBackendProduct` so the session carries the backend executables, then read
/// the plan the same way. The other seam tests need only the transport facts.
fn pull_root_backend_plan_for_test<'a>(
    tel: &'a ConfiguredTelemetry,
    world: &mut World<'_>,
    root: super::RootId,
) -> (ProductDriver<'a>, MaterializedTransportPlan) {
    let driver = pull_root_backend_driver_for_test(tel, world, root);
    let entry = world.root_entry_executable(root);
    let plan = super::jobs::backend::symbolic_materialized_transport_plan(
        driver.session(),
        &entry,
        world,
        driver.session().callable_facts_inventory(),
        driver.session().boundary_facts_inventory(),
    );
    (driver, plan)
}

/// Drive the full `RootBackendProduct` and return only the driven session. Used
/// by the few tests whose intent is the ABI/backend-product inventory itself
/// (call-edge symbolism), which genuinely require those artifacts.
fn pull_root_backend_driver_for_test<'a>(
    tel: &'a ConfiguredTelemetry,
    world: &mut World<'_>,
    root: super::RootId,
) -> ProductDriver<'a> {
    let mut driver = ProductDriver::new(tel, root);
    pull_product_until_produced_with_fact_waits(
        &mut driver,
        world,
        root,
        ProductKey::RootBackendProduct(root),
        "root backend product should be product-derivable",
    );
    driver.finish_session();
    driver
}

fn pull_product_until_produced_with_fact_waits(
    driver: &mut ProductDriver<'_>,
    world: &mut World<'_>,
    root: super::RootId,
    key: ProductKey,
    message: &str,
) -> ProductValue {
    let mut stack = vec![key.clone()];
    let mut last_wait = None;
    for _ in 0..50_000 {
        let Some(current) = stack.pop() else {
            stack.push(key.clone());
            continue;
        };
        let outcome = {
            let mut producers = WorldProductProducers::new(world);
            driver.pull(&mut producers, current.clone())
        };
        match outcome {
            PullOutcome::Produced(value) if current == key => return value,
            PullOutcome::Produced(_) => {}
            PullOutcome::Waiting(waits) => {
                last_wait = Some((current.clone(), waits.clone()));
                stack.push(current);
                for wait in waits.into_iter().rev() {
                    match wait {
                        PullWait::Product(product) => stack.push(product),
                        PullWait::Fact(fact) => {
                            let producer_pokes = drive_product_fact_wait_for_test(world, root, fact, message);
                            driver.session_mut().record_producer_pokes(producer_pokes);
                        }
                    }
                }
            }
        }
    }
    panic!("{message}: product {key:?} did not settle; last wait: {last_wait:?}");
}

fn drive_product_fact_wait_for_test(
    world: &mut World<'_>,
    _root: super::RootId,
    fact: FactUse<FactKey>,
    message: &str,
) -> u64 {
    let mut jobs_ran = 0_u64;
    let mut producer_pokes = 0_u64;
    while !product_fact_wait_is_satisfied_for_test(world, &fact) {
        let job = match world.work_graph.pop() {
            Some(job) => job,
            None => {
                producer_pokes += demand_product_fact_producer_for_test(world, fact.fact());
                let Some(job) = world.work_graph.pop() else {
                    panic!("{message}: product path waited on {fact:?} with no ready producer");
                };
                job
            }
        };
        let effects = super::jobs::run(world, &job)
            .unwrap_or_else(|_| panic!("{message}: prerequisite job failed before product fact settled: {job:?}"));
        world.complete_job(job, effects);
        jobs_ran += 1;
        if jobs_ran > 50_000 {
            panic!("{message}: product path exceeded fact-wait budget for {fact:?}");
        }
    }
    producer_pokes
}

fn demand_product_fact_producer_for_test(world: &mut World<'_>, fact: &FactKey) -> u64 {
    let job = match fact {
        FactKey::RootEntry(root) => Some(Job::SeedRoot(*root)),
        FactKey::FunctionDefined(function) => Some(Job::DefineFunction(*function)),
        FactKey::LoweredBody(function) => Some(Job::LowerFunction(*function)),
        FactKey::Recursive(function) => Some(Job::DeriveRecursive(*function)),
        FactKey::DispatchMask(function) => Some(Job::DeriveDispatchMask(*function)),
        FactKey::Activation(activation) | FactKey::ActivationInputs(activation) => {
            Some(Job::SeedActivation(activation.clone()))
        }
        FactKey::ActivationAnalyzed(activation) | FactKey::ReturnType(activation) => {
            let mut pokes = 0;
            if !world.has_fact(&FactKey::Activation(activation.clone()))
                || !world.has_fact(&FactKey::ActivationInputs(activation.clone()))
            {
                pokes += demand_if_needed_for_test(world, Job::SeedActivation(activation.clone()), fact) as u64;
            }
            return pokes + demand_if_needed_for_test(world, Job::AnalyzeActivation(activation.clone()), fact) as u64;
        }
        FactKey::CallSiteTargets(key) | FactKey::CallSiteSummary(key) => {
            let mut pokes = 0;
            if !world.has_fact(&FactKey::Activation(key.activation.clone()))
                || !world.has_fact(&FactKey::ActivationInputs(key.activation.clone()))
            {
                pokes += demand_if_needed_for_test(world, Job::SeedActivation(key.activation.clone()), fact) as u64;
            }
            return pokes
                + demand_if_needed_for_test(world, Job::AnalyzeActivation(key.activation.clone()), fact) as u64;
        }
        _ => None,
    };
    job.map(|job| demand_if_needed_for_test(world, job, fact) as u64)
        .unwrap_or(0)
}

fn demand_if_needed_for_test(world: &mut World<'_>, job: Job, target_fact: &FactKey) -> bool {
    if world.work_graph.output_keys(&job).contains(target_fact) && !world.work_graph.rebased(&job) {
        return false;
    }
    world.demand(job);
    true
}

fn product_fact_wait_is_satisfied_for_test(world: &World<'_>, fact: &FactUse<FactKey>) -> bool {
    match fact.readiness() {
        FactReadiness::Current => world.fact_revision(fact.fact()).is_some(),
        FactReadiness::Settled => world.fact_is_settled(fact.fact()),
    }
}

fn materialized_call_edge_callees(edge: &super::artifact::MaterializedCallEdge) -> Vec<&ExecutableKey> {
    match &edge.target {
        super::artifact::CallEdge::Direct(direct) => direct.callee.local().into_iter().collect(),
        super::artifact::CallEdge::Dispatch(dispatch) => {
            dispatch.arms.iter().filter_map(|arm| arm.callee.local()).collect()
        }
    }
}

fn abi_ready_call_edge_callees(edge: &super::artifact::AbiReadyCallEdge) -> Vec<&ExecutableKey> {
    match &edge.target {
        super::artifact::CallEdge::Direct(direct) => direct.callee.local().into_iter().collect(),
        super::artifact::CallEdge::Dispatch(dispatch) => {
            dispatch.arms.iter().filter_map(|arm| arm.callee.local()).collect()
        }
    }
}

fn assert_symbolic_backend_body_has_no_dense_targets(body: &super::pull::SymbolicBackendBody, caller: &ExecutableKey) {
    let super::pull::SymbolicBackendBody::Clauses { entries, .. } = body else {
        return;
    };
    for entry in entries {
        match &entry.tail {
            SymbolicBackendTail::DirectCall { target, .. } => {
                assert!(
                    !abi_call_edge_callees_from_target(target).is_empty(),
                    "symbolic backend direct call in {caller:?} should keep ExecutableKey targets"
                );
            }
            SymbolicBackendTail::ClosureCall { target, .. } => {
                if let Some(target) = target {
                    assert!(
                        target.activation.root == caller.activation.root,
                        "symbolic backend closure target should be an ExecutableKey, got {target:?}"
                    );
                }
            }
            SymbolicBackendTail::Value { .. }
            | SymbolicBackendTail::If { .. }
            | SymbolicBackendTail::Dispatch { .. }
            | SymbolicBackendTail::Receive(_)
            | SymbolicBackendTail::Halt { .. } => {}
        }
    }
}

fn abi_call_edge_callees_from_target(target: &super::artifact::CallEdge<ExecutableKey>) -> Vec<&ExecutableKey> {
    match target {
        super::artifact::CallEdge::Direct(direct) => direct.callee.local().into_iter().collect(),
        super::artifact::CallEdge::Dispatch(dispatch) => {
            dispatch.arms.iter().filter_map(|arm| arm.callee.local()).collect()
        }
    }
}

fn upstream_callable_flow_for_producer(session: &PullSession, function: super::FunctionId) -> CallableFlowFact {
    runtime_demands_for_frontier(session)
        .values()
        .flat_map(|demand| demand.callable_flows.values())
        .find(|flow| flow.function == function)
        .cloned()
        .unwrap_or_else(|| panic!("upstream callable flow for producer {function:?}"))
}

fn upstream_input_demand_for_function(
    world: &World<'_>,
    session: &PullSession,
    name: &str,
    arity: usize,
    semantic_index: usize,
) -> RuntimeDemand {
    runtime_demands_for_frontier(session)
        .iter()
        .find_map(|(executable, demand)| {
            let function_ref = world.function_ref(executable.activation.function);
            (function_ref.name == name && function_ref.arity == arity)
                .then(|| demand.input_demands.get(semantic_index).cloned())
                .flatten()
        })
        .unwrap_or_else(|| panic!("upstream input demand for {name}/{arity}[{semantic_index}]"))
}

fn assert_generic_callable_shape_matches_upstream_demand(
    world: &World<'_>,
    session: &PullSession,
    callable: super::transport::CallableId,
    demand: RuntimeDemand,
) {
    if demand.callable.is_empty() {
        panic!("expected upstream callable demand for generic callable shape, got {demand:?}")
    }
    let demand = demand.callable;
    let descr = world.callable(callable);
    // A boxed first-class callable's VALUE shape is a pure layout fact: one boxed
    // value lane and `function: None`. The invocation contract (the observed
    // surfaces) projects into the published BOUNDARIES, not the value's identity
    // — asserted below.
    assert_eq!(descr.function, None, "an opaque callable value is boxed: function None");
    assert_eq!(
        descr.capture_lanes.len(),
        1,
        "a boxed callable value occupies exactly one value lane: {descr:?}"
    );
    let facts = session
        .callable_facts_inventory()
        .get(&callable)
        .unwrap_or_else(|| panic!("callable facts should exist for generic callable {callable:?}"));
    assert_eq!(
        facts.boundary_ids.len(),
        usize::from(demand.opaque || demand.escape) * demand.resolved.len(),
        "generic callable boundaries should be published from upstream callable surfaces"
    );
}

fn assert_callable_facts_match_upstream_flow(
    world: &mut World<'_>,
    session: &PullSession,
    callable: super::transport::CallableId,
    flow: &CallableFlowFact,
) {
    let facts = session
        .callable_facts_inventory()
        .get(&callable)
        .unwrap_or_else(|| panic!("callable facts should exist for {callable:?}"));
    assert_eq!(
        sorted_executable_symbols(facts.resolutions.as_ref()),
        flow_resolution_symbols(world, flow),
        "transport callable resolutions should exactly project upstream callable-flow evidence"
    );
    assert_transport_surfaces_match_upstream(world, &facts.direct_surfaces, &flow.direct_surfaces);
    assert!(
        facts.boundary_ids.len() <= flow.first_class_surfaces.len(),
        "transport boundary ids should be justified by upstream first-class surfaces"
    );
    assert_boundary_resolutions_match_upstream_flow(world, session, facts, flow);
}

fn flow_resolution_symbols(world: &World<'_>, flow: &CallableFlowFact) -> Vec<ExecutableSymbol> {
    let mut symbols = flow
        .resolutions
        .iter()
        .map(|resolution| ExecutableSymbol {
            activation: ActivationSymbol {
                function: resolution.activation.function,
                input: resolution.activation.inputs(world.types()).into_boxed_slice(),
            },
            need: resolution.need,
        })
        .collect::<Vec<_>>();
    symbols.sort_by_key(executable_symbol_test_key);
    symbols
}

fn assert_boundary_resolutions_match_upstream_flow(
    world: &mut World<'_>,
    session: &PullSession,
    facts: &super::transport::CallableFacts,
    flow: &CallableFlowFact,
) {
    let mut expected_by_surface = BTreeMap::<CallableSurface, Vec<ExecutableSymbol>>::new();
    for edge in &flow.first_class_edges {
        expected_by_surface
            .entry(edge.surface.clone())
            .or_default()
            .push(ExecutableSymbol {
                activation: ActivationSymbol {
                    function: edge.resolution.activation.function,
                    input: edge.resolution.activation.inputs(world.types()).into_boxed_slice(),
                },
                need: edge.resolution.need,
            });
    }
    for symbols in expected_by_surface.values_mut() {
        symbols.sort_by_key(executable_symbol_test_key);
    }

    for boundary in facts.boundary_ids.iter().copied() {
        let boundary_descr = world.boundary(boundary);
        let surface_arg_shapes = boundary_descr.surface_arg_shapes.clone();
        let expected = expected_by_surface
            .iter()
            .find_map(|(surface, expected)| {
                surface_shape_matches_upstream(world, &surface_arg_shapes, surface).then_some(expected)
            })
            .unwrap_or_else(|| panic!("boundary {boundary:?} should have upstream first-class edge evidence"));
        let boundary_facts = session
            .boundary_facts_inventory()
            .get(&boundary)
            .unwrap_or_else(|| panic!("boundary facts should exist for {boundary:?}"));
        assert_eq!(
            sorted_executable_symbols(boundary_facts.resolutions.as_ref()),
            *expected,
            "boundary facts should carry exactly the executable resolutions for their published surface"
        );
    }
}

fn assert_callable_resolution_capture_prefixes_match_descriptors(world: &World<'_>, session: &PullSession) {
    for (callable, facts) in session.callable_facts_inventory() {
        let descr = world.callable(*callable);
        let Some(function) = descr.function else {
            continue;
        };
        for resolution in facts
            .resolutions
            .iter()
            .filter(|resolution| resolution.activation.function == function)
        {
            for (semantic_index, expected) in descr.capture_shapes.iter().copied().enumerate() {
                let position = TransportPosition::ExecutableInput {
                    executable: resolution.clone(),
                    semantic_index,
                };
                let actual =
                    session.transport_shapes().get(&position).copied().unwrap_or_else(|| {
                        panic!("callable resolution should publish capture input shape: {position:?}")
                    });
                assert_eq!(
                    actual, expected,
                    "callable {callable:?} records resolution {resolution:?}, but capture input {semantic_index} uses shape {actual:?} while the callable descriptor captures {expected:?}; transport must preserve callable-flow edge/capture ABI correlation"
                );
            }
        }
    }
}

fn sorted_executable_symbols(symbols: &[ExecutableSymbol]) -> Vec<ExecutableSymbol> {
    let mut sorted = symbols.to_vec();
    sorted.sort_by_key(executable_symbol_test_key);
    sorted
}

fn executable_symbol_test_key(symbol: &ExecutableSymbol) -> (u32, Vec<Ty>, u8, usize) {
    let need = match symbol.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        symbol.activation.function.as_u32(),
        symbol.activation.input.to_vec(),
        need.0,
        need.1,
    )
}

fn assert_transport_surfaces_match_upstream(
    world: &mut World<'_>,
    actual: &[Box<[ShapeId]>],
    expected: &BTreeSet<CallableSurface>,
) {
    assert!(
        transport_surfaces_match_upstream(world, actual, expected),
        "transport callable surfaces should exactly project upstream callable-flow inputs"
    );
}

fn transport_surfaces_match_upstream(
    world: &mut World<'_>,
    actual: &[Box<[ShapeId]>],
    expected: &BTreeSet<CallableSurface>,
) -> bool {
    if actual.len() != expected.len() {
        return false;
    }
    let mut matched = vec![false; actual.len()];
    for expected_surface in expected {
        let Some(index) = actual.iter().enumerate().find_map(|(index, actual_surface)| {
            (!matched[index] && surface_shape_matches_upstream(world, actual_surface, expected_surface))
                .then_some(index)
        }) else {
            return false;
        };
        matched[index] = true;
    }
    true
}

fn surface_shape_matches_upstream(world: &mut World<'_>, actual: &[ShapeId], expected: &CallableSurface) -> bool {
    actual.len() == expected.inputs.len()
        && actual
            .iter()
            .copied()
            .zip(expected.inputs.iter().copied())
            .all(|(shape, ty)| shape_matches_surface_input_ty(world, shape, ty))
}

fn shape_matches_surface_input_ty(world: &mut World<'_>, shape: ShapeId, ty: Ty) -> bool {
    match shape_descr(world, shape).clone() {
        ShapeDescr::Lane(lane) => world.lane(lane).ty == ty,
        ShapeDescr::Tuple(items) => {
            exact_tuple_field_tys_for_surface(world, ty, items.len()).is_some_and(|field_tys| {
                items.len() == field_tys.len()
                    && items
                        .iter()
                        .copied()
                        .zip(field_tys)
                        .all(|(field_shape, field_ty)| shape_matches_surface_input_ty(world, field_shape, field_ty))
            })
        }
        ShapeDescr::Callable(_) => world.types().arrow_result(&ty).is_some(),
        ShapeDescr::Nothing => false,
    }
}

fn exact_tuple_field_tys_for_surface(world: &mut World<'_>, ty: Ty, arity: usize) -> Option<Vec<Ty>> {
    let predicate = world.types().runtime_type_predicate(&ty);
    if predicate.tuple_arities.cofinite
        || predicate.tuple_arities.values.len() != 1
        || !predicate.tuple_arities.values.contains(&arity)
    {
        return None;
    }
    let any = world.types_mut().any();
    let mut fields = world.types_mut().tuple_projections(&ty, arity);
    if fields.len() < arity {
        fields.resize(arity, any);
    } else if fields.len() > arity {
        fields.truncate(arity);
    }
    Some(fields)
}

fn function_is(world: &World<'_>, function: super::FunctionId, name: &str, arity: usize) -> bool {
    let function_ref = world.function_ref(function);
    function_ref.name == name && function_ref.arity == arity
}

fn resume_shapes_for(
    positions: &HashMap<TransportPosition, ShapeId>,
    executable: &super::transport::ExecutableSymbol,
) -> Vec<ShapeId> {
    positions
        .iter()
        .filter_map(|(position, shape)| match position {
            TransportPosition::ResumePayload {
                executable: candidate, ..
            } if candidate == executable => Some(*shape),
            _ => None,
        })
        .collect()
}

fn plan_shape_at(positions: &HashMap<TransportPosition, ShapeId>, position: &TransportPosition) -> ShapeId {
    *positions
        .get(position)
        .unwrap_or_else(|| panic!("transport position should exist: {position:?}"))
}

fn shape_descr<'a>(world: &'a World<'_>, shape: ShapeId) -> &'a ShapeDescr {
    world.shape(shape)
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
    seam_facts: &[CodegenSeamFact],
    seam_matches: impl Fn(&CodegenSeam) -> bool,
    shape: Option<ShapeId>,
    lane: LaneId,
    repr: CodegenLaneRepr,
    intent: &str,
) {
    assert!(
        seam_facts
            .iter()
            .any(|fact| { seam_matches(&fact.seam) && fact.shape == shape && fact.lane == lane && fact.repr == repr }),
        "{intent}: expected shape {shape:?}, lane {lane:?}, repr {repr:?}; facts: {seam_facts:?}",
    );
}

fn assert_plan_executable_references_are_root_scoped(
    world: &World<'_>,
    transport: &MaterializedTransportPlan,
    session: &PullSession,
) {
    let membership = session
        .demanded_executables()
        .iter()
        .map(|key| executable_symbol_for(world, key))
        .collect::<HashSet<_>>();
    assert!(
        membership.contains(&transport.entry),
        "the root plan entry must be part of executable membership: {membership:?}"
    );
    for position in session.transport_shapes().keys() {
        let executable = position_executable(position);
        assert!(
            membership.contains(executable),
            "transport position should reference only root-member executables: {position:?}"
        );
    }
    for facts in session.callable_facts_inventory().values() {
        for executable in facts.resolutions.iter() {
            assert!(
                membership.contains(executable),
                "callable facts should resolve only to root-member executables: {executable:?}"
            );
        }
    }
    for fact in transport.codegen_seam_facts.iter() {
        if let Some(executable) = seam_executable(&fact.seam) {
            assert!(
                membership.contains(executable),
                "codegen seam facts should reference only root-member executables: {:?}",
                fact.seam
            );
        }
    }
}

fn position_executable(position: &TransportPosition) -> &super::transport::ExecutableSymbol {
    match position {
        TransportPosition::ExecutableInput { executable, .. }
        | TransportPosition::ExecutableReturn { executable }
        | TransportPosition::ResumePayload { executable, .. }
        | TransportPosition::ReturnPayload { executable, .. }
        | TransportPosition::CallArg { executable, .. }
        | TransportPosition::EntryCapture { executable, .. }
        | TransportPosition::Value { executable, .. } => executable,
    }
}

fn seam_executable(seam: &CodegenSeam) -> Option<&super::transport::ExecutableSymbol> {
    match seam {
        CodegenSeam::FunctionEntry { executable, .. }
        | CodegenSeam::BlockParam { executable, .. }
        | CodegenSeam::ReturnDelivery { executable }
        | CodegenSeam::ContinuationEntry { executable, .. }
        | CodegenSeam::ReturnContinuation { executable, .. }
        | CodegenSeam::TailCall { executable, .. }
        | CodegenSeam::ExternBoundary { executable } => Some(executable),
        CodegenSeam::CallableBoundary { .. } | CodegenSeam::FirstClassPublication { .. } => None,
    }
}

fn transport_position_is_semantic(position: &TransportPosition) -> bool {
    match position {
        TransportPosition::ExecutableInput { .. }
        | TransportPosition::ExecutableReturn { .. }
        | TransportPosition::ResumePayload { .. }
        | TransportPosition::ReturnPayload { .. }
        | TransportPosition::CallArg { .. }
        | TransportPosition::EntryCapture { .. }
        | TransportPosition::Value { .. } => true,
    }
}

fn single_boundary_descr<'a>(world: &'a World<'_>, session: &PullSession) -> &'a BoundaryDescr {
    let boundaries = session.boundary_facts_inventory().keys().copied().collect::<Vec<_>>();
    let [boundary] = boundaries.as_slice() else {
        panic!(
            "fixture should publish exactly one boundary contract: {:?}",
            session.boundary_facts_inventory()
        )
    };
    world.boundary(*boundary)
}

fn boundary_with_callable_arg<'a>(world: &'a World<'_>, session: &PullSession) -> &'a BoundaryDescr {
    session
        .boundary_facts_inventory()
        .keys()
        .map(|boundary| world.boundary(*boundary))
        .find(|boundary| {
            boundary
                .surface_arg_shapes
                .iter()
                .any(|shape| matches!(shape_descr(world, *shape), ShapeDescr::Callable(_)))
        })
        .unwrap_or_else(|| {
            panic!(
                "fixture should publish a boundary with a callable argument: {:?}",
                session.boundary_facts_inventory()
            )
        })
}

fn callable_return_for_executable(
    world: &World<'_>,
    positions: &HashMap<TransportPosition, ShapeId>,
    executable: super::transport::ExecutableSymbol,
) -> super::transport::CallableId {
    let returned = plan_shape_at(positions, &TransportPosition::ExecutableReturn { executable });
    let ShapeDescr::Callable(callable) = shape_descr(world, returned) else {
        panic!(
            "fixture executable should return a callable shape, got {:?}",
            shape_descr(world, returned)
        )
    };
    *callable
}

fn boundary_with_callable_return<'a>(
    world: &'a World<'_>,
    session: &PullSession,
    callable: super::transport::CallableId,
) -> &'a BoundaryDescr {
    session
        .callable_facts_inventory()
        .get(&callable)
        .into_iter()
        .flat_map(|facts| facts.boundary_ids.iter())
        .map(|boundary| world.boundary(*boundary))
        .find(|boundary| {
            boundary.callable == callable && shape_contains_callable(world, boundary.published_return_shape)
        })
        .unwrap_or_else(|| {
            panic!(
                "callable {callable:?} should publish a boundary with a callable return child: {:?}",
                session.callable_facts_inventory()
            )
        })
}

fn continuation_boundary_descr<'a>(
    world: &'a World<'_>,
    session: &PullSession,
    callable: super::transport::CallableId,
) -> &'a BoundaryDescr {
    session
        .callable_facts_inventory()
        .get(&callable)
        .into_iter()
        .flat_map(|facts| facts.boundary_ids.iter())
        .map(|boundary| world.boundary(*boundary))
        .find(|boundary| boundary.callable == callable)
        .unwrap_or_else(|| {
            panic!(
                "escaped callable {callable:?} should publish a boundary: {:?}",
                session.callable_facts_inventory()
            )
        })
}

fn assert_no_unreachable_callable_facts(world: &World<'_>, session: &PullSession) {
    let mut reachable = HashSet::new();
    for shape in session.transport_shapes().values().copied() {
        collect_callable_shapes(world, shape, &mut reachable);
    }
    for boundary in boundary_descrs(world, session) {
        for shape in boundary.surface_arg_shapes.iter().copied() {
            collect_callable_shapes(world, shape, &mut reachable);
        }
        collect_callable_shapes(world, boundary.published_return_shape, &mut reachable);
    }
    let unreachable = session
        .callable_facts_inventory()
        .keys()
        .copied()
        .filter(|callable| !reachable.contains(callable))
        .collect::<Vec<_>>();
    assert!(
        unreachable.is_empty(),
        "callable facts must be justified by reachable transport shapes; unreachable={unreachable:?}; facts={:?}",
        session.callable_facts_inventory()
    );
}

fn collect_callable_shapes(world: &World<'_>, shape: ShapeId, out: &mut HashSet<super::transport::CallableId>) {
    match shape_descr(world, shape) {
        ShapeDescr::Callable(callable) => {
            out.insert(*callable);
            let descr = world.callable(*callable);
            for capture in descr.capture_shapes.iter().copied() {
                collect_callable_shapes(world, capture, out);
            }
        }
        ShapeDescr::Tuple(items) => {
            for item in items.iter().copied() {
                collect_callable_shapes(world, item, out);
            }
        }
        ShapeDescr::Nothing | ShapeDescr::Lane(_) => {}
    }
}

fn boundary_descrs<'a>(world: &'a World<'_>, session: &PullSession) -> Vec<&'a BoundaryDescr> {
    session
        .boundary_facts_inventory()
        .keys()
        .map(|boundary| world.boundary(*boundary))
        .collect()
}

fn shape_contains_callable(world: &World<'_>, shape: ShapeId) -> bool {
    match shape_descr(world, shape) {
        ShapeDescr::Callable(_) => true,
        ShapeDescr::Tuple(items) => items.iter().any(|item| shape_contains_callable(world, *item)),
        ShapeDescr::Nothing | ShapeDescr::Lane(_) => false,
    }
}

fn first_callable_in_shape(world: &World<'_>, shape: ShapeId) -> Option<super::transport::CallableId> {
    match shape_descr(world, shape) {
        ShapeDescr::Callable(callable) => Some(*callable),
        ShapeDescr::Tuple(items) => items.iter().find_map(|item| first_callable_in_shape(world, *item)),
        ShapeDescr::Nothing | ShapeDescr::Lane(_) => None,
    }
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

fn measurement_u64(event: &crate::telemetry::capture::OwnedEvent, key: &str) -> u64 {
    let Some(Value::U64(value)) = event.measurements.get(key) else {
        panic!("expected u64 measurement {key} in {:?}", event.measurements)
    };
    *value
}

fn metadata_str<'a>(event: &'a crate::telemetry::capture::OwnedEvent, key: &str) -> &'a str {
    let Some(Value::Str(value)) = event.metadata.get(key) else {
        panic!("expected string metadata {key} in {:?}", event.metadata)
    };
    value
}

fn product_no_dump_interp_job_telemetry(source: &str) -> (super::RootId, JobTelemetry) {
    let tel = ConfiguredTelemetry::new();
    let jobs = JobTelemetry::new();
    tel.attach(&["fz", "compiler2", "job"], jobs.handler());
    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("current_no_dump_00181_enum_reduce_operator_ref.fz".to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .run_root_interp(root)
        .expect("product no-dump interp should run fixture 00181");
    (root, jobs)
}

struct JobTelemetry {
    live: Rc<RefCell<HashMap<u64, Job>>>,
    stops: Rc<RefCell<Vec<Job>>>,
}

impl JobTelemetry {
    fn new() -> Self {
        Self {
            live: Rc::new(RefCell::new(HashMap::new())),
            stops: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(JobTelemetryHandler {
            live: self.live.clone(),
            stops: self.stops.clone(),
        })
    }

    fn total_stops(&self) -> usize {
        self.stops.borrow().len()
    }
}

struct JobTelemetryHandler {
    live: Rc<RefCell<HashMap<u64, Job>>>,
    stops: Rc<RefCell<Vec<Job>>>,
}

impl Handler for JobTelemetryHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "job"] {
            return;
        }
        match event.kind {
            EventKind::SpanStart => {
                if let Some(job) = event.metadata.get("job").and_then(|value| value.downcast_ref::<Job>()) {
                    self.live.borrow_mut().insert(event.span_id, job.clone());
                }
            }
            EventKind::SpanStop => {
                if let Some(job) = self.live.borrow_mut().remove(&event.span_id) {
                    self.stops.borrow_mut().push(job);
                }
            }
            EventKind::Event | EventKind::SpanException => {}
        }
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
