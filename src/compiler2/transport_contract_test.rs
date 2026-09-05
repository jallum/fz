use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use super::artifact::{AbiValueRepr, MaterializedTransportPlan};
use super::body::{DeliveredValueSource, delivered_value_joins};
use super::facts::FactUse;
use super::pull::{
    ProductDriver, ProductKey, ProductValue, PullOutcome, PullSession, PullWait, SymbolicBackendTail, TransportCarrier,
    TransportLayout, TransportShapeFact, WorldProductProducers,
};
use super::semantic::{CallableFlowFact, CallableSurface, SemanticOrd as _};
use super::transport::{ActivationSymbol, ExecutableSymbol};
use super::transport::{
    BoundaryDescr, CodegenLaneRepr, CodegenSeam, CodegenSeamFact, LaneId, ShapeDescr, ShapeId, TransportPosition,
};
use super::types::Ty;
use super::{
    CallableConstructionTargetKey, CodeSubmission, Compiler2, ExecutableKey, ExecutableNeed, ExecutableRuntimeDemand,
    FactKey, Job, RootSubmission, RuntimeDemand, ShapeDemand, World,
};
use crate::exec::runtime::DbgCapture;
use crate::telemetry::ConfiguredTelemetry;

const EVENT_NAME: &[&str] = &["fz", "compiler2", "transport_flow", "defined"];

type SettledProducts = Rc<RefCell<Vec<ProductKey>>>;

struct PullTelemetryCapture {
    produced: SettledProducts,
}

impl PullTelemetryCapture {
    fn install(telemetry: &ConfiguredTelemetry) -> Self {
        let capture = Self {
            produced: Rc::new(RefCell::new(Vec::new())),
        };
        let produced = Rc::clone(&capture.produced);
        telemetry.attach_raw_event3::<ProductKey, ProductValue, super::pull::ProductSettlement, _>(
            &["fz", "compiler2", "pull", "product", "settled"],
            move |_, _, _, product, _, _| produced.borrow_mut().push(product.clone()),
        );
        capture
    }

    fn produced_count(&self) -> usize {
        self.produced.borrow().len()
    }

    fn produced_kind(&self, kind: &str) -> bool {
        self.produced.borrow().iter().any(|product| product.kind() == kind)
    }
}

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
    (
        "S_pair_return",
        "Tuple([structural(S_int), structural(S_direct_callable)])",
    ),
    ("S_pub_callable", "Callable(C_pub)"),
];

const LANE_DESCRIPTORS: &[(&str, &str)] = &[("L_int", "LaneDescr { ty: int, transport_class: value }")];

const CALLABLE_FACTS: &[(&str, &str)] = &[
    (
        "C_direct",
        "target E_add; capture_layouts [structural(S_int)]; direct_surfaces [[S_int]]; boundary_ids []",
    ),
    (
        "C_pub",
        "target E_add; capture_layouts [structural(S_int)]; direct_surfaces []; boundary_ids [B_pub]",
    ),
];

const BOUNDARY_FACTS: &[(&str, &str)] = &[(
    "B_pub",
    "callable C_pub; surface_arg_layouts [structural(S_int)]; published_value_lane L_int",
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
        Some("Tuple([structural(S_int), structural(S_direct_callable)])"),
        "pair/1 returns the same tuple shape that main/0 resumes from"
    );
    assert_eq!(
        position_shape("Pos(E_pair.return)"),
        position_shape("Pos(E_main.resume(pair call))"),
        "producer return and consumer resume must share one ShapeId"
    );
    assert_eq!(
        callable("C_direct"),
        Some("target E_add; capture_layouts [structural(S_int)]; direct_surfaces [[S_int]]; boundary_ids []"),
        "direct callable identity is separate from boundary publication"
    );
    assert_eq!(
        callable("C_pub"),
        Some("target E_add; capture_layouts [structural(S_int)]; direct_surfaces []; boundary_ids [B_pub]"),
        "the escaped callable shares the target but publishes an explicit boundary fact"
    );
    assert_eq!(
        boundary("B_pub"),
        Some("callable C_pub; surface_arg_layouts [structural(S_int)]; published_value_lane L_int"),
        "boundary publication is contextual and retains its physical argument layouts"
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
    let mut world = World::new();
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_codegen_seam_tail_call.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (_, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    assert!(
        plan.codegen_seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::TailCall { .. }) && fact.repr == CodegenLaneRepr::RawF64),
        "a tail float call should publish a RawF64 tail-call seam: {:?}",
        plan.codegen_seam_facts
    );
}

#[test]
fn compiler2_transport_shapes_retain_named_child_product_dependencies() {
    let tel = ConfiguredTelemetry::new();
    let pull_events = PullTelemetryCapture::install(&tel);
    let mut world = World::new();
    world.submit_code(
        Some("direct_transport_shape_products.fz".to_string()),
        "fn main() do\n  xs = [1, 2, 3, 4, 5]\n  dbg(Enum.drop_while(xs, fn (x) -> x < 4 end))\n  dbg(Enum.drop_while(xs, fn (x) -> x < 0 end))\nend\n".to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);

    assert!(pull_events.produced_kind("transport_shape"));
    let session = driver.session();
    let _ = plan
        .position_layouts
        .iter()
        .map(|(position, _)| position)
        .filter_map(|position| {
            session
                .memo()
                .product_dependencies(&ProductKey::TransportShape(position.clone()))
        })
        .find(|dependencies| {
            dependencies
                .keys()
                .any(|dependency| matches!(dependency, ProductKey::TransportShape(_)))
        })
        .expect("a composed transport shape should retain its named child shape dependency");
}

#[test]
fn compiler2_transport_flow_names_tail_return_payload_position() {
    let source = r#"
fn inc(x), do: x + 1.0
fn main(), do: inc(1.0)
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_tail_return_payload_position.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let transport_shapes = plan_shapes(&plan);
    let main = executable_for(&world, session, "main", 0);
    let inc = executable_for(&world, session, "inc", 1);
    let main_return = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableReturn {
            executable: main.clone(),
        },
    );
    let inc_return = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: inc });
    let return_payloads = transport_shapes
        .iter()
        .filter_map(|(position, shape)| match position {
            TransportPosition::ReturnPayload { executable, callsite } if *executable == main => {
                Some((callsite, *shape))
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
            if executable == &main && candidate == *callsite)
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
    let mut world = World::new();
    world.submit_code(
        Some("fixtures2/behavior/multi_relay.fz".to_string()),
        include_str!("../../fixtures2/behavior/multi_relay.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (_driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let transport_shapes = plan_shapes(&plan);
    let return_payloads = transport_shapes
        .iter()
        .filter_map(|(position, payload_shape)| match position {
            TransportPosition::ReturnPayload { executable, callsite } => {
                let caller_return = plan_shape_at(
                    &plan,
                    &TransportPosition::ExecutableReturn {
                        executable: executable.clone(),
                    },
                );
                Some((executable.clone(), callsite, *payload_shape, caller_return))
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
                    } if candidate_executable == &executable && *candidate_callsite == *callsite
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
    let mut world = World::new();
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
fn compiler2_callable_boundary_seams_keep_capture_carriers_distinct_from_raw_arguments() {
    let source = r#"
fn main() do
  flag = self() == self()
  f = if flag do
    fn () -> {41.5, :ok} end
  else
    fn () -> {42.5, :bad} end
  end
  {n, _} = f.()
  g = if flag do
    fn x -> n + x end
  else
    fn x -> n - x end
  end
  g.(1.0)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("callable_boundary_carrier_provenance.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (_, plan) = pull_transport_plan_for_test(&tel, &mut world, root);

    let (boundary, capture, argument) = plan
        .boundary_facts
        .keys()
        .find_map(|boundary| {
            let descr = world.boundary(*boundary);
            let [capture] = world.callable(descr.callable).capture_layouts.as_ref() else {
                return None;
            };
            let [argument] = descr.surface_arg_layouts.as_ref() else {
                return None;
            };
            (capture.carrier.is_value_ref() && argument.carrier == TransportCarrier::Absent)
                .then_some((*boundary, *capture, *argument))
        })
        .expect("the joined scalar closure should publish a carried capture and raw argument boundary");
    let capture_lane = world.layout_lane_ids(capture);
    let argument_lane = world.layout_lane_ids(argument);
    assert_eq!(
        capture_lane, argument_lane,
        "the proof must exercise one typed lane in two physical roles"
    );

    let seams = plan
        .codegen_seam_facts
        .iter()
        .filter_map(|fact| match fact.seam {
            CodegenSeam::CallableBoundary { boundary: found, slot } if found == boundary => {
                Some((slot, fact.shape, fact.lane, fact.repr))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        seams,
        vec![
            (0, Some(capture.structural), capture_lane[0], CodegenLaneRepr::ValueRef),
            (1, Some(argument.structural), argument_lane[0], CodegenLaneRepr::RawF64),
        ],
        "boundary seam slots must preserve carrier and structural provenance for repeated lane identities",
    );
}

#[test]
fn compiler2_transport_flow_publishes_extern_boundary_codegen_seams() {
    let source = r#"
extern "C" fn fz_float_id(float) :: float
fn main(), do: fz_float_id(1.0)
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_codegen_seam_extern_boundary.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (_, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    assert!(
        plan.codegen_seam_facts
            .iter()
            .any(|fact| matches!(fact.seam, CodegenSeam::ExternBoundary { .. }) && fact.repr == CodegenLaneRepr::RawF64),
        "a float extern should publish RawF64 extern-boundary lane facts: {:?}",
        plan.codegen_seam_facts
    );
}

#[test]
fn compiler2_extern_any_marshals_a_raw_scalar_without_promoting_its_transport_carrier() {
    let source = r#"
extern "C" fn fz_any_id(any) :: any
fn main(), do: fz_any_id(1.0)
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some("transport_extern_any_scalar.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let executable = executable_for(&world, &driver.session(), "fz_any_id", 1);
    let input = plan
        .layout_at(&TransportPosition::ExecutableInput {
            executable: executable.clone(),
            semantic_index: 0,
        })
        .expect("the extern scalar input should have a transport layout");

    assert_eq!(input.carrier, TransportCarrier::Absent);
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::ExternBoundary { executable: found } if found == &executable),
        Some(input.structural),
        world.layout_lane_ids(input)[0],
        CodegenLaneRepr::RawF64,
        "the extern marshal, not the transport layout, boxes a raw scalar for an Any parameter",
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_spawn_callable_boundary_input.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let spawn = executable_for(&world, session, "spawn", 1);
    let spawn_input = TransportPosition::ExecutableInput {
        executable: spawn.clone(),
        semantic_index: 0,
    };
    let (_, boundaries) = callable_owner_facts_for_test(session);
    let boundary = boundaries
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_extern_tuple_value_input.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let dbg_wrapper = executable_for(&world, session, "dbg", 1);
    let dbg = executable_for(&world, session, "fz_dbg", 1);
    let wrapper_input = plan
        .layout_at(&TransportPosition::ExecutableInput {
            executable: dbg_wrapper,
            semantic_index: 0,
        })
        .expect("the direct wrapper input should have a transport layout");
    assert!(
        matches!(shape_descr(&world, wrapper_input.structural), ShapeDescr::Tuple(_))
            && wrapper_input.carrier == TransportCarrier::Absent,
        "the direct wrapper input should retain complete tuple lanes until the extern boundary",
    );
    let input = plan
        .layout_at(&TransportPosition::ExecutableInput {
            executable: dbg.clone(),
            semantic_index: 0,
        })
        .expect("the extern input should have a transport layout");
    assert!(
        input.carrier.is_value_ref(),
        "extern any input should attach one explicit boxed carrier",
    );
    let leaf_lanes = world.layout_physical_lanes(input);
    let [physical] = leaf_lanes.as_slice() else {
        panic!("extern any input should have exactly one boxed lane")
    };
    assert_seam_fact(
        &plan.codegen_seam_facts,
        |seam| matches!(seam, CodegenSeam::FunctionEntry { executable, semantic_index } if executable == &dbg && *semantic_index == 0),
        Some(physical.structural),
        physical.lane,
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_codegen_seam_tuple_leaf_lanes.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let pair = executable_for(&world, session, "pair", 2);
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_codegen_seam_int_atom_reprs.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_codegen_seam_boxed_internal_reprs.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let id_box = executable_for(&world, session, "id_box", 1);
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_codegen_seam_boxed_tail_extern_reprs.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let extern_id = executable_for(&world, session, "fz_binary_id", 1);
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
    let mut world = World::new();
    world.submit_code(Some("transport_ignore.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let ping = executable_for(&world, session, "ping", 1);
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
    let mut world = World::new();
    world.submit_code(Some("transport_direct_callable.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let apply1 = executable_for(&world, session, "apply1", 2);
    let make_adder = executable_for(&world, session, "make_adder", 1);
    let main = executable_for(&world, session, "main", 0);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: make_adder });
    let applied = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableInput {
            executable: apply1.clone(),
            semantic_index: 0,
        },
    );
    let resumed = resume_shapes_for(&plan, &main)
        .into_iter()
        .find(|shape| *shape == returned)
        .unwrap_or_else(|| panic!("main should resume the direct callable returned by make_adder/1"));
    assert!(
        plan.position_layouts.iter().any(|(position, layout)| {
            matches!(position, TransportPosition::CallArg { executable, semantic_index: 0, .. }
                if executable == &main && layout.structural == applied)
        }),
        "main/0 must conform its apply1/2 argument to the callee-owned callable input ABI"
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
    let flow = upstream_callable_flow_for_producer(&world, session, producer_function);
    assert_callable_facts_match_upstream_flow(&mut world, session, callable, &flow);
    let ShapeDescr::Callable(applied_callable) = shape_descr(&world, applied) else {
        panic!("apply1/2's input ABI should remain callable-shaped")
    };
    let applied_descr = world.callable(*applied_callable);
    assert_eq!(
        callable_capture_lanes(&world, *applied_callable).len(),
        1,
        "apply1/2 must preserve the returned closure's captured `a` payload: {applied_descr:?}"
    );
    assert_eq!(
        plan.layout_at(&TransportPosition::ExecutableInput {
            executable: apply1,
            semantic_index: 0,
        })
        .expect("apply1 input layout")
        .carrier,
        TransportCarrier::Absent,
        "the directly resolved callable input should require no runtime carrier",
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_artifact_handoff_contract.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    assert_plan_executable_references_are_root_scoped(&world, &plan, session);

    let pair = executable_for(&world, session, "pair", 1);
    let main = executable_for(&world, session, "main", 0);
    let pair_return = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: pair });
    let pair_resume = resume_shapes_for(&plan, &main)
        .into_iter()
        .find(|shape| *shape == pair_return)
        .unwrap_or_else(|| {
            panic!(
                "main/0 should resume pair/1's returned shape: {:?}",
                plan.position_layouts
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
        matches!(shape_descr(&world, n_shape.structural), ShapeDescr::Lane(_)),
        "the scalar field should remain a lane shape"
    );
    let ShapeDescr::Callable(pair_callable) = shape_descr(&world, f_shape.structural) else {
        panic!("the callable field should remain a CallableId shape")
    };

    let apply1 = executable_for(&world, session, "apply1", 2);
    let apply1_callable_input = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableInput {
            executable: apply1.clone(),
            semantic_index: 0,
        },
    );
    assert!(
        plan.position_layouts.iter().any(|(position, layout)| {
            matches!(position, TransportPosition::CallArg { executable, semantic_index: 0, .. }
                if executable == &main && layout.structural == apply1_callable_input)
        }),
        "the caller argument must conform to apply1/2's independently owned callable input ABI"
    );
    let (callables, boundaries) = callable_owner_facts_for_test(session);
    let callable_facts = callables
        .get(pair_callable)
        .unwrap_or_else(|| panic!("direct callable facts should exist for {pair_callable:?}"));
    assert!(
        !callable_facts.direct_surfaces.is_empty(),
        "direct callable surfaces should be plan facts, not artifact-local recovery"
    );
    let ShapeDescr::Callable(apply1_callable) = shape_descr(&world, apply1_callable_input) else {
        panic!("apply1/2's input ABI should remain callable-shaped")
    };
    let apply1_descr = world.callable(*apply1_callable);
    assert_eq!(
        callable_capture_lanes(&world, *apply1_callable).len(),
        1,
        "apply1/2 must preserve the returned closure's structural capture payload: {apply1_descr:?}"
    );
    assert_eq!(
        plan.layout_at(&TransportPosition::ExecutableInput {
            executable: apply1,
            semantic_index: 0,
        })
        .expect("apply1 input layout")
        .carrier,
        TransportCarrier::Absent,
        "the direct callable input must carry its structural capture without an additional boxed carrier",
    );

    let escape = executable_for(&world, session, "escape", 0);
    let escaped = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: escape });
    let ShapeDescr::Callable(escaped_callable) = shape_descr(&world, escaped) else {
        panic!("escape/0 should return a callable shape")
    };
    let escaped_facts = callables
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
        boundaries
            .get(boundary)
            .is_some_and(|facts| !facts.publications.is_empty()),
        "first-class publication positions should be plan facts, not artifact-local boundary selection"
    );

    let double = executable_for(&world, session, "double", 1);
    let double_return = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: double });
    let double_resume = resume_shapes_for(&plan, &main)
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
fn compiler2_transport_plan_does_not_publish_unused_callable_construction() {
    let source = r#"
fn make(), do: fn (x) -> x + 1 end

fn main() do
  make()
  :ok
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some("transport_unused_callable.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let (_, boundaries) = callable_owner_facts_for_test(session);
    assert_eq!(
        boundaries.len(),
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
    let mut world = World::new();
    world.submit_code(Some("transport_direct_lambda_use.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let main = executable_for(&world, session, "main", 0);
    let callable_shapes = plan
        .position_layouts
        .iter()
        .filter_map(|(position, layout)| match position {
            TransportPosition::Value {
                executable: candidate, ..
            } if *candidate == main && matches!(shape_descr(&world, layout.structural), ShapeDescr::Callable(_)) => {
                Some(layout.structural)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        !callable_shapes.is_empty(),
        "direct lambda use should keep a callable shape in the root plan"
    );
    assert_eq!(
        callable_owner_facts_for_test(session).1.len(),
        0,
        "a direct-only lambda path should not publish a first-class boundary"
    );
    let direct_owners = root_backend_answer_for_test(session)
        .transport
        .callable_owners
        .iter()
        .filter(|positioned| {
            positioned.position.executable() == &main
                && matches!(
                    shape_descr(&world, positioned.owner.layout.structural),
                    ShapeDescr::Callable(_)
                )
        })
        .collect::<Vec<_>>();
    assert!(
        !direct_owners.is_empty(),
        "the direct lambda should own its callable layout"
    );
    assert!(
        direct_owners
            .iter()
            .all(|positioned| positioned.owner.construction.is_none()),
        "direct-only callable positions must not publish wrapper constructions: {direct_owners:#?}",
    );
}

#[test]
fn compiler2_transport_plan_requires_a_boundary_for_an_escaped_lambda() {
    let source = r#"
fn make(), do: fn (x) -> x + 1 end
fn main(), do: make()
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some("transport_escaped_lambda.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let make = executable_for(&world, session, "make", 0);
    let returned = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableReturn {
            executable: make.clone(),
        },
    );
    assert!(
        matches!(shape_descr(&world, returned), ShapeDescr::Callable(_)),
        "escaped lambda should still be a callable shape in the transport plan"
    );
    assert_eq!(
        callable_owner_facts_for_test(session).1.len(),
        1,
        "escaping a lambda as a returned callable should publish exactly one boundary contract"
    );
    let constructions = root_backend_answer_for_test(session)
        .transport
        .callable_owners
        .iter()
        .filter_map(|positioned| positioned.owner.construction.as_ref())
        .filter(|construction| construction.producer.executable() == &make)
        .collect::<Vec<_>>();
    let [construction] = constructions.as_slice() else {
        panic!("the escaped lambda producer should own one exact wrapper construction: {constructions:#?}")
    };
    assert!(
        !construction.members.is_empty(),
        "a first-class wrapper construction must own at least one executable member",
    );
}

#[test]
fn compiler2_transport_plan_requires_a_boundary_for_an_opaque_callable_input() {
    let source = "fn main(f), do: f.(1)\n";

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_opaque_callable_input.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let main = executable_for(&world, session, "main", 1);
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
    let ShapeDescr::Callable(input_callable) = shape_descr(&world, input_shape) else {
        unreachable!("checked above")
    };
    let input_demand = upstream_input_demand_for_function(&world, session, "main", 1, 0);
    assert_generic_callable_shape_matches_upstream_demand(&world, session, *input_callable, input_demand);
    assert_eq!(
        callable_owner_facts_for_test(session).1.len(),
        1,
        "an opaque callable input should publish one explicit boundary contract"
    );
}

#[test]
fn compiler2_runtime_demand_excludes_unused_same_source_callable_sibling() {
    let source = r#"
@spec use((integer) -> integer) :: integer
fn use(f), do: f.(1)

fn ignore(_), do: 0

fn make(v), do: fn (_) -> v end

fn main() do
  use(make(1))
  ignore(make(:unused))
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("runtime_demand_used_and_ignored_callable_siblings.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let demanded_lambda_inputs = session
        .demanded_executables()
        .iter()
        .filter(|executable| {
            world
                .function_ref(executable.activation.function)
                .name
                .starts_with("#lambda:")
        })
        .map(|executable| {
            world
                .activation_inputs_joined(&executable.activation)
                .unwrap_or_else(|| executable.activation.inputs(world.types()))
        })
        .collect::<Vec<_>>();
    assert_eq!(
        demanded_lambda_inputs.len(),
        1,
        "only the callable sibling that reaches use/1 should enter runtime demand: {:?}",
        demanded_lambda_inputs
            .iter()
            .map(|inputs| inputs.iter().map(|ty| world.types().display(ty)).collect::<Vec<_>>())
            .collect::<Vec<_>>()
    );
    assert!(
        demanded_lambda_inputs[0].iter().all(|ty| world.types().is_integer(ty)),
        "the demanded construction should be the integer capture used by use/1: {:?}",
        demanded_lambda_inputs[0]
            .iter()
            .map(|ty| world.types().display(ty))
            .collect::<Vec<_>>()
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_distinct_opaque_callable_surfaces.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 2, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let main = executable_for(&world, session, "main", 2);
    // Both opaque inputs are boxed callables, so their VALUE shapes are pure
    // layout (one boxed value lane) and may coincide. The surface contract is
    // not part of the value identity any more — it lives on the boundaries.
    for semantic_index in [0, 1] {
        let shape = plan_shape_at(
            &plan,
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
    let (_, boundaries) = callable_owner_facts_for_test(session);
    let surface_contracts = boundaries
        .keys()
        .map(|boundary| {
            world
                .boundary(*boundary)
                .surface_arg_layouts
                .iter()
                .map(|layout| layout.structural)
                .collect::<Vec<_>>()
        })
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_same_surface_distinct_captures.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let main = executable_for(&world, session, "main", 0);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: main });
    let ShapeDescr::Tuple(items) = shape_descr(&world, returned) else {
        panic!("main/0 should return a tuple of callable values")
    };
    let [left, right] = items.as_ref() else {
        panic!("main/0 should return exactly two callable tuple fields")
    };
    let ShapeDescr::Callable(left) = shape_descr(&world, left.structural) else {
        panic!("first tuple field should be callable-shaped")
    };
    let ShapeDescr::Callable(right) = shape_descr(&world, right.structural) else {
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_boundary_callable_arg.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let boundary = boundary_with_callable_arg(&world, session);
    let [arg_layout] = boundary.surface_arg_layouts.as_ref() else {
        panic!("f/1 boundary should publish one surface argument layout")
    };
    assert!(
        matches!(shape_descr(&world, arg_layout.structural), ShapeDescr::Callable(_)),
        "the published boundary argument should preserve the callable shape"
    );
    assert_eq!(
        world.layout_lane_ids(*arg_layout).len(),
        1,
        "a callable argument crossing a boundary should be boxed into one published lane"
    );
}

#[test]
fn compiler2_transport_plan_preserves_enumerable_suspend_continuation_captures() {
    let escaped_source = r#"
fn make() do
  fn () ->
    Enumerable.reduce([1, 2, 3], {:suspend, 0}, fn (x, acc) -> {:cont, acc + x} end)
  end
end

fn main(), do: make()
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_enumerable_reduce_suspend_continuation.fz".to_string()),
        escaped_source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let make = executable_for(&world, session, "make", 0);
    let outer = callable_return_for_executable(&world, &plan, make);
    let (callables, _) = callable_owner_facts_for_test(session);
    let outer_facts = callables
        .get(&outer)
        .unwrap_or_else(|| panic!("the escaped closure should carry callable facts"));
    assert_eq!(
        outer_facts.boundary_ids.len(),
        1,
        "the un-invoked escaped closure should publish exactly one first-class boundary"
    );
    let outer_resolution = outer_facts
        .resolutions
        .first()
        .unwrap_or_else(|| panic!("the escaped closure should resolve to its body executable"));
    let grounded_return = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableReturn {
            executable: outer_resolution.clone(),
        },
    );
    assert!(matches!(world.shape(grounded_return), ShapeDescr::Tuple(_)));
    let continuation = sole_callable_with_callable_capture(&world, session);
    assert_suspend_continuation_captures(&world, continuation);

    let consumed_source = r#"
fn make() do
  fn () ->
    Enumerable.reduce([1, 2, 3], {:suspend, 0}, fn (x, acc) -> {:cont, acc + x} end)
  end
end

fn main() do
  {:suspended, acc, cont} = make().()
  dbg(cont.())
  acc
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_enumerable_reduce_suspend_continuation_resumed.fz".to_string()),
        consumed_source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let make = executable_for(&world, session, "make", 0);
    let outer = callable_return_for_executable(&world, &plan, make);
    let (callables, _) = callable_owner_facts_for_test(session);
    let outer_resolution = callables
        .get(&outer)
        .and_then(|facts| facts.resolutions.first())
        .unwrap_or_else(|| panic!("the invoked closure should resolve to its body executable"));
    let demanded_return = plan_shape_at(
        &plan,
        &TransportPosition::ExecutableReturn {
            executable: outer_resolution.clone(),
        },
    );
    assert!(matches!(shape_descr(&world, demanded_return), ShapeDescr::Tuple(_)));
    let continuation = sole_callable_with_callable_capture(&world, session);
    assert_suspend_continuation_captures(&world, continuation);

    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("transport_enumerable_reduce_suspend_continuation_runtime.fz".to_string()),
        text: r#"
fn main() do
  {:suspended, acc, cont} = Enumerable.reduce(1..5, {:suspend, 9}, fn (x, sum) -> {:cont, sum + x} end)
  dbg(acc)
  dbg(cont.())
end
"#
        .to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .run_root_interp(root)
        .expect("interpreter should resume the continuation");
    compiler.run_root_jit(root).expect("JIT should resume the continuation");
    assert_eq!(dbg.lines().as_slice(), ["9", "{:done, 24}", "9", "{:done, 24}"]);
}

fn sole_callable_with_callable_capture(world: &World, session: &PullSession) -> super::transport::CallableId {
    let (callables, _) = callable_owner_facts_for_test(session);
    let candidates = callables
        .keys()
        .copied()
        .filter(|callable| {
            world
                .callable(*callable)
                .capture_layouts
                .iter()
                .any(|layout| matches!(shape_descr(world, layout.structural), ShapeDescr::Callable(_)))
        })
        .collect::<Vec<_>>();
    let [continuation] = candidates.as_slice() else {
        panic!("exactly one callable (the suspend continuation) should capture a callable, got {candidates:?}")
    };
    *continuation
}

fn assert_suspend_continuation_captures(world: &World, continuation: super::transport::CallableId) {
    let continuation_descr = world.callable(continuation);
    assert_eq!(
        continuation_descr.capture_layouts.len(),
        3,
        "the suspend continuation should capture the remaining list, accumulator, and reducer"
    );
    assert!(
        matches!(
            shape_descr(world, continuation_descr.capture_layouts[2].structural),
            ShapeDescr::Callable(_)
        ),
        "the captured reducer should remain callable-shaped inside the continuation descriptor"
    );
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_tuple_returned_callable_resume_capture.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let main = executable_for(&world, session, "main", 0);
    let (resume_position, resume_layout) = plan
        .position_layouts
        .iter()
        .find(|(position, layout)| {
            matches!(
                position,
                TransportPosition::ResumePayload {
                    executable,
                    callsite: Some(_),
                    ..
                } if *executable == main
            ) && shape_contains_callable(&world, layout.structural)
        })
        .unwrap_or_else(|| {
            panic!(
                "main should resume the make/3 tuple return with the callable field still present: {:?}",
                plan.position_layouts
            )
        });
    let resume_shape = resume_layout.structural;
    let callable = first_callable_in_shape(&world, resume_shape)
        .expect("the resumed tuple shape should contain the returned callable field");
    let (callables, boundaries) = callable_owner_facts_for_test(session);
    let facts = callables
        .get(&callable)
        .unwrap_or_else(|| panic!("returned callable should have facts: {callables:?}"));
    let boundary = facts
        .boundary_ids
        .iter()
        .copied()
        .map(|boundary| (boundary, world.boundary(boundary)))
        .find(|(_, boundary)| boundary.callable == callable)
        .unwrap_or_else(|| {
            panic!(
                "the tuple-returned callable should publish a boundary at the resume seam: {:?}",
                callables
            )
        });
    assert!(
        boundaries
            .get(&boundary.0)
            .is_some_and(|facts| facts.publications.iter().any(|position| position == resume_position)),
        "the callable boundary must record the resume payload publication that carries the boxed closure pointer; \
         resume_position={resume_position:?}; boundary={:?}; boundary_facts={:?}; seam_facts={:?}",
        boundary.1,
        boundaries.get(&boundary.0),
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
                } if executable == &main && *candidate_callsite == *callsite && *candidate_entry == *entry
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_protocol_escaped_continuation.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();

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
    let mut world = World::new();
    world.submit_code(
        Some("transport_direct_and_escaped_callable.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let main = executable_for(&world, session, "main", 0);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: main });
    let ShapeDescr::Callable(callable) = shape_descr(&world, returned) else {
        panic!("main/0 should return the callable value it also invoked directly")
    };
    let callable = *callable;
    let producer_function = world
        .callable(callable)
        .function
        .unwrap_or_else(|| panic!("returned direct-and-escaped callable should name its local producer"));
    let flow = upstream_callable_flow_for_producer(&world, session, producer_function);
    assert_callable_facts_match_upstream_flow(&mut world, session, callable, &flow);
    let (callables, boundaries) = callable_owner_facts_for_test(session);
    let facts = callables
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
    let runtime_demands = runtime_demands_for_frontier(&world, session);
    for boundary in facts.boundary_ids.iter() {
        let boundary_facts = boundaries
            .get(boundary)
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
        // The direct surface above and this boundary are two ways to reach one
        // lambda, and only the direct one carries the discard. A boundary is
        // the boxed apply seam: its wrapper's public return form comes from
        // these members, and no callsite past the seam names them, so the
        // discard on the direct side must not narrow them (fz-kdt.155).
        assert!(
            target_demands
                .iter()
                .all(|(_, demand)| demand.as_ref().is_some_and(|demand| !demand.is_ignore())),
            "a member behind a first-class boundary carries the seam's return lane even while a direct \
             sibling callsite discards its result: {target_demands:?}",
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_callable_capture_flow.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let (callables, _) = callable_owner_facts_for_test(session);
    let captured_callable = callables
        .iter()
        .find_map(|(outer, _)| {
            let outer_descr = world.callable(*outer);
            let [capture_layout] = outer_descr.capture_layouts.as_ref() else {
                return None;
            };
            let ShapeDescr::Callable(captured) = shape_descr(&world, capture_layout.structural) else {
                return None;
            };
            Some(*captured)
        })
        .unwrap_or_else(|| {
            panic!(
                "outer direct callable should capture add1 as a callable shape: {:?}",
                callables
            )
        });
    let captured_facts = callables
        .get(&captured_callable)
        .unwrap_or_else(|| panic!("captured callable facts should be present"));
    let producer_function = world
        .callable(captured_callable)
        .function
        .unwrap_or_else(|| panic!("captured callable should name its local producer"));
    let flow = upstream_callable_flow_for_producer(&world, session, producer_function);
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_recursive_callable_return.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let make = executable_for(&world, session, "make", 1);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: make });
    let ShapeDescr::Callable(callable) = shape_descr(&world, returned) else {
        panic!("recursive make/1 should return a callable shape")
    };
    let (callables, _) = callable_owner_facts_for_test(session);
    let facts = callables
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_duplicate_capture_lanes.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let make = executable_for(&world, session, "make", 2);
    let returned = plan_shape_at(&plan, &TransportPosition::ExecutableReturn { executable: make });
    let ShapeDescr::Callable(callable) = shape_descr(&world, returned) else {
        panic!("make/2 should return a callable shape")
    };
    assert!(
        callable_owner_facts_for_test(session).0.contains_key(callable),
        "returned callable facts should be present"
    );
    assert_eq!(
        callable_capture_lanes(&world, *callable).len(),
        2,
        "two same-typed captures are two ordered payload lanes, not one deduplicated lane"
    );
    let boundary = single_boundary_descr(&world, session);
    assert_eq!(
        boundary.callable, *callable,
        "the boundary must derive its capture payload from the callable descriptor"
    );
}

#[test]
fn compiler2_transport_plan_publishes_boundary_contracts_per_surface() {
    let source = r#"
fn main() do
  id = fn (x) -> x end
  id.(1)
  id.({1, 2})
  id
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_surface_specific_boundary_contracts.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let (_, boundary_facts) = callable_owner_facts_for_test(session);
    assert_eq!(
        boundary_facts.len(),
        2,
        "one escaped callable used at two surfaces should publish one boundary contract per surface"
    );
    for (boundary, facts) in &boundary_facts {
        let boundary_descr = world.boundary(*boundary);
        let [target] = facts.resolutions.as_ref() else {
            panic!("each callable boundary should name its exact executable target: {boundary:?} -> {facts:?}")
        };
        assert_eq!(
            target.activation.input.len(),
            boundary_descr.surface_arg_layouts.len(),
            "boundary target arity should match the boundary's published surface"
        );
    }
}

#[test]
fn compiler2_transport_plan_does_not_publish_dead_callable_input_boundaries() {
    let source = include_str!("../../fixtures2/behavior/range_enumerable.fz");

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_range_enumerable_dead_boundary.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let (_, boundaries) = callable_owner_facts_for_test(session);
    let dead_return_boundaries = boundaries
        .iter()
        .filter_map(|(boundary, facts)| {
            facts
                .resolutions
                .iter()
                .any(|target| {
                    matches!(
                        shape_descr(
                            &world,
                            plan_shape_at(
                                &plan,
                                &TransportPosition::ExecutableReturn {
                                    executable: target.clone(),
                                },
                            ),
                        ),
                        ShapeDescr::Nothing
                    )
                })
                .then_some(*boundary)
        })
        .collect::<Vec<_>>();
    assert!(
        dead_return_boundaries.is_empty(),
        "first-class callable boundaries whose resolved target returns an empty type are not callable contracts: {dead_return_boundaries:?}"
    );
}

#[test]
fn compiler2_transport_plan_scopes_enum_predicate_callback_inputs_to_concrete_activations() {
    let source = include_str!("../../fixtures2/behavior/enum_predicate_search.fz");

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_enum_predicate_search_activation_inputs.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_recursive_tuple_return.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let pair_down = executable_for(&world, session, "pair_down", 1);
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
#[serial_test::serial]
fn compiler2_pull_runtime_demand_keeps_enum_reduce_operator_refs_direct_callable() {
    let tel = ConfiguredTelemetry::new();
    let pull_events = PullTelemetryCapture::install(&tel);
    let finished_producer_pokes = capture_finished_producer_pokes(&tel);
    let mut world = World::new();
    let root = submit_enum_reduce_operator_ref_root(&mut world, &tel, "pull_runtime_enum_reduce_operator_refs.fz");
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = driver.session();
    let executables = session
        .memo()
        .materialized_executables()
        .map(|(executable, _)| executable)
        .collect::<Vec<_>>();

    let plus_flows = executables
        .iter()
        .filter_map(|executable| world.runtime_demand(executable))
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
        "the RuntimeDemand fact should keep operator refs as direct Kernel.+/2 callable flows: {plus_flows:?}"
    );
    assert!(
        plus_flows
            .iter()
            .all(|flow| flow.first_class_surfaces.is_empty() && !flow.opaque && !flow.escape),
        "operator refs used only as Enum.reduce reducers should not become first-class demand: {plus_flows:?}"
    );
    let executable_fact_pokes = assert_materialized_executable_fact_authority(&world, &driver.session());
    assert!(
        pull_events.produced_count() > 0,
        "product path should emit finished produced outcomes"
    );
    assert_eq!(*finished_producer_pokes.borrow(), Some(executable_fact_pokes));
}

#[test]
fn compiler2_runtime_demand_leaves_an_unused_callable_input_omitted() {
    // INTENT: a semantically-present but unused callable input claims no runtime
    // demand — its lane is omitted from transport instead of shipping a dead
    // closure value.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("unused_callable_input.fz".to_string()),
        r#"
fn ignore(f), do: 1
fn main() do
  id = fn x -> x end
  ignore(id)
end
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();

    let demand = runtime_demand_fact_for_function(&world, session, "ignore", 1);
    assert_eq!(
        demand.input_demands,
        vec![RuntimeDemand::ignore()],
        "semantic inputs stay present, but an unused callable input should not claim runtime demand",
    );
    let omitted_inputs = runtime_demands_for_frontier(&world, session)
        .values()
        .flat_map(|demand| demand.input_demands.iter())
        .filter(|input| input.is_ignore())
        .count();
    assert!(
        omitted_inputs >= 1,
        "the product demand inventory should keep omitted inputs countable",
    );
}

#[test]
#[serial_test::serial]
fn compiler2_exact_enum_with_index_mapper_enters_the_selected_clause_without_a_runtime_dispatch() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("enum_with_index_selected_clause.fz".to_string()),
        r#"
fn main(), do: Enum.with_index(["a", "b"], fn (x, _index) -> x <> "!" end)
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = pull_root_backend_driver_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let (executable, materialized) = session
        .memo()
        .materialized_executables()
        .find(|(executable, materialized)| {
            function_is(&world, executable.activation.function, "with_index", 2)
                && materialized
                    .runtime_demand
                    .input_demands
                    .get(1)
                    .is_some_and(|demand| !demand.callable.is_empty())
        })
        .expect("the mapper overload should materialize one with_index/2 executable");

    let mapper_demand = &materialized.runtime_demand.input_demands[1];
    assert!(matches!(mapper_demand.shape, ShapeDemand::Ignore));
    assert_eq!(mapper_demand.callable.targets.len(), 1);
    assert!(!mapper_demand.callable.is_first_class());
    let abi = session
        .memo()
        .abi_executable(executable)
        .expect("the mapper overload should publish an ABI executable");
    assert_eq!(
        abi.transport
            .layout_at(&TransportPosition::ExecutableInput {
                executable: abi.transport.executable.clone(),
                semantic_index: 1,
            })
            .map(|layout| layout.carrier),
        Some(TransportCarrier::Absent),
        "mapper input layout should be present in the materialized transport: {:?}",
        abi.transport.position_layouts,
    );
    assert_eq!(
        abi.semantic_inputs
            .iter()
            .find(|input| input.semantic_index == 1)
            .map(|input| input.layout.reprs.as_ref()),
        Some([].as_slice()),
    );
    let reachability = &world
        .activation_analysis(&executable.activation)
        .expect("the mapper overload should have settled semantic analysis")
        .entry_reachability;
    assert_eq!(reachability.clauses(), &[1]);
    assert!(!reachability.fail_reachable());
    assert!(reachability.is_direct_clause());
    assert!(
        materialized.entry_dispatch.is_none(),
        "a settled single-clause activation with no reachable failure should not re-test its lane-free mapper input",
    );
}

#[test]
fn compiler2_multi_clause_activation_retains_runtime_entry_dispatch() {
    assert_entry_dispatch_control(
        "multi_clause_runtime_dispatch.fz",
        r#"
fn main(:a), do: 1
fn main(:b), do: 2
fn main(_), do: 3
"#,
        "main",
        3,
        false,
    );
}

#[test]
fn compiler2_single_reachable_clause_with_reachable_failure_retains_runtime_entry_dispatch() {
    assert_entry_dispatch_control(
        "single_clause_reachable_failure.fz",
        r#"
fn choose(:a), do: 1
fn main(value), do: choose(value)
"#,
        "choose",
        1,
        true,
    );
}

#[test]
fn compiler2_runtime_demand_records_the_exact_surface_for_a_direct_lambda_call() {
    // INTENT: a lambda that is only ever invoked directly keeps exactly one
    // resolved call surface — no escape, no opacity, no boxed materialization.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("direct_lambda_call.fz".to_string()),
        r#"
fn main() do
  add1 = fn x -> x + 1 end
  add1.(1)
end
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let demands = runtime_demands_for_frontier(&world, &driver.session());

    let direct_callable_flows = demands
        .values()
        .flat_map(|demand| demand.callable_flows.values())
        .filter(|flow| !flow.direct_surfaces.is_empty())
        .count();
    assert!(
        direct_callable_flows >= 1,
        "the product demand inventory should report direct callable flow",
    );
    assert!(
        demands.values().any(|demand| {
            has_callable_flow(demand, |flow| {
                !flow.escape && !flow.opaque && flow.direct_surfaces.len() == 1
            })
        }),
        "a directly-invoked lambda should keep one exact resolved surface",
    );
}

/// fz-kdt.155 — INTENT: what a discarded closure call narrows its callee to
/// depends on whether a boxed apply seam reaches that callee, and on nothing
/// else. Both programs below discard `f.(1)` through a callsite that names its
/// target. They differ in one line: the first hands `f` back out of `main`, so
/// a construction wrapper is built for it and the members behind that wrapper
/// are the seam's authority for what crosses it — no consumer past the seam can
/// narrow them, so nothing may. The second keeps `f` to itself, no wrapper
/// exists, and the discard reaches the lambda's own return exactly as it always
/// did.
///
/// This is the axis fz-kdt.155 turns on. Getting it wrong in either direction
/// is a `fz_closure_get_capture_atom` abort (narrow a boxed member and the
/// wrapper hands back a lane the caller never reserved) or dead work (widen a
/// callable nobody boxes).
#[test]
fn compiler2_a_discarded_closure_call_narrows_its_callee_only_when_no_seam_boxes_it() {
    fn returned_lambda_return_demand(source: &str) -> RuntimeDemand {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        world.submit_code(Some("discarded_closure_call.fz".to_string()), source.to_string());
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
        let _ = &plan;
        let session = &*driver.session();
        let demands = runtime_demands_for_frontier(&world, session);
        // The callable-flow fact names the function it constructs; that is the
        // lambda whose own return the discarded call may or may not reach.
        let lambda_function = demands
            .values()
            .flat_map(|demand| demand.callable_flows.values())
            .map(|flow| flow.function)
            .next()
            .expect("`f` is a locally constructed callable and publishes a callable-flow fact");
        demands
            .iter()
            .find(|(executable, _)| executable.activation.function == lambda_function)
            .map(|(_, demand)| demand.return_demand.clone())
            .expect("the adder lambda should be part of the settled demand closure")
    }

    let boxed = returned_lambda_return_demand(
        r#"
fn make_adder(a), do: fn (x) -> x + a end
fn main() do
  f = make_adder(10)
  f.(1)
  f
end
"#,
    );
    assert!(
        !boxed.is_ignore(),
        "a lambda handed out through a construction wrapper carries the seam's return lane however \
         little its own callsites want it: {boxed:?}",
    );

    let never_boxed = returned_lambda_return_demand(
        r#"
fn make_adder(a), do: fn (x) -> x + a end
fn main() do
  f = make_adder(10)
  f.(1)
  0
end
"#,
    );
    assert!(
        never_boxed.is_ignore(),
        "no seam boxes this lambda, so the discarded call reaches its own return and narrows it to \
         nothing: {never_boxed:?}",
    );
}

#[test]
fn compiler2_runtime_demand_marks_an_escaped_callable_first_class() {
    // INTENT: a callable that escapes its definer with no known call surface is
    // a first-class runtime obligation — escaped but not opaque, with exactly
    // one first-class surface and one canonical executable resolution.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("escaped_callable.fz".to_string()),
        r#"
fn make() do
  fn x -> x + 1 end
end
fn main(), do: make()
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();

    let demand = runtime_demand_fact_for_function(&world, session, "make", 0);
    assert!(
        has_callable_flow(&demand, |flow| flow.escape && !flow.opaque),
        "a callable that escapes should be first-class at runtime: {demand:?}",
    );
    assert!(
        demand.callable_flows.values().any(|flow| {
            flow.escape
                && !flow.opaque
                && flow.direct_surfaces.is_empty()
                && flow.first_class_surfaces.len() == 1
                && flow.resolutions.len() == 1
        }),
        "an escaped callable with no known call surface should publish a first-class surface and canonical resolution upstream: {demand:?}",
    );
    let first_class_callable_flows = runtime_demands_for_frontier(&world, session)
        .values()
        .flat_map(|demand| demand.callable_flows.values())
        .filter(|flow| !flow.first_class_surfaces.is_empty())
        .count();
    assert!(
        first_class_callable_flows >= 1,
        "the product demand inventory should keep first-class callable flows countable",
    );
}

#[test]
fn compiler2_runtime_demand_keeps_a_returned_direct_callable_out_of_first_class_inventory() {
    // INTENT: a returned callable that every consumer calls directly stays a
    // direct callable flow — returning it does not force a first-class boxed
    // callable object.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("returned_direct_callable_transport.fz".to_string()),
        r#"
fn apply(fun), do: fun.(41)

fn make_adder(a), do: fn x -> x + a end

fn main(), do: apply(make_adder(1))
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;

    let demand = runtime_demand_fact_for_function(&world, &driver.session(), "make_adder", 1);
    assert!(
        has_callable_flow(&demand, |flow| {
            !flow.escape && !flow.opaque && !flow.direct_surfaces.is_empty()
        }),
        "make_adder/1 should still publish direct callable flow for transport",
    );
    assert!(
        !has_callable_flow(&demand, |flow| flow.escape || flow.opaque),
        "direct-only returned callable transport should not require a first-class callable object",
    );
}

#[test]
fn compiler2_runtime_demand_makes_opaque_callable_use_explicit() {
    // INTENT: calling an unresolved closure input keeps the opacity explicit —
    // the input demand carries the opaque callable obligation together with the
    // one observed call surface instead of collapsing to a plain value demand.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("opaque_callable_use.fz".to_string()),
        "fn main(f), do: f.(1)\n".to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();

    let demand = runtime_demand_fact_for_function(&world, session, "main", 1);
    assert!(
        matches!(
            demand.input_demands.as_slice(),
            [input] if !input.callable.is_empty()
                && input.callable.opaque
                && input.callable.resolved.len() == 1
                && input.callable.resolved.iter().any(|surface| surface.inputs.len() == 1)
        ),
        "an unresolved closure call should keep opaque callable demand and its observed surface explicit: {demand:?}",
    );
    let opaque_callable_demands = runtime_demands_for_frontier(&world, session)
        .values()
        .flat_map(|demand| demand.input_demands.iter())
        .filter(|input| input.callable.opaque)
        .count();
    assert!(
        opaque_callable_demands >= 1,
        "the product demand inventory should keep opaque callable demands countable",
    );
}

#[test]
fn compiler2_runtime_demand_marks_callable_arguments_to_opaque_calls_first_class() {
    // INTENT: a local lambda handed to an opaque closure call escapes — the
    // call-argument demand records the escape, and the lambda's callable flow
    // becomes a first-class obligation with a canonical resolution.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("opaque_call_callable_argument.fz".to_string()),
        r#"
fn main(f) do
  g = fn (x) -> x + 1 end
  f.(g)
end
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;

    let demand = runtime_demand_fact_for_function(&world, &driver.session(), "main", 1);
    assert!(
        demand.call_arg_demands.values().any(|demands| {
            matches!(
                demands.as_slice(),
                [arg] if !arg.callable.is_empty()
                    && arg.callable.escape && !arg.callable.opaque && arg.callable.resolved.is_empty()
            )
        }),
        "opaque closure-call argument demand should preserve callable escape before transport runs: {demand:?}",
    );
    assert!(
        has_callable_flow(&demand, |flow| {
            flow.escape
                && !flow.opaque
                && flow.direct_surfaces.is_empty()
                && flow.first_class_surfaces.len() == 1
                && flow.resolutions.len() == 1
        }),
        "the local lambda passed through the opaque call should be a first-class runtime obligation: {demand:?}",
    );
    let main = executable_for(&world, &driver.session(), "main", 1);
    let session = driver.session();
    let constructions = root_backend_answer_for_test(&session)
        .transport
        .callable_owners
        .iter()
        .filter(|positioned| positioned.position.executable() == &main)
        .filter_map(|positioned| positioned.owner.construction.as_ref())
        .collect::<Vec<_>>();
    let [construction] = constructions.as_slice() else {
        panic!("the lambda passed to an opaque call should own one first-class construction: {constructions:#?}")
    };
    assert!(
        !construction.members.is_empty(),
        "the opaque-call argument construction must retain its executable member",
    );
}

#[test]
fn compiler2_runtime_demand_marks_joined_function_refs_first_class_before_reduce_boundary() {
    // INTENT: named function refs that join across branches before feeding
    // Enum.reduce stay directly callable AND publish first-class obligations,
    // and the delivered joined value itself carries the escaped callable demand
    // with its arity-2 surface before downstream lowering.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("opaque_fn_value_join.fz".to_string()),
        include_str!("../../fixtures2/behavior/opaque_fn_value_join.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();

    let demands = runtime_demands_for_frontier(&world, session);
    let (main_executable, demand) = demands
        .iter()
        .find(|(executable, _)| function_is(&world, executable.activation.function, "main", 0))
        .expect("product runtime demand for main/0");
    for branch in ["add_a", "add_b"] {
        assert!(
            demand.callable_flows.values().any(|flow| {
                function_is(&world, flow.function, branch, 2)
                    && flow.direct_surfaces.iter().any(|surface| surface.inputs.len() == 2)
                    && !flow.direct_edges.is_empty()
                    && flow
                        .direct_edges
                        .iter()
                        .all(|edge| edge.resolution.activation.function == flow.function)
                    && flow
                        .first_class_surfaces
                        .iter()
                        .any(|surface| surface.inputs.len() == 2)
                    && flow.escape
            }),
            "a branch function ref that joins before Enum.reduce must remain directly callable and also publish a first-class runtime obligation: {demand:?}",
        );
    }

    let body = world.lowered_body(main_executable.activation.function);
    let joined_value = delivered_value_joins(&body)
        .values()
        .find_map(|join| {
            let producer_functions = join
                .sources
                .iter()
                .filter_map(|source| match source {
                    DeliveredValueSource::LocalValue(value) => {
                        demand.callable_flows.get(value).map(|flow| flow.function)
                    }
                    DeliveredValueSource::CallsiteReturn(_) => None,
                })
                .collect::<Vec<_>>();
            (producer_functions
                .iter()
                .any(|function| function_is(&world, *function, "add_a", 2))
                && producer_functions
                    .iter()
                    .any(|function| function_is(&world, *function, "add_b", 2)))
            .then_some(join.value)
        })
        .expect("main should have a delivered join fed by add_a/2 and add_b/2 function refs");
    let joined_demand = demand
        .value_demands
        .get(&joined_value)
        .unwrap_or_else(|| panic!("joined callable value {joined_value:?} should have runtime demand"));
    if joined_demand.callable.is_empty() {
        panic!("joined value {joined_value:?} should be callable-demanded: {demand:?}");
    }
    let joined_callable = &joined_demand.callable;
    assert!(
        joined_callable.escape && joined_callable.resolved.iter().any(|surface| surface.inputs.len() == 2),
        "the delivered joined callable value itself must publish a first-class discriminator before downstream lowering: {joined_callable:?}",
    );
}

#[test]
fn compiler2_runtime_demand_resolves_enum_take_first_class_reducer_surfaces_before_transport() {
    // INTENT: Enum.take's internal reducer callables settle to first-class
    // surfaces whose upstream executable edges are resolved before transport
    // consumes them — no surface reaches transport without its edges.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("runtime_demand_enum_take_reducer_surfaces.fz".to_string()),
        "fn main() do\n  xs = [1, 2, 3, 4, 5]\n  dbg(Enum.take(xs, 3))\nend\n".to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;

    let demands = runtime_demands_for_frontier(&world, &driver.session());
    let first_class_flows = demands
        .values()
        .flat_map(|demand| demand.callable_flows.values())
        .filter(|flow| !flow.first_class_surfaces.is_empty())
        .collect::<Vec<_>>();

    assert!(
        !first_class_flows.is_empty(),
        "Enum.take should publish first-class callable-flow surfaces before transport: {demands:?}",
    );
    assert!(
        first_class_flows.iter().all(|flow| !flow.first_class_edges.is_empty()),
        "every first-class callable-flow surface must carry upstream executable edges before transport consumes it: {first_class_flows:?}",
    );
}

#[test]
fn compiler2_runtime_demand_keeps_escaped_callable_return_opaque() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("runtime_demand_opaque_callable_tuple_return.fz".to_string()),
        r#"
fn make_pairer(), do: fn (x) -> {{1, 2}, 3} end
fn main(), do: make_pairer()
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;

    let runtime_demands = runtime_demands_for_frontier(&world, &driver.session());
    let tuple_return_demands = runtime_demands
        .iter()
        .filter_map(|(executable, demand)| {
            let function_ref = world.function_ref(executable.activation.function);
            (function_ref.name.starts_with("#lambda:") && function_ref.arity == 1).then_some(&demand.return_demand)
        })
        .collect::<Vec<_>>();
    let lambda_return_predicates = runtime_demands
        .keys()
        .filter_map(|executable| {
            let function_ref = world.function_ref(executable.activation.function);
            (function_ref.name.starts_with("#lambda:") && function_ref.arity == 1)
                .then(|| world.activation_return(&executable.activation))
                .flatten()
        })
        .map(|ty| world.types().runtime_type_predicate(&ty))
        .collect::<Vec<_>>();
    assert!(
        tuple_return_demands
            .iter()
            .all(|demand| demand.callable.is_empty() && matches!(demand.shape, ShapeDemand::Whole)),
        "the public carrier may be demanded as a whole but must not reconstruct tuple fields from its semantic type: {:?}",
        (tuple_return_demands, lambda_return_predicates)
    );
    assert!(
        lambda_return_predicates
            .iter()
            .any(|predicate| predicate.tuples.arities().contains(&2)),
        "the control must retain a tuple semantic return type while runtime demand remains ignored"
    );
}

#[test]
fn compiler2_runtime_demand_records_recursive_tuple_resume_value_demand() {
    // INTENT: the value resumed from a recursive call that is immediately
    // destructured carries tuple-field demand upstream, so the recursive return
    // can be delivered field-wise instead of as a boxed whole.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("runtime_demand_recursive_tuple_resume.fz".to_string()),
        r#"
fn pair_down(0), do: {0, 1}
fn pair_down(n) do
  {left, right} = pair_down(n - 1)
  {left, right}
end

fn main() do
  {left, right} = pair_down(2)
  left + right
end
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;

    let resume_demands = runtime_demands_for_frontier(&world, &driver.session())
        .iter()
        .filter_map(|(executable, demand)| {
            function_is(&world, executable.activation.function, "pair_down", 1).then_some(demand.value_demands.clone())
        })
        .flat_map(|demands| demands.into_values())
        .collect::<Vec<_>>();
    assert!(
        resume_demands.iter().any(|demand| {
            demand.callable.is_empty() && matches!(&demand.shape, ShapeDemand::TupleFields(fields) if fields.len() == 2)
        }),
        "recursive call resume value should carry tuple-field demand upstream: {resume_demands:?}"
    );
}

#[test]
fn compiler2_runtime_demand_preserves_reducer_surface_when_suspend_continuation_escapes() {
    // INTENT: when a suspend-shaped Enumerable.reduce continuation escapes, the
    // user reducer's direct arity-2 surface survives with canonical (not
    // type-template) executable resolutions — the escape of the continuation
    // must not erase the reducer's proven call surface.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("runtime_demand_enumerable_reduce_suspend_continuation.fz".to_string()),
        r#"
fn make() do
  fn () ->
    Enumerable.reduce([1, 2, 3], {:suspend, 0}, fn (x, acc) -> {:cont, acc + x} end)
  end
end

fn main(), do: make()
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();

    let reducer_executables = session
        .demanded_executables()
        .iter()
        .filter(|executable| {
            let function_ref = world.function_ref(executable.activation.function);
            function_ref.name.starts_with("#lambda:")
                && function_ref.arity == 2
                && executable.activation.input_len(world.types()) == 2
        })
        .cloned()
        .collect::<Vec<_>>();
    assert!(
        !reducer_executables.is_empty(),
        "the settled demand closure should include the user reducer lambda executable before transport"
    );
    assert!(
        reducer_executables.iter().all(|executable| {
            let inputs = executable.activation.inputs(world.types());
            inputs[0] == inputs[1]
        }),
        "the settled demand closure should hold canonical reducer activations, not type-template inputs: {reducer_executables:?}"
    );

    let demands = runtime_demands_for_frontier(&world, session);
    assert!(
        demands.values().any(|demand| {
            has_callable_flow(demand, |flow| {
                !flow.opaque && flow.direct_surfaces.iter().any(|surface| surface.inputs.len() == 2)
            })
        }),
        "the reducer direct-call surface should be proven upstream before transport: {demands:?}",
    );
    assert!(
        demands.values().any(|demand| {
            demand.callable_flows.values().any(|flow| {
                flow.direct_surfaces.iter().any(|surface| surface.inputs.len() == 2)
                    && !flow.resolutions.is_empty()
                    && flow.resolutions.iter().all(|resolution| {
                        let inputs = resolution.activation.inputs(world.types());
                        inputs.len() == 2 && inputs[0] == inputs[1]
                    })
            })
        }),
        "the reducer callable-flow fact should carry direct surfaces and canonical executable resolutions upstream: {demands:?}",
    );
}

#[test]
fn compiler2_runtime_demand_keeps_dbg_inputs_live_when_the_return_is_ignored() {
    // INTENT: dbg/1 demands its input as a whole runtime value even when the
    // caller discards the return, and the continuation after `dbg(stats)` keeps
    // the captured value live for the later field access.
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("heap_stats_dbg_resume.fz".to_string()),
        r#"
fn main() do
  stats = Process.heap_alloc_stats()
  dbg(stats)
  dbg(stats[:list_cons_allocs])
end
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();

    // The per-executable product makes every dbg/1 activation individually
    // observable; the store-era test asserted one map entry — every activation
    // must satisfy the same contract.
    let dbg_input_demands = runtime_demands_for_frontier(&world, session)
        .iter()
        .filter(|(executable, _)| function_is(&world, executable.activation.function, "dbg", 1))
        .map(|(_, demand)| demand.input_demands.clone())
        .collect::<Vec<_>>();
    assert!(
        !dbg_input_demands.is_empty(),
        "dbg/1 should be part of the settled demand closure"
    );
    for input_demands in &dbg_input_demands {
        assert_eq!(
            input_demands,
            &vec![RuntimeDemand::whole()],
            "Kernel.dbg/1 must still demand its input as a runtime value even when callers ignore the returned value",
        );
    }

    let main_demand = runtime_demand_fact_for_function(&world, session, "main", 0);
    assert!(
        main_demand
            .entry_capture_demands
            .values()
            .any(|demands| demands.as_slice() == [RuntimeDemand::whole()]),
        "the continuation after dbg(stats) must keep one captured runtime value live for the later field access: {main_demand:?}",
    );
}

#[test]
fn compiler2_uncalled_named_function_value_is_callable_in_interp_and_jit() {
    let source = "fn identity(x), do: x\nfn main(), do: dbg(identity)\n";
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("uncalled_named_function_value_product.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, _) = pull_transport_plan_for_test(&tel, &mut world, root);
    let owners = callable_owners_for_test(&driver.session());
    let constructions = owners
        .iter()
        .filter_map(|owner| owner.construction.as_ref())
        .filter(|construction| {
            world
                .callable(construction.callable)
                .function
                .is_some_and(|function| world.function_ref(function).name == "identity")
        })
        .collect::<Vec<_>>();
    let [construction] = constructions.as_slice() else {
        panic!("the uncalled named function value should own one first-class construction: {constructions:#?}")
    };
    assert!(
        !construction.members.is_empty(),
        "the uncalled named function construction must retain its executable member",
    );

    let tel = ConfiguredTelemetry::new();
    let dbg = DbgCapture::new();
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(dbg.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("uncalled_named_function_value.fz".to_string()),
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
        .expect("interpreter should preserve the callable value");
    compiler
        .run_root_jit(root)
        .expect("JIT should preserve the callable value");
    let lines = dbg.lines();
    assert_eq!(lines.len(), 2);
    assert!(lines.iter().all(|line| line.starts_with("#fn<")), "got {lines:?}");
}

#[test]
#[serial_test::serial]
fn compiler2_pull_transport_keeps_enum_reduce_operator_refs_direct_callable() {
    let tel = ConfiguredTelemetry::new();
    let pull_events = PullTelemetryCapture::install(&tel);
    let mut world = World::new();
    let root = submit_enum_reduce_operator_ref_root(&mut world, &tel, "pull_transport_enum_reduce_operator_refs.fz");
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

    let (owner_callables, _) = callable_owner_facts_for_test(&driver.session());
    let plus_callables = owner_callables
        .iter()
        .filter_map(|(callable, facts)| {
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
    let session = driver.session();
    let zero_capture_plus_input = session
        .demanded_executables()
        .iter()
        .find_map(|executable| {
            let runtime = world.runtime_demand(executable)?;
            runtime
                .input_demands
                .iter()
                .enumerate()
                .find_map(|(semantic_index, demand)| {
                    let targets = demand.callable.targets.clone();
                    if demand.callable.is_first_class() || targets.len() != 1 {
                        return None;
                    }
                    let target = targets.into_iter().next().expect("singleton target");
                    (target.activation_inputs.len() == target.surface.inputs.len()
                        && function_is(&world, target.activation.function, "+", 2))
                    .then_some((executable, semantic_index, target))
                })
        })
        .expect("Enum.reduce should carry an exact zero-capture Kernel.+/2 input");
    let plus_layout = plan
        .layout_at(&TransportPosition::ExecutableInput {
            executable: executable_symbol_for(&world, zero_capture_plus_input.0),
            semantic_index: zero_capture_plus_input.1,
        })
        .expect("Kernel.+ input layout");
    let ShapeDescr::Callable(plus_callable) = shape_descr(&world, plus_layout.structural) else {
        panic!("the exact Kernel.+/2 input should retain a callable shape")
    };
    let plus_descr = world.callable(*plus_callable);
    assert_eq!(plus_descr.function, Some(zero_capture_plus_input.2.activation.function));
    assert!(callable_capture_lanes(&world, *plus_callable).is_empty());
    assert_eq!(plus_layout.carrier, TransportCarrier::Absent);
    assert_materialized_executable_fact_authority(&world, &driver.session());
    assert!(
        pull_events.produced_count() > 0,
        "product transport path should emit finished produced outcomes"
    );
}

#[test]
#[serial_test::serial]
fn compiler2_pull_transport_shape_is_stable_across_product_request_order() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let root = submit_enum_reduce_operator_ref_root(
        &mut world,
        &tel,
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
    let ProductValue::TransportShape(TransportShapeFact::Layout(TransportLayout {
        structural: shape_first_shape,
        ..
    })) = shape_first
    else {
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
fn compiler2_pull_materialized_products_keep_enum_reduce_operator_refs_symbolic() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let root = submit_enum_reduce_operator_ref_root(&mut world, &tel, "pull_materialized_enum_reduce_operator_refs.fz");
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;

    assert!(
        driver
            .session()
            .memo()
            .materialized_executables()
            .any(|(executable, _)| {
                let function = world.function_ref(executable.activation.function);
                function.name == "main" && function.arity == 0
            }),
        "product materialization should include main/0"
    );
    assert!(
        driver
            .session()
            .memo()
            .materialized_executables()
            .any(|(executable, _)| {
                let function = world.function_ref(executable.activation.function);
                function.name == "+" && function.arity == 2
            }),
        "product materialization should include Kernel.+/2"
    );
    for (caller, materialized) in driver.session().memo().materialized_executables() {
        for edge in materialized.call_edges.values() {
            for callee in materialized_call_edge_callees(edge) {
                assert!(
                    driver.session().memo().materialized_executable(callee).is_some(),
                    "symbolic materialized call edge from {caller:?} points to an undemanded callee {callee:?}"
                );
            }
        }
    }
    assert_materialized_executable_fact_authority(&world, &driver.session());
}

#[test]
#[serial_test::serial]
fn compiler2_pull_abi_and_backend_products_keep_call_edges_symbolic() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let root = submit_enum_reduce_operator_ref_root(&mut world, &tel, "pull_abi_backend_enum_reduce_operator_refs.fz");
    let driver = pull_root_backend_driver_for_test(&tel, &mut world, root);
    let executables = driver
        .session()
        .memo()
        .backend_executables()
        .map(|(executable, _)| executable.clone())
        .collect::<HashSet<_>>();

    assert_eq!(
        driver.session().memo().abi_executables().count(),
        executables.len(),
        "ABI products should be per demanded executable"
    );
    assert_eq!(
        driver.session().memo().backend_executables().count(),
        executables.len(),
        "backend products should be per demanded executable"
    );
    for (caller, abi) in driver.session().memo().abi_executables() {
        for edge in abi.call_edges.values() {
            for callee in abi_ready_call_edge_callees(edge) {
                assert!(
                    executables.contains(callee),
                    "ABI call edge from {caller:?} should remain an ExecutableKey in the demanded set, got {callee:?}"
                );
            }
        }
    }
    for (caller, backend) in driver.session().memo().backend_executables() {
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
    assert_materialized_executable_fact_authority(&world, &driver.session());
}

#[test]
#[serial_test::serial]
fn compiler2_pull_root_backend_product_packages_and_runs_enum_reduce_operator_refs() {
    let tel = ConfiguredTelemetry::new();
    let finished_producer_pokes = capture_finished_producer_pokes(&tel);
    let (_interp_root, no_dump_jobs) = product_no_dump_interp_job_telemetry(ENUM_REDUCE_OPERATOR_REF_SOURCE);
    let no_dump_job_fires = no_dump_jobs.total_stops();
    assert!(
        no_dump_job_fires < LEGACY_00181_NO_DUMP_JOB_STARTS,
        "product no-dump interp should reduce fixture 00181 compiler job starts below the legacy baseline; got {no_dump_job_fires}"
    );

    let mut world = World::new();
    let root = submit_enum_reduce_operator_ref_root(&mut world, &tel, "pull_root_backend_enum_reduce_operator_refs.fz");
    let pull_events = PullTelemetryCapture::install(&tel);
    let product_jobs = JobTelemetry::new();
    product_jobs.install(&tel);
    let (program, driver) =
        super::product_drive::drive_root_backend_product::<_, PanicProductDriveError>(&mut world, &tel, root)
            .expect("panic-based ProductDriveError never returns Err");
    let packaged = program
        .executables
        .iter()
        .map(|executable| executable.key.clone())
        .collect::<HashSet<_>>();
    let demanded = driver
        .session()
        .memo()
        .backend_executables()
        .map(|(executable, _)| executable.clone())
        .collect::<HashSet<_>>();
    assert_eq!(
        packaged, demanded,
        "final backend packaging should preserve the demanded executable frontier"
    );
    let mut ordered = demanded.into_iter().collect::<Vec<_>>();
    ordered.sort_by(|left, right| left.semantic_cmp(right, world.types()));
    assert_eq!(
        program
            .executables
            .iter()
            .map(|executable| &executable.key)
            .collect::<Vec<_>>(),
        ordered.iter().collect::<Vec<_>>(),
        "the backend program vector is the one typed, deterministic dense executable index"
    );
    assert!(
        program.construction_wrappers.is_empty(),
        "direct operator refs should not fabricate first-class construction wrappers",
    );
    assert_direct_clause_param_forwards_have_abi_reprs(&world, &program);
    let executable_fact_pokes = assert_materialized_executable_fact_authority(&world, &driver.session());
    driver.finish_session();
    assert!(
        product_jobs.total_stops() > 0,
        "cold root product demand should drive exact fact prerequisites without legacy pre-settle"
    );
    assert!(
        pull_events.produced_count() > 0,
        "root backend product path should emit finished produced outcomes"
    );
    assert_eq!(*finished_producer_pokes.borrow(), Some(executable_fact_pokes));

    assert!(
        no_dump_job_fires > 0,
        "public no-dump interp proof should exercise the product-built BackendProgram"
    );
}

fn assert_direct_clause_param_forwards_have_abi_reprs(world: &World, program: &super::artifact::BackendProgram) {
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
            if executable_input_shape_is_nothing(world, callee, 0) {
                continue;
            }
            checked += 1;
            assert!(
                executable.value_layouts.contains_key(&first_arg.value),
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
    world: &World,
    executable: &super::artifact::BackendExecutable,
    semantic_index: usize,
) -> bool {
    let shape = executable
        .semantic_inputs
        .iter()
        .find(|input| input.semantic_index == semantic_index)
        .map(|input| input.layout.structural)
        .unwrap_or_else(|| panic!("backend product should publish callee input {semantic_index}"));
    matches!(world.shape(shape), ShapeDescr::Nothing)
}

#[test]
fn compiler2_transport_plan_publishes_joined_enum_reduce_reducer_as_first_class() {
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_enum_reduce_joined_reducer.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let (callables, _) = callable_owner_facts_for_test(session);
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

    let reducer_arg_shapes = plan
        .position_layouts
        .iter()
        .filter_map(|(position, layout)| match position {
            TransportPosition::CallArg { semantic_index: 2, .. }
                if matches!(shape_descr(&world, layout.structural), ShapeDescr::Callable(_)) =>
            {
                Some(layout.structural)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        !reducer_arg_shapes.is_empty(),
        "the third Enum.reduce argument should be transported as a callable shape, not a scalar lane: {:?}",
        plan.position_layouts
    );
    assert!(
        reducer_arg_shapes.iter().any(|shape| {
            let ShapeDescr::Callable(callable) = shape_descr(&world, *shape) else {
                return false;
            };
            callables
                .get(callable)
                .is_some_and(|facts| !facts.boundary_ids.is_empty())
        }),
        "the joined reducer must publish a first-class callable boundary instead of pooling a direct target"
    );
}

#[test]
fn compiler2_transport_plan_publishes_joined_callable_value_position_before_native_capture() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("opaque_fn_value_join.fz".to_string()),
        include_str!("../../fixtures2/behavior/opaque_fn_value_join.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let main = executable_for(&world, session, "main", 0);
    let add_a = executable_for(&world, session, "add_a", 2).activation.function;
    let add_b = executable_for(&world, session, "add_b", 2).activation.function;
    let (_, boundaries) = callable_owner_facts_for_test(session);
    let (boundary, facts) = boundaries
        .iter()
        .find(|(_, facts)| {
            let resolutions = facts
                .resolutions
                .iter()
                .map(|resolution| resolution.activation.function)
                .collect::<HashSet<_>>();
            resolutions.contains(&add_a) && resolutions.contains(&add_b)
        })
        .unwrap_or_else(|| {
            panic!("one published boundary must own the joined add_a/add_b resolutions: {boundaries:?}")
        });
    let publications = facts
        .publications
        .iter()
        .filter(|position| position.executable() == &main)
        .inspect(|&position| {
            let layout = plan
                .layout_at(position)
                .unwrap_or_else(|| panic!("a published callable position must carry its settled layout: {position:?}"));
            let ShapeDescr::Callable(callable) = shape_descr(&world, layout.structural) else {
                panic!("a joined callable publication must remain callable-shaped: {position:?} -> {layout:?}")
            };
            assert_eq!(world.callable(*callable).function, None);
            assert!(layout.carrier.is_value_ref());
        })
        .collect::<Vec<_>>();
    assert!(
        !publications.is_empty(),
        "main must carry the joined callable boundary before native lowering"
    );
    assert!(
        plan.codegen_seam_facts.iter().any(|fact| {
            matches!(fact.seam, CodegenSeam::FirstClassPublication { boundary: candidate } if candidate == *boundary)
                && fact.shape.is_none()
        }),
        "transport should publish a first-class codegen lane for the joined callable boundary"
    );
}

#[test]
fn compiler2_transport_plan_gives_lambda_capture_lane_for_published_callable_capture() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("opaque_fn_value_join.fz".to_string()),
        include_str!("../../fixtures2/behavior/opaque_fn_value_join.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let (callables, _) = callable_owner_facts_for_test(session);
    let lambda_capturing_published_callable = callables.keys().find_map(|callable| {
        let descr = world.callable(*callable);
        let [capture_layout] = descr.capture_layouts.as_ref() else {
            return None;
        };
        let ShapeDescr::Callable(captured) = shape_descr(&world, capture_layout.structural) else {
            return None;
        };
        let captured_descr = world.callable(*captured);
        let captured_facts = callables.get(captured)?;
        (descr.function.is_some() && captured_descr.function.is_none() && !captured_facts.boundary_ids.is_empty())
            .then_some((*callable, capture_layout.structural))
    });
    let (callable, capture_shape) = lambda_capturing_published_callable
        .expect("Enum.reduce's generated loop lambda should capture the published joined reducer value");
    let descr = world.callable(callable);
    assert_eq!(
        callable_capture_lanes(&world, callable).len(),
        1,
        "a lambda that captures a first-class callable value must carry that runtime value in a physical capture lane, not recurse into the captured callable's zero structural lanes: {descr:?}; capture_shape={capture_shape:?}",
    );
    assert!(
        callables[&callable].resolutions.iter().all(|executable| {
            plan.layout_at(&TransportPosition::ExecutableInput {
                executable: executable.clone(),
                semantic_index: 0,
            })
            .is_some_and(|layout| layout.carrier.is_value_ref())
        }),
        "each generated lambda executable must receive its first-class callable capture through a ValueRef-owned input layout: callable={callable:?}; layouts={:?}",
        plan.position_layouts,
    );
}

#[test]
fn compiler2_singleton_callable_target_refines_input_to_its_exact_capture_prefix() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("closure_typed_captures.fz".to_string()),
        include_str!("../../fixtures2/behavior/closure_typed_captures.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let (executable, semantic_index, target) = session
        .demanded_executables()
        .iter()
        .find_map(|executable| {
            let demand = world.runtime_demand(executable)?;
            demand
                .input_demands
                .iter()
                .enumerate()
                .find_map(|(semantic_index, input)| {
                    let targets = input.callable.targets.clone();
                    if targets.len() != 1 {
                        return None;
                    }
                    let target = targets.into_iter().next().expect("singleton target");
                    (!input.callable.is_first_class() && target.activation_inputs.len() > target.surface.inputs.len())
                        .then_some((executable.clone(), semantic_index, target))
                })
        })
        .expect("apply1/2 should receive one exact captured lambda target");
    let position = TransportPosition::ExecutableInput {
        executable: executable_symbol_for(&world, &executable),
        semantic_index,
    };
    let layout = plan.layout_at(&position).expect("captured callable input layout");
    let ShapeDescr::Callable(callable) = shape_descr(&world, layout.structural) else {
        panic!("the exact callable input should retain a callable shape: {layout:?}")
    };
    let descr = world.callable(*callable);
    assert_eq!(descr.function, Some(target.activation.function));
    assert_eq!(descr.capture_tys.as_ref(), &target.activation_inputs[..2]);
    assert_eq!(descr.capture_layouts.len(), 2);
    assert_eq!(callable_capture_lanes(&world, *callable).len(), 2);
    assert_eq!(layout.carrier, TransportCarrier::Absent);
}

#[test]
fn compiler2_transport_plan_keeps_a_continuation_captured_first_class_callable_boxed_by_carrier() {
    // `maplist` is non-tail recursive (`[f.(h) | maplist(t, f)]`), so its
    // recursion is captured in a continuation that closes over `f`. The phi of
    // two lambdas forces `f` to be a genuine first-class (boxed, function:None)
    // callable. The carrier owns the boxed pointer while callable structure
    // remains capture-free.
    let source = r#"
fn maplist([], _f), do: []
fn maplist([h | t], f), do: [f.(h) | maplist(t, f)]

fn main() do
  g = if true, do: (fn x -> x + 1 end), else: (fn x -> x + 2 end)
  maplist([1, 2], g)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_first_class_callable_continuation_capture.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (_driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let captured_first_class = plan
        .position_layouts
        .iter()
        .filter(|(position, _)| matches!(position, TransportPosition::EntryCapture { .. }))
        .filter_map(|(position, layout)| match shape_descr(&world, layout.structural) {
            ShapeDescr::Callable(callable) => Some((position.clone(), *layout, *callable)),
            _ => None,
        })
        .filter(|(_, _, callable)| world.callable(*callable).function.is_none())
        .collect::<Vec<_>>();
    assert!(
        !captured_first_class.is_empty(),
        "maplist's non-tail recursion must capture the first-class callable `f` in a continuation as a generic (boxed) callable shape",
    );
    for (position, layout, _) in captured_first_class {
        assert_eq!(
            world.shape_width(layout.structural),
            0,
            "a generic callable's structure must not duplicate its boxed carrier: {position:?}",
        );
        assert!(
            layout.carrier.is_value_ref(),
            "the continuation capture must carry the first-class callable through its exact layout carrier: {position:?}",
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_enum_style_reducer_captures_callable.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let (callables, _) = callable_owner_facts_for_test(session);
    let captured_callable = callables.iter().find_map(|(outer, facts)| {
        let outer_descr = world.callable(*outer);
        let [capture_layout] = outer_descr.capture_layouts.as_ref() else {
            return None;
        };
        let ShapeDescr::Callable(captured) = shape_descr(&world, capture_layout.structural) else {
            return None;
        };
        (!facts.direct_surfaces.is_empty()).then_some((*captured, capture_layout.structural, facts.resolutions.clone()))
    });
    let (captured_callable, captured_shape, reducer_resolutions) =
        captured_callable.unwrap_or_else(|| panic!("the reducer lambda should capture predicate as a callable shape"));
    for resolution in reducer_resolutions {
        let position = TransportPosition::ExecutableInput {
            executable: resolution,
            semantic_index: 0,
        };
        assert_eq!(
            plan.shape_at(&position),
            Some(captured_shape),
            "the reducer executable capture-prefix input should read the producer capture ShapeId from callable-flow resolution evidence"
        );
    }
    let captured_facts = callables
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

#[test]
fn compiler2_layout_distinct_input_positions_keep_independent_owned_answers() {
    let source = include_str!("../../fixtures2/behavior/enum_take_drop_split.fz");
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("layout_distinct_input_positions.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (_, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let mut inputs = BTreeMap::<(u32, usize), Vec<(&TransportPosition, &TransportLayout)>>::new();
    for (position, layout) in &plan.position_layouts {
        if let TransportPosition::ExecutableInput {
            executable,
            semantic_index,
        } = position
        {
            inputs
                .entry((executable.activation.function.as_u32(), *semantic_index))
                .or_default()
                .push((position, layout));
        }
    }
    let distinct = inputs.values().find(|answers| {
        answers
            .iter()
            .map(|(position, _)| position.executable().activation.input.as_ref())
            .collect::<BTreeSet<_>>()
            .len()
            >= 2
            && answers.iter().map(|(_, layout)| **layout).collect::<HashSet<_>>().len() >= 2
    });
    assert!(
        distinct.is_some(),
        "layout-distinct executable input positions must retain independent settled answers: {inputs:#?}"
    );
}

#[test]
fn compiler2_transport_plan_preserves_enum_reducer_constructions_behind_anonymous_abi() {
    let source = include_str!("../../fixtures2/behavior/enum_take_drop_split.fz");

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_enum_take_drop_split_nested_predicate_capture.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let owners = callable_owners_for_test(session);
    let reducers = owners
        .iter()
        .filter_map(|owner| owner.construction.as_ref().map(|construction| (owner, construction)))
        .filter(|(_, construction)| {
            let descr = world.callable(construction.callable);
            descr.function.is_some()
                && construction.captures.iter().any(|capture| {
                    matches!(
                        shape_descr(&world, capture.layout.structural),
                        ShapeDescr::Callable(callable) if world.callable(*callable).function.is_none()
                    )
                })
        })
        .collect::<Vec<_>>();
    assert!(
        reducers.len() >= 4,
        "the take/drop/split fixture should preserve its concrete reducer constructions: {reducers:?}"
    );
    for (owner, construction) in reducers {
        assert!(
            !construction.members.is_empty(),
            "a published reducer construction must retain its executable members: {construction:?}"
        );
        let facts = owner
            .callable_facts
            .get(&construction.callable)
            .unwrap_or_else(|| panic!("a concrete reducer construction must publish callable facts: {construction:?}"));
        assert!(
            !facts.resolutions.is_empty() && !facts.direct_edges.is_empty(),
            "a concrete reducer construction must retain its resolved call edges: {construction:?} -> {facts:?}"
        );
        for capture in construction.captures.iter().filter(|capture| {
            plan.shape_at(&capture.source)
                .is_some_and(|shape| matches!(shape_descr(&world, shape), ShapeDescr::Callable(_)))
        }) {
            let shape = plan
                .shape_at(&capture.source)
                .unwrap_or_else(|| panic!("a carrier source must publish a transport shape: {capture:?}"));
            let ShapeDescr::Callable(captured) = shape_descr(&world, shape) else {
                panic!("a carrier source must publish a callable shape: {capture:?} -> {shape:?}")
            };
            assert_eq!(
                world.callable(*captured).function,
                None,
                "the captured public callable ABI must not encode source function identity"
            );
            assert!(
                capture.layout.carrier.is_value_ref(),
                "a callable capture must carry its callable value even when its descriptor has no nested lanes",
            );
        }
    }
}

#[test]
fn compiler2_callable_construction_capture_carriers_reach_backend_wrappers() {
    let source = r#"
fn make(n) do
  if true do
    fn x -> n + x end
  else
    fn x -> n - x end
  end
end
fn main(), do: make(41).(1)
"#;
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some("scalar_capture_construction.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (program, driver) =
        super::product_drive::drive_root_backend_product::<_, PanicProductDriveError>(&mut world, &tel, root)
            .expect("panic-based ProductDriveError never returns Err");
    driver.finish_session();
    let session = &*driver.session();
    let owners = callable_owners_for_test(session);
    let constructions = owners
        .iter()
        .filter_map(|owner| owner.construction.as_ref())
        .filter(|construction| {
            world
                .callable(construction.callable)
                .function
                .is_some_and(|function| world.function_ref(function).name.starts_with("#lambda:"))
                && construction.captures.len() == 1
                && construction.members.len() == 1
        })
        .collect::<Vec<_>>();
    assert_eq!(
        constructions.len(),
        2,
        "both public scalar-capturing lambdas should retain one construction fact",
    );
    for construction in constructions {
        let descriptor = world.callable(construction.callable);
        assert_eq!(
            descriptor.capture_layouts.as_ref(),
            construction
                .captures
                .iter()
                .map(|capture| capture.layout)
                .collect::<Vec<_>>(),
            "the callable descriptor and construction must share one capture-layout authority",
        );
        for member in &construction.members {
            assert_eq!(
                world.boundary(member.boundary).callable,
                construction.callable,
                "public boundaries must derive captures from the construction's callable descriptor",
            );
        }
        let capture = &construction.captures[0];
        let shape = capture.layout.structural;
        assert!(
            matches!(shape_descr(&world, shape), ShapeDescr::Lane(_)),
            "the detached probe should exercise a scalar capture shape: {capture:?}",
        );
        assert_eq!(
            capture.layout.structural, shape,
            "the construction fact should retain the settled scalar capture shape",
        );
        assert_eq!(capture.layout.carrier, TransportCarrier::Absent);
        let wrapper = program
            .construction_wrappers
            .iter()
            .find(|wrapper| wrapper.callable == construction.callable)
            .unwrap_or_else(|| panic!("public construction should retain its backend wrapper: {construction:?}"));
        assert_eq!(
            wrapper.captures[0].layout.carrier, capture.layout.carrier,
            "backend packaging must preserve the construction fact's scalar capture carrier",
        );
        for member in &wrapper.members {
            let semantic_index = member.capture_semantic_inputs[0];
            let target_input = member
                .target_inputs
                .iter()
                .find(|input| input.semantic_index == semantic_index)
                .unwrap_or_else(|| panic!("scalar capture input should remain in the member ABI: {member:?}"));
            assert_eq!(
                target_input.layout.structural, capture.layout.structural,
                "the construction owner and member ABI must share the settled scalar shape",
            );
            assert_eq!(target_input.layout.reprs.as_ref(), &[AbiValueRepr::RawInt]);
        }
    }

    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("scalar_capture_construction_runtime.fz".to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(42));
}

#[test]
fn compiler2_callable_capture_carriers_reach_backend_wrappers() {
    let source = include_str!("../../fixtures2/behavior/enum_predicate_search.fz");
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some("callable_capture_construction.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (program, driver) =
        super::product_drive::drive_root_backend_product::<_, PanicProductDriveError>(&mut world, &tel, root)
            .expect("panic-based ProductDriveError never returns Err");
    driver.finish_session();
    let session = &*driver.session();
    let owners = callable_owners_for_test(session);
    let mut checked = 0;
    for wrapper in &program.construction_wrappers {
        let construction = owners
            .iter()
            .filter_map(|owner| owner.construction.as_ref())
            .find(|construction| construction.callable == wrapper.callable)
            .unwrap_or_else(|| panic!("backend wrapper should retain its callable construction fact"));
        let callable_capture = construction
            .captures
            .iter()
            .any(|capture| matches!(shape_descr(&world, capture.layout.structural), ShapeDescr::Callable(_)));
        assert_eq!(
            wrapper
                .captures
                .iter()
                .map(|capture| capture.layout.carrier)
                .collect::<Vec<_>>(),
            construction
                .captures
                .iter()
                .map(|capture| capture.layout.carrier)
                .collect::<Vec<_>>(),
            "backend packaging must preserve the construction fact's callable capture carriers",
        );
        for (capture_index, _) in construction.captures.iter().enumerate() {
            for member in &wrapper.members {
                let semantic_index = member.capture_semantic_inputs[capture_index];
                let target_carries = member
                    .target_inputs
                    .iter()
                    .find(|input| input.semantic_index == semantic_index)
                    .is_some_and(|input| !input.layout.reprs.is_empty());
                assert_eq!(
                    target_carries,
                    !wrapper.captures[capture_index].layout.reprs.is_empty(),
                    "the construction fact must agree with every member target capture ABI",
                );
            }
        }
        checked += usize::from(callable_capture);
    }
    assert!(checked > 0, "the fixture should package a callable capture");
}

/// A published whole-value lane is a CONTRACT, so it may only ever be wider
/// than the value it carries: every runtime value of the position's analyzed
/// type has to fit through it. A position that ships one lane whose type is
/// strictly below its own analyzed type is therefore an anomaly, not a
/// narrowing -- some of its values simply have no lane to travel in.
///
/// Decomposed positions (one lane per field) and elided ones (no lanes at all,
/// the zero a discarded result's boundary derives) are legitimately not
/// whole-value contracts and are out of scope here: the invariant binds
/// exactly where a position ships ONE lane for a whole value.
///
/// Executable returns and local values are both covered. Call arguments,
/// return payloads and resume payloads are not reachable from a published
/// `BackendExecutable`, so this gate does not see them -- reaching them needs
/// the `MaterializedTransportPlan`, which the backend product does not retain
/// on the executables themselves.
#[test]
fn compiler2_whole_value_lanes_stay_above_their_analyzed_ty() {
    let source = include_str!("../../fixtures2/behavior/enum_predicate_search.fz");
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some("return_lane_contract.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (program, driver) =
        super::product_drive::drive_root_backend_product::<_, PanicProductDriveError>(&mut world, &tel, root)
            .expect("panic-based ProductDriveError never returns Err");
    driver.finish_session();

    let mut whole_value_lanes = 0;
    let mut sunk = Vec::new();
    for executable in &program.executables {
        let name = &world.function_ref(executable.key.activation.function).name;
        let mut check = |what: String, layout: &super::artifact::BackendValueLayout, ty: Ty, world: &World| {
            let ShapeDescr::Lane(_) = shape_descr(world, layout.structural) else {
                return 0;
            };
            let [lane_ty] = layout.tys.as_ref() else {
                return 0;
            };
            if !world.types().is_subtype(&ty, lane_ty) {
                sunk.push(format!(
                    "{what} lane {} under analyzed {}",
                    world.types().display(lane_ty),
                    world.types().display(&ty),
                ));
            }
            1
        };
        whole_value_lanes += check(
            format!("{name}/{} return", executable.key.activation.function.as_u32()),
            &executable.return_layout.layout,
            executable.return_ty,
            &world,
        );
        for (value, layout) in &executable.value_layouts {
            let Some(value_ty) = executable.value_types.get(value).copied() else {
                continue;
            };
            whole_value_lanes += check(
                format!(
                    "{name}/{} v{}",
                    executable.key.activation.function.as_u32(),
                    value.as_u32()
                ),
                layout,
                value_ty,
                &world,
            );
        }
    }
    assert!(
        whole_value_lanes > 0,
        "the fixture should publish whole-value lanes for this invariant to bind",
    );
    sunk.sort();
    assert_eq!(
        sunk,
        Vec::<String>::new(),
        "every whole-value return lane must carry its position's whole analyzed type",
    );
}

/// A transport position named the way a reader can act on it: which function
/// specialization, and which position within it.
fn owner_position_label(world: &World, position: &TransportPosition) -> String {
    let activation = &position.executable().activation;
    let name = &world.function_ref(activation.function).name;
    let what = match position {
        TransportPosition::ExecutableInput { semantic_index, .. } => format!("input#{semantic_index}"),
        TransportPosition::ExecutableReturn { .. } => "return".to_string(),
        TransportPosition::ResumePayload { entry, .. } => format!("resume#{}", entry.as_u32()),
        TransportPosition::ReturnPayload { callsite, .. } => format!("payload#{}", callsite.as_u32()),
        TransportPosition::CallArg {
            callsite,
            semantic_index,
            ..
        } => format!("arg#{semantic_index}@{}", callsite.as_u32()),
        TransportPosition::EntryCapture {
            entry, capture_index, ..
        } => format!("capture#{capture_index}@{}", entry.as_u32()),
        TransportPosition::Value { value, .. } => format!("v{}", value.as_u32()),
    };
    format!(
        "{name}/{}[{}] {what}",
        activation.function.as_u32(),
        world.types().display(&activation.arrow)
    )
}

/// A boundary publication names the transport position a first-class callable
/// is published AT: this value, here, is where that boundary enters the
/// artifact. It is a fact about ONE position, so an owner may only ever
/// publish its own.
///
/// The recursion knot used to contradict that. A cycle of callable-construction
/// products settles as one group, and the group resolution projected a single
/// fact set -- built from whichever member's job happened to close the cycle --
/// and cloned it onto every member, publications included. Every member then
/// claimed to publish at every group-mate's position, and WHICH positions those
/// were came from `pending_strong_component`: transient scheduler state, so the
/// answer was a lottery the schedule drew (fz-kdt.96). The root artifact unions
/// every owner's boundary facts, which is why the surplus never showed up in a
/// canonical dump -- it showed up here, in what each owner claims about itself.
///
/// Per-member projection makes the invariant exact, and the whole surface is
/// covered by construction: every producer of a callable owner records its
/// publications against the position it is producing, and nothing merges one
/// owner's finished facts into another's.
///
/// Order-invariance itself is not a production path -- perturbing the schedule
/// is a source edit -- so the manual recipe stays here as the sibling gate
/// (precedent: fz-kdt.93). Flip `Agenda::pop` in `src/compiler2/agenda.rs` from
/// `pop_front` to `pop_back` for a full-LIFO drive, or reverse `pending` in
/// `collect_return_origins` (`src/compiler2/jobs/runtime_demand.rs`), rebuild,
/// and diff `fz2 interp --dump backend=...` against the unperturbed dump.
/// Known gap: this gate asserts publications exist globally and that no
/// owner publishes at a foreign position; it does not assert that every
/// owner with first-class boundaries publishes its OWN position, so a
/// member-level self-publication drop would pass here and be caught only
/// by seam/canon consequences downstream.
#[test]
fn compiler2_callable_owners_publish_only_their_own_position() {
    let source = include_str!("../../fixtures2/00420_enum_take_drop_split.fz");
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some("owner_publications.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let driver = pull_root_backend_driver_for_test(&tel, &mut world, root);

    let mut published = 0;
    let mut foreign = Vec::new();
    for positioned in root_backend_answer_for_test(&driver.session())
        .transport
        .callable_owners
        .iter()
    {
        for facts in positioned.owner.boundary_facts.values() {
            for publication in facts.publications.iter() {
                published += 1;
                if publication != &positioned.position {
                    foreign.push(format!(
                        "{} publishes at {}",
                        owner_position_label(&world, &positioned.position),
                        owner_position_label(&world, publication),
                    ));
                }
            }
        }
    }
    assert!(
        published > 0,
        "the fixture should publish first-class callable boundaries for this invariant to bind",
    );
    foreign.sort();
    foreign.dedup();
    assert_eq!(
        foreign,
        Vec::<String>::new(),
        "a callable owner may only publish the boundary at its own position",
    );
}

/// Large immutable facts and products cross several ownership surfaces, but
/// each surface must retain the producer's one allocation. Structural equality
/// remains the movement rule; pointer identity is only the ownership proof.
#[test]
fn world_facts_and_product_memo_share_their_immutable_payloads() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("shared_product_payloads.fz".to_string()),
        "fn add1(x), do: x + 1\nfn main(), do: add1(41)".to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let mut driver = pull_root_backend_driver_for_test(&tel, &mut world, root);

    let root_key = ProductKey::RootBackendProduct(root);
    let root_answer = match driver.session().memo().get(&root_key) {
        Some(ProductValue::RootBackendProduct(answer)) => answer.clone(),
        other => panic!("expected shared root backend answer, got {other:?}"),
    };
    let session = driver.session();
    let memo = session.memo();
    for (executable, materialized) in memo.materialized_executables() {
        let runtime_demand = world
            .runtime_demand(executable)
            .expect("materialized executable must read a RuntimeDemand fact");
        assert!(
            Rc::ptr_eq(&materialized.runtime_demand, runtime_demand),
            "materialization must retain the producer's RuntimeDemand allocation",
        );
    }
    for (executable, abi) in memo.abi_executables() {
        let runtime_demand = world
            .runtime_demand(executable)
            .expect("ABI executable must read a RuntimeDemand fact");
        assert!(Rc::ptr_eq(&abi.materialized.runtime_demand, runtime_demand));
        assert!(Rc::ptr_eq(
            &abi.materialized,
            memo.materialized_executable(executable)
                .expect("memoized materialized input")
        ));
        for positioned in abi.callable_owners.iter() {
            match memo.get(&ProductKey::CallableConstruction(positioned.position.clone())) {
                Some(ProductValue::CallableConstruction(owner)) => {
                    assert!(
                        Rc::ptr_eq(&positioned.owner, owner),
                        "ABI owner at {:?} must retain its memo allocation (equal={})",
                        positioned.position,
                        positioned.owner == *owner,
                    );
                }
                other => panic!("expected memoized callable owner, got {other:?}"),
            }
        }
    }
    for (executable, backend) in memo.backend_executables() {
        let runtime_demand = world
            .runtime_demand(executable)
            .expect("backend executable must read a RuntimeDemand fact");
        assert!(Rc::ptr_eq(&backend.abi.materialized.runtime_demand, runtime_demand));
        assert!(Rc::ptr_eq(
            &backend.abi,
            memo.abi_executable(executable).expect("memoized ABI input")
        ));
    }
    for executable in &root_answer.program.executables {
        let runtime_demand = world
            .runtime_demand(&executable.key)
            .expect("packaged executable must read a RuntimeDemand fact");
        assert!(
            Rc::ptr_eq(&executable.runtime_demand, runtime_demand),
            "backend packaging must retain the producer's RuntimeDemand allocation",
        );
    }

    drop(session);
    let cached = driver.pull(&mut WorldProductProducers::new(&mut world, &tel), root_key);
    match cached {
        PullOutcome::Produced(ProductValue::RootBackendProduct(answer)) => {
            assert!(Rc::ptr_eq(&answer.transport, &root_answer.transport));
            assert!(Rc::ptr_eq(&answer.program, &root_answer.program));
        }
        other => panic!("settled root product should be a cache hit, got {other:?}"),
    }

    driver.finish_session();
}

/// One recursion component publishes ONE return contract.
///
/// Two functions that call each other in return position are two views of one
/// calling convention: each returns the other's result, so their published
/// returns and the payloads read for those calls all describe the same value.
/// When they agree the artifact makes the call a TAIL call; when they disagree
/// the caller re-materializes the result on every step of the recursion, which
/// on a 30,000-element split cost about a quarter of the runtime (fz-kdt.97).
///
/// They can only disagree by deriving their forms independently, and the
/// recursion cut is what invites it: the cut member sees only the arms beside
/// the cut, while the member whose edge survived joins that form with its own
/// other arms and, finding no agreement, invents a whole-value one. Neither is
/// wrong on its own; the two together are.
///
/// The invariant binds exactly where it is decidable from the artifact: a call
/// in return position whose callee can call back to the caller, and whose
/// callee publishes the caller's own return type. Same type, same convention,
/// one contract.
///
/// Assumed and so far unconstructible: equal return DEMAND across the bound
/// pair. Two component members with equal type but different demand (possible
/// only when every caller of one member is strictly partial, since
/// `ShapeDemand::join` collapses Whole with anything to Whole) would derive
/// two legitimately different contracts; if such a fixture ever exists, this
/// assertion needs a demand-equality filter, not a weakening.
#[test]
fn compiler2_one_recursion_component_publishes_one_return_contract() {
    let source = include_str!("../../fixtures2/00420_enum_take_drop_split.fz");
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some("one_return_contract.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (program, driver) =
        super::product_drive::drive_root_backend_product::<_, PanicProductDriveError>(&mut world, &tel, root)
            .expect("panic-based ProductDriveError never returns Err");
    driver.finish_session();

    let reaches = direct_call_reachability(&program);
    let mut checked = 0;
    let mut demoted = Vec::new();
    for (caller, executable) in program.executables.iter().enumerate() {
        let super::artifact::BackendBody::Clauses { entries, .. } = &executable.body else {
            continue;
        };
        for entry in entries {
            let super::artifact::BackendTail::DirectCall {
                target, dest, callsite, ..
            } = &entry.tail
            else {
                continue;
            };
            let super::body::ControlDestination::Return = dest else {
                continue;
            };
            for (callee, return_flow) in return_flow_arms(target) {
                if !reaches[callee].contains(&caller) {
                    continue;
                }
                if program.executables[callee].return_ty != executable.return_ty {
                    continue;
                }
                checked += 1;
                let super::artifact::BackendReturnFlow::Continue { .. } = return_flow else {
                    continue;
                };
                demoted.push(format!(
                    "{}#{} {:?} -> {}#{}",
                    world.function_ref(executable.key.activation.function).name,
                    caller,
                    callsite,
                    world
                        .function_ref(program.executables[callee].key.activation.function)
                        .name,
                    callee,
                ));
            }
        }
    }

    assert!(
        checked > 0,
        "the fixture should return through mutually recursive direct calls for this invariant to bind",
    );
    demoted.sort();
    assert_eq!(
        demoted,
        Vec::<String>::new(),
        "a call returning into its own recursion component must be a tail call: \
         every member of the component derives the same return contract",
    );
}

/// Which executables each executable can reach through packaged call edges --
/// the artifact's own call graph, read back off the program it published.
fn direct_call_reachability(program: &super::artifact::BackendProgram) -> Vec<BTreeSet<usize>> {
    let mut edges = vec![BTreeSet::new(); program.executables.len()];
    for (caller, executable) in program.executables.iter().enumerate() {
        let super::artifact::BackendBody::Clauses { entries, .. } = &executable.body else {
            continue;
        };
        for entry in entries {
            let target = match &entry.tail {
                super::artifact::BackendTail::DirectCall { target, .. } => target,
                _ => continue,
            };
            edges[caller].extend(target.local_callees().into_iter().copied());
        }
    }
    let mut reaches = edges.clone();
    let mut growing = true;
    while growing {
        growing = false;
        for caller in 0..reaches.len() {
            let reached = reaches[caller]
                .iter()
                .flat_map(|callee| reaches[*callee].iter().copied())
                .collect::<Vec<_>>();
            for callee in reached {
                growing |= reaches[caller].insert(callee);
            }
        }
    }
    reaches
}

/// The callee and return flow of every arm one packaged call edge can take.
fn return_flow_arms(
    target: &super::artifact::CallEdge<usize, super::artifact::BackendReturnFlow>,
) -> Vec<(usize, &super::artifact::BackendReturnFlow)> {
    match target {
        super::artifact::CallEdge::Direct(direct) => direct
            .callee
            .copied_local()
            .map(|callee| (callee, &direct.return_flow))
            .into_iter()
            .collect(),
        super::artifact::CallEdge::Dispatch(dispatch) => dispatch
            .arms
            .iter()
            .filter_map(|arm| Some((arm.callee.copied_local()?, &arm.return_flow)))
            .collect(),
        super::artifact::CallEdge::Indirect(_) => Vec::new(),
    }
}

#[test]
fn positioned_callable_owners_have_observable_obligations() {
    for (name, source) in [
        (
            "take_drop",
            include_str!("../../fixtures2/00420_enum_take_drop_split.fz"),
        ),
        ("scalar", "fn main(), do: 42"),
    ] {
        let tel = ConfiguredTelemetry::new();
        let evaluated = Rc::new(RefCell::new(Vec::new()));
        let observed = Rc::clone(&evaluated);
        tel.attach_raw_event3::<ProductKey, super::pull::ProductRequestId, PullOutcome, _>(
            &["fz", "compiler2", "pull", "product", "evaluated"],
            move |_, _, _, key, _, _| observed.borrow_mut().push(key.clone()),
        );
        let mut world = World::new();
        world.submit_code(Some(format!("{name}.fz")), source.into());
        let root = world.submit_root(None, "main".into(), 0, ExecutableNeed::Value);
        let driver = pull_root_backend_driver_for_test(&tel, &mut world, root);
        let session = driver.session();
        let mut classes = BTreeMap::new();
        for (key, abi) in session.memo().abi_executables() {
            for positioned in &abi.callable_owners {
                let owner = &positioned.owner;
                let class = if owner.construction.is_some() {
                    "construction"
                } else if !owner.callable_facts.is_empty() || !owner.boundary_facts.is_empty() {
                    "metadata"
                } else {
                    "empty"
                };
                let physical = !world.layout_physical_lanes(owner.layout).is_empty();
                *classes.entry((class, physical)).or_insert(0usize) += 1;
                assert!(
                    session
                        .memo()
                        .product_dependencies(&ProductKey::AbiExecutable(key.clone()))
                        .expect("ABI dependency inventory")
                        .contains_key(&ProductKey::CallableConstruction(positioned.position.clone())),
                    "the final owner has its exact ABI consumer"
                );
            }
        }
        assert!(
            !classes.keys().any(|(class, _)| *class == "empty"),
            "every retained owner carries construction or callable/boundary facts"
        );
        if name == "scalar" {
            assert!(
                !evaluated
                    .borrow()
                    .iter()
                    .any(|key| matches!(key, ProductKey::CallableConstruction(_))),
                "physical scalar layouts perform no callable-construction producer work"
            );
        } else {
            assert_eq!(
                classes,
                BTreeMap::from([
                    (("construction", true), 38),
                    (("metadata", false), 125),
                    (("metadata", true), 302)
                ]),
                "the pruned owner population preserves every nonempty baseline obligation"
            );
        }
    }
}

#[test]
fn ignored_forwarded_input_requests_no_positioned_products() {
    let tel = ConfiguredTelemetry::new();
    let evaluated = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&evaluated);
    tel.attach_raw_event3::<ProductKey, super::pull::ProductRequestId, PullOutcome, _>(
        &["fz", "compiler2", "pull", "product", "evaluated"],
        move |_, _, _, key, _, _| observed.borrow_mut().push(key.clone()),
    );
    let mut world = World::new();
    world.submit_code(
        Some("ignored_forwarded_input.fz".into()),
        "fn discard(_), do: 0\nfn forward(x), do: discard(x)\nfn main(), do: forward(42)".into(),
    );
    let root = world.submit_root(None, "main".into(), 0, ExecutableNeed::Value);
    let driver = pull_root_backend_driver_for_test(&tel, &mut world, root);
    let session = driver.session();
    let (executable, abi) = session
        .memo()
        .abi_executables()
        .find(|(key, _)| function_is(&world, key.activation.function, "forward", 1))
        .expect("reached forward executable");
    let demand = world.runtime_demand(executable).expect("settled demand authority");
    assert!(
        demand.input_demands[0].is_ignore(),
        "neither physical nor callable input is demanded"
    );
    let super::body::LoweredBody::Clauses { clauses, .. } = &abi.materialized.body else {
        panic!("ordinary forward body")
    };
    for clause in clauses {
        assert!(
            !demand.callable_flows.contains_key(&clause.params[0]),
            "ignored scalar is not a callable flow"
        );
    }
    let position = TransportPosition::ExecutableInput {
        executable: executable_symbol_for(&world, executable),
        semantic_index: 0,
    };
    let forbidden = [
        ProductKey::TransportShape(position.clone()),
        ProductKey::CallableConstruction(position.clone()),
    ];
    assert_eq!(
        evaluated
            .borrow()
            .iter()
            .filter(|key| forbidden.contains(key))
            .collect::<Vec<_>>(),
        Vec::<&ProductKey>::new(),
        "an authoritative absent input has no positioned producer work"
    );
    assert!(
        !abi.transport.input_positions.contains(&position),
        "ABI has no absent input consumer"
    );
    assert!(
        !abi.callable_owners.iter().any(|owner| owner.position == position),
        "ABI has no absent callable owner"
    );
}

#[test]
fn compiler2_unused_capture_layout_reaches_backend_wrapper() {
    let source = r#"
fn discard(_), do: 0

fn make(n) do
  if true do
    fn (x) -> if discard(n) == 0, do: x, else: x end
  else
    fn (x) -> if discard(n) == 0, do: x, else: x end
  end
end
fn main(), do: make(41).(1)
"#;
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some("unused_capture_construction.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (program, driver) =
        super::product_drive::drive_root_backend_product::<_, PanicProductDriveError>(&mut world, &tel, root)
            .expect("panic-based ProductDriveError never returns Err");
    driver.finish_session();
    let session = &*driver.session();
    let owners = callable_owners_for_test(session);
    let construction = owners
        .iter()
        .filter_map(|owner| owner.construction.as_ref())
        .find(|construction| {
            world
                .callable(construction.callable)
                .function
                .is_some_and(|function| world.function_ref(function).name.starts_with("#lambda:"))
                && construction.captures.len() == 1
        })
        .expect("ignored-input lambda should retain its lexical capture fact");
    let capture = &construction.captures[0];
    assert_eq!(
        capture.layout.carrier,
        TransportCarrier::Absent,
        "a capture used only by an ignored callee input should have no physical carrier",
    );
    let TransportPosition::Value {
        executable: capture_executable,
        value,
    } = &capture.source
    else {
        panic!("lexical capture has a positioned source value")
    };
    let (_, capture_abi) = session
        .memo()
        .abi_executables()
        .find(|(key, _)| executable_symbol_for(&world, key) == *capture_executable)
        .expect("capture producer ABI");
    assert!(
        capture_abi.transport.value_positions.contains(&capture.source),
        "the lexical source owns capture metadata directly, independent of parameter transport"
    );
    assert!(capture_abi.value_layouts[value].reprs.is_empty());
    for (key, abi) in session.memo().abi_executables() {
        for (semantic_index, demand) in world.runtime_demand(key).unwrap().input_demands.iter().enumerate() {
            if demand.is_ignore() {
                assert!(
                    !abi.transport
                        .input_positions
                        .contains(&TransportPosition::ExecutableInput {
                            executable: executable_symbol_for(&world, key),
                            semantic_index,
                        }),
                    "lexical metadata must not retain an ignored input ABI position"
                );
            }
        }
    }
    let wrapper = program
        .construction_wrappers
        .iter()
        .find(|wrapper| wrapper.callable == construction.callable)
        .expect("ignored-input lambda should retain its backend wrapper");
    assert_eq!(wrapper.captures[0].layout.carrier, TransportCarrier::Absent);
    for member in &wrapper.members {
        let semantic_index = member.capture_semantic_inputs[0];
        assert!(
            member
                .target_inputs
                .iter()
                .find(|input| input.semantic_index == semantic_index)
                .is_none_or(|input| input.layout.reprs.is_empty()),
            "an absent construction capture must agree with every member target capture ABI",
        );
    }
}

#[test]
fn compiler2_transport_plan_resolves_enum_take_reducer_input_boundary_from_source_publication() {
    let source = "fn main() do\n  xs = [1, 2, 3, 4, 5]\n  dbg(Enum.take(xs, 3))\nend\n";

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_enum_take_reducer_input_boundary_resolution.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let (callables, boundaries) = callable_owner_facts_for_test(session);
    let reducer_input_boundaries = plan
        .position_layouts
        .iter()
        .filter_map(|(position, layout)| {
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
            let ShapeDescr::Callable(callable) = shape_descr(&world, layout.structural) else {
                return None;
            };
            let facts = callables
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
            let facts = boundaries
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_enum_take_unpublished_multi_surface_callables.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let (callables, boundaries) = callable_owner_facts_for_test(session);
    let unpublished = plan
        .position_layouts
        .iter()
        .filter_map(|(position, layout)| {
            let ShapeDescr::Callable(callable) = shape_descr(&world, layout.structural) else {
                return None;
            };
            let facts = callables.get(callable)?;
            if facts.boundary_ids.len() <= 1 {
                return None;
            }
            let publications = boundaries
                .iter()
                .filter_map(|(boundary, facts)| facts.publications.contains(position).then_some(*boundary))
                .collect::<Vec<_>>();
            if !publications.is_empty() {
                return None;
            }
            let function_name = world
                .function_ref(position.executable().activation.function)
                .name
                .clone();
            function_name.contains("reduce_while").then_some((
                function_name,
                position.clone(),
                layout.structural,
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
fn compiler2_direct_callable_owners_preserve_shared_callable_resolutions() {
    let source = "fn make(seed) do\n  dbg(seed)\n  fn (x) -> x end\nend\nfn apply_int(f), do: f.(1)\nfn apply_atom(f), do: f.(:ok)\nfn main(), do: {apply_int(make(1)), apply_atom(make(:ok))}\n";
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("shared_closure_owner_resolutions.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let answers = root_backend_answer_for_test(session)
        .transport
        .callable_owners
        .iter()
        .filter(|positioned| {
            matches!(positioned.position, TransportPosition::Value { .. })
                && world
                    .function_ref(positioned.position.executable().activation.function)
                    .name
                    == "make"
                && !positioned.owner.callable_facts.is_empty()
        })
        .collect::<Vec<_>>();
    let [left, right] = answers.as_slice() else {
        panic!("the two specialized make/1 activations should own two callable answers: {answers:#?}")
    };
    assert!(left.owner.construction.is_none());
    assert!(right.owner.construction.is_none());
    assert_ne!(left.position, right.position);
    let left_callables = left.owner.callable_facts.keys().copied().collect::<Vec<_>>();
    let [left_callable] = left_callables.as_slice() else {
        panic!("the left make/1 specialization should own one direct callable identity: {left:#?}")
    };
    let right_callables = right.owner.callable_facts.keys().copied().collect::<Vec<_>>();
    let [right_callable] = right_callables.as_slice() else {
        panic!("the right make/1 specialization should own one direct callable identity: {right:#?}")
    };
    assert_eq!(left_callable, right_callable);
    let left_facts = &left.owner.callable_facts[left_callable];
    let right_facts = &right.owner.callable_facts[right_callable];
    assert_ne!(left_facts.resolutions, right_facts.resolutions);
    assert_ne!(left_facts.direct_surfaces, right_facts.direct_surfaces);
    assert_eq!(left.owner.layout, right.owner.layout);
}

#[test]
fn compiler2_callable_construction_owners_preserve_shared_boundary_publications() {
    let source =
        "fn inc(x), do: x + 1\nfn left(), do: &inc/1\nfn right(), do: &inc/1\nfn main(), do: {left(), right()}\n";
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("shared_function_ref_owner_publications.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2));
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let answers = ["left", "right"].map(|name| {
        let position = TransportPosition::ExecutableReturn {
            executable: executable_for(&world, session, name, 0),
        };
        let answer = match session.memo().get(&ProductKey::CallableConstruction(position.clone())) {
            Some(ProductValue::CallableConstruction(answer)) => answer.as_ref(),
            value => panic!("{name}/0 should own its exact return answer: {value:?}"),
        };
        (position, answer)
    });
    let [(left_position, left), (right_position, right)] = answers;
    assert!(left.construction.is_none());
    assert!(right.construction.is_none());
    let left_callable = *left
        .callable_facts
        .keys()
        .find(|callable| world.callable(**callable).function.is_some())
        .expect("left/0 return should refine the inc/1 callable identity");
    let right_callable = *right
        .callable_facts
        .keys()
        .find(|callable| world.callable(**callable).function.is_some())
        .expect("right/0 return should refine the inc/1 callable identity");
    assert_eq!(left_callable, right_callable);
    let [left_boundary] = left.callable_facts[&left_callable].boundary_ids.as_ref() else {
        panic!("left/0 should publish one boundary")
    };
    let [right_boundary] = right.callable_facts[&right_callable].boundary_ids.as_ref() else {
        panic!("right/0 should publish one boundary")
    };
    assert_eq!(left_boundary, right_boundary);
    assert!(left.boundary_facts[left_boundary].publications.contains(&left_position));
    assert!(
        !left.boundary_facts[left_boundary]
            .publications
            .contains(&right_position)
    );
    assert!(
        right.boundary_facts[right_boundary]
            .publications
            .contains(&right_position)
    );
    assert!(
        !right.boundary_facts[right_boundary]
            .publications
            .contains(&left_position)
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
    let mut world = World::new();
    world.submit_code(
        Some("transport_direct_reducer_capture_prefix_shape.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let (callables, _) = callable_owner_facts_for_test(session);
    let reducer = callables
        .iter()
        .find_map(|(callable, facts)| {
            let descr = world.callable(*callable);
            let [capture_layout] = descr.capture_layouts.as_ref() else {
                return None;
            };
            let ShapeDescr::Callable(captured) = shape_descr(&world, capture_layout.structural) else {
                return None;
            };
            let reducer_shape = plan.position_layouts.iter().find_map(|(_, layout)| {
                matches!(shape_descr(&world, layout.structural), ShapeDescr::Callable(candidate) if candidate == callable)
                    .then_some(layout.structural)
            })?;
            (!facts.direct_surfaces.is_empty()).then_some((
                reducer_shape,
                capture_layout.structural,
                *captured,
                facts.resolutions.clone(),
            ))
        })
        .unwrap_or_else(|| panic!("the direct reducer should capture the predicate as a callable shape"));
    let (_reducer_shape, _predicate_shape, predicate_callable, reducer_resolutions) = reducer;
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
            &plan,
            &TransportPosition::ExecutableInput {
                executable: reduce_plain.clone(),
                semantic_index: 2,
            },
        );
        assert!(matches!(
            shape_descr(&world, reduce_plain_reducer_input),
            ShapeDescr::Callable(_)
        ));
    }
    assert!(
        callable_capture_lanes(&world, predicate_callable).is_empty(),
        "the predicate lambda captures nothing, so the reducer capture-prefix input must carry no payload lanes"
    );
    for resolution in reducer_resolutions {
        let position = TransportPosition::ExecutableInput {
            executable: resolution,
            semantic_index: 0,
        };
        let capture_input = plan.shape_at(&position).expect("capture input shape");
        assert!(matches!(shape_descr(&world, capture_input), ShapeDescr::Callable(_)));
    }
}

#[test]
fn compiler2_escaped_callable_uses_its_exact_target_to_project_branded_capture_demand() {
    let source = r#"
fn main() do
  predicate = fn x -> x > 2 end
  fn (entry, acc) ->
    if predicate.(entry), do: acc + 1, else: acc
  end
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some("escaped_branded_capture.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let session = &*driver.session();
    let owner = super::jobs::backend::executable_key_for_symbol(root, &plan.entry);
    let owner_demand = world.runtime_demand(&owner).expect("main demand");
    let (value, flow) = owner_demand
        .callable_flows
        .iter()
        .find(|(_, flow)| flow.captures.len() == 1 && !flow.first_class_edges.is_empty())
        .expect("the escaped outer closure should have one exact construction target");
    assert!(flow.direct_edges.is_empty());
    assert!(
        owner_demand
            .value_demands
            .get(value)
            .expect("escaped outer demand")
            .callable
            .targets
            .is_empty(),
        "the escaped-only path must prove construction-fact correlation rather than the direct-target path",
    );
    let target_key = CallableConstructionTargetKey {
        owner: owner.clone(),
        value: *value,
        surface: flow.first_class_edges[0].surface.clone(),
    };
    assert!(
        world
            .job_reads(&Job::DeriveRuntimeDemand(owner))
            .contains(&FactUse::current(FactKey::CallableConstructionTarget(target_key))),
        "the owner formula must retain the exact construction-target dependency used to select the row",
    );
    let (callables, _) = callable_owner_facts_for_test(session);
    let captured_shapes = callables
        .keys()
        .filter_map(|callable| {
            let descr = world.callable(*callable);
            let [capture] = descr.capture_layouts.as_ref() else {
                return None;
            };
            Some(capture.structural)
        })
        .collect::<Vec<_>>();

    assert!(
        captured_shapes
            .iter()
            .any(|shape| matches!(shape_descr(&world, *shape), ShapeDescr::Callable(_))),
        "the escaped outer callable must carry its invoked predicate capture as a callable: {captured_shapes:?}",
    );
}

#[test]
fn compiler2_transport_plan_projects_enum_reduce_bridge_callable_flow_by_producer_identity_over_range() {
    let source = include_str!("../../fixtures2/behavior/fz_f98_range_reduce_scalar.fz");

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("transport_fz_f98_range_reduce_scalar_contract.fz".to_string()),
        source.to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
    let (callables, _) = callable_owner_facts_for_test(session);
    let runtime_demands = runtime_demands_for_frontier(&world, session);
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
        let matching_callables = callables
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
            callables
        );
        let (callable, facts) = matching_callables[0];
        assert_callable_facts_match_upstream_flow(&mut world, session, *callable, flow);
        assert!(
            facts.boundary_ids.len() <= flow.first_class_surfaces.len(),
            "direct reducer use must not invent extra first-class boundaries: flow={flow:?}; facts={facts:?}"
        );
    }
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
    let mut world = World::new();
    world.submit_code(
        Some("range_int_elements.fz".to_string()),
        "fn main() do\n  dbg(Enum.to_list(1..3))\nend\n".to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let _ = &plan;
    let session = &*driver.session();
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

fn executable_symbol_for(world: &World, key: &ExecutableKey) -> ExecutableSymbol {
    ExecutableSymbol {
        activation: ActivationSymbol {
            function: key.activation.function,
            arrow: key.activation.arrow,
            input: key.activation.inputs(world.types()).into_boxed_slice(),
        },
        need: key.need,
    }
}

fn executable_membership(world: &World, session: &PullSession) -> Vec<ExecutableSymbol> {
    session
        .demanded_executables()
        .iter()
        .map(|key| executable_symbol_for(world, key))
        .collect()
}

fn executable_for(world: &World, session: &PullSession, name: &str, arity: usize) -> ExecutableSymbol {
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

fn assert_entry_dispatch_control(
    source_name: &str,
    source: &str,
    function_name: &str,
    expected_clause_count: usize,
    expected_fail_reachable: bool,
) {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some(source_name.to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
    let driver = pull_root_backend_driver_for_test(&tel, &mut world, root);
    let session = driver.session();
    let (executable, materialized) = session
        .memo()
        .materialized_executables()
        .find(|(executable, _)| function_is(&world, executable.activation.function, function_name, 1))
        .unwrap_or_else(|| panic!("{function_name}/1 should materialize"));
    let reachability = &world
        .activation_analysis(&executable.activation)
        .unwrap_or_else(|| panic!("{function_name}/1 should have settled semantic analysis"))
        .entry_reachability;

    assert_eq!(reachability.clauses().len(), expected_clause_count);
    assert_eq!(reachability.fail_reachable(), expected_fail_reachable);
    assert_eq!(
        materialized.entry_dispatch.is_none(),
        reachability.is_direct_clause(),
        "runtime dispatch should be omitted exactly for a proven direct clause",
    );
}

fn runtime_demands_for_frontier(
    world: &World,
    session: &PullSession,
) -> HashMap<ExecutableKey, ExecutableRuntimeDemand> {
    session
        .demanded_executables()
        .iter()
        .filter_map(|executable| {
            world
                .runtime_demand(executable)
                .map(|demand| (executable.clone(), demand.as_ref().clone()))
        })
        .collect()
}

fn runtime_demand_fact_for_function(
    world: &World,
    session: &PullSession,
    name: &str,
    arity: usize,
) -> ExecutableRuntimeDemand {
    session
        .demanded_executables()
        .iter()
        .find(|executable| function_is(world, executable.activation.function, name, arity))
        .and_then(|executable| world.runtime_demand(executable))
        .map(|demand| demand.as_ref().clone())
        .unwrap_or_else(|| panic!("RuntimeDemand fact for {name}/{arity}"))
}

fn has_callable_flow(demand: &ExecutableRuntimeDemand, predicate: impl Fn(&CallableFlowFact) -> bool) -> bool {
    demand.callable_flows.values().any(predicate)
}

fn submit_enum_reduce_operator_ref_root(
    world: &mut World,
    _tel: &ConfiguredTelemetry,
    source_name: &str,
) -> super::RootId {
    world.submit_code(
        Some(source_name.to_string()),
        ENUM_REDUCE_OPERATOR_REF_SOURCE.to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, ExecutableNeed::TupleFields(2))
}

fn pull_transport_plan_for_test<'a>(
    tel: &'a ConfiguredTelemetry,
    world: &mut World,
    root: super::RootId,
) -> (ProductDriver<'a, ConfiguredTelemetry>, MaterializedTransportPlan) {
    let driver = pull_root_backend_driver_for_test(tel, world, root);
    let plan = (*root_backend_answer_for_test(&driver.session()).transport).clone();
    (driver, plan)
}

fn root_backend_answer_for_test(session: &super::pull::PullSession) -> &super::artifact::RootBackendProductAnswer {
    match session.memo().get(&ProductKey::RootBackendProduct(session.root())) {
        Some(ProductValue::RootBackendProduct(answer)) => answer,
        Some(other) => panic!("root backend product produced unexpected value {other:?}"),
        None => panic!("root backend product should be memoized"),
    }
}

fn callable_owners_for_test(
    session: &super::pull::PullSession,
) -> Vec<std::rc::Rc<super::transport::CallableConstructionOwner>> {
    root_backend_answer_for_test(session)
        .transport
        .callable_owners
        .iter()
        .map(|positioned| positioned.owner.clone())
        .collect()
}

fn callable_owner_facts_for_test(
    session: &super::pull::PullSession,
) -> (
    HashMap<super::transport::CallableId, super::transport::CallableFacts>,
    HashMap<super::transport::BoundaryId, super::transport::BoundaryFacts>,
) {
    let transport = &root_backend_answer_for_test(session).transport;
    (transport.callable_facts.clone(), transport.boundary_facts.clone())
}

fn pull_root_backend_driver_for_test<'a>(
    tel: &'a ConfiguredTelemetry,
    world: &mut World,
    root: super::RootId,
) -> ProductDriver<'a, ConfiguredTelemetry> {
    let (_, driver) = super::product_drive::drive_root_backend_product::<_, PanicProductDriveError>(world, tel, root)
        .expect("panic-based ProductDriveError never returns Err");
    driver.finish_session();
    driver
}

/// Panics on each `ProductDriveError` hook instead of returning a value,
/// so this file keeps its old fail-loudly ergonomics while sharing the one
/// production pull-drive loop. No test asserts on the panic text.
#[derive(Debug)]
struct PanicProductDriveError;

impl super::product_drive::ProductDriveError for PanicProductDriveError {
    fn dependency_failed<T: crate::telemetry::Telemetry>(
        _world: &World,
        _tel: &T,
        address: super::drive::ProductAddress,
        source: super::scheduler::FatalError,
    ) -> Self {
        panic!("product dependency {address:?} failed: {source:?}");
    }

    fn product_failed<T: crate::telemetry::Telemetry>(
        _world: &World,
        _tel: &T,
        root: super::RootId,
        product: &ProductKey,
        failure: super::pull::ProductFailure,
    ) -> Self {
        panic!("root {} product {product:?} failed: {failure:?}", root.as_u32());
    }

    fn job_failed<T: crate::telemetry::Telemetry>(
        _world: &World,
        _tel: &T,
        root: super::RootId,
        fact: &FactUse<FactKey>,
        job: &Job,
        source: super::scheduler::FatalError,
    ) -> Self {
        panic!(
            "root {} job {job:?} failed producing {fact:?}: {source:?}",
            root.as_u32()
        );
    }

    fn no_ready_producer<T: crate::telemetry::Telemetry>(
        _world: &World,
        _tel: &T,
        root: super::RootId,
        fact: &FactUse<FactKey>,
    ) -> Self {
        panic!("root {} no ready producer for {fact:?}", root.as_u32());
    }

    fn fact_wait_budget_exceeded<T: crate::telemetry::Telemetry>(
        _world: &World,
        _tel: &T,
        root: super::RootId,
        fact: &FactUse<FactKey>,
    ) -> Self {
        panic!("root {} fact-wait budget exceeded for {fact:?}", root.as_u32());
    }

    fn did_not_settle<T: crate::telemetry::Telemetry>(
        _world: &World,
        _tel: &T,
        root: super::RootId,
        last_wait: Option<(ProductKey, Vec<PullWait>)>,
    ) -> Self {
        panic!(
            "root {} product did not settle; last wait: {last_wait:?}",
            root.as_u32()
        );
    }
}

/// Pulls an arbitrary `ProductKey` to a settled `ProductValue`, expanding any
/// `PullWait::Fact` through the shared `product_drive::drive_product_fact_wait`.
/// These tests also request transport shapes, runtime demands, and
/// materialized executables, so only the inner fact-wait loop is shared.
fn pull_product_until_produced_with_fact_waits(
    driver: &mut ProductDriver<'_, ConfiguredTelemetry>,
    world: &mut World,
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
            let mut producers = WorldProductProducers::new(world, driver.telemetry());
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
                            let tel = driver.telemetry();
                            let producer_pokes =
                                super::product_drive::drive_product_fact_wait::<_, PanicProductDriveError>(
                                    world,
                                    tel,
                                    root,
                                    driver,
                                    fact,
                                    super::product_drive::PRODUCT_DRIVE_BUDGET,
                                )
                                .expect("panic-based ProductDriveError never returns Err");
                            driver.session_mut().record_producer_pokes(producer_pokes);
                        }
                    }
                }
            }
            PullOutcome::Failed(failure) => panic!("{message}: product {current:?} failed: {failure:?}"),
        }
    }
    panic!("{message}: product {key:?} did not settle; last wait: {last_wait:?}");
}

fn materialized_call_edge_callees(edge: &super::artifact::MaterializedCallEdge) -> Vec<&ExecutableKey> {
    match &edge.target {
        super::artifact::CallEdge::Direct(direct) => direct.callee.local().into_iter().collect(),
        super::artifact::CallEdge::Dispatch(dispatch) => {
            dispatch.arms.iter().filter_map(|arm| arm.callee.local()).collect()
        }
        super::artifact::CallEdge::Indirect { .. } => Vec::new(),
    }
}

fn abi_ready_call_edge_callees(edge: &super::artifact::AbiReadyCallEdge) -> Vec<&ExecutableKey> {
    match &edge.target {
        super::artifact::CallEdge::Direct(direct) => direct.callee.local().into_iter().collect(),
        super::artifact::CallEdge::Dispatch(dispatch) => {
            dispatch.arms.iter().filter_map(|arm| arm.callee.local()).collect()
        }
        super::artifact::CallEdge::Indirect { .. } => Vec::new(),
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
        super::artifact::CallEdge::Indirect { .. } => Vec::new(),
    }
}

fn upstream_callable_flow_for_producer(
    world: &World,
    session: &PullSession,
    function: super::FunctionId,
) -> CallableFlowFact {
    runtime_demands_for_frontier(world, session)
        .values()
        .flat_map(|demand| demand.callable_flows.values())
        .find(|flow| flow.function == function)
        .cloned()
        .unwrap_or_else(|| panic!("upstream callable flow for producer {function:?}"))
}

fn upstream_input_demand_for_function(
    world: &World,
    session: &PullSession,
    name: &str,
    arity: usize,
    semantic_index: usize,
) -> RuntimeDemand {
    runtime_demands_for_frontier(world, session)
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
    world: &World,
    session: &PullSession,
    callable: super::transport::CallableId,
    demand: RuntimeDemand,
) {
    if demand.callable.is_empty() {
        panic!("expected upstream callable demand for generic callable shape, got {demand:?}")
    }
    let demand = demand.callable;
    let descr = world.callable(callable);
    // A boxed first-class callable's VALUE shape is a capture-free callable
    // identity with `function: None`. The invocation contract (the observed
    // surfaces) projects into the published BOUNDARIES, not the value's identity
    // — asserted below.
    assert_eq!(descr.function, None, "an opaque callable value is boxed: function None");
    assert_eq!(
        callable_capture_lanes(world, callable).len(),
        0,
        "a generic callable identity must not duplicate its external carrier as a capture lane: {descr:?}"
    );
    let (callables, _) = callable_owner_facts_for_test(session);
    let facts = callables
        .get(&callable)
        .unwrap_or_else(|| panic!("callable facts should exist for generic callable {callable:?}"));
    assert_eq!(
        facts.boundary_ids.len(),
        usize::from(demand.opaque || demand.escape) * demand.resolved.len(),
        "generic callable boundaries should be published from upstream callable surfaces"
    );
}

fn assert_callable_facts_match_upstream_flow(
    world: &mut World,
    session: &PullSession,
    callable: super::transport::CallableId,
    flow: &CallableFlowFact,
) {
    let (callables, boundaries) = callable_owner_facts_for_test(session);
    let facts = callables
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
    assert_boundary_resolutions_match_upstream_flow(world, &boundaries, facts, flow);
}

fn flow_resolution_symbols(world: &World, flow: &CallableFlowFact) -> Vec<ExecutableSymbol> {
    let mut symbols = flow
        .resolutions
        .iter()
        .map(|resolution| ExecutableSymbol {
            activation: ActivationSymbol {
                function: resolution.activation.function,
                arrow: resolution.activation.arrow,
                input: resolution.activation.inputs(world.types()).into_boxed_slice(),
            },
            need: resolution.need,
        })
        .collect::<Vec<_>>();
    symbols.sort_by_key(executable_symbol_test_key);
    symbols
}

fn assert_boundary_resolutions_match_upstream_flow(
    world: &mut World,
    boundaries: &HashMap<super::transport::BoundaryId, super::transport::BoundaryFacts>,
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
                    arrow: edge.resolution.activation.arrow,
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
        let surface_arg_shapes = boundary_descr
            .surface_arg_layouts
            .iter()
            .map(|layout| layout.structural)
            .collect::<Vec<_>>();
        let expected = expected_by_surface
            .iter()
            .find_map(|(surface, expected)| {
                surface_shape_matches_upstream(world, &surface_arg_shapes, surface).then_some(expected)
            })
            .unwrap_or_else(|| panic!("boundary {boundary:?} should have upstream first-class edge evidence"));
        let boundary_facts = boundaries
            .get(&boundary)
            .unwrap_or_else(|| panic!("boundary facts should exist for {boundary:?}"));
        assert_eq!(
            sorted_executable_symbols(boundary_facts.resolutions.as_ref()),
            *expected,
            "boundary facts should carry exactly the executable resolutions for their published surface"
        );
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
    world: &mut World,
    actual: &[Box<[ShapeId]>],
    expected: &BTreeSet<CallableSurface>,
) {
    assert!(
        transport_surfaces_match_upstream(world, actual, expected),
        "transport callable surfaces should exactly project upstream callable-flow inputs"
    );
}

fn transport_surfaces_match_upstream(
    world: &mut World,
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

fn surface_shape_matches_upstream(world: &mut World, actual: &[ShapeId], expected: &CallableSurface) -> bool {
    actual.len() == expected.inputs.len()
        && actual
            .iter()
            .copied()
            .zip(expected.inputs.iter().copied())
            .all(|(shape, ty)| shape_matches_surface_input_ty(world, shape, ty))
}

fn shape_matches_surface_input_ty(world: &mut World, shape: ShapeId, ty: Ty) -> bool {
    match shape_descr(world, shape).clone() {
        ShapeDescr::Lane(lane) => world.lane(lane).ty == ty,
        ShapeDescr::Tuple(items) => {
            exact_tuple_field_tys_for_surface(world, ty, items.len()).is_some_and(|field_tys| {
                items.len() == field_tys.len()
                    && items
                        .iter()
                        .copied()
                        .zip(field_tys)
                        .all(|(field, field_ty)| shape_matches_surface_input_ty(world, field.structural, field_ty))
            })
        }
        ShapeDescr::Callable(_) => world.types().arrow_result(&ty).is_some(),
        ShapeDescr::Nothing => false,
    }
}

fn exact_tuple_field_tys_for_surface(world: &mut World, ty: Ty, arity: usize) -> Option<Vec<Ty>> {
    let predicate = world.types().runtime_type_predicate(&ty);
    if predicate.tuples.arities().cofinite
        || predicate.tuples.arities().values.len() != 1
        || !predicate.tuples.arities().values.contains(&arity)
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

fn function_is(world: &World, function: super::FunctionId, name: &str, arity: usize) -> bool {
    let function_ref = world.function_ref(function);
    function_ref.name == name && function_ref.arity == arity
}

fn resume_shapes_for(
    plan: &MaterializedTransportPlan,
    executable: &super::transport::ExecutableSymbol,
) -> Vec<ShapeId> {
    plan.position_layouts
        .iter()
        .filter_map(|(position, layout)| match position {
            TransportPosition::ResumePayload {
                executable: candidate, ..
            } if candidate == executable => Some(layout.structural),
            _ => None,
        })
        .collect()
}

fn plan_shapes(plan: &MaterializedTransportPlan) -> HashMap<TransportPosition, ShapeId> {
    plan.position_layouts
        .iter()
        .map(|(position, layout)| (position.clone(), layout.structural))
        .collect()
}

fn plan_shape_at(plan: &MaterializedTransportPlan, position: &TransportPosition) -> ShapeId {
    plan.shape_at(position)
        .unwrap_or_else(|| panic!("transport position should exist: {position:?}"))
}

fn shape_descr(world: &World, shape: ShapeId) -> &ShapeDescr {
    world.shape(shape)
}

fn callable_capture_lanes(world: &World, callable: super::transport::CallableId) -> Vec<LaneId> {
    world
        .callable(callable)
        .capture_layouts
        .iter()
        .copied()
        .flat_map(|layout| world.layout_lane_ids(layout))
        .collect()
}

fn shape_leaf_lanes(world: &World, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
    world
        .shape_physical_lanes(shape)
        .into_iter()
        .map(|physical| (physical.structural, physical.lane))
        .collect()
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
    world: &World,
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
    for (position, _) in &transport.position_layouts {
        let executable = position.executable();
        assert!(
            membership.contains(executable),
            "transport position should reference only root-member executables: {position:?}"
        );
    }
    let (callables, _) = callable_owner_facts_for_test(session);
    for facts in callables.values() {
        for executable in facts.resolutions.iter() {
            assert!(
                membership.contains(executable),
                "callable facts should resolve only to root-member executables: {executable:?}"
            );
        }
    }
    for fact in transport.codegen_seam_facts.iter() {
        if let Some(executable) = fact.seam.executable() {
            assert!(
                membership.contains(executable),
                "codegen seam facts should reference only root-member executables: {:?}",
                fact.seam
            );
        }
    }
}

fn single_boundary_descr<'a>(world: &'a World, session: &PullSession) -> &'a BoundaryDescr {
    let (_, boundary_facts) = callable_owner_facts_for_test(session);
    let boundaries = boundary_facts.keys().copied().collect::<Vec<_>>();
    let [boundary] = boundaries.as_slice() else {
        panic!(
            "fixture should publish exactly one boundary contract: {:?}",
            boundary_facts
        )
    };
    world.boundary(*boundary)
}

fn boundary_with_callable_arg<'a>(world: &'a World, session: &PullSession) -> &'a BoundaryDescr {
    let (_, boundaries) = callable_owner_facts_for_test(session);
    boundaries
        .keys()
        .map(|boundary| world.boundary(*boundary))
        .find(|boundary| {
            boundary
                .surface_arg_layouts
                .iter()
                .any(|layout| matches!(shape_descr(world, layout.structural), ShapeDescr::Callable(_)))
        })
        .unwrap_or_else(|| {
            panic!(
                "fixture should publish a boundary with a callable argument: {:?}",
                boundaries
            )
        })
}

fn callable_return_for_executable(
    world: &World,
    plan: &MaterializedTransportPlan,
    executable: super::transport::ExecutableSymbol,
) -> super::transport::CallableId {
    let returned = plan_shape_at(plan, &TransportPosition::ExecutableReturn { executable });
    let ShapeDescr::Callable(callable) = shape_descr(world, returned) else {
        panic!(
            "fixture executable should return a callable shape, got {:?}",
            shape_descr(world, returned)
        )
    };
    *callable
}

fn shape_contains_callable(world: &World, shape: ShapeId) -> bool {
    match shape_descr(world, shape) {
        ShapeDescr::Callable(_) => true,
        ShapeDescr::Tuple(items) => items.iter().any(|item| shape_contains_callable(world, item.structural)),
        ShapeDescr::Nothing | ShapeDescr::Lane(_) => false,
    }
}

fn first_callable_in_shape(world: &World, shape: ShapeId) -> Option<super::transport::CallableId> {
    match shape_descr(world, shape) {
        ShapeDescr::Callable(callable) => Some(*callable),
        ShapeDescr::Tuple(items) => items
            .iter()
            .find_map(|item| first_callable_in_shape(world, item.structural)),
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

fn capture_finished_producer_pokes(tel: &ConfiguredTelemetry) -> Rc<RefCell<Option<u64>>> {
    let observed = Rc::new(RefCell::new(None));
    let sink = Rc::clone(&observed);
    tel.attach_raw_event1::<PullSession, _>(
        &["fz", "compiler2", "pull", "session", "finished"],
        move |_, _, _, session| {
            *sink.borrow_mut() = Some(session.producer_pokes());
        },
    );
    observed
}

fn assert_materialized_executable_fact_authority(world: &World, session: &PullSession) -> u64 {
    let producer_pokes = session.producer_pokes();
    let starts = world.work_start_tally();
    assert!(
        starts.blocked_waiter_expansion >= producer_pokes,
        "each product-triggered fact producer poke must be attributed to BlockedWaiterExpansion: {starts:?}",
    );
    assert_eq!(
        starts.unclassified, 0,
        "direct fact production must not start unsanctioned work"
    );
    assert_eq!(starts.root_scans, 0, "direct fact production must not scan roots");
    for (executable, _) in session.memo().materialized_executables() {
        let fact = FactKey::ExecutableFacts(executable.clone());
        let job = Job::DeriveExecutableFacts(executable.clone());
        assert!(
            world.fact_revision(&fact).is_some(),
            "demanded executable fact must publish"
        );
        assert_eq!(
            world.job_outputs(&job),
            vec![fact],
            "each demanded executable key must have exactly its one direct producer",
        );
        let runtime_fact = FactKey::RuntimeDemand(executable.clone());
        assert!(
            world.fact_is_settled(&runtime_fact),
            "each materialized executable must consume one settled RuntimeDemand fact",
        );
        assert!(
            world
                .job_outputs(&Job::DeriveRuntimeDemand(executable.clone()))
                .contains(&runtime_fact),
            "each runtime-demand value must come from its exact formula",
        );
    }
    producer_pokes
}

fn product_no_dump_interp_job_telemetry(source: &str) -> (super::RootId, JobTelemetry) {
    let tel = ConfiguredTelemetry::new();
    let jobs = JobTelemetry::new();
    jobs.install(&tel);
    let mut compiler = Compiler2::new(tel);
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
    stops: Rc<RefCell<Vec<Job>>>,
}

impl JobTelemetry {
    fn new() -> Self {
        Self {
            stops: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
        let stops = Rc::clone(&self.stops);
        telemetry.attach_raw_event2::<World, super::JobCompletion, _>(
            &["fz", "compiler2", "work_graph", "applied"],
            move |_, _, _, _, completion| stops.borrow_mut().push(completion.job.clone()),
        );
    }

    fn total_stops(&self) -> usize {
        self.stops.borrow().len()
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

/// The construction wrappers a root publishes are NUMBERED by the order of the
/// callable-owner positions they hang off, and the canonical dump prints those
/// numbers as `construction=w<N>`. Two owners belonging to sibling
/// specializations of one function agree on everything but their INPUT TYPES,
/// so the input vector is the whole of their tiebreak — and keyed on raw `Ty`
/// interner ids that tiebreak is interning order, which the agenda decides.
///
/// Measured red on `enum_take_drop_split` (fz-kdt.101): flip `Agenda::pop` to
/// `pop_back` (src/compiler2/agenda.rs:36 — build, dump, revert) and two
/// byte-identical `Enum.reduce/3#lambda@439-517/2` wrappers trade indices,
/// `w10` <-> `w11`, moving four lines of a dump whose content did not change.
///
/// The invariant: owner positions sort on fz-kdt.105's canonical, id-free
/// structural order, so the wrapper numbering says what the owners say.
#[test]
fn callable_owner_positions_break_sibling_ties_on_canonical_inputs() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("fixtures2/00420_enum_take_drop_split.fz".to_string()),
        include_str!("../../fixtures2/00420_enum_take_drop_split.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (_driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);
    let types = world.types();
    let descents = plan
        .callable_owners
        .windows(2)
        .filter(|pair| {
            let left = pair[0].position.executable();
            let right = pair[1].position.executable();
            left.activation.function == right.activation.function
        })
        .filter(|pair| {
            types
                .cmp_activation_tys(
                    &pair[0].position.executable().activation.input,
                    &pair[1].position.executable().activation.input,
                )
                .is_gt()
        })
        .count();
    assert_eq!(
        descents, 0,
        "callable-owner positions sit in interning order rather than canonical order, so \
         `construction=w<N>` numbering follows the schedule",
    );
}

/// fz-kdt.152. `Enum.reduce/3` hands its reducer down to `List.reduce_cont/3`,
/// which specializes on the accumulator: the first step is reached at the
/// literal accumulator's type and every later step at the reducer's widened
/// return. So ONE callable input reaches TWO activations of one lambda.
///
/// A transport layout is pure physics, and both activations describe the same
/// captures, so the input carries those captures — which activation a callsite
/// reaches is decided there, from the argument types it holds. Reading "more
/// than one target" as "no exact layout at all" left this input carrying
/// NOTHING while the callsite still ground a direct call to one of the two,
/// and the reducer's own capture had no lane to travel in.
///
/// The reducer arrives through the mailbox so that it is opaque: a reducer the
/// compiler can name has no surviving capture lane, and the missing lane is
/// then accidentally the right answer.
#[test]
fn compiler2_transport_plan_carries_captures_when_one_layout_covers_several_activations() {
    let source = r#"
fn main() do
  send(self(), fn (x, acc) -> acc + x end)
  reducer = receive do f -> f end
  Enum.reduce([1, 2, 3], 0, reducer)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(Some("transport_multi_activation.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let (_driver, plan) = pull_transport_plan_for_test(&tel, &mut world, root);

    let reducer_inputs = plan
        .position_layouts
        .iter()
        .filter(|(position, _)| {
            matches!(
                position,
                TransportPosition::ExecutableInput {
                    executable,
                    semantic_index: 2,
                } if world.function_ref(executable.activation.function).name == "reduce_cont"
            )
        })
        .map(|(position, layout)| (position.clone(), *layout))
        .collect::<Vec<_>>();
    assert!(
        reducer_inputs.len() > 1,
        "the accumulator split should reach several List.reduce_cont/3 activations, got {reducer_inputs:?}"
    );
    for (position, layout) in &reducer_inputs {
        let ShapeDescr::Callable(callable) = shape_descr(&world, layout.structural) else {
            panic!("a reducer input must stay callable-shaped: {position:?} {layout:?}")
        };
        let descr = world.callable(*callable);
        assert_eq!(
            callable_capture_lanes(&world, *callable).len(),
            1,
            "every activation reached by this reducer captures the mailbox callable, so the \
             input must carry its one lane: {position:?} {descr:?}"
        );
    }
}
