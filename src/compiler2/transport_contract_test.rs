use std::cell::RefCell;
use std::rc::Rc;

use super::transport::{ShapeDescr, ShapeId, TransportPlan, TransportPosition};
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
     published_arg_lanes [L_int]; published_return Value(L_int)",
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

const SEAM_FACTS: &[(&str, &str)] = &[
    ("Seam(E_pair.return)", "lanes [L_int, L_int]"),
    ("Seam(E_main.resume(pair call))", "lanes [L_int, L_int]"),
    (
        "Seam(B_pub.publish)",
        "capture [L_int]; args [L_int]; return Value(L_int)",
    ),
];

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
             published_arg_lanes [L_int]; published_return Value(L_int)"
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

fn assert_resolved(outcome: DriveOutcome<super::Job, super::FactKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
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
