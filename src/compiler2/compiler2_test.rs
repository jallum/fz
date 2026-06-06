use super::{CodeSubmission, Compiler2, World};
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

struct ContractCase<'a> {
    name: &'a str,
    source_name: &'a str,
    source_text: &'a str,
}

#[test]
fn compiler2_contract_harness_keeps_code_ingest_isolated_from_production_compiler() {
    for case in [
        ContractCase {
            name: "inline_main",
            source_name: "inline_main.fz",
            source_text: "fn main(), do: 42\n",
        },
        ContractCase {
            name: "fixture_add1",
            source_name: "fixtures/add1/input.fz",
            source_text: include_str!("../../fixtures/add1/input.fz"),
        },
    ] {
        run_contract(case);
    }
}

fn run_contract(case: ContractCase<'_>) {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new();
    let mut world = World::new();

    let submitted = compiler.submit_code(
        &mut world,
        CodeSubmission {
            name: Some(case.source_name.to_string()),
            text: case.source_text.to_string(),
        },
        &tel,
    );

    assert_eq!(world.code_count(), 1, "{} should add one code record", case.name);
    let record = world.code(submitted.code_id).expect("submitted code record");
    assert_eq!(
        record.name(),
        Some(case.source_name),
        "{} should preserve source name",
        case.name
    );
    assert_eq!(
        record.text(),
        case.source_text,
        "{} should preserve source text",
        case.name
    );

    let submitted_event = capture
        .last(&["fz", "compiler2", "code", "submitted"])
        .expect("compiler2 submitted event");
    let submitted_id = match submitted_event.measurements.get("code_id") {
        Some(Value::U64(id)) => *id,
        other => panic!("submitted event missing code_id measurement: {other:?}"),
    };
    assert_eq!(
        submitted_id,
        submitted.code_id.as_u32() as u64,
        "{} should report the submitted code id",
        case.name
    );
    let submitted_name = match submitted_event.metadata.get("name") {
        Some(Value::Str(name)) => name.as_ref(),
        other => panic!("submitted event missing name metadata: {other:?}"),
    };
    assert_eq!(
        submitted_name, case.source_name,
        "{} should report the source name",
        case.name
    );

    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "{} should not invoke the production frontend",
        case.name
    );
    assert_eq!(
        capture.count(&["fz", "planner", "planned"]),
        0,
        "{} should not invoke the production planner",
        case.name
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "code", "submitted"]),
        1,
        "{} should emit exactly one Compiler2 submission event",
        case.name
    );
}
