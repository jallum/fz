use std::cell::Cell;
use std::env::temp_dir;
use std::fs::{read_to_string, remove_file};
use std::io::Write;
use std::process::id as process_id;
use std::rc::Rc;
use std::thread::sleep;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use crate::telemetry::capture::vec_writer;
use crate::telemetry::event::{Measurements, Metadata};
use crate::telemetry::handler::{Event, EventKind};
use crate::telemetry::{ConfiguredTelemetry, Telemetry as _, TelemetryExt as _};

use super::*;

fn make_event<'ev, 'meas, 'meta>(
    name: &'ev [&'static str],
    kind: EventKind,
    m: &'ev Measurements<'meas>,
    md: &'ev Metadata<'meta>,
) -> Event<'ev, 'meas, 'meta> {
    Event {
        name,
        kind,
        measurements: m,
        metadata: md,
        span_id: 0,
        parent_span_id: 0,
    }
}

fn capture_jsonl(ev: &Event<'_, '_, '_>) -> String {
    let (buf, w) = vec_writer();
    let backend = JsonlBackend::new_writer(w);
    backend.handle(ev);
    backend.flush();
    String::from_utf8(buf.borrow().clone()).unwrap()
}

struct CountingWriter {
    writes: Rc<Cell<usize>>,
    flushes: Rc<Cell<usize>>,
}

struct PartialThenErrorWriter {
    bytes: Rc<RefCell<Vec<u8>>>,
    calls: Rc<Cell<usize>>,
}

impl Write for PartialThenErrorWriter {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        let call = self.calls.get();
        self.calls.set(call + 1);
        if call == 0 {
            let written = bytes.len() / 2;
            self.bytes.borrow_mut().extend_from_slice(&bytes[..written]);
            Ok(written)
        } else if call == 1 {
            Err(std::io::Error::other("injected write failure"))
        } else {
            self.bytes.borrow_mut().extend_from_slice(bytes);
            Ok(bytes.len())
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl Write for CountingWriter {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.writes.set(self.writes.get() + 1);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.flushes.set(self.flushes.get() + 1);
        Ok(())
    }
}

#[test]
fn jsonl_batches_writes_and_flushes_at_the_owner_boundary() {
    let writes = Rc::new(Cell::new(0));
    let flushes = Rc::new(Cell::new(0));
    let backend = JsonlBackend::new_public_writer(CountingWriter {
        writes: writes.clone(),
        flushes: flushes.clone(),
    });
    let measurements = Measurements::new();
    let metadata = Metadata::new();
    let event = make_event(&["fz", "lexer", "pass"], EventKind::Event, &measurements, &metadata);
    backend.handle(&event);
    backend.handle(&event);
    assert_eq!(writes.get(), 0);
    assert_eq!(flushes.get(), 0);
    backend.flush();
    assert_eq!(writes.get(), 1);
    assert_eq!(flushes.get(), 1);
}

#[test]
fn default_jsonl_backend_retains_internal_compiler_events() {
    let (buf, writer) = vec_writer();
    let backend = JsonlBackend::new_writer(writer);
    let measurements = Measurements::new();
    let metadata = Metadata::new();
    for name in [
        &["fz", "compiler2", "work_graph", "applied"][..],
        &["fz", "compiler2", "drive", "timed_out"][..],
    ] {
        backend.handle(&make_event(name, EventKind::Event, &measurements, &metadata));
    }
    let output = String::from_utf8(buf.borrow().clone()).unwrap();
    assert!(output.contains("\"work_graph\",\"applied\""));
    assert!(output.contains("\"drive\",\"timed_out\""));
}

#[test]
fn compiler_drive_and_job_spans_render_raw_authorities() {
    let telemetry = ConfiguredTelemetry::new();
    let (buf, writer) = vec_writer();
    JsonlBackend::new_writer(writer).install(&telemetry);
    let mut compiler = crate::compiler2::Compiler2::new(telemetry);
    compiler.submit_code(crate::compiler2::CodeSubmission {
        name: Some("raw_span.fz".to_string()),
        text: "fn main(), do: 0\n".to_string(),
    });

    let outcome = compiler.drive();

    assert!(matches!(outcome, crate::compiler2::DriveOutcome::Resolved));
    let output = String::from_utf8(buf.borrow().clone()).unwrap();
    let drive = output
        .lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"compiler2\",\"drive\"]"))
        .collect::<Vec<_>>();
    let jobs = output
        .lines()
        .filter(|line| line.contains("\"name\":[\"fz\",\"compiler2\",\"job\"]"))
        .collect::<Vec<_>>();
    assert_eq!(drive.len(), 2);
    assert!(drive[0].contains("\"kind\":\"span_start\""));
    assert!(drive[1].contains("\"kind\":\"span_stop\""));
    assert!(drive[1].contains("\"outcome\":{\"opaque_type\":"));
    assert!(drive[1].contains("\"status\":\"resolved\""));
    assert!(!drive[1].contains("jobs_ran"));
    assert_eq!(jobs.len(), 2);
    assert!(jobs[0].contains("\"kind\":\"span_start\""));
    assert!(jobs[0].contains("\"job\":{\"opaque_type\":"));
    assert!(jobs[1].contains("\"kind\":\"span_stop\""));
    assert!(!jobs[1].contains("\"world\":"));
    assert!(!jobs[1].contains("\"completion\":"));
    assert_ne!(jobs[0].split("\"parent_span_id\":").nth(1), Some("0"));
}

#[test]
fn jsonl_retries_only_the_unsent_suffix_after_a_partial_write_error() {
    let bytes = Rc::new(RefCell::new(Vec::new()));
    let calls = Rc::new(Cell::new(0));
    let backend = JsonlBackend::new_public_writer(PartialThenErrorWriter {
        bytes: bytes.clone(),
        calls,
    });
    let measurements = Measurements::new();
    let metadata = Metadata::new();
    let event = make_event(&["fz", "lexer", "pass"], EventKind::Event, &measurements, &metadata);
    backend.handle(&event);
    backend.flush();
    let prefix = bytes.borrow().len();
    assert!(prefix > 0);
    backend.flush();
    let output = String::from_utf8(bytes.borrow().clone()).unwrap();
    assert_eq!(output.lines().count(), 1, "retry must not duplicate the sent prefix");
}

#[test]
fn event_line_is_valid_json_object() {
    let (m, md) = (Measurements::new(), Metadata::new());
    let ev = make_event(&["fz", "test", "ping"], EventKind::Event, &m, &md);
    let line = capture_jsonl(&ev);
    // Must end with newline
    assert!(line.ends_with('\n'), "missing trailing newline");
    let trimmed = line.trim_end();
    // Must start with { and end with }
    assert!(trimmed.starts_with('{'));
    assert!(trimmed.ends_with('}'));
    // Must contain the name array
    assert!(trimmed.contains("\"fz\""));
    assert!(trimmed.contains("\"test\""));
    assert!(trimmed.contains("\"ping\""));
    assert!(trimmed.contains("\"kind\":\"event\""));
}

#[test]
fn measurements_and_metadata_serialised() {
    let m = crate::measurements! { count: 7usize };
    let md = crate::metadata! { label: "hello" };
    let ev = make_event(&["x"], EventKind::Event, &m, &md);
    let line = capture_jsonl(&ev);
    assert!(line.contains("\"count\":7"), "count not found: {}", line);
    assert!(line.contains("\"label\":\"hello\""), "label not found: {}", line);
}

#[test]
fn span_stop_has_elapsed_ns() {
    let (m, md) = (crate::measurements! { elapsed_ns: 9999u64 }, Metadata::new());
    let ev = Event {
        name: &["fz", "span"],
        kind: EventKind::SpanStop,
        measurements: &m,
        metadata: &md,
        span_id: 1,
        parent_span_id: 0,
    };
    let line = capture_jsonl(&ev);
    assert!(line.contains("\"elapsed_ns\":9999"), "elapsed: {}", line);
}

#[test]
fn numeric_values_correct() {
    let (m, md) = (crate::measurements! { a: -5i64, b: 0u64, c: 2.5f64 }, Metadata::new());
    let ev = make_event(&["x"], EventKind::Event, &m, &md);
    let line = capture_jsonl(&ev);
    assert!(line.contains("\"a\":-5"), "{}", line);
    assert!(line.contains("\"b\":0"), "{}", line);
    assert!(line.contains("\"c\":2.5"), "{}", line);
}

#[test]
fn bytes_value_renders_as_length_tag() {
    let (m, md) = (Measurements::new(), crate::metadata! { blob: vec![1u8, 2, 3] });
    let ev = make_event(&["x"], EventKind::Event, &m, &md);
    let line = capture_jsonl(&ev);
    assert!(line.contains("\"blob\":\"<3 bytes>\""), "{}", line);
}

#[test]
fn string_sequence_renders_as_json_array() {
    let (m, md) = (
        Measurements::new(),
        crate::metadata! { call_edges: vec!["Direct".to_string(), "Cont".to_string()] },
    );
    let ev = make_event(&["x"], EventKind::Event, &m, &md);
    let line = capture_jsonl(&ev);
    assert!(line.contains("\"call_edges\":[\"Direct\",\"Cont\"]"), "{}", line);
}

#[test]
fn opaque_values_render_as_type() {
    let payload = 99usize;
    let m = Measurements::new();
    let md = crate::metadata! {
        keep: "yes",
        payload: crate::telemetry::opaque(&payload),
    };
    let ev = make_event(&["x"], EventKind::Event, &m, &md);
    let line = capture_jsonl(&ev);
    assert!(line.contains("\"keep\":\"yes\""), "{}", line);
    assert!(line.contains("\"payload\":{\"opaque_type\":\"usize\"}"), "{}", line);
}

#[test]
fn string_escaping_handles_special_chars() {
    let (m, md) = (Measurements::new(), crate::metadata! { msg: "hello\nworld\t\"end\"" });
    let ev = make_event(&["x"], EventKind::Event, &m, &md);
    let line = capture_jsonl(&ev);
    assert!(line.contains("\\n"), "newline not escaped: {}", line);
    assert!(line.contains("\\t"), "tab not escaped: {}", line);
    assert!(line.contains("\\\""), "quote not escaped: {}", line);
}

#[test]
fn time_ns_is_present_and_numeric() {
    let (m, md) = (Measurements::new(), Metadata::new());
    let ev = make_event(&["fz", "test", "ping"], EventKind::Event, &m, &md);
    let line = capture_jsonl(&ev);
    // Extract the time_ns value — must exist and parse as a u64.
    let after = line.split("\"time_ns\":").nth(1).expect("time_ns missing");
    let digits: String = after.chars().take_while(|c| c.is_ascii_digit()).collect();
    assert!(!digits.is_empty(), "time_ns has no digits: {}", line);
    digits.parse::<u64>().expect("time_ns is not a valid u64");
}

#[test]
fn time_ns_increases_across_events() {
    let (buf, w) = vec_writer();
    let backend = JsonlBackend::new_writer(w);
    let (m, md) = (Measurements::new(), Metadata::new());
    let ev = make_event(&["x"], EventKind::Event, &m, &md);
    backend.handle(&ev);
    // Burn a small but reliable amount of time.
    sleep(Duration::from_micros(50));
    backend.handle(&ev);
    backend.flush();
    let output = String::from_utf8(buf.borrow().clone()).unwrap();
    let times: Vec<u64> = output
        .lines()
        .map(|l| {
            let after = l.split("\"time_ns\":").nth(1).unwrap();
            after
                .chars()
                .take_while(|c| c.is_ascii_digit())
                .collect::<String>()
                .parse::<u64>()
                .unwrap()
        })
        .collect();
    assert_eq!(times.len(), 2);
    assert!(
        times[1] > times[0],
        "second time_ns {} not > first {}",
        times[1],
        times[0]
    );
}

#[test]
fn through_configured_telemetry_roundtrips() {
    let (buf, w) = vec_writer();
    let tel = ConfiguredTelemetry::new();
    JsonlBackend::new_writer(w).install(&tel);

    tel.dispatch(
        &["fz", "lexer", "pass"],
        &crate::measurements! { token_count: 42usize },
        &Metadata::new(),
    );

    drop(tel);

    let output = String::from_utf8(buf.borrow().clone()).unwrap();
    assert!(output.contains("\"fz\""), "{}", output);
    assert!(output.contains("\"lexer\""), "{}", output);
    assert!(output.contains("\"pass\""), "{}", output);
    assert!(output.contains("\"token_count\":42"), "{}", output);
    // Exactly one line (newline-terminated)
    assert_eq!(output.lines().count(), 1);
}

#[test]
fn callable_owner_settlement_renders_its_existing_obligations() {
    use crate::compiler2::pull::{ProductValue, TransportCarrier, TransportLayout};
    use crate::compiler2::transport::{CallableConstructionOwner, ShapeId};
    let value = ProductValue::CallableConstruction(Rc::new(CallableConstructionOwner {
        layout: TransportLayout {
            structural: ShapeId::for_test(17),
            carrier: TransportCarrier::Absent,
        },
        construction: None,
        callable_facts: Default::default(),
        boundary_facts: Default::default(),
    }));
    let measurements = Measurements::new();
    let metadata = crate::metadata! { value: crate::telemetry::opaque(&value) };
    let event = make_event(&["test"], EventKind::Event, &measurements, &metadata);
    let json: serde_json::Value = serde_json::from_str(&capture_jsonl(&event)).unwrap();
    let answer = &json["metadata"]["value"];
    assert_eq!(answer["structural_shape_id"], 17);
    assert_eq!(answer["carrier"], "absent");
    assert_eq!(answer["construction"], false);
    assert_eq!(answer["callable_facts"], 0);
    assert_eq!(answer["boundary_facts"], 0);
}

#[test]
fn pull_product_settled_renders_the_value_authority() {
    let (buf, writer) = vec_writer();
    let telemetry = ConfiguredTelemetry::new();
    JsonlBackend::new_writer(writer).install(&telemetry);
    let product = crate::compiler2::pull::ProductKey::RootBackendProduct(crate::compiler2::RootId::for_test(9));
    let value = crate::compiler2::pull::ProductValue::Unit;
    let settlement = crate::compiler2::pull::ProductSettlement {
        generation: 1,
        changed: true,
        group: None,
    };
    telemetry.raw_event3(
        &["fz", "compiler2", "pull", "product", "settled"],
        &product,
        &value,
        &settlement,
    );
    drop(telemetry);

    let output = String::from_utf8(buf.borrow().clone()).unwrap();
    assert_eq!(output.lines().count(), 1);
    assert!(output.contains("\"value\""), "{output}");
    assert!(output.contains("\"settlement\""), "{output}");
    assert!(output.contains("\"generation\":1"), "{output}");
    assert!(output.contains("\"changed\":true"), "{output}");
    assert!(output.contains("\"group\":null"), "{output}");
    assert!(!output.contains("\"product\",\"produced\""), "{output}");
    assert!(!output.contains("\"product\",\"waited\""), "{output}");
}

#[test]
fn opposite_mint_histories_render_byte_identical_multi_element_owner_batches() {
    use crate::compiler2::DependencyKey;
    use crate::compiler2::SemanticOrd as _;
    use crate::compiler2::{ActivationKey, FactChange, FactKey, FactMovement, FactState, FactUse, FunctionId, RootId};

    fn canonicalize_arrows(
        value: &serde_json::Value,
        arrows: &std::collections::HashMap<u64, &'static str>,
        field: Option<&str>,
    ) -> serde_json::Value {
        match (field, value) {
            (Some("arrow"), serde_json::Value::Number(id)) => serde_json::Value::String(
                arrows
                    .get(&id.as_u64().expect("arrow id is an integer"))
                    .expect("test dictionary covers every activation arrow")
                    .to_string(),
            ),
            (_, serde_json::Value::Object(fields)) => serde_json::Value::Object(
                fields
                    .iter()
                    .map(|(name, value)| (name.clone(), canonicalize_arrows(value, arrows, Some(name))))
                    .collect(),
            ),
            (_, serde_json::Value::Array(values)) => serde_json::Value::Array(
                values
                    .iter()
                    .map(|value| canonicalize_arrows(value, arrows, None))
                    .collect(),
            ),
            _ => value.clone(),
        }
    }

    let render = |non_empty_first: bool| {
        let mut types = crate::compiler2::Types::new();
        let int = types.int();
        let root = RootId::for_test(71);
        let function = FunctionId::for_test(710);
        let (list, non_empty) = if non_empty_first {
            let non_empty = types.non_empty_list(int);
            let non_empty = ActivationKey::from_inputs(root, function, &[non_empty], &mut types);
            let list = types.list(int);
            let list = ActivationKey::from_inputs(root, function, &[list], &mut types);
            (list, non_empty)
        } else {
            let list = types.list(int);
            let list = ActivationKey::from_inputs(root, function, &[list], &mut types);
            let non_empty = types.non_empty_list(int);
            let non_empty = ActivationKey::from_inputs(root, function, &[non_empty], &mut types);
            (list, non_empty)
        };
        let raw_order = list.arrow < non_empty.arrow;
        let keys = if non_empty_first {
            vec![
                FactKey::ReturnType(non_empty.clone()),
                FactKey::ReturnType(list.clone()),
            ]
        } else {
            vec![
                FactKey::ReturnType(list.clone()),
                FactKey::ReturnType(non_empty.clone()),
            ]
        };
        let mut keys = keys.into_iter().map(DependencyKey::Fact).collect::<Vec<_>>();
        keys.sort_by(|left, right| left.semantic_cmp(right, &types));
        let step = crate::compiler2::AppliedStep {
            changed: keys
                .iter()
                .cloned()
                .map(|key| FactChange {
                    key,
                    old_revision: None,
                    new_revision: Some(1),
                    old_settled: false,
                    new_settled: true,
                })
                .collect(),
            movements: keys
                .iter()
                .cloned()
                .map(|key| FactMovement {
                    key,
                    state: FactState {
                        revision: Some(1),
                        settled: true,
                    },
                })
                .collect(),
            wakes: Vec::<crate::compiler2::Wake<crate::compiler2::Job, DependencyKey>>::new(),
            blocked: keys.into_iter().map(FactUse::settled).collect(),
        };
        let mut body = String::new();
        write_applied_step_body(&mut body, &step);
        let json = format!(
            "{{{}}}",
            body.strip_prefix(',').expect("applied body starts with a field")
        );
        let raw: serde_json::Value = serde_json::from_str(&json).expect("applied step JSON");
        let arrows = std::collections::HashMap::from([
            (list.arrow.as_u32() as u64, "list-activation"),
            (non_empty.arrow.as_u32() as u64, "non-empty-list-activation"),
        ]);
        (
            raw_order,
            serde_json::to_vec(&canonicalize_arrows(&raw, &arrows, None)).expect("canonical batch JSON"),
        )
    };

    let list_first = render(false);
    let non_empty_first = render(true);
    assert_ne!(
        list_first.0, non_empty_first.0,
        "fixture must deterministically reverse raw arrow ids"
    );
    assert_eq!(
        list_first.1, non_empty_first.1,
        "renderer must preserve the typed owner sequence across opposite mint and insertion histories"
    );
}

#[test]
fn fact_dependency_steps_preserve_the_existing_causal_json_shape() {
    use crate::compiler2::DependencyKey;
    use crate::compiler2::{
        AppliedStep, FactChange, FactKey, FactMovement, FactState, FactUse, Job, RootId, Wake, WakeDisposition,
    };

    let root = RootId::for_test(7);
    let key = DependencyKey::Fact(FactKey::RootEntry(root));
    let step = AppliedStep {
        changed: vec![FactChange {
            key: key.clone(),
            old_revision: None,
            new_revision: Some(1),
            old_settled: false,
            new_settled: true,
        }],
        wakes: vec![Wake {
            cause: FactUse::settled(key.clone()),
            job: Job::SeedRoot(root),
            disposition: WakeDisposition::Enqueued,
            shift: true,
        }],
        movements: vec![FactMovement {
            key: key.clone(),
            state: FactState {
                revision: Some(1),
                settled: true,
            },
        }],
        blocked: vec![FactUse::settled(key)],
    };
    let mut body = String::new();
    write_applied_step_body(&mut body, &step);
    assert_eq!(
        body,
        concat!(
            ",\"changed\":[{\"kind\":\"RootEntry\",\"root_id\":7,\"old_revision\":null,\"new_revision\":1,\"old_settled\":false,\"new_settled\":true}]",
            ",\"wakes\":[{\"cause\":{\"use\":\"settled\",\"kind\":\"RootEntry\",\"root_id\":7},\"job\":{\"kind\":\"SeedRoot\",\"root_id\":7},\"disposition\":\"enqueued\",\"shift\":true}]",
            ",\"movements\":[{\"kind\":\"RootEntry\",\"root_id\":7,\"revision\":1,\"settled\":true}]",
            ",\"blocked\":[{\"kind\":\"RootEntry\",\"root_id\":7}]",
        )
    );
}

#[test]
fn product_dependency_reads_identify_both_the_owner_and_the_product() {
    use crate::compiler2::{DependencyKey, ProductAddress};
    use crate::compiler2::{FactUse, ProductKey, RootId};

    for owner in [7, 8] {
        let dependency = FactUse::settled(DependencyKey::Product(ProductAddress {
            root: RootId::for_test(owner),
            key: ProductKey::RootBackendContent(RootId::for_test(9)),
        }));
        let mut body = String::new();
        write_dependency_use_identity(&mut body, &dependency);
        assert_eq!(
            body,
            format!(
                "{{\"use\":\"settled\",\"kind\":\"Product\",\"root_id\":{owner},\"product\":{{\"kind\":\"root_backend_content\",\"root_id\":9}}}}"
            )
        );
    }
}

#[test]
fn incoming_slot_facts_identify_the_exact_root_executable_and_input() {
    use crate::compiler2::incoming_inputs::InputSlot;
    use crate::compiler2::{
        ActivationKey, DependencyKey, ExecutableKey, ExecutableNeed, FactKey, FactUse, FunctionId, RootId, Types,
    };

    let mut types = Types::new();
    let int = types.int();
    let mut identities = std::collections::HashSet::new();
    for root in [7, 8] {
        for index in [0, 1] {
            let activation =
                ActivationKey::from_inputs(RootId::for_test(root), FunctionId::for_test(9), &[int, int], &mut types);
            let arrow = activation.arrow.as_u32();
            let slot = InputSlot {
                executable: ExecutableKey {
                    activation,
                    need: ExecutableNeed::Value,
                },
                semantic_index: index,
            };
            let dependency = FactUse::settled(DependencyKey::Fact(FactKey::IncomingInputSlot(slot)));
            let mut body = String::new();
            write_dependency_use_identity(&mut body, &dependency);
            let identity: serde_json::Value = serde_json::from_str(&body).expect("typed slot dependency JSON");
            assert_eq!(
                identity,
                serde_json::json!({
                    "use": "settled", "kind": "IncomingInputSlot", "root_id": root,
                    "function_id": 9, "arrow": arrow, "need": "value", "semantic_index": index,
                })
            );
            assert!(
                identities.insert(body),
                "different root/input slots must not collapse in causal replay"
            );
        }
    }
}

#[test]
fn product_movements_are_public_causal_events() {
    use crate::compiler2::{AppliedStep, FactMovement, FactState, Job, ProductKey, RootId};
    use crate::compiler2::{DependencyKey, ProductAddress};

    let telemetry = ConfiguredTelemetry::new();
    let (buf, writer) = vec_writer();
    JsonlBackend::new_public_writer(writer).install(&telemetry);
    let step = AppliedStep::<Job, DependencyKey> {
        changed: vec![],
        wakes: vec![],
        blocked: vec![],
        movements: vec![FactMovement {
            key: DependencyKey::Product(ProductAddress {
                root: RootId::for_test(7),
                key: ProductKey::RootBackendContent(RootId::for_test(7)),
            }),
            state: FactState {
                revision: Some(3),
                settled: true,
            },
        }],
    };
    telemetry.raw_event1(&["fz", "compiler2", "work_graph", "dependencies_moved"], &step);
    drop(telemetry);
    let log = String::from_utf8(buf.borrow().clone()).unwrap();
    let events = log
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(events.len(), 1, "each product movement has one causal record");
    assert_eq!(
        events[0]["metadata"]["step"]["movements"][0]["product"]["kind"],
        "root_backend_content"
    );
    assert_eq!(events[0]["metadata"]["step"]["movements"][0]["revision"], 3);
}

#[test]
fn failed_product_requests_report_the_dependency_that_failed() {
    use crate::compiler2::{DependencyKey, DriveOutcome, Job, ProductAddress, ProductKey, RootId};

    let outcome = DriveOutcome::<Job, DependencyKey>::DependencyFailed {
        dependency: DependencyKey::Product(ProductAddress {
            root: RootId::for_test(7),
            key: ProductKey::NativeProgram(RootId::for_test(7)),
        }),
    };
    let measurements = Measurements::new();
    let metadata = crate::metadata! { outcome: crate::telemetry::opaque(&outcome) };
    let event = make_event(
        &["fz", "compiler2", "drive"],
        EventKind::SpanStop,
        &measurements,
        &metadata,
    );
    let rendered: serde_json::Value = serde_json::from_str(&capture_jsonl(&event)).unwrap();
    let outcome = &rendered["metadata"]["outcome"];
    assert_eq!(outcome["status"], "dependency_failed");
    assert_eq!(outcome["dependency"]["root_id"], 7);
    assert_eq!(outcome["dependency"]["product"]["kind"], "native_program");
    assert!(outcome.get("job_kind").is_none());
}

#[test]
fn file_backend_flushes_when_telemetry_owner_drops() {
    let path = temp_dir().join(format!(
        "fz_jsonl_flush_{}_{}.jsonl",
        process_id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock before unix epoch")
            .as_nanos()
    ));
    let tel = ConfiguredTelemetry::new();
    JsonlBackend::new_file(&path).expect("open jsonl").install(&tel);

    tel.event_lazy(&["fz", "diag", "error"], || crate::metadata! { code: "spec/violation" });

    drop(tel);

    let output = read_to_string(&path).expect("read live jsonl");
    let _ = remove_file(&path);
    assert!(output.contains("\"name\":[\"fz\",\"diag\",\"error\"]"), "{output}");
    assert!(output.contains("\"code\":\"spec/violation\""), "{output}");
}

/// fz-kdt.69.2: the unresolved edge renders as itself. A reached callsite that
/// names no target is a published VALUE, so the stream must show it — before,
/// the fact simply was not there and the projection wrote nothing at all.
#[test]
fn an_unresolved_callsite_edge_renders_as_itself() {
    use crate::compiler2::{CallSiteResolution, CallSiteSummary, CallTargetSummary, SelectedCallee, World};

    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let root = world.submit_root(None, "main".to_string(), 0, crate::compiler2::ExecutableNeed::Value);
    let caller = world.root_function(root);
    let activation = crate::compiler2::ActivationKey::from_inputs(root, caller, &[], world.types_mut());
    let unresolved = crate::compiler2::CallSiteKey {
        activation: activation.clone(),
        callsite: crate::compiler2::CallSiteId::from_u32(0),
    };
    let resolved = crate::compiler2::CallSiteKey {
        activation,
        callsite: crate::compiler2::CallSiteId::from_u32(1),
    };
    world.define_callsite_summary(unresolved.clone(), CallSiteResolution::Unresolved);
    world.define_callsite_summary(
        resolved.clone(),
        CallSiteResolution::Resolved(CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::ProviderBoundary(caller),
                surface_inputs: Vec::new(),
                activation: None,
                activation_inputs: None,
                extern_params: None,
                return_ty: None,
            }],
            return_ty: None,
        }),
    );

    let mut out = String::new();
    write_callsite_resolution(
        &mut out,
        &world,
        world.callsite_resolution(&unresolved).expect("a reached callsite"),
    );
    assert_eq!(out, "{\"unresolved\":true}");

    let mut out = String::new();
    write_callsite_resolution(
        &mut out,
        &world,
        world.callsite_resolution(&resolved).expect("a resolved callsite"),
    );
    assert!(
        out.starts_with("{\"return\":null,\"targets\":[{\"callee\":"),
        "a resolved edge keeps the shape it always had: {out}"
    );
}
