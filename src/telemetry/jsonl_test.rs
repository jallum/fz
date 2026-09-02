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
    assert!(jobs[1].contains("\"world\":{\"opaque_type\":"));
    assert!(jobs[1].contains("\"completion\":{\"opaque_type\":"));
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
