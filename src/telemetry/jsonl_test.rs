use std::env::temp_dir;
use std::fs::{read_to_string, remove_file};
use std::process::id as process_id;
use std::thread::sleep;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use crate::telemetry::capture::vec_writer;
use crate::telemetry::event::{Measurements, Metadata};
use crate::telemetry::handler::{Event, EventKind};
use crate::telemetry::value::opaque_debug;
use crate::telemetry::{ConfiguredTelemetry, Telemetry as _};

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
    String::from_utf8(buf.borrow().clone()).unwrap()
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
fn opaque_values_render_as_type_and_debug() {
    let payload = 99usize;
    let m = Measurements::new();
    let md = crate::metadata! {
        keep: "yes",
        payload: opaque_debug(&payload),
    };
    let ev = make_event(&["x"], EventKind::Event, &m, &md);
    let line = capture_jsonl(&ev);
    assert!(line.contains("\"keep\":\"yes\""), "{}", line);
    assert!(
        line.contains("\"payload\":{\"opaque_type\":\"usize\",\"debug\":\"99\"}"),
        "{}",
        line
    );
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
    tel.attach(&[], Box::new(JsonlBackend::new_writer(w)));

    tel.execute(
        &["fz", "lexer", "pass"],
        &crate::measurements! { token_count: 42usize },
        &Metadata::new(),
    );

    let output = String::from_utf8(buf.borrow().clone()).unwrap();
    assert!(output.contains("\"fz\""), "{}", output);
    assert!(output.contains("\"lexer\""), "{}", output);
    assert!(output.contains("\"pass\""), "{}", output);
    assert!(output.contains("\"token_count\":42"), "{}", output);
    // Exactly one line (newline-terminated)
    assert_eq!(output.lines().count(), 1);
}

#[test]
fn file_backend_flushes_each_event() {
    let path = temp_dir().join(format!(
        "fz_jsonl_flush_{}_{}.jsonl",
        process_id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock before unix epoch")
            .as_nanos()
    ));
    let tel = ConfiguredTelemetry::new();
    tel.attach(&[], Box::new(JsonlBackend::new_file(&path).expect("open jsonl")));

    tel.event(&["fz", "diag", "error"], crate::metadata! { code: "spec/violation" });

    let output = read_to_string(&path).expect("read live jsonl");
    let _ = remove_file(&path);
    assert!(output.contains("\"name\":[\"fz\",\"diag\",\"error\"]"), "{output}");
    assert!(output.contains("\"code\":\"spec/violation\""), "{output}");
}
