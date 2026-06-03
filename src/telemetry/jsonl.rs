//! JSON-lines file backend for the telemetry bus (fz-ndf.13).
//!
//! `JsonlBackend` is a `Handler` that serializes every event to one JSON
//! line and writes it to a `Write` sink (usually a file opened by the
//! driver). No external dep — values are serialized with a hand-rolled
//! emitter because the format is simple and we want zero compile-time cost
//! from serde in the default build.
//!
//! Format per line (keys always in this order, no pretty-printing):
//!
//! ```json
//! {"name":["fz","lexer","pass"],"time_ns":12345,"kind":"span_stop","span_id":3,
//!  "parent_span_id":2,"elapsed_ns":12345,
//!  "measurements":{},"metadata":{}}
//! ```
//!
//! `time_ns` is a monotonic nanosecond offset from when the `JsonlBackend`
//! was constructed. All events in one session share the same epoch, making
//! it trivial to profile relative ordering.
//!
//! Opaque metadata values are skipped. `Value::Bytes` is rendered as
//! `"<N bytes>"`; `Value::StrSeq` is rendered as a JSON string array.

use std::cell::RefCell;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::time::Instant;

use super::handler::{Event, EventKind, Handler};
use super::value::Value;

pub struct JsonlBackend {
    writer: RefCell<Box<dyn Write>>,
    start: Instant,
}

impl JsonlBackend {
    pub fn new_file(path: &Path) -> std::io::Result<Self> {
        let f = File::create(path)?;
        Ok(Self {
            writer: RefCell::new(Box::new(f)),
            start: Instant::now(),
        })
    }

    #[cfg(test)]
    pub fn new_writer(w: impl Write + 'static) -> Self {
        Self {
            writer: RefCell::new(Box::new(w)),
            start: Instant::now(),
        }
    }
}

impl Handler for JsonlBackend {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        let time_ns = self.start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
        let mut buf = String::with_capacity(128);
        write_event(&mut buf, ev, time_ns);
        buf.push('\n');
        let mut writer = self.writer.borrow_mut();
        let _ = writer.write_all(buf.as_bytes());
        let _ = writer.flush();
    }
}

fn write_event(out: &mut String, ev: &Event<'_, '_, '_>, time_ns: u64) {
    out.push('{');
    // name
    out.push_str("\"name\":");
    write_name(out, ev.name);
    // time_ns — monotonic offset from backend construction
    out.push_str(",\"time_ns\":");
    push_u64(out, time_ns);
    // kind
    out.push_str(",\"kind\":");
    write_str_lit(out, kind_str(ev.kind));
    // span_id
    out.push_str(",\"span_id\":");
    push_u64(out, ev.span_id);
    // parent_span_id
    out.push_str(",\"parent_span_id\":");
    push_u64(out, ev.parent_span_id);
    // elapsed_ns — present only for span events
    match ev.kind {
        EventKind::SpanStop | EventKind::SpanException => {
            out.push_str(",\"elapsed_ns\":");
            // elapsed_ns is not on Event directly; measurements carry it
            // if the bus filled it in, otherwise omit by emitting null
            match ev.measurements.get("elapsed_ns") {
                Some(Value::U64(n)) => push_u64(out, *n),
                _ => out.push_str("null"),
            }
        }
        _ => {}
    }
    // measurements
    out.push_str(",\"measurements\":");
    write_kv(out, ev.measurements.iter());
    // metadata
    out.push_str(",\"metadata\":");
    write_kv(out, ev.metadata.iter());
    out.push('}');
}

fn write_name(out: &mut String, name: &[&'static str]) {
    out.push('[');
    for (i, seg) in name.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write_str_lit(out, seg);
    }
    out.push(']');
}

fn write_kv<'a, 'v: 'a>(out: &mut String, iter: impl Iterator<Item = &'a (&'static str, Value<'v>)>) {
    out.push('{');
    let mut first = true;
    for (k, v) in iter {
        if matches!(v, Value::Opaque(_)) {
            continue;
        }
        if !first {
            out.push(',');
        }
        first = false;
        write_str_lit(out, k);
        out.push(':');
        write_value(out, v);
    }
    out.push('}');
}

fn write_value(out: &mut String, v: &Value) {
    match v {
        Value::I64(n) => {
            // manual i64 → decimal, no alloc
            push_i64(out, *n);
        }
        Value::U64(n) => push_u64(out, *n),
        Value::F64(f) => {
            // finite floats only; NaN/Inf → null (not valid JSON numbers)
            if f.is_finite() {
                use std::fmt::Write as _;
                let _ = write!(out, "{}", f);
            } else {
                out.push_str("null");
            }
        }
        Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Value::Str(s) => write_str_lit(out, s),
        Value::StrSeq(values) => {
            out.push('[');
            for (idx, value) in values.iter().enumerate() {
                if idx > 0 {
                    out.push(',');
                }
                write_str_lit(out, value);
            }
            out.push(']');
        }
        Value::Bytes(b) => {
            // Emit length tag rather than raw bytes — keeps lines ASCII-clean
            // and avoids a base64 dep. Callers that need binary round-trips
            // should use a different channel.
            out.push('"');
            out.push('<');
            push_u64(out, b.len() as u64);
            out.push_str(" bytes>");
            out.push('"');
        }
        Value::Opaque(_) => {}
    }
}

fn write_str_lit(out: &mut String, s: &str) {
    out.push('"');
    for b in s.bytes() {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0x00..=0x1f => {
                out.push_str("\\u00");
                let hi = b >> 4;
                let lo = b & 0xf;
                out.push(hex_digit(hi));
                out.push(hex_digit(lo));
            }
            _ => out.push(b as char),
        }
    }
    out.push('"');
}

fn kind_str(k: EventKind) -> &'static str {
    match k {
        EventKind::Event => "event",
        EventKind::SpanStart => "span_start",
        EventKind::SpanStop => "span_stop",
        EventKind::SpanException => "span_exception",
    }
}

fn push_u64(out: &mut String, mut n: u64) {
    if n == 0 {
        out.push('0');
        return;
    }
    let mut buf = [0u8; 20];
    let mut pos = 20;
    while n > 0 {
        pos -= 1;
        buf[pos] = b'0' + (n % 10) as u8;
        n /= 10;
    }
    for &b in &buf[pos..] {
        out.push(b as char);
    }
}

fn push_i64(out: &mut String, n: i64) {
    if n < 0 {
        out.push('-');
        // For i64::MIN, -n overflows. Cast to u64 via wrapping.
        push_u64(out, (n as u64).wrapping_neg());
    } else {
        push_u64(out, n as u64);
    }
}

fn hex_digit(n: u8) -> char {
    match n {
        0..=9 => (b'0' + n) as char,
        _ => (b'a' + n - 10) as char,
    }
}

#[cfg(test)]
mod tests {
    use std::env::temp_dir;
    use std::fs::{read_to_string, remove_file};
    use std::process::id as process_id;
    use std::thread::sleep;
    use std::time::{Duration, SystemTime, UNIX_EPOCH};

    use crate::telemetry::capture::vec_writer;
    use crate::telemetry::event::{Measurements, Metadata};
    use crate::telemetry::handler::{Event, EventKind};
    use crate::telemetry::value::opaque;
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
    fn opaque_values_are_omitted() {
        let payload = 99usize;
        let m = Measurements::new();
        let md = crate::metadata! {
            keep: "yes",
            payload: opaque(&payload),
        };
        let ev = make_event(&["x"], EventKind::Event, &m, &md);
        let line = capture_jsonl(&ev);
        assert!(line.contains("\"keep\":\"yes\""), "{}", line);
        assert!(!line.contains("payload"), "{}", line);
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
}
