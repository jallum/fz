use std::cell::RefCell;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::time::Instant;

use crate::compiler2::artifact::{EmissionReadyProgram, MaterializedProgram};
use crate::compiler2::drive::{FactKey, Job, JobEffects};
use crate::compiler2::protocol::{ProtocolCallback, ProtocolImpl, ProtocolImplKey};
use crate::compiler2::semantic::{ActivationAnalysis, CallSiteSummary, SemanticClosure};
use crate::compiler2::{
    ActivationKey, CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, Function, FunctionRef, LoweredBody, Module,
    Root, RootSubmission, Ty, UnresolvedWait,
};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch};
use crate::telemetry::handler::{Event, EventKind, Handler};
use crate::telemetry::{ConfiguredTelemetry, Value};

#[test]
#[ignore = "manual trace harness for one-off Compiler2 telemetry analysis"]
fn dump_quicksort_compiler2_telemetry_to_jsonl() {
    let path = Path::new("/tmp/fz-compiler2-quicksort.jsonl");
    let tel = ConfiguredTelemetry::new();
    tel.attach(&[], Box::new(RichJsonlBackend::new_file(path).expect("open log file")));

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: format!(
            "{}\nfn foo(), do: 42\n",
            include_str!("../../fixtures/quicksort/input.fz")
        ),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    match compiler.drive() {
        DriveOutcome::Resolved => {}
        other => panic!("expected resolved quicksort compilation, got {other:?}"),
    }
}

struct RichJsonlBackend {
    writer: RefCell<Box<dyn Write>>,
    start: Instant,
}

impl RichJsonlBackend {
    fn new_file(path: &Path) -> std::io::Result<Self> {
        let file = File::create(path)?;
        Ok(Self {
            writer: RefCell::new(Box::new(file)),
            start: Instant::now(),
        })
    }
}

impl Handler for RichJsonlBackend {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        let time_ns = self.start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
        let mut buf = String::with_capacity(256);
        write_event(&mut buf, event, time_ns);
        buf.push('\n');
        let mut writer = self.writer.borrow_mut();
        let _ = writer.write_all(buf.as_bytes());
        let _ = writer.flush();
    }
}

fn write_event(out: &mut String, event: &Event<'_, '_, '_>, time_ns: u64) {
    out.push('{');
    out.push_str("\"name\":");
    write_name(out, event.name);
    out.push_str(",\"time_ns\":");
    push_u64(out, time_ns);
    out.push_str(",\"kind\":");
    write_str_lit(out, kind_str(event.kind));
    out.push_str(",\"span_id\":");
    push_u64(out, event.span_id);
    out.push_str(",\"parent_span_id\":");
    push_u64(out, event.parent_span_id);
    if matches!(event.kind, EventKind::SpanStop | EventKind::SpanException) {
        out.push_str(",\"elapsed_ns\":");
        match event.measurements.get("elapsed_ns") {
            Some(Value::U64(n)) => push_u64(out, *n),
            _ => out.push_str("null"),
        }
    }
    out.push_str(",\"measurements\":");
    write_kv(out, event.measurements.iter());
    out.push_str(",\"metadata\":");
    write_kv(out, event.metadata.iter());
    out.push('}');
}

fn write_name(out: &mut String, name: &[&'static str]) {
    out.push('[');
    for (index, segment) in name.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        write_str_lit(out, segment);
    }
    out.push(']');
}

fn write_kv<'a, 'v: 'a>(out: &mut String, iter: impl Iterator<Item = &'a (&'static str, Value<'v>)>) {
    out.push('{');
    let mut first = true;
    for (key, value) in iter {
        if !first {
            out.push(',');
        }
        first = false;
        write_str_lit(out, key);
        out.push(':');
        write_value(out, value);
    }
    out.push('}');
}

fn write_value(out: &mut String, value: &Value<'_>) {
    match value {
        Value::I64(n) => push_i64(out, *n),
        Value::U64(n) => push_u64(out, *n),
        Value::F64(f) => {
            if f.is_finite() {
                use std::fmt::Write as _;
                let _ = write!(out, "{f}");
            } else {
                out.push_str("null");
            }
        }
        Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Value::Str(s) => write_str_lit(out, s),
        Value::StrSeq(values) => {
            out.push('[');
            for (index, value) in values.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                write_str_lit(out, value);
            }
            out.push(']');
        }
        Value::Bytes(bytes) => {
            out.push('"');
            out.push('<');
            push_u64(out, bytes.len() as u64);
            out.push_str(" bytes>");
            out.push('"');
        }
        Value::Opaque(opaque) => write_opaque(out, value, &format!("{opaque:?}")),
    }
}

fn write_opaque(out: &mut String, value: &Value<'_>, fallback_debug: &str) {
    out.push('{');
    if let Some((type_name, debug)) = opaque_debug(value) {
        write_str_lit(out, "opaque_type");
        out.push(':');
        write_str_lit(out, type_name);
        out.push(',');
        write_str_lit(out, "debug");
        out.push(':');
        write_str_lit(out, &debug);
    } else {
        write_str_lit(out, "opaque_debug");
        out.push(':');
        write_str_lit(out, fallback_debug);
    }
    out.push('}');
}

fn opaque_debug(value: &Value<'_>) -> Option<(&'static str, String)> {
    macro_rules! try_debug {
        ($t:ty) => {
            if let Some(inner) = value.downcast_ref::<$t>() {
                return Some((std::any::type_name::<$t>(), format!("{inner:?}")));
            }
        };
    }

    try_debug!(Job);
    try_debug!(JobEffects);
    try_debug!(Root);
    try_debug!(FunctionRef);
    try_debug!(Function);
    try_debug!(Module);
    try_debug!(ActivationKey);
    try_debug!(ActivationAnalysis);
    try_debug!(CallSiteSummary);
    try_debug!(Ty);
    try_debug!(SemanticClosure);
    try_debug!(MaterializedProgram);
    try_debug!(EmissionReadyProgram);
    try_debug!(LoweredBody);
    try_debug!(PatternGuardDispatch<Ty>);
    try_debug!(PatternDispatchPlan<Ty>);
    try_debug!(ProtocolCallback);
    try_debug!(ProtocolImplKey);
    try_debug!(ProtocolImpl);
    try_debug!(crate::compiler2::AppliedStep<Job, FactKey>);
    try_debug!(UnresolvedWait<Job, FactKey>);
    try_debug!(Vec<UnresolvedWait<Job, FactKey>>);
    try_debug!(FactKey);

    None
}

fn kind_str(kind: EventKind) -> &'static str {
    match kind {
        EventKind::Event => "event",
        EventKind::SpanStart => "span_start",
        EventKind::SpanStop => "span_stop",
        EventKind::SpanException => "span_exception",
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
                out.push(hex_digit(b >> 4));
                out.push(hex_digit(b & 0xf));
            }
            _ => out.push(b as char),
        }
    }
    out.push('"');
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
    for digit in &buf[pos..] {
        out.push(*digit as char);
    }
}

fn push_i64(out: &mut String, n: i64) {
    if n < 0 {
        out.push('-');
        push_u64(out, n.unsigned_abs());
    } else {
        push_u64(out, n as u64);
    }
}

fn hex_digit(nibble: u8) -> char {
    match nibble {
        0..=9 => (b'0' + nibble) as char,
        10..=15 => (b'a' + (nibble - 10)) as char,
        _ => unreachable!("hex nibble must be in 0..=15"),
    }
}
