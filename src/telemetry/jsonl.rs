//! JSON-lines file backend for the telemetry bus (fz-ndf.13).
//!
//! `JsonlBackend` is a `Handler` that serializes every event to one JSON
//! line and writes it to a `Write` sink (usually a file opened by the
//! driver). No external dep — values are serialized with a hand-rolled
//! emitter because the format is simple and we want zero extra compile-time
//! cost for telemetry encoding.
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
//! Opaque metadata values are rendered as `{"opaque_type":"..."}`. `Value::Bytes`
//! is rendered as `"<N bytes>"`; `Value::StrSeq` is rendered as a JSON string
//! array.

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
    write_compiler2_semantic(out, ev);
    out.push('}');
}

fn write_compiler2_semantic(out: &mut String, ev: &Event<'_, '_, '_>) {
    let Some(world) = ev
        .metadata
        .get("world")
        .and_then(Value::downcast_ref::<crate::compiler2::World>)
    else {
        return;
    };
    if ev.name == ["fz", "compiler2", "callsite", "defined"] {
        if let Some(callsite) = ev
            .metadata
            .get("callsite")
            .and_then(|value| value.downcast_ref::<crate::compiler2::CallSiteKey>())
            && let Some(summary) = world.callsite_summary(callsite)
        {
            out.push_str(",\"semantic\":");
            write_callsite_summary(out, world, summary);
        }
        return;
    }
    let Some(activation) = ev
        .metadata
        .get("activation")
        .and_then(Value::downcast_ref::<crate::compiler2::ActivationKey>)
    else {
        return;
    };
    match ev.name {
        ["fz", "compiler2", "activation_inputs", "defined"] => {
            if let Some(inputs) = world.activation_inputs_ref(activation) {
                out.push_str(",\"semantic\":{\"inputs\":");
                write_types(out, world, inputs);
                out.push('}');
            }
        }
        ["fz", "compiler2", "return_type", "defined"] => {
            out.push_str(",\"semantic\":{\"return\":");
            write_optional_type(out, world, world.activation_return_evidence(activation));
            out.push('}');
        }
        ["fz", "compiler2", "activation_analysis", "defined"] => {
            if let Some(analysis) = world.activation_analysis(activation) {
                out.push_str(",\"semantic\":{\"reachable_clauses\":");
                push_u64(out, analysis.reachable_clauses.len() as u64);
                out.push_str(",\"reachable_entries\":");
                push_u64(out, analysis.reachable_entries.len() as u64);
                out.push_str(",\"callsites\":");
                push_u64(out, analysis.callsites.len() as u64);
                out.push_str(",\"latent_executables\":");
                push_u64(out, analysis.latent_executables.len() as u64);
                out.push_str(",\"values\":");
                push_u64(out, analysis.value_types.len() as u64);
                out.push('}');
            }
        }
        _ => {}
    }
}

fn write_types(out: &mut String, world: &crate::compiler2::World, types: &[crate::compiler2::Ty]) {
    out.push('[');
    for (index, ty) in types.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        write_str_lit(out, &world.types().display(ty));
    }
    out.push(']');
}

fn write_optional_type(out: &mut String, world: &crate::compiler2::World, ty: Option<crate::compiler2::Ty>) {
    match ty {
        Some(ty) => write_str_lit(out, &world.types().display(&ty)),
        None => out.push_str("null"),
    }
}

fn write_callsite_summary(
    out: &mut String,
    world: &crate::compiler2::World,
    summary: &crate::compiler2::CallSiteSummary,
) {
    out.push_str("{\"return\":");
    write_optional_type(out, world, summary.return_ty);
    out.push_str(",\"targets\":[");
    for (index, target) in summary.targets.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str("{\"callee\":");
        let (kind, function) = match target.callee {
            crate::compiler2::SelectedCallee::Function(function) => ("function", function),
            crate::compiler2::SelectedCallee::ProviderBoundary(function) => ("provider_boundary", function),
        };
        out.push('{');
        write_str_lit(out, "kind");
        out.push(':');
        write_str_lit(out, kind);
        out.push(',');
        write_str_lit(out, "name");
        out.push(':');
        let function_ref = world.function_ref(function);
        write_str_lit(out, &function_ref.name);
        out.push(',');
        write_str_lit(out, "arity");
        out.push(':');
        push_u64(out, function_ref.arity as u64);
        out.push('}');
        out.push_str(",\"inputs\":");
        write_types(out, world, &target.surface_inputs);
        out.push_str(",\"return\":");
        write_optional_type(out, world, target.return_ty);
        out.push('}');
    }
    out.push_str("]}");
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
        Value::Opaque(opaque) => write_opaque(out, *opaque),
    }
}

fn write_opaque(out: &mut String, opaque: super::value::OpaqueRef<'_>) {
    out.push('{');
    write_str_lit(out, "opaque_type");
    out.push(':');
    write_str_lit(out, opaque.type_name());
    if let Some(job) = opaque.downcast_ref::<crate::compiler2::Job>() {
        out.push(',');
        write_str_lit(out, "kind");
        out.push(':');
        write_str_lit(out, job_kind(job));
    } else if let Some(effects) = opaque.downcast_ref::<crate::compiler2::JobEffects>() {
        out.push(',');
        write_str_lit(out, "reads");
        out.push(':');
        push_u64(out, effects.reads.len() as u64);
        out.push(',');
        write_str_lit(out, "waits");
        out.push(':');
        push_u64(out, effects.waits.len() as u64);
        out.push(',');
        write_str_lit(out, "outputs");
        out.push(':');
        push_u64(out, effects.outputs.len() as u64);
        out.push(',');
        write_str_lit(out, "changed");
        out.push(':');
        push_u64(out, effects.changed.len() as u64);
    } else if let Some(program) = opaque.downcast_ref::<crate::compiler2::BackendProgram>() {
        out.push(',');
        write_str_lit(out, "backend_revision");
        out.push(':');
        push_u64(out, program.backend_revision);
        out.push(',');
        write_str_lit(out, "executables");
        out.push(':');
        push_u64(out, program.executables.len() as u64);
    } else if let Some(step) =
        opaque.downcast_ref::<crate::compiler2::AppliedStep<crate::compiler2::Job, crate::compiler2::FactKey>>()
    {
        out.push(',');
        write_str_lit(out, "changed");
        out.push(':');
        push_u64(out, step.changed.len() as u64);
        out.push(',');
        write_str_lit(out, "enqueued");
        out.push(':');
        push_u64(out, step.enqueued.len() as u64);
        out.push(',');
        write_str_lit(out, "blocked");
        out.push(':');
        out.push('[');
        let mut blocked = step
            .blocked
            .iter()
            .map(|wait| fact_kind(wait.fact()))
            .collect::<Vec<_>>();
        blocked.sort_unstable();
        for (index, kind) in blocked.iter().enumerate() {
            if index > 0 {
                out.push(',');
            }
            write_str_lit(out, kind);
        }
        out.push(']');
    } else if let Some(key) = opaque.downcast_ref::<crate::compiler2::ActivationKey>() {
        write_activation_key(out, key);
    } else if let Some(key) = opaque.downcast_ref::<crate::compiler2::CallSiteKey>() {
        out.push(',');
        write_str_lit(out, "callsite");
        out.push(':');
        push_u64(out, key.callsite.as_u32() as u64);
        write_activation_key(out, &key.activation);
    } else if let Some(function) = opaque.downcast_ref::<crate::compiler2::FunctionRef>() {
        out.push(',');
        write_str_lit(out, "module_id");
        out.push(':');
        push_u64(out, function.module.as_u32() as u64);
        out.push(',');
        write_str_lit(out, "name");
        out.push(':');
        write_str_lit(out, &function.name);
        out.push(',');
        write_str_lit(out, "arity");
        out.push(':');
        push_u64(out, function.arity as u64);
    } else if let Some(key) = opaque.downcast_ref::<crate::compiler2::ProductKey>() {
        out.push(',');
        write_str_lit(out, "kind");
        out.push(':');
        write_str_lit(out, key.kind());
    } else if let Some(wait) = opaque.downcast_ref::<crate::compiler2::PullWait>() {
        out.push(',');
        write_str_lit(out, "kind");
        out.push(':');
        write_str_lit(
            out,
            match wait {
                crate::compiler2::PullWait::Product(_) => "product",
                crate::compiler2::PullWait::Fact(_) => "fact",
            },
        );
    } else if let Some(waits) = opaque.downcast_ref::<Vec<crate::compiler2::PullWait>>() {
        out.push(',');
        write_str_lit(out, "count");
        out.push(':');
        push_u64(out, waits.len() as u64);
        out.push(',');
        write_str_lit(out, "kinds");
        out.push(':');
        out.push('[');
        let mut kinds = waits
            .iter()
            .map(|wait| match wait {
                crate::compiler2::PullWait::Product(key) => key.kind(),
                crate::compiler2::PullWait::Fact(fact) => fact_kind(fact.fact()),
            })
            .collect::<Vec<_>>();
        kinds.sort_unstable();
        for (index, kind) in kinds.iter().enumerate() {
            if index > 0 {
                out.push(',');
            }
            write_str_lit(out, kind);
        }
        out.push(']');
    } else if let Some(world) = opaque.downcast_ref::<crate::compiler2::World>() {
        let (codes, roots, frontier) = world.telemetry_counts();
        out.push(',');
        write_str_lit(out, "codes");
        out.push(':');
        push_u64(out, codes as u64);
        out.push(',');
        write_str_lit(out, "roots");
        out.push(':');
        push_u64(out, roots as u64);
        out.push(',');
        write_str_lit(out, "activation_frontier");
        out.push(':');
        push_u64(out, frontier as u64);
    } else if let Some(ty) = opaque.downcast_ref::<crate::compiler2::Ty>() {
        out.push(',');
        write_str_lit(out, "interned");
        out.push(':');
        write_str_lit(out, &format!("{ty:?}"));
    } else if let Some(types) = opaque.downcast_ref::<Vec<crate::compiler2::Ty>>() {
        out.push(',');
        write_str_lit(out, "values");
        out.push(':');
        write_str_lit(out, &format!("{types:?}"));
    } else if let Some(ty) = opaque.downcast_ref::<Option<crate::compiler2::Ty>>() {
        out.push(',');
        write_str_lit(out, "value");
        out.push(':');
        write_str_lit(out, &format!("{ty:?}"));
    } else if let Some(analysis) = opaque.downcast_ref::<crate::compiler2::ActivationAnalysis>() {
        out.push(',');
        write_str_lit(out, "value");
        out.push(':');
        write_str_lit(out, &format!("{analysis:?}"));
    } else if let Some(summary) = opaque.downcast_ref::<crate::compiler2::CallSiteSummary>() {
        out.push(',');
        write_str_lit(out, "value");
        out.push(':');
        write_str_lit(out, &format!("{summary:?}"));
    }
    out.push('}');
}

fn write_activation_key(out: &mut String, key: &crate::compiler2::ActivationKey) {
    out.push(',');
    write_str_lit(out, "root_id");
    out.push(':');
    push_u64(out, key.root.as_u32() as u64);
    out.push(',');
    write_str_lit(out, "function_id");
    out.push(':');
    push_u64(out, key.function.as_u32() as u64);
}

fn fact_kind(fact: &crate::compiler2::FactKey) -> &'static str {
    use crate::compiler2::FactKey;

    match fact {
        FactKey::CodeIndexed(_) => "CodeIndexed",
        FactKey::CodeScoped(_) => "CodeScoped",
        FactKey::ModuleIndexed(_) => "ModuleIndexed",
        FactKey::ModuleDefined(_) => "ModuleDefined",
        FactKey::ModuleInterface(_) => "ModuleInterface",
        FactKey::FunctionSource(_) => "FunctionSource",
        FactKey::FunctionSourceStash(_) => "FunctionSourceStash",
        FactKey::ExpandedFunctionSource(_) => "ExpandedFunctionSource",
        FactKey::TypeDefined(_) => "TypeDefined",
        FactKey::StructDefined(_) => "StructDefined",
        FactKey::ProtocolDispatch(_) => "ProtocolDispatch",
        FactKey::ProtocolImplProviders(_) => "ProtocolImplProviders",
        FactKey::FunctionDefined(_) => "FunctionDefined",
        FactKey::FunctionContract(_) => "FunctionContract",
        FactKey::LoweredBody(_) => "LoweredBody",
        FactKey::GuardDispatch(_) => "GuardDispatch",
        FactKey::EntryDispatch(_) => "EntryDispatch",
        FactKey::MacroExecutable(_) => "MacroExecutable",
        FactKey::Recursive(_) => "Recursive",
        FactKey::DispatchMask(_) => "DispatchMask",
        FactKey::RootEntry(_) => "RootEntry",
        FactKey::Activation(_) => "Activation",
        FactKey::ActivationInputs(_) => "ActivationInputs",
        FactKey::ActivationAnalyzed(_) => "ActivationAnalyzed",
        FactKey::ReturnType(_) => "ReturnType",
        FactKey::CallSiteTargets(_) => "CallSiteTargets",
        FactKey::CallSiteSummary(_) => "CallSiteSummary",
        FactKey::Executable(_) => "Executable",
        FactKey::BackendProgram(_) => "BackendProgram",
        FactKey::NativeProgram(_) => "NativeProgram",
    }
}

fn job_kind(job: &crate::compiler2::Job) -> &'static str {
    use crate::compiler2::Job;

    match job {
        Job::IndexCode(_) => "IndexCode",
        Job::ScopeCode(_) => "ScopeCode",
        Job::DefineModule(_) => "DefineModule",
        Job::DefineModuleInterface(_) => "DefineModuleInterface",
        Job::PublishFunctionSource(_) => "PublishFunctionSource",
        Job::ExpandFunctionSource(_) => "ExpandFunctionSource",
        Job::DefineFunction(_) => "DefineFunction",
        Job::DeriveTypeDef(_) => "DeriveTypeDef",
        Job::DeriveFunctionContract(_) => "DeriveFunctionContract",
        Job::LowerFunction(_) => "LowerFunction",
        Job::ReifyGuardDispatch(_) => "ReifyGuardDispatch",
        Job::PlanEntryDispatch(_) => "PlanEntryDispatch",
        Job::BuildMacroExecutable(_) => "BuildMacroExecutable",
        Job::DeriveRecursive(_) => "DeriveRecursive",
        Job::DeriveDispatchMask(_) => "DeriveDispatchMask",
        Job::SeedRoot(_) => "SeedRoot",
        Job::SeedActivation(_) => "SeedActivation",
        Job::AnalyzeActivation(_) => "AnalyzeActivation",
        Job::BuildBackendProduct(_) => "BuildBackendProduct",
        Job::LowerNativeProgram(_) => "LowerNativeProgram",
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
#[path = "jsonl_test.rs"]
mod jsonl_test;
