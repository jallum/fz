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

use std::any::Any;
#[cfg(test)]
use std::cell::Cell;
use std::cell::RefCell;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::rc::Rc;
use std::time::Instant;

use super::bus::ConfiguredTelemetry;
use super::event::{Measurements, Metadata};
use super::handler::{Event, EventKind, Handler};
use super::value::Value;

#[cfg(test)]
thread_local! {
    static CODEGEN_PROJECTIONS: Cell<u64> = const { Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_codegen_projection_count() {
    CODEGEN_PROJECTIONS.with(|count| count.set(0));
}

#[cfg(test)]
pub(crate) fn codegen_projection_count() -> u64 {
    CODEGEN_PROJECTIONS.with(Cell::get)
}

fn note_codegen_projection() {
    #[cfg(test)]
    CODEGEN_PROJECTIONS.with(|count| count.set(count.get() + 1));
}

pub struct JsonlBackend {
    writer: RefCell<Box<dyn Write>>,
    buffer: RefCell<Vec<u8>>,
    start: Instant,
    public_compiler2_trace: bool,
    buffered: bool,
}

impl JsonlBackend {
    pub fn new_file(path: &Path) -> std::io::Result<Self> {
        let f = File::create(path)?;
        Ok(Self {
            writer: RefCell::new(Box::new(f)),
            buffer: RefCell::new(Vec::with_capacity(64 * 1024)),
            start: Instant::now(),
            public_compiler2_trace: false,
            buffered: false,
        })
    }

    pub fn new_public_file(path: &Path) -> std::io::Result<Self> {
        let mut backend = Self::new_file(path)?;
        backend.public_compiler2_trace = true;
        backend.buffered = true;
        Ok(backend)
    }

    pub fn install(self, telemetry: &ConfiguredTelemetry) {
        let backend = Rc::new(self);
        let legacy = Rc::clone(&backend);
        telemetry.attach(&[], Box::new(move |event: &Event<'_, '_, '_>| legacy.handle(event)));
        Self::install_world_key::<crate::compiler2::CodeId>(
            telemetry,
            &backend,
            &["fz", "compiler2", "code", "submitted"],
            "code",
        );
        Self::install_world_key::<crate::compiler2::ActivationKey>(
            telemetry,
            &backend,
            &["fz", "compiler2"],
            "activation",
        );
        Self::install_world_key::<crate::compiler2::CallSiteKey>(telemetry, &backend, &["fz", "compiler2"], "callsite");
        Self::install_world_key::<crate::compiler2::FunctionId>(telemetry, &backend, &["fz", "compiler2"], "function");
        let module_backend = Rc::clone(&backend);
        telemetry.attach_raw_event2::<crate::compiler2::World, crate::compiler2::ModuleId, _>(
            &["fz", "compiler2"],
            move |name, span_id, parent_span_id, world, module| {
                let metadata = if name == ["fz", "compiler2", "protocol_dispatch", "defined"] {
                    crate::metadata! {
                        world: crate::telemetry::opaque(world),
                        protocol: crate::telemetry::opaque(module),
                    }
                } else {
                    crate::metadata! {
                        world: crate::telemetry::opaque(world),
                        module: crate::telemetry::opaque(module),
                    }
                };
                module_backend.handle_raw_event(name, span_id, parent_span_id, metadata);
            },
        );
        Self::install_world_key::<crate::compiler2::RootId>(telemetry, &backend, &["fz", "compiler2"], "root");
        Self::install_world_key::<crate::compiler2::TypeName>(telemetry, &backend, &["fz", "compiler2"], "name");
        Self::install_world_key::<crate::compiler2::JobCompletion>(
            telemetry,
            &backend,
            &["fz", "compiler2"],
            "completion",
        );
        let function_owner_backend = Rc::clone(&backend);
        telemetry.attach_raw_event3::<
            crate::compiler2::World,
            crate::compiler2::FunctionId,
            crate::compiler2::FunctionId,
            _,
        >(
            &["fz", "compiler2", "function", "defined"],
            move |name, span_id, parent_span_id, world, function, owner| {
                function_owner_backend.handle_raw_event(
                    name,
                    span_id,
                    parent_span_id,
                    crate::metadata! {
                        world: crate::telemetry::opaque(world),
                        function: crate::telemetry::opaque(function),
                        owner: crate::telemetry::opaque(owner),
                    },
                );
            },
        );
        let callback_backend = Rc::clone(&backend);
        telemetry
            .attach_raw_event3::<crate::compiler2::World, crate::compiler2::FunctionId, crate::compiler2::ModuleId, _>(
                &["fz", "compiler2", "protocol_callback", "defined"],
                move |name, span_id, parent_span_id, world, function, protocol| {
                    callback_backend.handle_raw_event(
                        name,
                        span_id,
                        parent_span_id,
                        crate::metadata! {
                            world: crate::telemetry::opaque(world),
                            function: crate::telemetry::opaque(function),
                            protocol: crate::telemetry::opaque(protocol),
                        },
                    );
                },
            );
        let protocol_impl_backend = Rc::clone(&backend);
        telemetry
            .attach_raw_event3::<crate::compiler2::World, crate::compiler2::ModuleId, crate::compiler2::ModuleId, _>(
                &["fz", "compiler2", "protocol_impl", "defined"],
                move |name, span_id, parent_span_id, world, protocol, target| {
                    protocol_impl_backend.handle_raw_event(
                        name,
                        span_id,
                        parent_span_id,
                        crate::metadata! {
                            world: crate::telemetry::opaque(world),
                            protocol: crate::telemetry::opaque(protocol),
                            target: crate::telemetry::opaque(target),
                        },
                    );
                },
            );
        Self::install_raw_value::<crate::compiler2::pull::PullSession>(
            telemetry,
            &backend,
            &["fz", "compiler2", "pull", "session", "finished"],
            "session",
        );
        Self::install_raw_value::<crate::compiler2::pull::ProductKey>(
            telemetry,
            &backend,
            &["fz", "compiler2", "pull", "product"],
            "product",
        );
        let product_backend = Rc::clone(&backend);
        telemetry.attach_raw_event2::<crate::compiler2::pull::ProductKey, crate::compiler2::pull::ProductValue, _>(
            &["fz", "compiler2", "pull", "product", "settled"],
            move |name, span_id, parent_span_id, product, value| {
                product_backend.handle_raw_event(
                    name,
                    span_id,
                    parent_span_id,
                    crate::metadata! {
                        product: crate::telemetry::opaque(product),
                        value: crate::telemetry::opaque(value),
                    },
                );
            },
        );
        let native_backend = Rc::clone(&backend);
        telemetry.attach_raw_event2::<crate::compiler2::RootId, crate::compiler2::BackendProgram, _>(
            &["fz", "compiler2", "native_program", "reusable_cons"],
            move |name, span_id, parent_span_id, root, program| {
                native_backend.handle_raw_event(
                    name,
                    span_id,
                    parent_span_id,
                    crate::metadata! {
                        root: crate::telemetry::opaque(root),
                        program: crate::telemetry::opaque(program),
                    },
                );
            },
        );
        Self::install_compiler_spans(telemetry, &backend);
        Self::install_remaining_raw_boundaries(telemetry, &backend);
    }

    fn handle_raw_event<'a>(&self, name: &[&'static str], span_id: u64, parent_span_id: u64, metadata: Metadata<'a>) {
        let measurements = Measurements::new();
        self.handle(&Event {
            name,
            kind: EventKind::Event,
            measurements: &measurements,
            metadata: &metadata,
            span_id,
            parent_span_id,
        });
    }

    fn handle_raw_span<'a>(
        &self,
        name: &[&'static str],
        kind: EventKind,
        span_id: u64,
        parent_span_id: u64,
        elapsed_ns: Option<u64>,
        metadata: Metadata<'a>,
    ) {
        let measurements = elapsed_ns.map_or_else(Measurements::new, |elapsed_ns| {
            crate::measurements! { elapsed_ns: elapsed_ns }
        });
        self.handle(&Event {
            name,
            kind,
            measurements: &measurements,
            metadata: &metadata,
            span_id,
            parent_span_id,
        });
    }

    fn install_compiler_spans(telemetry: &ConfiguredTelemetry, backend: &Rc<Self>) {
        let drive_start = Rc::clone(backend);
        let drive_stop = Rc::clone(backend);
        let drive_exception = Rc::clone(backend);
        telemetry.attach_raw_span0_1::<crate::compiler2::DriveOutcome<crate::compiler2::Job, crate::compiler2::FactKey>, _, _, _>(
            &["fz", "compiler2", "drive"],
            move |name, span_id, parent_span_id| {
                drive_start.handle_raw_span(
                    name,
                    EventKind::SpanStart,
                    span_id,
                    parent_span_id,
                    None,
                    Metadata::new(),
                );
            },
            move |name, span_id, parent_span_id, elapsed_ns, outcome| {
                drive_stop.handle_raw_span(
                    name,
                    EventKind::SpanStop,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    crate::metadata! { outcome: crate::telemetry::opaque(outcome) },
                );
            },
            move |name, span_id, parent_span_id, elapsed_ns| {
                drive_exception.handle_raw_span(
                    name,
                    EventKind::SpanException,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    Metadata::new(),
                );
            },
        );
        let job_start = Rc::clone(backend);
        let job_stop = Rc::clone(backend);
        let job_exception = Rc::clone(backend);
        telemetry.attach_raw_span1_2::<crate::compiler2::Job, crate::compiler2::World, crate::compiler2::JobCompletion, _, _, _>(
            &["fz", "compiler2", "job"],
            move |name, span_id, parent_span_id, job| {
                job_start.handle_raw_span(
                    name,
                    EventKind::SpanStart,
                    span_id,
                    parent_span_id,
                    None,
                    crate::metadata! { job: crate::telemetry::opaque(job) },
                );
            },
            move |name, span_id, parent_span_id, elapsed_ns, world, completion| {
                job_stop.handle_raw_span(
                    name,
                    EventKind::SpanStop,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    crate::metadata! {
                        world: crate::telemetry::opaque(world),
                        completion: crate::telemetry::opaque(completion),
                    },
                );
            },
            move |name, span_id, parent_span_id, elapsed_ns| {
                job_exception.handle_raw_span(
                    name,
                    EventKind::SpanException,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    Metadata::new(),
                );
            },
        );
    }

    fn install_remaining_raw_boundaries(telemetry: &ConfiguredTelemetry, backend: &Rc<Self>) {
        Self::install_raw_value::<crate::diag::Diagnostic>(telemetry, backend, &["fz", "diag"], "diagnostic");
        Self::install_raw_value::<std::time::Duration>(
            telemetry,
            backend,
            &["fz", "compiler2", "drive", "timed_out"],
            "timeout",
        );
        let timeout_backend = Rc::clone(backend);
        telemetry.attach_raw_event1::<Option<std::time::Duration>, _>(
            &["fz", "compiler2", "drive", "timed_out"],
            move |name, span_id, parent_span_id, timeout| {
                timeout_backend.handle_raw_event(
                    name,
                    span_id,
                    parent_span_id,
                    crate::metadata! { timeout: crate::telemetry::opaque(timeout) },
                );
            },
        );
        let stall_backend = Rc::clone(backend);
        telemetry.attach_raw_event2::<usize, std::collections::HashSet<crate::compiler2::FactKey>, _>(
            &["fz", "compiler2", "drive", "demand_on_stall"],
            move |name, span_id, parent_span_id, producer_pokes, demanded_facts| {
                stall_backend.handle_raw_event(
                    name,
                    span_id,
                    parent_span_id,
                    crate::metadata! {
                        producer_pokes: *producer_pokes,
                        demanded_facts: crate::telemetry::opaque(demanded_facts),
                    },
                );
            },
        );
        let mask_backend = Rc::clone(backend);
        telemetry.attach_raw_event2::<crate::compiler2::FunctionId, Vec<crate::compiler2::DispatchDemand>, _>(
            &["fz", "compiler2", "dispatch_mask", "derived"],
            move |name, span_id, parent_span_id, function, mask| {
                mask_backend.handle_raw_event(
                    name,
                    span_id,
                    parent_span_id,
                    crate::metadata! {
                        function: crate::telemetry::opaque(function),
                        mask: crate::telemetry::opaque(mask),
                    },
                );
            },
        );
        let service_backend = Rc::clone(backend);
        telemetry.attach_raw_event3::<crate::compiler2::World, crate::compiler2::FunctionId, crate::compiler2::FunctionSource, _>(
            &["fz", "compiler2", "compiler_service", "define"],
            move |name, span_id, parent_span_id, world, function, source| {
                service_backend.handle_raw_event(name, span_id, parent_span_id, crate::metadata! {
                    origin: "fz_compiler",
                    world: crate::telemetry::opaque(world),
                    function: crate::telemetry::opaque(function),
                    source: crate::telemetry::opaque(source),
                });
            },
        );
        let macro_backend = Rc::clone(backend);
        telemetry.attach_raw_event3::<crate::compiler2::World, crate::compiler2::FunctionId, crate::compiler2::QuotedSourceRoot, _>(
            &["fz", "compiler2", "macro", "expanded"],
            move |name, span_id, parent_span_id, world, function, output| {
                macro_backend.handle_raw_event(name, span_id, parent_span_id, crate::metadata! {
                    world: crate::telemetry::opaque(world),
                    function: crate::telemetry::opaque(function),
                    output: crate::telemetry::opaque(output),
                });
            },
        );
        let exit_backend = Rc::clone(backend);
        telemetry.attach_raw_event2::<crate::ir_codegen::PidId, fz_runtime::process::Process, _>(
            &["fz", "runtime", "process_exited"],
            move |name, span_id, parent_span_id, pid, process| {
                exit_backend.handle_raw_event(
                    name,
                    span_id,
                    parent_span_id,
                    crate::metadata! {
                        pid: *pid,
                        process: crate::telemetry::opaque(process),
                    },
                );
            },
        );
        Self::install_raw_value::<crate::ir_codegen::PidId>(
            telemetry,
            backend,
            &["fz", "runtime", "send_to_unknown_pid"],
            "pid",
        );
        let tokens_backend = Rc::clone(backend);
        telemetry
            .attach_raw_event3::<crate::source::Id, Option<std::rc::Rc<str>>, Vec<crate::parser::lexer::Token>, _>(
                &["fz", "lexer", "tokens_built"],
                move |name, span_id, parent_span_id, code, source_name, tokens| {
                    tokens_backend.handle_raw_event(
                        name,
                        span_id,
                        parent_span_id,
                        crate::metadata! {
                            code: crate::telemetry::opaque(code),
                            source_name: crate::telemetry::opaque(source_name),
                            tokens: crate::telemetry::opaque(tokens),
                        },
                    );
                },
            );
        Self::install_raw_span2_0::<crate::source::Id, Option<std::rc::Rc<str>>>(
            telemetry,
            backend,
            &["fz", "lexer", "pass"],
            "code",
            "source_name",
        );
        Self::install_raw_span1_0::<crate::compiler2::NativeProgram>(
            telemetry,
            backend,
            &["fz", "compiler2", "native_backend", "compile"],
            "program",
        );
        Self::install_raw_span1_0::<crate::ir_codegen::AotArtifact>(
            telemetry,
            backend,
            &["fz", "compiler2", "aot", "write_object"],
            "artifact",
        );
        let archive_start = Rc::clone(backend);
        let archive_stop = Rc::clone(backend);
        let archive_exception = Rc::clone(backend);
        telemetry.attach_raw_span0_1::<crate::aot_link::RuntimeArchiveSource, _, _, _>(
            &["fz", "compiler2", "aot", "resolve_runtime_archive"],
            move |name, span_id, parent_span_id| {
                archive_start.handle_raw_span(
                    name,
                    EventKind::SpanStart,
                    span_id,
                    parent_span_id,
                    None,
                    Metadata::new(),
                )
            },
            move |name, span_id, parent_span_id, elapsed_ns, source| {
                archive_stop.handle_raw_span(
                    name,
                    EventKind::SpanStop,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    crate::metadata! { source: crate::telemetry::opaque(source) },
                )
            },
            move |name, span_id, parent_span_id, elapsed_ns| {
                archive_exception.handle_raw_span(
                    name,
                    EventKind::SpanException,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    Metadata::new(),
                )
            },
        );
        Self::install_raw_span1_0::<crate::ir_codegen::AotArtifact>(
            telemetry,
            backend,
            &["fz", "compiler2", "aot", "link"],
            "artifact",
        );
        Self::install_raw_span1_0::<crate::fz_ir::Module>(telemetry, backend, &["fz", "codegen", "compile"], "module");
        Self::install_raw_span1_0::<crate::fz_ir::Module>(telemetry, backend, &["fz", "codegen", "declare"], "module");
        Self::install_raw_span1_0::<crate::fz_ir::Module>(
            telemetry,
            backend,
            &["fz", "codegen", "emit_runtime"],
            "module",
        );
        Self::install_raw_span1_0::<crate::fz_ir::Module>(telemetry, backend, &["fz", "codegen", "finalize"], "module");
        Self::install_raw_span2_0::<crate::fz_ir::Module, crate::fz_ir::FnId>(
            telemetry,
            backend,
            &["fz", "codegen", "lower_function"],
            "module",
            "function",
        );
        Self::install_raw_span1_1::<crate::fz_ir::FnId, cranelift_codegen::Context>(
            telemetry,
            backend,
            &["fz", "codegen", "define_function"],
            "function",
            "context",
        );
    }

    fn install_raw_span1_0<S: Any>(
        telemetry: &ConfiguredTelemetry,
        backend: &Rc<Self>,
        prefix: &[&'static str],
        start_name: &'static str,
    ) {
        let start = Rc::clone(backend);
        let stop = Rc::clone(backend);
        let exception = Rc::clone(backend);
        telemetry.attach_raw_span1_0::<S, _, _, _>(
            prefix,
            move |name, span_id, parent_span_id, value| {
                start.handle_raw_span(
                    name,
                    EventKind::SpanStart,
                    span_id,
                    parent_span_id,
                    None,
                    Metadata::from_pairs([(start_name, crate::telemetry::opaque(value))]),
                )
            },
            move |name, span_id, parent_span_id, elapsed_ns| {
                stop.handle_raw_span(
                    name,
                    EventKind::SpanStop,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    Metadata::new(),
                )
            },
            move |name, span_id, parent_span_id, elapsed_ns| {
                exception.handle_raw_span(
                    name,
                    EventKind::SpanException,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    Metadata::new(),
                )
            },
        );
    }

    fn install_raw_span2_0<A: Any, B: Any>(
        telemetry: &ConfiguredTelemetry,
        backend: &Rc<Self>,
        prefix: &[&'static str],
        a_name: &'static str,
        b_name: &'static str,
    ) {
        let start = Rc::clone(backend);
        let stop = Rc::clone(backend);
        let exception = Rc::clone(backend);
        telemetry.attach_raw_span2_0::<A, B, _, _, _>(
            prefix,
            move |name, span_id, parent_span_id, a, b| {
                start.handle_raw_span(
                    name,
                    EventKind::SpanStart,
                    span_id,
                    parent_span_id,
                    None,
                    Metadata::from_pairs([
                        (a_name, crate::telemetry::opaque(a)),
                        (b_name, crate::telemetry::opaque(b)),
                    ]),
                )
            },
            move |name, span_id, parent_span_id, elapsed_ns| {
                stop.handle_raw_span(
                    name,
                    EventKind::SpanStop,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    Metadata::new(),
                )
            },
            move |name, span_id, parent_span_id, elapsed_ns| {
                exception.handle_raw_span(
                    name,
                    EventKind::SpanException,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    Metadata::new(),
                )
            },
        );
    }

    fn install_raw_span1_1<S: Any, P: Any>(
        telemetry: &ConfiguredTelemetry,
        backend: &Rc<Self>,
        prefix: &[&'static str],
        start_name: &'static str,
        stop_name: &'static str,
    ) {
        let start = Rc::clone(backend);
        let stop = Rc::clone(backend);
        let exception = Rc::clone(backend);
        telemetry.attach_raw_span1_1::<S, P, _, _, _>(
            prefix,
            move |name, span_id, parent_span_id, value| {
                start.handle_raw_span(
                    name,
                    EventKind::SpanStart,
                    span_id,
                    parent_span_id,
                    None,
                    Metadata::from_pairs([(start_name, crate::telemetry::opaque(value))]),
                )
            },
            move |name, span_id, parent_span_id, elapsed_ns, value| {
                stop.handle_raw_span(
                    name,
                    EventKind::SpanStop,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    Metadata::from_pairs([(stop_name, crate::telemetry::opaque(value))]),
                )
            },
            move |name, span_id, parent_span_id, elapsed_ns| {
                exception.handle_raw_span(
                    name,
                    EventKind::SpanException,
                    span_id,
                    parent_span_id,
                    Some(elapsed_ns),
                    Metadata::new(),
                )
            },
        );
    }

    fn install_world_key<K: Any>(
        telemetry: &ConfiguredTelemetry,
        backend: &Rc<Self>,
        prefix: &[&'static str],
        key_name: &'static str,
    ) {
        let backend = Rc::clone(backend);
        telemetry.attach_raw_event2::<crate::compiler2::World, K, _>(
            prefix,
            move |name, span_id, parent_span_id, world, key| {
                backend.handle_raw_event(
                    name,
                    span_id,
                    parent_span_id,
                    Metadata::from_pairs([
                        ("world", crate::telemetry::opaque(world)),
                        (key_name, crate::telemetry::opaque(key)),
                    ]),
                );
            },
        );
    }

    fn install_raw_value<K: Any>(
        telemetry: &ConfiguredTelemetry,
        backend: &Rc<Self>,
        prefix: &[&'static str],
        key_name: &'static str,
    ) {
        let backend = Rc::clone(backend);
        telemetry.attach_raw_event1::<K, _>(prefix, move |name, span_id, parent_span_id, value| {
            backend.handle_raw_event(
                name,
                span_id,
                parent_span_id,
                Metadata::from_pairs([(key_name, crate::telemetry::opaque(value))]),
            );
        });
    }

    #[cfg(test)]
    pub fn new_writer(w: impl Write + 'static) -> Self {
        Self {
            writer: RefCell::new(Box::new(w)),
            buffer: RefCell::new(Vec::with_capacity(64 * 1024)),
            start: Instant::now(),
            public_compiler2_trace: false,
            buffered: false,
        }
    }

    #[cfg(test)]
    pub fn new_public_writer(w: impl Write + 'static) -> Self {
        let mut backend = Self::new_writer(w);
        backend.public_compiler2_trace = true;
        backend.buffered = true;
        backend
    }
}

impl Handler for JsonlBackend {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        if self.public_compiler2_trace && !is_public_compiler2_trace_event(ev) {
            return;
        }
        let time_ns = self.start.elapsed().as_nanos().min(u64::MAX as u128) as u64;
        let mut buf = String::with_capacity(128);
        write_event(&mut buf, ev, time_ns);
        buf.push('\n');
        let mut buffer = self.buffer.borrow_mut();
        buffer.extend_from_slice(buf.as_bytes());
        if !self.buffered || buffer.len() >= 64 * 1024 {
            let mut writer = self.writer.borrow_mut();
            write_buffer(&mut **writer, &mut buffer);
        }
    }
}

impl JsonlBackend {
    #[cfg(test)]
    pub fn flush(&self) {
        let mut buffer = self.buffer.borrow_mut();
        {
            let mut writer = self.writer.borrow_mut();
            write_buffer(&mut **writer, &mut buffer);
        }
        let _ = self.writer.borrow_mut().flush();
    }
}

impl Drop for JsonlBackend {
    fn drop(&mut self) {
        let buffer = self.buffer.get_mut();
        write_buffer(self.writer.get_mut(), buffer);
        let _ = self.writer.get_mut().flush();
    }
}

fn write_buffer(writer: &mut dyn Write, buffer: &mut Vec<u8>) {
    while !buffer.is_empty() {
        match writer.write(buffer) {
            Ok(0) | Err(_) => break,
            Ok(written) => {
                buffer.drain(..written);
            }
        }
    }
}

fn is_public_compiler2_trace_event(ev: &Event<'_, '_, '_>) -> bool {
    if !ev.name.starts_with(&["fz", "compiler2"]) {
        return true;
    }
    matches!(
        ev.name,
        ["fz", "compiler2", "pull", "session", ..]
            | ["fz", "compiler2", "pull", "phase", ..]
            | ["fz", "compiler2", "pull", "product", "settled"]
            | ["fz", "compiler2", "work", "started"]
            | ["fz", "compiler2", "drive", "stalled"]
            | ["fz", "compiler2", "drive", "timed_out"]
            | ["fz", "compiler2", "job"]
            | ["fz", "compiler2", "backend_program", "defined"]
            | ["fz", "compiler2", "native_program", "defined"]
            | ["fz", "compiler2", "native_program", "reusable_cons"]
            | ["fz", "compiler2", "native_backend", ..]
            | ["fz", "compiler2", "aot", ..]
    )
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
    if ev.name == ["fz", "compiler2", "activation_inputs", "defined"] {
        let Some(completion) = ev
            .metadata
            .get("completion")
            .and_then(Value::downcast_ref::<crate::compiler2::JobCompletion>)
        else {
            return;
        };
        let mut activations = completion.activation_input_changed.iter().collect::<Vec<_>>();
        activations.sort_by_key(|activation| format!("{activation:?}"));
        out.push_str(",\"semantic\":{\"activations\":[");
        for (index, activation) in activations.into_iter().enumerate() {
            if index > 0 {
                out.push(',');
            }
            out.push_str("{\"activation\":");
            write_activation_key(out, activation);
            if let Some(alternatives) = world.activation_input_alternatives(activation) {
                out.push_str(",\"rows\":[");
                for (row_index, row) in alternatives.rows().iter().enumerate() {
                    if row_index > 0 {
                        out.push(',');
                    }
                    write_types(out, world, row.columns());
                }
                out.push(']');
            }
            out.push('}');
        }
        out.push_str("]}");
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
        ["fz", "compiler2", "return_type", "defined"] => {
            out.push_str(",\"semantic\":{\"return\":");
            write_optional_type(out, world, world.activation_return_evidence(activation));
            out.push('}');
        }
        ["fz", "compiler2", "activation_analysis", "defined"] => {
            if let Some(analysis) = world.activation_analysis(activation) {
                out.push_str(",\"semantic\":{\"reachable_clauses\":");
                push_u64(out, analysis.entry_reachability.clauses().len() as u64);
                out.push_str(",\"fail_reachable\":");
                out.push_str(if analysis.entry_reachability.fail_reachable() {
                    "true"
                } else {
                    "false"
                });
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
        Value::BorrowedBytes(bytes) => write_str_lit(out, std::str::from_utf8(bytes).unwrap_or("<non-utf8 bytes>")),
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
    } else if let Some(outcome) =
        opaque.downcast_ref::<crate::compiler2::DriveOutcome<crate::compiler2::Job, crate::compiler2::FactKey>>()
    {
        out.push(',');
        write_str_lit(out, "status");
        out.push(':');
        match outcome {
            crate::compiler2::DriveOutcome::Resolved => write_str_lit(out, "resolved"),
            crate::compiler2::DriveOutcome::Unresolved { waits } => {
                write_str_lit(out, "unresolved");
                out.push(',');
                write_str_lit(out, "wait_count");
                out.push(':');
                push_u64(out, waits.len() as u64);
            }
            crate::compiler2::DriveOutcome::Fatal { job } => {
                write_str_lit(out, "fatal");
                out.push(',');
                write_str_lit(out, "job_kind");
                out.push(':');
                write_str_lit(out, job_kind(job));
            }
            crate::compiler2::DriveOutcome::TimedOut { jobs_ran, pending_jobs } => {
                write_str_lit(out, "timed_out");
                out.push(',');
                write_str_lit(out, "jobs_ran");
                out.push(':');
                push_u64(out, *jobs_ran);
                out.push(',');
                write_str_lit(out, "pending_jobs");
                out.push(':');
                push_u64(out, *pending_jobs as u64);
            }
        }
    } else if let Some(diagnostic) = opaque.downcast_ref::<crate::diag::Diagnostic>() {
        out.push(',');
        write_str_lit(out, "severity");
        out.push(':');
        write_str_lit(
            out,
            match diagnostic.severity {
                crate::diag::diagnostic::Severity::Error => "error",
                crate::diag::diagnostic::Severity::Warning => "warning",
            },
        );
        out.push(',');
        write_str_lit(out, "code");
        out.push(':');
        write_str_lit(out, diagnostic.code.0);
        out.push(',');
        write_str_lit(out, "message");
        out.push(':');
        write_str_lit(out, &diagnostic.message);
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
        let (birth_count, transport_count) = reusable_cons_counts(program);
        out.push(',');
        write_str_lit(out, "backend_revision");
        out.push(':');
        push_u64(out, program.backend_revision);
        out.push(',');
        write_str_lit(out, "executables");
        out.push(':');
        push_u64(out, program.executables.len() as u64);
        out.push(',');
        write_str_lit(out, "birth_count");
        out.push(':');
        push_u64(out, birth_count);
        out.push(',');
        write_str_lit(out, "transport_count");
        out.push(':');
        push_u64(out, transport_count);
    } else if let Some(session) = opaque.downcast_ref::<crate::compiler2::PullSession>() {
        let work_starts = session.work_starts();
        for (name, value) in [
            ("producer_pokes", session.producer_pokes()),
            ("work_starts_ignition", work_starts.ignition),
            ("work_starts_changed_revision_wake", work_starts.changed_revision_wake),
            ("work_starts_standing_root_frontier", work_starts.standing_root_frontier),
            ("work_starts_activation_frontier", work_starts.activation_frontier),
            (
                "work_starts_blocked_waiter_expansion",
                work_starts.blocked_waiter_expansion,
            ),
            ("unsanctioned_work_starts", work_starts.unclassified),
            ("root_scans", work_starts.root_scans),
        ] {
            out.push(',');
            write_str_lit(out, name);
            out.push(':');
            push_u64(out, value);
        }
    } else if let Some(context) = opaque.downcast_ref::<cranelift_codegen::Context>() {
        note_codegen_projection();
        out.push(',');
        write_str_lit(out, "code_bytes");
        out.push(':');
        let code_bytes = context
            .compiled_code()
            .map(|code| code.code_buffer().len() as u64)
            .unwrap_or(0);
        push_u64(out, code_bytes);
    } else if let Some(process) = opaque.downcast_ref::<fz_runtime::process::Process>() {
        for (name, value) in [
            ("live_count", process.heap.live_count() as u64),
            ("bytes_used", process.heap.bytes_used() as u64),
            ("reusable_cons_attempts", process.reusable_cons_attempts),
            ("reusable_cons_reused", process.reusable_cons_reused),
        ] {
            out.push(',');
            write_str_lit(out, name);
            out.push(':');
            push_u64(out, value);
        }
        out.push(',');
        write_str_lit(out, "halt_value");
        out.push(':');
        push_i64(out, process.halt_value);
    } else if let Some(code) = opaque.downcast_ref::<crate::source::Id>() {
        out.push(',');
        write_str_lit(out, "code_id");
        out.push(':');
        push_u64(out, code.0 as u64);
    } else if let Some(source_name) = opaque.downcast_ref::<Option<std::rc::Rc<str>>>() {
        if let Some(source_name) = source_name {
            out.push(',');
            write_str_lit(out, "source_name");
            out.push(':');
            write_str_lit(out, source_name);
        }
    } else if let Some(tokens) = opaque.downcast_ref::<Vec<crate::parser::lexer::Token>>() {
        out.push(',');
        write_str_lit(out, "count");
        out.push(':');
        push_u64(out, tokens.len() as u64);
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
    } else if let Some(outcome) = opaque.downcast_ref::<crate::compiler2::pull::PullOutcome>() {
        out.push(',');
        write_str_lit(out, "status");
        out.push(':');
        match outcome {
            crate::compiler2::pull::PullOutcome::Produced(_) => {
                write_str_lit(out, "produced");
                out.push(',');
                write_str_lit(out, "wait_count");
                out.push(':');
                push_u64(out, 0);
            }
            crate::compiler2::pull::PullOutcome::Waiting(waits) => {
                write_str_lit(out, "waiting");
                out.push(',');
                write_str_lit(out, "wait_count");
                out.push(':');
                push_u64(out, waits.len() as u64);
                out.push(',');
                write_str_lit(out, "wait_kinds");
                out.push(':');
                out.push('[');
                let mut kinds = waits
                    .iter()
                    .map(|wait| match wait {
                        crate::compiler2::pull::PullWait::Product(key) => key.kind(),
                        crate::compiler2::pull::PullWait::Fact(fact) => fact_kind(fact.fact()),
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
            }
        }
    } else if let Some(timeout) = opaque.downcast_ref::<Option<std::time::Duration>>() {
        out.push(',');
        write_str_lit(out, "timeout_ms");
        out.push(':');
        push_u64(
            out,
            timeout.map_or(0, |duration| duration.as_millis().min(u64::MAX as u128) as u64),
        );
    } else if let Some(source) = opaque.downcast_ref::<crate::aot_link::RuntimeArchiveSource>() {
        out.push(',');
        write_str_lit(out, "source");
        out.push(':');
        write_str_lit(
            out,
            match source {
                crate::aot_link::RuntimeArchiveSource::EnvOverride => "override",
                crate::aot_link::RuntimeArchiveSource::Embedded => "embedded",
                crate::aot_link::RuntimeArchiveSource::IsolatedCoverageBuild => "isolated_coverage_build",
            },
        );
    } else if let Some(completion) = opaque.downcast_ref::<crate::compiler2::JobCompletion>() {
        out.push(',');
        write_str_lit(out, "kind");
        out.push(':');
        write_str_lit(out, job_kind(&completion.job));
        out.push(',');
        write_str_lit(out, "rebased");
        out.push(':');
        out.push_str(if completion.rebased { "true" } else { "false" });
        out.push(',');
        write_str_lit(out, "changed");
        out.push(':');
        push_u64(out, completion.step.changed.len() as u64);
        out.push(',');
        write_str_lit(out, "enqueued");
        out.push(':');
        push_u64(out, completion.step.enqueued.len() as u64);
        out.push(',');
        write_str_lit(out, "blocked");
        out.push(':');
        out.push('[');
        let mut blocked = completion
            .step
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

fn reusable_cons_counts(program: &crate::compiler2::BackendProgram) -> (u64, u64) {
    let mut birth_count = 0;
    let mut transport_count = 0;
    for executable in &program.executables {
        let crate::compiler2::BackendBody::Clauses { clauses, entries, .. } = &executable.body else {
            continue;
        };
        for clause in clauses {
            birth_count += clause
                .projections
                .iter()
                .filter(|step| matches!(step, crate::compiler2::BackendStep::SplitList { .. }))
                .count() as u64;
        }
        for entry in entries {
            birth_count += entry
                .steps
                .iter()
                .filter(|step| matches!(step, crate::compiler2::BackendStep::SplitList { .. }))
                .count() as u64;
            transport_count += entry.reusable_cons_captures.len() as u64;
        }
    }
    (birth_count, transport_count)
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
