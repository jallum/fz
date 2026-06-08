# Telemetry

Compile-time telemetry is the compiler's observability bus. Every output that is
not control flow — diagnostics, pass spans, counters, IR dumps, internal markers
— flows through it as an event. Fatal errors do **not**: they stay on
`Result<T, FatalError>`. Telemetry is the side channel; the `Result` is the
answer.

The compiler depends on one thing: the `Telemetry` trait (`sink.rs`). It threads
`&dyn Telemetry` through the whole pipeline and calls `execute`/`span` on it. Who
is listening, and what they do with the events, is none of the compiler's
business.

This doc covers compile-time telemetry. The running scheduler's events — process
exit, `dbg` output, how tests observe a run — live in
[`runtime-telemetry`](runtime-telemetry.md).

## The Pieces

**`Telemetry` trait** (`sink.rs`) — the compiler-facing surface. Four methods:
`execute(name, measurements, metadata)` emits one event; `span_start` /
`span_stop` / `span_exception` bracket a timed region. `emit(name)` and
`event(name, metadata)` are payload-free conveniences. `name` is a
`&[&'static str]` path like `&["fz", "lexer", "tokens_built"]` — broad to
specific.

**Silence by configuration** — there is no separate no-op telemetry type.
Callers still thread a real `&dyn Telemetry` through the pipeline; when they want
no observable output they instantiate a `ConfiguredTelemetry` and attach no
handlers. That keeps one observability path across production, tests, and
interactive tooling.

**`ConfiguredTelemetry`** (`bus.rs`) — the listening impl the driver
instantiates. It owns a handler registry (`Vec<Entry>`, each entry a `prefix` +
boxed `Handler`), a `span_stack`, and monotonic `next_handler_id` /
`next_span_id` counters. It is single-threaded by design — `RefCell` interior
mutability, no `Send`/`Sync`. The CLI driver and each test root own their own
bus.

**`Handler` trait** (`handler.rs`) — a subscriber: `handle(&Event)`. The bus
routes an event to a handler when `name.starts_with(handler.prefix)`; the empty
prefix `&[]` matches everything. Concrete handlers:

- `DiagRenderer` (`diag_render.rs`) — events under `[fz, diag]` carrying a
  `Diagnostic` in their metadata; it downcasts and hands them to
  `diag::render::Renderer` for stderr/writer output.
- `JsonlBackend` (`jsonl.rs`) — serializes every routed event to one JSON line.
- `StatsHandler` (`stats.rs`) — counts events by name.
- `Capture` (`capture.rs`) — the test handler; copies events into an owned
  buffer for assertions. Gated behind `#[cfg(test)]`.

**`Event`** (`handler.rs`) — the borrowed view a handler receives: `name`,
`kind`, `measurements`, `metadata`, `span_id`, `parent_span_id`. A handler that
keeps an event past the call must clone it into owned form.

**`EventKind`** (`handler.rs`) — `Event` for user emits, plus `SpanStart` /
`SpanStop` / `SpanException` for the synthetic events a span's lifecycle emits.
`is_span()` is true for the three span kinds. The kind rides on the event so
handlers match the structural `name` without the bus mangling a suffix into it.

**`Measurements` and `Metadata`** (`event.rs`) — both are the same shape, a
`SmallVec<[(&'static str, Value); 4]>` built by the `kv_newtype!` macro, but they
stay distinct types so emit sites and handlers can tell numbers apart from
context without convention. The `measurements! { count: 3, ns: 1421 }` and
`metadata! { fn_name: "foo" }` macros build them. Inline storage means ≤ 4
entries never heap-allocate.

**`Value`** (`value.rs`) — the typed cell inside a payload: `I64`, `U64`, `F64`,
`Bool`, `Str(Cow)`, `StrSeq(Arc<[String]>)`, `Bytes(Arc<[u8]>)`, and
`Opaque(OpaqueRef)`. `From` impls cover the primitives and string/byte forms so
macro authors write `Value::from(expr)` blind to the concrete type. `Opaque`
wraps an event-scoped `&dyn Any` with its `type_name`; a handler recovers it with
`downcast_ref::<T>()`. This is how `DiagRenderer` pulls a whole `Diagnostic` out
of metadata without flattening it to a string.

## Dataflow

```text
pass code                bus                       handlers
---------                ---                       --------
tel.execute(name, m, md) ── dispatch ──▶ for each entry where
                                          name.starts_with(prefix):
                                            handler.handle(&Event{ .. })
```

The bus borrows its handler list immutably for the whole dispatch, so a handler
that attaches or detaches mid-dispatch panics on the re-borrow — that is a
programmer error, not a case the bus defends against.

## Spans

A span is a timed region whose child events know their parent. `TelemetryExt`
(`sink.rs`) gives `t.span(name, metadata)` on any `&dyn Telemetry` and returns an
RAII `Span` guard. Construction calls `span_start` (which pushes a fresh id onto
the bus's `span_stack` and emits a `SpanStart`); `Drop` measures `elapsed_ns` and
emits `SpanStop`, or `SpanException` when the scope is unwinding from a panic
(`panicking()`).

While a span is open it sits on the `span_stack`, so every `execute` during that
region carries the span's id as `span_id` and the enclosing span as
`parent_span_id`. `close_span` pops LIFO but tolerates any position so a panic
unwinding several layers still closes cleanly. The pop happens after dispatch, so
a handler peeking at the stack still sees the closing span as open.

```text
tel.span(["fz","compile"], { compile_nonce, module_path })
  span_start → SpanStart(id=7, parent=0)
  ... lexer/parser/lowering emit events tagged span_id=7 ...
  Drop → SpanStop(id=7, elapsed_ns=…)
```

The `["fz", "compile"]` span is real: `next_compile_nonce()` (`mod.rs`) hands out
a process-unique id, and the driver opens this span with `compile_nonce` plus
`module_path`/`source_name` metadata around each compilation. That makes the
compile/run boundary explicit, so child events can carry cheap module-local ids
(`FnId`, `SpecId`, `BlockId`) without pretending those numbers mean anything
across separate compiles — the enclosing `compile_nonce` disambiguates them.

## Policy Choices

**Fatal vs telemetry.** A failure that must stop compilation returns
`Err(FatalError)`. Everything observational — including diagnostics that get
rendered as user errors — is an event. So the trait has no fallible method: a
handler cannot change what the compiler computes.

**Measurements vs metadata.** Numbers an aggregator might sum go in
measurements; identity and reasons (names, paths, kinds, the
why-was-this-pruned) go in metadata. They are the same storage but separate
types, so a counting handler never has to skip over a string field.

**Prefix routing.** A handler subscribes to a name prefix, not a single event.
`StatsHandler` on `&[]` sees everything; `DiagRenderer` on `[fz, diag]` sees only
diagnostics. Adding an event under an existing prefix needs no handler change.

**Stats counts decisions, not bookkeeping.** `StatsHandler` ignores any event
where `kind.is_span()` and counts only `EventKind::Event`, keyed by the
`.`-joined name in a `BTreeMap`. `print_summary()` writes the sorted table to
stderr; the driver calls it after a run.

**Jsonl is dependency-free and lossy on purpose.** `JsonlBackend` hand-rolls the
JSON and stamps each line with `time_ns`, a
monotonic offset from when the backend was constructed, so relative ordering is
trivial to profile. It drops `Opaque` values (no stable serialization), renders
`Bytes` as `"<N bytes>"` to keep lines ASCII, and renders non-finite floats as
`null`. A consumer needing binary round-trips uses a different channel.

**The bus is single-threaded.** No `Send`/`Sync`; the driver and each test hold
their own `ConfiguredTelemetry`. This is why handlers can share state through
plain `Rc<RefCell<…>>` (the pattern `Capture` and `StatsHandler` both use: keep
the typed object, attach a `handler()` that shares its buffer).

## Compiler2 Conventions

Compiler2 uses telemetry as its only observability surface. `Compiler2::new`
hands one caller-owned sink to `World`, and every job/event under
`[fz, compiler2, ...]` flows through that single bus.

**Emit raw compiler facts, not formatted strings.** Compiler2 emission sites
pass existing ids in measurements and existing compiler-owned structures in
metadata via `opaque(...)`: `Job`, `JobEffects`, `AppliedStep<Job, FactKey>`,
`FunctionRef`, `CallSiteSummary`, `SemanticClosure`, `MaterializedProgram`,
`AbiReadyProgram`, `EmissionReadyProgram`, `BackendProgram`, `Ty`, and
unresolved waits. If an emit site has to build a display string just for
telemetry, that is the wrong side of the boundary. The ignored JSONL harness in
`src/compiler2/telemetry_dump_test.rs` is the model: the handler decides how
to render opaque values, not the compiler.

**Slot revisions are the stable change signal.** Compiler2 state stores and fact
slots bump revisions only when their aggregate value changes. Handlers and
tests that care about "did this semantic thing actually change?" should key on
the reported revision or the published fact/output, not on the mere existence
of a repeated event. This matters most for joined facts like
`FactValue::Inputs(Vec<Ty>)`, callsite summaries, semantic closure, and
materialized programs.

**Local type ids are world-owned facts.** Compiler2 `Ty` values are interned
`u32` handles owned by `World.types`. They are valid only inside that one
compiler world. Telemetry therefore treats them like `FunctionId` or `ModuleId`:
cheap compiler-owned identity, never a printable semantic contract by itself.
If a handler wants a rendered type, it must derive that rendering on its side.

**Drive and job spans are the execution spine.** `World::drive()` opens one
`[fz, compiler2, drive]` span. Each popped job opens one
`[fz, compiler2, job]` span. Successful job spans close with raw `effects` and
the applied `work_graph` step in metadata; unresolved drives close with the raw
wait frontier; fatal drives close with the fatal job. There is no extra
"job_fatal" event and no redundant "fact_published" stream.

Artifact jobs lean on that raw `JobEffects` payload as a contract surface. The
tests assert that:

- `MaterializeRoot(root)` reads only `SemanticClosed(root)`
- `DeriveAbiReady(root)` reads only `MaterializedProgram(root)`
- `DeriveEmissionReady(root)` reads only `AbiReadyProgram(root)`
- `LowerBackendProgram(root)` reads only `EmissionReadyProgram(root)`
- `LowerNativeProgram(root)` reads only `BackendProgram(root)`

So a backend adapter that asks semantic, type, or reachability questions after
the artifact boundary is visible as the wrong `reads`/`waits` shape on the job
span, not just as a vague architectural complaint.

**Compiler2 tests should observe telemetry, not world internals.** The common
captures live in `src/compiler2/drive_test.rs` and assert on emitted
definitions, work-graph steps, callsite summaries, semantic closure, and the
full artifact ladder through `NativeProgram(root)`. The quicksort,
`Enum.reduce`, and variadic-extern contracts are the fast summary probe; the
shared-native JIT tests plus the `Compiler2::compile_root_jit` /
`compile_root_aot` front-door tests prove that Compiler2-native codegen does
not fall back to planner or type-preparation telemetry; the ignored JSONL dump
is the occasional deep trace.

Useful reruns:

- `cargo test --lib compiler2_ -- --nocapture`
- `cargo test --lib compiler2_quicksort_root_closes_with_a_finite_recursive_frontier -- --exact --nocapture`
- `cargo test --lib compiler2_materialization_projects_only_the_closed_quicksort_frontier -- --exact --nocapture`
- `cargo test --lib compiler2_enum_reduce_selects_list_protocol_impl_and_callable_reducer -- --exact --nocapture`
- `cargo test --lib compiler2_materialization_freezes_only_the_selected_enum_reduce_path -- --exact --nocapture`
- `cargo test --lib compiler2_artifact_ladder_consumes_only_the_previous_rung -- --exact --nocapture`
- `cargo test --lib compiler2_emission_ready_preserves_variadic_extern_inventory_and_marshals -- --exact --nocapture`
- `cargo test --lib compiler2_native_program_jit_runs_quicksort_through_shared_codegen -- --exact --nocapture`
- `cargo test --lib compiler2_native_program_jit_runs_enum_reduce_through_shared_codegen -- --exact --nocapture`
- `cargo test --lib compiler2_native_program_jit_runs_variadic_extern_through_shared_codegen -- --exact --nocapture`
- `cargo test --lib compiler2_compile_root_jit_consumes_native_program_without_legacy_prepare -- --exact --nocapture`
- `cargo test --lib compiler2_compile_root_aot_consumes_native_program_without_legacy_prepare -- --exact --nocapture`
- `cargo test --lib compiler2::telemetry_dump_test::dump_quicksort_compiler2_telemetry_to_jsonl -- --ignored --exact --nocapture`

The ignored harness writes its log to `/tmp/fz-compiler2-quicksort.jsonl`.

## Codegen Regression Events

Three codegen events carry stable enough fields to assert on in tests, proving
codegen consumed the ABI and callable-entry facts the planner handed it. They are
emitted for reachable specs / lowered sites and pair with CLIF or runtime checks
when the generated shape matters.

- `fz.codegen.abi_contract` (`ir_codegen/driver.rs`) — one per reachable lowered
  spec. Measurements: `spec_id`, `fn_id`, `param_count`, `capture_count`.
  Metadata: `module_path`, `fn_name`, `spec_key`, `param_reprs`, `return_repr`,
  and the `is_native` / `is_cont_fn` / `is_closure_target` flags.
- `fz.codegen.callable_entry_selected` (`ir_codegen/prim.rs`) — the site-specific
  callable entry chosen while lowering `MakeFnRef` / `MakeClosure`. Measurements
  include the active `spec_id`/`fn_id`, `closure_fn_id`, `capture_count`,
  `callable_entry_spec_id`, `block_id`, `stmt_idx`, source `span_start`/
  `span_end`, and `candidate_count`. Metadata includes `body_name`,
  `closure_fn_name`, `selection_kind`, and the planned vs selected spec keys.
- `fz.codegen.closure_call_lowered` (`ir_codegen/terminator.rs`) — one per
  `CallClosure` lowering. Measurements: active `spec_id`, `closure_var`,
  `continuation_spec_id`. Metadata: `body_name`, `call_kind`,
  `closure_binding_repr`, `dispatch_kind` (`direct` when the body literal
  resolves, else `indirect`), and `continuation_storage` (`lazy_descriptor` or
  `heap_closure`).

## Telemetry In Tests

The bus is the test seam for "did the compiler make the decision I expected?"
without `#[cfg(test)] pub` peepholes into pass internals. A test builds a
`ConfiguredTelemetry`, attaches a `Capture`, drives the smallest pipeline that
owns the behavior, then queries the captured stream:

```text
let tel = ConfiguredTelemetry::new();
let cap = Capture::new();
tel.attach(&[], cap.handler());
run_pass(&tel);
cap.count(&["fz", "ir", "dce", "block_pruned"])   // assert the pass fired
```

`Capture` offers `count`, `find` (prefix), `last`, `contains`, and
`count_by_kind`; events come back as `OwnedEvent` with their measurements and
metadata cloned into `'static` form (`durable_owned`, which drops `Opaque`
values it cannot own).

The ownership rule is strict: only the true root of a run creates the
`ConfiguredTelemetry`. Shared helpers take caller-owned `&dyn Telemetry`; they
do not quietly allocate a second bus, because that creates a shadow event
stream the test cannot observe and can accidentally double-run planner/codegen
work under a different sink.

The decision and the artifact are two questions. Telemetry proves the compiler
*chose* something — a pass ran, a path was selected, N items were pruned. It does
not prove the produced program is correct. When the shape matters, a structural
assertion checks the artifact directly: the IR has the right form, the ABI has
the right params, the CLIF contains the expected op, a fixture still prints the
right result. Real codegen tests assert both: `fz.codegen.abi_contract` proves
the planned contract reached codegen, and a CLIF/runtime check proves the lowered
function honors it.
