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

**`NullTelemetry`** (`sink.rs`) — the no-op impl. Every method is `#[inline]` and
returns immediately, allocating nothing. The driver passes `&NullTelemetry` when
it wants silence; emit sites pay nothing.

**`ConfiguredTelemetry`** (`bus.rs`) — the listening impl the driver
instantiates. It owns a handler registry (`Vec<Entry>`, each entry a `prefix` +
boxed `Handler`), a `span_stack`, and monotonic `next_handler_id` /
`next_span_id` counters. It is single-threaded by design — `RefCell` interior
mutability, no `Send`/`Sync`. The CLI driver and each test own their own bus.

**`Handler` trait** (`handler.rs`) — a subscriber: `handle(&Event)`. The bus
routes an event to a handler when `name.starts_with(handler.prefix)`; the empty
prefix `&[]` matches everything. Concrete handlers:

- `DiagRenderer` (`diag_render.rs`) — events under `[fz, diag]` carrying a
  `Diagnostic` in their metadata; source-backed failures can also carry the
  relevant `SourceMap` in event metadata, so fatal callers do not need to
  thread render state through error values. The renderer downcasts and hands
  the diagnostic to `diag::render::Renderer` for stderr/writer output.
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
`Err(FatalError)`. Everything explanatory — including diagnostics that get
rendered as user errors, plus any source-map context the renderer needs — is an
event. So the trait has no fallible method: a handler cannot change what the
compiler computes.

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
JSON (no serde in the default build) and stamps each line with `time_ns`, a
monotonic offset from when the backend was constructed, so relative ordering is
trivial to profile. It drops `Opaque` values (no stable serialization), renders
`Bytes` as `"<N bytes>"` to keep lines ASCII, and renders non-finite floats as
`null`. A consumer needing binary round-trips uses a different channel.

**The bus is single-threaded.** No `Send`/`Sync`; the driver and each test hold
their own `ConfiguredTelemetry`. This is why handlers can share state through
plain `Rc<RefCell<…>>` (the pattern `Capture` and `StatsHandler` both use: keep
the typed object, attach a `handler()` that shares its buffer).

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

## Compiler World Events

`src/compiler.rs` owns the source-backed module world model introduced by
`fz-hua.1`. Its event vocabulary is the test seam for "did the compiler move a
module through the world the way we intended?" before loader/resolver work lands.

- `fz.compiler.file_registered` — a new compiler-owned file identity was created.
  Measurements: `file_id`. Metadata: `file_origin`, `file_label`.
- `fz.compiler.file_cache_hit` — the compiler reused an existing file identity.
  Measurements: `file_id`. Metadata: `file_origin`, `file_label`.
- `fz.compiler.module_discovered` — a new module identity was created.
  Measurements: `module_id`, `file_id`. Metadata: `module_key`,
  `module_key_kind`, `module_origin`, `file_origin`.
- `fz.compiler.module_cache_hit` — discovery asked for a module the compiler
  already knows about. Measurements: `module_id`, `file_id`. Metadata mirrors
  `module_discovered`.
- `fz.compiler.source_loaded` — the compiler materialized source text for a
  module-owned file. Measurements: `module_id`, `file_id`. Metadata:
  `module_key`, `module_key_kind`, `module_origin`, `source_name`,
  `file_origin`, `parse_kind`, `bytes`.
- `fz.compiler.parsed` — the compiler lexed and parsed one source-backed module
  into its cached syntax form. Measurements: `module_id`, `file_id`. Metadata:
  `module_key`, `module_key_kind`, `module_origin`, `source_name`,
  `parse_kind`, `items`. This event should happen once per module/file unless
  invalidation is introduced later.
- `fz.compiler.fn_group_discovered` — the compiler registered one executable
  function-group descriptor for a module body surface without lowering the
  group's IR yet. Measurements: `module_id`, `file_id`, `fn_group_id`,
  `arity`. Metadata: `module_key`, `module_key_kind`,
  `module_origin`, `owner_module`, `fn_name`, `visibility`.
- `fz.compiler.body_surface_ready` — the compiler collected the body-free
  executable surface for one module: stable function-group descriptors and
  root-fn ownership without emitted body IR. Measurements: `module_id`,
  `file_id`. Metadata: `module_key`, `module_key_kind`, `module_origin`,
  `owner_module`, `groups`, `parse_kind`.
- `fz.compiler.fn_group_lowered` — one source-backed function-group emitted IR
  exactly once into the compiler-owned cache. Measurements: `fn_group_id`,
  `functions`. Metadata: `module_key`, `owner_module`,
  `fn_name`.
- `fz.compiler.fn_group_requested` — a live lowered body referenced a source
  function-group that was not yet present in the executable surface, so the
  compiler requested it in the active reactive lowering loop. Measurements:
  `fn_group_id`, `loaded_functions`.
  Metadata: `module_key`, `owner_module`, `fn_name`.
- `fz.compiler.fn_group_cache_hit` — a later lowering request reused the cached
  IR for one source-backed function-group instead of re-emitting it.
  Measurements mirror `fn_group_lowered`. Metadata mirrors
  `fn_group_lowered`.
- `fz.compiler.interface_ready` — the compiler collected module interfaces from
  cached parsed source. Measurements: `module_id`, `file_id`. Metadata:
  `module_key`, `module_key_kind`, `module_origin`, `interfaces`,
  `parse_kind`.
- `fz.compiler.macro_surface_ready` — the compiler stored a fn-only compile-time
  surface for a macro provider without lowering or planning runtime work.
  Measurements: `module_id`, `file_id`. Metadata: `module_key`,
  `module_key_kind`, `module_origin`, `macros`, `items`.
- `fz.compiler.cache_miss` / `fz.compiler.cache_hit` — a phase or reachability
  query did or did not need work. Measurements: `module_id`, `file_id`.
  Metadata names the module plus the requested phase or reachability slice.
- `fz.compiler.state_work` — span around real state-advancement work. Tests
  should assert on the `SpanStop` event's `elapsed_ns` measurement rather than
  assuming work happened.
- `fz.compiler.state_advanced` — the module state lattice moved forward.
  Measurements: `module_id`, `file_id`. Metadata: `from_state`, `to_state`,
  plus module identity.
- `fz.module.unit_materialized` — the compiler-owned reactive runtime loop
  materialized one runtime source unit. Metadata: `kind`, `module`.
- `fz.module.execution_units_prepared` — the compiler-owned reactive runtime
  loop finished linking the root unit plus all reachable runtime units.
  Measurements: `interfaces`, `runtime_units`, `total_units`.
- `fz.compiler.module_reachable` — one reachability dimension (`interface`,
  `macro`, or `runtime`) was first marked true for a module. Measurements:
  `module_id`, `file_id`. Metadata: `reachability` plus module identity.
- `fz.compiler.runtime_module_reachable` — one runtime-library module became
  live for execution. Measurements: `module_id`, `file_id`. Metadata:
  `module_key`, `module_key_kind`, `module_origin`, `reason`, and
  `from_module` (empty when the module was seeded directly). Current reasons
  include exact `planned_external_target` roots, `runtime_import`,
  `runtime_implementation_dependency`, and the narrower protocol fallback
  `runtime_protocol_impl_provider`.
- `fz.compiler.runtime_lowered` — a live runtime-library module was lowered for
  execution. Measurements: `module_id`, `file_id`, `functions`, `groups`,
  `units`.
  Metadata: module identity.
- `fz.compiler.runtime_planned` — a live runtime-library module was planned for
  execution. Measurements: `module_id`, `file_id`, `planned_specs`, `groups`,
  `units`. Metadata: module identity.

## Resolver Contract Events

`src/frontend/resolve.rs` now emits explicit contract-lookup events so tests can
prove which source reference asked for a module contract, and whether the answer
came from a compiler-owned source module or a supplemental interface table.

- `fz.resolve.module_contract_requested` — the resolver encountered a module
  reference and asked for its contract. Measurements: `span_start`, `span_end`.
  Metadata: `requester_module`, `target_module`, `cause`
  (`import`, `alias`, `qualified_reference`, `protocol_impl_protocol`,
  `runtime_dependency`).
- `fz.resolve.module_contract_ready` — the resolver satisfied that request.
  Measurements: `span_start`, `span_end`. Metadata: `requester_module`,
  `target_module`, `cause`, `compiler_owned`, and `contract_origin`
  (`filesystem`, `embedded_runtime`, `primitive_prelude`, or `supplemental`).

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

The decision and the artifact are two questions. Telemetry proves the compiler
*chose* something — a pass ran, a path was selected, N items were pruned. It does
not prove the produced program is correct. When the shape matters, a structural
assertion checks the artifact directly: the IR has the right form, the ABI has
the right params, the CLIF contains the expected op, a fixture still prints the
right result. Real codegen tests assert both: `fz.codegen.abi_contract` proves
the planned contract reached codegen, and a CLIF/runtime check proves the lowered
function honors it.
