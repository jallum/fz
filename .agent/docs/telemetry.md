# Telemetry

Compile-time telemetry is the compiler's observability bus. Every output that is
not control flow — diagnostics, pass spans, counters, IR dumps, internal markers
— flows through it as an event. Fatal errors do **not**: they stay on
`Result<T, FatalError>`. Telemetry is the side channel; the `Result` is the
answer.

The compiler depends on one thing: the `Telemetry` trait (`sink.rs`). Generic
compiler paths retain the concrete handler type and pass `&T` through to lazy
event/span helpers; callers may choose dynamic dispatch only at an intentional
boundary. Who is listening, and what they do with the events, is none of the
compiler's business.

This doc covers compile-time telemetry. The running scheduler's events — process
exit, `dbg` output, how tests observe a run — live in
[`runtime-telemetry`](runtime-telemetry.md).

## The Pieces

**`Telemetry` trait** (`sink.rs`) — the sink surface. `dispatch` receives an
already-borrowed event only after lazy routing proved interest; `span_start` /
`span_stop` / `span_exception` bracket an active timed region. Compiler emit
sites use `TelemetryExt::execute_lazy`, `execute_lazy_with`, `event_lazy`, and
`span_lazy`, never construct a payload for `dispatch` directly. `name` is a
`&[&'static str]` path like `&["fz", "lexer", "tokens_built"]` — broad to
specific.

**Silence by type** — `NullTelemetry` is a zero-sized implementation whose
interest checks are false. Lazy payload closures therefore do not run, disabled
spans do not timestamp, allocate an id, or touch stack state, and generic
compiler execution can inline the branch away. `ConfiguredTelemetry` is used
when handlers may be attached at runtime.

**`ConfiguredTelemetry`** (`bus.rs`) — the listening impl the driver
instantiates. It owns a handler registry (`Vec<Entry>`, each entry a `prefix` +
boxed `Handler`), a `span_stack`, and monotonic `next_handler_id` /
`next_span_id` counters. It is single-threaded by design — `RefCell` interior
mutability, no `Send`/`Sync`. The CLI driver and each test root own their own
bus.

**`Handler` trait** (`handler.rs`) — a subscriber: `handle(&Event)`. Any
closure over a borrowed event is a handler too (`impl<F: Fn(&Event)> Handler
for F`), which is how observers project opaque payloads — downcast, render,
compute — while the event's borrows are still alive. The bus routes an event
to a handler when `name.starts_with(handler.prefix)`; the empty prefix `&[]`
matches everything. Concrete handlers:

- `DiagRenderer` (`diag_render.rs`) — events under `[fz, diag]` carrying a
  `Diagnostic` in their metadata; it downcasts and hands them to
  `diag::render::Renderer` for stderr/writer output. `fz2` gives it the
  compiler-owned `CodeMap` source index at front-door construction, so source
  text remains shared with compilation rather than being copied, formatted, or
  attached to each event. The renderer owns only its output/status state.
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
tel.execute_lazy(name, || (m, md)) ── interest ──▶ payload + dispatch only when
                                                    name.starts_with(prefix):
                                                      handler.handle(&Event{ .. })
```

The bus borrows its handler list immutably for the whole dispatch, so a handler
that attaches or detaches mid-dispatch panics on the re-borrow — that is a
programmer error, not a case the bus defends against.

## Spans

A span is a timed region whose child events know their parent. `TelemetryExt`
(`sink.rs`) gives `t.span_lazy(name, || metadata)` on any `T: Telemetry`
(including an intentional trait object) and returns an RAII `Span<'_, T>`
guard. The guard borrows both `T` and the static name slice; it neither erases
`T` nor copies the name. When no handler can observe the span or a descendant,
the guard is disabled and performs no timestamp, id, or stack work. An active
guard calls `span_start` (which pushes a fresh id onto
the bus's `span_stack` and emits a `SpanStart`); `Drop` measures `elapsed_ns` and
emits `SpanStop`, or `SpanException` when the scope is unwinding from a panic
(`panicking()`).

While a span is open it sits on the `span_stack`, so every lazy event during that
region carries the span's id as `span_id` and the enclosing span as
`parent_span_id`. `close_span` pops LIFO but tolerates any position so a panic
unwinding several layers still closes cleanly. The pop happens after dispatch, so
a handler peeking at the stack still sees the closing span as open.

```text
tel.span_lazy(["fz","compile"], || { compile_nonce, module_path })
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
trivial to profile. It renders `Opaque` values as
`{"opaque_type":"...","debug":"..."}` (the `debug` field only when the emit
site used `opaque_debug`), renders `Bytes` as `"<N bytes>"` to keep lines
ASCII, and renders non-finite floats as `null`. A consumer needing binary
round-trips uses a different channel.

**The bus is single-threaded.** No `Send`/`Sync`; the driver and each test hold
their own `ConfiguredTelemetry`. This is why handlers can share state through
plain `Rc<RefCell<…>>` (the pattern `Capture` and `StatsHandler` both use: keep
the typed object, attach a `handler()` that shares its buffer).

## Compiler2 Conventions

Compiler2 uses telemetry as its only observability surface. `Compiler2<T>` owns
its lifetime-free semantic `World` and its `T: Telemetry` side by side. A drive
constructs a short-lived `ExecutionContext<'_, T>` that split-borrows
`&mut World` and `&T`; `World` never stores, accepts, or dispatches telemetry.
Every job/event
under `[fz, compiler2, ...]` flows through the compiler's one telemetry value.

**Emit points are cheap: raw borrowed authorities only.** An emit site places
every payload expression inside a lazy closure. Before handler interest, it
performs no formatting, processing, allocation, calculation, cloning, or World
lookup. After interest, it passes O(1) immutable keys and the smallest borrowed
authority that already owns the decision, normally `&World`. The event does not
also extract a `FunctionRef`, source, body, dispatch plan, activation result, or
program from that authority. A handler that needs one copies or renders it at
event time. The JSONL backend is such a handler: it derives semantic activation
inputs, return evidence, and call summaries from `World` plus their keys.

Metadata must be nonredundant. An id belongs either in measurements or as the
key used to query an authority, never both under alternate names. Emitters pass
plain `opaque(...)` borrows; they never use `opaque_debug(...)`, construct a
display string, collect a derived vector, or clone a value for telemetry.

Two recurring patterns keep emit sites clone-free and erasable:

- **Define in `World`, then pass the authority.** A `World::define_*` core owns
  mutation and invariants without accepting telemetry. Its typed
  `ExecutionContext::define_*` wrapper calls that core, then emits only
  `&World`, the fact key, and the change outcome. The handler performs any
  post-mutation lookup. A `store.define(k, v.clone())`, World getter, or
  projection written so an emitter can report a detail is telemetry work on the
  wrong side of the boundary.
- **Spans borrow.** Span-start metadata and `stop_with` payloads accept
  borrowed lifetimes. Use `close_with_lazy` only when drop-time emission needs
  owned data; it evaluates that payload only for an active span. Prefer
  `stop_with` so names and paths ride as borrows.
- **Front doors borrow labels until storage.** CLI helpers, `compile_pipeline`,
  and `parse_quoted_program` thread `source_name` as `&str` across the public
  entry seams. If both the lexer and parser need the same label at once, they
  share one `Rc<str>` internally; owned `String`s are created only where a
  stored span or emitted metadata actually requires ownership.

The workspace ratchets this boundary through Cargo-owned clippy policy:
`redundant_clone`, `map_clone`, `iter_cloned_collect`, `implicit_clone`,
`useless_conversion`, and `unnecessary_to_owned` all warn in both workspace
crates, and the canonical `cargo clippy --workspace --all-targets -- -D warnings`
path promotes them to errors in the hook and CI.

**Slot revisions are the stable change signal.** Compiler2 state stores and fact
slots bump revisions only when their aggregate value changes. Handlers and
tests that care about "did this semantic thing actually change?" should key on
the reported revision or the published fact/output, not on the mere existence
of a repeated event. This matters most for joined facts like
`FactValue::Inputs(Vec<Ty>)`, callsite summaries, and product artifacts.

**Local type ids are world-owned facts.** Compiler2 `Ty` values are interned
`u32` handles owned by `World.types`. They are valid only inside that one
compiler world. Telemetry therefore treats them like `FunctionId` or `ModuleId`:
cheap compiler-owned identity, never a printable semantic contract by itself.
If a handler wants a rendered type, it must derive that rendering on its side.

**Drive and job spans are the execution spine.** `ExecutionContext::drive()` opens one
`[fz, compiler2, drive]` span. Each popped job opens one
`[fz, compiler2, job]` span. Successful job spans close with the raw `effects`
borrowed in place; the applied graph step rides the separate
`[fz, compiler2, work_graph, applied]` event that `complete_job` emits with
the job and `AppliedStep`. Unresolved drives close with the raw wait frontier;
fatal drives close with the fatal job. Because the JSONL handler renders
opaque metadata, the emitted log shows the actual precipitating `Job`,
`JobEffects`, `AppliedStep`, and unresolved waits instead of hiding them
behind the final outcome. There is no extra "job_fatal" event and no redundant
"fact_published" stream.

When the agenda drains with unresolved waiters, `ExecutionContext::drive()`
(`drive.rs`) runs its stall pass: it demands every submitted root's entry
analysis and, for each blocked waiter's fact not already demanded since the
last content change, pokes that fact's mapped producer through the
fact->producer map (`demand_fact_producer`). If that expansion pokes at least
one producer, the pass emits `[fz, compiler2, drive, demand_on_stall]`
(payload-only `event`, no span; the `event` path carries everything as
metadata). Metadata: `producer_pokes`, the total pokes this round, and
`demanded_facts`, the
`Vec<FactKey>` poked this round, as `opaque_debug` — this is what lets a test
or trace tell *which* facts were stalled, not just that a stall-demand
happened. A round with `producer_pokes == 0` is a genuine stall: the drive
breaks out and reports `DriveOutcome::Unresolved` instead of emitting the
event. Separately, `[fz, compiler2, drive, timed_out]` fires when a deadline
passed to `drive` elapses mid-agenda, before any stall pass runs. Measurements:
none (payload rides in metadata). Metadata: `pending_jobs`, `jobs_ran`,
`timeout_ms`.

Product artifact producers lean on pull telemetry as their contract surface. The
tests assert that the interpreter front door requests `RootBackendProduct(root)`,
that producers wait on exact `ProductKey` / `FactUse<FactKey>` prerequisites,
and that no forbidden root artifact jobs fire on the product path. Legacy job
span assertions remain useful for macro/native compatibility paths, but they
are not the target model for new artifact work.

The public 00181 no-dump proof should be gathered from CLI telemetry, not from
world internals:

```sh
rm -f /tmp/fz-00181.jsonl
cargo run -q -- --log-telemetry /tmp/fz-00181.jsonl \
  interp fixtures2/00181_enum_reduce_operator_ref.fz

jq -sr '
  def nm: .name|join(".");
  "job_starts=\([.[] | select(nm=="fz.compiler2.job" and .kind=="span_start")] | length)",
  "root_session=\([.[] | select(nm=="fz.compiler2.pull.session.finished" and .measurements.root_id==0)] | last | .measurements)"
' /tmp/fz-00181.jsonl
```

The job trace is minimal by construction: the legacy `SealSemanticClosure` /
`DeriveRuntimeDemand` / `DeriveExecutableTransport` / `DeriveTransportPlan` jobs
do not exist, so no job debug string can name them. The fixture call-edge
oracle sources its activation set from `Compiler2::product_executable_inventory`
(`compiler.rs`), which drives the root through the product backend path and
collects `driver.session().materialized_executables()` — there is no separate
frontier scan.
Root session measurements for `fixtures2/00181_enum_reduce_operator_ref.fz` are
`executables=10`, `transport_positions=160`, `callables=2`, `boundaries=0`,
`producer_pokes=0`. Backend dumps may be requested with `--dump
backend=/tmp/fz-00181.backend`; the `types` / `activations` dumps are served
from the product-path activation inventory
(`Compiler2::emit_product_semantic_dumps`, which walks the demanded session's
materialized executables).

Transport product construction emits `[fz, compiler2, pull, product, *]` for
per-position product demand. There is no root-wide `transport_flow` signal: the
legacy `DeriveTransportPlan` job that emitted it — and its `TransportPlan(root)`
fact — do not exist. The product path treats the
`RuntimeDemand(E)` product as pre-transport evidence; `TransportPosition ->
ShapeId`, `CallableId` facts, `BoundaryId` contracts, and `CodegenSeamFact` rows
are produced for the positions and boundaries named by demanded executable
products. Tests assert ShapeId relationships from the demanded
`MaterializedTransportPlan` when correctness depends on sharing.

`ProductDriver` (`pull.rs`) names four `[fz, compiler2, pull, product, *]` leaf
events off one shared `key`/`kind` shape (`kind: key.kind()`,
`product: opaque_debug(key)`), so a handler on the `[fz, compiler2, pull,
product]` prefix sees every product pull without per-event wiring:
`requested` and `cache_hit` fire from `ProductDriver::pull`'s entry/memo-hit checks,
`reentered` fires when a product pull recurses into its own in-flight demand
(`wait_count: 1`), `waited` fires whenever the producer body returns
`PullOutcome::Waiting` (measurements: `wait_count`; metadata additionally
carries `waits: opaque_debug(waits)`, the blocking `PullWait`s), and
`produced` fires once the value settles (measurements: `wait_count: 0`,
`identical` — whether the settled value repeats the prior demand). This is the
cache-hit/re-solve signal for the product path: a test asserting bounded
re-computation counts `produced`/`cache_hit` rather than re-deriving state
from `World` internals.

`[fz, compiler2, pull, transport_component, produced]`
(`jobs/transport.rs::emit_transport_component_produced`) fires every time
`produce_transport_component_product` resolves a position's transport
component, whether served from the session's `transport_components` product
cache or freshly materialized. Measurements carry `component_size` (the
component's member-position count); metadata carries the component's
`representative` position as `opaque_debug`. `[fz, compiler2,
executable_transport, projected]`
(`jobs/transport.rs::emit_transport_component_materialized`) fires only on the
fresh-materialize path — never on the cache-hit early return — so it is the
narrower signal: "this executable's transport was (re)projected on this
drive." Measurements carry the same `component_size`; metadata carries the
`ExecutableKey` as `opaque_debug`. Together the two events let a test
distinguish a cache-hit pull (only `transport_component.produced` fires) from
a fresh solve (both fire), which is the observable form of the cone-scoped
bounded-blast-radius property: a position outside the demanded closure never
re-triggers `executable_transport.projected`.

`[fz, compiler2, pull, transport_component, closure_solved]`
(`jobs/transport.rs::emit_transport_closure_solved`) fires when
`solve_transport_closure` finishes covering an executable's transport
closure. Measurements carry `executables`, `components`, and `positions`
counts from the `SolvedTransportClosure`. It is the per-solve sizing signal
for the covering solve that `transport_component.produced`/
`executable_transport.projected` ride on.

`[fz, compiler2, pull, session, finished]` (`pull.rs::PullSession::emit_finished`,
called from `ProductDriver::finish_session`) fires once per pull session, when
the driving front door finishes demanding the session's products. Measurements:
`root_id`, `executables` (count of demanded `ExecutableKey`s),
`transport_positions` (count of demanded `TransportPosition`s), `callables`
(count of demanded `CallableId`s), `boundaries` (count of demanded
`BoundaryId`s), `producer_pokes` (the session's running count of
`demand_fact_producer` calls the drive made while resolving this session's
waits), the per-reason work-start breakdown `work_starts_ignition`,
`work_starts_changed_revision_wake`, `work_starts_standing_root_frontier`,
`work_starts_activation_frontier`, `work_starts_blocked_waiter_expansion`
(the world's cumulative agenda-entry counts under each sanctioned
`WorkStartReason`), `unsanctioned_work_starts` (the count under
`WorkStartReason::Unclassified`), and `root_scans` (the world's cumulative
count of whole-fact-table scans taken through `Scheduler::fact_keys`). No
metadata. This is the root-level summary a test or CLI trace reads to assert
product-path work stayed bounded — the `fz-00181` no-dump proof above keys off
exactly these fields, and `work_start_reason_test`'s
`pull_only_guard_holds_for_*` cases assert `unsanctioned_work_starts == 0`,
`root_scans == 0`, AND `ignition == 2` (the true external front-door count)
for every fixture they drive.

### Work-Start Attribution (`WorkStartReason`)

`Scheduler::enqueue` (`scheduler.rs`) takes a `WorkStartReason` alongside the
job, tagging every agenda insertion with why it started. Tagging is
observation-only: it changes no scheduling decision, only which counter a
work-start increments. The scheduler tallies starts per reason plus the
whole-fact-table-scan count into a single `WorkStartTally` snapshot
(`Scheduler::work_start_tally`), surfaced through `World::work_start_tally`,
recorded onto the `PullSession` at finish time, and read back through the
session's own `work_starts()`/`unsanctioned_work_starts()`/`root_scans()`
accessors.

The taxonomy holds exactly the pull-only northstar's sanctioned ways work can
start (`../pull-based.html`):

- `Ignition` — an EXTERNAL submission (`ExecutionContext::submit_code`,
  `World::submit_module_interface`, `ExecutionContext::submit_root`) enqueuing the one job that begins
  that submission's own work. "External" is load-bearing: the only production
  callers of those three methods are the CLI front door (`cli.rs`) and the
  public `Compiler2` API (`compiler.rs`) — a user/CLI request, never a job
  body mid-execution. A job that needs source minted (e.g. an unloaded
  runtime module) must NOT drive it through `submit_code`; it registers the
  source (`ExecutionContext::register_code`, via `ensure_runtime_module`) and lets the
  fact->producer pull mint it. The `ignition == 2` assertion in the guard is
  what enforces this: a job that tried to mint source through `submit_code`
  mid-execution would inflate the ignition count past the two external
  front-door starts and trip the guard red.
- `ChangedRevisionWake` — `Scheduler::complete`'s wake propagation
  (`enqueue_dependents`/`enqueue_step`) re-running a job whose fact
  subscription (read, wait, or settled-presence) just changed. This is the
  core pull mechanism: readers wake because their ground moved, never because
  a producer pushed them by name. This reason is never passed by a caller —
  `enqueue_step` applies it internally, since it names the wake mechanism
  itself.
- `StandingRootFrontier` — `drive::demand_root_entry_analyses` expanding a
  submitted root's standing entry-analysis demand through the fact->producer
  map (`demand_fact_producer`).
- `ActivationFrontier` — `drive::demand_activation_frontier_analyses`
  expanding a discovered callee activation's standing analysis demand through
  the same map.
- `BlockedWaiterExpansion` — the fact->producer map expanding a blocked
  waiter's missing fact to its single producer at a drain/stall point: both
  the bare scheduler's `demand_blocked_wait_producers`/`drive_until` stall
  pass and the bounded product-pull's own fact-wait loop
  (`product_drive::drive_product_fact_wait`) use this. This is the reason
  runtime-module minting now rides: an `ensure_runtime_module` caller waits on
  `CodeIndexed(code_id)` (or a `ModuleDefined` wait that chains to it through
  `define_module`), and the drain/stall pull expands it to `Job::IndexCode`.

`Unclassified` is the catch-all default (`#[derive(Default)]` on
`WorkStartReason`). A future enqueue call site that forgets to pass one of the
reasons above — the shape a reintroduced `follow_up`-style push would take —
lands here by construction, which is exactly what trips
`unsanctioned_work_starts` above zero and fails the running guard.

The two bounded inner product-pulls (`jobs::macro_runtime::build_macro_executable`,
`jobs::native::lower_native_program`) drive their own fresh
`RootBackendProduct` and register its result through `ExecutionContext::complete_job`
directly — they never call `Scheduler::enqueue` for that work, so they carry
no `WorkStartReason` at all; there is nothing on the shared agenda to
misclassify.

**The guard's boundary (honest limits).** The running guard catches an
*untagged* enqueue: a future dev adds a new `Scheduler::enqueue` call site and
omits the reason, so it defaults to `Unclassified` and
`unsanctioned_work_starts` rises above zero — caught. It does NOT, by the
`unsanctioned` counter alone, catch a deliberately *mislabeled* push: a new
internal (mid-job) caller that hand-passes a sanctioned reason (say
`Ignition`) would be counted as sanctioned. The `ignition == 2` assertion in
`work_start_reason_test` is the specific backstop for that class — an internal
caller mislabeling work as the external front door pushes the ignition count
past the true external total and fails the guard. There is no general counter
that catches an arbitrary mislabel to `ChangedRevisionWake`/`*Frontier`/
`BlockedWaiterExpansion`; those remain a code-review responsibility, and the
per-reason breakdown emitted on `pull.session.finished` is the observability
that makes such a drift visible in a trace.

Macro executable readiness also emits
`[fz, compiler2, macro_executable, defined]` with raw `function_id`,
`root_id`, backend revision, macro executable revision, and the backend program
as opaque debug metadata. The event is observational only; tests that care
about correctness should still assert the `JobEffects` facts and the absence of
`NativeProgram(macro_root)` for macro roots.

Macro expansion emits `[fz, compiler2, macro, expanded]` after a
`MacroExecutable` runs over quoted source and before recursive expansion
continues. Measurements carry `function_id`, `module_id`, expansion `depth`,
`depth_budget`, `arg_count`, and the input/output quoted-source
`heap_id`/`root_ref` pairs. This is the deterministic signal for runaway
expansion and for proving that a returned root stayed in the same quoted-source
transport world. The event is emitted by the shared quoted expander, so item
macros and demanded function-body macros both report through the same path.

Demand-time body staging emits `[fz, compiler2, function, source, expanded]`
when `ExpandFunctionSource(function)` materializes `ExpandedFunctionSource`.
Measurements carry the same raw function/code ids and quoted-source
`heap_id`/`root_ref` pair as `function.source.noted`, but the event should only
appear once a function is actually demanded. `ScopeCode` should not emit this
event for ordinary undemanded function bodies; item-macro publication is still
scope-order work, body-local macro expansion is not.

Source-order compiler services emit `[fz, compiler2, compiler_service, define]`
when `Fz.Compiler.define` publishes an expanded source root. Measurements carry
raw compiler ids (`code_id`, `module_id`, `owner_module_id`, `function_id`),
the publication `revision`, the captured `namespace`, the quoted-source
`source_heap_id` / `source_root_ref`, and `env_root_ref` for the projected
`__ENV__`. Literal functions, protocol callbacks, synthesized module-info
functions, item-macro returned definitions, and explicit compiler-service forms
all use this same event with `origin=fz_compiler`.

Function surface/body publication emits three sibling events. Each
`ExecutionContext::define_*`/`note_*`/`stash_*` wrapper first calls its
observer-free `World` core, then sequences observation from immutable getters;
the context never owns the store. `[fz, compiler2, function, source, noted]`
(`world.rs::note_function_source`) fires when a function's `FunctionSource`
becomes readable — the interface-tier signal a name-keyed observer watches for
every scoped function, macro-expanded or not. `[fz, compiler2, function,
source, stashed]` (`world.rs::stash_function_source`) mirrors that shape for a
function whose identity/interface are published at scope time while its body
stays cold until a reached consumer pulls it (the surface counterpart to
`type.noted`); it carries no `changed` measurement because stashing does not
touch the fact store. Its metadata carries raw post-mutation borrows of the
`FunctionRef`, stored `FunctionSource`, `FunctionId`, and `World`, so a handler
can verify or project the settled state without any emit-side copy or
transformation. `[fz, compiler2, function, defined]`
(`world.rs::define_function` and `world.rs::define_generated_function`, its
macro-literal-return sibling) fires when
a function's parsed surface is stored; both call sites share the measurement
set `code_id`, `module_id`, `owner_module_id`, `function_id`, `arity`,
`clauses`, `source_heap_id`, `source_root_ref` and the metadata set
`function`/`function_ref`/`function_id`/`module_id`/`owner_module_id` as
`opaque_debug`, with the macro-literal site adding `owner_function_id` to both
channels. All three carry the code/module/function ids plus arity and clause
count in measurements. Each carries its stored `FunctionSource` or
`FunctionState` as raw metadata, so a handler can render the actual source
without the emit site formatting anything; the stashed event uses its raw
`World` borrow instead of duplicating module ids in metadata.

`[fz, compiler2, function_contract, defined]` (`world.rs::define_function_contract`)
fires when a function's `FunctionContract` (its declared/inferred call
contract) is stored. Measurements: `function_id`, `arity`, `changed`. Metadata:
`function_ref`, `contract` as `opaque_debug`.

Dispatch- and body-shape facts each emit one `[fz, compiler2, X, defined]` (or
`derived`) event from their `ExecutionContext::define_*` step, all following the same
shape: measurements carry the owning `code_id`/`module_id`/`function_id`/
`arity` plus a size count specific to the fact, and metadata carries the
`function_ref` and the stored value as `opaque_debug`.

- `[fz, compiler2, entry_dispatch, defined]` (`world.rs::define_entry_dispatch`)
  — measurements add `outcomes`, `guards`, `pinned` (from the
  `PatternDispatchPlan`) and `source_root_ref`; metadata adds `plan`.
- `[fz, compiler2, guard_dispatch, defined]` (`world.rs::define_guard_dispatch`)
  — measurements add `bodies`, `guards`, `pinned`, `source_root_ref`; metadata
  adds `dispatch`.
- `[fz, compiler2, dispatch_mask, derived]` (`jobs/keying.rs::derive_dispatch_mask`)
  — measurements are just `function_id`/`arity` (mask length); metadata carries
  the derived `DispatchInputMask` as `mask`.
- `[fz, compiler2, lowered_body, defined]` (`world.rs::define_lowered_body`) —
  measurements add `clauses`, `generated`, `source_root_ref`; metadata carries
  the `LoweredBody` as `body`.

Activation-level analysis facts follow the same "define, then re-borrow, then
emit" shape keyed by `ActivationKey` instead of `FunctionId`:

- `[fz, compiler2, activation_analysis, defined]` (`world.rs::define_activation_analysis`)
  — measurements: `root_id`, `function_id`, `reachable_clauses`, `callsites`,
  `values` (sizes off the stored `ActivationAnalysis`). Metadata: `activation`,
  `analysis` as `opaque_debug`.
- `[fz, compiler2, activation_inputs, defined]` (`ExecutionContext::complete_job`)
  — fires once per activation whose input types changed this job completion.
  Measurements: `root_id`, `function_id`, `input_arity`, `rebased` (whether
  this settle narrowed rather than joined). Emission occurs only after
  `World::complete_job` has published the fact and revision. Metadata:
  `activation`, `inputs`, the post-mutation `world`, and `publisher` (the completing `Job`). The raw
  `World` and input borrows let handlers render types or inspect related state
  without making the emit site construct a display projection.
- `[fz, compiler2, return_type, defined]` (`world.rs::define_activation_return`)
  — measurements: `root_id`, `function_id`, `ascents` (join-step count),
  `rebased`. Metadata: `activation`, `return_ty`. When the same settle widens
  the return type rather than narrowing it, the same call site also emits
  `[fz, compiler2, return_type, widened]` with the same `root_id`/
  `function_id`/`ascents` measurements — the two together distinguish "the
  return type advanced" from "the return type advanced by widening," which a
  convergence-runaway diagnosis reads to tell a genuine narrowing settle from
  a widening one.
- `[fz, compiler2, callsite, defined]` (`world.rs::define_callsite_summary`) —
  measurements: `root_id`, `function_id`, `callsite_id`, `input_arity`,
  `target_count`, `changed`. Metadata: `callsite`, `summary` (the
  `CallSiteSummary`) as `opaque_debug`.

Module, root, and code identity emit their own definition events:
`[fz, compiler2, module, defined]` (`world.rs::define_module`, measurements
`code_id`/`module_id`, metadata `module`/`module_id`); `[fz, compiler2, root,
submitted]` (`world.rs::submit_root`, measurements `root_id`, `module_id`,
`function_id`, `arity`, `pending_codes`, metadata `root`/`function_ref`) fires
when a caller submits a fresh compile root, ahead of any drive; `[fz,
compiler2, code, submitted]` (`world.rs::submit_code`, measurements `code_id`,
`bytes`, no metadata) fires when source text is registered, before indexing.

Protocol wiring emits one definition event per store: `[fz, compiler2,
protocol_callback, defined]` (`world.rs::define_protocol_callback`,
measurements `protocol_id`/`function_id`/`arity`, metadata
`callback`/`function_ref`); `[fz, compiler2, protocol_dispatch, defined]`
(`world.rs::define_protocol_dispatch`, measurements `protocol_id`/`arms`/
`changed`, metadata `dispatch`); `[fz, compiler2, protocol_impl, defined]`
(`world.rs::define_protocol_impl`, measurements `protocol_id`/`target_id`/
`callbacks`, metadata `key`/`protocol_impl`).

Backend and native artifact definitions: `[fz, compiler2, backend_program,
defined]` (`world.rs::define_backend_program`, measurements `root_id`,
`atom_count`, `executable_count`, `callable_entry_count`, `changed`, metadata
`program`/`root_id` as `opaque_debug`) fires when a root's `BackendProgram`
is stored — the `--dump backend=` handler subscribes to this same event.
`[fz, compiler2, native_program, defined]` (`world.rs::define_native_program`,
measurements `root_id`, `body_count`, `callable_boundary_count`, `fn_count`,
`changed`, metadata `program`/`root_id`) fires when the CPS/native lowering of
a root's `BackendProgram` is stored — the `--dump native=`/`--dump fnir=`
handlers subscribe to this event. `[fz, compiler2, native_program,
reusable_cons]` (`jobs/native.rs::lower_native_program`) fires alongside it
with measurements `root_id`, `birth_count`, `transport_count` — the counts
`NativeLowerer` collects for cons cells that are constructed fresh versus
reused across a transport boundary, no metadata.

Type identity emits two narrower events than `[fz, compiler2, type,
defined]` (the resolved `TypeDef`, exercised by `rendered_type_defs` above):
`[fz, compiler2, type, noted]` (`world.rs::note_type_decl`) fires when an
unresolved `@type` declaration becomes a referenceable identity, before
`DeriveTypeDef` resolves it — measurements `module_id`/`arity`/`namespace`,
metadata `name`/`decl`. `[fz, compiler2, type, referenced]`
(`world.rs::emit_type_referenced`) fires from typedef/contract/dispatch
resolution whenever one type name's resolution reaches another named type —
measurements `ref_module_id`/`ref_arity`, metadata `ref_name`, `consumer_kind`,
`consumer` (the referencing name), and `referenced` (the full `TypeName`) —
the dependency-edge signal a type-cycle diagnostic reads.

`--dump` output rides its own events rather than a side channel: `[fz,
compiler2, dump, types]` and `[fz, compiler2, dump, activations]`
(`dump.rs::emit_dump_events`, called from the product-path
`emit_product_semantic_dump_events`) fire once each per root, carrying
`root_id` in measurements and the rendered `TypesDump`/`ActivationsDump` text
as a plain `opaque` metadata `dump` (not `opaque_debug` — the dump handler is
the sole consumer and renders the text directly). `install_dump_handlers`
attaches a one-shot writer to each dump kind's event, keyed by `--dump
<kind>=<path>`; `Backend`/`Native`/`Fnir` dump kinds instead attach to the
`backend_program.defined`/`native_program.defined` definition events above,
so a dump never forces extra computation beyond what the product path already
demanded. `[fz, compiler2, dump, clif]`
(`native_codegen/driver.rs::lower_function`, gated on
`ir_text_record_enabled()`) additionally fires per lowered function body when
CLIF text recording is on, carrying `fn_id`/`spec_id` measurements and a
`ClifDumpEntry` as plain `opaque` metadata.

**Compiler2 tests should observe telemetry, not world internals.** The common
captures live in `src/compiler2/drive_test.rs` and assert on emitted
definitions, work-graph steps, callsite summaries, product pulls, and native
handoff products where relevant. The quicksort,
`Enum.reduce`, and variadic-extern contracts are the fast summary probe; the
compiler2-owned native JIT fixture tests prove the in-house backend can consume
`NativeProgram(root)` directly, while the `Compiler2::compile_root_jit` /
`run_root_jit` / `compile_root_aot` front-door tests prove that the public
runtime setup now stays on that same compiler2-owned backend path without
falling back to planner or type-preparation
telemetry. `tests/fz2_cli.rs` extends that proof to the real `fz2` binary
surface; its source-production macro/sugar fixture test asserts
`FunctionSource` publication, `Fz.Compiler.define` publication, macro expansion
when expected, and no legacy frontend/planner/type-infer events. Its
`Enum.reduce` CLI probe also asserts that `lexer.pass` span-start events match
the exact submitted source set one-for-one: user source plus the demanded
runtime sources, with no duplicate pass and no fragment pseudo-source. The
quicksort CLI probe carries the original perf question: on 2026-06-10,
running `target/debug/fz2` with telemetry on `fixtures2/behavior/quicksort.fz`
emitted four lexer span-starts, exactly
`fixtures2/behavior/quicksort.fz`, `runtime:runtime.fz`, `runtime:Kernel.fz`, and
`runtime:Process.fz`. The old source-fragment re-lex and its hidden per-call
type-env rebuild are gone by construction on the compiler2 path. The same trace
showed the native tail clearly: `fz.compiler2.drive` took 58.109 ms, then
post-drive native backend compilation took 47.207 ms before runtime exit. That
tail is now named by `fz.compiler2.native_backend.compile`, whose child
`fz.codegen.compile` owns the backend-internal phase breakdown (`47.136 ms` in
the same run). It is not a source-production re-lex problem. The ignored JSONL
dump is the occasional deep trace.

Useful reruns:

- `cargo test --lib compiler2_ -- --nocapture`
- `cargo test --lib compiler2::drive_test::compiler2_quicksort_root_closes_with_a_finite_recursive_frontier -- --exact --nocapture`
- `cargo test --lib compiler2::drive_test::compiler2_backend_program_keeps_only_the_closed_quicksort_inventory -- --exact --nocapture`
- `cargo test --lib compiler2::drive_test::compiler2_enum_reduce_selects_list_protocol_impl_and_callable_reducer -- --exact --nocapture`
- `cargo test --lib compiler2::drive_test::compiler2_backend_program_keeps_direct_only_enum_reduce_out_of_callable_inventory -- --exact --nocapture`
- `cargo test --lib compiler2::drive_test::compiler2_backend_program_carries_return_payload_flow_before_native_lowering -- --exact --nocapture`
- `cargo test --lib compiler2::drive_test::compiler2_backend_program_preserves_variadic_extern_wire_classes -- --exact --nocapture`
- `cargo test --lib compiler2::drive_test::compiler2_native_program_jit_runs_quicksort_through_compiler2_codegen -- --exact --nocapture`
- `cargo test --lib compiler2::drive_test::compiler2_native_program_jit_runs_enum_reduce_through_compiler2_codegen -- --exact --nocapture`
- `cargo test --lib compiler2::drive_test::compiler2_native_program_jit_runs_variadic_extern_through_compiler2_codegen -- --exact --nocapture`
- `cargo test --lib compiler2::compiler2_test::compiler2_compile_root_jit_consumes_native_program_without_legacy_prepare -- --exact --nocapture`
- `cargo test --lib compiler2::compiler2_test::compiler2_run_root_jit_executes_resources_without_legacy_prepare -- --exact --nocapture`
- `cargo test --lib compiler2::compiler2_test::compiler2_compile_root_aot_consumes_native_program_without_legacy_prepare -- --exact --nocapture`
- `cargo test --test fz2_cli -- --nocapture`
- `cargo test --lib compiler2::telemetry_dump_test::dump_quicksort_compiler2_telemetry_to_jsonl -- --ignored --exact --nocapture`

The ignored harness writes its log to `/tmp/fz-compiler2-quicksort.jsonl`.

For runtime-membership regressions below the native handoff, the fast probes are
the explicit runtime-predicate projection tests and the cached receive-dispatch
test:

- `cargo test --lib runtime_type_predicate_ -- --nocapture`
- `cargo test --lib cached_matcher_type_region_uses_runtime_type_predicate -- --exact --nocapture`

## Codegen Regression Events

Compiler2 emits `fz.compiler2.native_backend.compile` when a public native front
door consumes a `NativeProgram(root)` through JIT or AOT. It is the artifact
boundary span: metadata names the `root_id`, `backend_revision`, `entry_fn_id`,
`body_count`, `callable_boundary_count`, and backend kind. The raw
`fz.codegen.compile` span nests under it, so a trace can account for both the
fact drive and the post-drive native backend tail without treating codegen as an
unattributed gap.

Three codegen events carry stable enough fields to assert on in tests, proving
codegen consumed the published ABI and callable-boundary facts handed to it. They
are emitted for reachable specs / lowered sites and pair with CLIF or runtime
checks when the generated shape matters. Both backends emit them; the
compiler2 copy (`compiler2/native_codegen/`) follows the cheap-emit
discipline, while the old-pipeline twin (`ir_codegen/`) still preformats some
fields and dies with that pipeline.

- `fz.codegen.abi_contract` (`compiler2/native_codegen/driver.rs`) — one per
  lowered body slot. Measurements: `spec_id`, `fn_id`, `param_count`,
  `capture_count`. Metadata: borrowed `module_path`/`fn_name`, `body_origin`
  and `entry_abi` as `opaque_debug` enum borrows, `param_reprs` as an
  `opaque_debug` `Vec<ArgRepr>` borrow, `return_repr` (`ArgRepr::as_str`,
  `&'static str`), and the `is_native` / `is_cont_fn` / `is_closure_target`
  flags. (The ir_codegen twin additionally carries `spec_key` and renders
  `param_reprs` as strings.)
- `fz.codegen.callable_boundary_materialized` (`compiler2/native_codegen/prim.rs`)
  — one per `MakeFnRef` / `MakeClosure` lowered through compiler2-native
  codegen. Measurements include the active `spec_id`/`fn_id`,
  `closure_fn_id`, `capture_count`, `callable_boundary_id`, `block_id`,
  `stmt_idx`, and source `span_start`/`span_end`. Metadata: borrowed
  `module_path`/`body_name`, `materialization_kind`,
  `callable_boundary_target_fn_id`, and the `fz_ir::Module` as a plain
  `opaque` borrow — a handler wanting the closure's name resolves
  `closure_fn_id` against it at event time. For compiler2-native, this event
  means "codegen materialized the settled callable boundary already published
  by native lowering"; codegen no longer re-selects among candidate
  boundaries from local type evidence.
- `fz.codegen.closure_call_lowered` (`compiler2/native_codegen/terminator.rs`)
  — one per `CallClosure` or `TailCallClosure` lowering. Measurements include
  active `spec_id` and `closure_var`; non-tail closure calls also include
  `continuation_spec_id`. Metadata: `body_name`, `call_kind`,
  `closure_binding_repr` (`ArgRepr::as_str`), `dispatch_kind` (`direct` when
  the body literal resolves, else `indirect`), optional `direct_target_fn_id`
  for direct calls, and optional `callable_boundary_id` plus
  `callable_boundary_target_fn_id` when the closure value carries a settled
  callable-boundary fact. Non-tail closure calls also report
  `continuation_storage` (`lazy_descriptor` or `heap_closure`). Absence of
  `callable_boundary_id` means the call lowered without a known callable
  boundary id. Direct closure fast paths consume the native call term selected
  by `CallReturnFlow`; narrowing return delivery is represented by an explicit
  continuation before codegen.

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
values it cannot own). That drop is by design: a test that needs an opaque
payload attaches an event-time closure handler that downcasts and projects
while the borrows are alive — `rendered_type_defs` in
`src/compiler2/drive_test.rs` is the exemplar (it downcasts the `TypeDef` and
`Types` interner off `[fz, compiler2, type, defined]` and renders the type in
the handler). Borrowed `Str` values survive durable capture (the handler
clones them at event time), so emit sites lending `&str`s cost tests nothing.

The ownership rule is strict: only the true root of a run creates the
`ConfiguredTelemetry`, and `Compiler2` takes ownership of it. Short-lived
execution contexts and shared helpers borrow that owned telemetry; they do not
quietly allocate a second bus or preserve a caller-owned reference through a
forwarding adapter, because either choice creates an ambiguous ownership seam.

The decision and the artifact are two questions. Telemetry proves the compiler
*chose* something — a pass ran, a path was selected, N items were pruned. It does
not prove the produced program is correct. When the shape matters, a structural
assertion checks the artifact directly: the IR has the right form, the ABI has
the right params, the CLIF contains the expected op, a fixture still prints the
right result. Real codegen tests assert both: `fz.codegen.abi_contract` proves
the planned contract reached codegen, and a CLIF/runtime check proves the lowered
function honors it.
