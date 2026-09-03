# Telemetry

Compile-time telemetry is the compiler's observability bus. Every output that is
not control flow — diagnostics, pass spans, counters, and internal markers —
flows through it as an event. Requested compiler output such as IR dumps uses
the synchronous `RequestedOutputSink`, not telemetry. Fatal errors stay on
`Result<T, FatalError>`. Telemetry is the side channel; the `Result` is the
answer.

The compiler depends on the object-safe `Telemetry` event surface and, where it
opens raw spans, the `RawSpanTelemetry` capability (`sink.rs`). Production paths
retain the concrete `T` from the front door through every emitter and call typed
raw methods with borrowed values. There is no production telemetry trait-object
boundary. Who is listening, and what handlers do with the borrowed values, is
none of the compiler's business.

This doc covers compile-time telemetry. The running scheduler's events — process
exit, `dbg` output, how tests observe a run — live in
[`runtime-telemetry`](runtime-telemetry.md).

## The Pieces

**`Telemetry` and `RawSpanTelemetry` traits** (`sink.rs`) — the sink surfaces.
Raw event and span methods receive references to values the compiler already
owns. Their generic type and arity identify the callback signature without
constructing an `Event`, `Metadata`, or `Value`. `RawSpanTelemetry` selects a
guard type for each supported start/stop arity, so a caller can invoke only the
stop operation declared by that span signature. `name` is a
`&[&'static str]` path like `&["fz", "lexer", "tokens_built"]` — broad to
specific.

**Silence by type** — `NullTelemetry` is a zero-sized implementation whose raw
methods are empty and whose associated raw-span guard is the zero-sized,
non-dropping `NullSpan`. Because front doors preserve its concrete type,
optimized compiler, lexer, interpreter, and runtime paths erase the calls and
the guard itself.
`ConfiguredTelemetry` activates a raw event only for an exact arity callback and
activates a raw span only for an exact start/stop type signature or a matching
payload-free lifecycle observer. An inactive span does not timestamp, allocate
an id, or touch stack state.

**`ConfiguredTelemetry`** (`bus.rs`) — the listening impl the driver
instantiates. It owns exact typed raw callback registries, a payload-free raw
lifecycle registry, the legacy handler registry, a span stack, and monotonic
ids. It is single-threaded by design. The CLI driver and each test root own
their own bus.

**Raw callbacks** — the normal subscriber surface. A callback receives the
static name, span ids, and exact borrowed authorities synchronously. It may
render, derive, or copy them; the emitter may not. Prefix-only lifecycle
callbacks receive no payload and are sufficient for stats and structural test
capture. Legacy `Handler::handle(&Event)` routing remains for legacy emitters
and does not enable raw events. Concrete handlers:

- `DiagRenderer` (`diag_render.rs`) — events under `[fz, diag]` carrying a
  raw `Diagnostic`; it hands that value to
  `diag::render::Renderer` for stderr/writer output. `fz2` gives it the
  compiler-owned `CodeMap` source index at front-door construction, so source
  text remains shared with compilation rather than being copied, formatted, or
  attached to each event. The renderer owns only its output/status state.
- `JsonlBackend` (`jsonl.rs`) — serializes every routed event to one JSON line.
- `StatsHandler` (`stats.rs`) — counts events by name.
- `Capture` (`capture.rs`) — the test handler; copies events into an owned
  buffer for assertions. Gated behind `#[cfg(test)]`.

**`PublicTrace`** (`public_trace.rs`, `#[cfg(test)]`) — parses the rendered
public JSONL text a `JsonlBackend::new_public_writer` produces, the same
allowlisted stream `fz2 --log-telemetry` writes in production. `compile`
drives a source string to completion behind a public-only writer inside an
inner scope, drops the `Compiler2` so the buffered backend flushes its tail,
then parses the shared buffer into ordered `PublicEvent`s and paired
`PublicSpan`s. It parses text rather than reusing `Capture` because `Capture`
attaches ahead of the allowlist and would expose pre-projection `Any`
payloads a production reader of the JSONL stream never sees.

**Legacy compatibility surface** — `Event`, `Measurements`, `Metadata`, and
`Value` remain for legacy emitters and tests. They do not define the production
compiler2 payload model and do not enable raw events or spans.

**`EventKind`** (`handler.rs`) — raw lifecycle observers receive `Event`,
`SpanStart`, `SpanStop`, or `SpanException` with ids and optional elapsed time,
but no typed payload. Stats uses this surface without activating payload
handlers.

## Dataflow

```text
compiler<T>              ConfiguredTelemetry                  handler
-----------              -------------------                  -------
raw_event2(name, &a, &b) ─ exact arity callback for A, B ────▶ project/copy
raw_span1_1(name, &a)    ─ exact A start/B stop signature ───▶ project/copy
                         └ matching lifecycle observer ──────▶ ids/kind/time
```

The emitter constructs no telemetry payload. The handler receives raw references
only for the duration of the synchronous callback and owns every transformation
or retained copy. The bus borrows its handler list immutably for the dispatch;
attaching or detaching from inside a callback is a programmer error.

## Spans

A span is a timed region whose child events know their parent. Typed raw span
methods return the concrete sink's associated guard without erasing `T` or
copying the static name. `ConfiguredTelemetry` returns the RAII `Span<'_, T,
...>` and starts it only when an exact typed handler or a matching lifecycle
observer exists. The active guard owns the id and timestamp; drop emits a
payload-free stop for zero-stop-payload signatures or an exception during
unwinding. Explicit `stop1` and `stop2` lend their raw stop authorities
synchronously. `NullTelemetry` returns `NullSpan`, which has no state and no
drop glue.

While an active span is open, raw events receive its id and its parent id.
Lifecycle observers receive the same structure without registering interest in
the span payload.

```text
let span = tel.raw_span1_1(["fz", "compiler2", "job"], job)
  exact handler → start(id=7, parent=0, &Job)
  ... raw child events carry span_id=7 ...
span.stop1(completion)
  exact handler → stop(id=7, elapsed_ns, &JobCompletion)
  lifecycle observer → stop(id=7, elapsed_ns)
```

## Policy Choices

**Fatal vs telemetry.** A failure that must stop compilation returns
`Err(FatalError)`. Everything observational — including diagnostics that get
rendered as user errors — is an event. So the trait has no fallible method: a
handler cannot change what the compiler computes.

**Emitters pass authorities, handlers present them.** Raw emitters pass existing
references and direct scalars only. They do not format, clone, collect, query
`World`, or build metadata for telemetry. A handler that wants owned or
presentational data performs that work during the callback and copies only what
it retains.

**Routing is prefix plus signature.** A typed raw callback runs only when the
name matches its prefix and the event arity or span start/stop types match
exactly. A lifecycle observer is payload-free and needs only a prefix.

**Stats observes lifecycle without payloads.** `StatsHandler` counts raw events
by their `.`-joined name and raw spans as `.start`, `.stop`, and `.exception`.
Its lifecycle registration does not register interest in any typed payload.
`print_summary()` writes the sorted table to stderr after a run.

**Jsonl owns presentation.** `JsonlBackend` registers exact raw handlers and a
payload-free lifecycle observer, projects borrowed authorities during each
callback, and writes one JSON line. Emitters do not construct JSON fields.

**The bus is single-threaded.** No `Send`/`Sync`; the driver and each test hold
their own `ConfiguredTelemetry`. This is why handlers can share state through
plain `Rc<RefCell<…>>` while exact callbacks project or retain values.

## Compiler2 Conventions

Compiler2 uses telemetry as its only observability surface. `Compiler2<T>` owns
its lifetime-free semantic `World` and its `T: Telemetry` side by side. A drive
constructs a short-lived `ExecutionContext<'_, T>` that split-borrows
`&mut World` and `&T`; `World` never stores, accepts, or dispatches telemetry.
Every job/event
under `[fz, compiler2, ...]` flows through the compiler's one telemetry value.

**Emit points are cheap: raw borrowed authorities only.** An emit site places
existing references and direct scalars directly into a typed raw method. It
performs no formatting, processing, allocation, calculation, cloning, or World
lookup for telemetry. It passes O(1) immutable keys and the smallest borrowed
authority that already owns the decision, normally `&World`. The event does not
also extract a `FunctionRef`, source, body, dispatch plan, activation result, or
program from that authority. A handler that needs one copies or renders it
during the callback. The JSONL backend derives semantic activation inputs,
return evidence, and call summaries from `World` plus their keys.

Signals must be nonredundant. An id belongs either as a direct scalar or as the
key used to query an authority, never both under alternate names. Raw emitters
pass existing authorities by reference, borrowed byte slices, and direct
scalars. They never construct a display string, collect a derived vector, query
`World`, or clone a value for telemetry. A handler copies borrowed data only
when it retains that data beyond the callback. The compiler2 source-inventory
test rejects known construction and legacy emitter APIs in production paths;
typed callback signatures and code review establish semantic authority. The
test intentionally does not attempt interprocedural provenance inference.

Two recurring patterns keep emit sites clone-free and erasable:

- **Define in `World`, then pass the authority.** A `World::define_*` core owns
  mutation and invariants without accepting telemetry. Its typed
  `ExecutionContext::define_*` wrapper calls that core, then emits only
  `&World` and the fact key when the store reports an actual change. Event
  presence is the change signal; no parallel `changed` scalar is emitted. The handler performs any
  post-mutation lookup. A `store.define(k, v.clone())`, World getter, or
  projection written so an emitter can report a detail is telemetry work on the
  wrong side of the boundary.
- **Spans borrow.** Raw span start and explicit stop methods accept existing
  authorities by reference. The guard stores no payload for later projection.
- **Front doors borrow labels until storage.** CLI helpers, `compile_pipeline`,
  and `parse_quoted_program` thread `source_name` as `&str` across the public
  entry seams. If both the lexer and parser need the same label at once, they
  share one `Rc<str>` internally; owned `String`s are created only where a
  semantic storage actually requires ownership.

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
Revision **0** is a real, renderable value: it means a cumulative fact
(`ReturnType`, `ActivationInputs`) is present at the bottom of its join, which a
`Current` reader cannot tell from absence, so `null -> 0` on the stream is a
publisher appearing and not a change (`.agent/docs/fact-engine.md`, *Absence is
bottom*). Reading a stream for content movement means comparing
`old_revision.unwrap_or(0)` against `new_revision.unwrap_or(0)`, not comparing
the two optionals.

**Local type ids are world-owned facts.** Compiler2 `Ty` values are interned
`u32` handles owned by `World.types`. They are valid only inside that one
compiler world. Telemetry therefore treats them like `FunctionId` or `ModuleId`:
cheap compiler-owned identity, never a printable semantic contract by itself.
If a handler wants a rendered type, it must derive that rendering on its side.

**Drive and job spans are the execution spine.** `ExecutionContext::drive()` opens one
`[fz, compiler2, drive]` span. Each popped job opens one
`[fz, compiler2, job]` span. The drive span has no start payload and closes once
at the return boundary with the raw `DriveOutcome<Job, FactKey>` that the caller
receives. Successful job spans start with the raw `Job` already popped from the
agenda and close with raw `World` and `JobCompletion`; the same completion rides
the separate `[fz, compiler2, work_graph, applied]` event. Returned job failures
and panics close as payloadless exceptions under the start/stop signature. JSONL
handlers derive timing and presentation fields only after matching these raw
signatures. There is no separate per-outcome drive stop schema, extra
`job_fatal` event, or redundant `fact_published` stream.

The public JSONL projection (`jsonl.rs::write_opaque`) renders `Job`,
`FactKey`, `ProductKey`, `CallSiteKey`, and `TransportPosition` as
within-run identity, not a bare variant name: each carries its raw payload
ids (`root_id`, `function_id`, `arrow`, `code_id`, `module_id`, `callsite`,
`entry`, `semantic_index`, `need`, ...) alongside `kind`. `arrow` is the
interned `Ty`'s raw handle (`Ty::as_u32`), never `Types::display` — display
is measured non-injective and would conflate distinct activations that
happen to render the same. A raw handle is a within-run join key only; the
`fz.compiler2.canon.*` definition lines below are what make it mean something
to a reader in another process. This is what lets a reader of the public log
distinguish, for example, the many separate `AnalyzeActivation` evaluations
one real compile can produce, each a different `(root, function, arrow)`
triple where the projection used to render only `"kind":"AnalyzeActivation"`
for all of them alike. `DeriveExecutableFacts(E)` and
`FactKey::ExecutableFacts(E)` likewise render the complete executable identity;
the value is owned by `World` and its lifecycle is visible through the normal
`work_graph.applied` projection. There is deliberately no
`pull.product` event whose kind is `executable_facts`.
`ExecutableKey` and `TransportPosition`'s
`ExecutableSymbol` render the same way nested inside a `ProductKey`
(`BackendExecutable`, `TransportShape`, ...): activation identity plus
`need` (`"value"` or `"tuple_fields"` with a count). The blocked-wait lists
on `AppliedStep` and `JobCompletion` render each waited-on `FactKey` as its
own identity object, sorted as rendered strings (a presentation-boundary
sort) rather than as bare kind strings.

`[fz, compiler2, activation_inputs, budget_collapsed]` is public (fz-0xp,
allowlisted in `is_public_compiler2_trace_event`). It fires from
`ExecutionContext::complete_job` only when that completion widened at least one
correlated-input row set past `ACTIVATION_INPUT_ROW_BUDGET`, carrying
`measurements.collapses` — how many row sets the completion collapsed. A
collapse discards the correlation its publishers kept, so one wide activation
key stands where several narrow ones would have; since fz-kdt.106 nothing in
`fixtures2` produces one, which is what makes a single event worth reading.
The count reaches the emitter by the same producer/drain split
`flush_reported_warnings` and `take_quiescence_steps` use: the producer tallies
into an owned field, and `ExecutionContext` drains it with
`World::take_activation_input_collapses`, which is what lets a fact produced
inside a `World` method be reported by a `World` that holds no telemetry
handle. The field itself is `Types::activation_input_collapses` rather than a
`World` field, because the collapse fires inside
`ActivationInputAlternatives`' monotone join, whose `JoinContribution::Ctx` is
`Types` — an associated type no borrowed sink can ride without a GAT on every
implementor — and the join is measurably where every collapse happens (the one
path that could return a count to its caller, `push_row`, produced none of the
28/30 the lenses recorded before fz-kdt.106). Keeping the tally in the type
store makes it per-`World` by construction, so an undrained collapse dies with
the `World` that produced it instead of leaking into the next reader.

`[fz, compiler2, work_graph, applied]` is public (fz-kdt.34.3). It fires
unconditionally on every job completion — all five `ExecutionContext::
complete_job` call sites (`compiler.rs`, `drive.rs`, `product_drive.rs`,
`jobs/native.rs`, `jobs/macro_runtime.rs`) route through `emit_job_completion`
(`drive.rs`), which always emits it — carrying the raw `JobCompletion` under
`metadata.completion`. `write_applied_step_body` (`jsonl.rs`) renders the
shared `AppliedStep` body once and both the standalone `AppliedStep` opaque
arm and the `JobCompletion` arm call it, so the two can never drift apart:
`"changed"` is every `FactChange` as a full identity object (`kind` + ids,
`old_revision`/`new_revision`, `old_settled`/`new_settled`), in the
completion's own emission order; `"wakes"` is every `Wake` this completion
caused, in wake order, each `{"cause": <FactUse identity>, "job": <Job
identity>, "disposition": "enqueued"|"coalesced", "shift": bool}` —
`AppliedStep::wakes` replaced the old deduped `enqueued`/`coalesced` job
lists, so a job coalesced by two distinct causes in the same `Scheduler::
complete` call now renders as two `Wake` records, not one; `"movements"` is
the full post-wave `FactMovement` report, each entry a full identity object.
Both `"movements"` and the event's own `"semantic":{"reads":[...]}` (the
completed job's current `deps.reads`, read directly off
`World.work_graph.reads` at render time — nothing new is stored) are
rendered as presentation-sorted strings, because their source in both cases
is a `HashSet` with no meaningful iteration order — the same
presentation-boundary sort the blocked-wait lists already used.

`old_settled`/`new_settled` and `movements[].settled` render TRANSITIVE
finality (fz-kdt.44): `true` means the fact's whole upstream cone is
quiescent, not merely that its own publishers are clean
(`.agent/docs/fact-engine.md`, *Content, cleanliness and finality are three
questions*). Two consequences for anyone reading the stream. First, `changed`
arrays got SMALLER — a fact that is transitively unfinal stops flipping its
settled bit on each local dirty/clean cycle, worth -5% of the log on 00181 and
-30% on `enum_take_drop_split`. Second, the settled bit can now move with no
job completion behind it, so it gets its own event.

`[fz, compiler2, work_graph, quiesced]` is public. It carries a bare
`AppliedStep` under `metadata.step`, rendered by the same
`write_applied_step_body`, and fires when the drain arbiter
(`Scheduler::settle_quiescent`) discharges the settled questions standing at an
empty agenda. `blocked` is always empty and every `changed` entry is
readiness-only: `old_revision == new_revision`, `old_settled != new_settled`.
Without this event a fact's `settled` bit would change between
two `movements` renderings with nothing on the log to explain it, and any
evaluation woken by such a flip would classify as `Cause::Uncaused`.

Measured today the arbiter wakes NOTHING: the settled waits it answers belong
to the product pull (`jobs::artifact`, `jobs::backend`, `jobs::transport`,
`jobs::runtime_demand`, `jobs::root`), and the pull driver polls the fact
rather than registering a scheduler waiter. So `Cause::Readiness` remains
unobserved (fz-kdt.59) — but now for a stated reason, with the movement
already on the log the day a scheduler waiter does stand on one of these
facts. `the_drain_arbiter_publishes_readiness_only_movement_and_attributes_every_evaluation`
(`tests/fz2_cli.rs`) asserts the zero rather than assuming it.

The public stream is SELF-DESCRIBING (fz-kdt.34.6). A raw `Ty` or `FunctionId`
is a position in one `World`, so a log that carries only ids means nothing to a
second process — fz-kdt.47 measured 16 differing arena slots over four runs, and
the `World` that could translate them is gone by the time the log is read. So
the first time the sink renders a given raw id it emits a DEFINITION line first,
then the referencing event:

```json
{"name":["fz","compiler2","canon","type"],...,"metadata":{"type_id":133,"canon":"fp[F] (list(int)) -> r0"}}
{"name":["fz","compiler2","canon","function"],...,"metadata":{"function_id":230,"canon":"Enum.reduce/3"}}
```

`canon` is fz-f98.21's faithful canonical form (`types::canon::TyCanon` for a
type, `compiler2::canon::function_label` for a function), never
`Types::display` — display is measured non-injective, so two different
activations would compare equal. The `type` domain covers every raw `Ty` on the
stream: the `arrow` field and the elements of an `ActivationSymbol`'s `input`
array both resolve through it. The canonical form is an EQUIVALENCE, not an
injection on ids: two mutually-subtype arena slots share one canonical form and
are one identity to a reader, which is the point — that is the pair a
renumbering is free to swap.

This lives entirely in the sink (`CanonStream`, `jsonl.rs`). No production emit
site changed, telemetry-off renders nothing, and the cost is per DISTINCT id
(measured on `00181_enum_reduce_operator_ref`: 203 definition lines, 38KB, on a
917KB log). Definitions need a `&World`, which only some events carry, so a line
naming a still-undefined id is PARKED until an event arrives that can define it;
once anything is parked everything parks, so the stream's own order never
changes and a streaming reader never sees an id it has no dictionary entry for.
On `enum_take_drop_split`, 128 of 325 distinct types are first named by an event
that carries no world — 99 by a `pull.product.settled`, 29 by a `job`
`span_start` whose `span_stop` carries the world a few lines later.

`telemetry::causal` (`causal.rs`, `pub`, re-exported as `fz::causal`) replays a
public log into a `CausalReport`: per canonical formula identity, evaluations
classified `Initial`/`Content`/`Readiness`/`Uncaused` plus changed outputs,
wakes and blocked completions; per canonical `ProductKey`, settlements,
generations, the changed split, cache hits and displacements; the summed
session tallies; per FACT KIND a `FactLifecycle` (distinct facts, first
appearances, retractions — `first_appearances > distinct` is the
retract-and-remint signature); and a `ShiftWork` count of shift-classified
wakes and rebased completions. Causality is DERIVED, never stored: for evaluation `e` of
formula `F` at stream position `t`, the moved inputs are `(F's reads UNION F's
blocked-set from its previous completion)` for which a movement appears in
`[F's previous conclusion, t)`. Both boundaries are load-bearing and both are
measured — `reads` alone false-flags wait-satisfied jobs as uncaused, and the
window must INCLUDE the previous conclusion because a formula that writes a fact
it also reads wakes itself. Raw ids are the within-run join key; the canon
tables are applied at report time, which is what makes `canonical_multiset()`
comparable across processes. Never infer identity or causality from counts: both
are on the stream exactly.

The `[fz, compiler2, job]` span still covers only two of these five
completion sites (`drive.rs`'s and `product_drive.rs`'s job-pop loops, the
only two callers wrapped in `start_job_span`/`stop_job_span`); that stays a
deliberate timing-only measurement, unchanged by this. `work_graph.applied`
is the one signal that observes every completion — it is the causality
record, the job span is the clock.

When the agenda drains with unresolved waiters, `ExecutionContext::drive()`
(`drive.rs`) runs its stall pass: it demands every submitted root's entry
analysis and, for each blocked waiter's fact not already demanded since the
last content change, pokes that fact's mapped producer through the
fact->producer map (`demand_fact_producer`). If that expansion pokes at least
one producer, the pass emits `[fz, compiler2, drive, demand_on_stall]`
(raw event, no span) with `&u64` for the total pokes this round and the
existing demanded fact set (`&HashSet<FactKey>`) as a raw borrow. `demand_on_stall`
is public (allowlisted in `is_public_compiler2_trace_event`, `jsonl.rs`):
its projected metadata carries `"producer_pokes"`, a `"demanded_facts"`
object with `"count"` and a `"facts"` array of presentation-sorted full fact
identities (`kind` + ids, via `render_fact_identity` — the same
presentation-boundary sort `blocked`/`movements` use, since the source is a
`HashSet`), and a hard-coded `"reason":"blocked_waiter_expansion"` — safe to
hard-code because `demand_on_stall` has exactly one emit site and every
member of the demanded set was passed through that one call to
`demand_fact_producer(fact, WorkStartReason::BlockedWaiterExpansion)`. This
lets a public trace name *which* facts were stalled and why, not just that a
stall-demand happened — the aggregate `pull.session.finished` tally
(`work_starts_blocked_waiter_expansion`) says how many; this event says
which one, and its fact->producer expansion is readable from the same log by
matching the next `work_graph.applied` completion the fact's producer job
runs as. One caveat: `stall_demanded` (and so `"demanded_facts"`) is
cumulative across stall passes within a single drive — it is cleared only
when something changed since the last stall (`changed_since_stall`) — so
each event carries the running demanded set at that pass, not a per-pass
delta; a later event's `"facts"` is a superset of an earlier one's unless the
set was cleared in between. A round with `producer_pokes == 0` is a genuine
stall: the drive breaks out and reports `DriveOutcome::Unresolved` instead of
emitting the event. Separately, `[fz, compiler2, drive, timed_out]` fires
when a deadline passed to `drive` elapses mid-agenda, before any stall pass
runs. It carries only the independently semantic raw configured timeout;
`pending_jobs` and `jobs_ran` belong to the drive span's raw `TimedOut`
outcome. JSON and test handlers derive `timeout_ms` during the callback.

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
  def nm: (.name | join("."));
  "job_starts=\([.[] | select(nm=="fz.compiler2.job" and .kind=="span_start")] | length)",
  "root_sessions=\([.[] | select(nm=="fz.compiler2.pull.session.finished")] | length)"
' /tmp/fz-00181.jsonl
```

The fixture call-edge oracle sources its activation set from
`Compiler2::product_executable_inventory`
(`compiler.rs`), which drives the root through the product backend path and
collects `driver.session().materialized_executables()` — there is no separate
frontier scan.
The root session carries the raw `PullSession`. An in-process
handler derives scheduler counters, demanded-set cardinalities, and root
identity during the callback instead of making the emit site traverse the
session. Backend dumps may be requested with `--dump
backend=/tmp/fz-00181.backend`; types and activations are served synchronously
from the product-path activation inventory.

Transport product construction emits `[fz, compiler2, pull, product, *]` for
per-position product demand. There is no root-wide `transport_flow` signal: the
legacy `DeriveTransportPlan` job that emitted it — and its `TransportPlan(root)`
fact — do not exist. The product path treats the
`RuntimeDemand(E)` product as pre-transport evidence; `TransportPosition ->
ShapeId`, `CallableId` facts, `BoundaryId` contracts, and `CodegenSeamFact` rows
are produced for the positions and boundaries named by demanded executable
products. Tests assert ShapeId relationships from the demanded
`MaterializedTransportPlan` when correctness depends on sharing.

`ProductDriver`/`ProductMemo` (`pull.rs`) expose four
`[fz, compiler2, pull, product, *]` leaves, all public (allowlisted in
`jsonl.rs::is_public_compiler2_trace_event`). `cache_hit` and `reentered` carry
the existing raw `ProductKey` and identify paths that do not run a producer.
`displaced` carries the raw `ProductKey` of a settled product the memo just
displaced (rejected group member, or a reader invalidated by a changed
dependency, stale fact, or explicit reproduction) -- Waiting outcomes do not
claim completion, and there is no `requested`, `produced`, `waited`, or generic
`finished` alias.

`settled` is the memo's own act of installing a value, not the driver's: it
fires once per PRODUCT that actually settles, from inside `ProductMemo::finish`
and `ProductMemo::finish_group` -- the single authority for both. A group
settle (`finish_group`, e.g. a callable-construction or transport-shape SCC)
fires once per member, not once for the anchor `ProductDriver::pull` happened
to be pulling; `ProductReadContext::publish_product`'s co-published members
(a demand cone's non-anchor executables, an effect SCC's non-anchor
executables) settle through the same `finish` authority and are equally
visible. The event carries the raw `ProductKey`, the authoritative
`ProductValue`, and a stack-built `ProductSettlement { generation, changed,
group }`: `generation` and `changed` are the memo's own bookkeeping (no
longer discarded after computation), and `group` is `Some(id)` for every
member of one group settle (a monotone id, distinct per settle, `None`
outside a group).

Transport uses the same product events. A settled `TransportShape(position)` or
`CallableConstruction(position)` event carries the raw `ProductKey`,
`ProductValue`, and `ProductSettlement`; handlers inspect the borrowed
position-owned answer directly. There is no parallel projection, component, or
solve event.

`[fz, compiler2, pull, session, finished]` (`pull.rs::PullSession::emit_finished`,
called from `ProductDriver::finish_session`) fires once per pull session, when
the driving front door finishes demanding the session's products. It carries
the raw `PullSession`, from which handlers derive its root and demanded
set cardinalities, `producer_pokes`, per-reason work-start breakdown,
`unsanctioned_work_starts`, and `root_scans` during the callback. The emitter
does not duplicate those values into measurements. This is the root-level
authority a handler reads to assert product-path work stayed bounded, and
`work_start_reason_test`'s
`pull_only_guard_holds_for_*` cases assert `unsanctioned_work_starts == 0`,
`root_scans == 0`, AND `ignition == 2` (the true external front-door count)
for every fixture they drive.

### Work-Start Attribution (`WorkStartReason`)

`Scheduler::enqueue` tags each agenda insertion with the existing reason it
started and tallies those tags in `WorkStartTally`; the finished `PullSession`
is the raw telemetry authority. The sanctioned reasons mirror the pull model:

- `Ignition` is the one job started by an external code, interface, or root
  submission.
- `ChangedRevisionWake` is scheduler-owned wake propagation after a subscribed
  fact changes.
- `StandingRootFrontier` and `ActivationFrontier` expand standing semantic
  demand through the fact-to-producer map.
- `BlockedWaiterExpansion` expands a drained waiter's missing fact to its
  producer, including runtime-module indexing.

`Unclassified` is the default and makes an untagged enqueue fail the running
guard through `unsanctioned_work_starts`. The fixture guard also pins
`ignition == 2`, so internal work mislabeled as an external start fails. Other
deliberate mislabeling remains a review concern made visible by the session's
per-reason breakdown. Bounded inner product pulls complete directly rather
than entering the shared scheduler agenda, so they have no work-start tag.

Macro executable readiness emits `[fz, compiler2, macro_executable, defined]`
with raw `World` and `FunctionId`; handlers select the stored executable and
backend revision during the callback. Artifact tests still assert the
`JobEffects` facts and absence of `NativeProgram(macro_root)`.

Macro expansion emits `[fz, compiler2, macro, expanded]` after a
`MacroExecutable` runs over quoted source and before recursive expansion
continues. Its exact raw signature is `(&World, &FunctionId,
&QuotedSourceRoot)` for the expanded output. Handlers derive module identity
and quoted-source heap/root identity during the callback. The shared quoted
expander emits the same event for item macros and demanded function-body macros.

Demand-time body staging emits `[fz, compiler2, function, source, expanded]`
when `ExpandFunctionSource(function)` materializes `ExpandedFunctionSource`.
It carries raw `World` and `FunctionId`. A handler
selects quoted-source identity during the callback. `ScopeCode` does not emit
this event for ordinary undemanded bodies; item-macro publication remains
scope-order work, while body-local expansion remains demand-time work.

Source-order compiler services emit `[fz, compiler2, compiler_service, define]`
when `Fz.Compiler.define` publishes an expanded source root. Its exact raw
signature is `(&World, &FunctionId, &FunctionSource)`. Handlers derive ids,
namespace, and quoted-source identity during the callback. Literal functions,
protocol callbacks, synthesized module-info functions, item-macro returned
definitions, and explicit compiler-service forms all use this same event.

World-owned definition events share one schema instead of reconstructing each
stored fact beside its owner. The observer-free `World` core mutates first; a
typed `ExecutionContext::emit_*` helper runs only when that mutation reports a
change. The raw callback receives `World` plus the stable
key that addresses the result: `FunctionId`, `ModuleId`, `RootId`, `TypeName`,
`ActivationKey`, or `CallSiteKey`. Generated-function publication adds its raw owner key. A
handler reads the stored function source, contract, lowered body, dispatch,
type, protocol wiring, activation analysis, callsite summary, backend program,
or native program from those authorities during the callback.

Type-reference publication keeps the two owning key domains explicit.
`[fz,compiler2,type,references,function,recorded]` carries raw `World` plus
`FunctionId`; `[fz,compiler2,type,references,type,recorded]` carries raw
`World` plus `TypeName`. There is no generic `consumer_kind`/`Value` envelope,
and recording borrows the source `TypeName` while the semantic map takes its
own required key clone.

This schema covers function `defined` and source `stashed`/`noted`/`expanded`,
function contracts, lowered bodies, guard and entry dispatch, modules, structs,
types, protocol dispatch, activation analysis, callsite summaries, backend
programs, native programs, roots, and code submissions. `input_demand.derived`
and `native_program.reusable_cons` already own their result outside `World`, so
they carry the raw key and artifact directly. Code submission carries raw
`World` plus either its `CodeId` or the existing runtime-module registration
result. No event duplicates ids, arities, counts, names, source references, or
stored artifacts.

Scheduler completion events carry raw `JobCompletion`. The
`work_graph.applied` and job-span handlers read its job and applied step;
production handlers observe changed facts, movements, wakes, and waits from
that step. Published keys remain in the scheduler's per-job claim ledger;
test-only output capture reads those standing claims from `World` instead of
making every completion rebuild them. One `activation_inputs.defined` event
carries the same completion plus `World`, and handlers iterate its affected
activation-key set.
Return publication carries raw `World` plus `ActivationKey` only when the
stored return changes. Event presence is the change signal; handlers read the
settled return from `World`. `return_type.widened` is a separate raw
`World`-plus-key event emitted only when the widening operator coarsens the
candidate.

`root.submitted` carries raw `World` and `RootId`. `code.submitted` carries raw
`World` with the submitted `CodeId` or runtime registration. Protocol callback
and implementation events carry raw `World` plus their already-existing
function/protocol/target keys. The reusable-cons handler derives its counts
from the raw `BackendProgram`.

`--dump` output is synchronous requested output, not telemetry. One
`RequestedOutputSink` receives types, activations, backend, native, FNIR, and
CLIF at the compiler boundary where each authority is populated. The null sink
is inert. A file sink selects requested kinds and renders or copies immediately;
requesting no dump cannot enable telemetry or retain compiler borrows.

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
surface; its source-production macro/sugar fixture test asserts successful
execution and the compiler2-only telemetry namespace. Its
`Enum.reduce` CLI probe also asserts that `lexer.pass` span-start events match
the exact submitted source set one-for-one: user source plus the demanded
runtime sources, with no duplicate pass and no fragment pseudo-source. The
quicksort CLI probe carries the original perf question: on 2026-06-10,
running `target/debug/fz2` with telemetry on `fixtures2/behavior/quicksort.fz`
emitted four lexer span-starts, exactly
`fixtures2/behavior/quicksort.fz`, `runtime:runtime.fz`, `runtime:Kernel.fz`, and
`runtime:Process.fz`. The old source-fragment re-lex is gone by construction.
`fz.compiler2.native_backend.compile` and its `fz.codegen.compile` child account
for the post-drive native tail without conflating it with source production.

Useful reruns:

- `cargo test --lib compiler2_ -- --nocapture`
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
boundary span and carries no reconstructed program summary. The raw
`fz.codegen.compile` span nests under it, so a trace can account for both the
fact drive and the post-drive native backend tail without treating codegen as
an unattributed gap.

Compiler2-native codegen keeps topology and timing on the
`fz.codegen.compile`, `declare`, `lower_function`, `define_function`,
`emit_runtime`, and `finalize` spans. Their starts carry no reconstructed
program summary. The `define_function` span stop carries the raw
Cranelift `Context`; handlers derive compiled code size while that context is
valid.

ABI, callable-boundary, and closure-call correctness belong to the published
`NativeProgram`, generated CLIF, and runtime behavior. Compiler2-native does
not emit parallel events that reconstruct those facts from codegen locals.
Tests inspect the owning artifact or execute it instead.

## Telemetry In Tests

The bus is the test seam for "did the compiler make the decision I expected?"
without `#[cfg(test)] pub` peepholes into pass internals. Tests attach exact raw
callbacks for payload-bearing events and copy only the assertion state they
retain. `Capture::install` combines legacy capture, raw diagnostic capture, and
the payload-free lifecycle observer for structural event/span assertions.

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
right result. Real codegen tests inspect the published native artifact and pair
that structural evidence with CLIF or runtime behavior. Event-time handlers are
used only when a raw codegen authority needs to be projected for timing or
regression measurements.
