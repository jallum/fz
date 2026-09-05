# Performance Instrumentation

Compiler2 is meant to do the least work it can, only when something needs it,
and to keep the answers it already has. Cost should track the complexity of the
code being compiled. On a small program a compile measured in seconds does not
mean the work was hard; it means work was repeated, or was scoped to more of the
program than the change required.

This doc is about the instruments that answer *where the time went and why the
work started*. The bus those instruments ride on is
[`telemetry`](telemetry.md); the running scheduler's own events are
[`runtime-telemetry`](runtime-telemetry.md).

## The front-door switches

Both are global arguments and go **before** the subcommand:

```
fz2 --log-telemetry <path> interp prog.fz     # JSONL event stream
fz2 --emit=stats            interp prog.fz    # event counts by name, on exit
```

`--dump <kind>=<path>` is per-command (`run`, `build`, `interp`) and writes a
stage artifact rather than a measurement: `activations`, `types`, `backend`,
`native`, `fnir`, `clif`.

`--log-telemetry` installs `JsonlBackend::new_public_file`, which filters to the
public compiler2 trace: `is_public_compiler2_trace_event` in
`telemetry/jsonl.rs` is the allowlist, and an event whose name is not on it does
not reach the file. Each emitter also needs an `install_raw_value` registration
for its payload type, or the event arrives with no fields. Both are required —
a new counter that appears empty in the JSONL is usually missing one of them.

## What the stream carries

**Job spans** — `fz.compiler2.job`, `span_start`/`span_stop`, carrying the job's
full identity (kind plus `root_id`/`function_id`/`arrow`/... as applicable) on
start and elapsed time on a payload-free stop. Pair them by `span_id` for a
per-formula time census. This covers the drive loop only, and only two of the
five completion sites; a product settled during a pull is not a job. The span
is the clock — `work_graph.applied` owns the completion payload and causal
record exactly once, and it fires on every completion.

**Job completions** — `fz.compiler2.work_graph.applied`, one per applied job,
carrying the completed formula's identity, the exact facts it changed with
before/after revision and settledness, the wakes it caused with their causes,
the full movement report, its blocked waits, and its read set. This is what an
investigation reads: which formula ran, on what evidence, and what it moved.

**Product settles** — `fz.compiler2.pull.product.settled`, carrying the
product's full identity (kind plus the executable/position it is filed under)
and its `ProductSettlement { generation, changed, group }`. There is no span, so
cost is attributed by taking the gap between an event and the one before it. A
product that settles a recursive group publishes its members atomically and
reports the group id on each.

**Product requests and evaluations** — `pull.product.requested` fires for
every stack pull, including requests answered from the memo;
`pull.product.evaluated` fires only when the producer body actually runs and
shares the request's session-owned `ProductRequestId`. The allocator remains
with a retained session, so ids increase across request activations. Exclusive driver
ownership and the producer's context-only API make overlapping pulls
impossible; cache requests have no evaluation. The evaluation
also carries its structured outcome plus exact product/fact waits. A producer
that settles another key emits `pull.product.copublished` with both publisher
and peer. Successful recursive settlement emits `pull.recursive_group.published`
for every actual member, again with publisher and peer. Cache hits,
displacements, settlements, requests, evaluations, general co-publication, and
recursive-group membership are distinct observations over the same structured
`ProductKey` identity. The driver caches whether any typed causal subscriber is
present; without one these new hot-path events do no registry traversal or
payload construction, and no session id is minted.

**Backend requests and pull sessions** —
`fz.compiler2.backend_request.started` / `finished` bracket one request for a
root backend program. Both boundaries use one gate and one typed payload;
finish says either `success` with final population or `failure`, so partial
subscriptions and errors cannot leave the public lifecycle structurally
unbalanced. `pull.session.started` / `finished` carry the same exact
numeric session id; nested sessions therefore have balanced lifecycles without
erasing the outer session's replay history. Backend request, retained session,
and product request are separate identities: successive backend requests
reactivate the same root session id, while nested roots use different session
ids and product request ids never repeat within a retained session.
The finished session's producer-poke and work-start fields are activation-local
deltas. `ProductSessions` partitions the World's monotone work-start counters
across its nested activation stack and gives standalone `Compiler2::drive` its
own balanced owner boundary, so nested sessions neither overlap the standalone
prefix nor charge a later cache hit for work performed outside its request.
When an interp, native, or macro consumer needs the World projection,
`pull.product.projected` carries the exact structured root product, retained
session id, product request id, settled generation, and fact movement. Causal
replay matches all three identities before accepting that movement. This is a
product projection, not another scheduler-formula evaluation; the three cold
fixture totals consequently contain two fewer formula evaluations than the
pre-retention baseline (1215, 1885, and 3169).
That classification travels with `JobEffects`, so an explicitly queued
`BuildBackendProduct` cannot silently become formula work at the shared
completion boundary.
Same-root artifact jobs stay in the agenda while the retained request
reconciles edits. The agenda's root-scoped pop parks only matching jobs it
encounters on the FIFO walk; it does not rescan the whole queue after every
completion. Parked jobs still coalesce duplicate demand, are excluded from the
runnable length, and are restored on every request exit. Total pending-job
counts still include them, so timeout diagnostics do not hide queued work. The projection takes
the one parked backend job directly, so an equal retained hit adds neither a
producer evaluation nor an artifact retraction/republication.

**Work starts** — `fz.compiler2.pull.session.finished` carries the
`WorkStartTally`: `ignition`, `changed_revision_wake`, `activation_frontier`,
`blocked_waiter_expansion`, plus `unsanctioned_work_starts`, `root_scans`, and
`drain_discovery_sweeps`. This is the pull-only guard's evidence — every job on
the agenda must name a sanctioned reason. All three scan/unsanctioned counters
are zero, and `compiler2::work_start_reason_test` holds them there: a
reintroduced job-pushes-job path lands in `Unclassified` by construction, and a
producer that discovers work by scanning the fact table shows up in `root_scans`.
`drain_discovery_sweeps` counts the narrower empty-agenda pass that clones and
orders the activation-frontier and unresolved-wait inventories; exact nonempty
indexes guard that work, so unchanged and irrelevant retained requests do not
increment it.
`activation_frontier` counts root-entry and caller-discovered-callee analyses
ignited from their published `Activation` edges. The typed regression pairs
`SeedRoot`'s claimed activation with the exact accepted frontier key and pins
the combined fixture population: 3 root plus 265 callee starts become 268
starts on the shared frontier, so compensating aggregate counts cannot hide a
second root path.

**Runtime-demand facts** — `work_graph.applied` names each
`DeriveRuntimeDemand(E)` completion, its exact reads, content movements,
readiness changes, and wakes. Group by the typed executable identity to measure
formula evaluations, and distinguish content-changing runs from readiness-only
finality. Because each formula is one ordinary scheduler job, these counts are
the work itself; there is no hidden cone member/round multiplier. Compare the
causal work multiset across legal arrival orders and retained requests, and
pair it with the canonical backend and runtime output so less work cannot hide
a changed result. `RuntimeDemandInputs(E)` is an independently revisioned view
of the input vector in the one stored demand value. On
`00420_enum_take_drop_split`, deleting the root/function callable-row aggregate
removed its 434 refolds and 273 signals; exact target/sub-fact reads reduced
changed-revision starts from 2,870 to 2,769. The resulting split is 1,730
unchanged non-demand starts plus 1,039 exact demand changed-revision starts;
1,278 RuntimeDemand formula evaluations occur across all start causes. Blocked expansion is
1,140 unchanged non-demand work plus 311 exact demand/construction formula
keys. Compare those explicit counts with the removed cone's 6,250 hidden member
derivations; none is a wall-clock claim.

The pre-deletion full-matrix census at exact old HEAD `7f2bcc2de` drove all 515
non-deferred fixture paths through run/interp/build serially. Its 1,708
`demand.cone.settled` events all reported `external_members=0`; the exact
command and result live in
`.agent/measurements/fz-kdt.4-external-members-census.txt`. The removed
external/displacement path therefore had no observed owner to preserve.

**Recursive-group searches** —
`fz.compiler2.pull.recursive_group.searched` carries the current product, the
prospective dependency, and one `RecursiveGroupSearch`. `candidate_inventory`
counts reachable products with freshly evaluated pending snapshots of the
publishing kind; `vertex_visits` counts all reached pending products, including
cross-kind bridges; and
`edge_scans` counts their pending dependency edges. `cycle_closed` says the
component contains the current product, and `group_members` counts only its
same-kind members. One dependency-rooted Tarjan traversal supplies all six
values. The prospective edge is recorded before borrowing the dependency map;
there is no graph copy, separate early-exit reachability pass, or repeated scan
per candidate. Displaced dependency history cannot participate in the search.
Causal replay compares both these totals and the exact current-graph
publisher/member identities. Search events are query work; successful
`pull.recursive_group.published` events separately report exact actual members.
After `fz-kdt.4` changes the RuntimeDemand graph, `fz-tfn.2` re-establishes this
same exact membership contract on that new graph.

## In tests

`Capture` and `StatsHandler` (`telemetry/`) attach to a `ConfiguredTelemetry` in
process: `StatsHandler::counts()` for event totals, `Capture::last(&name)` for a
payload. `telemetry.attach_raw_event1::<PayloadType, _>(&name, closure)` reads a
typed payload directly, which is how a test asserts on a counter rather than on
elapsed time. `compiler2::telemetry_dump_test` holds two `#[ignore]`d harnesses
that dump a full JSONL trace for one-off analysis.

Prefer asserting a count, a round, or a work-start reason over asserting a
duration — the first three are properties of the program and the lattice, and
the last is a property of the machine.

Never infer identity or causality from counts. Two `AnalyzeActivation`
evaluations are not "the same job twice" because they share a kind, and an
evaluation is not caused by whatever happened to precede it. Both questions are
answered exactly, from the log, by `telemetry::causal` (below): identity comes
off the event, and causation is derived by replay.

## Causal replay (`telemetry::causal`)

`CausalReport::derive(&parse_public_trace(&log))` turns a public log into work
counts. Nothing else is needed — not a `World`, not the process that wrote it.

Per FORMULA (canonical job identity): evaluations, split into `initial`,
`content_caused`, `readiness_caused` and `uncaused`; changed vs unchanged
outputs; wakes emitted; completions that ended blocked. Product rows retain the
raw structured `ProductKey`, so arena-distinct keys cannot overwrite each
other. `canonical_multiset()` is a separate projection which folds equivalent
raw rows only for cross-process comparison. Product rows count settlements,
the changed/unchanged split, cache hits, and displacements. Session tallies are
summed from balanced finished lifecycles.

`CausalReport::derive_requests(events)` returns that vocabulary once per
backend request. Product rows additionally separate requests, producer
evaluations, first productions, retained cache hits, changed/equal
reproductions, recursive peer publications, and first-generation products
recomputed after an earlier request. Every evaluation also retains one exact
causal record: session, request id, raw product, prior waits, prior evaluation
position, matching trigger positions and kinds, and cause class. The enclosing
report supplies backend-request identity. Triggers are
fact movement, product settlement or cache-hit readiness, dependency or self
displacement; records, not aggregate counters, are authoritative. The
`requested` and `evaluated` events for a producer run share an exact
session-local request id. Exclusive driver ownership prevents overlapping
requests, while cache-only requests have no evaluation. Recursive searches
performed by a producer run are measured as work rather than misreported as
its cause. Each recursive-search record retains its structured product and
dependency identities and the enclosing evaluation's cause. Each successful request boundary
carries the final reachable executable and construction-wrapper population, so
a future root cache hit reports population without requiring a new settlement.

Reproduce the long-lived baselines with:

```
cargo test --lib target_fixture_reports_exercise_all_five_request_scenarios -- --nocapture
cargo test --test fz2_cli target_fixture_public_causal_and_backend_observations_are_reproducible -- --nocapture
```

The first command runs cold, unchanged, unreachable edit, reached-leaf edit,
and callee replacement for each of the three exact target fixtures. It proves
that all five request reports are separated and internally exact. The second
produces one immutable observation bundle per fixture, each containing two
separate-process public reports, runtime outputs, and canonical backend dumps.
One immutable observation spec is the authority for the front door, public
telemetry, backend dump, inherited environment, process invocation, and failure
context. A controlled child proves inherited environments preserve ambient
values while fixed environments clear them. Owned trace and dump paths remove
partial files on an early return.
Pure named ratchets fan over those same bundles to compare every canonical work
dimension with zero exclusions and prove byte-identical backend output. This
removes one duplicate three-fixture producer pass: three bundles and six
subprocess compilations replace six bundles and twelve subprocess compilations.
No command interprets elapsed time as correctness.

The 2026-09-04 combined-stack baseline makes the retained-work problem
explicit. Columns are producer evaluations / settlements / distinct demanded
products / unexplained producer evaluations; the final pair is reachable
executables + construction wrappers:

| fixture | cold | unchanged request | population |
| --- | ---: | ---: | ---: |
| `fz_f98_range_map_converges` | 2986 / 2147 / 2086 / 15 | 0 / 0 / 1 / 0 | 62 + 0 |
| `enum_predicate_search` | 7584 / 5430 / 5056 / 35 | 0 / 0 / 1 / 0 | 168 + 32 |
| `00420_enum_take_drop_split` | 16028 / 12309 / 11815 / 40 | 0 / 0 / 1 / 0 | 239 + 38 |

`ExecutableEffects(E)` is now an ordinary formula over its local materialized
effect and the exact `ExecutableEffects(callee)` products. That makes 62/123/187
additional cold producer evaluations and 4/10/9 additional demanded product
keys visible for the three fixtures above. The settlements, distinct
generations, first productions, formula evaluations, backend artifacts, and
runtime outputs do not change. Before this cutover, one effect producer hid a
transitive materialized-executable walk and a private SCC fixpoint behind a
single evaluation and co-published the other answers. Ordinary member
evaluations now perform their local joins over recorded dependency edges. The
evaluation that closes a recursive group joins the already-recorded member-local
and external inputs once, then publishes the group's common idempotent answer.

On `00181_enum_reduce_operator_ref`, `List.reduce_cont/3` first waits on
`List.reduce_step/3`, which waits back on `List.reduce_cont/3`. The second
reduce-cont evaluation closes and settles both executable-effect products at
generation 1 under one group id. Each member already has one suspended request
on the pull stack, so those requests resume as one cache hit per member without
another producer evaluation. The old cone path instead left one cached
`Enum.reduce/3` effects request; removing that hit and adding the two group
member hits moves the fixture total from 18 to 19 while settlements,
generations, backend output, and runtime output remain unchanged.

The additional 3/5/13 unexplained product evaluations are recursive effect
members retried from an `ExecutableEffects(callee)` wait without an intervening
product movement. `fz-tfn.32` owns finding and correcting that generic
product-wait retry cause; it must not become an effect-specific path or a
causality exception.

The retained unchanged request does zero scheduler-formula evaluations, zero
product evaluations, zero settlements, and zero cross-request recomputations.
It makes one request for `RootBackendProduct`, records one retained cache hit,
and does not enter the scheduler drive or move `BackendProgram`. An unreachable
edit has the same product profile and zero displacements; only its two
source-processing formula evaluations run. Once that exact agenda drains, an
O(1) check of the activation-frontier and waiter indexes avoids cloning or
ordering either empty inventory. Reached edits evaluate only the displaced
dependency closure.

Cold, unchanged, and unreachable-edit requests have zero unexplained formula
evaluations on all three fixtures. Reached-leaf and callee-replacement requests
retain the exact unexplained formula counts 39/45, 90/122, and 156/185 in the
table order. They remain visible in both `FormulaWork.uncaused` and the exact
`CausalReport::uncaused` records, whose lengths the harness cross-checks. They
are not a cross-process exclusion or a cause inferred from nearby traffic.
Product evaluations have their own explicit unexplained class, reported in the
table above; no nearby settlement is invented as a cause.
Product identity is the structured key fields after removing JSONL renderer
metadata such as `opaque_type`; otherwise the same key nested in an outcome
wait would fail to match its top-level settlement solely because the renderer
annotates those two positions differently.

An evaluation is caused when a dependency MOVED in `[the formula's previous
conclusion, now)`, where the dependency set is the completion's `reads` UNION
the blocked-set its PREVIOUS completion recorded. `reads` alone is not enough —
`reads` and `waits` are separate maps, so a job re-run because a wait became
satisfiable has the fact only in `waits`.

`canonical_multiset()` is the comparand for two runs. Every count is keyed by
canonical identity, so two processes can be compared even though their arenas
renumber. It emits each canonical product/fact identity once, uses stable
dictionary ids in grouped evaluation/search signatures, and omits zero rows;
canonical text is report output, never replay authority. Typed owner-ordered completion waves make the complete causal
inventory reproducible: requests, evaluations, settlements, cache behavior,
recursive membership, grouped triggers, lifecycle/retraction and shift totals,
outputs, and population are all compared with no product-specific exception.

## Reading the numbers

Counts and per-unit costs answer different questions, and the interesting
failures show up in only one of them. A ladder of programs built from *n*
identical call sites separates them: complexity grows strictly linearly, so
anything that does not grow linearly is structural.

A product whose settle **count** grows with the program and whose **cost per
settle** stays flat is incremental — that is the shape to expect.
`abi_executable` holds flat per-settle costs across a 32x ladder.
`ExecutableFacts(E)` now appears in formula evaluation counts as the direct
`DeriveExecutableFacts(E)` job and in the fact publication/read ledger; it must
never appear in any per-product count. A product whose settle count is *constant* while its per-settle cost
grows is a pass wearing a product's clothes: its unit of work is the program,
not the key it is filed under.

`runtime_demand_facts_converge_across_independent_self_and_mutual_schedule_orders`
(`compiler2::drive_test`) perturbs root arrival while pinning the canonical
backend, runtime output, and exact `DeriveRuntimeDemand` work multiset.
