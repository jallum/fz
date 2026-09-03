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
full identity (kind plus `root_id`/`function_id`/`arrow`/... as applicable).
Pair them by `span_id` for a per-formula time census. This covers the drive loop
only, and only two of the five completion sites; a product settled during a pull
is not a job. The span is the clock — `work_graph.applied` is the causality
record, and it fires on every completion.

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
shares the request's session-local `ProductRequestId`. Exclusive driver
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
erasing the outer session's replay history. Request and session are separate
identities, so successive requests in one `Compiler2` cannot be conflated and a
future retained session may span request boundaries without changing the report
model.

**Work starts** — `fz.compiler2.pull.session.finished` carries the
`WorkStartTally`: `ignition`, `changed_revision_wake`, `activation_frontier`,
`blocked_waiter_expansion`, plus `unsanctioned_work_starts`
and `root_scans`. This is the pull-only guard's evidence — every job on the
agenda must name a sanctioned reason. `unsanctioned_work_starts` and `root_scans`
are zero, and `compiler2::work_start_reason_test` holds them there: a
reintroduced job-pushes-job path lands in `Unclassified` by construction, and a
producer that discovers work by scanning the fact table shows up in `root_scans`.
`activation_frontier` counts root-entry and caller-discovered-callee analyses
ignited from their published `Activation` edges. The typed regression pairs
`SeedRoot`'s claimed activation with the exact accepted frontier key and pins
the combined fixture population: 3 root plus 265 callee starts become 268
starts on the shared frontier, so compensating aggregate counts cannot hide a
second root path.

**Demand cones** — `fz.compiler2.demand.cone.settled` carries `members`,
`external_members`, `rounds`, `derivations`. `RuntimeDemand(E)` is settled by a
Jacobi ascent over a cone of executables collected transitively from its anchor,
stopping only where demand has already settled, so `members` — not the one
executable the key names — is the unit of work behind the answer.
`external_members` counts the boundary it did reuse. `rounds` is the height the
ascent climbed and `derivations` the member re-derivations it ran, which is well
under `members * rounds` because a member whose reads did not move is skipped.
Separating the three tells a cone that is too big from an ascent that climbs too
far from members that re-derive too often; a wall-clock number cannot.

**Recursive-group searches** —
`fz.compiler2.pull.recursive_group.searched` carries the current product, the
prospective dependency, and one `RecursiveGroupSearch`. `candidate_inventory`
counts reachable unsettled products of the publishing kind; `vertex_visits`
counts all reached pending products, including cross-kind bridges; and
`edge_scans` counts their pending dependency edges. `cycle_closed` says the
component contains the current product, and `group_members` counts only its
same-kind members. One dependency-rooted Tarjan traversal supplies all six
values. The prospective edge is recorded before borrowing the dependency map;
there is no graph copy, separate early-exit reachability pass, or repeated scan
per candidate. Causal replay compares both these totals and the exact current-graph
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
dependency identities and the enclosing evaluation's cause. Demand-cone
projections use the same per-product rows. Each successful request boundary
carries the final reachable executable and construction-wrapper population, so
a future root cache hit reports population without requiring a new settlement.

Reproduce the long-lived baselines with:

```
cargo test --lib target_fixture_reports_exercise_all_five_request_scenarios -- --nocapture
cargo test --test fz2_cli causal_work_multisets_agree_across_two_processes -- --nocapture
```

The first command runs cold, unchanged, unreachable edit, reached-leaf edit,
and callee replacement for each of the three exact target fixtures. It proves
that all five request reports are separated and internally exact. The second
compares every canonical work dimension from separate processes with zero
exclusions. No command interprets elapsed time as correctness.

The 2026-09-04 combined-stack baseline makes the retained-work problem
explicit. Columns are producer evaluations / settlements / distinct demanded
products / unexplained producer evaluations; the final pair is reachable
executables + construction wrappers:

| fixture | cold | unchanged request | population |
| --- | ---: | ---: | ---: |
| `fz_f98_range_map_converges` | 2924 / 2147 / 2082 / 12 | 2725 / 2065 / 2000 / 12 | 62 + 0 |
| `enum_predicate_search` | 7461 / 5430 / 5046 / 30 | 7154 / 5348 / 4964 / 30 | 168 + 32 |
| `00420_enum_take_drop_split` | 15841 / 12309 / 11806 / 27 | 15476 / 12227 / 11724 / 27 | 239 + 38 |

The unchanged request does zero scheduler-formula evaluations, yet starts a
fresh product session and reproduces 2065, 5141 and 11971 first-generation
products respectively. Those are `cross_request_recomputations`, not retained
hits; the baseline reports zero retained cache hits. This is the work the next
retention ticket removes.

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

`the_demand_ascent_height_does_not_grow_with_the_program`
(`compiler2::product_drive_test`) pins the two demand-cone numbers that are
supposed to be flat — `rounds`, and `derivations` per member — by doubling the
call sites and comparing.
