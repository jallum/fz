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

**Work starts** — `fz.compiler2.pull.session.finished` carries the
`WorkStartTally`: `ignition`, `changed_revision_wake`, `standing_root_frontier`,
`activation_frontier`, `blocked_waiter_expansion`, plus `unsanctioned_work_starts`
and `root_scans`. This is the pull-only guard's evidence — every job on the
agenda must name a sanctioned reason. `unsanctioned_work_starts` and `root_scans`
are zero, and `compiler2::work_start_reason_test` holds them there: a
reintroduced job-pushes-job path lands in `Unclassified` by construction, and a
producer that discovers work by scanning the fact table shows up in `root_scans`.

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
outputs; wakes emitted; completions that ended blocked. Per PRODUCT (canonical
`ProductKey`): settlements, distinct generations, the changed/unchanged split,
cache hits, displacements. Plus the `pull.session.finished` tallies summed over
every session.

An evaluation is caused when a dependency MOVED in `[the formula's previous
conclusion, now)`, where the dependency set is the completion's `reads` UNION
the blocked-set its PREVIOUS completion recorded. `reads` alone is not enough —
`reads` and `waits` are separate maps, so a job re-run because a wait became
satisfiable has the fact only in `waits`, and a reads-only rule reports it as
uncaused (measured: 37, 30 and 19 evaluations on the three fz-kdt.34 target
fixtures, against zero for the shipped rule). `Dependencies::Reads` keeps that
variant available so the acceptance test can measure the difference.

`canonical_multiset()` is the comparand for two runs. Every count is keyed by
canonical identity, so two PROCESSES can be compared even though their arenas
renumber. Measured over six processes per fixture (15 pairs each): every formula
dimension and every session tally agree 15/15 on all three target fixtures. One
dimension does not — `pull.product.cache_hit` on `CallableConstruction`
products, at 7/15, 6/15 and 1/15 — because the two runs construct different
intermediate types. `causal_work_multisets_agree_across_two_processes`
(`tests/fz2_cli.rs`) pins that divergence to exactly that dimension.

## Reading the numbers

Counts and per-unit costs answer different questions, and the interesting
failures show up in only one of them. A ladder of programs built from *n*
identical call sites separates them: complexity grows strictly linearly, so
anything that does not grow linearly is structural.

A product whose settle **count** grows with the program and whose **cost per
settle** stays flat is incremental — that is the shape to expect.
`executable_facts` and `abi_executable` hold flat per-settle costs across a 32x
ladder. A product whose settle count is *constant* while its per-settle cost
grows is a pass wearing a product's clothes: its unit of work is the program,
not the key it is filed under.

`the_demand_ascent_height_does_not_grow_with_the_program`
(`compiler2::product_drive_test`) pins the two demand-cone numbers that are
supposed to be flat — `rounds`, and `derivations` per member — by doubling the
call sites and comparing.
