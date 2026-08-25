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

**Job spans** — `fz.compiler2.job`, `span_start`/`span_stop`. The stop carries
`causality.formula_id`, every demand or exact fact movement coalesced into the
evaluation, exact changed facts, and downstream wakes. Group by `formula_id`,
not job kind; pair spans by `span_id` only when timing is useful. This covers
the drive loop only; a product settled during a pull is not a job.

**Product work** — `fz.compiler2.pull.product.evaluated` carries a stable
`product_id`, produced/waiting outcome, and exact product-generation/fact-state
dependencies. `settled` adds previous/current generation and whether the value
changed or was reproduced. `cache_hit`, `displaced`, and `reentered` separate
reuse from churn. `group_settled` names every atomically published member.
Session totals include recursive-group candidates and dependency-reach visits.
No event-time gap needs to stand in for identity or cause.

**Work starts** — `fz.compiler2.pull.session.finished` carries the
`WorkStartTally`: `ignition`, `changed_revision_wake`, `standing_root_frontier`,
`activation_frontier`, `blocked_waiter_expansion`, plus `unsanctioned_work_starts`
and `root_scans`. This is the pull-only guard's evidence — every job on the
agenda must name a sanctioned reason. `unsanctioned_work_starts` and `root_scans`
are zero, and `compiler2::work_start_reason_test` holds them there: a
reintroduced job-pushes-job path lands in `Unclassified` by construction, and a
producer that discovers work by scanning the fact table shows up in `root_scans`.
The corresponding job completion names the exact demanded fact, so the reason
count can be audited rather than trusted as an aggregate.

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

Prefer asserting a causal work multiset over asserting a duration: formula or
product identity, moved dependency, changed output, and downstream wake are
properties of the program and dependency graph. The three Enum performance
fixtures parse only public JSONL and require this stable identity vocabulary
without raw `Ty` ids.

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
