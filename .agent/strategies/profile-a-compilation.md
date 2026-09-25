# Profile a Compilation

Use this strategy when a front door is slow on a program that should be cheap,
or when a fixture lane trips the matrix's wall-clock guard and nobody knows
what the compiler spent the time on.

Jobs have spans. Spans have timing. That timing can be summed. The distiller
turns a `--log-telemetry` stream into where the time went, and the answer is a
mechanism, not a machine.

## The Loop

1. Capture the stream on the door that is slow.

```
fz2 --log-telemetry trace.jsonl run prog.fz
```

The stream carries a span per compiler job with the job's identity on the
start record and elapsed time on the stop, a `canon.function` event that names
each function id, and a `work_graph.applied` event per completion listing the
facts it changed and the jobs it woke. Rendering canon strings into that stream
costs many times the compile on deeply nested programs, so treat the
magnitudes as inflated and the shape as true.

2. Distill it.

```
elixir tools/distill-telemetry.exs trace.jsonl --top 20
```

Read the sections in order, each narrower than the last:

- **timeline**: how much sits before the first job, inside the jobs, in native
  codegen, and after the last span, which is the program itself running.
- **span names**: inclusive and self time per span name; a child's inclusive
  time is taken out of its parent's self time, so self says what a span did
  on its own.
- **jobs by kind**: which kind of work dominates. One kind at ninety percent is
  the usual answer.
- **job runs vs subjects**: per kind, `runs` against distinct `subjects`,
  `excess` (`runs - subjects`), and the worst single subject's run count.
  `excess` at zero means that kind ran each of its subjects exactly once;
  proportional compilation is every row's excess staying at zero. Sorted by
  excess, so the kind doing the most repeated work leads.
- **jobs by kind and subject**: which function that work was for, named.
- **most re-run jobs**: a job that ran more than once for one subject was
  woken by a changed fact; the count is the number of climbs the fixpoint took
  there.
- **return-type revisions per activation**: how many rounds each activation's
  return type took and whether the widening budget ended the climb; an
  activation at the ceiling widened its answer instead of finding it.
- **cause of every re-run**: every re-run in the stream (not just the hottest
  subjects), grouped by (job kind, changed fact + use, completing job kind,
  disposition) so the same shape of cause across many subjects is one row
  instead of one per subject. A wake rides on whichever of three events the
  scheduler emitted its `AppliedStep` on — `work_graph.applied` (an ordinary
  job completing), `work_graph.dependencies_moved` (a product settling), or
  `work_graph.quiesced` (a drain step) — and the census reads all three;
  reading only `applied` undercounts every re-run a product settlement or a
  drain step woke. The "completing job" column is the completion's job kind
  for `applied` rows and the bare event name (`dependencies_moved` /
  `quiesced`) for the other two. Only `enqueued` wakes count toward a re-run —
  an `enqueued` wake is what started it; a `coalesced` wake landed on a
  re-run some other wake had already enqueued, so those are reported in their
  own table underneath rather than double-counted. The census then
  cross-checks itself against the trace's session-summed `WorkStartTally`:
  matched `enqueued` wakes must equal `work_starts_changed_revision_wake`,
  and `ignition + activation_frontier + blocked_waiter_expansion` must equal
  the distinct subject count. Either mismatch prints both numbers and halts
  the distiller nonzero rather than rendering an unexplained row — a re-run
  the census cannot name is a defect in the census, not a fact to shrug at.
  This is where a ladder shows itself: one fact revised many times, each
  revision waking the same callers.

3. Corroborate the magnitude on the plain binary.

```
fz2 run prog.fz & sleep 0.3; sample $! 3 -file sample.txt
```

The inclusive shares in the sample must agree with the distiller's shape; the
seconds come from here, not from the stream. Counts are the authoritative
signal: revisions of a fact, runs of a job, activations per function.

4. Name the mechanism and find its ticket.

Search the board before filing. A recursive type that climbs a rung per
fixpoint round, a job re-run per revision of a fact it reads, an activation
per rung of an ascent: each has a name on the board already, and the distilled
numbers are the aggravating case that ticket wants.

## Worked example

`fixtures2/behavior/json_roundtrip.fz` on `run`: 4527 jobs, 54% of them
re-runs; three activations analyzed 32, 55 and 77 times, every re-run woken by
`Json.value/1`'s `ReturnType` changing, which it does 18 times and never
converges: it tops out at `any` when the widening budget runs out. The sample
of the plain binary puts about two thirds of the lane in the fixpoint drive and
a third in Cranelift, with the program's own execution under a fifth of a
percent; the stream's span times said 97% in one job kind, and that number was
the stream rendering canon strings, which is why step 3 exists. The mechanism
is a recursive value type expanded rung by rung until the cap, and the ticket
is the one about representing recursive denotations without a ladder.
