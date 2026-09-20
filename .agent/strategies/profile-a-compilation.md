# Profile a Compilation

Use this strategy when a front door is slow on a program that should be cheap,
or when a fixture lane trips the matrix's wall-clock guard and nobody knows
what the compiler spent the time on.

Jobs have spans. Spans have timing. That timing can be summed. The distiller
turns a `--log-telemetry` stream into where the time went, and the answer is a
mechanism, not a machine.

Two tools read that stream, over one shared reader (`tools/telemetry.exs`):

- `tools/distill-telemetry.exs` answers *where did this one compilation go*.
- `tools/work-census.exs` answers the question before it: *which programs are
  we doing too much work for, relative to their size*. Reach for the census
  when you do not yet know which program to profile.

Counts lead in both. A job that should not have run is a correctness answer;
times follow, because once the counts are right the remaining juice is how
long each job takes.

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

2. Or, when you do not know which program is the problem, census a corpus
first.

```
elixir tools/work-census.exs run fixtures2/behavior --top 25
```

`j/fn` -- jobs per function -- is the proportionality number: small when work
tracks the input, large when something is reprocessing. `rerun%` says how much
of the work was a repeat, `hot` how many times the single most re-run job ran,
and `rev` the most return-type revisions one activation took. The size column
counts the program without its comments, because a fixture carries its paper
answer in a leading block and that prose is not input the compiler works on.

A program the door cannot compile is reported, not skipped: a crash is work
too, and an unbounded one is the loudest signal there is.

3. Distill it.

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
- **jobs by kind and subject**: which function that work was for, named.
- **most re-run jobs**: a job that ran more than once for one subject was
  woken by a changed fact; the count is the number of climbs the fixpoint took
  there.
- **return-type revisions per activation**: how many rounds each activation's
  return type took, and whether `ACTIVATION_INPUT_ROW_BUDGET` ended the climb
  by collapsing a correlated-input row set column-wise. An activation at that
  ceiling widened its answer instead of finding it. The budget is not the
  usual answer: on the fixtures measured here it fires zero times, so a large
  revision count almost always means a fact genuinely climbing, not a cap.
- **wake causes**: for each of those, which fact changed and which completion
  changed it. This is where a ladder shows itself: one fact revised many
  times, each revision waking the same callers.

4. Corroborate the magnitude on the plain binary.

```
fz2 run prog.fz & sleep 0.3; sample $! 3 -file sample.txt
```

The inclusive shares in the sample must agree with the distiller's shape; the
seconds come from here, not from the stream. Counts are the authoritative
signal: revisions of a fact, runs of a job, activations per function.

5. Name the mechanism and find its ticket.

Search the board before filing. A recursive type that climbs a rung per
fixpoint round, a job re-run per revision of a fact it reads, an activation
per rung of an ascent: each has a name on the board already, and the distilled
numbers are the aggravating case that ticket wants.

## Worked example

`fixtures2/behavior/cross_kind_operators.fz` on `run`: 117 functions, 1555 job
spans, 714.9 ms end to end. Native codegen is 23.8 ms and the program itself
runs in 0.1 ms, so effectively all of it is analysis.

By kind, `AnalyzeActivation` takes 459.3 ms of the 545.3 ms of job time. The
subject breakdown narrows that to one line: **`AnalyzeActivation main/0` runs
119 times for 427.3 ms** -- one activation of one function, 78% of all job time
in the compilation.

The wake causes say why, and they say it by *not* repeating. Nearly all 119
wakes are distinct facts firing exactly once: `ReturnType` of `ge?/2` on one
input row, then `gt?/2` on another, then `le?/2`, then an `InputDemand`, and so
on through every callee `main/0` mentions. Only `Kernel.dbg/1` fires twice.
Return-type revisions are 1 for every activation but that one, which is 2.

So almost nothing here is climbing, and reaching for a widening or ladder
explanation would be wrong. `main/0` reads a fact per callee and re-runs in
full each time one of them lands. A waiter is re-run only once all of its waits
are satisfied, so naming those callee returns as waits costs one analysis;
reading them costs one analysis per arrival. That is the difference between 119
runs and a handful, and the count of distinct single-fire wake causes is what
proves which one is happening.

Do read the budget separately rather than inferring it from the revision
counts: `budget_collapsed` fires 8 times in this same trace while no activation
revises more than twice. A collapse and a climb are different events, and one
does not imply the other.

## A hazard worth knowing

Check that the binary you are measuring was built from the tree you are
reading. A stale `target/release/fz2` produces a trace that distills perfectly
and describes a compiler that no longer exists. This is not hypothetical: the
first draft of the section above was written from one, and reported a stack
overflow under `--log-telemetry`, 1708 jobs, and a budget that never fired.
Rebuilding changed the binary hash and all three claims: no overflow, 1555
jobs, budget fires 8 times.

`cargo build --release --bin fz2` answering "Finished" in well under a second
means it believed there was nothing to do, which is a claim about mtimes, not
about content. Restoring a file from a `.bak` copy preserves its old mtime and
defeats the check outright. When a measurement surprises you, confirm the hash
moved before you explain the surprise.
