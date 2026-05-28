# Reduction-driven Yielding Plan

## Goal

Move scheduler fairness and allocation-pressure yielding onto one reductions
mechanism.

A process should run until one of these happens:

- its reduction budget expires;
- it blocks on receive or another scheduler-visible wait;
- it halts.

Allocation must not have a separate GC-yield control path. If allocation crosses
the heap pressure watermark, allocation expires the current process's reduction
budget and marks the process as needing GC. The next normal yield boundary
materializes the scheduler continuation. The scheduler then performs boundary
maintenance, including GC when needed, resets the process budget, and requeues
the process if it is still runnable.

## Signal

The observable proof of success is:

- allocation-light CPU loops cannot monopolize the worker;
- allocation-heavy loops reach GC through the same yield path as ordinary budget
  exhaustion;
- continuation materialization always has reserved heap space available;
- allocation fast paths keep the current shape: bump, compare against a
  precomputed watermark, rare slow signal;
- telemetry can distinguish natural quantum exhaustion from allocation-pressure
  exhaustion.

## Historical Starting State

Before this plan was implemented, compiled back edges read a GC-specific yield
flag. Heap allocation set that flag when a process crossed its GC watermark, and
the scheduler treated the resulting mid-flight yield as a GC event.

That couples fairness to allocation pressure:

```text
allocation crosses watermark
  set GC-specific yield flag
back edge sees yield flag
  materialize continuation closure
  yield
scheduler sees runnable continuation
  GC
  requeue
```

This keeps allocation-heavy loops collectible, but an allocation-light loop can
run without yielding. It also keeps a GC-specific yield story in the hot loop.

## Target Model

Use reductions as the scheduler budget:

```text
scheduler dispatch:
  process.reductions_remaining = process.reductions_per_quantum

compiled/interpreted back edge:
  process.reductions_remaining -= back_edge_cost
  if process.reductions_remaining <= 0:
    materialize continuation closure
    yield
  else:
    continue

allocation:
  bump
  if bump_top >= allocation_watermark:
    process.reductions_remaining = 0
    process.yield_reasons |= NEEDS_GC

scheduler boundary:
  if process.yield_reasons has NEEDS_GC or heap is past pressure watermark:
    GC process roots
  clear boundary yield reasons
  reset reductions
  requeue runnable process
```

The mechanism is one thing: budget exhaustion. The cause remains observable:

- natural reductions exhaustion;
- allocation pressure;
- explicit runtime yield;
- future timer or external preemption request.

## Heap Reserve Invariant

Allocation pressure should force a yield while the process still has enough
headroom to allocate the yield continuation needed to hand control back to the
scheduler.

The invariant is:

```text
allocation_watermark <= heap_end - yield_continuation_reserve
```

The implementation uses bounded pessimism, not exact accounting. The reserve is
an explicit soft watermark, and compiled yield telemetry measures the full slow
path allocation window so the bound can be tightened or raised from evidence.

Recommended initial heap layout:

```text
heap_start
  ordinary allocation region

allocation_watermark = heap_end - yield_continuation_reserve
  ordinary allocation crossing this point expires reductions and marks NEEDS_GC

heap_end - emergency_reserve
  ordinary allocation must not casually consume this band

heap_end
  hard stop
```

The reserve policy should start simple:

```text
yield_continuation_reserve = GLOBAL_MIN_YIELD_RESERVE
```

Only specialize by function, back edge, or SCC after telemetry proves the global
reserve costs meaningful heap utilization.

## Allocation Fast Path

Do not pass scheduler budget, SCC ids, continuation sizes, or reserve values
through ordinary allocation calls in the first implementation.

The allocator should preserve the existing hot-path shape:

```text
ptr = bump_top
bump_top += size
if bump_top >= allocation_watermark:
  expire current process budget for allocation pressure
return ptr
```

This replaces the meaning of the existing watermark signal. It does not add a
second allocation check.

## Continuation Allocation

Yield-continuation materialization is allowed to spend from the reserved band.
Ordinary allocation is not. Compiled code samples heap margin at slow-path entry
and records the delta when `fz_yield_mid_flight_report(...)` hands the
continuation to the scheduler.

If the continuation cannot be materialized within the reserve, that is a
runtime/compiler invariant failure. It should not fall back to "try GC now",
because the process is already in the act of producing the root that GC needs.

The first implementation can use a narrow allocation mode internally for
continuation materialization if that keeps the ordinary allocation path clean:

```rust
enum AllocMode {
    Ordinary,
    YieldContinuation,
}
```

The mode must not leak into ordinary allocation call sites unless measurements
justify it.

## Work DAG

### reductions.1: Add process budget state and telemetry

Goal: make reductions visible without changing scheduling behavior.

Tasks:

- add process fields for `reductions_remaining`, `reductions_per_quantum`,
  `reductions_executed`, `reduction_yields`, `allocation_pressure_yields`, and
  compact yield reasons;
- expose the counters through process stats or focused runtime telemetry;
- add tests that prove the counters reset at dispatch and accrue at back-edge
  observation points.

### reductions.2: Teach interpreter back edges to spend budget

Goal: prove the semantic model in the easiest execution path.

Tasks:

- decrement budget on interpreted `TailCall { is_back_edge: true }`;
- yield or return a scheduler step when budget is exhausted;
- preserve the existing interpreter GC root handling at the scheduler boundary;
- add a two-process allocation-light fairness test.

### reductions.3: Replace compiled back-edge GC flag checks with budget checks

Goal: make compiled loops yield by reductions, not by a GC-specific flag.

Tasks:

- expose a cheap scheduler-budget cell to compiled code;
- emit budget decrement/check at back edges;
- materialize the same zero-arg continuation closure on exhausted budget;
- carry yield reasons separately from the branch condition;
- keep the hot branch compact and measurable.

### reductions.4: Turn allocation pressure into budget expiration

Goal: delete the special allocation-to-GC-yield story.

Tasks:

- rename/redefine the heap watermark as `allocation_watermark`;
- make crossing the watermark expire the current process budget and set
  `NEEDS_GC`;
- keep the allocation fast path to bump plus one precomputed watermark compare;
- ensure stale pressure state cannot leak between scheduled processes.

### reductions.5: Make continuation reserve explicit

Goal: replace the hand-waved 75% reserve with a named invariant.

Tasks:

- introduce a conservative global yield-continuation reserve;
- compute `allocation_watermark = heap_end - yield_continuation_reserve`;
- ensure continuation materialization may allocate inside the reserved band;
- add tests for pressure near the watermark and successful mid-flight
  continuation materialization;
- add telemetry for maximum continuation allocation and remaining bytes before
  and after materialization.

### reductions.6: Move GC to scheduler-boundary maintenance

Goal: make GC a boundary policy rather than a yield mechanism.

Tasks:

- run process-root GC at scheduler boundaries when `NEEDS_GC` or heap pressure
  is present;
- clear yield reasons after boundary maintenance;
- keep receive parking, runnable closure roots, mailboxes, and timers rooted
  through the existing scheduler root model;
- prove allocation-heavy loops still collect and complete.

### reductions.7: Remove obsolete GC-yield affordances and update docs

Goal: collapse the old model once reductions own yielding.

Tasks:

- remove the GC-specific yield flag once compiled and AOT paths no longer need
  it;
- remove docs that describe a GC-specific mid-flight yield trigger;
- update `guides/processes.html`, `guides/memory.html`,
  `.agent/docs/ir-interp-runtime.md`, and
  `.agent/docs/scheduler-zero-arg-closures.md`;
- preserve user-facing claims that pure fz yields automatically, now backed by
  reduction-budget tests.

## What Goes Away

The target design should remove these concepts:

- GC-specific back-edge branch condition;
- a GC-specific yield byte;
- the 75% watermark as an implicit continuation reserve;
- docs that describe allocation as directly triggering a GC-specific yield.

The zero-arg scheduler continuation model stays. Reductions decide when that
continuation must be produced; GC decides what maintenance happens after it is
produced.

## Measurements

Add boundary-level metrics, not per-allocation metrics:

- reductions spent per quantum;
- natural reduction yields;
- allocation-pressure yields;
- explicit/runtime yields;
- max continuation materialization bytes;
- heap bytes remaining before and after yield-continuation materialization;
- GC count by boundary cause.

These metrics are test oracles first. They can later guide whether the global
reserve should become SCC-local or site-local.

## Research Notes

BEAM uses reductions as a process scheduling budget. Erlang documentation
describes reductions as roughly function and BIF calls, with a scheduler context
switch after the process reaches the maximum reductions for its timeslice. NIFs
must cooperate by consuming timeslice explicitly.

The useful lesson for fz is not the exact unit. The invariant to copy is:

```text
a runnable process cannot execute unbounded pure work without spending a bounded
scheduler budget
```

For fz, SCC back edges are the correct first charging point because unbounded
pure loops are tail-recursive SCCs and the compiler already identifies those
edges.
