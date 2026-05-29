# Reduction-driven Yielding

Scheduler fairness and allocation-pressure collection ride on **one** mechanism:
a per-process reduction budget. A running process keeps going until exactly one
of these happens:

- its reduction budget reaches zero;
- it blocks on receive or another scheduler-visible wait;
- it halts.

There is no separate GC-yield control path. Allocation pressure expresses itself
as budget expiration, so allocation-heavy loops reach GC through the same yield
boundary as ordinary budget exhaustion, and an allocation-light CPU loop can no
longer monopolize the worker.

## Process budget state

`Process` carries the budget and its accounting (`runtime/src/process.rs`):

- `reductions_remaining: i32` — spent down by loop back edges during the quantum.
- `reductions_per_quantum: i32` — the budget installed at dispatch.
- `reductions_executed: u64` — cumulative reductions burned across all quanta.
- `reduction_yields: u64` / `allocation_pressure_yields: u64` — cumulative yield
  counts split by cause.
- `yield_reasons: u8` — a transient bitfield for *this* quantum's boundary
  decision, cleared each dispatch. Bits: `YIELD_REASON_REDUCTIONS`,
  `YIELD_REASON_ALLOCATION_PRESSURE`, `YIELD_REASON_EXPLICIT`.

## The cycle

```text
dispatch          reset_reduction_budget():
                    reductions_remaining = reductions_per_quantum
                    yield_reasons = 0

back edge         reductions_remaining -= back_edge_cost
                  if reductions_remaining <= 0:
                    materialize the zero-arg continuation closure
                    yield

allocation        bump_top += size
                  if bump_top >= allocation_watermark:
                    heap.owner.reductions_remaining = 0          # owner set per quantum
                    heap.owner.yield_reasons |= ALLOCATION_PRESSURE

boundary          boundary_maintenance():
                    if needs_boundary_gc():  # should_gc flag or ALLOCATION_PRESSURE bit
                      gc_roots(self); quiet_quanta = 0
                    else:
                      quiet_quanta += 1
                    clear should_gc flag; clear yield_reasons
```

The mechanism is one thing — budget exhaustion — and the *cause* stays
observable through the yield-reason bits and the split cumulative counters.

Compiled code spends the budget by reading and writing `reductions_remaining`
directly through the pinned `Process` base register; see
[`pinned-process-register.md`](pinned-process-register.md). The interpreter
spends the same field through the process it threads explicitly
(`IrInterpRuntime.current_proc`). Both engines materialize the same zero-arg
continuation closure on exhaustion; see
[`scheduler-zero-arg-closures.md`](scheduler-zero-arg-closures.md).

## Allocation watermark and the continuation reserve

Allocation pressure must force a yield while the process still has enough heap
headroom to allocate the continuation closure that hands control back to the
scheduler. The heap reserves a fixed band for that:

```text
allocation_watermark = heap_end - YIELD_CONTINUATION_RESERVE_BYTES   # 256
```

(`allocation_watermark_for` in `runtime/src/heap/ref_io.rs`;
`YIELD_CONTINUATION_RESERVE_BYTES` in `runtime/src/heap/mod.rs`.) Ordinary
allocation crossing the watermark expires the budget; yield-continuation
materialization is allowed to spend from the reserved band below it.

The reserve is bounded pessimism, not exact accounting — an explicit soft
watermark. Compiled yield telemetry samples the full slow-path allocation window
(`max_yield_continuation_bytes`, `min_yield_continuation_margin_*`) so the bound
can be tightened or raised from evidence rather than guesswork.

## Accounting at the boundary

The yield boundary is the source of truth, not any implementation-specific
budget cell. `finish_yield_report(remaining_reductions, reason)` records the
report: the scheduler knows the budget it issued, so it derives
`burned = reductions_per_quantum - remaining_reductions` and folds that into
`reductions_executed`. A signed (possibly negative) `remaining_reductions`
records how far past budget the process ran before reaching a back edge.

Cause is counted off the *accumulated* `yield_reasons`, not just the report's
bits: allocation pressure sets its bit directly on the `Process` mid-quantum via
the heap's per-quantum `owner` back-pointer, so the back edge that finally yields
reports only
`REDUCTIONS` while `ALLOCATION_PRESSURE` is already standing. Allocation pressure
therefore dominates the cause classification when both bits are present.

`quiet_quanta` is scheduler-boundary state: it advances only in
`boundary_maintenance`, never per back edge, so it counts scheduler quanta
completed without boundary GC consistently across all three engines.

## Parity

The model is identical in the interpreter, JIT, and AOT: the same `Process`
fields, the same watermark, the same `boundary_maintenance`, and the same
zero-arg continuation. Pure fz code yields automatically, and that claim is
backed by reduction-budget tests on every engine.

## Lineage

The reductions idea is borrowed from BEAM, where a process context-switches once
it spends its timeslice budget. The unit fz charges is the SCC back edge: an
unbounded pure loop is a tail-recursive SCC, and the compiler already identifies
those edges, so they are the natural place to spend budget.
