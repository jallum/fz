# Reduction-driven Yielding

Scheduler fairness and allocation-pressure collection ride on **one**
mechanism: a per-process reduction budget. A running process keeps going until
exactly one of these happens:

- its reduction budget reaches zero;
- it blocks on receive or another scheduler-visible wait;
- it halts.

There is no separate GC-yield control path. Allocation pressure expresses
itself as budget expiration, so allocation-heavy loops reach GC through the same
yield boundary as ordinary budget exhaustion, and an allocation-light CPU loop
cannot monopolize the worker.

The unit charged is the loop back edge. An unbounded pure loop is a
tail-recursive SCC; the compiler marks those edges (`is_back_edge`), so they are
the natural place to spend budget. Each back edge spends exactly one reduction.

## Who owns what

- **`Process`** (`runtime/src/process.rs`) owns the budget cell, the cumulative
  counters, and the transient per-quantum reason bits. Its methods are the only
  budget accounting: `reset_reduction_budget`, `expire_budget`,
  `finish_yield_report`, `boundary_maintenance`, `needs_boundary_gc`.
- **`Heap`** (`runtime/src/heap`) owns the allocation watermark and a per-quantum
  `owner` back-pointer to its `Process`. Crossing the watermark in `alloc()`
  expires the owner's budget through that pointer.
- **The schedulers** (JIT `src/exec/runtime.rs`, interpreter `src/ir_interp`,
  AOT `runtime/src/aot_shim.rs`) own dispatch and the quantum boundary: each one
  installs the budget and the `owner` pointer at dispatch, then runs the boundary
  decision after the quantum returns.

## Process budget state

`Process` carries the budget and its accounting:

- `reductions_remaining: i32` — spent down by back edges during the quantum.
  Compiled code reads and writes this field directly at
  `PROCESS_REDUCTIONS_REMAINING_OFFSET` through the pinned `Process` base
  register (`runtime/src/process_abi.rs`; see
  [`pinned-process-register.md`](pinned-process-register.md)); the interpreter
  spends the same field through the process it threads explicitly
  (`IrInterpRuntime.current_proc`).
- `reductions_per_quantum: i32` — the budget installed at dispatch
  (`DEFAULT_REDUCTIONS_PER_QUANTUM` is 4000).
- `reductions_executed: u64` — cumulative reductions burned across all quanta.
- `reduction_yields: u64` / `allocation_pressure_yields: u64` — cumulative yield
  counts split by cause. These two counters are the authoritative yield-cause
  telemetry.
- `yield_reasons: u8` — a transient bitfield for *this* quantum's boundary
  decision, cleared each dispatch. The constants are `YIELD_REASON_REDUCTIONS`,
  `YIELD_REASON_ALLOCATION_PRESSURE`, and `YIELD_REASON_EXPLICIT`; the two raised
  by the runtime are `REDUCTIONS` (the yielding back edge) and
  `ALLOCATION_PRESSURE` (`expire_budget`).

## The cycle

```text
dispatch          reset_reduction_budget():
                    reductions_remaining = reductions_per_quantum
                    yield_reasons = 0
                  heap.set_owner(self)

back edge         reductions_remaining -= 1
                  if reductions_remaining <= 0:
                    materialize the zero-arg continuation closure
                    yield, reporting REDUCTIONS

allocation        bump_top += size
                  if bump_top >= allocation_watermark and owner is set:
                    owner.expire_budget(ALLOCATION_PRESSURE)
                      # banks reductions burned so far (once per quantum),
                      # zeroes the budget, stands the bit

boundary          if needs_boundary_gc():   # should_gc flag OR ALLOCATION_PRESSURE bit
                    gc over scheduler-owned roots; quiet_quanta = 0
                  else:
                    quiet_quanta += 1
                  clear should_gc flag; clear yield_reasons
```

The mechanism is one thing — budget exhaustion — and the *cause* stays
observable through the yield-reason bits and the split cumulative counters. Both
engines materialize the same zero-arg continuation closure on exhaustion; see
[`scheduler-zero-arg-closures.md`](scheduler-zero-arg-closures.md).

## Allocation watermark and the continuation reserve

Allocation pressure must force a yield while the process still has enough heap
headroom to allocate the continuation closure that hands control back to the
scheduler. The heap reserves a fixed band for that:

```text
allocation_watermark = block_start + (block_size - YIELD_CONTINUATION_RESERVE_BYTES)
```

`YIELD_CONTINUATION_RESERVE_BYTES` is 256 (`runtime/src/heap/mod.rs`);
`allocation_watermark_for` recomputes the watermark whenever the block grows or
GC installs a new to-space (`runtime/src/heap/ref_io.rs`). Ordinary allocation
crossing the watermark expires the budget; yield-continuation materialization is
allowed to spend from the reserved band below it.

The reserve is bounded pessimism, not exact accounting — an explicit soft
watermark. Compiled yield telemetry samples the full slow-path allocation
window: `max_yield_continuation_bytes` is the largest continuation allocation
observed, and `min_yield_continuation_margin_before_bytes` /
`min_yield_continuation_margin_after_bytes` are the smallest in-block margins
seen immediately before and after materialization. The compiled slow path frames
the sample with `fz_yield_slow_path_begin` (margin before) and
`fz_yield_mid_flight_report` (bytes plus margin after).

## Accounting at the boundary

The yield boundary is the source of truth, not the hot-path budget cell.
`finish_yield_report(remaining_reductions, reason)` records the report: the
scheduler knows the budget it issued, so it derives
`burned = reductions_per_quantum - remaining_reductions` and folds that into
`reductions_executed`. A signed (possibly negative) `remaining_reductions`
records how far past budget the process ran before reaching a back edge — a back
edge that observes a zeroed budget yields reporting a slightly-negative
remaining (its own cost).

Allocation pressure banks earlier. `expire_budget` fires mid-quantum through the
heap's per-quantum `owner` back-pointer: on the first pressure cross of the
quantum it banks the reductions burned up to that point, then it zeroes the
budget and stands the `ALLOCATION_PRESSURE` bit. The first-pressure guard makes
the bank happen exactly once even if allocation crosses the watermark again. The
back edge that then observes the zeroed budget reports only `REDUCTIONS`, so
`finish_yield_report` sees the already-standing `ALLOCATION_PRESSURE` bit, skips
re-deriving burned from the zeroed cell (which would credit a phantom full
quantum), and banks only the work done since expiry. Cause is counted off the
*accumulated* `yield_reasons`, so allocation pressure dominates the
classification when both bits are present.

`needs_boundary_gc()` is true when `heap.should_gc()` is set (occupancy crossed
`gc_threshold_bytes`) or the `ALLOCATION_PRESSURE` bit stands. When it fires, the
scheduler runs Cheney over the scheduler-owned roots — the runnable continuation
closure plus the mailbox in compiled code; the resume args plus pending
after-continuations in the interpreter — and resets `quiet_quanta`; otherwise it
advances `quiet_quanta`. `quiet_quanta` moves at scheduler-quantum boundaries,
never per back edge, so it counts quanta completed without a boundary GC.

`boundary_maintenance` packages this decision (GC-or-advance, then clear the
`should_gc` flag and the reason bits) for the interpreter and the JIT mid-flight
yield path. The AOT shim runs the same steps inline rather than calling it.

## A tiny walkthrough

```text
fn count(0, acc), do: acc
fn count(n, acc), do: count(n - 1, acc + 1)

count(5000, 0) with reductions_per_quantum = 4000:

  each recursion is a back edge: reductions_remaining -= 1
  after 4000 back edges reductions_remaining hits 0
    -> build the zero-arg continuation capturing (n, acc)
    -> yield reporting REDUCTIONS
  boundary: no allocation pressure, should_gc unset
    -> quiet_quanta += 1, reason bits cleared
  dispatch resumes the continuation with a fresh 4000 budget
    -> the count finishes in the next quantum
```

An allocation-heavy loop differs only in where the budget dies: a cons that
trips the watermark calls `expire_budget(ALLOCATION_PRESSURE)`, the next back
edge sees the zeroed budget and yields, and the boundary GCs because the
`ALLOCATION_PRESSURE` bit stands — `allocation_pressure_yields` increments, not
`reduction_yields`.

## Parity

The model is identical in the interpreter, JIT, and AOT: the same `Process`
fields, the same watermark, the same `needs_boundary_gc` decision, and the same
zero-arg continuation. Pure fz code yields automatically. Reduction-budget tests
on each engine pin this: the interpreter and JIT
allocation-light-loop tests assert `reduction_yields > 0` with
`allocation_pressure_yields == 0`, the allocation-pressure tests assert the
reverse and that a pressure yield banks only the reductions genuinely burned
(positive, below a full quantum), and the `quiet_quanta` tests assert it moves
once per scheduler yield, not once per back edge.
