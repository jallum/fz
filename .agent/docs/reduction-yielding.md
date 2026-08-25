# Reduction-driven Yielding

Scheduler fairness is driven only by a per-process reduction budget. A running
process keeps going until exactly one of these happens:

- its reduction budget reaches zero;
- it blocks on receive or another scheduler-visible wait;
- it halts.

GC pressure does not force a yield. Allocation may mark the heap as needing
collection, and it may grow into a new heap block, but it never zeroes
`reductions_remaining` and never sets a yield reason. The scheduler observes the
heap pressure flag only at a natural boundary: a reduction yield, a block, or a
return to the scheduler.

The unit charged today is the loop back edge. An unbounded pure loop is a
tail-recursive SCC; the compiler marks those edges (`is_back_edge`), so they are
the natural place to spend budget. Each back edge spends exactly one reduction.

## Who owns what

- **`Process`** (`runtime/src/process.rs`) owns the budget cell, cumulative
  reduction counters, and transient per-quantum yield reason bits. Its budget
  accounting methods are `reset_reduction_budget`, `finish_yield_report`, and
  `boundary_maintenance`.
- **`Heap`** (`runtime/src/heap`) owns allocation, block growth, and the
  `should_gc` pressure flag. Crossing `gc_threshold_bytes` sets that flag.
  Exhausting the current block allocates a larger block and parks the old block
  in `abandoned_blocks` for the next Cheney pass.
- **The schedulers** (JIT `src/exec/runtime.rs`, interpreter `src/ir_interp`,
  AOT `runtime/src/aot_shim.rs`) own dispatch and the boundary decision: install
  a fresh budget, run the process, then collect if the heap pressure flag is set
  at the boundary.

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
- `reductions_executed: u64` — cumulative reductions reported at yield
  boundaries.
- `reduction_yields: u64` — cumulative yields caused by reduction-budget
  exhaustion.
- `yield_reasons: u8` — transient reason bits for this quantum's yield report,
  cleared each dispatch/boundary. Runtime code currently raises
  `YIELD_REASON_REDUCTIONS` when a back edge yields.

## The cycle

```text
dispatch          reset_reduction_budget():
                    reductions_remaining = reductions_per_quantum
                    yield_reasons = 0

back edge         reductions_remaining -= 1
                  if reductions_remaining <= 0:
                    compiled: materialize the zero-arg continuation closure
                    interpreter: forward resume_fn + resume_args
                    yield, reporting REDUCTIONS

allocation        bump_top += size
                  if bytes_used >= gc_threshold_bytes:
                    heap.should_gc = true
                  if bump_top would cross block_end:
                    allocate a larger block
                    move old current block to abandoned_blocks

boundary          if heap.should_gc():
                    gc over scheduler-owned roots; quiet_quanta = 0
                  else:
                    quiet_quanta += 1
                  clear should_gc flag; clear yield_reasons
```

The two engines hand control back differently. Compiled code (JIT and AOT)
materializes a zero-arg continuation closure on exhaustion and leaves it in
`runnable` (see
[`scheduler-zero-arg-closures.md`](scheduler-zero-arg-closures.md)). The
interpreter runs synchronously: it forwards the next iteration's `resume_fn` and
`resume_args` to the scheduler and gathers GC roots over those args and the
after-continuations, never building a closure.

## Allocation and block growth

Allocation is pure bump on the fast path. When the current block cannot fit an
object, `Heap::alloc_kind` allocates a fresh block from the next size class that
can hold it, records the old block in `abandoned_blocks`, and continues. This is
why allocation does not need to force a scheduler yield to remain total.

Large objects above the heap fragment threshold use fragment allocations. They
also mark pressure through `note_alloc_pressure`, but they do not move during
Cheney; the collector marks survivors and frees unmarked fragments during the
fragment sweep.

Compiled yield telemetry still samples the slow path that materializes a
continuation closure:
`max_yield_continuation_bytes`,
`min_yield_continuation_margin_before_bytes`, and
`min_yield_continuation_margin_after_bytes`. These measure reduction-yield
continuation allocation, not a reserved heap band.

## Accounting at the boundary

The yield boundary is the source of truth, not allocation. `finish_yield_report`
records the signed remaining budget reported by the yielding back edge, derives
`burned = reductions_per_quantum - remaining_reductions`, and folds that into
`reductions_executed`. A signed, possibly negative `remaining_reductions` records
how far past budget the process ran before reaching a back edge.

`needs_boundary_gc()` is true when `heap.should_gc()` is set. When it fires, the
scheduler runs Cheney over scheduler-owned roots — the runnable continuation
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
    -> compiled: build the zero-arg continuation capturing (n, acc)
       interpreter: forward resume_fn + resume_args (n, acc)
    -> yield reporting REDUCTIONS
  boundary: if heap.should_gc is set, collect; otherwise quiet_quanta += 1
  dispatch resumes the continuation with a fresh 4000 budget
    -> the count finishes in the next quantum
```

An allocation-heavy loop differs only in heap state: consing may set
`heap.should_gc()` or grow into another block, but it does not affect the
reduction budget. The next yield still happens when reductions run out.

## Parity

The model is identical in the interpreter, JIT, and AOT: the same `Process`
budget fields, the same heap pressure flag, and the same boundary-GC decision.
The resume carrier differs — a zero-arg continuation closure in compiled code,
forwarded `resume_fn` + `resume_args` in the interpreter — but the boundary sees
the same budget accounting and roots the live continuation state either way.
Pure fz code yields automatically by reduction budget. Tests pin both sides:
allocation-light loops assert `reduction_yields > 0`, and allocation-heavy loops
with spare budget assert allocation pressure does not produce a yield before
budget exhaustion.
