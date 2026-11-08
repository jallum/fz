# Reduction-driven Yielding

Scheduler fairness is driven only by a per-process reduction budget. A running
process keeps going until exactly one of these happens:

- its reduction budget reaches zero;
- it blocks on receive or another scheduler-visible wait;
- it halts.

A due collection does not force a yield. Allocation may make the heap due for
collection, and it may grow into a new heap block, but it never zeroes
`reductions_remaining` and never sets a yield reason. The scheduler asks
`Heap::should_gc` only at a natural boundary: a reduction yield, a block, or a
return to the scheduler.

The unit charged today is the loop back edge. An unbounded pure loop is a
tail-recursive SCC; the compiler marks those edges (`is_back_edge`), so they are
the natural place to spend budget. Each back edge spends exactly one reduction.
A back edge is a tail call between native functions of one SCC
(`annotate_back_edges` in `src/compiler2/jobs/native.rs`). Control that stays
inside a function moves by `Goto` and spends nothing; an entry is a block only
when one direct transfer reaches it, so blocks never form a loop of their own
and every loop still crosses a tail call.

## Who owns what

- **`Process`** (`runtime/src/process.rs`) owns the budget cell, cumulative
  reduction counters, and transient per-quantum yield reason bits. Its budget
  accounting methods are `reset_reduction_budget`, `finish_yield_report`, and
  `boundary_maintenance`. `Process::collect` is the one place a process's roots
  are assembled (see "Accounting at the boundary").
- **`Heap`** (`runtime/src/heap`) owns allocation, block growth, and
  `should_gc`, a pure function of the heap's state: the tip's fill plus the fill
  of every parked block (`bytes_used`) against half the
  tip's capacity. Exhausting the current block allocates a larger block and
  parks the old block in `blocks` for the next Cheney pass. Blocks grafted from
  another heap's gift segment (`Heap::graft`) join `blocks`, are from-space for
  the next pass, and count by fill like any other parked block.
- **The schedulers** (JIT `src/exec/runtime.rs` with `CompiledModule::run_quantum`
  in `src/ir_codegen/compiled.rs`, AOT `runtime/src/aot_shim.rs`, interpreter
  `src/ir_interp`) own dispatch and the boundary decision: install a fresh
  budget, run the process, then call `Process::boundary_maintenance`, which
  collects if `Heap::should_gc` holds. The interpreter does not collect.

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
                  if bump_top would cross block_end:
                    allocate a larger block
                    move old current block to blocks

boundary          if heap.should_gc():   (bytes_used >= block_size / 2)
                    Process::collect
                  clear yield_reasons
```

The two engines hand control back differently. Compiled code (JIT and AOT)
materializes a zero-arg continuation closure on exhaustion and leaves it in
`runnable` (see
[`scheduler-zero-arg-closures.md`](scheduler-zero-arg-closures.md)). The
interpreter runs synchronously: it forwards the next iteration's `resume_fn` and
`resume_args` to the scheduler, never building a closure.

## Allocation and block growth

Allocation is pure bump on the fast path. When the current block cannot fit an
object, `Heap::alloc_kind` allocates a fresh block one capacity step up, or
exactly large enough for the object when that is more, records the old block in
`blocks`, and continues. This is why allocation does not need to force a
scheduler yield to remain total.

`SIZE_TABLE` lists the capacities the block pool recycles, from 1 KiB to about
7 MiB (32 entries). A block above the table is allocated at the object's size rounded up to
16 bytes and is returned to the system allocator, not the pool, when it is
released; `pool_outstanding_blocks` counts pooled blocks only. Such an object is
part of `bytes_used` and is copied by Cheney like any other, so to-space
grows past the table to hold it.

## The gift window

A gift is measured, then copied. `measure_deep_copy` returns the bytes the
copy will allocate: it walks the same kinds under the same ownership test and
the same sharing as `deep_copy_any_value_ref`, so an object reached twice is
counted once, and each object is the size `strict_object_size` states for its
source. `Heap::begin_gift(measured_bytes)` sets the current tip aside and
installs one fresh block of `pick_block_capacity(measured_bytes)`: a table
entry, or an exact block above the table. The copy allocates through
`alloc_kind` into that block and cannot overflow it. `Heap::end_gift` asserts
the block's fill is exactly the measured bytes, turns the block and the MSO
stubs produced since the window opened
into a `GiftSegment` of exactly one block, restores the saved tip, and puts
`live_count` back. Allocation statistics stay with the heap that did the
copying. `Heap::graft` on another heap adopts the segment; dropping an
un-grafted segment releases its block and its stubs' off-heap references. A
collection asserts that no window is open. Cross-process send is the window's user: `sched::gift_copy` measures a
message, or a match's bound values, and copies it inside one, and the segment travels to the
receiver on its `in_queue` (see [scheduler](scheduler-zero-arg-closures.md)).

Grafted blocks are parked blocks like any other, so a gift's fill is part of
`bytes_used`. A collection sizes to-space from `bytes_used` first: the
capacity holding every byte in use is the floor, and the grow, keep and
shrink bands choose between that floor and a larger capacity. Grow applies when
`bytes_used` fills 75% or more of the tip; shrink when the last survivors
fill 25% or less of it; keep otherwise. To-space capacity is therefore at
least the bytes a pass can copy, whatever raised `should_gc`.

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

`needs_boundary_gc()` is true when `heap.should_gc()` holds. When it fires,
`Process::collect` runs `Heap::collect` over one root slice that it builds from
the process: the runnable continuation closure; the park record's clause
bodies, after body and pinned values; the mailbox; and any transient values the
caller passes. Each slot holds its forwarded value afterwards and is written
back to where it came from. The decision is made at scheduler-quantum
boundaries, never per back edge. Gifts waiting in the delivery in-queue are not
roots: their blocks join the heap only when grafted, and every reference in a
gift points into its own segment.

`Process::boundary_maintenance` packages this decision (collect if needed,
then clear the reason bits) and returns the `Collection` it performed, which
the JIT reports as `fz.runtime.gc` (see [runtime telemetry](runtime-telemetry.md)).
The JIT calls it after every quantum, whatever state the process is in. The AOT shim calls it after a quantum that leaves the
process runnable or parked on a receive. The interpreter keeps its resume args
and parked receives in its own structures and never collects.

## A tiny walkthrough

```text
def count(0, acc), do: acc
def count(n, acc), do: count(n - 1, acc + 1)

count(5000, 0) with reductions_per_quantum = 4000:

  each recursion is a back edge: reductions_remaining -= 1
  after 4000 back edges reductions_remaining hits 0
    -> compiled: build the zero-arg continuation capturing (n, acc)
       interpreter: forward resume_fn + resume_args (n, acc)
    -> yield reporting REDUCTIONS
  boundary: if heap.should_gc() holds, collect
  dispatch resumes the continuation with a fresh 4000 budget
    -> the count finishes in the next quantum
```

An allocation-heavy loop differs only in heap state: consing may make
`heap.should_gc()` true or grow into another block, but it does not affect the
reduction budget. The next yield still happens when reductions run out.

## Parity

The budget model is identical in the interpreter, JIT, and AOT: the same
`Process` budget fields and the same `Heap::should_gc`. The compiled paths (JIT
and AOT) share the boundary collection through `Process::boundary_maintenance`.
The resume carrier differs — a zero-arg continuation closure in compiled code,
forwarded `resume_fn` + `resume_args` in the interpreter, which does not collect.
Pure fz code yields automatically by reduction budget. Tests pin both sides:
allocation-light loops assert `reduction_yields > 0`, and allocation-heavy loops
with spare budget assert a due collection does not produce a yield before
budget exhaustion.
