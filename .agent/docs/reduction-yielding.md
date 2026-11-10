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
  accounting methods are `reset_reduction_budget` and `finish_yield_report`.
  `Process::collect` is the one place a process's roots are assembled (see
  "Accounting at the boundary").
- **`Heap`** (`runtime/src/heap`) owns allocation, block growth, and
  `should_gc`, a pure function of the heap's state: the bytes allocated since
  the heap was last all live (`bytes_used - live_baseline`) against the larger
  of `live_baseline` and half the smallest tip. A collection sets
  `live_baseline` to its survivors and `graft` raises it by the gift's fill;
  allocation leaves it alone. Exhausting the current block parks it in `blocks` for the next
  Cheney pass and installs a tip one capacity step up; an object larger than
  that step is parked in a block of its own and the tip is left as it was. Blocks grafted from
  another heap's gift segment (`Heap::graft`) join `blocks`, are from-space for
  the next pass, and count by fill like any other parked block.
- **The schedulers** (JIT `src/exec/runtime.rs` with `CompiledModule::run_quantum`
  in `src/ir_codegen/compiled.rs`, AOT `runtime/src/aot_shim.rs`, interpreter
  `src/ir_interp`) own dispatch: install a fresh budget and run the process.
  The scheduling core (`runtime/src/sched_core.rs`) owns the boundary decision:
  the JIT, AOT and interpreter schedulers call `end_quantum` after every
  quantum, which collects if `Heap::should_gc` holds, runs the destructors of
  the resources that collection or the exit freed, and returns the process's
  `Disposition`. A process a caller lends the interpreter, whose heap the caller
  holds refs into, is not collected.

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

boundary          if heap.should_gc():   (bytes_used - live_baseline >= max(live_baseline, SIZE_TABLE[0] / 2))
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
object, `Heap::alloc_kind` takes one of two paths. An object no larger than
`next_block_capacity(block_size)` parks the tip in `blocks` and installs a fresh
tip one capacity step up. A larger (huge) object is placed at the start of a
block of `pick_block_capacity(size)` that is parked in `blocks` at once, with its
fill ending at the object; the tip, its bump pointer and its capacity do not
move, so the next small allocation lands in the tip it was already filling. This is why allocation does not need to force a
scheduler yield to remain total.

`SIZE_TABLE` lists the capacities the block pool recycles, from 1 KiB to about
7 MiB (32 entries). A tip starts at the first entry and climbs the table. A
block outside the table's range is exact: `pick_block_capacity` returns the
request rounded up to 16 bytes, whether the request is below the first entry
or above the last. An exact block is allocated at that size and is returned to
the system allocator, not the pool, when it is released;
`pool_outstanding_blocks` counts pooled blocks only. An object above the table
is parked in an exact block, is part of `bytes_used` and is copied by Cheney like any other, so to-space
grows past the table to hold it.

## The gift window

A gift is measured, then copied. `measure_deep_copy` returns the bytes the
copy will allocate: it walks the same kinds under the same ownership test and
the same sharing as `deep_copy_any_value_ref`, so an object reached twice is
counted once, and each object is the size `strict_object_size` states for its
source. `Heap::begin_gift(measured_bytes)` sets the current tip aside and
installs one fresh block of `pick_block_capacity(measured_bytes)`: an exact
block of the measured bytes below the table, a table entry within it, and an
exact block above it. The copy allocates through
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
`bytes_used`; it is also part of `live_baseline`, because a gift arrives packed
and fully live, the state of a heap after a collection. A gift therefore never
makes a collection due: only the receiver's own allocation does, once it
reaches the baseline. A collection sizes to-space from `bytes_used` first: the
capacity holding every byte in use is the floor, and the grow, keep and
shrink bands choose between that floor and a larger capacity. Grow applies when
`bytes_used` fills 75% or more of the tip; shrink when the live baseline
fills 25% or less of it; keep otherwise. To-space capacity is therefore at
least the bytes a pass can copy.

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

`sched_core::end_quantum` packages this decision (collect if needed, clear the
reason bits, run the queued destructors) and returns a `QuantumEnd`: the
`Disposition` (`Requeue`, `Parked` or `Exited`) and the `Collection` it
performed, which the JIT reports as `fz.runtime.gc` (see
[runtime telemetry](runtime-telemetry.md)). The JIT, the AOT shim and the
interpreter call it after every quantum, whatever state the process is in. A
halted process whose heap is not due is not collected; its resource stubs are
swept without a to-space. The interpreter keeps a parked receive's environment
and continuations in its own structures; its `Scheduler::collect_heap` passes
their heap refs to `Process::collect` as transient roots and writes the
forwarded refs back. It never yields, so no resume entry of a process outlives
its quantum.

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
`Process` budget fields and the same `Heap::should_gc`. All three paths
share the boundary collection through `sched_core::end_quantum`. The resume
carrier differs — a zero-arg continuation closure in compiled code,
forwarded `resume_fn` + `resume_args` in the interpreter, which charges no
reductions and so collects only at a park or an exit.
Pure fz code yields automatically by reduction budget. Tests pin both sides:
allocation-light loops assert `reduction_yields > 0`, and allocation-heavy loops
with spare budget assert a due collection does not produce a yield before
budget exhaustion.
