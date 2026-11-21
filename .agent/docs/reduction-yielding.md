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
(`annotate_back_edges` in `src/compiler2/jobs/native.rs`), and a tail call to
the function itself is the one such edge that stays inside a function: it
charges its reduction and makes the yield check like any other, then jumps to
the function's head block instead of calling. A yield there captures the new
arguments and resumes by calling the function with them. Control that stays
inside a function otherwise moves by `Goto` and spends nothing: a function's
dispatch hands control to a clause body by `Goto`, so a step through a
multi-clause function spends one reduction, at its tail call. An entry is a
block only when every transfer that reaches it is a direct transfer from its own
function (see [`pipeline`](pipeline.md)), so blocks never form a loop of their
own and every loop closes at a tail call. A call to a frame-free function is
lowered in its caller (see [`pipeline`](pipeline.md)): it is neither a tail
call nor a continuation, and a frame-free function is in no call cycle, so it
has no back edge; it spends no reduction and builds no continuation closure.
The closures a loop builds are those of its calls to functions that need a
frame and one per yield. Fixture 01177 pins both through
`Process.heap_alloc_stats()`: its loop's calls are all frame-free, so
`continuation_allocs` minus `reduction_yields` is 1, for `main`'s call into the
loop, and `reductions_executed` is the reductions the loop's back edges spent,
one per iteration. Fixture 01880 counts the continuations of calls to callees
that are and are not frame-free. Fixture 01376 loops past many
quanta through a self tail call beside a second process.

## Who owns what

- **`Process`** (`runtime/src/process.rs`) owns the budget cell, cumulative
  reduction counters, and transient per-quantum yield reason bits. Its budget
  accounting methods are `reset_reduction_budget` and `finish_yield_report`.
  `Process::collect` is the one place a process's roots are assembled (see
  "Accounting at the boundary").
- **`Heap`** (`runtime/src/heap`) owns allocation, block growth, and
  `should_gc`, a pure function of the heap's state: the young bytes, those
  allocated or received since the last collection (`young_bytes`), against
  `live_baseline`, the bytes in old blocks, held between `BUDGET_FLOOR` (4096
  bytes) and the largest pooled block (`young_budget`). A
  collection sets `live_baseline` to the old bytes it leaves; allocation and
  `graft` leave it alone. Exhausting the current
  block parks it in `young_blocks` for the next Cheney pass and installs a tip
  one capacity step up; an object larger than that step is parked in a block of
  its own and the tip is left as it was. The tip and `young_blocks` are the
  young blocks, and so are the blocks grafted from another heap's gift segment
  (`Heap::graft`); `parked_fill` is the running sum of the fill of the parked
  ones, so `young_bytes` is the tip's fill plus `parked_fill`. Blocks a
  collection filled with survivors are old (`old_blocks`). Every block counts by
  fill. `should_gc` is also due when the shared
  binary bytes made since the last collection (`binary_budget.young_binary_bytes()`)
  reach the bytes of binary buffers the heap still holds, at least 256 KiB
  (`BinaryBudget` in `runtime/src/heap/binary_budget.rs`). A process allocating a
  shared binary through `Process::alloc_bitstring`, `alloc_bitstring_with` or
  `alloc_concatenation` that reaches that budget sets `reductions_remaining` to
  zero, so its quantum ends at the allocation and the boundary collects; an
  allocation made directly on a `Heap`, such as a message copy onto a receiver,
  cuts no quantum.
- **The schedulers** (JIT `src/exec/runtime.rs` with `CompiledModule::run_quantum`
  in `src/ir_codegen/compiled.rs`, AOT `runtime/src/aot_shim.rs`, interpreter
  `src/ir_interp`) own dispatch: install a fresh budget and run the process.
  The scheduling core (`runtime/src/sched_core.rs`) owns the boundary decision:
  the JIT, AOT and interpreter schedulers call `end_quantum` after every
  quantum, which collects a yielding or parked process if `Heap::should_gc`
  holds (a halting process is not collected), runs the destructors of the
  resources that collection or the exit sweep freed, and returns the process's
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
                    compiled: build the zero-arg continuation closure
                    interpreter: forward resume_fn + resume_args
                    yield, reporting REDUCTIONS

allocation        bump_top += size
                  if bump_top would cross block_end:
                    allocate a larger block
                    move old current block to young_blocks

boundary          if heap.should_gc():   (young_bytes >= max(live_baseline, BUDGET_FLOOR)
                                          or young_binary_bytes >= binary_budget)
                    Process::collect
                  clear yield_reasons
```

The two engines hand control back differently. Compiled code (JIT and AOT)
builds a zero-arg continuation closure on exhaustion and leaves it in
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
7 MiB (32 entries). A tip starts at the first entry and climbs the table, and
`next_block_capacity` stays at the last entry once it reaches it. A request below the first entry gets a block of the request rounded up to 16
bytes, and the pool keeps a free list for each such multiple of 16, so a small
block is recycled like a table block and its in-use and idle bytes are its exact
size. A single allocation or gift above the last entry is exact:
`pick_block_capacity` returns the request rounded up to 16 bytes, and the block is allocated at that size and
returned to the system allocator, not the pool, when it is released. A young tip
or a collection's to-space is never exact: `pick_tip_capacity` clamps
`pick_block_capacity` to the last entry, so young space past the table is a chain
of last-entry blocks that recycle through the pool;
`pool_outstanding_blocks` counts pooled blocks, small ones included. An object above the table
is parked in an exact block, is part of `bytes_used` and is copied by Cheney like any other, into an
exact block of its own.

## The gift window

A gift is measured, then copied. `measure_deep_copy` returns the bytes the
copy will allocate: it walks the same kinds under the same ownership test and
the same absence of sharing as `deep_copy_any_value_ref`, which keeps no record
of what it has copied, as a send in BEAM does not: an object reached twice is
copied twice and counted twice. Each object is the size `strict_object_size`
states for its source. `Heap::begin_gift(measured_bytes)` sets the current tip aside and
installs one fresh block of `pick_block_capacity(measured_bytes)`: a pooled
block of the measured bytes below the table, a table entry within it, and an
exact block above it. The copy allocates through
`alloc_kind` into that block and cannot overflow it. `Heap::end_gift` asserts
the block's fill is exactly the measured bytes, turns the block and the off-heap
objects produced since the window opened (one chain of BinRefs and resource stubs)
into a `GiftSegment` of exactly one block, restores the saved tip, and puts
`live_count` back. Allocation statistics stay with the heap that did the
copying. `Heap::graft` on another heap adopts the segment; dropping an
un-grafted segment releases its block and its objects' off-heap references. A
collection asserts that no window is open. Cross-process send is the window's user: `sched::gift_copy` measures a
message, or a match's roots, and copies it inside one, and the segment travels to the
receiver on its `in_queue` (see [scheduler](scheduler-zero-arg-closures.md)).

A grafted block is young: it is parked among the young blocks and its fill
counts toward `young_bytes` exactly as allocation does, so received bytes bring
the next collection nearer. `Heap::graft` leaves `live_baseline`, `old_blocks`
and `old_objects` alone and adds the block's fill to `received_bytes`, which
the next collection reports as `received_bytes` in the gc event and resets. A
gift references only itself and literals. A minor collection reclaims the block
of a gift that is dead and copies a live gift's data once, into an old block.
Its list cells are shared from birth (`link_list_tail` marks each cell copied
inside a window), so a message's cells are never rewritten in place. The gift's
off-heap prefix, BinRefs and resource stubs on one chain, splices onto the
young chain (`off_heap_head`) and a sweep moves the survivors to the old chain.

A message waits outside the heap until a receive takes it. The `Mailbox`
(`runtime/src/mailbox.rs`) holds one queue in arrival order of messages, each
with the gift segment that holds it. A message the process sends to itself is
copied into a gift like any other (`sched::self_send`). `sched::drain_in_queue`
puts each arriving message in the mailbox with its segment, ungrafted, and
grafts only a match for the parked receive. The receive that matches a waiting
message calls `Mailbox::take`, which grafts the segment, so the message becomes
young at the moment it is taken. A message nobody takes costs the heap nothing
and is no collection root.

A collection is minor or major (`Heap::next_generation`). A minor collection's
from-space is the young blocks, so old blocks stay where they are and a
pointer into one is left as it is. A major collection's from-space is every
block, and it runs once `live_baseline` exceeds `MAJOR_GROWTH_FACTOR` (2) times
the larger of the old bytes the last major collection left and half the smallest
tip; a heap with nothing old is always minor. Either way the survivors are
copied by `Heap::bump_to_space` into a to-space block whose capacity is a guess
(the old bytes for a major collection; the bytes the last minor collection
copied for a minor one; at least the smallest tip): a copy that fills the block
parks it and installs an overflow block, the smallest class first (the last table
entry when the guess is at least that large) and one class up for each later one,
saturating at the last entry, and an object above
the next step parks alone. A wrong guess leaves at most about the overflow
unused (`to_space_capacity_bytes` less `copied_bytes`). The blocks the copy filled become old, the
from-space is released, and allocation continues in a fresh tip sized to the
old bytes, at most the last table entry. After a minor collection `live_baseline` is the old bytes it had plus
the bytes copied; after a major collection it is the bytes copied.

Compiled yield telemetry samples the slow path that builds the yield
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
the process: the runnable continuation closure; the park record's frame; a delivered handler; the handler captures; and any transient values the
caller passes. Each slot holds its forwarded value afterwards and is written
back to where it came from. The decision is made at scheduler-quantum
boundaries, never per back edge. Gifts waiting in the delivery in-queue and
messages waiting in the mailbox are not roots: their blocks join the heap only
when grafted, and every reference in a gift points into its own segment.

`sched_core::end_quantum` packages this decision (collect if needed, clear the
reason bits, run the queued destructors) and returns the `Disposition` (`Requeue`, `Parked` or `Exited`); it reports the
`Collection` it performed through `Scheduler::observe` (see
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
reductions and so collects only at a park, never at an exit.
Pure fz code yields automatically by reduction budget. Tests pin both sides:
allocation-light loops assert `reduction_yields > 0`, and allocation-heavy loops
with spare budget assert a due collection does not produce a yield before
budget exhaustion.
