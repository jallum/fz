# Runtime Telemetry

## Model

Runtime telemetry is how the running scheduler reports what a task did, and how
tests observe a run without reaching into a `Process`. It is the runtime side of
the same idea as compile-time [`telemetry`](telemetry.md): the system writes down
facts it already holds, and a sink that is listening reads them.

Every runtime event is a variant of `RuntimeEvent` (`runtime/src/telemetry.rs`),
and the scheduling core reports each one through `Scheduler::observe`, a
required method with no default: a scheduler that ignores events says so in
code. `end_quantum` observes the collection and the exit, `next_runnable`
observes a sleep, and the send paths and run teardown observe their own events.

- The JIT `Runtime` and the interpreter's scheduler adapter implement `observe`
  with `emit_runtime_event` (`exec/runtime.rs`), the one function that raises
  the typed raw event for each variant on the telemetry bus.
  `Runtime::new(compiled, workers, tel)` preserves the concrete telemetry type,
  so `NullTelemetry` remains monomorphizable.
- `JsonlBackend` handles each raw event by rendering it with
  `fz_runtime::telemetry::write_line`, the one writer of a runtime event's
  line: the envelope every telemetry line shares, then the event's metadata.
- `AotScheduler::observe` appends each event, rendered with the same
  `write_line`, to the file `FZ_LOG_TELEMETRY` names; see
  [Built binaries](#built-binaries).

Ten events matter:

- `fz.runtime.execution_ready` — the boundary between compiling a program and
  running it, emitted by `run_root_jit` and `run_root_interp`.
- `fz.runtime.process_exited` — one per task exit, carrying the existing pid and
  live `Process` authority.
- `fz.runtime.scheduler_slept` — one each time the scheduling core sleeps for a
  pending receive-after timer because nothing is runnable.
- `fz.runtime.timer.armed`, `fz.runtime.timer.fired`, `fz.runtime.timer.cancelled`
  — the life of one receive-after timer; see [`fz.runtime.timer.*`](#fzruntimetimer).
- `fz.runtime.send.probe` — one per cross-process send, carrying what the
  sender's probe decided and what it cost.
- `fz.runtime.raise` — one per raise, caught or not, before the runtime decides
  where it goes.
- `fz.runtime.gc` — one per heap collection a scheduler boundary performs,
  carrying the collection's stats.
- `fz.runtime.alloc_site` — one per allocation site that placed an object,
  after every process has been torn down; see [`fz.runtime.alloc_site`](#fzruntimealloc_site).
- `fz.runtime.reuse_site` — one per reuse site that reused or replaced an
  object, next to the allocation sites; see [`fz.runtime.reuse_site`](#fzruntimereuse_site).
- `fz.runtime.run_ended` — one per run, after every process has been torn down,
  carrying the block pool's census.

## `fz.runtime.execution_ready`

`signal_execution_ready` (`execution_ready.rs`) raises it through `emit_runtime_event`, called
by `run_root_jit` just before the runtime spawns the entry and by
`run_root_interp` just before `run_backend_main` enqueues it — so the event
lands once per `fz2 run`, once per `fz2 interp`, and once per `run-test-root`
child `fz2 test` starts, with parsing, the fixpoint drive, the backend product
and Cranelift all behind it. A built binary observes it from `fz_aot_run_main` before its run-queue loop.
The event has no payload; its content is its position in the stream. The same
call writes one byte to the descriptor named by
`FZ_EXEC_READY_FD` when the environment names one — the fixture matrix's
execution deadline is a consumer of this boundary, not a second definition of it
(see [fixtures](fixtures.md)). A built binary does not write that byte; the
build leg's deadline starts when the binary is spawned.

## `fz.runtime.process_exited`

`sched_core::end_quantum` observes `RuntimeEvent::ProcessExited` for a halted
process once its destructors have run, on every scheduler. `emit_runtime_event`
raises it with the process's pid and the `Process` before it is retired (its heap is
released right after the event); the event carries no derived process fields:

```text
raw event:    fz.runtime.process_exited
signature:    (&PidId, &Process)
```

`ExitRecord` is the test-side projection: `{ pid, halt_value: i64,
bytes_used: usize, raises_delivered: u64, reduction_yields: u64,
failed: bool, dtors_dispatched: u64, frame_copies: u64 }`. `failed` is
`Process::ended_in_failure`: whether the process ended through an uncaught raise
with a non-zero exit status (see [exceptions](exceptions.md)); an exit with a
shutdown reason of status 0 ends a process without failing it. A failed
process's `halt_value` is not a return value. `raises_delivered` counts the
raises a handler took in this process, and `reduction_yields` the times its
reduction budget ran out and it yielded to the scheduler. `write_line` also
renders `parks` after `reduction_yields`: the quanta that ended with the
process parked on a receive (`sched_core::end_quantum` counts them), so
`reduction_yields + parks` is the boundaries at which a collection could run.
It renders `binaries_shared` after `bytes_used`: the binaries the
process marked shared (see [any-value](any-value.md), "Shared Lists, Structs
And Binaries").
`frame_copies` counts the
shared body frames a store copied to the heap tip because a collection had kept
them (see [scheduler-zero-arg-closures](scheduler-zero-arg-closures.md)). `ProcessExitCapture`
builds it during dispatch by reading the live process. `write_line` reads the
same fields when it renders the event, nested under
`"process":{"opaque_type":"fz_runtime::process::Process",...}` with `failed` as
a JSON boolean. The emitter does not traverse the process for telemetry.

Retention is not a per-process figure. What a program reused in place or
replaced is counted at its reuse sites and reported by
[`fz.runtime.reuse_site`](#fzruntimereuse_site).

`dtors_dispatched` is `Process::dtors_dispatched`: the resource destructors the
scheduling core ran for the process over its whole life, whether a collection
freed the resource at a yield or park or the exit swept it (see
[scheduler](scheduler-zero-arg-closures.md#the-step-after-a-quantum)).
`write_line` renders it on `process_exited` as a number beside
`parks`. There is no separate destructor event; a destructor
dispatched mid-life is visible on the exit record of the process that ran it,
and the `fz.runtime.gc` event of the collection that freed it precedes it. A
minor collection examines only the young off-heap chain, so a resource stub that
became old is found dead by the next major collection, whose event has
`generation` `"major"`; a resource that dies young is found by the next
collection of either kind.
`tests/fixture_matrix.rs`
(`a_resource_freed_by_a_collection_runs_its_destructor_once_on_every_path`)
pins it on the `run`, `interp` and `build` paths: 1 for fixture 00906 and 3 for 00907.

The raw `&Process` is valid only during dispatch. A handler that needs data
after the callback must project and copy that data itself. `write_line` renders
fields synchronously.

## `fz.runtime.scheduler_slept`

`next_runnable` (`runtime/src/sched_core.rs`) observes
`RuntimeEvent::SchedulerSlept(wait)` just before it waits on its `Clock`; `wait` is the
`Duration` until the next timer deadline. `write_line` renders it as `wait_ns`.
The event fires only when the run queue is empty and a timer pends and has not
yet expired, so a program whose timers are all cancelled by arriving messages
never emits it, and whether a short timer emits it depends on how long the
machine took to reach the wait. A test therefore pins it only on a core driven
by a manual `Clock` (`sched_core_test.rs`), where the wait is exact; a test of a
whole run reads the `timer` events instead.

## `fz.runtime.timer.*`

<a id="fzruntimetimer"></a>

A receive with a positive `after` timeout arms one timer for its process.
Three events report its life, each carrying the timer id the core handed out and
the pid it wakes:

```text
raw event:    fz.runtime.timer.armed       signature: (&TimerArmed)      { timer, pid, armed, deadline }
raw event:    fz.runtime.timer.fired       signature: (&TimerFired)      { timer, pid }
raw event:    fz.runtime.timer.cancelled   signature: (&TimerCancelled)  { timer, pid }
```

- `armed` is observed by the `ExecCtx::timer_schedule` hook (`timer_schedule_hook`)
  right after the core schedules the timer. `armed` and `deadline` are how long
  after the scheduler's `Clock` began the core read its clock and the timer
  expires; `write_line` renders them as `armed_ns` and `deadline_ns`, so
  `deadline_ns - armed_ns` is exactly the requested `after` in nanoseconds.
  Deadlines of one run share that origin, so they order the run's
  timers whatever the load on the machine.
- `fired` is observed by `next_runnable` for each timer it drains as expired, in
  deadline order, just before the scheduler's `wake_expired` runs.
- `cancelled` is observed by the `ExecCtx::timer_cancel` hook only when the timer
  was still pending: a message that wakes the receiver cancels its timer, and a
  cancel of a timer that already fired or was already cancelled reports nothing.

Every timer armed ends in exactly one of `fired` or `cancelled`, unless the
program halts first. All three schedulers report them through `observe`: the JIT
`Runtime` and the interpreter adapter raise the typed raw event
(`emit_runtime_event`) and the AOT scheduler writes the line to its log, so the
three paths emit the same sequence for the same program.

`SchedulingCore` reads and waits on a `Clock` (`runtime/src/clock.rs`): the system
clock sleeps the thread, and a manual clock, which only tests construct, lets
the core's wait pass instantly. `sched_core_test.rs` drives the core on a manual
clock, so deadline order, cancellation and the exact `scheduler_slept` wait are
asserted without sleeping. `TimerWheel::schedule` takes the deadline itself and
`drain_expired` takes `now`, so `timer_test.rs` never waits for a deadline.

`tests/fixture_matrix.rs`
(`a_receive_timer_is_armed_then_fired_or_cancelled_and_fires_in_deadline_order_on_every_path`)
reads the events from the `run`, `interp` and `build` logs: fixture 00687's one
timer is armed for exactly 1 ms then fired, 00692's is armed for exactly 60000 ms then cancelled with nothing fired,
00690's child timer fires while main's long timer is cancelled, and the two
timers of 00693 and 00691 fire in the order of the deadlines their `armed` events
reported. That order is read from the run's own deadlines, so it holds however
long the machine stalled between the two arms.

## `fz.runtime.alloc_site`

An allocation site is one place that puts an object on a heap
(`runtime/src/alloc_site.rs`). There are two kinds:

- A **compiled site** is a place in a compiled function that allocates
  inline. `SiteTable::count_alloc` (`src/compiler2/native_codegen/site_table.rs`)
  registers it while the function is lowered and emits one increment of the
  site's own counter, placed where the fast and slow paths of the allocation
  join, so one placement is one count. The counters are one zeroed, writable
  data object of the module; its kind and size are fixed per site, so bytes are
  the count times the size. The continuation frame, the list cell, the struct or
  tuple, the closure and the scalar box are the allocations compiled code places inline,
  through `emit_place` (`native_codegen/place.rs`), the one emitter of the
  bump: a non-tail call's frame, the frame a budget yield leaves, each cell a
  list literal or a cons builds, each struct or tuple that is not a constant,
  each closure with captures, each int, float or reference boxed for an `any`
  slot, and each inline bitstring a slice copy or a whole-byte construction places are compiled sites. The runtime's own continuation site is the
  copy `fz_frame_for_write` makes of an old frame.
- A **runtime site** is a runtime function that allocates:
  `Heap::alloc_at` takes a `RuntimeAllocSite`, which fixes the object's kind,
  and records the allocation and its bytes in `Node::runtime_allocs`.

Both tables belong to the program's `Node`, so a process carries no site
state and spawning one costs nothing for it. The compiled table
(`runtime/src/site_table.rs`) holds the program's allocation sites and its
reuse sites together, each with the counter words it owns. It is registered
once: `JitBackend::finalize` hands the node the module's sites and the address
of its counters, and a built program's `main` calls
`fz_aot_register_sites` with the same two things before any compiled code
runs. An interpreted program has no compiled sites.

`report_sites` (`runtime/src/telemetry.rs`) raises one `alloc_site` event per
site that placed at least one object, compiled sites first in registration
order, then runtime sites, and then the `reuse_site` events. Each path raises
them at the end of the run, just before `run_ended`.

```text
raw event:    fz.runtime.alloc_site
signature:    (&AllocSiteCount)
```

`AllocSiteCount` is `{ function, kind, placed }`; `write_line` renders it as
`function`, `object` (the kind, spelled as `System.alloc_stats()` spells
it), `allocs` and `bytes`. `function` is the compiled function's symbol, or
`runtime::<function>` for a runtime site. Two sites in one function are two
events with the same `function`.

A list cell a deep copy places is counted at `runtime::copy_list_cell`, apart
from the cells the runtime builds for the interpreter and its own helpers
(`runtime::alloc_list_cons_storage` and `runtime::alloc_list_cons_value`); a
compiled program's own cells are compiled sites. A message's cells are copied by its sender
into a gift, so a run whose copy site counts exactly the cells its
`fz.runtime.send.probe` gifts carry copied nothing on the receiving side;
fixtures 00901 and 00902 are pinned that way.

The sites count for the whole program, from the moment it is loaded, every
process and the closures the scheduler builds to enter each one. The figure
`System.alloc_stats()` returns is the sum of these sites (`Node::alloc_stats`),
so the two always agree. An off-heap binary buffer is the runtime site
`runtime::alloc_shared_bin`, reported with kind `shared_bin`; it is not in the
figure's total.

## `fz.runtime.reuse_site`

A reuse site is one place that rebuilds a list cell or a struct from the object
it took apart (`runtime/src/reuse_site.rs`). The object is written in place, a
**hit**, or a new one is placed, a **miss**. Each reuse bumps exactly one of its
site's two counters; the attempts at a site are its hits plus its misses. A
site's kind is `list`, `struct` or `tuple`.

- A **compiled site** is a place in a compiled function that decides a reuse
  inline. It owns two counter words, hits then misses, in the same zeroed data
  object as the allocation sites' counters (`SiteTable::register_reuse`,
  `src/compiler2/native_codegen/site_table.rs`). The list-cell row
  (`native_codegen/list_reuse.rs`) is one site: a cell kept as it is and a cell
  rewritten in place count hits, and the new cell it places counts a miss. An
  unshared struct an update stores into (`CodegenFn::rewrite_unshared_struct`)
  counts a hit at its own site; the copy it makes instead is `fz_struct_copy`,
  which counts at its runtime site.
- A **runtime site** is a runtime function that reuses or replaces, a
  `RuntimeReuseSite`, counted on the node in `Node::runtime_reuses`:
  `fz_list_reuse_or_cons_parts` (`ListReuse`, a hit when the answer is the
  source cell), `fz_struct_copy` (`StructCopy`, a miss), `fz_struct_reuse_or_copy`
  (`StructReuse`, a hit when it answers the base and a miss when it copies) and
  `fz_tuple_put` (`TupleCopy`, a miss of kind `tuple`). The interpreter has only
  these.

```text
raw event:    fz.runtime.reuse_site
signature:    (&ReuseSiteCount)
```

`ReuseSiteCount` is `{ function, kind, reused }`; `write_line` renders it as
`function`, `object` (`list`, `struct` or `tuple`), `hits` and `misses`. One
event is raised per site that reused or replaced at least one object, after the
`alloc_site` events.

The program's figure is the sum of these sites: `Node::retention_stats` is the
list figure and the struct figure, where the struct figure includes tuple
copies, and `Node::reuse_stats(kind)` asks for one kind alone. A fixture that
pins a retention figure sums the events of one run, not the exit lines of its
processes.

## `fz.runtime.run_ended`

`RunEnded::sample` (`runtime/src/telemetry.rs`) reads the census and
`emit_runtime_event` raises it. The JIT `Runtime` observes it from its `Drop`, after dropping the process table (an exited process's
heap is released at its exit, so what the drop releases is the parked processes' heaps and any gifts still
queued on them). The interpreter observes it in
`run_backend_main` after dropping its `IrInterpRuntime`.

```text
raw event:    fz.runtime.run_ended
signature:    (&RunEnded)
```

`RunEnded` is `{ pool_outstanding_before_run, pool_outstanding_after_run,
pool_cached_blocks, footprint }`. The first three are block counts of the
thread's block pool; `footprint` is the byte accounting described under
`fz.runtime.gc`, read once every process has been torn down, and `write_line`
renders it as `in_use_bytes`, `idle_bytes`, `peak_in_use_bytes`, `trims` and
`pages_given_back`. Outstanding
is the count `pool_alloc` has handed out minus the count `pool_free` has taken
back (`heap::pool_outstanding_blocks`), sampled when the run began and again
once every process has been torn down; `pool_cached_blocks` is the blocks
resting in the pool's free lists. Exact blocks (a gift above the
table) are spans of the heap range that no pool recycles and appear in neither count. The compiler's own heaps live on the same
thread for the whole run, so the absolute outstanding count is never zero. The
run's guarantee is `pool_outstanding_after_run == pool_outstanding_before_run`:
it returned every block it took. `write_line` renders
all three as numbers. A built binary samples the outstanding count in `fz_aot_setup` before it
creates main's process and observes the event from `fz_aot_run_main` after the
scheduler has dropped. `tests/fixture_matrix.rs`
(`a_receiver_left_parked_with_queued_gifts_drops_them_at_teardown`) asserts the
equality for fixture 00903 on the `run`, `interp` and `build` paths.

## `fz.runtime.interp_ran`

The interpreter counts its own work in plain integer fields on
`IrInterpRuntime` (`counts: InterpRan`), so the hot path pays an increment, and
`run_backend_main` raises `INTERP_RAN` once, through `raw_event1`, after the
runtime has dropped and just before `run_ended`:

```text
raw event:    fz.runtime.interp_ran
signature:    (&InterpRan)
```

`InterpRan` is `{ entries, calls, frames }`:

- `entries` — control entries run by `step_eval_entry`: a clause entry, a
  call-return resume, a branch, a receive outcome.
- `calls` — executables started by `step_backend_executable`, extern bodies
  included.
- `frames` — `Frame`s built, one per clause-backed executable started (see
  [interpreter frame](interpreter-frame.md)); `calls` minus `frames` is the
  extern calls.

The counts are per run: one `IrInterpRuntime` serves every process of the run,
so they sum over all of them. A macro expansion runs in its own runtime and
reports nothing. `JsonlBackend` renders the three numbers as metadata; the
payload is typed, so `--emit=stats` shows only that the event fired once.
`Enum.to_list(1..n)` then `Enum.count` runs 18 entries, 11 calls and 11 frames
per element; `building_and_counting_a_list_runs_eighteen_entries_per_element`
(`ir_interp/backend_test.rs`) reads the event through `attach_raw_event1` and
pins the three as the difference between two list sizes.

## `fz.runtime.send.probe`

A send to another process runs `sched::probe_sender` on the sender: the
receiver's parked matcher, if any, is tested against the message with the
sender as the allocating process, and whatever the receiver will keep (the
roots of the winning clause on a hit, the whole message on a miss) is copied into a gift on the
sender's heap and queued on the receiver's `in_queue`. The JIT
`send_via`, the interpreter's `send_ref` and the AOT send hook each observe
`RuntimeEvent::SendProbe` with the `SendProbe` the probe returned; the first two
raise it through `emit_runtime_event` and the AOT scheduler writes it to its log:

```text
raw event:    fz.runtime.send.probe
signature:    (&SendProbe)
```

`SendProbe` is `{ outcome: Hit | Miss, receiver: PidId, reductions: i64,
gift_bytes: usize, gift_blocks: usize, gift_roots: usize }`. `reductions` is the change in the
sender's remaining budget across the matcher call; `gift_bytes` and
`gift_blocks` are the segment's fill and block count. `gift_bytes` equals the
bytes `measure_deep_copy` returned before the copy, and `gift_blocks` is `1`
for every gift that allocates; both are `0` when a hit gifts nothing and no
window opens. `gift_roots` is the number of roots a hit carries (see
[pattern matching](pattern-matching.md#outcome-values-and-retained-lists)) and
`0` for a miss. `write_line` renders the
outcome as `"hit"` or `"miss"` and the rest as numbers. A self-send is a copy into
the sender's own mailbox and emits nothing, as does a send to an exited or unknown receiver. `tests/fixture_matrix.rs`
(`a_send_probes_on_the_sender_and_gifts_its_result_through_the_receivers_in_queue`)
pins the event sequence of fixtures 00901 and 00902 on the `run`, `interp` and
`build` paths, together with the cells their run copied (see
[`fz.runtime.alloc_site`](#fzruntimealloc_site)), and `a_receiver_left_parked_with_queued_gifts_drops_them_at_teardown`
pins each of fixture 00903's three gifts (`gift_bytes` 16032, 64 and 16, one
block each).
`many_senders_into_one_guarded_receive_gift_one_message_each_and_leave_the_misses_queued`
pins fixture 00910's hundred probes on `run`, `interp` and `build` (fifty misses of 80
bytes, the one hit of 48, then forty-nine misses; 7968 bytes in all), and
`a_large_list_passed_back_and_forth_crosses_as_one_gift_per_message_on_every_path`
pins fixture 00911's nine hits (the empty announcement, then eight balls of
320016 bytes: 20000 cells plus the bound number as a boxed scalar). Both
fixtures have the same probes on all three paths.

## `fz.runtime.gc`

`sched_core::end_quantum` (`runtime/src/sched_core.rs`) collects the process's
heap when `Heap::should_gc` holds and observes the collection it performed as
`RuntimeEvent::Gc`, right after collecting and before any destructor runs. The
collection's `Collected` is alive for the observation and dropped after it, so the
event reads the from-space blocks as they were. How the quantum ended is read off the process
(`Process::quantum_end`, a `Disposition`):

```text
raw event:    fz.runtime.gc
signature:    (&Collection, &GcStats, &Heap)
```

`Collection` is `{ pid, boundary: CollectionBoundary }`. The `GcStats` is the
slot `Process::gc_stats`, which `Heap::collect` writes once; the `Heap` is the
one whose blocks the collection left (`Heap::collected_blocks`). The runtime
computes nothing only to report it: the writer (`write_collection` in
`runtime/src/telemetry.rs`) computes the block counts and capacities from those
blocks, and reads the pool itself. A halting
process is not collected, so the boundary of a collection is `Yield` or `Park`.
`write_line` renders `pid`, the `boundary` as `"yield"` or `"park"` and the
`generation` as `"minor"` or `"major"`, then these `GcStats` fields as numbers.
A minor collection's from-space is the young blocks (the tip and the blocks
allocation parked since the last collection) and leaves old blocks in place; a
major collection's from-space is every block (`Heap::next_generation`):

- `copied_objects`: objects the pass copied, the survivors of its from-space; a list
  cell, a tuple, a map, a closure and a binary view each count one;
- `copied_bytes`: bytes the pass copied, the survivors of its from-space; a minor
  pass copies only young survivors, a major pass every live object;
- `live_bytes`: bytes the heap holds once the pass finished: what earlier
  collections kept (old bytes a minor pass left) plus what this
  pass copied, so after a major pass it equals `copied_bytes`; dead old data a
  minor pass cannot see is included until a major pass reclaims it;
- `young_bytes`: bytes the heap allocated or received since its previous collection, by
  fill (`Heap::young_bytes`): what `Heap::should_gc` compared with the budget
  when the collection became due. A process runs its whole quantum before the
  boundary asks, so it can be many times `young_budget`;
- `young_budget`: the young bytes at which the collection was due: the old
  bytes, at most the largest pooled block and at least `BUDGET_FLOOR` (4096);
- `received_bytes`: the bytes of `young_bytes` that receives brought in, the fill of
  the gift blocks `Heap::graft` parked since the previous collection;
- `young_binary_bytes`: capacity of the shared binary buffers the heap made since
  its previous collection (`BinaryBudget::young_binary_bytes`): the filled-buffer
  and concatenation-buffer sites, never an in-place append. `Heap::should_gc`
  compares it with `binary_budget`;
- `binary_budget`: the young binary bytes at which the collection was due: the
  binary bytes the heap held after its previous collection, at least
  `MIN_BINARY_BUDGET` (256 KiB). A collection is due by the binary rule when
  `young_binary_bytes >= binary_budget`, by the heap rule when
  `young_bytes >= young_budget`, or by both;
- `from_space_capacity_bytes`: capacity of every block the pass collected: the
  young blocks (the tip and every young parked block) for a minor pass, every
  block for a major pass. The writer sums it over `Heap::from_blocks`, which the
  `Collected` holds until it is dropped (`CollectedBlocks::from_space_capacity_bytes`);
- `blocks_released`: from-space blocks the pass releases when its `Collected`
  is dropped (`CollectedBlocks::blocks_released`);
- `to_space_guess_bytes`: capacity of the to-space block the pass started with,
  its guess at how many bytes it would copy;
- `to_space_capacity_bytes`: capacity of every block the copy filled, the guess
  block and its overflow blocks: the old blocks from `Heap::retired_from` on,
  summed by the writer (`CollectedBlocks::to_space_capacity_bytes`). Less
  `copied_bytes`, the room the pass left unused in old blocks;
- `blocks_after`: old blocks the heap holds once the pass finished, every block
  holding data a collection kept or a gift brought; the fresh empty tip is not
  counted.
- `stub_visits`: off-heap chain links the pass followed. Every BinRef and resource
  stub on a chain the pass examines is visited once by the sweep (a view is not on a chain): the young chain for
  a minor pass, the young and old chains for a major pass. Summed by `generation`, it
  says whether the sweep's cost lies in minors or in majors.
- `in_use_bytes` and `idle_bytes`: the thread's memory when the pass finished,
  across every process. The writer reads `heap::pool_footprint` while the
  from-space is still held and reports the footprint once it is released
  (`CollectedBlocks::footprint_once_released`): the from-space's capacity is
  not in use, and the pooled share of it is idle.
  In-use bytes are the capacity of every block the pool has handed out and not
  had returned (pooled and exact blocks, heaps and gift segments) plus the bytes
  of every off-heap binary block not yet freed (`bits::shared_bin_alloc_with`
  adds the whole block, header + capacity + 1; `shared_bin_destructor_heap`
  subtracts it); idle bytes are
  the capacity of the blocks resting in the pool's free lists. The pool owns
  the counters (`Footprint` in `runtime/src/heap/block_pool.rs`), so the
  runtime reads one authority. `Footprint.peak_in_use_bytes`, rendered on
  `run_ended`, is the highest in-use value any allocation reached, updated at
  every grow. `Footprint.trims` and `Footprint.pages_given_back`, rendered on
  `run_ended` only, are the pool's running counts of ended epochs and of
  operating-system pages the trims returned (`arena::drop_pages` reports its
  page count); both are field reads. An epoch ends when the bytes the pool has
  handed out reach `EPOCH_FACTOR` times `in_use_bytes + idle_bytes` (never under
  `EPOCH_FLOOR`), and the trim gives back the pages of each trimmed-class block
  that rested idle through the whole epoch; `idle_bytes` is a running count,
  adjusted where a block enters or leaves a free list. The binary buffer count is per thread, matching the pool: a
  buffer freed on a thread other than the one that allocated it is
  subtracted from the freeing thread's count, which stays signed so the
  free cannot underflow; the reporting thread is the one that runs the
  program and frees its own buffers.
- `stubs_made`, `binrefs_made` and `stubs_survived`: objects keyed by the site
  that made the binary object, every site present (0 when none), always in this order:
  `appended_in_place` (an append wrote into the spare room of the buffer its
  left side views, and the view is the longer view of that buffer),
  `window_of_buffer` (a window onto part of a buffer larger than the inline
  threshold), `grown_buffer` (an append overflowed its buffer and the result
  went into a new one with room to grow), `filled_buffer` (a binary above the
  inline threshold written into a new buffer sized to it: built binaries,
  `:binary.copy`, literals copied from module bytes), `message_copy` (a message
  copy gave the receiving heap its own BinRef and view of a shared buffer) and `static_literal`
  (a literal baked into the module, viewed in place).
  `stubs_made` counts the views the heap made since its previous collection, in
  every generation and for a view that went on to die; `binrefs_made` counts the
  BinRefs it made in the same window, one per fresh buffer or message-copied
  view and none for a window or an in-place append, so the two differ by the
  views that shared a BinRef. Both start again at each collection.
  `stubs_survived` counts, by site, the BinRefs the pass kept among those it
  examined: young BinRefs for a minor pass, young and old for a major pass, so
  a major pass counts a survivor under the site that made it however many
  collections ago. BinRefs a gift brought are made on the sender's heap and
  join the receiver's old chain unexamined. `StubSite` in
  `runtime/src/heap/stats.rs` is the one list of sites; `alloc_binref` and
  `alloc_view` take the site as a required argument, and a BinRef stores it in
  the low nibble of its `off_heap_next` word, which heap alignment leaves free, so
  it carries its site to its to-space copy at no cost in size.

`GcStats` carries more (object counts, root and per-container edge
counts); `Heap::collect` and `Process::collect` return all of it to their
callers and the heap's unit tests read it there. Every scheduler's
`end_quantum` observes it, so a built binary logs it too.
`tests/fixture_matrix.rs`
(`a_matched_reply_fixture_collects_only_the_child_and_only_where_it_yields`)
pins fixture 00901: 3 collections on `run`, all the child's yields, copying
512416 bytes in all, and none on `interp`, since the interpreter charges no
reductions and never yields mid-run. The parent is collected on neither path:
its heap is not due when it parks, and no collection follows before it exits.
The same file pins fixture 00910 (`interp`: the parent's park at 48 bytes;
`run`: its park at 288 bytes) and fixture 00911 (`interp`:
seven collections, each at a park and each copying 0 bytes, since a ball is dead by
the park after the receive that took it; `run`: thirteen collections, the parent's
yields while it builds the list, each park that follows a ball taken, and the
parent's later yields). The
run-ended equality is pinned for both fixtures on `run`, `interp` and `build`.
`sched_core_test.rs` pins the collection that `end_quantum` observes, that a
halting process is not collected, and the exit it observes and the destructors it dispatches.

## Built binaries

A built binary links `fz_runtime` and no host crate, so it has no telemetry bus.
When the environment variable `FZ_LOG_TELEMETRY` names a path, `fz_aot_setup`
opens it with create and append, so a log that `fz2 --log-telemetry <path>
build` wrote keeps its compile events first and the run's events follow. Each
event is rendered by `write_line` with span ids 0 and `time_ns` counted from
`fz_aot_setup`, and written with one `write` of one whole line on the unbuffered
file. With the variable unset no file is opened and `observe` returns on one
branch. A path that cannot be opened is a loud failure: a message naming the
path and the error on stderr and a non-zero exit before the program runs.

The binary reports `execution_ready`, `send.probe`, `gc`, `scheduler_slept`,
the three `timer` events, `process_exited` and `run_ended`. The absolute pool counts in `run_ended` are
smaller than on `run`, since no compiler heaps share the thread; the guarantee
is the same equality. In the fixture matrix the build leg of
`run_path_logged_to` runs `fz2 --log-telemetry <log> build`, then the binary
with the fixture's arguments and `FZ_LOG_TELEMETRY=<log>`.
`a_built_binary_reports_the_same_probes_collections_and_destructors_as_run`
asserts that for fixtures 00901, 00906, 00907, 00910 and 00911 the build's probe
sequence, collections and per-process `dtors_dispatched` equal `run`'s.

## `fz.runtime.raise`

The raise route (`fz_panic`, `fz_throw`, `fz_exit`, `fz_reraise`, `fz_raise_undefined_function`) reports every raise before deciding
where it goes, through the
`ExecCtx.raise` hook; the JIT runtime and the interpreter's scheduler adapter
emit `RuntimeEvent::Raise` with a `Raise<'a> { kind, exception, handler_depth,
stack_bytes }` (`runtime/src/telemetry.rs`), whose `kind` and `exception` borrow
the hook's bytes as `&[u8]`; the writer decodes them as UTF-8, lossily. The typed
raw event hosts attach to carries a `RaiseRecord`, the same four fields with the
text owned, made only when `Telemetry::is_raw_event_enabled` says a handler listens,
so a raise nobody listens to allocates nothing. The kind's name (`error`, `throw`
or `exit`), the exception's module name (empty when the raised value is not an
exception, as it never is for a throw or an exit), and how many handlers could
take it. Depth zero is an uncaught raise. `stack_bytes` is the bytes of machine
stack between the running quantum's entry and the raise (`Process::stack_base`,
set by `Process::run_quantum` and by the interpreter's drive loop), 0 when no
quantum is running. `write_line` renders the four as `kind`, `exception`,
`handler_depth` and `stack_bytes`. The AOT scheduler keeps the default
no-op hook. See [exceptions](exceptions.md).

## Program Output

Printed bytes are semantic program output, not telemetry. `write_output`
passes the bytes `fz_io_write` was given, unchanged and with no newline added,
through the running process's `ExecCtx.output` hook to an event-scoped `OutputSink`. The CLI sink writes those
bytes to stdout immediately. A retaining test sink copies them during the
callback. `NullOutput` does nothing. No sink constructs an event or stages a
second copy for a later telemetry call.

A warning from `IO.warn` takes the same road through `ExecCtx.warn` to
`OutputSink::warn`, which carries the message, the file (empty for none) and
the line. The default writes `warning: <message>`, and `  <file>:<line>` when
located, to stderr in one write, so the CLI, the AOT binary and a plain sink
report a run-time warning there; `NullOutput` drops it. A macro run installs
`MacroRunOutput`, which keeps each warning for the compiler (see
macro-expansion.md).

Interpreter, JIT, and AOT install the same raw callback boundary. An interpreter
destructor-drain failure is propagated directly; it is not converted into a
telemetry-only warning.

## Program Arguments

`System.argv/0` reads the command line from the running process's `ExecCtx`:
`argv` points at an `Argv`, a list of raw byte strings the driver owns, and
null reads as `[]`. `fz_system_argv` conses a binary per argument, back to
front, and every execution door calls that one helper by symbol.

- JIT: `Compiler2::set_program_args` holds the arguments; `run_root_jit` passes
  them to `Runtime::with_argv`, which copies the pointer onto the context
  `run_until_idle` builds.
- Interpreter: `run_root_interp` passes them to `run_backend_main`, which hands
  them to `drive_backend_until_idle`. Macro execution
  (`run_backend_entry_on_process`) passes `NO_ARGV`, so a macro reads `[]`.
- AOT: the emitted C `main(argc, argv)` passes both to `fz_aot_setup`, which
  copies `argv[1..]` into the `AotScheduler` and points its context at the copy.
  The program name is not an argument, as in Elixir.

`fz2 run|interp <src.fz> args...` gives the program every token after the
source path, verbatim and as bytes (`args_os`). fz2's own options are read only
before the path.

## Observing In Tests

There is one run path — the production scheduler — and tests watch its exit event
instead of poking task internals:

- `ProcessExitCapture` reconstructs a typed `ExitRecord` (result + heap stats +
  per-process counters) from each `process_exited` event's
  live process during dispatch, queryable by `last()` or `by_pid(pid)`.
- `ReuseSiteCapture` collects the run's `reuse_site` events; `retention()` is
  their sum, the figure `Node::retention_stats` reads.
- `DbgCapture` is a retaining `OutputSink` that copies each callback-scoped line,
  read back with `lines()`.

`observe(compiled, entry)` (codegen tests) attaches the exit handler and installs
the output sink, spawns `entry`, drains `run_until_idle`, and returns the root
task's `ExitRecord` plus the dbg lines. The
result/output/heap helpers build on it: `run_main` reads `observe(...).exit.halt_value`,
and `capture_main` reads `observe(...).output`.

`CompiledModule::run(tel, fn_id)` is a sibling convenience: a thin `spawn` +
`run_until_idle` that uses the caller-owned telemetry bus, attaches a
`ProcessExitCapture`, and returns the root pid's `halt_value` from its
`process_exited` record. Both seams read the result from the event, not from
`task.halt_value`.

Tests follow the same ownership rule as compile-time telemetry: the test root
creates the bus, then helpers thread it downward. A helper that allocates its
own runtime bus splits the observation stream and stops the test from seeing the
actual run it asked for.
