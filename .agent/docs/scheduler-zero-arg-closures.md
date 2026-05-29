# Scheduler Re-entry Is Zero-arg Closures

## Model

When a process stops running, the scheduler does not need to understand why. It
needs to know one thing:

```text
Do I have a closure I can run?
```

If yes, the process is runnable. Restarting it means calling that closure with no
scheduler-visible arguments.

```text
scheduler runs process
process stops and leaves a closure behind
scheduler later calls closure()
process continues
```

The closure captures everything needed to continue. The scheduler does not pass a
message, a timeout value, loop arguments, a continuation pointer, or a hidden
resume token. Those are all captured before the process is placed back on the run
queue.

## Core Invariant

Every re-entry path has the same shape from the scheduler's point of view:

```text
Runnable = zero-arg closure
Blocked  = waiting for something that may later produce a zero-arg closure
Exited   = no closure remains
```

`Process.state` (`ProcessState`: `New`, `Ready`, `Running`, `Blocked`, `Exited`)
names which case the process is in. That gives one re-entry rule and one GC rule:

```text
All scheduler re-entry is closure()
The runnable closure is the primary root.
```

If a process can be resumed after a scheduler boundary, its live continuation
state is reachable from that closure. GC copies the closure, copies everything it
reaches, rewrites the root pointer, and the scheduler runs the moved closure.

## Receive

When a process executes `receive`, it parks because there is no runnable work yet.

```text
receive:
  build waiting state
  process becomes Blocked
```

The waiting state is a `ParkRecord` in `Process.parked_matched`. Plain `receive()`
installs an accept-any matcher; selective receive installs its compiled matcher.
When a message later matches, the matcher materializes a zero-arg outcome closure.
Bound pattern values and any original continuation state are captures.

```text
message matches:
  outcome = closure captures(bound_values, continuation_state)
  process.runnable_closure = outcome
  enqueue process
```

The scheduler does not pass the message to the closure. The message is already
consumed and its useful parts captured.

## Timeout

An `after` timeout is also a closure to run if the timer wins. `receive` lowering
mints the after-clause body alongside the message-clause bodies.

```text
receive after 500:
  timeout_closure = closure captures(after_body_state)
  register timer(pid, deadline, timeout_closure)
  process becomes Blocked
```

If the timer ticks first, `runnable_closure` becomes the timeout closure and the
process is enqueued. If a message matches first, the scheduler cancels the timer
and schedules the matched outcome closure instead. Either way the runnable result
is the same shape: `closure()`.

## Mid-flight Reduction Yield

A back-edge yield is not different. The process is mid-loop, and the live state is
the next loop iteration plus the current continuation. The slow path builds a
continuation closure instead of spilling raw words into process fields:

```text
reductions_remaining -= back_edge_cost
if reductions_remaining <= 0:
  k = closure captures(next_loop_args, continuation_state)
  yield_mid_flight(k)
  return YIELD_PTR
else:
  tail_call loop(next_loop_args)
```

The scheduler treats `k` as the primary root. If boundary maintenance decides the
process needs GC, `k` is forwarded to its to-space copy before restart. Restarting
is `k()`.

Synchronous native calls do not build this closure early. They carry
compiler-known continuation state as a stack-backed lazy descriptor and
materialize it only if the exhausted-budget branch is taken. See
[`lazy-continuation-materialization`](lazy-continuation-materialization.md) and
the budget mechanism in [`reduction-yielding`](reduction-yielding.md).

Destination-passing values add no scheduler side channel. A tuple, list, or map
destination live at a yield boundary is held in the ordinary continuation state
captured by `k`, so GC sees it through the same typed capture path as any other
heap value. Init tokens are compile-time proof only; they are never stored in the
closure. See [`destination-passing`](destination-passing.md).

## Process Fields

`Process` carries the runnable work and the per-path entry pointers directly:

- `runnable_closure: *mut u8` — the general scheduler-runnable zero-arg closure.
  The scheduler calls it to continue the process.
- `parked_matched: Option<Box<ParkRecord>>` — the receive park snapshot; a match
  materializes `runnable_closure`.
- `pending_closure_entry` / `pending_main_entry` — a pending spawned-closure or
  main-style entry. `run_quantum` dispatches them through the `fz_spawn_entry` /
  `fz_main_entry` SystemV→Tail-CC shims, then clears them.
- `halt_cont_singletons: [*mut u8; 3]` — per-repr halt continuations indexed by
  return kind (`ValueRef`, `RawInt`, `RawF64`).
- `mailbox` and `heap` — process-owned persistent storage, traced as process roots
  until that state becomes heap-owned.

Each of these resolves to the same scheduler action: call a zero-arg closure, or
dispatch a pending entry through its shim. The continuation always carries its own
state; the scheduler passes no arguments into it.

## Shapes The Scheduler Does Not Carry

The mid-flight argument-slab machinery does not exist. There is no:

- mid-flight raw roots slab
- mid-flight side-band root tags slab
- mid-flight root count
- mid-flight resume function pointer
- per-ABI mid-flight resume shim
- fixed eight-argument mid-flight limit
- scheduler path that passes arguments into a resume helper
- separate scheduler concept for "pending resume" versus "parked continuation"

The scheduler has these verbs:

```text
enqueue runnable closure
block on wait state
run closure
exit process
```

Everything else belongs to compiler-generated closure construction or to runtime
event handling that produces a closure.

## Proof Gates

- `cargo test --test fixture_matrix enum_reduce_suspend` — a mid-flight suspend
  materializes a real heap closure; native CLIF references neither
  `fz_mid_flight_roots_ptr` nor `fz_mid_flight_root_tags_ptr` (those symbols do
  not exist).
- `cargo test --test fixture_matrix receive_selective_refs` — selective receive
  with an `after` timeout resumes through the closure entry across interpreter,
  JIT, AOT, and REPL.
- `cargo test --test fixture_matrix spawn` — spawn entry (`spawn2_basic`,
  `spawn_with_captures`) dispatched as a pending closure.
- `cargo test reduction_budget` (`runtime/src/process.rs`:
  `reduction_budget_resets_and_spends`,
  `reset_reduction_budget_clears_yield_reasons`) — budget reset/spend and
  yield-reason clearing.
- `cargo test coexistence` (`src/ir_interp/tests/coexistence.rs`) — two
  interpreters run on one thread without clobbering each other.
