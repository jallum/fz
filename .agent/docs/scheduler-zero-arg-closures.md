# Scheduler Re-entry Is Zero-arg Closures

## Model

When a process stops running, the scheduler should not need to understand why.
It should only need to know one thing:

```text
Do I have a closure I can run?
```

If yes, the process is runnable. Restarting the process means calling that
closure with no scheduler-visible arguments.

```text
scheduler runs process
process stops and leaves a closure behind
scheduler later calls closure()
process continues
```

The closure captures everything needed to continue. The scheduler does not pass
a message, a timeout value, loop arguments, a continuation pointer, or a hidden
resume token. Those are all captured before the process is placed back on the
run queue.

## Core Invariant

From the scheduler's point of view, every re-entry path has the same shape:

```text
Runnable = zero-arg closure
Blocked  = waiting for something that may later produce a zero-arg closure
Exited   = no closure remains
```

That gives us one rule:

```text
All scheduler re-entry is closure()
```

And one GC rule:

```text
The runnable closure is the primary root.
```

If the process can be resumed after a scheduler boundary, the live continuation
state must be reachable from that closure. The GC copies the closure, copies
everything the closure can reach, rewrites the root pointer, and the scheduler
runs the moved closure.

## Why This Is Better

The old model makes each suspension kind special:

```text
receive park        -> parked_cont plus resume_park(msg, kind, cont)
selective receive   -> pending_resume_matched
timeout             -> after-cont special path
mid-flight GC yield -> fn pointer plus roots slab plus tags slab
spawn/main entry    -> pending entry pointer fields
```

Those are different scheduler words for the same idea: "here is the next thing
to run."

The closure model removes that distinction:

```text
receive park        -> later produces closure()
selective receive   -> later produces closure()
timeout             -> later produces closure()
mid-flight GC yield -> immediately produces closure()
spawn/main entry    -> initially produces closure()
```

The scheduler does not need arity-specific resume shims. It does not need to
know whether the closure came from a matched message, an after timeout, a
back-edge yield, or process startup.

## Receive

When a process executes `receive`, it parks because there is no runnable work
yet.

```text
receive:
  build waiting state
  process becomes Blocked
```

When a message later matches, the matcher materializes a zero-arg outcome
closure. Bound pattern values and any original continuation state are captures.

```text
message matches:
  outcome = closure captures(bound_values, continuation_state)
  process.runnable = outcome
  enqueue process
```

The scheduler does not pass the message to the closure. The message has already
been consumed and its useful parts have been captured.

## Timeout

An `after` timeout is also just a closure to run if the timer wins.

```text
receive after 500:
  timeout_closure = closure captures(after_body_state)
  register timer(pid, deadline, timeout_closure)
  process becomes Blocked
```

If the timer ticks first:

```text
timer fires:
  process.runnable = timeout_closure
  enqueue process
```

If a message matches first, the scheduler cancels the timer and schedules the
matched outcome closure instead.

Either way, the runnable result is the same shape:

```text
closure()
```

## Mid-flight GC Yield

A back-edge yield is not different. The process is in the middle of a loop, and
the live state is the next loop iteration plus the current continuation.

Instead of spilling raw words and side-band tags into process fields, the slow
path builds a continuation closure:

```text
if should_yield:
  k = closure captures(next_loop_args, continuation_state)
  yield_mid_flight(k)
  return YIELD_PTR
else:
  tail_call loop(next_loop_args)
```

The scheduler runs GC with `k` as the primary root. After GC, `k` points at the
to-space copy. Restarting the process is just:

```text
k()
```

No roots slab. No root tags slab. No artificial fixed argument limit. No
per-ABI resume shim to reload spilled arguments.

Destination-passing values do not add a scheduler side channel. If a tuple,
list, or map destination is live at a yield boundary, it must be held in the
ordinary continuation state captured by `k`. The GC then sees the destination
through the same typed closure/frame capture path as any other heap value. Init
tokens are compile-time proof only; they are not scheduler state and are never
stored in the closure.

## Process Shape

The long-term process state should separate runnable work from blocked waiting
state:

```rust
pub struct Process {
    pub runnable: Option<ClosureRef>,
    pub wait: Option<WaitState>,
    pub mailbox: Mailbox,
    pub heap: Heap,
}
```

`runnable` means the scheduler can call `closure()`.

`wait` means the process is blocked until some external event, message match, or
timer produces a runnable closure.

Mailbox and other process-owned persistent storage still need to be traced as
process roots until they become heap-owned state. The runnable closure replaces
mid-flight argument slabs; it does not magically make out-of-closure process
containers disappear.

## What This Model Keeps Out

These shapes are not part of the scheduler under this model:

- mid-flight raw roots slab
- mid-flight side-band root tags slab
- mid-flight root count
- mid-flight resume function pointer
- per-ABI mid-flight resume shims
- fixed eight-argument mid-flight limit
- scheduler paths that pass arguments into resume helpers
- separate scheduler concepts for "pending resume" vs "parked continuation"

The scheduler has these verbs and no more:

```text
enqueue runnable closure
block on wait state
run closure
exit process
```

Everything else belongs either in compiler-generated closure construction or in
runtime event handling that produces a closure.

## Acceptance Test Shape

A good implementation should prove these properties:

- A receive resume runs through the same zero-arg closure entry as a timeout.
- A mid-flight GC yield roots the continuation closure and resumes from the
  moved closure after collection.
- Message-bound values are captured before scheduling; the scheduler does not
  pass message args.
- Timeout bodies are stored as closures at timer registration time.
- No generated CLIF calls `fz_mid_flight_roots_ptr`,
  `fz_mid_flight_root_tags_ptr`, or a mid-flight resume shim.
- The scheduler has one runnable closure dispatch path.
