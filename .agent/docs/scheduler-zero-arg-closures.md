# Scheduler Re-entry Is Zero-arg Closures

## Model

The scheduler does not need to understand why a process stopped. It needs one
thing: a closure it can run.

```text
scheduler runs process
process stops and leaves a closure behind
scheduler later calls closure()
process continues
```

The closure captures everything needed to continue. The scheduler passes no
message, timeout value, loop argument, continuation pointer, or resume token —
all of that is captured into the closure before the process goes back on the run
queue. So a `Process` carries just two scheduler-facing slots:

- `runnable: Option<ClosureRef>` — the one re-entry verb. `ClosureRef` wraps a
  non-null pointer to a `(self)`-callable closure, so `Some` always names real
  work; `None` means nothing is queued.
- `wait: Option<Box<WaitState>>` — the receive-park snapshot. A matcher hit
  clears `wait` and moves the outcome closure into `runnable`.

`Process.state` (`ProcessState`: `New`, `Ready`, `Running`, `Blocked`, `Exited`)
names which case the process is in:

```text
Runnable (Ready) = a zero-arg closure sits in `runnable`
Blocked          = waiting for something that may later produce that closure
Exited           = no closure remains; `halt_value` is final
```

That gives one re-entry rule and one GC rule. In the JIT and AOT schedulers every
resume is `runnable()`, run through the single `fz_resume` shim. The runnable
closure is the primary GC root: if a process can resume after a scheduler
boundary, its live continuation state is reachable from that closure. The
boundary's GC (`gc_process_roots`) copies the closure, copies everything it
reaches, rewrites the root pointer in place to the to-space copy, and the
scheduler resumes the moved closure.

The interpreter is a parallel scheduler with the same shape but its own state. It
keeps re-entry as a `ResumeEntry` tuple (`FnId`, args, `SpecKey`,
`Vec<InterpContinuation>`) in a `resume` HashMap, driven by `pop_runnable` /
`take_resume`, and uses its own `ParkRecord` (`src/ir_interp/scheduler.rs`); it
never touches `Process.runnable` or `fz_resume`. The runnable/`fz_resume` model
below is the compiled-path model.

## fz_resume: the one verb

`fz_resume(cont) -> i64` is a SystemV shim. It reads the closure's code pointer
(via `fz_closure_code_ref`) and tail-calls the body with the single argument
`(self)`. Bound values, loop args, and continuation state already live in the
closure's captures, so the shim signature is fixed regardless of what kind of
closure it resumes. Both the JIT `Runtime` and the AOT run-queue loop resume
every task through this one shim.

## Receive

When a process executes `receive`, it parks because there is no runnable work
yet. The park snapshot is a `WaitState` (alias for `ParkRecord`) stored in
`Process.wait`. It holds the compiled `matcher_fn`, the pinned `^name` values in
matcher order, one `clause_bodies` closure-template pointer per clause, the
per-clause bound-var counts, and (if there is an `after`) the timeout state.

Receive lowering compiles the clause patterns into one matcher via the pattern
matrix and mints one continuation-template fn per clause body. A bare
`receive do msg -> msg end` is just the degenerate case: its matcher always
matches and binds `msg`.

```text
receive:
  build WaitState (matcher + pinned + clause templates)
  mailbox empty -> Blocked ; else Ready (scheduler runs an initial scan)
```

When a message matches, `materialize_outcome_closure` turns the winning clause
template into a runnable zero-arg closure. The template env is
`[outer_cont, cap0, …]`; the outcome env splices the matcher's bound values in
after the outer continuation: `[outer_cont, bound0, …, cap0, …]`. The matcher hit
then clears `wait`, cancels any after-timer, and moves the outcome closure into
`runnable`.

```text
message matches clause k:
  outcome = materialize_outcome_closure(clause_bodies[k], bound_vals)
  wait = None ; runnable = outcome ; state = Ready
  enqueue process
```

The scheduler never passes the message to the closure. The message is already
consumed and its useful parts captured. Two entry points drive this: `probe_sender`
runs the matcher on `send` arrival, and `initial_scan` walks the mailbox in
arrival order when a parked task wakes Ready with messages already queued
(rejected messages stay in the mailbox — Erlang save-queue semantics).

## Timeout

An `after` clause is a second closure to run if the timer wins. Receive lowering
mints the after-clause body alongside the message-clause bodies, and the after
body closure (`after_cont`) is stored on the `WaitState`.

```text
receive ... after 500 -> :timeout:
  WaitState.after_cont       = after-body closure
  timer wheel schedule(pid, 500ms) -> TimerId
  WaitState.after_timer_id   = TimerId
  state = Blocked
```

The timer wheel entry holds only `(id, deadline, pid)` — not the closure. When it
fires, `fire_after_timer` checks the parked task still holds that exact timer id,
then moves `after_cont` into `runnable` and flips Ready. If a message matches
first, the matcher-hit path cancels the timer via `timer_cancel` and schedules
the matched outcome instead. Either way the runnable result has the same shape:
`runnable()`.

## Mid-flight Reduction Yield

A back-edge yield is not a different shape. The process is mid-loop, and the live
state is the next loop iteration plus the current continuation. The compiled back
edge spends one reduction and yields when the budget is gone:

```text
reductions_remaining -= 1
if reductions_remaining <= 0:
  k = closure capturing the loop roots (last root materialized via materialize_cont)
  fz_yield_mid_flight_report(k, remaining, YIELD_REASON_REDUCTIONS)
  return YIELD_PTR
else:
  tail_call loop(next_loop_args)
```

`fz_yield_mid_flight_report` stores `k` into `runnable` (`set_runnable_closure`),
banks the burned reductions, and returns the `YIELD_PTR` sentinel so the trampoline
hands control back to the scheduler. `k` is then the primary GC root, forwarded to
its to-space copy at the boundary if GC runs, and restart is `k()`.

Synchronous native calls do not build this closure eagerly. They carry
compiler-known continuation state as a stack-backed lazy descriptor and
materialize it only on the exhausted-budget branch (`materialize_cont` on the last
root above) — the budget mechanism is in [`reduction-yielding`](reduction-yielding.md).

## Spawn: a fresh task is still just a closure

A fresh task has no continuation yet, so spawn builds one. Its `runnable` is an
**entry thunk**: a one-capture closure whose code is `fz_entry_thunk` and whose
capture[0] is the task's *inner* closure (`mint_entry_thunk`). On first resume the
thunk reads the inner closure, picks the halt continuation matching the inner
closure's `halt_kind`, and tail-calls the inner body `(inner, halt_cl)`.

The inner closure is one of two things:

- a spawned user closure, deep-copied from the sender's heap into the new task's
  heap (`spawn_closure`); or
- a synthetic main-style entry. A `main` fn has a raw `(cont)` body, so
  `mint_main_inner` wraps the raw fn pointer in a raw-int capture (GC never treats
  it as a heap reference) behind the fixed `fz_main_trampoline` body, which reads
  the pointer and tail-calls `main(cont)`. The inner closure's `halt_kind` is set
  from the entry fn's computed halt seam, the same way on the JIT spawn path and
  the AOT `fz_aot_run_main` path.

Either way the spawned task's `runnable` is a closure, resumed through `fz_resume`
exactly like a continuation. The entry thunk and inner are scheduler scaffolding
prepared before the task runs, so spawn resets the heap's alloc stats afterward —
alloc telemetry then measures only the task's own execution.

## Halt continuations

When a resumed body finishes, it calls a halt continuation that records the final
value into the process. These are per-process singletons in
`halt_cont_singletons: [*mut u8; 4]`, indexed by return repr kind: `0=ValueRef`,
`1=RawInt`, `2=RawF64`, `3=RawAtom`. Each slot is a closure whose code pointer is
the matching `fz_halt_cont_body_*` Cranelift body. The JIT pre-populates them at
process construction; under AOT a slot may be null at first use, so
`fz_get_halt_cont(process, body_addr, kind)` lazily allocates it. The closure
header packs `halt_kind` into its flags (low 14 bits = capture count, high 2 bits =
halt kind), which is how `fz_entry_thunk` selects the right halt continuation for
the inner body.

The singleton buffers are off-heap (`static_closure_bufs`), so the per-process GC
arena does not own them and they live for the process's lifetime.

## What the scheduler owns vs. what closures carry

The scheduler's entire vocabulary:

```text
enqueue runnable closure
block on wait state
run closure (fz_resume)
exit process
```

Everything else — message matching, timeout firing, loop-root capture, spawn
setup — belongs to compiler-generated closure construction or to runtime event
handlers that produce a closure. There is no separate "pending resume" vs.
"parked continuation" concept and no side-band argument slab: a resume never
passes arguments into a helper, because the closure already carries its own state.
The roots the boundary GC traces are exactly the `runnable` closure and the
`mailbox`; the process `heap` is the arena being collected, not a root.

## Proof Gates

- `cargo test --test fixture_matrix enum_reduce_suspend` — a runtime-value suspend
  (`Enumerable.reduce` returning `{:suspended, acc, fn () -> … end}`) stays a real
  heap closure across all four paths, never optimized away. Native JIT/AOT pin
  `closure_allocs = 1` (`closure_bytes = 48`, `scalar_box_allocs = 1`); interpreter
  and REPL pin `closure_allocs = 2`.
- `cargo test --test fixture_matrix receive_selective_refs` — selective receive
  with `^`-pinned matchers and an `after` timeout resumes through the closure entry
  across all four paths.
- `cargo test --test fixture_matrix spawn` — selects `spawn2_basic` and
  `spawn_with_captures`: a spawned task resumed as an entry thunk through
  `fz_resume`, the same verb a continuation uses.
- `reduction_budget_resets_and_spends` / `reset_reduction_budget_clears_yield_reasons`
  (`runtime/src/process_test.rs`) — budget reset/spend and yield-reason clearing.
- `coexistence` (`src/ir_interp/tests/coexistence.rs`) — two interpreters run on
  one thread without clobbering each other, proving no ambient current-process.
