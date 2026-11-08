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
queue. So a `Process` carries just two scheduler-facing slots, one of them behind a
lock:

- `runnable: Option<ClosureRef>` — the one re-entry verb. `ClosureRef` wraps a
  non-null pointer to a `(self)`-callable closure, so `Some` always names real
  work; `None` means nothing is queued.
- `delivery: DeliveryLock` — the receive-park snapshot (`WaitState`) and the
  in-queue of gifts, reachable only through the lock (see [Delivery
  lock](#delivery-lock)). A matcher hit takes the park and moves the outcome
  closure into `runnable`.

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

Compiler2's backend interpreter mirrors that idea with its own
`BackendResumeEntry` plus `Vec<BackendContinuation>` state. One quantum runs by
looping over explicit executable/entry transitions for that backend seam,
rather than re-entering through nested helper calls for each delivered resume
or local join.

## fz_resume: the one verb

`fz_resume(cont) -> i64` is a shim in the target's C convention, since the
scheduler holds its address in an `extern "C"` fn pointer. It reads the
closure's code pointer
(via `fz_closure_code_ref`) and tail-calls the body with the single argument
`(self)`. Bound values, loop args, and continuation state already live in the
closure's captures, so the shim signature is fixed regardless of what kind of
closure it resumes. Both the JIT `Runtime` and the AOT run-queue loop resume
every task through this one shim.

## Receive

A `receive` scans its mailbox when it is reached, oldest message first, and only
a miss parks. The park snapshot is a `WaitState` (alias for `ParkRecord`) stored
in `Process.delivery` once a miss must wait. It holds the compiled `matcher_fn`, the pinned `^name` values in
matcher order, one `clause_bodies` closure-template pointer per clause, the
per-clause bound-var counts, and (if there is an `after`) the timeout state.

Receive lowering compiles the clause patterns into one matcher via the pattern
matrix and mints one continuation-template fn per clause body. A bare
`receive do msg -> msg end` is just the degenerate case: its matcher always
matches and binds `msg`.

`fz_receive_park_matched` decides the receive in one step
(`sched::reach_receive`); generated code tail-calls whatever closure it returns,
exactly as `fz_resume` would, and returns the yield sentinel only when it parks.

```text
receive:
  build WaitState (matcher + pinned + clause templates)
  a message matches clause k -> splice it out, return the outcome closure (no yield)
  no match, `after 0`        -> return the after body closure (no yield)
  no match otherwise         -> park = WaitState ; arm the after-timer ; Blocked ; yield
```

A process with a park has therefore already searched its whole mailbox, so
a sender tests only its own message.

When a message matches, `materialize_outcome_closure` turns the winning clause
template into a runnable zero-arg closure. The template env is
`[outer_cont, cap0, …]`; the outcome env splices the matcher's bound values in
after the outer continuation: `[outer_cont, bound0, …, cap0, …]`. A scan hit
returns that closure to the receive that is running. A sender-side hit is
delivered in two halves: the sender runs the matcher (`ParkRecord::try_match`
with the sender as the allocating process, which the matcher uses for allocation
only: a guard's `self()` is a pinned value the receiver took at park time, see
[pattern-matching](pattern-matching.md#receive-guards-run-on-the-sender)), cancels the after-timer and calls
`sched::gift_match`, which copies the bound values with one forwarding map into
a gift on the sender's heap (`sched::gift_copy`: measure, then copy into one
block of the measured size) and queues a `Gift { segment,
payload: GiftPayload::Match { clause_idx, bound_vals } }` on the receiver's
`in_queue`; a miss calls `sched::gift_message`, which gifts the whole message
as a `GiftPayload::Message`. These two functions are the only implementation of
"gift and queue": `sched::probe_sender` (JIT and AOT) and the interpreter's
`probe_parked_receive` differ only in which matcher runs and which record holds
the after-timer. A copy that allocates nothing gifts nothing: `gift_copy` of no
values, or of values that cross as they are (the empty list, a pointer the
sender does not own), measures zero and returns `GiftSegment::empty()` without
opening a window, and grafting it is a no-op. The receiver's dispatch grafts each segment, takes the park record
and materializes the outcome closure (`sched::deliver_in_queue`). The queued
entry is the partial closure: a clause index and gifted bound values, no new
heap object type.

This is outcome-closure delivery, not mailbox delivery. A sender-side hit does
not enqueue the message and does not wake the receiver for a second mailbox
scan. The matcher projects only the winning arm's useful payload, the sender
copies only that projected capture set, and the receiver resumes from an
outcome closure built on its own heap. Mailbox traffic is the miss path only: a
rejected message is gifted whole as `GiftPayload::Message` and joins the
mailbox when the receiver next drains its queue. A sender never writes into a
receiver's heap, and a receiver whose receive is already matched is not probed
again; its later arrivals are misses.

For compiler2-native codegen, that resumed clause body is just another
continuation boundary. The parked outcome closure publishes the bound-value
projection; if the resumed native body then tailcalls a callee whose published
return lane differs from the body's own published return lane, codegen must
insert a compiler-generated boundary adapter closure and pass that adapter as
the callee's continuation. Passing the receiver's outer continuation straight
through would let the callee deliver on the wrong ABI lane and corrupt the
resumed receive path.

The parked template always resumes clause/after bodies through an explicit
continuation closure for the post-`receive` join. There is one receive-join
contract now: outcome code hands the joined value off explicitly instead of
relying on an alternate `outer_cont` mode.

```text
message arrives for a waiting receive and matches clause k:
  outcome = materialize_outcome_closure(clause_bodies[k], bound_vals)
  wait = None ; runnable = outcome
  core.make_runnable(pid, &mut state)   # Blocked -> Ready, queued once
```

The scheduler never passes the message to the closure. The message is already
consumed and its useful parts captured. Two entry points drive this:
`reach_receive` walks the mailbox in arrival order when the receive is reached
(rejected messages stay in the mailbox — Erlang save-queue semantics), and
`probe_sender(sender, receiver, msg)` runs the matcher on `send` arrival for a
process that is already waiting and bypasses the mailbox entirely on a hit. The
JIT `Runtime` and the AOT scheduler deliver every send through `probe_sender`;
the interpreter runs the same shape with its own matcher
(`IrInterpRuntime::probe_parked_receive`). Every path drains the receiver's
`in_queue` as the first act of a dispatch, before the runnable closure or resume
entry is taken: `deliver_in_queue` in `run_until_idle` (JIT) and
`dispatch_quantum` (AOT), `IrInterpRuntime::deliver_in_queue` in
`drive_backend_until_idle`. A receiver that exits with gifts still queued drops
them with its `Process`; each un-grafted segment returns its blocks to the pool.

## Delivery lock

A send and a receive contest three things: the park record, the in-queue and
the walk of the mailbox that decides whether the receive parks at all. They
live in one `Delivery` (`runtime/src/delivery.rs`) behind one `std::sync::Mutex`
in `Process.delivery`, and a `&mut Delivery` can only come from the guard. The
mailbox stays outside the lock: only the owning process touches it, and only
after a drain. Each critical section holds the lock from its first read to its
last write:

- `sched::reach_receive` holds it across the mailbox walk and the park install.
  If the walk and the install were separate sections, a delivery between the
  end of the walk and the install would find no park to probe while the walk
  had already passed the mailbox, and nobody would probe the message. Under the
  lock the delivery waits for the install and is then probed against the park.
  A hit or an `after 0` miss returns without installing a park.
- `sched::probe_sender` (and the interpreter's `probe_parked_receive`, whose
  caller takes the lock) holds it across reading the park, checking for a
  pending match, running the matcher on the sender, queueing the gift and
  cancelling the after-timer. The first hit decides the receive. A later sender
  finds the match queued (`Delivery::undecided_park` is `None`) and gifts a
  plain miss without running the matcher.
- `sched::fire_after_timer` (and the interpreter's `wake_receive_after`) takes
  the park under the same lock, so a timer and a hit win or lose the same way:
  the loser finds no park, or a park whose timer id is not its own. The
  stale-timer check in each scheduler's `wake_expired` is the fallback for a
  timer that fires after the hit cancelled it.
- `sched::drain_in_queue` takes entries under the lock, and `deliver_in_queue`
  keeps it through taking the park for a matched receive.

The matcher a sender runs executes with the receiver's lock held, so a guard
that tried to deliver to the same receiver would deadlock; matchers never send.
The interpreter keeps its own park record in `IrInterpRuntime.backend_parked`
rather than in `Delivery`; its probe, timer and delivery paths still take the
receiver's lock for the pending-match decision and the in-queue.

`delivery` is declared before `heap` in `Process`, so a process dropped with
gifts still queued drops them first: each `GiftSegment` returns its block to
the pool (or the allocator, for an exact block) and releases its stubs. A receiver left parked
when the run ends is torn down this way, and `fz.runtime.run_ended` reports that
the pool got every block back ([runtime telemetry](runtime-telemetry.md)). With
one worker the lock is never contended.

## Timeout

An `after` clause is a second closure to run if the timer wins. Receive lowering
mints the after-clause body alongside the message-clause bodies, and the after
body closure (`after_cont`) is stored on the `WaitState`.

```text
receive ... after 500 -> :timeout:
  WaitState.after_cont       = after-body closure
  scheduling core schedule_timer(pid, 500ms) -> TimerId
  WaitState.after_timer_id   = TimerId
  state = Blocked
```

The timer wheel entry holds only `(id, deadline, pid)` — not the closure. When it
fires, `fire_after_timer` checks the parked task still holds that exact timer id,
then moves `after_cont` into `runnable`; the scheduler makes the task runnable
through its core. If a message matches first, the matcher-hit path cancels the
timer via `timer_cancel` and schedules the matched outcome instead. Either way
the runnable result has the same shape: `runnable()`.

## The Scheduling Core

`SchedulingCore` (`runtime/src/sched_core.rs`) owns the run queue and the timer
wheel. The JIT `Runtime`, the AOT `AotScheduler`, and the interpreter's
`BackendSchedulerAdapter` each hold one and implement `Scheduler`: `core()`
exposes it, `wake_expired(pid, timer)` says how an expired timer wakes that
path's process (`fire_after_timer` for JIT and AOT; the interpreter queues the
parked receive's `after` entry), and `about_to_sleep(wait)` observes a sleep.

`SchedulingCore::make_runnable(pid, &mut state)` is the one way a process
becomes Ready. It takes the process's state word, moves New, Running or Blocked
to Ready and pushes the pid once, and returns whether this call made the process
runnable; a process that is already Ready is in the queue and is not pushed
again, and an Exited one never runs. Spawn, send, yield and timer wakes on all
three paths go through it, so `Ready` and "in the run queue" are the same fact.
`probe_sender` and `fire_after_timer` only report their decision; the caller
hands it to the core.

`next_runnable` is the single loop and the single definition of idle:

```text
loop:
  wake every process whose timer expired (each scheduler makes the woken
                                          ones runnable through its core)
  if a process is runnable: return it
  if a timer is pending:   about_to_sleep(wait); sleep until its deadline
  else:                    return None   # idle
```

A program is idle only when nothing is runnable and no timer is pending. The
JIT's `run_until_idle`, `aot_run_queue_loop` and the interpreter's
`drive_backend_until_idle` all loop on it. `timer_schedule_hook::<S>()` and
`timer_cancel_hook::<S>()` give the one pair of `ExecCtx` timer hooks,
instantiated per scheduler type.

The interpreter arms a timer for a receive with a positive timeout through the
same `ExecCtx` hooks and records its id on the `BackendParkRecord`; a matching
send cancels it, and an expired one queues the receive's `after` entry. The
interpreter's macro path (`keepalive_pid`) leaves its finished process Blocked
(off the queue, holding no timer) until the next entry queues it, so the core
reports idle once only that process remains.

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
  heap (`spawn_closure`; the spawn paths are the only remaining callers of
  `deep_copy_any_value_ref` that write another process's heap, and the child
  has not run yet); or
- a synthetic main-style entry. A `main` function has a raw `(cont)` body, so
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
- `cargo test --test fixture_matrix a_send_probes_on_the_sender_and_gifts_its_result_through_the_receivers_in_queue`
  — fixtures 00695 and 00696 on the `run` and `interp` paths: a miss gifts the
  whole message in one block (800032 bytes for the 50000-element log), a hit gifts exactly the bound cells (48 bytes for `[1, 2, 3]`),
  the receiver is woken once, and its own heap allocates no list cells for the
  delivery.
- `runtime/src/sched_test.rs` — the probe, drain and delivery primitives: a hit
  leaves the receiver's heap untouched until it runs, two bindings of one cell
  copy it once, a second sender does not re-probe a matched receive, a dropped
  receiver returns its queued gifts to the pool and releases their binaries. The
  lock scope is pinned there too: a hit and a timer decide one park once in
  either order, a sender's matcher runs with the receiver's lock held, and a
  delivery cannot take the lock during the receive-entry walk and is probed
  against the installed park afterwards.
- `cargo test --test fixture_matrix a_receiver_left_parked_with_queued_gifts_drops_them_at_teardown`
  — fixture 00697: three messages gifted to a receiver that stays parked, on
  `run` and `interp`, each one block of exactly its measured bytes; the run ends with them still queued and `run_ended` shows
  the pool's outstanding count back at its starting value. The fixture runs on
  all three paths for output parity.
- `cargo test --test fixture_matrix spawn_with_captures` — a spawned task is
  resumed as an entry thunk through `fz_resume`, the same verb a continuation
  uses.
- `reduction_budget_resets_and_spends` / `reset_reduction_budget_clears_yield_reasons`
  (`runtime/src/process_test.rs`) — budget reset/spend and yield-reason clearing.
- `coexistence` (`src/ir_interp/tests/coexistence.rs`) — two interpreters run on
  one thread without clobbering each other, proving no ambient current-process.
