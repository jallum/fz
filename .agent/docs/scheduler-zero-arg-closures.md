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
closure is a GC root: if a process can resume after a scheduler boundary, its
live continuation state is reachable from that closure. The boundary's GC
(`Process::collect`) lists the closure among the process's roots, copies it and
everything it reaches, rewrites `runnable` to the to-space copy, and the
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
in `Process.delivery` once a miss must wait. It holds the receive's `site`, the
arrival's `frame`, and (if there is an `after`) the timeout state.

The site (`ReceiveSite`) is what the compiler knows about the receive: the
matcher, the `after` body's code, the pinned-value count, and each clause's
code and bound-value count. Codegen emits it once per receive as read-only
data. The frame is one closure built each time the receive is reached,
`[outer_cont, captures..., pinned...]`, and is never called. A receive of any
number of clauses builds one frame.

Receive lowering compiles the clause patterns into one matcher via the pattern
matrix and mints one continuation fn per clause body. A bare
`receive do msg -> msg end` is just the degenerate case: its matcher always
matches and binds `msg`.

`fz_receive_park_matched` decides the receive in one step
(`sched::reach_receive`); generated code tail-calls whatever closure it returns,
exactly as `fz_resume` would, and returns the yield sentinel only when it parks.

```text
receive:
  build the frame ; WaitState = (site, frame)
  a message matches clause k -> splice it out, return the outcome closure (no yield)
  no match, `after 0`        -> build and return the after body closure (no yield)
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

The parked frame always resumes clause/after bodies through an explicit
continuation closure for the post-`receive` join. There is one receive-join
contract now: outcome code hands the joined value off explicitly instead of
relying on an alternate `outer_cont` mode.

```text
message arrives for a waiting receive and matches clause k:
  outcome = wait.outcome_closure(k, bound_vals)   # clause k's code over [outer_cont, bound..., captures...]
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
them with its `Process`; each un-grafted segment returns its block to the pool.

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
the pool (a table-sized block) or the allocator (an exact block) and releases its stubs. A receiver left parked
when the run ends is torn down this way, and `fz.runtime.run_ended` reports that
the pool got every block back ([runtime telemetry](runtime-telemetry.md)). With
one worker the lock is never contended.

## Timeout

An `after` clause is a second closure to run if the timer wins. Receive lowering
mints the after-clause body alongside the message-clause bodies, and the site
records its code. The after closure is built from the frame when the timer wins.

```text
receive ... after 500 -> :timeout:
  scheduling core schedule_timer(pid, 500ms) -> TimerId
  WaitState.after_timer_id   = TimerId
  state = Blocked
```

The timer wheel entry holds only `(id, deadline, pid)` — not the closure. When it
fires, `fire_after_timer` checks the parked task still holds that exact timer id,
then builds the after closure from the frame into `runnable`; the scheduler makes the task runnable
through its core. If a message matches first, the matcher-hit path cancels the
timer via `timer_cancel` and schedules the matched outcome instead. Either way
the runnable result has the same shape: `runnable()`.

## The Scheduling Core

`SchedulingCore` (`runtime/src/sched_core.rs`) owns the run queue and the timer
wheel. The JIT `Runtime`, the AOT `AotScheduler`, and the interpreter's
`BackendSchedulerAdapter` each hold one and implement `Scheduler`: `core()`
exposes it, `wake_expired(pid, timer)` says how an expired timer wakes that
path's process (`fire_after_timer` for JIT and AOT; the interpreter queues the
parked receive's `after` entry), `observe(event)` receives every runtime event the core reports (see
[runtime telemetry](runtime-telemetry.md)), and
`run_destructor(process, closure, payload)` runs one resource destructor closure
as fz code (see [`end_quantum`](#the-step-after-a-quantum)).

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
  if a timer is pending:   read the clock and wake every process whose timer expired
                           (observe(TimerFired) for each, then each scheduler makes
                           the woken one runnable through its core)
  if a process is runnable: return it
  if a timer is pending:   observe(SchedulerSlept(wait)); wait on the clock until its deadline
  else:                    return None   # idle
```

The clock is read only when a timer is pending, so a program that arms no
timer never asks the time.

A program is idle only when nothing is runnable and no timer is pending. The
JIT's `run_until_idle`, `aot_run_queue_loop` and the interpreter's
`drive_backend_until_idle` all loop on it. The core also records the program's
end (`halt`, `process_ended`), after which `next_runnable` returns `None`
whatever is still runnable. `halt_hook::<S>()` is the `ExecCtx::halt` hook. `timer_schedule_hook::<S>()` and
`timer_cancel_hook::<S>()` give the one pair of `ExecCtx` timer hooks,
instantiated per scheduler type.

The interpreter arms a timer for a receive with a positive timeout through the
same `ExecCtx` hooks and records its id on the `BackendParkRecord`; a matching
send cancels it, and an expired one queues the receive's `after` entry. The
interpreter's macro path (`keepalive_pid`) leaves its finished process Blocked
(off the queue, holding no timer) until the next entry queues it, so the core
reports idle once only that process remains.


### The step after a quantum

`sched_core::end_quantum(scheduler, process)` is the one step that follows every
quantum on the JIT and AOT paths, in every state. It reads how the quantum ended off the
process (`Process::quantum_end`, a `Disposition`: runnable means `Requeue`, `Blocked`
means `Parked`, anything else means `Exited`), collects when `Heap::should_gc` holds and the
process did not exit, clears the quantum's yield reasons, and, for a halted process,
marks it `Exited` without collecting it and releases every object on its off-heap chain
with `Heap::release_resources_at_exit`, since nothing is live. Nothing a
collection would forward is read after the exit, so the heap is released as it
stands. BinRefs and Resource stubs share one chain per generation (`off_heap_head`,
`off_heap_old_head`), told apart by the kind tag of each link. The sweep (`off_heap::sweep`) decides each stub, once, the same way
after a collection and at exit: a survivor is relinked, a dead BinRef releases
its SharedBin, and a dead Resource whose last reference this was queues
`(destructor, payload)` on `heap.pending_dtors`: the destructor is the literal
closure word the `Resource` holds, outside every heap, and the payload is the
raw `u64`, so the queue holds no heap word and nothing is forwarded for it.
`GcStats::stub_visits` counts the chain links the one sweep followed; it is not
published on `fz.runtime.gc`.

`end_quantum` then drains `pending_dtors` oldest first, boxing each payload as
an integer on the process heap just before calling
`Scheduler::run_destructor` for each and counting it in
`Process::dtors_dispatched`. A destructor runs to completion under a fresh
reduction budget; one that yielded would overwrite the process's own
continuation and is a fault. The JIT enters `fz_drain_dtor_entry` through
`pinned_abi::call2`, the AOT scheduler does the same through the address
`fz_aot_set_drain_dtor_entry` registered, and the interpreter interprets the
closure. It returns the `Disposition` (`Requeue`, `Parked`, `Exited`) the driver acts on,
and reports what it did through `Scheduler::observe`: the `Collection` it
performed, right after collecting and before any destructor runs, and the
exited process, after its destructors have run so `dtors_dispatched` counts the
ones the exit dispatched. The interpreter calls it too, after a park or an exit; it
never yields. A parked receive's environment and continuations live in the
interpreter, so `Scheduler::collect_heap` (default: `Process::collect` with no
transient roots) is overridden to pass their heap refs as the transient roots
and write the forwarded refs back. A process a caller lends the interpreter
(`run_backend_entry_on_process`) ends without `end_quantum`: its caller holds
refs into its heap, so it is neither collected nor swept.

## Mid-flight Reduction Yield

A back-edge yield is not a different shape. The process is mid-loop, and the live
state is the next loop iteration plus the current continuation. The compiled back
edge spends one reduction and yields when the budget is gone:

```text
reductions_remaining -= 1
if reductions_remaining <= 0:
  k = closure capturing the loop roots
  fz_yield_mid_flight_report(k, remaining, YIELD_REASON_REDUCTIONS)
  return YIELD_PTR
else:
  tail_call loop(next_loop_args)
```

`fz_yield_mid_flight_report` stores `k` into `runnable` (`set_runnable_closure`),
banks the burned reductions, and returns the `YIELD_PTR` sentinel so the trampoline
hands control back to the scheduler. `k` is then a GC root, forwarded to its
to-space copy at the boundary if GC runs, and restart is `k()`.

The budget mechanism is in [`reduction-yielding`](reduction-yielding.md). The
yield closure is built only on the exhausted-budget branch; the continuation a
non-tail call leaves behind is built every time, as described next.

## A continuation is a heap object built and read by inline code

Every continuation a non-tail call leaves behind (`Term::Call`,
`Term::CallClosure`, and the `NativeEntryAbi::Continuation` delivery) is a
one-argument closure on the process heap. `build_cont_closure`
(`src/compiler2/native_codegen/closure.rs`) emits the whole construction as CLIF:

```text
top, end = heap.bump_top, heap.block_end
if top + closure_size_for_count(n) <= end:        inline
  heap.bump_top += size
  heap.alloc_count, alloc_stats.total, alloc_stats.continuation += 1 object, size bytes
  [top+0] = header; [top+8] = code address
else:                                              block full
  top = fz_alloc_continuation(...)                 header and code written there
[top+16+8*i]        = raw word of capture i        (capture 0 is the outer cont)
[top+16+8*n+i]      = kind byte of capture i
```

`heap::INLINE_ALLOC_LAYOUT` and `process_abi::PROCESS_HEAP_OFFSET` give the field
offsets, and a heap test pins them against the real fields. Because the inline
path counts its own allocation, `Process.heap_alloc_stats()` reports every
continuation in its own `continuation_allocs` / `continuation_bytes` row (the
total includes it); the `closure` rows count only closures a program makes. The
stats map holds 34 entries, past `MAP_FLAT_MAX` (32). A ref capture's raw word is the payload of
its ref word; an int, float, pid or reference ref names a slot, so its raw word
is read through the ref. A capture does not mark a list shared: whether a cell a
continuation holds may be rewritten in place is the compiler's call-site
ownership decision, and an argument that a retained alias may reach is published
before the call.

Captures are read by inline loads (`closure_capture_ref`, `closure_capture_i64`,
`closure_capture_f64`, `closure_capture_atom`, `closure_code_ref`), and a
continuation is delivered with `return_call` / `return_call_indirect`, so a chain
of pending continuations lives on the heap rather than the native stack.

A continuation is resumed at most once (the rule is written on
`fz_ir::Cont`). At entry a continuation function reads every capture and its
outer continuation into registers, then `release_resumed_frame` gives the frame
back: when the frame ends at `heap.bump_top` and no `ValueRef` capture is
scalar-kinded (kinds 9..=0xE name their raw slot inside the frame), `bump_top`
returns to the frame's start and `alloc_count` falls by one. The statistics keep
the allocation; a frame under a newer object, or a pinned one, stays until the
next collection. The mid-flight yield continuation body releases its frame the
same way before it calls the callee. The back-edge yield stores a raw int, float
or atom straight into the frame's raw slot, and the body reads that slot raw, so
only its `ValueRef` and `HeapRef` slots count as ref slots; a frame of raw
captures is the newest object at resume and is given back. Only a capture whose
type is an integer, a float or an atom is raw (`AbiValueRepr::for_ty`); an `any`
or `int | float` capture is a `ValueRef`.

### Shared body frames

A body that calls many times is cut into one continuation per call, and each
resume would otherwise carry every value still live across it, so the code and
the frames grow with the square of the calls. `native_body_frame::frame_bodies`
instead lets a chain of continuations share one heap frame. A continuation joins
a chain when it is built at exactly one site, by another continuation of the
chain, nothing else enters it (a direct call, closure, protocol, `try` handler
or `receive` does), and at least `MIN_CHAIN` (16) continuations precede it.
The chain's root is built with a slot for every value the chain holds
(`BodyFrame { role: Root, slots }`); each member (`role: Member`) is handed the
frame itself: its builder writes the values new at the site with
`Prim::FrameStore`, clears the boxed slots whose values die there
(`Prim::FrameClear`), points the frame's code at the member
(`frame_resume_at`), and the member reads what it uses with `Prim::FrameLoad`.

A body frame is never released at a resume: later members still read it, so the
entry harness skips `release_resumed_frame` (the pop, and the poison under
`poison_dead_frames`) for every continuation that runs in one. A collection
reclaims the frame once the chain is done. The poison fixtures include two long
bodies (01253, 01255) so a release of a shared frame fails loudly.

A frame a collection kept lives in an old block, and a store into it that names a
younger object would be invisible to the next minor collection. Every frame
store and clear therefore first tests that the frame lies in the tip block,
`[block_start, bump_top)`, and otherwise calls `fz_frame_for_write`, which
answers the frame itself when it is young (a frame too large for the tip is
parked alone in a young block) and a copy at the tip when it is old; the store
goes to the answer, which the rest of the step uses. `Process::frame_copies`
counts the copies and the `process_exited` event reports it. A clear overwrites
a dead boxed slot with the nil atom so the frame does not keep the value
reachable; a slot whose kind is scalar is left whole, because a live ref to a
scalar names its own slot.

The `poison_dead_frames` cargo feature builds a compiler that poisons a
releasable frame (null code pointer, kind bytes 0xB, raw words
`0xDEAD000000000008`) instead of giving it back, and
`FZ_POISON_LATE_OUTER_READ` makes it read the outer continuation after the
release. `cargo test --features poison_dead_frames --test poison_dead_frames`
runs the native paths of representative fixtures under poison and checks that
the late read fails. CI runs that command as its own pull-request step
(`.github/workflows/ci.yml`); the workspace step and the coverage run do not
pass `--all-features`, because the feature replaces the pop with poison and so
changes the heap pins of every other test. The local gate does not run it.

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
value into the process. There are four per program, one per return repr kind:
`0=ValueRef`, `1=RawInt`, `2=RawF64`, `3=RawAtom`. Each is a zero-capture closure
whose code pointer is the matching `fz_halt_cont_body_*` Cranelift body. Codegen
emits them once, as read-only data objects (`fz_halt_cont_strict`,
`fz_halt_cont_i64`, `fz_halt_cont_f64`, `fz_halt_cont_atom`), and code takes their
address directly. The closure header packs `halt_kind` into its flags (low 14 bits
= capture count, high 2 bits = halt kind), which is how `fz_entry_thunk` selects
the right halt continuation for the inner body.

A thin function reference (a `MakeFnRef`, a function value with no captures) is
the same kind of object: one read-only data object per zero-capture callable
boundary (`fz_static_closure_<boundary id>`), emitted once, whose code pointer is
the boundary's function. Every process of the program, on the JIT and under AOT,
holds the same address. The interpreter's equivalent is `Node::static_closure`:
one 16-byte object per (denotation, arity, `FnId`), owned by the `Node` for the
run, laid out as a heap closure with no captures (header word, `FnId` as the
code word), referenced through a literal ref. Materializing the same function
twice answers the same word.

These objects are not in any process heap. The collector and deep copy
recognize them by the literal bit every reference to one carries (see
`any-value.md`, "The literal bit"): a literal passes through by pointer and is
never written. A write to one faults. They are not heap allocations, so they never appear in
heap alloc stats.

A halt continuation is declared `(value, self)`: it takes one word. The kind
comes from the one lane the bound body returns, which is why the root's return is
a one-word boundary (see [`externs`](externs.md), "One-word boundaries") and why
binding a root that returns any other number of lanes is a codegen error.

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
The roots the boundary GC traces are the `runnable` closure, the `delivered`
handler slot (a raise's handler, resumed inside the quantum that raised it, see
[exceptions](exceptions.md)), the park record's frame, the handlers of the `try` bodies the process is inside, the
`mailbox`, and the caller's transient values, all gathered by
`Process::collect`; the process `heap` is the arena being collected, not a root.

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
  — fixtures 00901 and 00902 on the `run` and `interp` paths: a miss gifts the
  whole message in one block (800032 bytes for the 50000-element log), a hit gifts exactly the bound cells (48 bytes for `[1, 2, 3]`),
  the receiver is woken once, and its own heap allocates no list cells for the
  delivery.
- `runtime/src/sched_core_test.rs` (`end_quantum` tests) — a resource freed by a
  collection has its destructor closure dispatched at the same boundary, and a
  queued raw payload is boxed as an integer only at dispatch; a held resource is left alone; a halted process dispatches every
  destructor without collecting; a claimed resource dispatches none; a
  destructor that yields is a fault.
- `cargo test --test fixture_matrix a_resource_freed_by_a_collection_runs_its_destructor_once_on_every_path`
  — fixtures 00906 and 00907: `process_exited` reports one dispatched destructor
  for the resource dropped mid-run and three for the resources held at exit, on
  `run` and `interp`; both fixtures run on all three paths for output parity.
- `runtime/src/sched_test.rs` — the probe, drain and delivery primitives: a hit
  leaves the receiver's heap untouched until it runs, two bindings of one cell
  copy it once, a second sender does not re-probe a matched receive, a dropped
  receiver returns its queued gifts to the pool and releases their binaries. The
  lock scope is pinned there too: a hit and a timer decide one park once in
  either order, a sender's matcher runs with the receiver's lock held, and a
  delivery cannot take the lock during the receive-entry walk and is probed
  against the installed park afterwards.
- `cargo test --test fixture_matrix a_receiver_left_parked_with_queued_gifts_drops_them_at_teardown`
  — fixture 00903: three messages gifted to a receiver that stays parked, on
  `run` and `interp`, each one block of exactly its measured bytes; the run ends with them still queued and `run_ended` shows
  the pool's outstanding count back at its starting value. The fixture runs on
  all three paths for output parity.
- `cargo test --test fixture_matrix many_senders_into_one_guarded_receive_gift_one_message_each_and_leave_the_misses_queued`
  — fixture 00910, on `run` and `interp`: a hundred senders into a guarded
  receive; fifty misses, the one hit, forty-nine misses, each miss one 80-byte
  block and the hit 48 bytes, with the same gift bytes on both paths and the
  pool census back at its starting value.
- `cargo test --test fixture_matrix a_large_list_passed_back_and_forth_crosses_as_one_gift_per_message_on_every_path`
  — fixture 00911, on `run` and `interp`: a 20000-element list passed for four
  rounds; every message is a hit gifting 320016 bytes in one block. Both
  fixtures run on all three paths for output parity.
- `cargo test --test fixture_matrix spawn_with_captures` — a spawned task is
  resumed as an entry thunk through `fz_resume`, the same verb a continuation
  uses.
- `reduction_budget_resets_and_spends` / `reset_reduction_budget_clears_yield_reasons`
  (`runtime/src/process_test.rs`) — budget reset/spend and yield-reason clearing.
- `coexistence` (`src/ir_interp/tests/coexistence.rs`) — two interpreters run on
  one thread without clobbering each other, proving no ambient current-process.
