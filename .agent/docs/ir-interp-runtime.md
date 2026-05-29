# IR Interpreter Runtime Ownership

## Model

`IrInterpRuntime` owns interpreter runtime state. Callers choose whether that
runtime is fresh for one entry or persistent across many entries.

```text
one-shot command -> fresh IrInterpRuntime -> enqueue entry -> drive -> drop
REPL session     -> persistent runtime   -> enqueue chunk -> drive -> keep
```

Scheduler state lives on `IrInterpRuntime`. It does not belong in
`eval::CompileTimeEvaluator`, thread-local interpreter globals, or host-side
helper state.

## What The Runtime Owns

`IrInterpRuntime` is the owner for:

- process table
- process `CodeImage` generation
- next pid
- runnable pid queue
- resume entries
- selective receive park records
- shared process schema registry
- tuple schema id cache

`run_main` and `run_test_fn` are convenience wrappers for one-shot commands.
They create a runtime, run an entry, and discard the runtime. Code that needs
mailboxes, heaps, blocked processes, resources, or spawned children to survive
must keep an `IrInterpRuntime` value and drive it again later.

## Code Images

Every process runs against its own immutable `CodeImage`.

`enqueue_entry(module, pid, fn_id, args)` creates a new image from `module` and
assigns it to `pid` before enqueueing the entry. A spawned child inherits the
spawning process's image. This matters because blocked continuations contain
`FnId`s owned by the image they were compiled in.

Do not dispatch runnable processes through one ambient module. A persistent
runtime may contain:

```text
evaluator pid -> newest REPL chunk image
child pid     -> older image, blocked in receive
```

The child must resume against the older image even after the evaluator has
advanced.

## Running process is threaded, not ambient

The interpreter owns its processes and threads the running one explicitly; the
running process is never ambient. Each quantum, `drive_until_idle` sets
`IrInterpRuntime.current_proc` to the dispatched process; `cur_proc()` returns
it, and the free helpers that lack a runtime handle take a `*mut Process`
parameter threaded down from the eval loop. Sites that use it:

- heap allocation (list cons, map/struct/bitstring builders, scalar boxing)
- mailbox reads
- tuple schema lookup
- `self()`
- resource allocation and destructor draining
- back-edge GC over process roots
- the receive matcher (`resolve_matcher_subject` and friends carry it)

Because the process is per-instance state on `IrInterpRuntime`, two interpreters
can run on one thread without clobbering each other (see
`ir_interp/tests/coexistence.rs`).

## Drive Semantics

The scheduler loop is:

```text
enqueue(pid, fn_id, args)
while run queue has pid:
  load pid's CodeImage
  set current_proc = pid's process (+ heap owner, ExecCtx)
  run_fn(..., pid_code_image.module)
  Done    -> drain task resources unless pid is keepalive
  Yielded -> store resume entry, run boundary maintenance, re-enqueue
  Blocked -> store resume entry, mark blocked
  Parked  -> store selective receive park record, mark blocked
```

`send` is scheduler work. It copies the message into the receiver heap, probes a
parked selective receive when present, and re-enqueues the receiver if the send
wakes it.

Pass a `keepalive_pid` when a completed process must survive the drive. REPL
evaluator processes use this so a successful chunk does not tear down the
mailbox, heap, or resources needed by later chunks.

## Compile-Time Evaluator Boundary

`eval::CompileTimeEvaluator` is compile-time infrastructure for macro expansion
and source-world metadata. It is not the runtime substrate for REPL chunks,
tests, scheduler state, spawned processes, or mailboxes.

Runtime user code lowers to IR and runs on `IrInterpRuntime`.
