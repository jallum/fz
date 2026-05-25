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

## CURRENT_PROCESS Boundary

`fz_runtime::process::CURRENT_PROCESS` is a dynamic bridge, not the runtime
owner.

During one interpreter quantum, the scheduler installs the selected process in
`CURRENT_PROCESS`, calls `run_fn`, then restores the previous pointer. Helpers
below `run_fn` use that bridge for:

- heap allocation
- mailbox reads
- tuple schema lookup
- `self()`
- resource allocation and destructor draining
- back-edge GC over process roots

The runtime decides which process runs. `CURRENT_PROCESS` only exposes that
process while it is running.

## Drive Semantics

The scheduler loop is:

```text
enqueue(pid, fn_id, args)
while run queue has pid:
  load pid's CodeImage
  install pid as CURRENT_PROCESS
  run_fn(..., pid_code_image.module)
  Done    -> drain task resources unless pid is keepalive
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
