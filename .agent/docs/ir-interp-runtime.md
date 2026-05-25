# IR Interpreter Runtime Ownership

## ELI5

The IR interpreter is becoming the runtime substrate for the REPL. That only
works if the REPL can keep one runtime alive across many user inputs.

Today `run_main` and `run_test_fn` create a fresh hidden world, run one entry,
then tear that world down. That is fine for `fz interp <file>` and `fz test`,
but it cannot model:

```text
fz> child = spawn(fn -> receive() end)
fz> send(child, :go)
```

The child must still exist at the second prompt. Therefore runtime state must be
owned by an explicit `IrInterpRuntime`, not by thread-local globals reset at
each entry.

## Ownership Rule

`IrInterpRuntime` owns interpreter runtime state:

- process table
- next pid
- run queue
- resume entries
- parked selective receive records
- schema registry
- tuple schema ids

The target direction is one-way:

```text
run_main/run_test_fn wrappers -> fresh IrInterpRuntime -> enqueue entry -> drive
REPL session              -> persistent IrInterpRuntime -> enqueue chunks -> drive
```

Do not add new scheduler state to `eval::Interp` or to new interpreter TLS.

## Current Runtime State

Interpreter runtime state is owned by `IrInterpRuntime`:

- process table: pid to `Process`
- process code image: pid to immutable `CodeImage` generation that owns its
  `FnId`s
- next spawned pid
- runnable pid queue
- resume entries: pid to `(fn_id, captures, after_chain)`
- selective receive park records
- shared process schema registry
- tuple arity to schema id cache

`run_main` and `run_test_fn` still create a fresh runtime for each one-shot
entry. A persistent REPL runtime must not recreate this state between prompts.

Use `IrInterpRuntime::fresh_with_root`, `enqueue_entry`, and
`drive_until_idle` when a caller needs to keep the same evaluator process alive
across more than one entry. Pass the evaluator pid as `keepalive_pid` so a
completed chunk leaves the process, mailbox, heap, and resources available for
the next drive instead of running task-exit cleanup.

`enqueue_entry(module, pid, fn_id, args)` creates a new `CodeImage` generation
from that module and assigns it to the process before enqueueing the entry.
`spawn` assigns the spawning process's `CodeImage` to the child, so a child
blocked in `receive` keeps the generation that owns its continuation `FnId`s`.
Host-spawned test helpers that run outside an active process create a
`CodeImage` from the module passed to `spawn`.

`drive_until_idle` dispatches each runnable pid against its own stored
`CodeImage`, not against a single ambient module. This is required for the
REPL: a blocked child may hold continuation `FnId`s from an older compiled
chunk while the evaluator pid has already moved to a newer chunk module.

## `CURRENT_PROCESS` Boundary

`fz_runtime::process::CURRENT_PROCESS` is not the scheduler state owner. It is
the dynamic bridge used while one process is actively running.

During an interpreter quantum, `run_main` installs the selected `Process` in
`CURRENT_PROCESS`, calls `run_fn`, then restores the previous pointer. Code
below `run_fn` expects that bridge for:

- heap allocation
- mailbox reads
- tuple schema lookup through `IrInterpRuntime`
- `self()`
- resource allocation and destructor draining
- back-edge GC over process roots

The runtime object should decide which process runs. `CURRENT_PROCESS` should
only expose that selected process to heap/runtime helpers for the duration of
the call.

## Scheduler Shape

The current scheduler shape is:

```text
enqueue(pid, fn_id, args)
while run queue has pid:
  load pid's CodeImage generation
  install pid as CURRENT_PROCESS
  run_fn(..., pid_code_image.module)
  Done      -> drain task resources, mark exited
  Blocked   -> store resume entry, mark blocked
  Parked    -> store selective receive park record, mark blocked
```

`send` is scheduler work. It copies the message into the receiver heap, probes a
parked selective receive when present, and re-enqueues the receiver if the send
wakes it.

This model must survive as the REPL starts using it. The owner is explicit now;
the next boundary is persistent driving without recreating the runtime.

## Elixir/IEx Reference Model

Elixir's IEx does not run each prompt in a disconnected toy evaluator. IEx has a
long-lived evaluator process that holds the session binding and environment.
Each complete input is sent to that evaluator, evaluated with the current
environment, and returns an updated binding/environment. Because evaluation runs
inside a real BEAM process, `self`, `spawn`, `send`, `receive`, blocking, and
mailboxes use normal runtime semantics.

The fz equivalent is:

```text
ReplSession
  ReplWorld      definitions, modules, macros, docs, types
  ReplBindings   top-level names mapped to runtime values
  ReplRuntime    persistent IrInterpRuntime with evaluator process/task
```

Each user chunk should lower to IR, synthesize an evaluator entry function, and
drive it on the same `IrInterpRuntime`. The chunk returns display value plus
updated top-level bindings. Runtime process state is not rebuilt between
chunks.

## Non-goals

Do not solve these while extracting `IrInterpRuntime`:

- no JIT requirement for the first REPL runtime path
- no rewrite of parser buffering, prompt handling, `?doc`, or script I/O
- no retirement of `eval::Interp` for compile-time macro expansion
- no new toy mailbox/process model for the REPL
- no direct call to `fz interp <file>` as the interactive implementation

`eval::Interp` may remain the compile-time macro evaluator until a separate
ticket retires or renames that layer.

## Tests That Must Stay Green

Keep the existing one-shot paths behaviorally stable during extraction:

- `cargo test ir_interp`
- `cargo test fixture_matrix`
- `cargo test repl`
- `fz interp` fixture paths that currently pass
- `fz test` interpreter dispatch through `run_test_fn`

Add focused tests as runtime ownership moves:

- `run_main` and `run_test_fn` are fresh-runtime wrappers
- spawn returns before the child runs
- send to blocked receiver wakes it through runtime state
- selective receive miss parks matcher state and keeps unmatched mail
- selective receive hit wakes via sender-side probe
- tuple schema ids are runtime-owned, not process-global TLS
- persistent drive can enqueue entry A, block, enqueue/send entry B later, and
  resume A without reset

The first persistent-drive test is the gate before routing `repl --script` or
interactive REPL evaluation through `ReplSession`.
