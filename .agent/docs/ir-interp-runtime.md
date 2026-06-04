# IR Interpreter Runtime Ownership

## Model

The IR interpreter walks a lowered `fz_ir::Module` directly, but uses the same
heap, value representation, and runtime FFI as the compiled engine. Spawn, send,
and receive run on its own cooperative scheduler; processes, heaps, and
mailboxes are byte-compatible with the JIT/AOT path.

`IrInterpRuntime` is the single owner of all interpreter runtime state. A caller
decides whether that runtime is fresh for one entry or held across many:

```text
fz interp    -> run_main_with_plan -> fresh runtime -> run main/0 -> drop
REPL session -> persistent runtime  -> enqueue_entry_with_plan -> drive -> keep
```

The pieces a reader needs to sketch the box-and-arrow:

- `IrInterpRuntime` — owns the process table, scheduler queues, code images,
  the shared atom node, and the schema registry.
- `CodeImage` — an immutable `(Module, ModulePlan)` pair; each process runs
  against the image it was compiled in.
- `run_fn_typed` — the per-quantum executor; returns an `InterpStep`.
- `drive_until_idle` — the scheduler loop that dispatches runnable pids until
  the queue empties.

## What The Runtime Owns

`IrInterpRuntime` holds, in fields:

- `tasks` — the process table, `pid -> Box<Process>`.
- `code_images` — `pid -> Rc<CodeImage>`, the image each process runs against.
- `next_pid` — the next pid to hand out (the root process is pid 1, so this
  starts at 2).
- `run_queue` — FIFO of runnable pids.
- `resume` — per-pid resume state: `(FnId, args, Option<SpecKey>, after-chain)`.
- `parked` — per-pid selective-receive park records.
- `schemas` — an `Rc<RefCell<SchemaRegistry>>` shared by every process in this
  runtime, plus `tuple_schema_ids`, a cache from tuple arity to schema id.
- `node` — the shared `Node` (the atom table), cloned by `Rc` into every
  process so all tasks in one runtime see one atom set.
- `current_proc` — a raw `*mut Process` pointing at the process running this
  quantum (see "Running process is threaded, not ambient").

`run_main_with_plan` is the production one-shot wrapper behind `fz interp`: it
takes a module and the plan the caller already prepared, builds a fresh runtime
with the root process seeded (`fresh_with_root`), installs the plan as pid 1's
image, runs `main/0` to completion, and returns the halt value paired with the
runtime. `run_test_fn` is the `fz test` per-test wrapper: it builds a fresh
runtime, gives the test its own heap and mailbox, and runs one test fn so state
cannot leak between tests in a module. (`run_main` is a
`#[cfg(test)]` convenience that plans the module and then calls
`run_main_with_plan`, keeping only the halt value.)

A one-shot wrapper drops its runtime when the entry finishes. Code that needs
mailboxes, heaps, blocked processes, resources, or spawned children to survive
past one entry keeps the returned `IrInterpRuntime` value and drives it again.

## Code Images

Every process runs against an immutable `CodeImage`, which pairs an `Rc<Module>`
with the `Rc<ModulePlan>` planned for that exact module shape. `FnId`s are
module-local and resume entries, continuations, and park records all carry
`FnId`s, so a process can only be resumed against the image that minted them.

Two entry points install an image:

- `enqueue_entry_with_plan(t, module, module_plan, pid, fn_id, args)` takes a
  plan the caller already prepared and stores it on `pid`'s image before
  enqueueing. The CLI/REPL path uses this: it prepares the execution graph
  (`graph.module`, `graph.module_plan`) and threads that plan straight in.
- `enqueue_entry(module, pid, fn_id, args)` (test-only) plans the module itself
  via `plan_module` at image-construction time.

A spawned child inherits the spawning process's image: `spawn` looks up the
parent's `CodeImage` (through `current_proc`) and assigns the same `Rc` to the
child. A persistent runtime therefore holds a mix of images at once:

```text
evaluator pid -> newest REPL chunk image
child pid     -> older image, blocked in receive
```

The child resumes against its older image even after the evaluator advances to a
newer chunk.

Planning happens only at image construction, never inside the scheduler loop:
`drive_until_idle` reads `module` and `module_plan` off the loaded image and
calls `run_fn_typed` against them. The contract is that progress consumes an
already-prepared image; the scheduler never re-derives plan facts while running,
yielding, resuming, or draining destructors.

## Running Process Is Threaded, Not Ambient

The interpreter owns its processes and threads the running one explicitly.
`drive_until_idle` sets `current_proc` to the dispatched process at the top of
each quantum; `cur_proc()` reads it. Free helpers that lack a runtime handle
either read `cur_proc()` or take a `*mut Process` threaded down from the eval
loop. The sites that need it:

- heap allocation: list cons, map/struct/bitstring builders, and scalar
  materialization (`value(cur_proc())` boxes a scalar into the heap on demand).
- mailbox reads in `Term::ReceiveMatched`.
- tuple schema lookup.
- `self()` (returns `cur_proc().pid`).
- resource allocation and destructor draining.
- the back-edge in `Term::TailCall`, which charges a reduction against
  `cur_proc()` and does cooperative GC over process roots.
- the receive matcher (`resolve_matcher_subject` and friends carry
  `cur_proc()`).

Because the running process is per-instance state on `IrInterpRuntime` rather
than a thread-local, two interpreters with separate telemetry sinks run on one
thread without clobbering each other. `ir_interp/tests/coexistence.rs` proves
this: two runtimes, each routing `dbg` through its own per-task `ExecCtx`, and
each sink sees only its own output.

## Drive Semantics

`drive_until_idle` builds one `ExecCtx` on its stack frame (carrying the
scheduler pointer, the telemetry sink, and the `dbg`/`print` output thunk),
points every dispatched process's `ctx` at it, then loops:

```text
while run_queue has a pid:
  load pid's CodeImage (module + module_plan)
  take pid's resume entry (fn_id, args, spec, after)
  set current_proc; mark Running; reset the reduction budget; set heap owner
  step = run_fn_typed(...)
  loop on step:
    Done(val) | Halt(val):
      drain the after-chain first; each link feeds val + captures to the next fn
      record completion
      keepalive pid? -> mark Ready, leave intact, move on
      else -> drop deferred MSOs, drain pending dtors, record halt_value,
              emit process_exited, mark Exited
    Yielded {...}:
      finish_yield_report + boundary_maintenance (GC over resume/after roots)
      store resume entry, re-enqueue, mark Ready
    BlockedMatched(park, after):
      store the park record, mark Blocked
```

`InterpStep` (returned by `run_fn_typed`) has exactly four variants: `Done`,
`Halt`, `Yielded`, and `BlockedMatched`. A `Yielded` step carries the resume
fn/args/spec, an after-chain, the remaining reduction count, and a yield reason
byte; the back edge in `run_fn_typed` produces it when the reduction budget hits
zero. `BlockedMatched` carries the selective-receive `ParkRecord` and the
after-chain to run once the receive resolves.

`send` is scheduler work, not a heap primitive. It deep-copies the message into
the receiver's heap. If the receiver is parked on a selective receive, `send`
runs the parked matcher inline against the new message: on a hit it sets the
matched clause's body as the receiver's next resume and re-enqueues it without
touching the mailbox; on a miss the park stays and the copy lands in the
mailbox. A receiver blocked without a park record is woken by inserting the
copied message at the front of its resume args.

`drive_until_idle` takes a `keepalive_pid`. When a completed process matches it,
the runtime records the result, marks the process `Ready`, and leaves its
mailbox, heap, and resources intact instead of tearing them down. The REPL
passes its evaluator pid as keepalive so a successful chunk does not destroy the
state later chunks depend on.

## Selective Receive

`Term::ReceiveMatched` scans the mailbox head-to-tail, trying each clause via
the cached `Matcher` lowered at the receive site; first match wins, and the
matched message is removed. On a miss, an `after` with a literal `0` timeout
fires its body inline; any other timeout (including `:infinity`) parks without a
timer, because the interpreter has no wall clock. Parking returns
`BlockedMatched(ParkRecord, after)`.

A `ParkRecord` snapshots exactly what the sender-side probe needs to re-run the
match later: the per-clause `MatchedClause` list (`bound_names`, optional
`guard` FnId, body FnId), the `Arc<Matcher>`, the pinned `^name` bindings, and
the capture values from the receive site. Guards execute inside the cached
matcher, so a parked clause needs no AST re-walk when a new message arrives.

## Compile-Time Evaluator Boundary

Two evaluators exist for two worlds. `eval::CompileTimeEvaluator` walks the AST
to run `defmacro` bodies during compilation; it works on the tree value model
(`exec::value::Value`) and carries only a toy pid/mailbox model for macro-time
`self`/`spawn`/`send`. `IrInterpRuntime` runs lowered IR on real `Process`es and
heaps.

User runtime code runs on `IrInterpRuntime`. REPL chunks lower to IR evaluator
entries and execute through `enqueue_entry_with_plan` + `drive_until_idle`, so
`x = 42` on one line and `x + 1` on the next take the same runtime path as
spawned processes and receives. Keeping interactive code on the program runtime
means spawn, receive, resources, and heap values behave at the prompt exactly as
they do in an ordinary program.
