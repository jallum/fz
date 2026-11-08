# Runtime Telemetry

## Model

Runtime telemetry is how the running scheduler reports what a task did, and how
tests observe a run without reaching into a `Process`. It is the runtime side of
the same idea as compile-time [`telemetry`](telemetry.md): the system writes down
facts it already holds, and a sink that is listening reads them.

`Runtime::new(compiled, workers, tel)` preserves the concrete telemetry type on
the compiled scheduler; the interpreter call graph does the same. Both engines
route through the same typed raw emit site, so `NullTelemetry` remains
monomorphizable and configured handlers behave identically across interpreter,
JIT, and AOT.

Four events matter:

- `fz.runtime.execution_ready` — the boundary between compiling a program and
  running it, emitted by `run_root_jit` and `run_root_interp`.
- `fz.runtime.process_exited` — one per task exit, carrying the existing pid and
  live `Process` authority.
- `fz.runtime.scheduler_slept` — one each time the scheduling core sleeps for a
  pending receive-after timer because nothing is runnable.
- `fz.runtime.send.probe` — one per cross-process send, carrying what the
  sender's probe decided and what it cost.

## `fz.runtime.execution_ready`

`signal_execution_ready` (`execution_ready.rs`) is the single emit site, called
by `run_root_jit` just before the runtime spawns the entry and by
`run_root_interp` just before `run_backend_main` enqueues it — so the event
lands once per `fz2 run`, once per `fz2 interp`, and once per `run-test-root`
child `fz2 test` starts, with parsing, the fixpoint drive, the backend product
and Cranelift all behind it. An AOT binary never emits it: `fz2 build` stops at
the object file, and the executable links `fz_runtime` and its own
`aot_run_queue_loop`, which carries no telemetry bus and emits no
`process_exited` or `scheduler_slept` either. The event has no payload; its content is its position
in the stream. The same call writes one byte to the descriptor named by
`FZ_EXEC_READY_FD` when the environment names one — the fixture matrix's
execution deadline is a consumer of this boundary, not a second definition of it
(see [fixtures](fixtures.md)).

## `fz.runtime.process_exited`

`ExitRecord::emit` (in `exec/runtime.rs`) is the single emit site, shared by both
engines: the compiled scheduler calls it as a task leaves `run_until_idle`, and
`IrInterpRuntime` calls it at its own halt sites. The event carries no derived
process fields:

```text
raw event:    fz.runtime.process_exited
signature:    (&PidId, &Process)
```

`ExitRecord` is a handler-side projection: `{ pid, halt_value: i64, live_count:
usize, bytes_used: usize, list_retention_attempts: u64,
list_retention_hits: u64, failed: bool }`. `failed` is `Process.failed`: whether
the process ended through `fz_panic` (see [process failure](process-failure.md));
a failed process's `halt_value` is not a return value. `ProcessExitCapture`
builds it during dispatch by reading the live process. `JsonlBackend` performs
the same projection only when it handles the event, writing `failed` as a JSON
boolean. The emitter does not traverse the process for telemetry.

List-retention fallbacks are derived, not emitted separately:
`fallback_count = list_retention_attempts - list_retention_hits`. The runtime
FFI helper increments `attempts` for every `fz_list_reuse_or_cons_parts` call,
and increments `hits` when the heap returns the original source cell, either
unchanged or after guarded rewrite. That keeps the runtime telemetry seam at one
boundary event instead of a per-attempt side channel.

The raw `&Process` is valid only during dispatch. A handler that needs data
after the callback must project and copy that data itself. `JsonlBackend`
renders fields synchronously.

## `fz.runtime.scheduler_slept`

`Scheduler::about_to_sleep` is the hook `next_runnable`
(`runtime/src/sched_core.rs`) calls just before it sleeps. The JIT `Runtime` and
the interpreter's scheduler adapter implement it by emitting `SCHEDULER_SLEPT`
(`exec/runtime.rs`) with a `Duration`, the wait until the next timer deadline.
`JsonlBackend` renders it as `wait_ns`. The event fires only when the run queue
is empty and a timer pends, so a program whose timers are all cancelled by
arriving messages never emits it. The AOT scheduler carries no telemetry bus and
keeps the default no-op hook. `exec/runtime_test.rs` observes the event on the
`run` and `interp` paths.

## `fz.runtime.send.probe`

A send to another process runs `sched::probe_sender` on the sender: the
receiver's parked matcher, if any, is tested against the message with the
sender as the allocating process, and whatever the receiver will keep (the
bound values on a hit, the whole message on a miss) is copied into a gift on the
sender's heap and queued on the receiver's `in_queue`. `emit_send_probe`
(`exec/runtime.rs`) is the single emit site; the JIT `send_via` and the
interpreter's `send_ref` call it with the `SendProbe` the probe returned:

```text
raw event:    fz.runtime.send.probe
signature:    (&SendProbe)
```

`SendProbe` is `{ outcome: Hit | Miss, receiver: PidId, reductions: i64,
gift_bytes: usize, gift_blocks: usize }`. `reductions` is the change in the
sender's remaining budget across the matcher call; `gift_bytes` and
`gift_blocks` are the segment's fill and block count, both `0` when a hit binds
nothing and no window opens. `JsonlBackend` renders the
outcome as `"hit"` or `"miss"` and the rest as numbers. A self-send is a mailbox
push and emits nothing. The AOT scheduler carries no telemetry bus and emits
nothing, as for the other runtime events. `tests/fixture_matrix.rs`
(`a_send_probes_on_the_sender_and_gifts_its_result_through_the_receivers_in_queue`)
pins the event sequence of fixtures 00695 and 00696 on the `run` and `interp`
paths.

## Program Output

`dbg`/print lines are semantic program output, not telemetry. `emit_print_line`
passes its existing rendered bytes through the running process's
`ExecCtx.output` hook to an event-scoped `OutputSink`. The CLI sink writes those
bytes to stdout immediately. A retaining test sink copies them during the
callback. `NullOutput` does nothing. No sink constructs an event or stages a
second copy for a later telemetry call.

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
  cumulative list-retention counters) from each `process_exited` event's
  live process during dispatch, queryable by `last()` or `by_pid(pid)`.
- `DbgCapture` is a retaining `OutputSink` that copies each callback-scoped line,
  read back with `lines()`.

`observe(compiled, entry)` (codegen tests) attaches the exit handler and installs
the output sink, spawns `entry`, drains `run_until_idle`, and returns the root
task's `ExitRecord` plus the dbg lines. The
result/output/heap helpers build on it: `run_main` reads `observe(...).exit.halt_value`,
`capture_main` reads `observe(...).output`, and `run_capturing` returns
`(exit.halt_value, exit.live_count)`.

`CompiledModule::run(tel, fn_id)` is a sibling convenience: a thin `spawn` +
`run_until_idle` that uses the caller-owned telemetry bus, attaches a
`ProcessExitCapture`, and returns the root pid's `halt_value` from its
`process_exited` record. Both seams read the result from the event, not from
`task.halt_value`.

Tests follow the same ownership rule as compile-time telemetry: the test root
creates the bus, then helpers thread it downward. A helper that allocates its
own runtime bus splits the observation stream and stops the test from seeing the
actual run it asked for.
