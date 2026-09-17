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

Two events matter:

- `fz.runtime.execution_ready` — the boundary between compiling a program and
  running it, emitted by `run_root_jit` and `run_root_interp`.
- `fz.runtime.process_exited` — one per task exit, carrying the existing pid and
  live `Process` authority.

## `fz.runtime.execution_ready`

`signal_execution_ready` (`execution_ready.rs`) is the single emit site, called
by `run_root_jit` just before the runtime spawns the entry and by
`run_root_interp` just before `run_backend_main` enqueues it — so the event
lands once per `fz2 run`, once per `fz2 interp`, and once per `run-test-root`
child `fz2 test` starts, with parsing, the fixpoint drive, the backend product
and Cranelift all behind it. An AOT binary never emits it: `fz2 build` stops at
the object file, and the executable links `fz_runtime` and its own
`aot_run_queue_loop`, which carries no telemetry bus and emits no
`process_exited` either. The event has no payload; its content is its position
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
list_retention_hits: u64 }`. `ProcessExitCapture` builds it during dispatch by
reading the live process. `JsonlBackend` performs the same projection only when
it handles the event. The emitter does not traverse the process for telemetry.

List-retention fallbacks are derived, not emitted separately:
`fallback_count = list_retention_attempts - list_retention_hits`. The runtime
FFI helper increments `attempts` for every `fz_list_reuse_or_cons_parts` call,
and increments `hits` when the heap returns the original source cell, either
unchanged or after guarded rewrite. That keeps the runtime telemetry seam at one
boundary event instead of a per-attempt side channel.

The raw `&Process` is valid only during dispatch. A handler that needs data
after the callback must project and copy that data itself. `JsonlBackend`
renders fields synchronously.

## Program Output

`dbg` lines and `IO` writes are semantic program output, not telemetry.
`emit_print_line` passes rendered debug bytes through the running process's
line-oriented `ExecCtx.output` hook to an event-scoped `OutputSink`; the stdout
sink appends its newline there. `IO.write/1` uses the separate
`ExecCtx.output_write` hook and preserves its binary argument byte-for-byte;
`IO.puts/1` is `IO.write(text <> "\\n")`. A retaining test sink copies each
callback-scoped line. `NullOutput` does nothing. No sink constructs an event or
stages a second copy for a later telemetry call.

`System.argv/0` reads the argument vector owned by that scheduler's `ExecCtx`.
`fz2 run` and `fz2 interp` accept those program arguments after `--`; an AOT
executable receives the operating-system argument vector directly. In every
case the source or executable name is omitted, arguments must be UTF-8, and the
runtime allocates a fresh fz list of binaries in the calling process heap.

Interpreter, JIT, and AOT install the same raw callback boundary. An interpreter
destructor-drain failure is propagated directly; it is not converted into a
telemetry-only warning.

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
