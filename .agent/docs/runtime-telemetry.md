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

One event matters:

- `fz.runtime.process_exited` — one per task exit, carrying the existing pid and
  live `Process` authority.

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
usize, bytes_used: usize, reusable_cons_attempts: u64,
reusable_cons_reused: u64 }`. `ProcessExitCapture` builds it during dispatch by
reading the live process. `JsonlBackend` performs the same projection only when
it handles the event. The emitter does not traverse the process for telemetry.

Reusable-cons fallbacks are derived, not emitted separately:
`fallback_count = reusable_cons_attempts - reusable_cons_reused`. The runtime
FFI helper increments `attempts` for every `fz_list_reuse_or_cons_parts` call,
and increments `reused` only when the heap reports in-place reuse by returning
the original source cons ref. That keeps the runtime telemetry seam at one
boundary event instead of a per-attempt side channel.

The raw `&Process` is valid only during dispatch. A handler that needs data
after the callback must project and copy that data itself. `JsonlBackend`
renders fields synchronously.

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

## Observing In Tests

There is one run path — the production scheduler — and tests watch its exit event
instead of poking task internals:

- `ProcessExitCapture` reconstructs a typed `ExitRecord` (result + heap stats +
  cumulative reusable-cons counters) from each `process_exited` event's
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
