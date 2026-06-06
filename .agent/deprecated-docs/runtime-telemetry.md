# Runtime Telemetry

## Model

Runtime telemetry is how the running scheduler reports what a task did, and how
tests observe a run without reaching into a `Process`. It is the runtime side of
the same idea as compile-time [`telemetry`](telemetry.md): the system writes down
facts it already holds, and a sink that is listening reads them.

`Runtime::new(compiled, workers, tel)` installs the sink on the compiled
scheduler at construction time; `IrInterpRuntime` carries one through its run.
Both engines route through the same emit sites, so a test behaves identically
across interpreter, JIT, and AOT.

Two events matter:

- `fz.runtime.process_exited` — one per task exit, carrying its halt value and
  heap stats.
- `fz.runtime.dbg` — one per `dbg`/print line.

## `fz.runtime.process_exited`

`ExitRecord::emit` (in `exec/runtime.rs`) is the single emit site, shared by both
engines: the compiled scheduler calls it as a task leaves `run_until_idle`, and
`IrInterpRuntime` calls it at its own halt sites. The event carries both a scalar
projection and the live `&Process`:

```text
event:        fz.runtime.process_exited       (an `execute`: measurements + metadata)
measurements: halt_value, live_count, bytes_used
metadata:     pid, process = opaque(&Process)
```

`ExitRecord` is the projection: `{ pid, halt_value: i64, live_count: usize,
bytes_used: usize }`. `ExitRecord::project` builds it by reading `process.halt_value`,
`process.heap.live_count()`, and `process.heap.bytes_used()` — the single place that
reads `Process` internals for this event. `emit` projects, then publishes the
scalars as measurements and the live `&Process` as opaque metadata beside `pid`.

The split is deliberate, and it decides what a handler may read:

- The **measurements** are the durable, stable contract — plain numbers. They are
  the part that survives into a stored event.
- The **opaque `&Process`** is the escape hatch for a synchronous handler that
  needs a field the projection omits; it `downcast_ref`s the metadata back to a
  `&Process` during dispatch. An opaque value never survives into a stored event:
  the `Capture` handler drops it when it owns the event (`durable_owned` keeps
  every value except opaque references — `to_owned_durable` returns `None` only
  for `Value::Opaque`, so numbers, bools, strings, string-seqs, and byte blobs
  all survive), and `JsonlBackend` skips it when it serializes. So the `&Process`
  is valid only during dispatch — never read it from a stored event.

## `fz.runtime.dbg`

`dbg`/print output is routed onto the bus too. `emit_print_line` (the shared
render seam in the runtime crate) writes production stdout with `println!`, then
forwards each rendered line through the running process's `ExecCtx.output` hook,
handing it the sink on `ExecCtx.tel`. Both are per-task fields on the `ExecCtx`
the scheduler installs, not thread-globals — so each scheduler's dbg output stays
on its own sink. The hook (`output_hook_thunk`) emits the line as an event:

```text
event:    fz.runtime.dbg     (an `event`: metadata only)
metadata: line
```

Both engines install the same `output_hook_thunk` on `ExecCtx.output`, so dbg
output is observable as events on the interpreter, JIT, and AOT alike.

## Observing In Tests

There is one run path — the production scheduler — and tests watch it through the
two events instead of poking task internals. They never construct a caller-owned
`Process` or read a print buffer; they attach handlers and read what was emitted:

- `ProcessExitCapture` reconstructs a typed `ExitRecord` (result + heap stats)
  from each `process_exited` event's measurements, queryable by `last()` or
  `by_pid(pid)`.
- `DbgCapture` records the `fz.runtime.dbg` line stream, read back with `lines()`.

`observe(compiled, entry)` (codegen tests) attaches both, spawns `entry`, drains
`run_until_idle`, and returns the root task's `ExitRecord` plus the dbg lines. The
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
