# Runtime Telemetry

## Model

Runtime telemetry is how the running scheduler reports what a task did, and how
tests observe a run without reaching into a `Process`. It is the runtime side of
the same idea as compile-time [`telemetry`](telemetry.md): the system writes down
facts it already holds, and a sink that is listening reads them.

`Runtime::with_telemetry` attaches the sink. Both execution engines — the
compiled `Runtime` and the interpreter `IrInterpRuntime` — emit the same events,
so a test behaves identically across interpreter, JIT, and AOT.

## `fz.runtime.process_exited`

Emitted once per task exit, through the single `ExitRecord::emit` site shared by
both engines:

```text
event:        fz.runtime.process_exited
measurements: halt_value, live_count, bytes_used   (durable; built by ExitRecord::project)
metadata:     pid, process = opaque(&Process)       (live during dispatch only)
```

It carries **both** a measurement projection and the live `&Process`, and the
split is deliberate:

- The **measurements** are the durable, stable contract. `durable_owned()` keeps
  them, so they survive into stored events (`Capture`, JSONL). `ExitRecord::project`
  is the single place that reads `Process` internals for the event.
- The **opaque `&Process`** is the escape hatch for a synchronous handler that
  needs a field the projection omits. `durable_owned()` drops opaque values, so
  it is valid only during dispatch — never read it from a stored event.

## `fz.runtime.dbg`

`dbg`/print output is routed onto the bus too. `emit_print_line` (the shared
render seam) writes production stdout and forwards each line through the running
process's `ExecCtx.output` hook to the sink on `ExecCtx.tel` — the per-task
dispatch table the scheduler installs, not a thread-global. So dbg output is
observable as events on both engines, and each scheduler's output stays on its
own sink:

```text
event:    fz.runtime.dbg
metadata: line
```

## Observing In Tests

There is one run path — the production scheduler — and the test convenience
`CompiledModule::run(fn_id)` is a thin `spawn` + `run_until_idle` over it that
reads its result from `process_exited`, not from `task.halt_value`. Tests do not
construct a caller-owned `Process` or read a print buffer; they observe:

- `ProcessExitCapture` → a typed `ExitRecord` (result + heap stats).
- `DbgCapture` → the `fz.runtime.dbg` line stream.

`observe(compiled, entry)` (codegen tests) bundles both, and the `run_main` /
`capture_main` family is built on it.
