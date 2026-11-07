# Process failure

A process that fails takes one route on every execution path. This doc covers
that route: the primitive, the line it prints, how each driver ends the process,
and how the program's exit status follows from the main process.

## The primitive

`Kernel.panic/1` is the one runtime failure primitive. It wraps
`extern "fz" defp fz_panic(any) :: never`, whose physical export is
`fz_runtime::failure::fz_panic(process, value_ref)`. The export:

1. renders the value as its failure line (`failure_line`);
2. sets `Process.failed = true`;
3. hands the line to the execution context's fault sink, `ExecCtx.fault`;
4. returns.

The export returns so each caller can end the process through its normal exit
path. Nothing after a panic runs.

`Kernel.raise/1` and `Kernel.raise/2` are plain fz code over `panic`.
`raise(name, message)` panics with the exception map
`%{__struct__: name, __exception__: true, message: message}`;
`raise(message)` is `raise(RuntimeError, message)`. Both are imported into
every namespace by `lib/runtime.fz`, beside `panic/1`.

## The line

`failure_line` prints what Elixir prints for an uncaught exception, without the
stacktrace:

| value | line |
|---|---|
| a map with `__exception__: true`, an atom `__struct__` and a byte-aligned binary `message` | `** (Name) message` |
| anything else | `** (ErlangError) Erlang error: <value>` |

`Name` and `<value>` use the dbg rendering, so a module name prints as its alias
(`ArgumentError`, not `:"Elixir.ArgumentError"`). A reason atom such as
`:badarg` prints as `** (ErlangError) Erlang error: :badarg`, as
`:erlang.error(:badarg)` would in Elixir. Elixir normalizes a few reason atoms
into named exceptions (`:badarith` becomes `ArithmeticError`); fz does not.

## The fault sink

`FaultHook` (`runtime/src/scheduler_hooks.rs`) is a line sink:
`fn(context, line_ptr, line_len)`. The line carries no newline. Two sinks exist:

- `failure::STDERR_FAULT_HOOK` writes the line and a newline to stderr. The JIT
  runtime, the AOT shim and the interpreter's program runs install it.
- the interpreter's `macro_fault_hook` records the line as the run's callback
  error. A macro expansion runs with it, so a panic during expansion is a
  compile error carrying the failure line, never a program exit.

## Ending the process

Each path ends the failed process the way it ends a completed one; none of them
uses a signal or a trap.

- **Native code (run and build).** After a call to a `never` extern,
  `lower_extern_generic` emits `end_failed_process`: it loads the process's
  `failed` byte (`PROCESS_FAILED_OFFSET`), traps if it is clear (an extern broke
  its `never` contract), and otherwise returns 0. Native code is
  continuation-passing, so the return unwinds to the scheduler, which finds no
  runnable closure and marks the process exited. `Term::Halt`, which lowering
  emits only for dispatch traps (`function_clause`, `case_clause`,
  `match_error` and the like), calls `fz_panic` with its reason atom and returns
  0 the same way.
- **Interpreter.** A `never` extern answers `ExternCallValue::ProcessFailed`
  when the process is marked failed, and an error naming the broken contract
  when it is not. The executable step becomes `BackendRunStep::Failed`. A clause
  miss and `BackendTail::Halt` call `fail_with_atom`, which panics with the
  reason atom through the same export. The drive loop exits a failed process
  through `exit_backend_process` with `ProcessExit::Failed`: destructors drain,
  the exit record is emitted, and `halt_value` is left unset.

Other processes keep running: a failed spawned process prints its line and
ends, and the scheduler carries on until idle.

## Exit status

The main process decides the program's exit status.

- `Compiler2::run_root_jit` and `run_root_interp` answer
  `Err(RunFailure::MainFailed)` when the main process failed.
  `RunFailure::Error(message)` is reserved for runs that could not complete
  (a compile failure, an interpreter contract violation).
- The CLI maps `MainFailed` to exit 1 with nothing more to print: the failure
  line is already on stderr. `Error` prints `fz2 <command>: <message>` and
  exits 1, or 75 for an interpreter path that is not yet supported.
- `fz_aot_run_main` returns `i32::from(process.failed)` for the main process.

The fixture matrix pins this: an `expect: abort` fixture must exit exactly 1.

## Observing a failure

`Process.failed` is projected into the `fz.runtime.process_exited` event as
`ExitRecord.failed` and as the JSONL field `failed`. See
[runtime telemetry](runtime-telemetry.md).

## Where it lives

- `runtime/src/failure.rs` — `failure_line`, `fz_panic`, `STDERR_FAULT_HOOK`.
- `lib/kernel.fz` — `panic/1`, `raise/1`, `raise/2`.
- `src/compiler2/native_codegen/prim.rs` — `end_failed_process`.
- `src/compiler2/native_codegen/terminator.rs` — `emit_halt`.
- `src/ir_interp/backend.rs` — `fail_with_atom`, `exit_backend_process`,
  `BackendRun`, `macro_fault_hook`.
- `src/compiler2/compiler.rs` — `RunFailure`.
