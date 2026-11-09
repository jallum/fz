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

`Kernel.raise/1` and `Kernel.raise/2` are the door every library failure takes.
`raise(name, message)` is `extern "fz" defp fz_raise(any, any) :: never`, whose
physical export `fz_runtime::failure::fz_raise` panics with the exception map
`%{__struct__: name, __exception__: true, message: message}`;
`raise(message)` is `raise(RuntimeError, message)`. Both are imported into
every namespace by `lib/runtime.fz`, beside `panic/1`. Outside `assert` and
`refute`, the library calls `panic/1` only where Elixir itself raises a raw
Erlang error (`JSON.encode!/1` of an invalid UTF-8 binary).

`Kernel.inspect/1` renders a value as `dbg` does, as a binary, for the messages
that show one; a map prints as `%{:a => 1}`, not `%{a: 1}`.

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
into named exceptions (`:badarith` becomes `ArithmeticError`); fz does not, so
the library raises the named exception itself.

## The library's exceptions

Every library failure raises the exception, with the message, Elixir does.
`Kernel.raise/2` is the only caller of the primitive; a clause that cannot
match is left to the decision's own `FunctionClauseError`.

| failure | prints |
|---|---|
| `byte_size/1`, `tuple_size/1`, `length/1`, `elem/2` of the wrong kind | `** (ArgumentError) errors were found at the given arguments:` then the argument and what is wrong with it |
| `map_size/1` of a non-map | `** (BadMapError) expected a map, got:` then the value |
| `elem/2` with a non-integer index | `** (ArithmeticError) bad argument in arithmetic expression`, as Elixir adds one to the index |
| `div/2`, `rem/2`, `/` and the other arithmetic that fails | `** (ArithmeticError) bad argument in arithmetic expression` |
| `Map.fetch!/2`, `Map.update!/3`, `Keyword.fetch!/2` | `** (KeyError) key <key> not found in:` then the collection |
| `Enum.max/1` and the other empty reductions | `** (Enum.EmptyError) empty error` |
| `Enum.fetch!/2` | `** (Enum.OutOfBoundsError) out of bounds error at position <n> when traversing enumerable <enumerable>` |
| `Enum.map_every/3`, `take_every/2`, `drop_every/2` with a negative step | `** (FunctionClauseError) no function clause matching in Enum.map_every/3` |
| `String.to_integer/1`, `String.to_float/1` | `** (ArgumentError) errors were found at the given arguments:` then `not a textual representation of an integer` / `of a float` |
| `JSON.decode!/1` | `** (JSON.DecodeError) invalid byte <n> at position (byte offset) <at>`, `unexpected end of JSON binary at ...` or `unexpected sequence <bytes> at ...` |
| `JSON.encode!/1` of a value or key with no encoding | `** (Protocol.UndefinedError)` for `JSON.Encoder`, or for `String.Chars` on a key |
| `JSON.encode!/1` of an invalid UTF-8 binary | `** (ErlangError) Erlang error: {:invalid_byte, <byte>}` or `:unexpected_end` |
| `JSON.encode!/1` of a bitstring that is not a binary | `** (FunctionClauseError) no function clause matching in :elixir_json.encode_binary/1` |
| `to_string/1` of a bitstring that is not a binary | `** (Protocol.UndefinedError) protocol String.Chars not implemented for BitString, cannot convert a bitstring to a string` |
| `File` bang functions | `** (File.Error)`, `File.CopyError`, `File.RenameError` or `File.LinkError`, with reason `I/O error` |

`assert/1,2` and `refute/1,2` are not Elixir's `Kernel`; they panic with their
message as the raw reason.

## Decisions that run out of clauses

Every decision is a dispatch plan, and a plan that can fail carries the
exception its arm of last resort raises: `PatternDispatchPlan.last_resort`, a
`LastResort` (`src/dispatch_matrix/pattern/last_resort.rs`) set when the plan's
rows are built (`SourcePatternRows::raising`). `=` is a decision like the others:
its pattern is a one-row plan. Reaching the plan's fail raises the exception
through `fz_runtime::failure::raise`, which panics with the exception map exactly
as `raise/2` does, so it prints the same line and ends the process the same way.

| decision | prints |
|---|---|
| a function's clauses | `** (FunctionClauseError) no function clause matching in M.f/1` |
| an anonymous function's clauses | `** (FunctionClauseError) no function clause matching in anonymous fn/1 in M.g/0` |
| `pattern = value` | `** (MatchError) no match of right hand side value:` then the value |
| `case` | `** (CaseClauseError) no case clause matching:` then the value |
| `cond` | `** (CondClauseError) no cond clause evaluated to a truthy value` |
| `with`'s `else` | `** (WithClauseError) no with clause matching:` then the value |
| `and` / `or` on a non-boolean | `** (BadBooleanError) expected a boolean on left-side of "and", got:` then the value |
| `not` on a non-boolean | `** (ArgumentError) argument error` |

A message that shows a value is Elixir's multi-line form: the lead, a blank
line, and the value rendered by dbg and indented four spaces
(`failure::message_showing`). The value is the plan's input 0.

A `with` whose binding fails without an `else`, and a `receive`, have no last
resort: the first yields the value, the second waits for another message.

A fail that no plan can reach is not a raise. An entry with no clause to run, a
call dispatch with no matching callee, and a construction-selection miss end in
`Term::Unreachable` in native code, which traps, and in an `internal error`
from the interpreter.

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
  runnable closure and marks the process exited. `Term::Raise`, which lowering
  emits at a decision's arm of last resort, calls `fz_raise` (or
  `fz_raise_showing` when the message shows the subject) and returns 0 the same
  way.
- **Interpreter.** A `never` extern answers `ExternCallValue::ProcessFailed`
  when the process is marked failed, and an error naming the broken contract
  when it is not. The executable step becomes `BackendRunStep::Failed`. A
  decision's arm of last resort calls `raise_last_resort`, which raises the
  plan's exception through `failure::raise`. The drive loop exits a failed process
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

- `runtime/src/failure.rs` — `failure_line`, `fz_panic`, `raise`,
  `message_showing`, `fz_raise`, `fz_raise_showing`, `STDERR_FAULT_HOOK`.
- `src/dispatch_matrix/pattern/last_resort.rs` — `LastResort`.
- `lib/kernel.fz` — `panic/1`, `raise/1`, `raise/2`, `inspect/1`.
- `src/compiler2/native_codegen/prim.rs` — `end_failed_process`.
- `src/compiler2/jobs/native.rs` — `raise_last_resort` (emits `Term::Raise`).
- `src/compiler2/native_codegen/terminator.rs` — `emit_raise`.
- `src/ir_interp/backend.rs` — `raise_last_resort`, `exit_backend_process`,
  `BackendRun`, `macro_fault_hook`.
- `src/compiler2/compiler.rs` — `RunFailure`.
