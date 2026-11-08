# Exceptions

A raise takes one route on every execution path: `fz_panic`. This doc covers
that route end to end: the primitive, the handler stack a `try` pushes, how a
raise reaches the nearest handler on each path, what `try`/`rescue` lowers to,
the line an uncaught raise prints, how each driver ends a failed process, and
the exit status that follows.

## The primitive

`Kernel.panic/1` is the one raise primitive. It wraps
`extern "fz" defp fz_panic(any) :: never`, whose physical export is
`fz_runtime::failure::fz_panic(process, value_ref)`. The export:

1. reports the raise to the execution context's raise observer, `ExecCtx.raise`
   (kind, exception name, handler depth);
2. pops the top handler, if any, and delivers the raise to it (below);
3. with no handler, renders the value as its failure line, sets
   `Process.failed = true`, and hands the line to the fault sink `ExecCtx.fault`;
4. returns.

The export returns so each caller can continue the way its path continues
after a call that cannot return. Nothing after a panic runs in the raising
code.

`Kernel.raise/1` and `Kernel.raise/2` are plain fz code over `panic`.
`raise(name, message)` panics with the exception map
`%{__struct__: name, __exception__: true, message: message}`;
`raise(message)` is `raise(RuntimeError, message)`. Dispatch traps
(`function_clause`, `case_clause`, `match_error` and the like) panic with their
reason atom through the same export, so a clause miss inside a `try` is
rescuable like any other raise.

## The handler stack

`Process.handlers: Vec<Handler>` (`runtime/src/process.rs`) is the stack of
handlers a raise can reach, innermost last. A `try` pushes one frame on entry
and pops it when its body completes; `fz_panic` pops the top frame and delivers
to it. The stack is a GC root beside `runnable` and the mailbox: a boundary
collection forwards every compiled handler on it (`Process::collect`).

Every handler receives the same three values: the kind atom (`:error` for a
`raise`/`panic`), the raised value, and the exception's name atom (`nil` when
the value is not an exception map).

- `Handler::Closure(template)` is compiled code's frame. `fz_try_push(process,
  template)` pushes it at the start of the try body (`emit_try` in
  `native_codegen/terminator.rs`); `fz_try_pop` pops it where the body's
  continuation begins. Delivery materializes the template with the three values
  as its bound values (`materialize_outcome_closure`, the receive-outcome
  machinery) and queues the result as the process's `runnable` closure.
- `Handler::Interpreter` is the interpreter's frame. The interpreter keeps a
  `BackendContinuation` with `handler: true` on its continuation stack and
  pushes this marker beside it; delivery leaves the three values in
  `Process::raised` for the interpreter to take when the panicking extern
  returns.

`Process::raises_delivered` counts the raises a handler took.

## Reaching the handler

- **Native code (run and build).** After a call to a `never` extern,
  `lower_extern_generic` emits `continue_after_raise`
  (`native_codegen/prim.rs`); `Term::Halt` emits `fz_panic` and then the same.
  It calls `fz_take_raised_handler`, which hands back the queued handler as a
  closure ref and clears the slot. With a handler, native code runs it in the
  raising call's place through the same tail call `fz_resume` would make
  (`emit_resume_closure`), inside the current quantum: the reduction budget keeps
  counting, so a loop that raises and rescues every iteration yields through its
  ordinary back edges. With none, the process has failed and the code returns 0
  to the scheduler, which finds no runnable closure and marks the process
  exited. A process that neither failed nor queued a handler was ended by an
  extern that broke its `never` contract, which traps.
- **Interpreter.** A `never` extern answers `ExternCallValue::ProcessFailed`
  when the process has diverged (`Process::diverged`: failed, or a raise is
  waiting), and an error naming the broken contract when it has not.
  `after_panic` (`ir_interp/backend.rs`) takes `Process::raised`, pops the
  continuation frames above the handler frame, and runs the handler entry with
  the three values as its params. With no raise waiting, the step becomes
  `BackendRunStep::Failed` and the drive loop exits the process through
  `exit_backend_process` with `ProcessExit::Failed`. A value reaching a handler
  frame is a contract violation: the try body pops its frame first.

## What `try` lowers to

`Expr::Try { body, rescue: Vec<RescueClause> }` (`src/ast/mod.rs`) lowers in
`jobs/body.rs::lower_try` to one `ExprStep::Try`:

- the body block, ending in `ExprStep::PopHandler`, whose continuation delivers
  the body's value to the join;
- the handler block: a pattern dispatch over the three params `(kind, value,
  name)` built from the rescue heads, one row per exception a clause names, in
  source order. A clause that admits a non-exception value (`ErlangError`, or a
  bare variable) gets a wrap row matching a `nil` name; its arm wraps the value
  in `%ErlangError{original: value}` before the clause body runs. The miss row
  re-raises the value through `Kernel.panic/1`, so a raise no clause takes
  continues to the next handler out by the route it arrived by;
- one join, typed as the union of the body and the arms.

Body calls are non-tail by construction (their continuation pops the handler),
and body bindings do not reach the join. A raise inside a rescue arm runs after
the try's own handler was popped, so the same try never catches it. The
`BackendTail::Try { body, handler }` tail and `ControlEntryOrigin::Handler`
carry this to the backend; `Term::Try { handler, captures, body }` and
`Prim::PopHandler` carry it to native code.

## The rescue head

`decode_rescue_head` (`src/compiler2/quoted_function.rs`) accepts exactly
Elixir's five shapes and nothing else:

| head | binding | exceptions |
|---|---|---|
| `e` | `e` | every exception |
| `Alias` | none | `Alias` |
| `[A, B]` | none | `A`, `B` |
| `e in Alias` | `e` | `Alias` |
| `e in [A, B]` | `e` | `A`, `B` |

Source sugar rewrites `in` to `Enum.member?` before decoding and stamps the
call with the operator it came from; the decoder reads the stamp, so a rescue
head spelled with `in` is seen as `in`. Any other head is Elixir's diagnostic
(`parse/invalid-try`):

```text
invalid "rescue" clause. The clause should match on an alias, a variable or be in the "var in [alias]" format. Got: %{}
```

A `try` with only a `do` block is `missing :catch/:rescue/:after option in
"try"`; a repeated section is `duplicate "rescue" clauses given for "try"`; a
`rescue` section that is not clauses is `invalid "rescue" block in "try", it
expects "pattern -> expr" clauses`. The `catch`, `after` and `else` sections are
refused with `` `try` with `catch` is not yet supported `` (`parse/unsupported`).

## The line

With no handler, `failure_line` prints what Elixir prints for an uncaught
exception, without the stacktrace:

| value | line |
|---|---|
| a map with `__exception__: true`, an atom `__struct__` and a byte-aligned binary `message` | `** (Name) message` |
| anything else | `** (ErlangError) Erlang error: <value>` |

`Name` and `<value>` use the dbg rendering, so a module name prints as its alias
(`ArgumentError`, not `:"Elixir.ArgumentError"`). A reason atom such as
`:badarg` prints as `** (ErlangError) Erlang error: :badarg`, as
`:erlang.error(:badarg)` would in Elixir. Elixir normalizes a few reason atoms
into named exceptions (`:badarith` becomes `ArithmeticError`, a clause miss
becomes `FunctionClauseError`); fz does not, so `rescue e in ErlangError`
takes those and `e.original` is the reason.

## The fault sink

`FaultHook` (`runtime/src/scheduler_hooks.rs`) is a line sink:
`fn(context, line_ptr, line_len)`. The line carries no newline. Two sinks exist:

- `failure::STDERR_FAULT_HOOK` writes the line and a newline to stderr. The JIT
  runtime, the AOT shim and the interpreter's program runs install it.
- the interpreter's `macro_fault_hook` records the line as the run's callback
  error. A macro expansion runs with it, so a panic during expansion is a
  compile error carrying the failure line, never a program exit.

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

## Observing

`fz_panic` reports every raise, caught or not, as `fz.runtime.raise` carrying a
`Raise { kind, exception, handler_depth }` (`runtime/src/telemetry.rs`); depth zero is an uncaught
raise. `Process.failed` and `raises_delivered` are projected into
`fz.runtime.process_exited` as `ExitRecord.failed` and
`ExitRecord.raises_delivered`. See [runtime telemetry](runtime-telemetry.md).
`exec/runtime_test.rs` observes both on the `run` and `interp` paths.

## Where it lives

- `runtime/src/failure.rs` — `failure_line`, `fz_panic`, `STDERR_FAULT_HOOK`.
- `runtime/src/process.rs` — `Handler`, `Raised`, `handlers`, `raised`,
  `raises_delivered`, `push_handler`, `pop_handler`, `diverged`.
- `runtime/src/ir_runtime.rs` — `fz_try_push`, `fz_try_pop`,
  `fz_take_raised_handler`.
- `lib/kernel.fz` — `panic/1`, `raise/1`, `raise/2`.
- `src/ast/mod.rs` — `Expr::Try`, `RescueClause`.
- `src/compiler2/quoted_function.rs` — `decode_try`, `decode_rescue_head`.
- `src/compiler2/source_sugar.rs` — the `in` rewrite and its operator stamp.
- `src/compiler2/jobs/body.rs` — `lower_try`, `rescue_arms`, `reraise_block`.
- `src/compiler2/native_codegen/terminator.rs` — `emit_try`, `emit_halt`,
  `emit_resume_closure`.
- `src/compiler2/native_codegen/prim.rs` — `continue_after_raise`,
  `Prim::PopHandler`.
- `src/ir_interp/backend.rs` — `after_panic`, `fail_with_atom`,
  `exit_backend_process`, `BackendRun`, `macro_fault_hook`.
- `src/compiler2/compiler.rs` — `RunFailure`.
- `fixtures/00815` through `fixtures/00831` — the rescue shapes, nesting,
  re-raise, the uncaught raise, a try in a spawned process, the raising loop,
  the allocating try body, and the refused `try` forms.
