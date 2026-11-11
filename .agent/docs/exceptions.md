# Exceptions

A raise takes one route on every execution path: `raise` in
`runtime/src/failure.rs`, entered through `fz_panic`, `fz_throw`, `fz_exit`,
`fz_reraise`, `fz_raise` or `fz_raise_showing`. This doc
covers that route end to end: the primitive and the three kinds of raise, the
handler stack a `try` pushes, how a raise reaches the nearest handler on each
path, what `try` with `rescue` and `catch` lowers to, the line an uncaught raise
prints, how each driver ends a failed process, and the exit status that
follows.

## The primitive

`Kernel.panic/1`, `Kernel.throw/1` and `Kernel.exit/1` are the raise
primitives, one per kind. Each wraps an `extern "fz" defp ... :: never` whose
physical export is `fz_runtime::failure::fz_panic(process, value_ref)`,
`fz_throw(process, value_ref)` or `fz_exit(process, value_ref)`; each is `raise`
with its fixed kind (`error`, `throw`, `exit`). Nothing in Kernel takes a kind
from a program. The compiler continues a raise a handler was delivered through
`fz_reraise(process, kind_ref, value_ref)`, which reads the kind from the atom
the handler received and is `raise` with it; a kind the runtime never delivers
panics, as a fault in the compiler.
`raise_exception(process, name, message)` and `raise_exception_showing(process,
name, lead, term)` each build an exception map and are `raise` with kind
`error`. There is one route behind all of them, which:

1. reports the raise to the execution context's raise observer, `ExecCtx.raise`
   (kind, exception name, handler depth);
2. pops the top handler, if any, and delivers the raise to it (below);
3. with no handler, records the exit status, renders the raise as its failure
   line, if it has one, sets `Process.failed = true`, and hands the line to the
   fault sink `ExecCtx.fault`;
4. returns.

The export returns so each caller can continue the way its path continues
after a call that cannot return. Nothing after a panic runs in the raising
code.

`Kernel.raise/1` and `Kernel.raise/2` are the door every library failure takes.
`raise(name, message)` is `extern "fz" defp fz_raise(any, any) :: never`, whose
physical export `fz_runtime::failure::fz_raise` calls `raise_exception`, which
raises the exception map
`%{__struct__: name, __exception__: true, message: message}`;
`raise(message)` is `raise(RuntimeError, message)`. Both are imported into every
namespace by `lib/runtime.fz`, beside `panic/1`. Outside `assert` and `refute`,
the library calls `panic/1` only where Elixir itself raises a raw Erlang error
(`JSON.encode!/1` of an invalid UTF-8 binary).

`Kernel.inspect/1` renders a value as `dbg` does, as a binary, for the messages
that show one; a map prints as `%{a: 1}`, as in Elixir. `Kernel.inspect/2`
checks its options in fz source, where `raise/2` can fail the process: an
extern that returns a value cannot, because the caller would carry on past the
failure.

A decision that runs out of clauses raises through the same route (below), so a
clause miss inside a `try` is rescuable like any other raise.

## The kinds

A raise has a kind, `error`, `throw` or `exit`, a runtime enum
(`RaiseKind`) delivered to handlers as its atom. It enters through the primitive
that raised:

| source | kind |
|---|---|
| `raise/1,2`, `panic/1`, `reraise/2`, a decision that runs out of clauses | `error` |
| `throw(value)` | `throw` |
| `exit(reason)` | `exit` |
| a `try` that no clause matches, or an `after` | the kind the raise arrived with |

`throw/1` and `exit/1` are plain fz code in `lib/kernel.fz`: `throw(v)` is
`fz_throw(v)` and `exit(r)` is `fz_exit(r)`, each over a fixed-kind extern.
`reraise(exception, stacktrace)` is `panic(exception)`: fz carries no
stacktraces, so the second argument is accepted and ignored. A `try` whose
handler matches nothing, and an `after`, continue the raise with `fz_reraise`
(below), which is how the original kind survives; no function a program can
call takes a kind.

## The handler stack

`Process.handlers: Vec<Handler>` (`runtime/src/process.rs`) is the stack of
handlers a raise can reach, innermost last. A `try` pushes one frame on entry
and pops it when its body completes; a raise pops the top frame and delivers
to it. The stack is a GC root beside `runnable` and the mailbox: a boundary
collection forwards every compiled handler on it (`Process::collect`),
and the `delivered` slot below.

Every handler receives the same three values: the kind atom (`:error`,
`:throw` or `:exit`), the raised value, and the exception's name atom (`nil`
when the value is not an exception map, which a throw or an exit's value never
is by kind, whatever it holds).

- `Handler::Closure(template)` is compiled code's frame. `fz_try_push(process,
  template)` takes the template as the closure reference word codegen holds a
  heap closure in, and the frame keeps that reference, literal bit included. It pushes it at the start of the try body (`emit_try` in
  `native_codegen/terminator.rs`); `fz_try_pop` pops it where the body's
  continuation begins. Delivery materializes the template with the three values
  as its bound values (`materialize_outcome_closure`, the receive-outcome
  machinery) and stores the result in `Process::delivered`. That slot is not
  `runnable`: `runnable` means queued for the scheduler, `delivered` means a
  handler the current quantum is about to run.
- `Handler::Interpreter` is the interpreter's frame. The interpreter keeps a
  `BackendContinuation` with `handler: true` on its continuation stack and
  pushes this marker beside it; delivery leaves the three values in
  `Process::raised` for the interpreter to take when the panicking extern
  returns.

`Process::raises_delivered` counts the raises a handler took.

## Reaching the handler

- **Native code (run and build).** After a call to a `never` extern,
  `lower_extern_generic` emits `continue_after_raise`
  (`native_codegen/prim.rs`); `Term::Raise`, which lowering emits at a decision's
  arm of last resort, calls `fz_raise` (or `fz_raise_showing` when the message
  shows the subject) and then the same; `Term::Reraise`, which lowering emits
  at a handler's arm of last resort, calls `fz_reraise` with the plan's first
  two inputs and then the same.
  The raising frame returns 0, as a yield does, and every frame above it
  returns that 0 to the quantum entry: the machine frames between the `try` and
  the raise are gone before the handler runs, so a loop that raises on every
  iteration uses the same stack for each: its raises are delivered at the entry
  path's depth, the resumed-handler path's depth and the resumed-yield paths'
  depths, and never deeper as the iterations go (`stack_bytes` on the raise
  event shows it). The entry is `Process::run_quantum`,
  which both the JIT driver (`CompiledModule::run_quantum`) and the AOT driver
  (`dispatch_quantum`) call. When the code unwinds, `run_quantum` takes
  `Process::delivered` and, if a handler is there, resumes it at once in the same
  quantum: it does not pass through the scheduler's run queue and does not reset
  the reduction budget, so a loop that raises and rescues every iteration still
  yields through its ordinary back edges. Every other way out of a quantum (a
  reduction or explicit yield, a receive park, process end, a failure) leaves
  `delivered` empty and hands the process back to the scheduler. With no
  handler the process has failed and the scheduler finds no runnable closure
  and marks the process exited. A process that neither failed nor has a
  delivered handler was ended by an extern that broke its `never` contract,
  which traps.
- **Interpreter.** A `never` extern answers `ExternCallValue::ProcessFailed`
  when the process has diverged (`Process::diverged`: failed, or a raise is
  waiting), and an error naming the broken contract when it has not.
  A decision's arm of last resort calls `raise_last_resort`, which raises the
  plan's exception through `failure::raise_exception`, or
  `failure::raise_exception_showing` with the subject, and continues in
  `after_panic`. `after_panic` (`ir_interp/backend.rs`) takes `Process::raised`, pops the
  continuation frames above the handler frame, and runs the handler entry with
  the three values as its params. With no raise waiting, the step becomes
  `BackendRunStep::Failed` and the drive loop exits the process through
  `exit_backend_process` with `ProcessExit::Failed`. A value reaching a handler
  frame is a contract violation: the try body pops its frame first.

## What `try` lowers to

`Expr::Try { body, rescue, catch, else_clauses, after }` (`src/ast/mod.rs`)
lowers in `jobs/body.rs::lower_try`. `rescue` and `catch` together are one
`ExprStep::Try` (`lower_handled`); `after` and `else` are built from that step
and from the dispatch step, below. A `try` with `rescue` or `catch` has:

- the body block, which pops its handler (`ExprStep::PopHandler`) as soon as the
  body completes and delivers the body's value to the join;
- the handler block: a pattern dispatch over the three params `(kind, value,
  name)`: first the rescue rows, one row per exception a clause names, then one
  row per catch clause, in source order within each (`handler_arms`, as Elixir
  orders `Rescue ++ Catch`). Rescue rows match kind `error` only, so a throw or
  an exit never matches one. A rescue clause that admits a non-exception value
  (`ErlangError`, or a bare variable) gets a wrap row matching a `nil` name; its
  arm wraps the value in `%ErlangError{original: value}` before the clause body
  runs. A catch row is `[kind pattern, value pattern, _]` with the clause's guard
  as the row's guard; a clause written with one head is a clause for throws, so
  its kind pattern is the atom `:throw`, and `catch :error, r` binds the raised
  value as it is, with no `ErlangError` wrap. The dispatch has no miss row:
  its last resort is `LastResort::Reraise`, which continues the delivered kind
  and value (the plan's first two inputs) to the next handler out by the route
  it arrived by, so a throw stays a throw;
- one join, typed as the union of the body and the arms.

Body calls are non-tail by construction (their continuation pops the handler),
and body bindings do not reach the join. A raise inside a rescue arm runs after
the try's own handler was popped, so the same try never catches it. The
`BackendTail::Try { body, handler }` tail and `ControlEntryOrigin::Handler`
carry this to the backend; `Term::Try { handler, captures, body }` and
`Prim::PopHandler` carry it to native code.

## `after` and `else`

Neither adds a runtime concept. Both are written in the vocabulary above, in the
nesting Erlang's `try` compiles to (`v3_core`):

```text
try do B rescue R else E after A end
  =>
Try#outer {                      handler: A ; dispatch (no rows) -> reraise
  body: Try#inner {              handler: dispatch over R
          body: B ; PopHandler ; case value of E
        }
        PopHandler
}
A                                (success path, after the join)
```

- `after` is the outermost layer, so `try ... rescue ... after` is two nested
  `Try` steps and `try ... after` alone is one. The outer handler
  runs the after body, then a dispatch over its first two params (kind and
  value) with no rows, whose last resort is the same re-raise the handler miss
  uses, so the original exception continues outward by the route it arrived by: a raise through an `after` is
  two `fz.runtime.raise` events, the original at the full handler depth and the
  re-raise one frame shallower. The success path runs the after body once, right
  after the outer join; its value is dropped, so the try's value is the body's
  (or the rescue's, or the `else`'s). The after body is lowered once per way
  out, so the code it holds, a closure included, appears twice in the body. An
  exception raised in the after body on either path leaves the outer handler
  already popped, so it replaces the one in flight.
- `else` clauses are a case over the body's value placed after the inner
  `PopHandler`, still inside the body block, so a rescue arm's value never
  reaches them and a raise in an `else` arm or in the miss is outside the
  `rescue`. It is inside the `after` layer, so `after` still runs. A value no
  clause matches reaches the plan's `LastResort`, like any other decision (below):
  it raises `TryClauseError` with the full banner as its `message` and the value
  in `e.term`.
- A `try` with `else` and none of `rescue`, `catch` and `after` has no handler
  to push: it lowers as the case it is, and carries Elixir's warning
  `"else" shouldn't be used as the only clause in "try", use "case" instead`
  (`lower/try-else-only`).
- Bindings made in the body or the after body do not reach what follows the
  `try`; reading one is `lower/unbound`.

The `else` section must be `->` clauses (`expected -> clauses for :else in
"try"`) and `after` and `else`, like `rescue`, may appear once.

## The catch head

`decode_catch_clauses` (`src/compiler2/quoted_function.rs`) reads each clause's
heads the way Elixir's `elixir_erl_try` does: one head is a throw, two are
`kind, value`, and a trailing `when guard` belongs to the clause. The front door
reads a `catch` section's clauses with parameter-style heads (`ClauseKind::Params`
in `frontdoor.rs`, the heads `fn` takes), so `a, b when g -> body` parses; every
other section keeps single-pattern heads. Misuse carries Elixir's text
(`parse/invalid-try`):

```text
expected one or two args for :catch clauses (->) in "try"
expected -> clauses for :catch in "try"
```

The first is a clause with no head or three or more, the second a `catch`
section that is not `->` clauses (an empty `catch` included). A repeated `catch`
section is `duplicate "catch" clauses given for "try"`.

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
expects "pattern -> expr" clauses`.

## The line

With no handler, `failure_line` prints what Elixir prints for an uncaught
raise, without the stacktrace:

| kind and value | line |
|---|---|
| `error`, a map with `__exception__: true`, an atom `__struct__` and a byte-aligned binary `message` | `** (Name) message` |
| `error`, anything else | `** (ErlangError) Erlang error: <value>` |
| `throw` | `** (throw) <value>` |
| `exit`, a reason that is not a shutdown | `** (exit) <reason>` |
| `exit`, a shutdown reason (below) | no line |

`Name`, `<value>` and `<reason>` use `inspect`, so a module name prints as its alias
(`ArgumentError`, not `:"Elixir.ArgumentError"`). A map whose keys are atoms may
list them in another order than Elixir, which orders atom keys by the atom
table; the fixtures avoid such maps. A reason atom such as
`:badarg` prints as `** (ErlangError) Erlang error: :badarg`, as
`:erlang.error(:badarg)` would in Elixir. Elixir normalizes a few reason atoms
into named exceptions (`:badarith` becomes `ArithmeticError`); fz does not, so
the library raises the named exception itself, and `rescue e in ErlangError`
takes a raw reason and `e.original` is the reason.

A showing exception (a decision's miss that shows its value, above) is a map with
`term` beside `message`: the line prints the message, `e.term` is the value
itself.

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
through `fz_runtime::failure::raise_exception`, or `raise_exception_showing` when
the message shows the subject, which raise the exception map as `raise/2` does, so the raise goes to the nearest handler, a `rescue`
around the decision catches it, and with no handler it prints the same line and
ends the process the same way.

| decision | prints |
|---|---|
| a function's clauses | `** (FunctionClauseError) no function clause matching in M.f/1` |
| an anonymous function's clauses | `** (FunctionClauseError) no function clause matching in anonymous fn/1 in M.g/0` |
| `pattern = value` | `** (MatchError) no match of right hand side value:` then the value |
| `case` | `** (CaseClauseError) no case clause matching:` then the value |
| `cond` | `** (CondClauseError) no cond clause evaluated to a truthy value` |
| `with`'s `else` | `** (WithClauseError) no with clause matching:` then the value |
| `try`'s `else` | `** (TryClauseError) no try clause matching:` then the value |
| `and` / `or` on a non-boolean | `** (BadBooleanError) expected a boolean on left-side of "and", got:` then the value |
| `not` on a non-boolean | `** (ArgumentError) argument error` |

A message that shows a value is Elixir's multi-line form: the lead, a blank
line, and the value rendered by dbg and indented four spaces
(`failure::raise_exception_showing`), and the exception carries the value itself in
its `term` field, as Elixir's `CaseClauseError`, `MatchError`, `WithClauseError`,
`TryClauseError` and `BadBooleanError` do. The value is the plan's input 0.

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

Other processes keep running while main does: a failed spawned process prints
its line and ends, and the scheduler carries on until main ends, a process halts
(see "How a program ends"), or the run goes idle. The sink does not know which
process is main, so a spawned process that exits with a reason that is not a
shutdown prints its `** (exit)` line; Elixir prints nothing for that, and prints
an uncaught spawned throw as `** (ErlangError) Erlang error: {:nocatch, value}`.

## How a program ends

A program ends when it halts, and its status is the halt's. The scheduler owns
the end: `SchedulingCore` (`sched_core.rs`) records the first `halt(status)`, and
`next_runnable` hands out nothing after it, so every driver's loop stops at the
same place. Two things halt:

- `System.halt/0,1` calls the extern `fz_system_halt(process, status)`
  (`failure.rs`). It reports the status through the `ExecCtx::halt` hook
  (`halt_hook::<S>()`, one instantiation per scheduler type) and ends the calling
  process with `failed` set and `exit_status = status`, the state an uncaught
  raise leaves, with no failure line and no handler search. The raise unwinding
  then runs as for any failed process, so no `catch` or `after` sees a halt.
  `halt(-1)` raises `ArgumentError` in `lib/system.fz` before reaching the extern.
- The main process (`MAIN_PID`) ending, normally or by an uncaught raise, records
  a halt with its `exit_status` through `SchedulingCore::process_ended`. Processes
  still running or waiting when main ends are stopped, as an Elixir script halts
  the VM at its end.

A run that goes idle without a halt, with main blocked forever on a `receive`,
ends with status 0. Every driver then calls `OutputSink::flush`, so a final
partial line reaches stdout on a built binary as well.

## Exit status

The main process decides the program's exit status. A raise no handler takes
ends its process with `Process.exit_status`, which `raise` sets from the kind
and value (`exit_status` in `failure.rs`), following Elixir's CLI
(`Kernel.CLI.exec_fun`):

| uncaught | status | prints |
|---|---|---|
| `raise`, `panic`, a decision with no matching clause, or any `error` | 1 | the `** (...)` line |
| `throw(value)` | 1 | `** (throw) value` |
| `exit(:normal)`, `exit(:shutdown)` | 0 | nothing |
| `exit({:shutdown, n})`, `n` an integer | `n` | nothing |
| `exit({:shutdown, other})` | 0 | nothing |
| `exit(reason)`, any other reason | 1 | `** (exit) reason` |

A status is what the operating system makes of it, so `n` is taken modulo 256.
The code after an `exit` never runs, whatever the status.

- `Compiler2::run_root_jit` and `run_root_interp` end the run with
  `RunFailure::from_main_status(status)`, `status` being the recorded halt (0 for
  a run that never halted): `Ok` for status 0,
  `Err(RunFailure::MainFailed)` for 1 and `Err(RunFailure::MainExited(n))` for
  any other. `RunFailure::Error(message)` is reserved for runs that could not
  complete (a compile failure, an interpreter contract violation).
- The CLI maps `MainFailed` to exit 1 and `MainExited(n)` to exit `n`, with
  nothing more to print: the failure line, if any, is already on stderr. `Error`
  prints `fz2 <command>: <message>` and exits 1, or 75 for an interpreter path
  that is not yet supported.
- `fz_aot_run_main` returns the status its scheduler's core recorded.

The fixture matrix pins what it can: an `expect: abort` fixture must exit exactly
1, and a success fixture 0, which covers `exit(:normal)` and `exit(:shutdown)`
(`00810`, `00811`). The other statuses are pinned in `exec/runtime_test.rs`
(`run` and `interp`, through `RunFailure` and the exit record) and in
`tests/fz2_cli.rs` (the process exit status and stderr of `fz2 run`,
`fz2 interp` and a program built by `fz2 build`).

## Observing

The raise route reports every raise, caught or not, as `fz.runtime.raise`
carrying a `Raise { kind, exception, handler_depth, stack_bytes }`
(`runtime/src/telemetry.rs`): the kind is `error`, `throw` or `exit`, the
exception name is empty for a throw and an exit, depth zero is an uncaught
raise, and `stack_bytes` is the machine stack between the quantum's entry and
the raise. `Process::ended_in_failure` and
`raises_delivered` are projected into `fz.runtime.process_exited` as
`ExitRecord.failed` and `ExitRecord.raises_delivered`. See
[runtime telemetry](runtime-telemetry.md).
`exec/runtime_test.rs` observes both on the `run` and `interp` paths.

## Where it lives

- `runtime/src/failure.rs` — `RaiseKind`, `failure_line`, `exit_status`,
  `fz_panic`, `fz_throw`, `fz_exit`, `reraise`, `fz_reraise`,
  `raise_exception`, `raise_exception_showing`, `fz_raise`,
  `fz_raise_showing`, `STDERR_FAULT_HOOK`.
- `src/dispatch_matrix/pattern/last_resort.rs` — `LastResort`.
- `runtime/src/process.rs` — `Handler`, `Raised`, `handlers`, `raised`,
  `delivered`, `raises_delivered`, `exit_status`, `push_handler`, `pop_handler`,
  `deliver_handler`, `run_quantum`, `diverged`.
- `runtime/src/ir_runtime.rs` — `fz_try_push`, `fz_try_pop`.
- `runtime/src/process_abi.rs` — `PROCESS_DELIVERED_OFFSET`, read by
  `continue_after_raise`.
- `lib/kernel.fz` — `panic/1`, `raise/1`, `raise/2`, `inspect/1`, `throw/1`,
  `exit/1`, `reraise/2`; `lib/runtime.fz` lists the raise
  functions for auto-import.
- `src/ast/mod.rs` — `Expr::Try`, `RescueClause`, `CatchClause`.
- `src/compiler2/quoted_function.rs` — `decode_try`, `decode_rescue_head`,
  `decode_catch_clauses`.
- `src/compiler2/frontdoor.rs` — `parse_do_section` (`ClauseKind::Params` for
  `catch`).
- `src/compiler2/source_sugar.rs` — the `in` rewrite and its operator stamp.
- `src/compiler2/jobs/body.rs` — `lower_try`, `lower_handled`, `handler_arms`, `rescue_arms`, `reraise_block`, `push_try_else`.
- `src/compiler2/jobs/native.rs` — `raise_last_resort` (emits `Term::Raise` and `Term::Reraise`).
- `src/compiler2/native_codegen/terminator.rs` — `emit_try`, `emit_raise`.
- `src/compiler2/native_codegen/prim.rs` — `continue_after_raise`,
  `Prim::PopHandler`.
- `src/ir_interp/backend.rs` — `after_panic`, `raise_last_resort`,
  `exit_backend_process`, `BackendRun`, `macro_fault_hook`.
- `src/compiler2/compiler.rs` — `RunFailure`.
- `fixtures/00815` through `fixtures/00831` — the rescue shapes, nesting,
  re-raise, the uncaught raise, a try in a spawned process, the raising loop,
  the allocating try body, and the refused `try` forms.
- `fixtures/00832` through `fixtures/00840`, with `fixtures/00800` through
  `fixtures/00806` — `after` and `else`.
- `fixtures/00841` through `fixtures/00847` and
  `fixtures/00807` through `fixtures/00814` — `throw`, `exit`, `catch`,
  `reraise/2`, the uncaught lines and statuses, and the refused `catch` forms.
- `fixtures/00848` and `fixtures/00850` — a rescued decision's exception name,
  `term` and message.
