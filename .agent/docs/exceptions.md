# Exceptions

A raise takes one route on every execution path: `raise` in
`runtime/src/failure.rs`, entered through `fz_panic`, `fz_raise_kind`,
`fz_raise` or `fz_raise_showing`. This doc
covers that route end to end: the primitive and the three kinds of raise, the
handler stack a `try` pushes, how a raise reaches the nearest handler on each
path, what `try` with `rescue` and `catch` lowers to, the line an uncaught raise
prints, how each driver ends a failed process, and the exit status that
follows.

## The primitive

`Kernel.panic/1` and `Kernel.raise_kind/2` are the raise primitives. `panic`
wraps `extern "fz" defp fz_panic(any) :: never`, whose physical export is
`fz_runtime::failure::fz_panic(process, value_ref)`; `raise_kind` wraps
`extern "fz" defp fz_raise_kind(any, any) :: never`, whose export is
`fz_raise_kind(process, kind_ref, value_ref)`. `fz_panic` is `raise` with kind
`error`; `fz_raise_kind` reads the kind from its atom and is `raise` with it.
`raise_exception(process, name, message)` builds an exception map and is `raise`
with kind `error`. There is one route behind all of them, which:

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

`throw/1`, `exit/1` and `raise_kind/2` are plain fz code in `lib/kernel.fz`:
`throw(v)` is `raise_kind(:throw, v)`, `exit(r)` is `raise_kind(:exit, r)`, and
`raise_kind(kind, value)` is `fz_raise_kind(kind, value)`. A kind that is not one of
the three is itself an error, `:badarg`. `reraise(exception, stacktrace)` is
`panic(exception)`: fz carries no stacktraces, so the second argument is
accepted and ignored. `raise_kind/2` is not Elixir's; a `try` whose handler
matches nothing continues the raise through it, which is how the original kind
survives. Because it is public Kernel surface, a program can call it too.

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
  template)` pushes it at the start of the try body (`emit_try` in
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
  shows the subject) and then the same.
  The raising frame returns 0, as a yield does, and every frame above it
  returns that 0 to the quantum entry: the machine frames between the `try` and
  the raise are gone before the handler runs, so a loop that raises on every
  iteration uses the same stack for each. The entry is `Process::run_quantum`,
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
  plan's exception through `failure::raise_exception` and continues in
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
  value as it is, with no `ErlangError` wrap. The miss row re-raises the
  delivered kind and value through `Kernel.raise_kind/2`, so a raise no clause
  takes continues to the next handler out by the route it arrived by, and a
  throw stays a throw;
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
Try#outer {                      handler: A ; panic(raised)
  body: Try#inner {              handler: dispatch over R
          body: B ; PopHandler ; case value of E
        }
        PopHandler
}
A                                (success path, after the join)
```

- `after` is the outermost layer, so `try ... rescue ... after` is two nested
  `Try` steps and `try ... after` alone is one. The outer handler's only row
  runs the after body and re-raises its first two params through the same
  `Kernel.raise_kind/2` call the handler miss makes, so the original exception
  continues outward by the route it arrived by: a raise through an `after` is
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
  clause matches raises `%TryClauseError{term: value}`. Its `message` is the
  lead alone, `no try clause matching:`; the term is in `e.term`.
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
through `fz_runtime::failure::raise_exception`, which raises the exception map
exactly as `raise/2` does, so the raise goes to the nearest handler, a `rescue`
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

Other processes keep running: a failed spawned process prints its line and
ends, and the scheduler carries on until idle. The sink does not know which
process is main, so a spawned process that exits with a reason that is not a
shutdown prints its `** (exit)` line; Elixir prints nothing for that, and prints
an uncaught spawned throw as `** (ErlangError) Erlang error: {:nocatch, value}`.

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
  `RunFailure::from_main_status(status)`: `Ok` for status 0,
  `Err(RunFailure::MainFailed)` for 1 and `Err(RunFailure::MainExited(n))` for
  any other. `RunFailure::Error(message)` is reserved for runs that could not
  complete (a compile failure, an interpreter contract violation).
- The CLI maps `MainFailed` to exit 1 and `MainExited(n)` to exit `n`, with
  nothing more to print: the failure line, if any, is already on stderr. `Error`
  prints `fz2 <command>: <message>` and exits 1, or 75 for an interpreter path
  that is not yet supported.
- `fz_aot_run_main` returns `process.exit_status` for the main process.

The fixture matrix pins what it can: an `expect: abort` fixture must exit exactly
1, and a success fixture 0, which covers `exit(:normal)` and `exit(:shutdown)`
(`00810`, `00811`). The other statuses are pinned in `exec/runtime_test.rs`
(`run` and `interp`, through `RunFailure` and the exit record) and in
`tests/fz2_cli.rs` (the process exit status and stderr of `fz2 run`,
`fz2 interp` and a program built by `fz2 build`).

## Observing

`fz_raise` reports every raise, caught or not, as `fz.runtime.raise` carrying a
`Raise { kind, exception, handler_depth }` (`runtime/src/telemetry.rs`): the
kind is `error`, `throw` or `exit`, the exception name is empty for a throw and
an exit, and depth zero is an uncaught raise. `Process::ended_in_failure` and
`raises_delivered` are projected into `fz.runtime.process_exited` as
`ExitRecord.failed` and `ExitRecord.raises_delivered`. See
[runtime telemetry](runtime-telemetry.md).
`exec/runtime_test.rs` observes both on the `run` and `interp` paths.

## Where it lives

- `runtime/src/failure.rs` — `RaiseKind`, `failure_line`, `exit_status`,
  `fz_panic`, `fz_raise_kind`, `raise_exception`, `message_showing`,
  `fz_raise`, `fz_raise_showing`, `STDERR_FAULT_HOOK`.
- `src/dispatch_matrix/pattern/last_resort.rs` — `LastResort`.
- `runtime/src/process.rs` — `Handler`, `Raised`, `handlers`, `raised`,
  `delivered`, `raises_delivered`, `exit_status`, `push_handler`, `pop_handler`,
  `deliver_handler`, `run_quantum`, `diverged`.
- `runtime/src/ir_runtime.rs` — `fz_try_push`, `fz_try_pop`.
- `runtime/src/process_abi.rs` — `PROCESS_DELIVERED_OFFSET`, read by
  `continue_after_raise`.
- `lib/kernel.fz` — `panic/1`, `raise/1`, `raise/2`, `inspect/1`, `throw/1`,
  `exit/1`, `reraise/2`, `raise_kind/2`; `lib/runtime.fz` lists the raise
  functions for auto-import.
- `src/ast/mod.rs` — `Expr::Try`, `RescueClause`, `CatchClause`.
- `src/compiler2/quoted_function.rs` — `decode_try`, `decode_rescue_head`,
  `decode_catch_clauses`.
- `src/compiler2/frontdoor.rs` — `parse_do_section` (`ClauseKind::Params` for
  `catch`).
- `src/compiler2/source_sugar.rs` — the `in` rewrite and its operator stamp.
- `src/compiler2/jobs/body.rs` — `lower_try`, `lower_handled`, `handler_arms`, `rescue_arms`, `reraise_block`, `push_try_else`.
- `src/compiler2/jobs/native.rs` — `raise_last_resort` (emits `Term::Raise`).
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
