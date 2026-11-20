# Exceptions

A raise takes one route on every execution path: `raise` in
`runtime/src/failure.rs`, entered through `fz_panic`, `fz_throw`, `fz_exit`,
`fz_reraise` or `fz_raise_undefined_function`. This doc covers
that route end to end: the primitive and the three kinds of raise, the handler
stack a `try` pushes, how a raise reaches the nearest handler on each path,
what `try` with `rescue` and `catch` lowers to, what the compiler knows a
handler can receive, the line an uncaught raise prints, how each driver ends a
failed process, and the exit status that follows.

## The primitive

`Kernel.panic/1`, `Kernel.throw/1` and `Kernel.exit/1` are the raise
primitives, one per kind; `:erlang.error/1` is `panic/1` under Elixir's name. Each wraps an `extern "fz" defp ... :: none` whose
physical export is `fz_runtime::failure::fz_panic(process, value_ref)`,
`fz_throw(process, value_ref)` or `fz_exit(process, value_ref)`; each is `raise`
with its fixed kind (`error`, `throw`, `exit`). Nothing in Kernel takes a kind
from a program. The compiler continues a raise a handler was delivered through
`fz_reraise(process, kind_ref, value_ref)`, which reads the kind from the atom
the handler received and is `raise` with it; a kind the runtime never delivers
panics, as a fault in the compiler.
`raise_exception(process, name, fields)` builds a struct of the exception
module `name` and is `raise` with kind `error`. It allocates in the layout of
the module's registered schema, takes every field the module declares but
`__exception__` (which it sets to `true`), and panics if the schema is not
registered or a field is not given. There is one route behind all of them,
which:

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

`Kernel.raise/1` and `Kernel.raise/2` are Elixir's macros, written in
`lib/kernel.fz`, and every one of their forms is a `panic` of an exception
struct:

| written | expands to |
|---|---|
| `raise "text"` | `panic(%RuntimeError{message: "text"})` |
| `raise Mod` | `panic(Mod.exception([]))` |
| `raise %Mod{...}` | `panic(%Mod{...})` |
| `raise value`, any other expression | `panic(Kernel.to_exception(value))` |
| `raise Mod, attributes` | `panic(Mod.exception(attributes))` |

`Kernel.to_exception/1` decides at run time what the macro could not read off
the source: a binary is a `RuntimeError`, an exception is itself, an atom is
`module.exception([])`, and anything else is the `ArgumentError` Elixir raises
for it. Both macros are imported into every namespace by `lib/runtime.fz`,
beside `panic/1`. The library calls `panic/1`
with a value that is no exception only where Elixir itself raises a raw Erlang
error (`JSON.encode!/1` of an invalid UTF-8 binary).

An exception the compiler raises itself (a decision that runs out of clauses,
below) is built by the compiled code as a struct, with the prim a
`%Mod{...}` literal uses, and raised through `fz_panic`.

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

`Process.handlers: HandlerStack` (`runtime/src/handler_stack.rs`) is the
stack of handlers a raise can reach, innermost on top. A `try` pushes one
record on entry and pops it when its body completes; a raise delivers to the
innermost record and pops it. Records live in a word stack the process owns,
so entering a `try` builds nothing on the heap. Each record ends in a trailer
word holding its size in bytes, trailer included, so the innermost record is
found from the stack's `top` alone.

The stack is a GC root beside `runnable` and the mailbox: a boundary
collection forwards every heap value a compiled record captures and writes it
back into the record in place (`Process::collect` through
`HandlerStack::captures` and `set_captures`), and the `delivered` slot below.

Every handler receives the same three values: the kind atom (`:error`,
`:throw` or `:exit`), the raised value, and the exception's name atom (`nil`
when the value is not an exception map, which a throw or an exit's value never
is by kind, whatever it holds).

- A compiled record is the image of the handler's continuation, laid out as a
  heap closure is (`[outer_cont, captures...]` and their kind bytes), followed
  by the trailer. `emit_try` (`native_codegen/terminator.rs`) writes it in
  place on the stack through `push_handler_record` (`native_codegen/closure.rs`):
  it reads the stack's `top` and `end` through `PROCESS_HANDLER_TOP_OFFSET` and
  `PROCESS_HANDLER_END_OFFSET` (`runtime/src/process_abi.rs`), bumps `top`
  inline while the record fits, and calls `fz_handler_reserve` to grow the
  stack only when it is full. `Prim::PopHandler`, where the body's continuation
  begins, pops inline with `pop_handler_record`: `top` falls by the trailer's
  size. Delivery materializes the image with the three values as its bound
  values (`materialize_outcome_closure`, the receive-outcome machinery), pops
  the record, and stores the result in `Process::delivered`. That slot is not
  `runnable`: `runnable` means queued for the scheduler, `delivered` means a
  handler the current quantum is about to run.
- An interpreter record is the trailer alone. The interpreter keeps a
  `BackendContinuation` with `handler: true` on its continuation stack and
  pushes this record beside it (`Process::push_interpreter_handler`); delivery
  leaves the three values in `Process::raised` for the interpreter to take when
  the panicking extern returns.

Both kinds share the one stack, so a raise reaches the innermost `try`
whichever path entered it.

`Process::raises_delivered` counts the raises a handler took.

## Reaching the handler

- **Native code (run and build).** After a call to a `none` extern,
  `lower_extern_generic` emits `continue_after_raise`
  (`native_codegen/prim.rs`); `Term::Raise`, which lowering emits at a decision's
  arm of last resort after a `Prim::MakeStruct` of the exception, calls
  `fz_panic` with that struct, and then the same; `Term::Reraise`, which lowering emits
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
  delivered handler was ended by an extern that broke its `none` contract,
  which traps.
- **Interpreter.** A `none` extern answers `ExternCallValue::ProcessFailed`
  when the process has diverged (`Process::diverged`: failed, or a raise is
  waiting), and an error naming the broken contract when it has not.
  A decision's arm of last resort calls `raise_last_resort`, which raises the
  plan's exception through `failure::raise_exception` with the fields of its
  struct, after registering the struct's schema with the process's heap
  (`register_exception`), and continues in `after_panic`. `after_panic` (`ir_interp/backend.rs`) takes `Process::raised`, pops the
  continuation frames above the handler frame, and runs the handler entry with
  the three values as its params. With no raise waiting, the raise route has
  already failed the process: the step becomes `BackendRunStep::Failed`, and
  the drive loop's `end_quantum` (`runtime/src/sched_core.rs`) reads that off
  the process and exits it. A value reaching a handler
  frame is a contract violation: the try body pops its frame first.

## A function body as a `try`

A `def`, `defp` or `defmacro` clause whose body carries `rescue`,
`catch`, `else` or `after` beside its `do` is a `try` around that body, as
Elixir reads it (`elixir_def.erl`, `def_to_clauses`). Each clause wraps only its
own body; its arguments and guard stay outside the protection.

- The front door reads every definition's `do ... end` block, sections
  included, with `frontdoor.rs::parse_do_block`; `defmacro` reaches it through
  `parse_defmacro_body`.
- `quoted_surface.rs::is_function_body_keyword` admits a body of `do` plus those
  sections. Any other key is refused (`parse/invalid-function-definition`).
- `jobs/source.rs::expand_function_clause` expands every section
  (`is_function_body_section`), not only `do`.
- `quoted_function.rs::decode_function_body` decodes a body of `do` alone as that
  expression, and any other body through `decode_try`. So an implicit `try` is
  judged as a written one is.

`Expr::Try` carries a `TryForm` naming what wrote it. Where Elixir names the
definition instead of `try`, fz does too: a `catch` or `else` section that is not
`->` clauses (`expected -> clauses for :catch in "defp"`), and the `else`-only
warning. Like Elixir, a repeated section and the clause-head refusals still
name `try`.

## What `try` lowers to

`Expr::Try { body, rescue, catch, else_clauses, after, form }` (`src/ast/mod.rs`)
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
`Prim::PopHandler` carry it to native code. The function that pushes the record
continues into the body as a block; the handler is the one function a `try`
adds, since only the runtime reaches it (see the pipeline doc's entry homes).

## What a handler can receive

A handler's three params cross the raise route, so their types are not read
off the `try` body. The compiler keeps one fact about each program instead:
`FactKey::Raisable(root)`, held as a `Raisable` (`src/compiler2/identity.rs`)
per root, which records for each `RaiseKind` the exception modules a raise of
that kind can hand over and whether it can also hand over any other value. A
program is a root: the one the CLI runs, or a macro's compiled program, which
runs while other modules are being defined. A raise reaches only the handlers
of the program that makes it, so a macro's handlers never wait on the program
that expands the macro. The fact only grows. `World::raisable_ty(root, kind)`
reads it as a type: `None` while the program raises nothing of that kind, the union of one struct per exception module with
only `__exception__: true` known, or `any` once some raise of that kind hands
over a value that is not surely an exception.

Each activation's analysis publishes what it can raise (`raises_of`,
`src/compiler2/jobs/semantic.rs`) into its own root's fact, through
`World::note_raisable`:

| the activation | raises |
|---|---|
| has a decision the types leave able to fail, or a protocol call that can miss | `error`, the plan's `LastResort` exception |
| has a call on a module value that can reach no function | `error`, `UndefinedFunctionError` and `ArgumentError` |
| is an extern declared `raises: Mod` | `error`, `Mod` |
| is an extern declared `delivers: kind` (`fz_panic`, `fz_throw`, `fz_exit`) | `kind`, what the type of its first argument says (`World::raised_by`) |

`World::raised_by` reads an argument type through `Types::listed_structs`: a
type that is surely one of some structs, each flagged `__exception__: true`,
raises those exceptions; any other type raises anything. The fields are not
kept, because a field can hold another exception. `fz_reraise` adds nothing: it
continues a raise that an entry above already recorded.

`World::note_raisable` also makes an exception's module one a value can name
(`FactKey::NameableModules`, see [modules](modules.md)), because an exception
is asked for its message through its module.

`LoweredTail::Try` is analysed against its root's fact. The handler entry is
analysed once for each kind the fact holds, with its params typed `(the kind's
atom, World::raisable_ty(root, kind), any)`, and the results join the body's. A kind the
program never raises is not analysed, so a `try` in a program that raises
nothing is its body alone, and a clause for `:error` costs nothing in a program
that only throws. The analysis reads `FactKey::Raisable(root)`, so a raise
published later in the same program re-runs it.

`Drive::program_entry` (`src/compiler2/drive_harness.rs`) roots a test at the
entry the CLI runs. `a_program_that_raises_nothing_compiles_no_handler`,
`a_program_that_only_throws_compiles_no_error_handling` and
`the_uncaught_banner_calls_only_the_exceptions_the_program_can_raise`
(`src/compiler2/drive_test.rs`) pin the three cases.

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

Each name a clause takes keeps the span it was written at
(`RescueClause::exceptions`), and is a reference to that module's struct:
`collect_local_dispatch_requirements` records it with
`record_struct_reference`, with no fields, as it does a struct literal. A
clause that names a module nothing defines is `resolve/unknown-module`, and
one that names a module with no struct is `resolve/not-a-struct`, each under
the name (fixtures `01315`, `01316`). Elixir warns for both; fz compiles the
whole program at once, so such a clause can never match and is refused. A
struct that is not an exception is accepted, as in Elixir. Matching itself is
on the name's atom (`rescue_arms`).

A `try` with only a `do` block is `missing :catch/:rescue/:after option in
"try"`; a repeated section is `duplicate "rescue" clauses given for "try"`; a
`rescue` section that is not clauses is `invalid "rescue" block in "try", it
expects "pattern -> expr" clauses`.

## `__STACKTRACE__`

`__STACKTRACE__` is a variable a rescue or catch clause binds. fz carries no
stacktraces, so the clause binds it to the empty list, where Elixir's holds the
frames of the raise. `lower_handler_arm` (`src/compiler2/jobs/body.rs`) binds
it in the clause's environment through `bind_stacktrace_where_read`, and only
when the clause body reads the name, so a clause that does not read it lowers
to the steps it had without it. Because it is a binding, everything inside the
clause reads it the way it reads any variable: a closure captures it, and a
nested `try` body inside the clause sees it.

It is a special form and not a hygienic variable. `decode_expr`
(`src/compiler2/quoted_function.rs`) gives the name the user context wherever
it is written, so a macro whose quote holds `__STACKTRACE__` reads the clause
the macro expands in.

Read anywhere else, the body of the `try` itself included, it is Elixir's
diagnostic (`lower/unbound`):

```text
__STACKTRACE__ is available only inside catch and rescue clauses of try expressions
```

No pattern can bind it, so nothing outside a clause can make the name
readable. `decode_pattern` refuses it (`parse/stacktrace-pattern`):

```text
invalid pattern in match, __STACKTRACE__ is not allowed in matches
```

`reraise(exception, __STACKTRACE__)` is Elixir's idiom and compiles; `reraise/2`
ignores its second argument.

## The line

An uncaught raise prints what Elixir prints for it, without the stacktrace.

An error is caught before it is uncaught. The function a program starts in is
`__entry__/0`, published with the program's source (`build_program_entry`,
`src/compiler2/source_publish.rs`), and `Kernel.spawn` wraps the spawned
function the same way:

```fz
def __entry__() do
  try do
    main()
  catch
    :error, reason -> Exception.__uncaught__(reason)
  end
end
```

`Exception.__uncaught__/1` (`lib/exception.fz`) words the line in fz. An
exception is asked for its message through its own module, a value that is no
exception is wrapped in `%ErlangError{original: value}` first, and the line
`** (Name) message` goes to `fz_fail`, which fails the process with status 1
and hands the line to the fault sink. A throw and an exit pass the clause, reach
no handler, and are worded by the runtime.

With no handler at all, `failure_line` (`runtime/src/failure.rs`) words the
raise. An error reaches it only where no entry wraps the code: a macro
expansion, which the interpreter runs directly.

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

An exception that shows a value (a decision's miss, below) carries the value
in `term`, and its module's `message/1` renders it.

## Declaring an exception

`defexception fields` (`Kernel`, `lib/kernel.fz`) is a macro that declares the
module's struct as `[__exception__: true] ++ fields` and defines, in the
module:

| function | does |
|---|---|
| `exception(fields)`, a list | `struct!(__MODULE__, fields)` |
| `exception(message)`, a binary, when `fields` has `:message` | `%__MODULE__{message: message}` |
| `message(exception)`, when `fields` has `:message` | the `message` field |

Both are marked `defoverridable`, so a `def` of the same name and arity
further down the module replaces the default, and the replaced default is
compiled only when the replacement calls it as `super`. `raise Mod, "text"` with a `Mod` that declares `:message`
raises a map of that struct's module, so `rescue e in Mod` takes it and
`e.message` reads it.

`Exception.message/1` (`lib/exception.fz`) is `e.__struct__.message(e)`, a
call on a module value. The modules it can reach are the ones `e`'s type
names, so on an `e` bound by `rescue e in Mod` it is `Mod.message(e)`. A
bare `rescue e` gives `e` what the program can raise as an error (above): the
call reaches those exceptions' modules, or every module a value can name when
some raise hands over a value that is not surely an exception.

`is_exception/1` (`Kernel`) is true for a map whose `__struct__` is an atom
and whose `__exception__` is `true`. Its clauses are a map pattern and a
catch-all, so it is a guard. `inspect` does not print the `__exception__`
field of a struct.

Fixture `00882` agrees with Elixir on interp, run and build.

## The library's exceptions

The built-in exceptions are library modules, one file each under
`lib/exceptions/`, declared with `defexception` and carrying the fields
Elixir's carry. Each words its own `message/1`; the ones that show a value
share `Exception.__format_message_with_term__/2`. A module is defined when
something names it, so a program compiles the exceptions it can raise and none
of the others (`a_program_defines_only_the_exception_modules_it_can_raise`).

Every library failure raises the exception, with the message, Elixir does. A
clause that cannot match is left to the decision's own `FunctionClauseError`.

| failure | prints |
|---|---|
| `bit_size/1`, `byte_size/1`, `tuple_size/1`, `length/1`, `elem/2` of the wrong kind; `put_elem/3` and `:erlang.setelement/3` of a non-tuple or an index outside it (the message lists every argument at fault); `abs/1`, `round/1`, `trunc/1`, `floor/1`, `ceil/1` of a non-number; `hd/1`, `tl/1` of anything but a non-empty list | `** (ArgumentError) errors were found at the given arguments:` then the argument and what is wrong with it |
| `map_size/1` of a non-map | `** (BadMapError) expected a map, got:` then the value |
| `elem/2` or `put_elem/3` with a non-integer index | `** (ArithmeticError) bad argument in arithmetic expression`, as Elixir adds one to the index |
| `abs/1` of the minimum integer; `round/1`, `trunc/1`, `floor/1`, `ceil/1` of a float outside the 64-bit range (Elixir answers a bignum) | `** (ArithmeticError) bad argument in arithmetic expression` |
| a `<<...>>` construction or `<>` given a field of the wrong kind, a size that is no non-negative integer, a too-short binary or a value that is no Unicode scalar | `** (ArgumentError) construction of binary failed: segment N of type 'T':` then what the segment expected, naming the segment the BEAM names |
| `div/2`, `rem/2`, `/` and the other arithmetic that fails | `** (ArithmeticError) bad argument in arithmetic expression` |
| `Map.fetch!/2`, `Map.update!/3`, `Map.replace!/3`, `Keyword.fetch!/2`, `struct!/2` on a struct | `** (KeyError) key <key> not found in:` then the collection |
| `struct!/2` on a module, naming a key its struct does not declare | `** (KeyError) key <key> not found` |
| `struct!/2` on a module, given another module as `:__struct__` | `** (ArgumentError) expected struct name returned by <module>.__struct__/1 to be <module>, got: <other>` |
| `%{map \| k: v}` naming a key `map` lacks | `** (KeyError) key <key> not found`, the first such key in the order written |
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

An update is Elixir's `put_map_exact`: it may only replace keys the map has.
A put naming a key its base lacks leaves the update with no destination, and
its freeze then answers the miss sentinel instead of a map; the lowering tests that answer
(`ok`, as a `cond`-shaped decision on `true`) and its miss arm calls
`Map.update_key_error/2`, which finds the missing key and raises. When the
base's type proves every updated key is present (`Types::map_surely_has_keys`),
`ok` is typed `true`, the decision's miss arm is trimmed, and the program
compiles no KeyError path. Otherwise a program whose keys are all present pays
one test. The raise runs even when the updated map is unused
(`_ = %{m | z: 1}`). Elixir names whichever missing key
the BEAM meets first in its own internal order; fz names the first missing key
in the order the update writes them, so the two agree whenever one key is
missing.

## Decisions that run out of clauses

Every decision is a dispatch plan, and a plan that can fail carries the
exception its arm of last resort raises: `PatternDispatchPlan.last_resort`, a
`LastResort` (`src/dispatch_matrix/pattern/last_resort.rs`) set when the plan's
rows are built (`SourcePatternRows::raising`). `=` is a decision like the others:
its pattern is a one-row plan. `LastResort::Exception` names the exception's
module and lists the fields the failure sets with what each holds (`FieldTerm`:
the plan's subject, or a `LiteralTerm`: a value written out in full).
`LastResort::struct_fields` completes it against the module's declaration:
every declared field in order, holding what the failure sets or the field's
default, `__exception__` among them; a failure that sets a field the module
does not declare is an error that names the field. The declaration reaches the
backends in the program's schema: `BackendSchema` carries each field's default
(`BackendProgram::struct_defaults`), and `produce_backend_executable_product`
waits for `StructDefined` of every exception module its code raises (each
failing plan's, an extern's declared failure, and `UndefinedFunctionError` and
`ArgumentError` for a call that can find no function) and includes that
module's `StructSchema`. Reaching the plan's fail builds that struct and
raises it: native code with `Prim::MakeStruct` and `Term::Raise` (`emit_raise`,
`src/compiler2/jobs/native.rs`), the interpreter through
`fz_runtime::failure::raise_exception`. The raised value is the same struct a
`%Mod{...}` literal builds on each path, so it inspects as `%Mod{...}`
(fixture `01311`). The raise goes to the nearest handler, a `rescue` around the decision
catches it, and uncaught it prints the line its module words and ends the
process as any error does.

| decision | prints |
|---|---|
| a function's clauses | `** (FunctionClauseError) no function clause matching in M.f/1` |
| an extern's one typed clause, for an argument outside a parameter's type | `** (FunctionClauseError) no function clause matching in fz_op_add_ii/2` |
| an anonymous function's clauses | `** (FunctionClauseError) no function clause matching in anonymous fn/1 in M.g/0` |
| `pattern = value` | `** (MatchError) no match of right hand side value:` then the value |
| `case` | `** (CaseClauseError) no case clause matching:` then the value |
| `cond` | `** (CondClauseError) no cond clause evaluated to a truthy value` |
| `with`'s `else` | `** (WithClauseError) no with clause matching:` then the value |
| `try`'s `else` | `** (TryClauseError) no try clause matching:` then the value |
| `and` / `or` on a non-boolean | `** (BadBooleanError) expected a boolean on left-side of "and", got:` then the value |
| `not` on a non-boolean | `** (ArgumentError) argument error` |

A message that shows a value is Elixir's multi-line form: the lead, a blank
line, and the value rendered by `inspect` and indented four spaces
(`Exception.__format_message_with_term__/2`), and the exception carries the
value itself in its `term` field, as Elixir's `CaseClauseError`, `MatchError`,
`WithClauseError`, `TryClauseError` and `BadBooleanError` do. The value is the
plan's input 0.

A `with` whose binding fails without an `else`, and a `receive`, have no last
resort: the first yields the value, the second waits for another message.

A call on a module value that reaches no function raises
`UndefinedFunctionError`, or `ArgumentError` when the value is no atom
(`failure::raise_undefined_function`). It is a target of the call and not a
last resort; `modules.md` has the wording for each case.

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

## What exceptions cost a compile

`tests/exception_cost_test.rs` counts `compiler2.job` spans over programs that
differ in one thing. A function that neither raises nor handles costs what it
costs in a program with no raise. A raise site costs 13 jobs and a handler 15.

An exception type that is declared and raised once costs 40:

| what | jobs |
|---|---|
| the function that raises it | 15 |
| its `exception/1` | 7 |
| its `message/1`, in three activations | 16 |
| its module's definition | 1 |
| one more analysis of `Exception.message/1`, which dispatches to every type | 1 |

Past eight types there is a bounded extra of one to five jobs that does not
grow with the number of types. `Kernel.panic/1` is keyed `(map)` and keeps one
input row per exception type raised into it. Each row is a struct whose
`__exception__` field is the literal `true`, so it is not ground and keys the
extern `fz_panic/1` as `map` too. Past `ACTIVATION_INPUT_ROW_BUDGET`
(`src/compiler2/semantic.rs`) rows the rows widen to one joined row: the union
of the structs with `__exception__` widened to `atom`. That union is ground,
so it keys `fz_panic/1` as itself (`Types::probe_keys_as_itself`): `panic/1` is
analysed once more and `fz_panic/1` gets a second activation. The joined row
counts as one row, so the next widening comes eight types later, with a larger
union replacing the last.

## Where it lives

- `runtime/src/failure.rs` — `RaiseKind`, `EXCEPTION_FIELD`, `failure_line`,
  `exit_status`, `fz_panic`, `fz_throw`, `fz_exit`, `fz_fail`, `reraise`,
  `fz_reraise`, `raise_exception`, `raise_undefined_function`,
  `fz_raise_undefined_function`, `STDERR_FAULT_HOOK`.
- `lib/exception.fz` — `Exception.message/1`, `__uncaught__/1`,
  `__format_message_with_term__/2`; `lib/exceptions/` — the built-in exception
  modules.
- `src/compiler2/source_publish.rs` — `PROGRAM_ENTRY`, `build_program_entry`.
- `src/compiler2/identity.rs` — `Raisable`, `Raised`; `src/compiler2/world.rs`
  — `note_raisable`, `raisable_ty`, `raised_by`;
  `src/compiler2/jobs/semantic.rs` — `raises_of` and the `LoweredTail::Try`
  analysis.
- `src/dispatch_matrix/pattern/last_resort.rs` — `LastResort`.
- `runtime/src/process.rs` — `Raised`, `handlers`, `raised`,
  `delivered`, `raises_delivered`, `exit_status`, `push_interpreter_handler`,
  `pop_handler`, `deliver_handler`, `run_quantum`, `diverged`.
- `runtime/src/handler_stack.rs` — `HandlerStack`, `Innermost`.
- `runtime/src/ir_runtime.rs` — `fz_handler_reserve`.
- `runtime/src/process_abi.rs` — `PROCESS_DELIVERED_OFFSET`, read by
  `continue_after_raise`; `PROCESS_HANDLER_TOP_OFFSET` and
  `PROCESS_HANDLER_END_OFFSET`, read and written by `emit_try` and
  `Prim::PopHandler`.
- `lib/kernel.fz` — `panic/1`, `raise/1`, `raise/2`, `to_exception/1`,
  `defexception/1`, `inspect/1`, `throw/1`, `exit/1`, `reraise/2`;
  `lib/runtime.fz` lists the raise functions for auto-import.
- `src/ast/mod.rs` — `Expr::Try`, `RescueClause`, `CatchClause`, `STACKTRACE`.
- `src/compiler2/quoted_function.rs` — `decode_try`, `decode_rescue_head`,
  `decode_catch_clauses`; `decode_expr` and `decode_pattern` for
  `__STACKTRACE__`.
- `src/compiler2/frontdoor.rs` — `parse_do_section` (`ClauseKind::Params` for
  `catch`).
- `src/compiler2/source_sugar.rs` — the `in` rewrite and its operator stamp.
- `src/compiler2/jobs/body.rs` — `lower_try`, `lower_handled`, `handler_arms`, `rescue_arms`, `lower_handler_arm`, `bind_stacktrace_where_read`, `push_try_else`.
- `src/compiler2/jobs/native.rs` — `raise_last_resort` (emits `Term::Raise` and `Term::Reraise`),
  `raise_undefined_function` (emits `Term::RaiseUndefined`).
- `src/compiler2/native_codegen/terminator.rs` — `emit_try`, `emit_raise`, `emit_raise_undefined`.
- `src/compiler2/native_codegen/prim.rs` — `continue_after_raise`,
  `Prim::PopHandler`.
- `src/ir_interp/backend.rs` — `after_panic`, `raise_last_resort`,
  `BackendRunStep`, `BackendRun`, `macro_fault_hook`.
- `src/compiler2/compiler.rs` — `RunFailure`.
- `fixtures/00815` through `fixtures/00831` — the rescue shapes, nesting,
  re-raise, the uncaught raise, a try in a spawned process, the raising loop,
  the allocating try body, and the refused `try` forms.
- `fixtures/00832` through `fixtures/00840`, with `fixtures/00800` through
  `fixtures/00806` — `after` and `else`.
- `fixtures/00841` through `fixtures/00847` and
  `fixtures/00807` through `fixtures/00814` — `throw`, `exit`, `catch`,
  `reraise/2`, the uncaught lines and statuses, and the refused `catch` forms.
- `fixtures/00885` through `fixtures/00889` — `__STACKTRACE__`: read in a
  rescue clause, a catch clause and a closure, passed to `reraise/2`, its value,
  the two refusals, and a macro that quotes it.
- `fixtures/00848` and `fixtures/00850` — a rescued decision's exception name,
  `term` and message.
- `fixtures/01150` through `fixtures/01152` — the forms of `raise`, the fields
  the library's exceptions carry, and a program that names one exception.
- `fixtures/00890` through `fixtures/00892` — a program that only throws, an
  uncaught library exception worded by its module, and one handler receiving
  each kind.
