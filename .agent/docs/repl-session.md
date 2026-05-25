# ReplSession Contract

## ELI5

The REPL is not a different language runtime. It is a long-lived session that
keeps code, bindings, and one evaluator process alive while each user input is
compiled into a small IR entry and driven on `IrInterpRuntime`.

```text
parse input
update world
synthesize chunk entry
enqueue entry on evaluator pid
drive existing IrInterpRuntime
return display value + updated bindings
```

No prompt may run user program semantics through `eval::Interp`.

## Layers

`ReplSession` owns three layers:

- `ReplWorld`: accumulated source-level program state.
- `ReplFrame`: top-level names represented as runtime values.
- `ReplRuntime`: persistent `IrInterpRuntime` plus evaluator pid.

`ReplWorld` contains definitions, modules, imports, aliases, macro definitions,
docs, specs, type declarations, and source-map material needed to compile the
next chunk. Replacing or appending function clauses follows the current
`repl.rs` behavior.

`ReplFrame` is not an AST `Env`. It is the REPL's top-level runtime frame:
an ordered set of binding names and their runtime values. Its order is part of
the chunk ABI because synthesized evaluator entries receive the current frame
as positional arguments and return the next frame in the same declared order.

`ReplRuntime` owns process/mailbox/heap/resource state. It is created once per
session and then driven with `IrInterpRuntime::enqueue_entry` and
`drive_until_idle`.

## Chunk Shape

Every expression chunk must lower to an evaluator entry function shaped like:

```text
__repl_eval_N(binding_0, binding_1, ...) ->
  {display_value, next_binding_0, next_binding_1, ...}
```

The caller passes the current `ReplFrame` values as arguments. After the entry
completes, the first returned field is rendered for interactive prompts and the
remaining returned fields replace the frame values.

Host code must not inspect expression ASTs to decide which names changed.
Binding semantics belong to the lowered program. A simple top-level binding
such as `x = 41`, a destructuring binding such as `{a, b} = pair`, and a
failed match must all follow the same IR semantics they would have outside the
REPL. The host coordinates chunks; it does not interpret pattern binding.

When a chunk introduces new top-level frame names, `ReplWorld` compiles an
entry whose return shape extends the ordered frame. Later chunks receive the
extended frame as positional arguments.

`repl --script` suppresses expression echo and only program-side `print`
reaches stdout.

Top-level item chunks update `ReplWorld`. If an item chunk also needs runtime
initialization, it must synthesize and drive an entry on the same evaluator pid;
it must not create a one-shot interpreter run.

The evaluator pid is passed as `keepalive_pid` to `drive_until_idle`, so a
completed chunk does not drain resources or exit the evaluator process between
prompts.

Each compiled chunk is a new IR `CodeImage` generation. `IrInterpRuntime`
stores the `CodeImage` per pid: the evaluator pid is updated to the newest
chunk image when `enqueue_entry` runs, while spawned children keep the image
they were spawned under. That lets a child blocked in `receive` resume after
later prompts even if the session has compiled more chunks and the newest
image has different `FnId`s.

## Macro Boundary

`eval::Interp` remains compile-time infrastructure for macro expansion. That
boundary is intentional:

- macro definitions live in `ReplWorld`
- macro expansion may evaluate macro bodies with `eval::Interp`
- expanded user runtime code lowers to IR and runs on `IrInterpRuntime`

Do not add spawn/send/receive runtime semantics to `eval::Interp` for REPL user
program execution.

## Docs And Help

The existing `?name` behavior is session-world behavior, not runtime behavior.
Docs, moduledocs, and rendered specs are stored in `ReplWorld` as items are
loaded. Help queries read that world and must not drive the runtime.

Keeping docs/help out of `ReplRuntime` matters: a blocked evaluator process must
not prevent `?name` from answering from already-loaded metadata.

## Errors, Blocking, And Interrupts

Parse/type/lower errors leave `ReplRuntime` untouched and report diagnostics.

Runtime errors from a chunk are reported for that chunk. The session may keep
the runtime only if `CURRENT_PROCESS` has been restored and the evaluator
process is not left in an ambiguous running state.

If a chunk parks the evaluator on receive, `drive_until_idle` can return with no
completion and the evaluator process blocked. The session must surface that as
"blocked" rather than pretending the expression produced a value. A later chunk
or spawned process may send a message and resume the evaluator through the same
runtime.

Interrupts should restore `CURRENT_PROCESS`, leave process state explicit, and
either keep a well-defined blocked/runnable evaluator or tear down the whole
session. Do not silently reset only part of the runtime.

## Script And Interactive

`repl --script` and interactive input use the same `ReplSession` execution
model. The differences are presentation only:

- interactive prints prompts and display values
- script reads file chunks, emits no prompts, echoes no expression result, and
  invokes `main/0` at EOF if defined

Both paths must share the same world, binding, macro, and runtime machinery.
