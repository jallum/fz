# ReplSession Contract

## Rule

The REPL is a long-lived language session, not a separate evaluator.

Each user input updates source-world state, lowers an entry to IR, runs that
entry on the persistent evaluator process, and returns a display value plus the
next top-level frame.

```text
input chunk
  -> ReplWorld parses/compiles
  -> ReplRuntime enqueues IR entry on evaluator pid
  -> IrInterpRuntime drives existing process state
  -> ReplFrame stores returned top-level values
```

No prompt may run user program semantics through
the compile-time macro/doc evaluator.

## Layers

`ReplSession` is the coordinator for three concepts:

- `ReplWorld`: source-level program state
- `ReplFrame`: top-level runtime values
- `ReplRuntime`: persistent IR interpreter runtime and evaluator process

`ReplWorld` owns definitions, modules, imports, aliases, macro definitions,
docs, specs, type declarations, parsed item chunks, committed REPL entry
chunks, and source-map material needed to compile the next chunk. The session
asks the world to parse chunks, apply item chunks, compile compiler-owned REPL
entries, commit successful entries, and answer docs queries.

`ReplFrame` is not an AST `Env`. It is an ordered ABI between host and lowered
chunk entry: field names plus their runtime values.

`ReplRuntime` owns the persistent `IrInterpRuntime`, evaluator pid, and current
evaluator module image. It enqueues evaluator entries, drives the runtime, reads
returned frame tuples, and renders values against the evaluator process heap.

## Chunk ABI

Every expression chunk lowers through the frontend's REPL entry API to an
evaluator entry shaped like:

```text
__repl_eval_N(binding_0, binding_1, ...) ->
  {display_value, next_binding_0, next_binding_1, ...}
```

The compiler returns the entry `FnId`, input frame layout, and output frame
layout. The host passes `ReplFrame` values using that input layout. The first
returned field is the value to display. The remaining fields become the next
frame values using the returned output layout.

Binding values must come from the lowered program, not host-side AST
interpretation. These cases must use the same semantics as ordinary runtime
code:

```text
x = 41
{a, b} = pair
{a, b} = :not_a_pair
```

The lowerer defines the frame ABI shape from the environment produced while
lowering the expression. The host must not decide whether a match succeeds,
which names a pattern binds, or what values bindings receive.

When a chunk introduces new top-level names, `ReplWorld` compiles an entry whose
return shape extends the ordered frame. Later chunks receive the extended frame
as positional arguments.

## Runtime Persistence

The evaluator pid is passed as `keepalive_pid` to `drive_until_idle`. A
completed chunk must not drain the evaluator process resources or discard its
mailbox, heap, or runtime-owned state.

Each compiled chunk is a new IR `CodeImage`. The evaluator pid advances to the
newest image when a chunk is enqueued. Spawned children keep the image they were
spawned under, so a child blocked in `receive` can resume after later prompts
compile newer chunks.

## Macro Boundary

Macro expansion is source-world work:

- macro definitions live in `ReplWorld`
- macro bodies may run in `ReplWorld`'s compile-time evaluator
- expanded user runtime code lowers to IR and runs on `IrInterpRuntime`

Do not add spawn, send, receive, mailbox, or scheduler semantics to
the compile-time evaluator for REPL user execution.

## Docs And Help

Help queries are world queries, not runtime work. Docs, moduledocs, and rendered
specs are stored in `ReplWorld` as items are loaded.

`?name` must not drive `ReplRuntime`. A blocked evaluator process should not
prevent help from answering from already-loaded metadata.

## Errors And Blocking

Parse, type, and lowering errors leave `ReplRuntime` untouched.

Runtime errors are reported for the current chunk. The session may keep the
runtime only when `CURRENT_PROCESS` has been restored and the evaluator process
state is still well-defined.

If a chunk parks the evaluator on `receive`, `drive_until_idle` can return
without a completed display value. Surface that as blocked state; do not invent
a value or reset only part of the runtime.

Interrupts must either leave an explicit blocked/runnable evaluator or tear
down the whole session.

## Script And Interactive

`repl --script` and interactive input share the same world, frame, macro, and
runtime machinery.

The differences are presentation and entry selection:

- interactive input prints prompts and display values
- script input emits no prompts, echoes no expression result, and invokes
  `main/0` at EOF when defined
