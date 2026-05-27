# REPL Session

## Model

The REPL is one long-running fz program session. Each prompt adds either more
source-world knowledge or one expression entry to run.

```text
user text
  -> ReplLineEditor edits until parser-complete text is ready
  -> ReplComposer classifies the submitted editor buffer
  -> ReplSession asks ReplWorld to parse, remember, and compile it
  -> ReplRuntime runs compiled IR on the persistent evaluator process
  -> ReplFrame carries top-level values into the next expression
```

That is the big idea: the prompt is not a second language runtime. Interactive
code goes through the same frontend lowering and IR interpreter machinery as
ordinary fz code.

## Major Pieces

`ReplComposer` is the submitted-buffer classifier. It is stateless. It
recognizes `:q`, `:quit`, `?name`, blank input, incomplete source, invalid
source, and complete chunks. It can ask the parser whether text is complete,
but it does not compile, run, edit, or retain anything.

`ReplSession` is the coordinator. It receives complete source chunks only. For
item chunks, it updates `ReplWorld`. For expression chunks, it asks `ReplWorld`
to compile a compiler-owned entry, asks `ReplRuntime` to run that entry, and
stores the returned top-level values in `ReplFrame`.

`ReplWorld` is the source-world memory. It owns definitions, modules, imports,
aliases, macros, docs, specs, type declarations, item chunks, committed REPL
entry chunks, and source-map material. It is also where help queries are
answered.

`ReplFrame` is the runtime value frame between prompts. It is not an AST
environment. It is an ordered ABI: field names plus `AnyValue`s that become the
arguments to the next lowered REPL expression entry.

`ReplRuntime` is the persistent IR interpreter owner. It owns an
`IrInterpRuntime`, the evaluator pid, and the current evaluator module image.
It enqueues entries, drives the scheduler, reads frame tuples, and renders
values against the evaluator process heap.

`ReplLineEditor` is the terminal composition boundary. The production
implementation is `rustyline`, behind the local trait. It owns cursor movement,
insertion, deletion, history navigation, Ctrl-D/C reporting, parser-driven
multiline editing, and the prompt string shown for the next read.

## Interactive Input Flow

Interactive presentation sits above the language session:

```text
rustyline
  -> ReplLineEditor
  -> ReplComposer
  -> ReplSession
  -> ReplWorld/ReplRuntime/ReplFrame
```

`rustyline` was chosen because it is a narrow readline-shaped dependency with
basic editing, history, Ctrl-D/C reporting, and a validator hook for multiline
completion. The validator asks `ReplWorld::parse_source_chunk` whether the
current editor buffer is complete.

Control behavior:

- Enter submits only when parser-complete input is present.
- Parser-incomplete input stays in the editor for another line.
- Invalid syntax is editor-complete, so `ReplComposer` can report the
  diagnostic without retaining source.
- Ctrl-D exits when `rustyline` reports EOF.
- Ctrl-C cancels the current editor read and returns to the next prompt without
  executing a chunk.

## Chunk ABI

Every expression chunk lowers through the frontend's REPL entry API. The entry
has this shape:

```text
__repl_eval_N(binding_0, binding_1, ...) ->
  {display_value, next_binding_0, next_binding_1, ...}
```

The compiler returns the entry `FnId`, input frame layout, and output frame
layout. The host passes `ReplFrame` values using the input layout. The first
returned tuple field is the display value. The remaining fields replace
`ReplFrame` using the output layout.

This makes top-level interactive bindings compiler-owned:

```text
x = 41
{a, b} = pair
{a, b} = :not_a_pair
```

The lowerer decides which names bind, whether matches succeed, and what frame
shape comes next. The host only passes and stores ordered runtime values.

## Runtime Persistence

The evaluator pid stays alive across prompts. `ReplRuntime` passes it as
`keepalive_pid` to `drive_until_idle`, so a successful expression does not drain
the evaluator process resources or discard mailbox, heap, or runtime-owned
state.

Each compiled chunk is a new IR `CodeImage`. The evaluator pid advances to the
newest image when a chunk is enqueued. Spawned children keep the image they were
spawned under, so a child blocked in `receive` can resume after later prompts
compile newer chunks.

## Source World Policy

Macro expansion, docs, and source metadata are world work:

```text
macro definitions -> ReplWorld
macro bodies      -> ReplWorld compile-time evaluator
user runtime code -> lowered IR on ReplRuntime
```

Help queries are also world work. `?name` reads already-loaded docs, moduledocs,
and rendered specs from `ReplWorld`. It does not drive `ReplRuntime`, so a
blocked evaluator process does not prevent help from answering.

## Script Mode

`repl --script` shares the same frontend/runtime model but not the terminal
presentation model. It drives whole-file source through
`ReplSession::run_script_str`, emits no prompts, echoes no expression display
values, and invokes `main/0` at EOF when present. Program-side `print()` remains
the only script-mode stdout.

Script mode bypasses `rustyline` and `ReplComposer` because whole-file parsing
already provides the complete source boundary.

## Module Artifact Policy

The REPL is session-eager. Interactive chunks and `repl --script` compile
against the source world already accumulated in `ReplWorld`, plus the built-in
runtime-library interfaces that normal frontend compilation sees. They do not
accept `--interface`, `--provider`, or `--artifact-root`, and they do not invoke
`ModuleGraphLoader` to load `.fzi`/`.fzo` provider artifacts.

That boundary keeps the persistent session simple: the REPL has one mutable
source world and one persistent evaluator image. Artifact-backed imports belong
to whole-file commands with an explicit root source and explicit provider roots:

```sh
fz run --interface Math --artifact-root build/fz consumer.fz
fz build --interface Math --artifact-root build/fz consumer.fz -o consumer
```

Use the REPL for definitions entered in the current session or script. Use
`run`/`build` when a program depends on provider artifacts emitted by another
module build.

## Error And Blocking Policy

Parse, type, and lowering errors leave `ReplRuntime` untouched.

Runtime errors are reported for the current chunk. The session may keep the
runtime only when `CURRENT_PROCESS` has been restored and the evaluator process
state is still well-defined.

If a chunk parks the evaluator on `receive`, `drive_until_idle` can return
without a completed display value. Surface that as blocked state; do not invent
a value or partially reset the runtime.

Interrupts should leave either an explicit blocked/runnable evaluator or tear
down the whole session.

## What This Model Keeps Out

The compile-time macro/doc evaluator is not a user-code REPL runtime. It should
not grow spawn, send, receive, mailbox, or scheduler semantics just to make
interactive execution work.

The terminal editor is not the language session. It should not parse docs,
execute chunks, or decide runtime behavior.

`ReplComposer` is not an editor. It should not own pending source, prompt mode,
cursor state, history, or multiline accumulation.

`ReplFrame` is not a host-side evaluator environment. It should not implement
pattern matching, binding semantics, or expression evaluation.
