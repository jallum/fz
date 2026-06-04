# REPL Session

## Model

The REPL is one long-running fz program session. Each prompt adds either more
source-world knowledge (an item chunk) or one expression entry to run.

```text
user text
  -> ReplLineEditor edits until parser-complete text is ready
  -> ReplComposer classifies the submitted editor buffer
  -> ReplSession asks ReplWorld to parse, remember, and compile it
  -> ReplRuntime runs compiled IR on the persistent evaluator process
  -> ReplFrame carries top-level values into the next expression
```

The prompt is not a second language runtime. Interactive code goes through the
same frontend lowering and IR interpreter machinery as ordinary fz code, so
`spawn`, `send`, `receive`, resources, and heap values behave at the prompt
exactly as they do in a whole-file program.

`ReplSession` (`src/cli/repl.rs`) holds the four pieces: `world: ReplWorld`,
`frame: ReplFrame`, `runtime: Option<ReplRuntime>`, and a `next_eval` counter
that names entries `__repl_eval_0`, `__repl_eval_1`, … The runtime is lazily
created the first time an expression compiles.

## Major Pieces

`ReplComposer` is the submitted-buffer classifier. It is stateless (a unit
struct). `submit_buffer` returns one `ReplComposerEvent`: `Quit` for `:q` /
`:quit`, `Empty` for blank input, `DocQuery(name)` for `?name`, and otherwise
parses the buffer via `ReplWorld::parse_source_chunk` to return `Complete(src)`
for parser-complete source or `Diagnostic(msg)` for incomplete / invalid
source. It does not compile, run, edit, or retain anything.

`ReplSession` is the coordinator. `eval_chunk` receives complete source only.
Item chunks update `ReplWorld` (`apply_items`) and produce no display value.
Expression chunks go to `eval_expr_chunk`, which asks `ReplWorld` to compile a
compiler-owned entry, asks `ReplRuntime` to run it, splits the returned tuple
into a display value plus the next frame, replaces `ReplFrame`, and commits the
entry program back into `ReplWorld`.

`ReplWorld` is the source-world memory. Its fields are a `Compiler`, a
`CompileTimeEvaluator` (macros, docs, globals, and rendered `@spec` text), the
accumulated item chunks (`item_chunks: Vec<ReplItemChunk>`), and the committed
REPL expression entries (`eval_chunks: Vec<Program>`). `session_program` rebuilds
one `Program` from item chunks (grouping same-name/arity `fn` clauses) followed
by the committed eval chunks; that program is the compilation context for the
next chunk. `ReplWorld` keeps no `SourceMap` field — every parse builds a fresh
`SourceMap`. It also answers help queries through `lookup_doc`.

`ReplFrame` is the runtime value frame between prompts. It is not an AST
environment: it is `values: BTreeMap<String, AnyValue>` — named bindings to
their runtime values. `names()` returns the keys in `BTreeMap` (key-sorted)
order; those names become the input frame for the next lowered entry, and the
lowered entry binds its parameters in that same order. `values_for` reads the
ordered argument vector; `replace` overwrites the whole map with the entry's
output names zipped to the returned values.

`ReplRuntime` owns the persistent IR interpreter. It holds an `IrInterpRuntime`,
the evaluator pid (`1`), and the `current_module`. It enqueues entries and
drives the scheduler (`enqueue_and_drive`), reads the returned frame tuple
(`read_tuple_fields` on the evaluator pid), and renders values against the
evaluator process heap (`render_value` on the evaluator pid).

`ReplLineEditor` is the terminal composition boundary, a local trait whose
production implementation (`RustylineReplLineEditor`) wraps `rustyline`. It owns
cursor movement, insertion, deletion, history, Ctrl-D/Ctrl-C reporting,
parser-driven multiline editing, and the prompt string for the next read.

## Interactive Input Flow

Interactive presentation sits above the language session:

```text
rustyline
  -> ReplLineEditor
  -> ReplComposer
  -> ReplSession
  -> ReplWorld / ReplRuntime / ReplFrame
```

`rustyline` is a narrow readline-shaped dependency: basic editing, history,
Ctrl-D/Ctrl-C reporting, and a validator hook for multiline completion.
`ReplEditorHelper::validation_result_for` is that hook. It returns `Valid` for
immediate inputs (blank, `:q`/`:quit`, `?…`), `Incomplete` when
`ReplWorld::parse_source_chunk` reports `Incomplete`, and `Valid` otherwise
(including on parse errors, so the buffer submits and the error is reported).

Control behavior follows from the validator and `run`'s loop:

- Enter submits only when parser-complete input is present.
- Parser-incomplete input stays in the editor for another line.
- Invalid syntax is editor-complete, so `ReplComposer` reports the diagnostic
  without retaining source.
- Ctrl-D exits when `rustyline` reports EOF.
- Ctrl-C cancels the current read and returns to the next prompt without
  executing a chunk.

## Chunk Classification

`ReplWorld::parse_source_chunk` lexes the buffer, then looks at the first
non-`Newline`/`Semi` token. A buffer whose first token is `@`, `fn`, `extern`,
`defmacro`, `defmodule`, `alias`, or `import` parses as a `Program` and becomes
a `ReplWorldChunk::Items`. Anything else parses with `parse_expr_eof` and
becomes a `ReplWorldChunk::Expr { expr, sm }`. A parser "incomplete" error maps
to `ReplWorldParse::Incomplete` (the editor keeps reading); any other error maps
to `ReplWorldParse::Err`.

A bare top-level `type` declaration is not in the item-start token set, so it
classifies as an expression chunk, not an item chunk.

## Chunk ABI

Every expression chunk lowers through the frontend's REPL entry API
(`compile_repl_expr_with_types`). The synthesized entry has this shape:

```text
__repl_eval_N(binding_0, binding_1, ...) ->
  {display_value, next_binding_0, next_binding_1, ...}
```

The lowerer binds the chunk expression to `__repl_display` and returns a tuple
of `__repl_display` followed by the output-frame variables. The output frame is
the input frame plus any new names a top-level `=` pattern binds
(`repl_output_frame_names`), so a binding expression grows the frame.

`compile_repl_expr_with_types` returns the input frame, the output frame, and
the synthesized `entry_item`. `ReplWorld::compile_repl_expr` compiles the whole
session program with that entry appended, then looks up the entry's `FnId` by
name in the prepared module. The host passes `ReplFrame` values in the input
layout, takes the first returned tuple field as the display value, and replaces
`ReplFrame` from the remaining fields under the output layout.

This makes top-level interactive bindings compiler-owned:

```text
x = 41
{a, b} = pair
{a, b} = :not_a_pair
```

The lowerer decides which names bind, whether matches succeed, and what frame
shape comes next. The host only passes and stores ordered runtime values; a
match failure surfaces through lowered runtime semantics, not host-side
matching.

## Runtime Persistence

The evaluator pid stays alive across prompts. For expression chunks
`ReplRuntime::eval_entry` drives with `keepalive = true`, which passes the
evaluator pid as `keepalive_pid` to `drive_until_idle`. When a completing
process is the keepalive pid, the scheduler records its result and marks it
`Ready` again instead of running the exit path (deferred-resource drop, dtor
drain, exit-record emit), so a successful expression does not drain the
evaluator process or discard its mailbox, heap, or runtime-owned state.

Each compiled chunk is a fresh `CodeImage` — an `Rc<Module>` paired with its
`Rc<ModulePlan>`. `FnId`s are module-local, so each runnable process carries the
image it was created under (`code_images: HashMap<u32, Rc<CodeImage>>`).
Enqueuing an entry sets the evaluator pid's image to the newest one, so the
evaluator runs the latest chunk; a child spawned earlier keeps its own image, so
a child blocked in `receive` resumes against the image it was spawned under even
after later prompts compile newer chunks.

`eval_entry` takes the most recent completion belonging to the evaluator pid as
the chunk's result; if no evaluator completion came back, the chunk is reported
blocked.

## Source World Policy

Macro definitions, docs, and `@spec` text are world work, owned by the
`CompileTimeEvaluator`; user runtime code is lowered IR run on `ReplRuntime`.
`load_docs_and_macros` flattens modules, records moduledocs, registers macros,
expands macro calls, then loads non-macro fns as closures in the evaluator's
globals.

```text
macro definitions -> ReplWorld compile-time evaluator (globals, macro_names)
macro bodies       -> expanded by ReplWorld before fn load
user runtime code  -> lowered IR on ReplRuntime
```

The `CompileTimeEvaluator` holds the source world the REPL queries: `globals`
(fn closures carrying their `@doc`/`@spec` text), `module_docs` (qualified path →
`@moduledoc`), and the macro tables (`macro_names`, `macro_def_spans`). It also
owns a single-threaded `EvalRuntime` with per-pid `mailboxes` and `send`/`spawn`/
`receive` over them, but no scheduler: an empty `receive` with no `after` errors
("receive would block on an empty mailbox") instead of parking the process. That
missing park/resume is the reason interactive code lives on `IrInterpRuntime`
instead — any expression that relies on `spawn`/`receive` to suspend and resume
needs the real scheduler, which keeps interactive code on the same runtime path
as ordinary programs.

Help queries are world work. `lookup_doc` reads the evaluator's globals and
moduledocs: it tries fns first (so `?M.add` finds the closure and renders its
`@spec` lines and `@doc` text), then falls back to a moduledoc lookup (so `?M`
finds the module). It never drives `ReplRuntime`, so a blocked evaluator process
does not prevent help from answering.

## Script Mode

`fz repl --script <path>` shares the frontend/runtime model but not the terminal
presentation. `ReplSession::run_script_str_with_telemetry` compiles the whole
file through the module pipeline, then runs `main/0` on a fresh `ReplRuntime`
via `run_script_main` (driven with `keepalive = false`) when a zero-parameter
`main` is present; with no such `main` it succeeds and runs nothing. It emits no
prompts and echoes no expression display values, so program-side `dbg()` is the
only script-mode stdout — which makes a fixture's REPL leg exact-comparable to
the other legs' golden output.

Script mode bypasses `rustyline` and `ReplComposer` because whole-file parsing
already provides the complete-source boundary.

## Module Artifact Policy

The interactive REPL is session-eager. Interactive chunks compile against the
source world accumulated in `ReplWorld` plus the built-in runtime-library
interfaces that ordinary frontend compilation sees. Both REPL paths build
`ProviderInputs` with the default artifact root and an empty provider list, so
neither loads user provider artifacts. The compile flags that select providers
(`--interface`, `--provider`, `--artifact-root`) live on the `run`, `build`, and
`dump` subcommands, not on `repl`.

`fz repl --script` has one whole-file root source, so it runs the
provider-free execution-graph path and can materialize reachable built-in
runtime modules; it still loads no user provider roots.

The choice keeps the persistent session simple: the REPL has one mutable source
world and one persistent evaluator image, while artifact-backed imports belong
to whole-file commands with an explicit root source and explicit provider roots:

```sh
fz run --interface Math --artifact-root build/fz consumer.fz
fz build --interface Math --artifact-root build/fz consumer.fz -o consumer
```

## Error And Blocking Policy

Parse, type, and lowering errors are reported and leave `ReplRuntime` untouched
(the runtime is built only once an expression compiles cleanly).

Runtime errors are reported for the current chunk. The session keeps the runtime
when the evaluator process state is still well-defined after the drive returns.

If a chunk parks the evaluator on `receive`, `drive_until_idle` can return with
no evaluator completion. That surfaces as blocked state — the runtime invents no
value and does not partially reset.

## Ownership Boundaries

```text
ReplComposer  : classifies a submitted buffer; owns no source, prompt, or cursor
ReplLineEditor: terminal editing, history, multiline read; runs no chunks
ReplWorld     : source-world memory + macros/docs/specs; answers help
ReplFrame     : ordered runtime bindings; no pattern-matching or evaluation
ReplRuntime   : the persistent IrInterpRuntime and evaluator process
```

Pattern matching, binding decisions, and expression evaluation all happen in
lowered IR on `ReplRuntime`; `ReplFrame` only carries the ordered values between
prompts.
