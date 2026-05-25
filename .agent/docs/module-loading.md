# Module Loading And Code Images

## ELI5 Model

Think of a module name as a library shelf label and a code image as one printed
copy of the book on that shelf.

The library catalog points new readers at the newest copy. Readers who already
have an older copy can keep reading it safely. A local page reference inside the
book stays inside that copy. A catalog lookup by module and function can enter
the newest copy.

That is the model FZ wants for interpreter and JIT execution:

```text
exported module call -> CodeServer catalog -> module current image
local call           -> current process image -> image-local FnId
blocked continuation -> pinned image         -> resume there later
```

AOT uses the same module and export identity, but its catalog is generated at
build time and is not a dynamic loader.

## Terms

`ModuleName` is the stable source identity of a module. It is structured data,
not a dotted function-name string. Display code may render it as text, but
runtime dispatch must not treat that rendering as identity.

`ExportKey` is `(ModuleName, function_name, arity)`. It identifies a callable
module export across code images. It is the key used for exported module calls.

`FnId` is image-local. It identifies one lowered function inside one IR or
compiled image. It is valid only with the image that produced it.

`CodeImage` is immutable executable content plus metadata for one compiled
version. Interpreter images contain an IR module. JIT images contain executable
code and the runtime metadata needed to run it. Images are reference-counted or
otherwise pinned while any process, continuation, closure, or scheduler record
can resume into them.

`ModuleSlot` is the CodeServer entry for one `ModuleName`.

```text
ModuleSlot {
  current: CodeImage,
  old: Option<CodeImage>,
}
```

`CodeServer` owns module slots and resolves exported calls. It also owns the
replacement and purge policy for interpreter and JIT execution.

## Call Semantics

Local calls stay inside the current image. Lowering may encode them as `FnId`s
because both caller and callee belong to the same image.

Exported module calls resolve through `CodeServer` by `ExportKey`. The resolved
entry returns an image pin plus the image-local entry target for that image.
This is the explicit boundary where a process may enter newer code.

Self-calls are not special. A call that was lowered as local recursion stays in
the current image. A call lowered as an exported module call to the same module
goes through `CodeServer` and may enter that module's current image.

Spawned work inherits the image that created the runnable closure or entry.
If later work enters by exported module call, it resolves through `CodeServer`
at that point.

Blocked receives and continuations resume against the image they captured. They
must never be silently rewritten to newer code.

## Replacement And Purge

Loading the first version of module `M` creates `M.current`.

Loading a replacement for `M` validates the new image and its exports first.
Only after validation succeeds does `CodeServer` move the previous current image
to `M.old` and install the new image as current.

Soft purge removes an old image only when it is not pinned by any process,
continuation, closure, run queue entry, parked receive, or backend-owned runtime
record. If the image is still referenced, soft purge refuses.

Hard purge is explicit policy. It may terminate processes or scheduler records
that can resume into the old image, then drop the image after those references
are gone. It must never leave a resumable record pointing at freed code.

Interpreter and JIT replacement share the same observable semantics. The JIT
adds one extra ownership requirement: executable memory remains live until no
resumable runtime state can call into it.

## AOT Policy

AOT is closed-world by default.

The AOT compiler emits a fixed module/export table from the program being
compiled. Exported module calls resolve through generated metadata or direct
symbols. There is no implicit filesystem path search, no runtime autoload, and
no dynamic replacement API in the default AOT runtime.

If a future plugin system exists, it must be an explicit ABI with its own ticket
and tests. It is not a compatibility bridge for dynamic module loading.

## Current FZ Mapping

`Program.modules` is the resolver-owned structural module declaration list. It
records `ModuleName`s, exports, aliases, and imports even while the current
frontend still emits flattened function items for downstream compatibility
inside this epic. Treat those structural declarations as the frontend invariant
for module identity; do not recover identity by splitting rendered fn names.

`Module.exports` is the IR image's export table. Each entry has an `ExportKey`
(`ModuleName`, function name, arity) plus the image-local `FnId` that implements
that export. `ExportKey` is stable across images; `FnId` is not.

`IrInterpRuntime` already owns the process table, run queue, blocked receive
records, resume records, and per-process `CodeImage`s. Its current `CodeImage`
wraps an `Rc<Module>`. This is the right ownership shape for image pinning, but
it currently lacks a module slot catalog for exported calls.

`ReplWorld` owns source-world definitions, modules, imports, aliases, macros,
docs, specs, type declarations, and chunk history. It should keep owning source
knowledge. Runtime module loading belongs below it: compiled chunks should
install images through the same runtime CodeServer path used by non-REPL
execution.

`ReplRuntime` owns the persistent evaluator process and an `IrInterpRuntime`.
Today, each compiled chunk advances the evaluator to the newest image while
spawned children can retain older images. That behavior should become a normal
CodeServer image-entry operation rather than a REPL-only convention.

`CompiledModule` currently owns one JIT module, function pointer table, schema
registry, frame metadata, atom names, static closure targets, scheduler shim
addresses, and diagnostics. Under this epic, those fields become the payload of
a JIT `CodeImage` pinned by processes and continuations. Export lookup should
return an image pin plus an entry pointer/ABI target, not just a raw function
address detached from image lifetime.

`emit_aot_c_main` currently emits fixed startup wiring: setup process metadata,
register static closures and tuple schemas, install scheduler shims, and call
the generated main entry. That is already a closed-world shape. The AOT work is
to generate module/export identity into that fixed world, not to add dynamic
loading.

`resolve::flatten_modules` currently erases module identity into dotted
function names before later compiler phases. That behavior may remain as a
temporary frontend implementation detail while this epic is in progress, but it
must stop being runtime authority by the end.

## Invariants

- Module identity is structured and survives into IR/runtime metadata.
- Rendered dotted names are diagnostics/debug text only.
- `FnId` never crosses image boundaries without the image that owns it.
- Local calls use the caller's current image.
- Exported module calls resolve through `CodeServer` in interpreter and JIT.
- Suspended runtime state pins the image it can resume into.
- Replacement never mutates an existing image.
- Soft purge never frees referenced code.
- Hard purge explicitly terminates or removes every resumable reference first.
- AOT has no implicit dynamic module discovery.

## Failure Modes

Missing module export: exported lookup by `ExportKey` fails with a diagnostic
that names the module, function, and arity.

Stale local `FnId`: using a `FnId` with the wrong image is a runtime/compiler
bug. Tests should make this structurally hard by carrying image pins with entry
targets.

Replacement validation failure: the old current image remains current and no
slot mutation occurs.

Soft purge refused: the caller receives a refusal that identifies the old image
as still referenced. No process is killed and no code is freed.

Hard purge termination: affected processes or records are terminated by the
documented policy. They do not resume into missing code.

JIT image lifetime bug: executable memory freed while a process can resume is a
correctness failure. Image pins must own or retain the executable allocation.

AOT dynamic load request: the default AOT runtime rejects it with a crisp
diagnostic or exposes no such API.

## Tests To Write

Frontend tests:

- A module declaration lowers to structured `ModuleName` metadata.
- Alias/import resolution produces module/function references, not dotted
  dispatch strings.
- Two module identities that render similarly cannot collide as runtime
  identities.

IR tests:

- Local calls and exported module calls dump differently and deterministically.
- `FnId` remains image-local while `ExportKey` is stable across images.
- Export metadata survives reducer, typer, DCE, inlining, and debug rendering.

CodeServer tests:

- First load creates a current image.
- Replacement moves current to old and installs the new current atomically.
- Third load obeys the documented old-image policy.
- Soft purge refuses while an old image is pinned.
- Hard purge removes or terminates all resumable references before dropping the
  image.

Interpreter tests:

- A blocked child resumes against the old image after replacement.
- A new exported call enters the current image.
- Local recursion stays in the old image after replacement.
- An exported self-call can cross to the current image.
- REPL chunk advancement uses the same CodeServer path as ordinary execution.

JIT tests:

- JIT replacement preserves executable memory while old continuations can
  resume.
- New exported calls use the current image.
- Suspended continuations are not rewritten during replacement.
- Export lookup is explicit enough to observe in diagnostics or telemetry.

AOT tests:

- Generated code contains a closed-world module/export table or direct-symbol
  equivalent.
- Exported module calls resolve without runtime filesystem discovery.
- Runtime dynamic-load attempts are rejected or impossible through the public
  API.
- Existing module/import fixtures pass through the AOT path.

End-to-end tests:

- Interp, JIT, and AOT agree on normal cross-module call behavior.
- Interp and JIT replacement behavior matches the CodeServer spec.
- AOT rejects or omits dynamic replacement behavior by design.

## What Gets Deleted

The runtime authority of dotted function names gets deleted.

By the end of this epic, code may still render names like `A.B.f/2` for users,
diagnostics, snapshots, or symbols, but dispatch must not depend on splitting or
comparing those strings as module identity. Comments and docs that say
downstream execution is module-unaware must be removed or rewritten.
