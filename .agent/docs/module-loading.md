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
records `ModuleName`s, exports, aliases, and imports. Treat those structural
declarations as the frontend invariant for module identity; do not recover
identity by splitting rendered fn names.

`Module.exports` is the IR image's export table. Each entry has an `ExportKey`
(`ModuleName`, function name, arity) plus the image-local `FnId` that implements
that export. `ExportKey` is stable across images; `FnId` is not.

`code_server::CodeServer` is the backend-neutral slot owner. It keeps one
current image and at most one old image per `ModuleName`. Image pins are `Arc`
clones. A soft purge removes old code only when the slot is the sole owner; a
hard purge detaches old code from the slot while any existing pins keep the
image payload alive.

`IrInterpRuntime` owns the interpreter `CodeServer<Module>`, process table, run
queue, blocked receive records, resume records, and per-process `CodeImage`
pins. `enqueue_entry` installs the supplied IR module through the CodeServer
and pins the resulting image for the target pid. Spawned children inherit the
sender image. `Term::ExportCall` and `Term::ExportTailCall` resolve through the
runtime CodeServer; local calls use the process image and image-local `FnId`s.

`ReplWorld` owns source-world definitions, modules, imports, aliases, macros,
docs, specs, type declarations, and chunk history. It does not own runtime
module slots. Compiled chunks install images through the same runtime
CodeServer path used by non-REPL execution.

`ReplRuntime` owns the persistent evaluator process and an `IrInterpRuntime`.
Each compiled chunk advances the evaluator by calling the interpreter
`enqueue_entry` path. That installs the chunk in the same CodeServer used by
non-REPL interpreter execution, while spawned children can retain older image
pins.

`CompiledModule` owns one JIT module, function pointer table, schema registry,
frame metadata, atom names, static closure targets, scheduler shim addresses,
export metadata, and diagnostics. `Runtime` installs compiled modules into a
CodeServer and pins a JIT `CodeImage` per process. Spawned closure tasks inherit
the sender's image. Exported tail calls resolve through the runtime CodeServer
helper, switch the process pin to the resolved current image, and then jump to
the resolved image's entry pointer. Local calls and suspended continuations keep
using their image-local targets.

`emit_aot_c_main` emits fixed startup wiring: setup process metadata, register
static closures and tuple schemas, install scheduler shims, and call the
generated main entry. AOT codegen uses `ExportDispatch::ClosedWorld`: exported
tail calls lower to the IR export table's image-local target during object
generation. The AOT object does not import the JIT dynamic export resolver and
there is no AOT runtime module-loading API.

`resolve::flatten_modules` may still render qualified function names into the
flat item list for diagnostics and symbol names. That rendered text is not
runtime authority. Runtime module identity comes from `ModuleName` and
`ExportKey` metadata.

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

AOT dynamic load request: the default AOT runtime exposes no such API.

## Implemented Coverage

Frontend and IR tests:

- `resolve::tests::records_structural_module_declaration_and_exports` proves
  `Program.modules` records structured module declarations and exports.
- `ir_lower::tests::lower_records_structural_module_exports` proves
  `Module.exports` carries `ExportKey` plus image-local `FnId`.
- `code_server::tests::module_identity_is_structural_not_rendered_dotted_text`
  proves similarly rendered module names do not collide as runtime identities.
- `fz_ir::tests::export_call_terms_render_symbolically` proves exported calls
  dump as export ids instead of image-local direct calls.

CodeServer tests in `src/code_server.rs` cover:

- First load creates a current image.
- Replacement moves current to old and installs the new current atomically.
- Third load obeys the documented old-image policy.
- Soft purge refuses while an old image is pinned.
- Hard purge detaches the old image from the slot while existing `Arc` pins keep
  the image payload alive.

Interpreter tests in `src/ir_interp/tests` cover:

- A blocked child resumes against the old image after replacement.
- A new exported call enters the current image.
- Local recursion stays in the old image after replacement.
- An exported self-call can cross to the current image.
- REPL chunk advancement uses the same CodeServer path as ordinary execution.

JIT tests in `src/runtime.rs` cover:

- New exported calls use the current image.
- A new spawn after replacement enters the current image.
- Spawned closure tasks inherit the sender's image.

AOT tests in `src/ir_codegen/tests.rs` cover:

- `aot_exported_tail_call_uses_closed_world_target` proves AOT export dispatch
  uses the closed-world export table/direct target and does not import the JIT
  dynamic resolver.

End-to-end fixture coverage:

- `fixtures/module_export_dispatch` runs through interp, JIT, AOT, and REPL to
  prove normal module export dispatch agrees across execution paths.
- Existing module/import fixtures also run through the AOT path.

## Intentionally Unsupported

- AOT does not load, replace, purge, or discover modules at runtime.
- The default AOT runtime exposes no dynamic module-loading API.
- `Term::ExportCall` is implemented by the interpreter, but codegen rejects it
  until non-tail exported calls have an explicit lowering policy for JIT and
  AOT.
- Runtime dispatch does not split dotted function names to recover module
  identity.
- Hard purge in `CodeServer` detaches old images from slots; it does not
  terminate processes by itself.

## What Gets Deleted

The runtime authority of dotted function names gets deleted.

By the end of this epic, code may still render names like `A.B.f/2` for users,
diagnostics, snapshots, or symbols, but dispatch must not depend on splitting or
comparing those strings as module identity. Comments and docs that say
downstream execution is module-unaware must be removed or rewritten.
