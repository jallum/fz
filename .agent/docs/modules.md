# Modules, Interfaces, and Runtime Sources

A module is a unit of separate compilation. The subsystem behind
`src/modules/mod.rs` answers four questions: who exists, what may others depend
on, how does a dependent compile against a provider without that provider's
implementation, and how do separately compiled units fuse into one runnable
image.

The shape of the answer is a layered boundary:

```text
private implementation   inferred inside one module
public module boundary    explicit interface facts (ModuleInterface)
dependent compile         consumes interface facts only
link                      copies provider IR in and resolves call edges
LTO                       loads implementations and erases boundaries
```

A dependent compile is correct knowing only interface facts. Whole-program
analysis (link, LTO) is an optimization layer on top of that proof, not the
proof itself.

The pieces that matter:

- `identity`: typed `ModuleName` / `Mfa` — the link identity, separate
  from any dotted display text.
- `interface`: `ModuleInterface`, the public contract, and the strict-export
  validator.
- `graph`: `ModuleGraphLoader`, which walks from root interfaces to the
  reachable runtime-library modules a runnable image needs.
- `pipeline`: source-first frontend, execution-graph preparation, and LTO.
- `runtime_library`: built-in standard-library modules as separate-compilation
  inputs.

Link-time fusion lives next door in `ir_codegen` (`link_ir_units`,
`CompiledUnit`, `CompiledImage`).

## Identity

`modules::identity` holds the typed names. The frontend renders many names as
dotted strings (`Math.add/2`) because the IR is string-shaped, but those
strings are display spellings, not the identity.

- `ModuleName` is a list of path segments (`segments: Vec<String>`). It is built
  from parsed segments via `from_segments` / `child`; `dotted()` renders the
  edge spelling.
- `QualifiedName` is `{ module: Option<ModuleName>, name: String }` — a
  possibly module-qualified function or type name that bridges flattened IR
  spellings.
- `Mfa` is the link identity of a public function:

```text
module: ModuleName
name:   String
arity:  usize
```

`Math.add/2` is what `Mfa::fmt` prints; the key itself is
`Mfa { module: Math, name: "add", arity: 2 }`. Link and interface code
key on the typed value.

## Interface Emission

`modules::interface::collect_from_program` runs over the source-level AST while
module and protocol declarations still exist. It returns one `ModuleInterface`
per module, keyed by `ModuleName`, plus one for each root `defprotocol`
namespace (a root protocol has no containing module but still publishes a
first-class public namespace, so it gets a module-shaped interface keyed by the
protocol name).

`ModuleInterface` carries only contract data:

- `name`: the `ModuleName`;
- `abi_version`: `FZ_INTERFACE_ABI_VERSION`;
- `imports`: declared imports with their `only` / `except` filters;
- `exports`: `Vec<InterfaceFn>` — public functions by name, arity, and ordered
  `@spec` overload set;
- `types`: public `@type` aliases, opaques, and refines (`InterfaceTypeKind` is
  `Alias` / `Opaque` / `Refines`);
- `protocols`: protocol declarations and their callback surfaces;
- `protocol_impls`: `(protocol, ImplTarget)` facts plus callback `Mfa`s;
- `docs`: optional `@moduledoc`;
- `fingerprint_inputs`: deterministic semantic strings used for compatibility.

A function reaches `exports` only when it is non-macro, non-private, has no
`extern_abi`, and is not the implicit `__info__/1` reflection builtin. So a
wrapper like `Utf8.valid?/1` is the export; the `extern "C"` primitive
`fz_bitstring_valid_utf8/1` and any `fnp` helper are implementation contracts
that stay out of the interface. Interface emission copies signatures, never
bodies, which is why a dependent can typecheck `Protocol.t(...)` domain
constraints and resolve imported calls without ever loading a provider body.

`fingerprint_inputs` is a stable list of strings (`abi=...`, `module=...`,
`import=...`, `type=...`, `fn=name/arity:specs=[...]`, `protocol=...`,
`protocol-impl=...`). `interface::fingerprint_digest` folds that list with FNV
into a 16-hex-digit string. Both the human-readable inputs and the digest are
the compatibility currency between separate compiles.

`validate_public_export_specs` enforces the library-boundary policy: every
module export needs an explicit `@spec`, or it reports `INTERFACE_MISSING_SPEC`
on the export's name span. Top-level non-module helpers are not interface
exports and stay inferable; `fnp` helpers inside a module participate in
same-module resolution and lowering but are omitted from `exports` and need no
public spec.

`render_interfaces` prints the human-readable contract dump used by
`fz dump --emit interfaces`.

## Import Resolution

`resolve::flatten_modules_with_interface_table` takes an external
`InterfaceTable`, injects the built-in runtime-library interfaces, and inserts
the current program's own collected interfaces (which win for a module name
they share). It uses interfaces to answer:

```text
does module M exist?
does M export f/N?
which module owns the bare imported call f(args...)?
```

Resolution behavior:

- `alias Missing` / `import Missing` -> `RESOLVE_UNKNOWN_MODULE`.
- `import M, only: [f: N]` checks `M`'s interface exports.
- the same `name/arity` imported from two modules -> `RESOLVE_CONFLICTING_IMPORT`.
- a local sibling function shadows an import.
- a bare imported call rewrites to the qualified flattened spelling, e.g.
  `add(x, y)` becomes `Math.add(x, y)`.

The flattened dotted spelling is the IR rendering; boundary code keys on the
typed `ModuleName` / `Mfa`.

## Runtime Reachability

`modules::graph::ModuleGraphLoader::load_reachable` starts from the root
`InterfaceTable` plus explicit runtime-root `ModuleName`s and produces a
`ModuleGraph { interfaces, runtime_modules }`.

It walks a worklist by public contract:

1. Queue each root's imports and the protocols of its `protocol_impls` (a
   `defimpl` depends on the protocol namespace as a public fact).
2. Pop a module. A runtime-library module is resolved through
   `runtime_library::interface`; when found, its imports and protocol-impl
   protocols are queued.
3. For each loaded runtime interface, queue any extra implementation-only
   runtime imports and any runtime modules that implement newly discovered
   protocols.

Two refinements:

- A protocol declaration already present in a loaded interface is a local fact.
  If `Contracts` owns nested protocol `Contracts.Collectable`, that protocol is
  not reloaded as a sibling module. Protocol-impl callback namespaces are
  export namespaces inside the defining module, not separate graph roots.
- Runtime-library implementation bodies may call other runtime modules that the
  interface does not advertise. `enqueue_runtime_implementation_imports` uses
  `runtime_library::implementation_dependencies` to scan checked-in
  runtime-library source for those references. This is consulted only for
  runtime modules.
- Runtime protocol implementation providers are discovered by comparing loaded
  protocol namespaces against the built-in runtime interface table. That keeps
  callback namespaces inside their owner modules while still loading reachable
  implementations such as `Enumerable.List`.

There is no user-module filesystem walk in this phase. User modules are present
only when they were part of the explicit source world compiled by the frontend;
an import of a missing user module fails in resolution instead of consulting a
sidecar store.

## Execution Graph and Linking

`modules::pipeline` turns a frontend result into a single linked IR module.
`CompileMode` is `Normal` or `Lto`.

Production callers do not usually stitch these functions together manually
anymore. `src/compiler.rs` is the facade that drives source/program frontend
work into `checked_module_for_mode`, then into `prepare_execution_graph`, and
stores the resulting linked module/plan pair on `compiler::World` before
handing that same world state to the interpreter or native backend. The world
names this execution image `linked_module` / `linked_module_plan` on purpose:
it is the fused runtime IR image, not one source `defmodule`.

`checked_module_for_mode` runs the frontend, collects the program's own module
interfaces (emitting `interfaces_collected`), and in `Lto` mode validates and
erases boundaries before planning. It yields a `CheckedModule` carrying the
module, its `ModulePlan`, its own interfaces, the external interfaces, the
`SourceMap`, and diagnostics.

`prepare_execution_graph` does source-first execution prep:

- It computes runtime roots from `runtime_library::prelude_required_modules()`
  plus any non-core runtime modules already named in the checked module's
  `external_interfaces`.
- `ModuleGraphLoader::load_reachable` returns the interface graph (emitting
  `graph_loaded`).
- The root `CheckedModule` becomes the first `CompiledUnit`.
- Each reachable runtime module is recompiled from its registered source text
  through `compile_source_with_interface_table(...)`, using the full graph
  interface table so runtime modules resolve imports the same way user modules
  do. Each of those units emits `unit_materialized` with
  `kind: "runtime-source"`.

With the units in hand, `link_execution_module` calls `link_ir_units` when there
is more than one unit (otherwise it is the single unit's `code`). The pipeline
then runs `plan_module_with_role(..., "linked_execution_graph")` over the linked
module; that linked-execution-graph plan is what downstream engines consume, so
passes that change dispatch or reachability must not run between link and that
plan.

### `link_ir_units` — the one correctness gate

`ir_codegen::link_ir_units` fuses reachable `CompiledUnit` IR into one dense
linked `Module`. `IrUnitLinker` copies each unit's fns, externs, external-call
edges, protocol facts, specs, planner facts, and type facts, remapping `FnId`,
`ExternId`, and atom ids as it goes; it builds an `Mfa -> FnId` map from
each unit's interface exports and protocol-impl callbacks; then it rewrites
`ExternalCallEdge` placeholders to direct local `FnId`s.

The checks, and the `ImageLinkError` each produces:

1. A unit whose recorded `interface_fingerprint` disagrees with its interface ->
   `InterfaceFingerprintMismatch`.
2. Two providers for one `Mfa` -> `DuplicateProvider`.
3. A copied `ExternalCallEdge` with no provider -> `MissingImport`.
4. A callsite that cannot be rewritten -> `UnresolvedExternalCalls`.

(`ImageLinkError` also has a `RuntimeMetadata` variant for runtime-table link
failures.)

`copy_planner_facts` carries upstream plans forward on a best-effort basis: each
unit's `module_plan` is remapped and merged into an internal `linked_plan` that
only needs to cover the edges the linker rewrites. Because the pipeline plans
the linked module again before codegen, a missing upstream planner fact is not a
link error.

The runtime-source units and the consumer link, plan as one module, and run
with no unresolved edges. Codegen rejects any edge that survives to it:
`unresolved external module call `Dep.run/0``.

### Compiled unit, program, image

`ir_codegen` names the link stages:

- `CompiledUnit` — one pre-link module: `code` (module-local IR), optional
  `module_plan`, `exports`, `interface`, and `interface_fingerprint`.
- `CompiledModule` — the JIT machine-code module (a `JITModule` plus per-fn
  pointer table and schemas). It is the executable payload, not the
  driver-facing product.
- `CompiledProgram` — one single-unit codegen result before image wrap, with
  `executable: CompiledModule`, `unit: CompiledUnit`, and
  `runtime: RuntimeUnitMetadata`.
- `CompiledImage` — a linked runnable image wrapping a `CompiledModule` and an
  optional `RuntimeImageMetadata`.

`CompiledProgram::link_image` is the single-unit JIT run path: it validates the
unit through `link_ir_units`, links that unit's runtime metadata, wraps the
machine-code module, and emits `link.succeeded` / `link.failed`.
Provider-backed runs link earlier through `prepare_execution_graph`, so
`CompiledImage::from_linked` only wraps an already-linked module and emits
`link.succeeded`.

### Runtime metadata linking

`RuntimeUnitMetadata` is one unit's runtime-global contribution: `module`,
`atoms`, `schemas`, `frame_sizes`, `exported_symbols`, `imported_refs`,
`static_closures`, `halt_kinds`, and `entrypoints`.
`RuntimeImageMetadata::link_units` deterministically merges those tables for
runtime and debug metadata. It is not the import-correctness gate; it enforces
its own table invariants:

- duplicate `module` identities are rejected (`DuplicateModule`);
- atoms are de-duplicated and sorted via `BTreeSet`;
- schemas are de-duplicated by `schema_key`;
- units are processed in stable module/input order;
- frame ids are relocated by per-unit frame bases;
- a duplicate exported runtime symbol is rejected (`DuplicateExport`);
- imported refs are de-duplicated and sorted;
- static closures are tagged with their input index and sorted;
- entrypoint requirements are OR'd together;
- per-input relocations are recorded in `RuntimeUnitRelocations`.

## LTO

LTO is validated boundary erasure. It consumes the same interface facts normal
mode does, but only after validation, and it is never the correctness path —
normal-mode linking already resolves every external edge.

The CLI LTO path:

1. `checked_module_for_mode` collects interfaces from the frontend result.
2. `LtoLinkedProgram::validate` runs `validate_public_export_specs` over the
   interfaces and emits `lto.interfaces_validated`. A missing public spec stops
   LTO here.
3. `LtoLinkedProgram::erase_boundaries` builds `Module::interface_export_map`
   (interface exports + protocol-impl callbacks -> loaded `FnId`s), calls
   `Module::rewrite_external_calls_for_lto`, clears the module's `boundary_fns`
   spec firewalls, and emits `lto.boundaries_erased`.
4. The caller materializes and codegens the direct-call module through the
   ordinary pipeline.

`LtoLinkedProgram` is private to `modules::pipeline`, so boundary erasure can
only follow validation — the ordering is enforced in the type shape, not by each
caller remembering it. Because erasure rewrites cross-module tail calls to
direct calls and lets inlining run, a call that exists before LTO can vanish
from `fz dump --emit bodies --lto`, which reads the same materialized reachable
body set.

`ExternalCallEdge { callsite: CallsiteId, target: Mfa }` in
`fz_ir::Module` is how an imported call is represented; its terminator carries a
placeholder `FnId` until link or LTO resolves the edge.

## Runtime Library Modules

`runtime_library` owns the built-in standard-library source set. The runtime has
two layers: primitive `extern "C"` contracts implemented by Rust/C symbols, and
ordinary FZ modules built on top of them.

`RUNTIME_MODULE_SOURCES` in `src/modules/runtime_library.rs` registers each
module with a `RuntimeModuleRole`:

- `CorePrelude` modules (`Kernel`, `Enumerable`, `Range`, `List`, `Map`) are
  prepended during lowering via `core_prelude_module_sources`, so their names
  are in scope without an explicit import.
- `Library` modules (`Process`, `Enum`, `Utf8`) are requested on demand.

`src/modules/runtime_library/runtime.fz` is the always-loaded prelude root: it
imports selected functions from core prelude modules (so raw extern declarations
stay module-scoped while names like `dbg/1` are exposed) and declares ordinary
global type aliases such as `keyword/0` and `keyword/1`. Runtime primitive
types such as `pid`, `ref`, and `utf8` are compiler-known built-ins, not aliases
in this file.

Each module's body lives in its own file (`utf8.fz`, `process.fz`, `enum.fz`,
...). `List`, `Map`, `Range`, `Enumerable`, and `Enum` carry the operator
helpers, protocol facts, and public enumeration wrappers. `Enumerable` is a root
`defprotocol`, so its public namespace is `Enumerable`; a nested `Foo.Enumerable`
would publish under that qualified path. Implementation detail stays in private
`fnp` helpers — `Enum.sort` is a merge sort over `sort_list` /
`merge_sort_lists`, none of which appear in the interface.

How a runtime module enters a compile:

- `runtime_library::interface` answers interface requests from imports, aliases,
  and qualified references — including the qualified runtime calls macros emit,
  so operator sugar can depend on `List` without every program importing it.
- `runtime_library::source` returns the checked-in source text for a reachable
  runtime module; `prepare_execution_graph` recompiles that source into a
  `CompiledUnit`.
- A reachable non-core runtime module contributes its interface and source to
  `ModuleGraphLoader`; the core prelude is already prepended during lowering.

Built-in interfaces are requested defaults. A user source module with the same
name is collected from the current program and wins for that compile.

To add a runtime-library module: add `src/modules/runtime_library/<name>.fz`
holding exactly one `defmodule Name do ... end` (or one root
`defprotocol Name do ... end`); register the file in `RUNTIME_MODULE_SOURCES`;
give it an `@moduledoc` and a narrowest-accurate `@spec` on every public export;
keep primitive `extern "C"` declarations module-scoped, exposing selected core
functions through `runtime.fz` imports. Standard-library growth prefers ordinary
FZ modules over a larger primitive runtime surface.

## Dumps and Telemetry

The product dumps follow the interface/implementation split:

- `fz dump --emit interfaces` renders public module contracts (with the
  fingerprint digest and inputs); `--strict-interfaces` rejects unspecified
  public exports.
- `fz dump --emit specs` renders the internal inferred `ModulePlan` — planner
  state, not a module ABI.
- `fz dump --emit bodies` renders reachable materialized user bodies from the
  codegen-facing `PlannedProgram`, after local rewrites and reachability
  pruning. `--lto` reads the post-erasure body set.

Interface dumps answer "what may other modules depend on?"; spec and body dumps
answer "what did this run infer and plan internally?". Raw IR dumps (`clif`,
`bodies`, `outcomes`, `specs`) are compiler-internal, not the
separate-compilation oracle.

Process facts stay out of product dumps and ride telemetry instead, inspectable
via `fz dump --emit stats`:

```text
fz.module.interfaces_collected
fz.module.unit_materialized   (kind = runtime-source)
fz.module.graph_loaded
fz.link.succeeded / fz.link.failed
fz.lto.interfaces_validated / fz.lto.boundaries_erased
```

## Command Surface

`fz dump --emit interfaces` is the public contract surface; add
`--strict-interfaces` to require explicit specs on public exports. `fz run`,
`fz build`, and `fz dump` always compile the root source directly and then load
reachable built-in runtime modules from checked-in source when the execution
graph needs them.

There are no `--emit-fzi`, `--emit-fzo`, `--interface`, `--provider`, or
`--artifact-root` flags anymore. User-module separate compilation is source
explicit: if a program needs another user module, that module must be part of
the source world being compiled.

`fz repl` is session-eager: it compiles against source already entered into the
REPL world plus built-in runtime-library interfaces. `fz repl --script` has one
whole-file root, so it takes the source-first execution-graph path and can
materialize reachable built-in runtime modules. REPL commands load no user
module store because there is none.

Tests follow the same split: assert public contracts with
`fz dump --emit interfaces`; assert execution-graph and linking behavior with
source-first `run` / `build` / `repl --script` fixtures.
