# Modules, Interfaces, and Artifacts

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

- `identity`: typed `ModuleName` / `ExportKey` — the link identity, separate
  from any dotted display text.
- `interface`: `ModuleInterface`, the public contract, and the strict-export
  validator.
- `artifact`: `FziArtifact` (`.fzi`) and `FzoArtifact` (`.fzo`) serde envelopes
  with ABI and fingerprint checks.
- `artifact_store`: `ModuleName` -> filesystem path policy and `.fzi`/`.fzo` IO.
- `graph`: `ModuleGraphLoader`, which walks from root interfaces to the provider
  artifacts a runnable image needs.
- `pipeline`: provider-aware frontend, execution-graph preparation, and LTO.
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
- `ExportKey` is the link identity of a public function:

```text
module: ModuleName
name:   String
arity:  usize
```

`Math.add/2` is what `ExportKey::fmt` prints; the key itself is
`ExportKey { module: Math, name: "add", arity: 2 }`. Link and artifact code key
on the typed value.

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
- `protocol_impls`: `(protocol, ImplTarget)` facts plus callback `ExportKey`s;
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
typed `ModuleName` / `ExportKey`.

## Artifacts: `.fzi` and `.fzo`

`modules::artifact` owns two serde envelopes. Each serializes as a one-line
magic header (`fzi` / `fzo`) followed by pretty JSON. `decode` rejects a wrong
header; the typed deserializer plus explicit ABI/fingerprint checks reject
incompatible content. Every load failure is an `ArtifactFormatError` rendered as
an `artifact/invalid` diagnostic.

### `.fzi` — the interface artifact

`FziArtifact` is the public contract artifact and nothing else:

```text
compiler_abi_version:         FZ_ARTIFACT_ABI_VERSION
runtime_abi_version:          FZ_RUNTIME_ARTIFACT_ABI_VERSION
interface_fingerprint_digest: hex digest of interface_fingerprint
interface_fingerprint:        Vec<String>
interface:                    ModuleInterface
```

`InterfaceFn.specs` and protocol-callback specs are ordered overload sets;
every `@spec` arrow appears in the fingerprint in source order, so a separate
compile sees the same correlated arrows the source module did.

`FziArtifact::deserialize` rejects: wrong/missing header; unsupported
compiler / runtime / interface ABI; malformed JSON or typed fields; a
fingerprint digest that does not match the recomputed digest; fingerprint
inputs that disagree with `interface.fingerprint_inputs`; and (when the caller
passes one) an expected fingerprint that does not match. Strict-export
validation is separate from deserialization — an export can deserialize without
a spec, but the emit path validates first.

### `.fzo` — the implementation-unit envelope

`FzoArtifact` carries an implementation, not a contract. The graph loader
consumes it only after interface compatibility is established:

```text
compiler_abi_version:           FZ_ARTIFACT_ABI_VERSION
runtime_abi_version:            FZ_RUNTIME_ARTIFACT_ABI_VERSION
module:                         Option<ModuleName>
unit_payload:                   FzoUnitPayload { format, body }
required_imports:               Vec<ExportKey>
implementation_fingerprint:     Vec<String>
implementation_fingerprint_digest: hex digest over the payload
interface_fingerprint_digest:   hex digest of interface_fingerprint
interface_fingerprint:          Vec<String>
```

`required_imports` is derived from the unit's `external_call_edges`, so an
imported module's `.fzo` can be emitted without machine-codegenning its
unresolved external calls. The payload format is one of three constants:

- `FZO_PAYLOAD_IR_UNIT_V1` (`fz-ir-unit-v1`) — a structural IR unit: the
  serialized `fz_ir::Module` plus every `PortableSourceFile` its spans
  reference (each with name, bytes, FNV content hash, and the provider's
  `FileId`). `FzoArtifact::from_unit_ir` builds it; this is what `fz build`
  emits.
- `FZO_PAYLOAD_RUNTIME_MODULE_V1` (`fz-runtime-module-v1`) — built-in
  runtime-library source text, materialized per execution context.
- `FZO_PAYLOAD_SOURCE_UNIT_V1` (`fz-source-unit-v1`) — checked source text;
  built by `from_unit_source` for tests.

`implementation_fingerprint_digest` is recomputed at load via `payload_digest`
(FNV over format tag + full body). It catches a payload that was swapped for a
different-but-still-valid-JSON body while other fields stayed stale.

Two reader gates split the payloads by how they are consumed:

- `source_unit_text` returns the body for the two source-shaped formats
  (`fz-source-unit-v1`, `fz-runtime-module-v1`) and rejects anything else, so
  inspection-only payloads cannot masquerade as materializable source.
- `ir_unit_payload` decodes a `fz-ir-unit-v1` body back into its `Module` +
  `sources`, and rejects any other format.

`FzoArtifact::deserialize` rejects: wrong/missing header; compiler/runtime ABI
mismatch; empty payload format or body; an interface fingerprint digest or
fingerprint mismatch; and a payload digest mismatch.

### Store paths

`modules::artifact_store::ArtifactStore` maps typed `ModuleName` values to
deterministic paths under a root (`DEFAULT_ARTIFACT_ROOT` is `build/fz`):

```text
build/fz/interfaces/<parent segments>/<last segment>.fzi
build/fz/objects/<parent segments>/<last segment>.fzo
```

```text
Utf8        -> build/fz/interfaces/Utf8.fzi          / objects/Utf8.fzo
Outer.Inner -> build/fz/interfaces/Outer/Inner.fzi   / objects/Outer/Inner.fzo
```

`path_for` consumes `ModuleName::segments()`; it never splits dotted text.
`validate_path_segment` requires each segment to be non-empty, not `.` or `..`,
and ASCII alphanumeric or `_`, so `.`, separators, spaces, and punctuation are
rejected before any filesystem touch.

The store owns the small IO helpers and emits process telemetry as it goes:
`write_fzi_artifacts` (`fzi_written`), `write_fzo_artifacts` (`fzo_written`),
`load_interface_table` (`fzi_loaded`), and `load_fzo_artifact` (`fzo_loaded`).
`load_fzi_artifact` reads one `.fzi` without emitting an event; the graph loader
calls it directly while walking the import tree.

## Reachable Graph Loading

`modules::graph::ModuleGraphLoader::load_reachable` starts from the root
`InterfaceTable` plus explicit provider-root `ModuleName`s and produces a
`ModuleGraph { interfaces, objects }`.

It walks a worklist by public contract:

1. Queue each root's imports and the protocols of its `protocol_impls` (a
   `defimpl` depends on the protocol namespace as a public fact).
2. Pop a module. A runtime-library module is resolved through
   `runtime_library::interface` before the filesystem store; a user module is
   loaded as a provider `.fzi`. Either way its imports and protocol-impl
   protocols are queued.
3. After all interfaces are reachable, load one `.fzo` per reachable module:
   runtime modules contribute their built-in `fz-runtime-module-v1` object, user
   modules load their `.fzo` from the store. Each user `.fzo` is validated
   against the `.fzi` fingerprint inputs that made the module reachable.

Two refinements:

- A protocol declaration already present in a loaded interface is a local fact.
  If a provider artifact `Contracts` owns nested protocol `Contracts.Collectable`,
  that protocol is not reloaded as a sibling `.fzi`. Protocol-impl callback
  namespaces are export namespaces inside the defining module's object, not
  separate artifact roots.
- Runtime-library implementation bodies may call other runtime modules that the
  interface does not advertise. `enqueue_runtime_implementation_imports` uses
  `runtime_library::implementation_dependencies` to scan checked-in
  runtime-library source for those references. This is consulted only for
  runtime modules; user implementation dependencies are carried by imports and
  provider roots.

Unused artifacts under the root are never read, so a stray `.fzo` for an
unreachable module cannot corrupt a build.

## Execution Graph and Linking

`modules::pipeline` turns a frontend result into a single linked IR module.
`CompileMode` is `Normal` or `Lto`.

`checked_module_for_mode` runs the frontend, collects the program's own module
interfaces (emitting `interfaces_collected`), and in `Lto` mode validates and
erases boundaries before planning. It yields a `CheckedModule` carrying the
module, its `ModulePlan`, its own interfaces, the external provider interfaces,
the `SourceMap`, and diagnostics.

`prepare_execution_graph` -> `load_provider_units` does the provider work:

- Provider roots are the explicit `--interface`/`--provider` modules, the
  prelude-required modules, and any non-core runtime module that appears in the
  external interfaces.
- `ModuleGraphLoader::load_reachable` returns the graph (emitting
  `graph_loaded`).
- Each reachable object becomes a `CompiledUnit`. A `fz-ir-unit-v1` object is
  materialized structurally; any other (source-shaped) object is recompiled
  through the frontend.

`materialize_ir_unit` is the structural load — it makes a provider available
without recompiling: decode the `Module` + `sources`, intern those source files
into the consumer `SourceMap`, remap the module's `FileId`s onto the interned
ids, `rebuild_indices` for the serde-dropped derived maps, and
`plan_module_with_role(..., "artifact_materialization")` the loaded unit. That
load-time plan regenerates the cross-module/protocol call facts the linker
needs, and because source identity is portable, the provider's spans render
real diagnostics against its own source after the merge. It emits
`unit_materialized` with `kind: "ir-unit"`; the recompile branch emits the same
event with `kind: "source"`.

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
`ExternId`, and atom ids as it goes; it builds an `ExportKey -> FnId` map from
each unit's interface exports and protocol-impl callbacks; then it rewrites
`ExternalCallEdge` placeholders to direct local `FnId`s.

The checks, and the `ImageLinkError` each produces:

1. A unit whose recorded `interface_fingerprint` disagrees with its interface ->
   `InterfaceFingerprintMismatch`.
2. Two providers for one `ExportKey` -> `DuplicateProvider`.
3. A copied `ExternalCallEdge` with no provider -> `MissingImport`.
4. A callsite that cannot be rewritten -> `UnresolvedExternalCalls`.

(`ImageLinkError` also has a `RuntimeMetadata` variant for runtime-table link
failures.)

`copy_planner_facts` carries provider plans forward on a best-effort basis: each
unit's `module_plan` is remapped and merged into an internal `linked_plan` that
only needs to cover the edges the linker rewrites. Because the pipeline plans
the linked module again before codegen, a missing upstream planner fact is not a
link error.

`materialize_ir_unit`-backed providers and the consumer link, plan as one
module, and run with no unresolved edges. Codegen rejects any edge that survives
to it: `unresolved external module call `Dep.run/0``.

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

`ExternalCallEdge { callsite: CallsiteId, target: ExportKey }` in
`fz_ir::Module` is how an imported call is represented; its terminator carries a
placeholder `FnId` until link or LTO resolves the edge.

## Runtime Library Modules

`runtime_library` owns the built-in standard-library source set and exposes each
module as the same `.fzi`/`.fzo` facts a user library would provide. The runtime
has two layers: primitive `extern "C"` contracts implemented by Rust/C symbols,
and ordinary FZ modules built on top of them.

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
- `runtime_library::artifacts` builds the deterministic `.fzi`/`.fzo` envelopes
  for every built-in module and root protocol namespace; the objects are
  `fz-runtime-module-v1` source payloads.
- A reachable non-core runtime module contributes its `.fzo` to
  `ModuleGraphLoader`; the core prelude is already prepended during lowering.

Built-in interfaces are requested defaults. A user source module with the same
name is collected from the current program and wins for that compile, while
artifact paths stay module-name based — so a distributor avoids shipping a user
and a built-in artifact under one module identity in one root.

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
fz.module.fzi_written / fzi_loaded / fzo_written / fzo_loaded
fz.module.unit_materialized   (kind = ir-unit | source)
fz.module.graph_loaded
fz.link.succeeded / fz.link.failed
fz.lto.interfaces_validated / fz.lto.boundaries_erased
```

## Command Surface

`fz build --emit-fzi --emit-fzo --artifact-root build/fz in.fz -o app` writes
artifacts: either emit flag first runs strict public export-spec validation;
`--emit-fzi` writes one `.fzi` per module; `--emit-fzo` writes the root unit as a
structural `fz-ir-unit-v1` object whose sources are the unit's referenced files.

`fz run` and `fz build` accept `--interface <Module>` (alias `--provider`) and
`--artifact-root <dir>`. `--interface` loads a provider's `.fzi` into the
resolver's external `InterfaceTable`, which proves provider-source-free import
validation; the current file's own interfaces still override external entries
for a shared name. Running or building the provider's body is the graph/linker
stage's job: those commands load reachable `.fzo` payloads through
`ModuleGraphLoader`, materialize provider `CompiledUnit`s, link, and reject
missing or duplicate providers before execution/codegen.

`fz repl` is session-eager: it compiles against source already entered into the
REPL world plus built-in runtime-library interfaces. `fz repl --script` has one
whole-file root, so it takes the provider-free execution-graph path and can
materialize reachable built-in runtime modules. REPL commands take no
`--interface`, `--provider`, or `--artifact-root` and load no user provider
artifacts; artifact-backed imports belong to whole-file `fz run` / `fz build`,
where root source and provider roots are explicit.

Tests follow the same split: assert public contracts with `.fzi` artifacts or
`fz dump --emit interfaces`; assert implementation-unit and graph behavior with
`.fzo` round-trips and provider-source-free `run`/`build` fixtures.
