# Modules, Interfaces, and Artifacts

Use this when changing module resolution, interface emission, separate
compilation artifacts, image linking, runtime-library modules, or LTO boundary
erasure.

## Core Invariant

Module correctness must not depend on loading dependency implementation bodies.

The compiler boundary is:

```text
private implementation code -> inferred inside one module
public module boundary      -> explicit interface facts
normal dependent compile    -> consumes interface facts only
LTO                         -> may load implementations and erase boundaries
```

Whole-program analysis is an optimization mode, not the proof of correctness.

## Identity Types

Do not recover module facts by splitting display strings if typed facts are
available.

- `ModuleName` is the semantic module path. It is built from parsed path
  segments and can render to dotted text at the edge.
- `QualifiedName` is a possibly module-qualified function/type name. It exists
  mostly to bridge current flattened IR spellings.
- `ExportKey` is the link identity for a public function:

```text
module: ModuleName
name:   String
arity:  usize
```

The display spelling `Math.add/2` is not the source of truth. The source of
truth is `ExportKey { module: Math, name: add, arity: 2 }`.

## Interface Emission

`modules::interface::collect_from_program` runs while source-level `ModuleDef`
nodes still exist. It produces one `ModuleInterface` per module.

`ModuleInterface` contains:

- `name`: the `ModuleName`;
- `abi_version`: currently `FZ_INTERFACE_ABI_VERSION`;
- `imports`: declared module imports and their `only` / `except` filters;
- `exports`: non-macro, non-extern public functions by name and arity;
- `types`: public module type aliases, opaques, and refines;
- `protocols`: protocol declarations and callback surfaces owned by the
  module;
- `protocol_impls`: `(protocol, ImplTarget)` implementation facts and callback
  exports;
- `docs`: optional module docs;
- `fingerprint_inputs`: deterministic semantic inputs for compatibility checks.

Function bodies must never enter a `ModuleInterface`.

Protocol facts are public contract data. Dependents need those facts to check
`Protocol.t(...)` domain constraints without loading provider bodies, just as
they use export facts to resolve imported calls.

Module-scoped `extern "C"` declarations are implementation contracts. They are
not exported from module interfaces. A wrapper function such as
`Utf8.valid?/1` is the public export; `fz_bitstring_valid_utf8/1` is not.

## Import Resolution

`resolve::flatten_modules_with_interface_table` accepts an external
`InterfaceTable` and also injects built-in runtime-library interfaces. Source
modules from the current program are collected and inserted into that table.

The resolver uses interfaces to answer:

```text
does module M exist?
does module M export f/N?
which module owns imported bare call f(args...)?
```

Important behavior:

- `alias Missing` and `import Missing` are `RESOLVE_UNKNOWN_MODULE`.
- `import M, only: [f: N]` checks `M`'s interface exports.
- conflicting imports of the same `name/arity` from different modules are
  `RESOLVE_CONFLICTING_IMPORT`.
- local sibling functions shadow imports.
- bare imported calls rewrite to the qualified current flattened spelling,
  e.g. `add(x, y)` becomes `Math.add(x, y)`.

This is still compatible with the current flattened IR, but new boundary code
should pass typed `ModuleName` / `ExportKey` values wherever possible.

## Strict Interfaces

`modules::interface::validate_public_export_specs` enforces the library-boundary
policy: every module export needs an explicit `@spec`.

Use this for public library boundaries and LTO validation:

```sh
fz dump --emit interfaces --strict-interfaces file.fz
```

Top-level non-module helpers are not interface exports and remain inferable.

## Vocabulary

Use these terms precisely:

- Interface: the public module contract represented by `ModuleInterface`.
  Interfaces contain module identity, imports, exported functions, public
  specs, public type aliases, docs, ABI version, and fingerprint inputs. They
  never contain function bodies.
- Spec: an internal planner/type fact unless it is attached to a public module
  export. `fz dump --emit specs` renders `ModulePlan`; it is not a module ABI.
- `.fzi`: the serialized interface artifact. Dependents use it to resolve and
  check imports without loading provider implementation bodies.
- `.fzo`: the serialized implementation-unit envelope. Normal
  `fz build --emit-fzo` output is deliberately pre-link: it stores the checked
  source text as a materializable source-unit payload
  (`fz-source-unit-v1`) plus the `CompiledUnit` identity/import/export facts
  needed by graph loading. Graph loading can recover the provider
  implementation input from the artifact without reading the original provider
  source path. Runtime-library modules use their own `fz-runtime-module-v1`
  payload, and internal inspection artifacts may still use `fz-ir-text-v1`
  until the linker consumes final object bytes or a richer relocatable unit
  format.
- `CompiledUnit`: one module before image link. It owns module-local IR plus
  the interface/import/export facts needed to prove link compatibility.
- `CompiledImage`: one linked runnable image. It owns runtime-global executable
  state and optional linked runtime metadata.
- LTO: validated boundary erasure. LTO may load compatible implementations and
  rewrite cross-module calls only after public interfaces have been validated.

Dump commands follow the same split:

- `fz dump --emit interfaces` renders public module contracts.
- `fz dump --emit specs` renders internal inferred planner specializations.

Do not treat either dump as a replacement for the other. Interface dumps answer
"what may other modules depend on?" Spec dumps answer "what did this compiler
run infer and plan internally?" Interface dumps include a stable
fingerprint digest for compatibility checks and the human-readable
fingerprint inputs for debugging.

Telemetry keeps process facts out of product dumps:

- `fz.module.interfaces_collected`
- `fz.module.fzi_written`
- `fz.module.fzi_loaded`
- `fz.module.fzo_written`
- `fz.module.fzo_loaded`
- `fz.module.graph_loaded`
- `fz.link.succeeded`
- `fz.link.failed`
- `fz.lto.interfaces_validated`
- `fz.lto.boundaries_erased`

Use `fz dump --emit stats` to inspect these event counts. Keep
`dump --emit interfaces` and `dump --emit specs` as product views: interfaces
render public contracts, specs render planner state.

## Package Boundary

The module subsystem lives behind `src/modules/mod.rs`. Keep new module-boundary
work inside this package unless it is a frontend, IR, or runtime concern.

- `modules::identity`: typed module/export names.
- `modules::interface`: public contracts, strict validation, and interface
  rendering.
- `modules::artifact`: `.fzi` / `.fzo` serde envelopes and ABI/fingerprint
  validation.
- `modules::artifact_store`: artifact path policy and filesystem IO.
- `modules::graph`: reachable `.fzi` / `.fzo` graph loading.
- `modules::pipeline`: provider-aware frontend checking, graph materialization,
  LTO validation/erasure, and pipeline error ownership.
- `modules::runtime_library`: built-in runtime-library source, interfaces, and
  artifacts.

## Artifact Store Paths

`modules::artifact_store::ArtifactStore` owns the filesystem path policy for
module artifacts. It maps typed `ModuleName` values to deterministic locations
and provides `.fzi` / `.fzo` read/write helpers used by build and
runtime-library tooling.

The default build root is:

```text
build/fz
```

Artifact paths are:

```text
build/fz/interfaces/<module segments>/<last segment>.fzi
build/fz/objects/<module segments>/<last segment>.fzo
```

Examples:

```text
Utf8        -> build/fz/interfaces/Utf8.fzi
Utf8        -> build/fz/objects/Utf8.fzo
Outer.Inner -> build/fz/interfaces/Outer/Inner.fzi
Outer.Inner -> build/fz/objects/Outer/Inner.fzo
```

Path construction consumes `ModuleName::segments()`. It must not recover
module identity by splitting dotted display text. Segments must be
filesystem-safe ASCII identifier fragments: letters, digits, or `_`. The path
policy rejects `.`, `..`, separators, spaces, punctuation, and other hostile
segments before artifact IO can touch the filesystem.

Build emission:

```sh
fz build --emit-fzi --emit-fzo --artifact-root build/fz path/to/input.fz -o path/to/app
```

`--emit-fzi` writes one `.fzi` per module through `ArtifactStore` and applies
strict public export-spec validation before writing. Loading uses
`ArtifactStore::load_fzi_artifact` / `load_interface_table`, which deserialize
`FziArtifact` without reading the provider source body. Telemetry-producing
variants (`write_fzi_artifacts_with_telemetry`,
`load_interface_table_with_telemetry`) emit process facts for stats dumps.
`--emit-fzo` writes the checked module product as a pre-link source-unit
envelope: it stores the checked source text as `fz-source-unit-v1`, records the
root `CompiledUnit` identity/import/export facts, derives IR-level link
metadata without machine-code compiling unresolved imports, and writes the
result through `ArtifactStore::write_fzo_artifacts`. The object path comes from
the same typed `ModuleName` policy. The `.fzo` telemetry variants emit `.fzo`
write/load process facts.

Reachable graph loading:

- `modules::graph::ModuleGraphLoader` owns import traversal over artifact stores.
- Inputs are the root checked `InterfaceTable` plus explicit provider-root
  module names.
- The loader queues imports from the roots, loads provider `.fzi` contracts,
  recursively queues their imports, and only then loads `.fzo` objects for
  reachable modules. Protocol implementation callback paths are export
  namespaces inside the defining module's object, not separate artifact roots.
- Runtime-library modules are checked through `modules::runtime_library::interface`
  before the filesystem artifact store. If a runtime module is reachable, the
  loader adds its built-in `.fzo` through `modules::runtime_library::artifact`.
  Runtime modules do not require user `.fzi`/`.fzo` files and do not mask
  missing user artifacts with unrelated names.
- Loaded `.fzo` objects are validated against the `.fzi` fingerprint inputs
  that made the module reachable. Unused artifacts under the artifact root are
  never read.

Run, build, and frontend-only dump commands can load provider artifacts from
the same store:

```sh
fz dump --emit interfaces --interface Math --artifact-root build/fz consumer.fz
fz run --interface Math --artifact-root build/fz consumer.fz
fz build --interface Math --artifact-root build/fz consumer.fz -o consumer
```

`--interface` takes a module name and loads its `.fzi` into the resolver's
external `InterfaceTable`. The current source file's own module interfaces are
still collected locally and override external entries for the same module.
This proves provider-source-free import validation. Calling an imported
provider body in a runnable image is the graph/linker stage's job: `fz run` and
`fz build` load reachable `.fzo` source-unit payloads through
`ModuleGraphLoader`, materialize provider `CompiledUnit` inputs, link IR units,
and reject missing or duplicate providers before execution/codegen.

REPL policy:

- Interactive `fz repl` is session-eager. It compiles against source already
  entered into the REPL world plus built-in runtime-library interfaces.
- `fz repl --script` has one whole-file root source, so script execution uses
  the provider-free execution graph path and can materialize reachable built-in
  runtime modules.
- REPL commands do not accept `--interface`, `--provider`, or
  `--artifact-root`, and they do not load user provider artifacts.
- Artifact-backed imports belong to whole-file `fz run` / `fz build` commands,
  where the root source and provider roots are explicit.

Testing policy:

- Use `.fzi` artifacts or `fz dump --emit interfaces` for public contract
  assertions: imports, exports, specs, ABI versions, and fingerprint inputs.
- Use `.fzo` round-trips and provider-source-free `run`/`build` fixtures for
  implementation-unit and graph-loading behavior.
- Keep raw IR dumps (`clif`, `bodies`, `outcomes`, and `specs`) for
  compiler-internal debugging and planner assertions. They are not the module
  ABI and should not be the oracle for separate-compilation compatibility.

## `.fzi`: Interface Artifact

`FziArtifact` is the public contract artifact. It contains only interface data
and version/fingerprint metadata.

Struct fields:

```text
compiler_abi_version:   FZ_ARTIFACT_ABI_VERSION
runtime_abi_version:    FZ_RUNTIME_ARTIFACT_ABI_VERSION
interface_fingerprint_digest: stable hex digest of fingerprint inputs
interface_fingerprint:  Vec<String>
interface:              ModuleInterface
```

Serialized shape:

```text
fzi
{
  "compiler_abi_version": 1,
  "runtime_abi_version": 1,
  "interface_fingerprint_digest": "<hex>",
  "interface_fingerprint": ["..."],
  "interface": {
    "name": {"segments": ["Module"]},
    "abi_version": 1,
    "imports": [],
    "exports": [],
    "types": [],
    "docs": null,
    "fingerprint_inputs": ["..."]
  }
}
```

The first line is the artifact magic. The body is pretty JSON serialized from
`FziArtifact` through serde. Strict-interface validation is separate from
deserialization: an export can deserialize without a spec, but
`--emit-fzi`/`--strict-interfaces` reject unspecified public exports before
writing or dumping strict contracts.

Load-time rejection:

- missing or wrong `fzi` header;
- unsupported compiler/runtime/interface ABI;
- malformed JSON or typed fields;
- interface fingerprint digest mismatch;
- interface fingerprint inputs mismatch;
- expected fingerprint mismatch.

All artifact load errors are `artifact/invalid` diagnostics.

## `.fzo`: Implementation Unit Artifact

`FzoArtifact` is the implementation-unit envelope. It is intentionally not a
public contract. The graph loader consumes it after interface compatibility is
established. Today normal user `.fzo` files are source-unit envelopes: they
record the compiled unit's identity, required imports, fingerprints, and a
typed payload whose body is checked source text.

Struct fields:

```text
compiler_abi_version:       FZ_ARTIFACT_ABI_VERSION
runtime_abi_version:        FZ_RUNTIME_ARTIFACT_ABI_VERSION
module:                     Option<ModuleName>
unit_payload:               FzoUnitPayload
required_imports:           Vec<ExportKey>
implementation_fingerprint: Vec<String>
interface_fingerprint_digest: stable hex digest of interface_fingerprint
interface_fingerprint:      Vec<String>
```

Payload fields:

```text
format: fz-source-unit-v1 | fz-ir-text-v1 | fz-runtime-module-v1 | another versioned payload format
body:   payload bytes represented as a JSON string
```

Serialized shape:

```text
fzo
{
  "compiler_abi_version": 1,
  "runtime_abi_version": 1,
  "module": {"segments": ["Module"]},
  "unit_payload": {
    "format": "fz-source-unit-v1",
    "body": "defmodule Module ..."
  },
  "required_imports": [],
  "implementation_fingerprint": ["..."],
  "interface_fingerprint_digest": "<hex>",
  "interface_fingerprint": ["..."]
}
```

The first line is the artifact magic. The body is pretty JSON serialized from
`FzoArtifact` through serde. Artifact compatibility remains enforced by the
typed deserializer and explicit ABI/fingerprint checks, not by ad hoc
line-count parsing.

Current `.fzo` deliberately stores a typed implementation payload instead of
final object bytes. `fz build --emit-fzo` stores the checked source text as
`fz-source-unit-v1` and derives required imports from the pre-link
`CompiledUnit` external-call edges; that lets imported modules emit their own
`.fzo` without compiling unresolved external calls through machine codegen.
`FzoArtifact::source_unit_text` is the materialization gate: it accepts
`fz-source-unit-v1` user artifacts and `fz-runtime-module-v1` built-in runtime
module artifacts. It rejects inspection-only payloads before graph loading can
treat them as source units. `FzoArtifact::from_unit` still derives an internal
`fz-ir-text-v1` payload from `CompiledUnit::code.to_string()` for
tests and inspection paths that need a deterministic unit dump, not a
reloadable implementation source.
Deserialization rejects empty payload format/body so a loaded `.fzo` cannot
silently degrade back into a metadata-only artifact.

Load-time rejection:

- missing or wrong `fzo` header;
- compiler/runtime ABI mismatch;
- missing or empty unit payload format/body;
- implemented-interface fingerprint digest mismatch;
- implemented-interface fingerprint mismatch;
- malformed JSON or typed fields.

All errors are `artifact/invalid` diagnostics.

## Compiled Unit vs Linked Image

Use the right term:

- `CompiledUnit`: one pre-link module. Owns module-local IR, interface facts,
  import/export facts, diagnostics, and interface fingerprint.
- `CompiledProgram`: one single-unit codegen result before image wrap. Owns the executable
  `CompiledModule`, the `CompiledUnit`, and the matching `RuntimeUnitMetadata`.
- `RuntimeUnitMetadata`: one unit's runtime-global contributions: atoms,
  schemas, frame sizes, exported runtime symbols, imported refs, static
  closure facts, halt kinds, and entrypoint requirements.
- `CompiledImage`: linked runnable image. Owns runtime-global JIT state and
  optional `RuntimeImageMetadata`.
- `CompiledModule`: machine-code module produced by codegen; `CompiledImage`
  wraps it after module graph correctness has already been proven by
  `link_ir_units`.

`link_ir_units` is the boundary-resolution step for module graphs. It copies all
reachable `CompiledUnit` IR bodies into one dense linked `Module`, remaps
`FnId`, `ExternId`, atom ids, and planner facts, builds provider keys from
implemented interfaces, and rewrites `ExternalCallEdge` placeholders to direct
local calls before JIT codegen sees the module.

Linking must also preserve planner facts that codegen consumes. A provider graph
must not depend on a normal post-link `plan_module` pass to recover dispatch,
return-demand, return-context, extern-marshal, or protocol call-edge facts that
were known upstream. Link/load may validate, remap, resolve, and strengthen
facts; ordinary provider linking is a fact-preserving transformation.
Provider-backed codegen uses `link_ir_units_with_plan`; missing planner facts
are a link error.

`CompiledProgram::link_image_with_telemetry` is the single-unit JIT run path. It
validates the unit through `link_ir_units`, links that unit's runtime metadata,
and wraps the compiled machine-code module. Provider-backed run/build paths
first call `modules::pipeline::prepare_execution_graph`, which materializes
provider units and calls `link_ir_units_with_plan`; codegen then sees one
linked IR module and one remapped `ModulePlan` with no unresolved external
edges. `CompiledImage::from_linked_with_telemetry` only wraps that
already-linked machine-code module and emits link telemetry.
`CompiledModule` remains the executable payload inside the image, not the
driver-facing product.

## IR Link Checks

`link_ir_units` is the only module graph correctness gate.

Checks:

1. Each `CompiledUnit` with an interface still matches its recorded
   `interface_fingerprint`.
2. Every exported interface function contributes one provider key:

```text
ExportKey(module, export.name, export.arity)
```

3. Duplicate providers are rejected.
4. Every copied `ExternalCallEdge` resolves to exactly one provider.
5. All resolved external calls are rewritten to direct local `FnId`s before
   codegen.

Errors include:

- `InterfaceFingerprintMismatch`
- `UnresolvedExternalCalls`
- `MissingImport`
- `DuplicateProvider`

## Runtime Metadata Linking

`RuntimeImageMetadata::link_units` deterministically merges runtime-global
tables for runtime/debug metadata. It is not the module import correctness
gate.

Rules:

- duplicate `module` identities are rejected;
- atoms are de-duplicated by string and sorted by `BTreeSet`;
- schemas are de-duplicated by `schema_key`;
- units are processed in stable module/input order;
- frame ids are relocated by per-unit frame bases;
- exported runtime symbols must be unique;
- imported refs are de-duplicated and sorted;
- static closures are tagged with input index and sorted;
- entrypoint requirements are OR'd together;
- per-input relocations are recorded in `RuntimeUnitRelocations`.

`RuntimeImageMetadata::render_stable` is for deterministic tests/debugging.

## External Calls and LTO

Imported module calls are represented by `ExternalCallEdge` in `fz_ir::Module`.
The terminator still carries a placeholder `FnId` until link/LTO resolves the
edge.

Normal module-graph linking resolves those edges through `link_ir_units` before
codegen. LTO may then consume the same validated graph facts to erase optimizer
boundaries, but LTO is not the correctness path.

Normal codegen rejects unresolved external calls:

```text
unresolved external module call `Dep.run/0`
```

CLI LTO path:

1. `modules::pipeline::checked_module_for_mode` runs the normal frontend
   result through module interface collection;
2. `modules::pipeline::LtoLinkedProgram::validate` validates public module
   interfaces and emits
   the `fz.lto.interfaces_validated` telemetry event;
3. `modules::pipeline::LtoLinkedProgram::erase_boundaries` builds
   `Module::interface_export_map` from interface exports to loaded
   implementation `FnId`s;
4. `erase_boundaries` calls `Module::rewrite_external_calls_for_lto`;
5. `erase_boundaries` clears spec-boundary firewalls for loaded
   implementations and emits `fz.lto.boundaries_erased`;
6. the caller re-plans/reduces/codegens with direct calls.

`LtoLinkedProgram` is intentionally private to `modules::pipeline` and is the
only input to boundary erasure there. That keeps boundary erasure behind
interface validation in the type shape instead of relying on each caller to
remember the order.

Mechanically, the pass:

1. builds `Module::interface_export_map` from interface exports to loaded
   implementation `FnId`s;
2. calls `Module::rewrite_external_calls_for_lto`;
3. clears spec-boundary firewalls for loaded implementations.

This makes whole-program optimization explicit while keeping normal-mode
correctness interface-based.

## Runtime Library Modules

`runtime_library` owns the built-in runtime source set and exposes built-in
library module interfaces/artifacts.

Rules:

- `src/modules/runtime_library/runtime.fz` is the always-loaded prelude root:
  root imports from core prelude modules plus ordinary global type aliases such
  as `keyword/0` and `keyword/1`. Runtime primitive types such as `pid`, `ref`,
  and `utf8` are compiler-known built-ins, not source aliases in this file;
- core prelude modules such as `Kernel` live in separate source files but are
  flattened into the built-in prelude, keeping raw extern declarations
  module-scoped while exposing imported names like `print/1`;
- ordinary module bodies live in individual files such as
  `src/modules/runtime_library/utf8.fz` and
  `src/modules/runtime_library/process.fz`;
- every runtime-library module should carry a crisp `@moduledoc`, and every
  public export should have the narrowest accurate `@spec`;
- module-scoped externs are implementation details, not interface exports;
- import and alias declarations request runtime interfaces on demand through
  `modules::runtime_library::interface`;
- `modules::runtime_library::artifacts` creates deterministic `.fzi`/`.fzo` envelopes
  for built-in runtime-library modules;
- reachable non-core runtime modules contribute `fz-runtime-module-v1` `.fzo`
  objects to `ModuleGraphLoader`, while the core prelude is prepended during
  lowering.

To add a runtime-library module:

1. add `src/modules/runtime_library/<name>.fz`;
2. put exactly one ordinary `defmodule Name do ... end` in that file;
3. add that file to `RUNTIME_MODULE_SOURCES` in
   `src/modules/runtime_library.rs`;
4. add a module `@moduledoc` plus public `@spec` declarations for exported
   functions;
5. keep primitive `extern "C"` declarations module-scoped. If the module is a
   core prelude module, expose selected functions through `runtime.fz` imports.

Generated artifacts still use the same module-name store as user artifacts:
`.fzi` under `build/fz/interfaces/...` and `.fzo` under
`build/fz/objects/...`. For example, `Utf8` maps to
`build/fz/interfaces/Utf8.fzi` and `build/fz/objects/Utf8.fzo` regardless of
the source file being `src/modules/runtime_library/utf8.fz`.

Built-in runtime-library interfaces are requested defaults. A source module
with the same name as a built-in module is collected from the current program
and wins for that compile; artifact paths stay module-name based, so
distributors should avoid shipping user and built-in artifacts with the same
module identity in one root.

Use this split when adding standard-library code: prefer ordinary FZ modules
over growing the primitive runtime surface.

## Before Changing This Area

Check at least these facts:

- interface dumps do not include function bodies;
- strict interface validation still rejects missing public specs;
- import resolution can use external interface tables;
- codegen still rejects unresolved external module calls;
- linked image metadata rejects missing/duplicate providers;
- artifact round trips are deterministic and reject fingerprint mismatches;
- runtime-library interfaces do not export primitive extern helpers;
- LTO validates interfaces before boundary erasure.
