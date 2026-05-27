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

`module_interface::collect_from_program` runs while source-level `ModuleDef`
nodes still exist. It produces one `ModuleInterface` per module.

`ModuleInterface` contains:

- `name`: the `ModuleName`;
- `abi_version`: currently `FZ_INTERFACE_ABI_VERSION`;
- `imports`: declared module imports and their `only` / `except` filters;
- `exports`: non-macro, non-extern public functions by name and arity;
- `types`: public module type aliases, opaques, and refines;
- `docs`: optional module docs;
- `fingerprint_inputs`: deterministic semantic inputs for compatibility checks.

Function bodies must never enter a `ModuleInterface`.

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

`module_interface::validate_public_export_specs` enforces the library-boundary
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
- `.fzo`: the serialized compiled-unit artifact. It carries a typed
  compiled-unit payload plus the link metadata derived from `CompiledUnit` and
  `RuntimeUnitMetadata`. The current source-compiled payload format is
  deterministic IR text (`fz-ir-text-v1`); runtime-library modules use their
  own `fz-runtime-module-v1` payload until the linker consumes final object
  bytes or a richer relocatable unit format.
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

## Artifact Store Paths

`module_artifact_store::ArtifactStore` owns the filesystem path policy for
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
fz build --emit-fzi --artifact-root build/fz path/to/input.fz -o path/to/app
```

`--emit-fzi` writes one `.fzi` per module through `ArtifactStore` and applies
strict public export-spec validation before writing. Loading uses
`ArtifactStore::load_fzi_artifact` / `load_interface_table`, which deserialize
`FziArtifact` without reading the provider source body. Object artifacts use
`ArtifactStore::write_fzo_artifacts` and `load_fzo_artifact`; the object path
comes from the same typed `ModuleName` policy.

Frontend-only dump commands can load provider interfaces from the same store:

```sh
fz dump --emit interfaces --interface Math --artifact-root build/fz consumer.fz
```

`--interface` takes a module name and loads its `.fzi` into the resolver's
external `InterfaceTable`. The current source file's own module interfaces are
still collected locally and override external entries for the same module.
This proves provider-source-free import validation. Calling an imported
provider body from normal code still requires the later `.fzo` payload/linker
tickets so codegen has an implementation target.

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
compiler_abi=<u32>
runtime_abi=<u32>
module=<ModuleName>
interface_abi=<u32>
fingerprint_digest=<hex>
docs=<escaped docs or empty>
fingerprint=<count>
fingerprint\t<escaped input>
...
imports=<count>
import\t<ModuleName>\t<only list>\t<except list>
...
types=<count>
type\t<name>\t<alias|opaque|refines>\t<body>
...
exports=<count>
export\t<name>\t<arity>\t<spec>
...
```

List encoding:

- A counted list starts with `name=<count>`.
- Each value line is `name\t<escaped value>`.
- Counts are checked on load.

Import filter encoding:

```text
name/arity,name/arity
```

Spec encoding:

```text
param,param=>result
```

An empty spec field means the export is unspecified. Strict-interface
validation is separate from deserialization.

Escaping:

- `\` becomes `\\`
- tab becomes `\t`
- newline becomes `\n`

Load-time rejection:

- missing or wrong `fzi` header;
- unsupported compiler/runtime/interface ABI;
- count mismatches;
- malformed imports/types/exports/specs;
- expected fingerprint mismatch.

All artifact load errors are `artifact/invalid` diagnostics.

## `.fzo`: Compiled Unit Artifact

`FzoArtifact` is the compiled-unit envelope. It is intentionally not a public
contract. The linker consumes it after interface compatibility is established.
Today it records the compiled unit's identity, dependency, export, fingerprint,
runtime metadata facts, and payload. The payload is the implementation body;
the counts are metadata that must agree with the payload producer, not the
source of truth.

Struct fields:

```text
compiler_abi_version:       FZ_ARTIFACT_ABI_VERSION
runtime_abi_version:        FZ_RUNTIME_ARTIFACT_ABI_VERSION
module:                     Option<ModuleName>
unit_payload:               FzoUnitPayload
code_fn_count:              usize
required_imports:           Vec<ExportKey>
exported_symbols:           Vec<(String, u32)>
atom_count:                 usize
schema_count:               usize
frame_sizes:                Vec<u32>
implementation_fingerprint: Vec<String>
interface_fingerprint_digest: stable hex digest of interface_fingerprint
interface_fingerprint:      Vec<String>
```

Payload fields:

```text
format: fz-ir-text-v1 | fz-runtime-module-v1 | future payload format
body:   escaped payload bytes represented as UTF-8 text
```

Serialized shape:

```text
fzo
compiler_abi=<u32>
runtime_abi=<u32>
module=<ModuleName or empty>
unit_payload_format=<escaped payload format>
unit_payload=<escaped payload body>
code_fn_count=<usize>
implementation_fingerprint=<count>
implementation_fingerprint\t<escaped input>
...
interface_fingerprint_digest=<hex>
interface_fingerprint=<count>
interface_fingerprint\t<escaped input>
...
imports=<count>
import\t<ExportKey>
...
exports=<count>
export\t<escaped symbol>\t<local fn id>
...
atom_count=<usize>
schema_count=<usize>
frame_sizes=<comma-separated u32 list>
```

Current `.fzo` deliberately stores the unit payload as deterministic internal
IR text instead of final object bytes. `FzoArtifact::from_unit` derives the
payload from `CompiledUnit::code.to_string()` and derives link metadata from
`RuntimeUnitMetadata`. Deserialization rejects empty payload format/body so a
loaded `.fzo` cannot silently degrade back into a metadata-only artifact.

Load-time rejection:

- missing or wrong `fzo` header;
- compiler/runtime ABI mismatch;
- missing or empty unit payload format/body;
- implemented-interface fingerprint digest mismatch;
- implemented-interface fingerprint mismatch;
- malformed `ExportKey` (`Module.name/arity`);
- imports/exports count mismatches;
- malformed frame-size CSV.

All errors are `artifact/invalid` diagnostics.

## Compiled Unit vs Linked Image

Use the right term:

- `CompiledUnit`: one pre-link module. Owns module-local IR, interface facts,
  import/export facts, diagnostics, and interface fingerprint.
- `RuntimeUnitMetadata`: one unit's runtime-global contributions: atoms,
  schemas, frame sizes, exported runtime symbols, imported refs, static
  closure facts, halt kinds, and entrypoint requirements.
- `CompiledImage`: linked runnable image. Owns runtime-global JIT state and
  optional `RuntimeImageMetadata`.
- `CompiledModule`: compatibility name for the current runnable image surface.

`CompiledImage::link_compiled(units, runtime_units, linked)` constructs the
runnable image. It validates unit/interface compatibility, rejects unresolved
external module calls, links runtime metadata, and only then wraps the compiled
machine-code module.

## Image Link Checks

`CompiledImage::link_compiled` calls `link_image_metadata`.

Checks:

1. `units.len() == runtime_units.len()`.
2. Each `CompiledUnit` with an interface still matches its recorded
   `interface_fingerprint`.
3. No `CompiledUnit` still has unresolved `external_call_edges`.
4. Every exported interface function contributes one provider key:

```text
ExportKey(module, export.name, export.arity)
```

4. Duplicate providers are rejected.
5. Every `runtime.imported_refs` entry has a provider.
6. `RuntimeImageMetadata::link_units` succeeds.

Errors include:

- `UnitRuntimeCountMismatch`
- `InterfaceFingerprintMismatch`
- `MissingImport`
- `DuplicateProvider`
- `RuntimeMetadata`

## Runtime Metadata Linking

`RuntimeImageMetadata::link_units` deterministically merges runtime-global
tables.

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

Normal codegen rejects unresolved external calls:

```text
unresolved external module call `Dep.run/0`
```

LTO path:

1. validate public module interfaces;
2. build `Module::interface_export_map` from interface exports to loaded
   implementation `FnId`s;
3. call `Module::rewrite_external_calls_for_lto`;
4. clear spec-boundary firewalls for loaded implementations;
5. re-plan/reduce/codegen with direct calls.

This makes whole-program optimization explicit while keeping normal-mode
correctness interface-based.

## Runtime Library Modules

`runtime_library` parses `src/runtime_library/runtime.fz` and exposes built-in
library module interfaces/artifacts.

Rules:

- top-level primitive externs remain runtime primitive contracts;
- module bodies such as `Utf8` and `Process` are ordinary library modules;
- module-scoped externs are implementation details, not interface exports;
- `runtime_library::interface_table` is injected into resolver interface
  lookup by default;
- `runtime_library::artifacts` creates deterministic `.fzi`/`.fzo` envelopes
  for built-in runtime-library modules.

To add a runtime-library module, edit `src/runtime_library/runtime.fz`, add a
`defmodule` with public `@spec` declarations for exported functions, and keep
primitive `extern "C"` declarations module-scoped unless they are deliberately
part of the primitive prelude. The generated artifacts live in the same store
as user artifacts: `.fzi` under `build/fz/interfaces/...` and `.fzo` under
`build/fz/objects/...`.

Built-in runtime-library interfaces are resolver defaults. A source module with
the same name as a built-in module is collected from the current program and
overrides the injected built-in interface for that compile; artifact paths stay
module-name based, so distributors should avoid shipping user and built-in
artifacts with the same module identity in one root.

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
