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

## `.fzi`: Interface Artifact

`FziArtifact` is the public contract artifact. It contains only interface data
and version/fingerprint metadata.

Struct fields:

```text
compiler_abi_version:   FZ_ARTIFACT_ABI_VERSION
runtime_abi_version:    FZ_RUNTIME_ARTIFACT_ABI_VERSION
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

Struct fields:

```text
compiler_abi_version:       FZ_ARTIFACT_ABI_VERSION
runtime_abi_version:        FZ_RUNTIME_ARTIFACT_ABI_VERSION
module:                     Option<ModuleName>
code_fn_count:              usize
required_imports:           Vec<ExportKey>
exported_symbols:           Vec<(String, u32)>
atom_count:                 usize
schema_count:               usize
frame_sizes:                Vec<u32>
implementation_fingerprint: Vec<String>
interface_fingerprint:      Vec<String>
```

Serialized shape:

```text
fzo
compiler_abi=<u32>
runtime_abi=<u32>
module=<ModuleName or empty>
code_fn_count=<usize>
implementation_fingerprint=<count>
implementation_fingerprint\t<escaped input>
...
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

Current `.fzo` deliberately stores metadata counts/tables needed by image
linking work, not final object bytes. `FzoArtifact::from_unit` derives the
envelope from a `CompiledUnit` plus `RuntimeUnitMetadata`.

Load-time rejection:

- missing or wrong `fzo` header;
- compiler/runtime ABI mismatch;
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

`CompiledImage::link_prelinked(units, runtime_units, prelinked)` is the current
bridge. It validates metadata and wraps an already-linked `CompiledModule`.
Later work can replace the `prelinked` argument with real per-unit codegen and
relocation.

## Image Link Checks

`CompiledImage::link_prelinked` calls `link_image_metadata`.

Checks:

1. `units.len() == runtime_units.len()`.
2. Each `CompiledUnit` with an interface still matches its recorded
   `interface_fingerprint`.
3. Every exported interface function contributes one provider key:

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

`runtime_library` parses `src/runtime.fz` and exposes built-in library module
interfaces/artifacts.

Rules:

- top-level primitive externs remain runtime primitive contracts;
- module bodies such as `Utf8` and `Process` are ordinary library modules;
- module-scoped externs are implementation details, not interface exports;
- `runtime_library::interface_table` is injected into resolver interface
  lookup by default;
- `runtime_library::artifacts` creates deterministic `.fzi`/`.fzo` envelopes
  for built-in runtime-library modules.

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
