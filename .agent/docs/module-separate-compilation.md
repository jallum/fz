# Module identity and separate compilation

Use this when changing module resolution, interfaces, compiled units, or runtime
library import behavior.

`ModuleName`, `QualifiedName`, and `ExportKey` are the semantic identity types.
Dotted strings remain compatibility/display spellings for current flattened IR,
dumps, and diagnostics. New module-boundary code should assemble typed names
from parsed segments or interface data and render dotted text only at the edge.

`ModuleInterface` is emitted by `resolve::flatten_modules` while source-level
`ModuleDef` nodes still exist, then carried on the flattened `Program`. Until
the resolver and linker consume interfaces in later tickets, it is an
observational contract artifact: downstream execution must not inspect
dependency implementation bodies through it.

Use `fz dump --emit interfaces <file.fz>` to inspect the current interface
shape. The dump is deterministic and intentionally contains only contract
facts: module docs, imports, public types, exported function names/arities,
specs, ABI version, and fingerprint inputs. Function bodies must not appear.

Use `fz dump --emit interfaces --strict-interfaces <file.fz>` for the current
library-boundary policy check. In compatibility/dev mode (the default),
interfaces may contain unspecified exports while this migration proceeds. In
strict mode, every module export must have an explicit `@spec`; top-level
non-interface helpers remain inferable.

The invariant for the separate-compilation arc is:

- private code is inferred inside a module;
- public boundaries are represented by typed interface/export facts;
- normal import resolution consumes interface facts, not dependency bodies;
- whole-program analysis may erase boundaries in LTO, but correctness cannot
  depend on doing so.

Codegen artifact vocabulary:

- `CompiledUnit` is the pre-link artifact for one source module. It owns that
  module's IR code, imports, exports, diagnostics, and visible interface
  fingerprint inputs.
- `CompiledImage` is the linked runnable artifact. It owns runtime-global JIT
  state, schema/atom tables, function pointers, and execution entrypoints.
- `CompiledModule` is the compatibility name for today's runnable image while
  call sites migrate. New linker/runtime-library code should use
  `CompiledUnit` for module-local work and `CompiledImage` for runnable state.
- Runtime metadata is split the same way: `RuntimeUnitMetadata` carries
  unit-local atoms, schemas, frame sizes, exported symbols, imported refs,
  static closure facts, halt kinds, and entrypoint requirements.
  `RuntimeImageMetadata::link_units` deterministically merges those tables and
  records per-unit relocation maps. Duplicate module identities or duplicate
  exported runtime symbols are controlled compiler errors, not warnings.
- Imported module calls are represented in IR as `ExternalCallEdge` metadata.
  The terminator keeps a temporary `FnId` placeholder until
  `Module::rewrite_external_calls_for_lto` is given an export map and rewrites
  the callsite to a direct local `FnId`. Codegen rejects any unresolved
  external edge; linked images must resolve or report the missing target first.
- Artifact ownership is explicit. `.fzi` stores only the versioned
  `ModuleInterface` contract plus compiler/runtime ABI versions and the
  interface fingerprint. `.fzo` stores the compiled-unit envelope: module
  identity, implementation fingerprint, implemented-interface fingerprint,
  required imports, exported runtime symbols, and local runtime metadata
  counts/tables needed by image linking. Loading rejects unsupported ABI
  versions and fingerprint mismatches as `artifact/invalid` diagnostics.
- `CompiledImage::link_prelinked` is the current image-linker bridge. It
  validates that each unit implements its recorded interface fingerprint,
  resolves every required `ExportKey` to exactly one provider, merges
  `RuntimeUnitMetadata` through `RuntimeImageMetadata::link_units`, and then
  wraps an already-linked runnable module. Later tickets replace that
  prelinked input with real per-unit codegen/link relocation.

Runtime library boundary:

- `src/runtime.fz` contains both primitive extern contracts and ordinary FZ
  standard-library modules. Primitive contracts are the top-level
  `extern "C"` declarations implemented by the Rust runtime; they remain
  runtime imports with explicit type contracts.
- Module bodies in `runtime.fz` (`Utf8`, `Process`, etc.) are treated as
  ordinary library modules. `runtime_library::interface_table` exposes their
  `ModuleInterface` facts to the resolver by default, so user modules can
  import from runtime-library interfaces without defining or source-pasting
  those modules.
- Interface emission does not export `extern "C"` declarations from modules.
  Those names are implementation contracts used by the module body, not
  public library functions.
- `runtime_library::artifacts` produces deterministic `.fzi` and `.fzo`
  envelopes for each built-in library module. The `.fzi` is the public
  contract; the `.fzo` records the implemented interface fingerprint and
  implementation fingerprint for linker/runtime-library staging.
