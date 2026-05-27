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
  identity, a typed implementation payload, implementation fingerprint,
  implemented-interface fingerprint plus digest, required imports, exported
  runtime symbols, and local runtime metadata facts needed by image-linker
  staging. The current source-compiled payload format is deterministic IR text
  (`fz-ir-text-v1`), not final object bytes. Loading rejects unsupported ABI
  versions, empty payloads, digest mismatches, and fingerprint mismatches as
  `artifact/invalid` diagnostics.
- `CompiledImage::link_compiled` is the image-linker constructor. It validates
  that each unit implements its recorded interface fingerprint, rejects
  unresolved external module calls in runnable units, resolves every required
  `ExportKey` to exactly one provider, merges `RuntimeUnitMetadata` through
  `RuntimeImageMetadata::link_units`, and only then wraps the compiled
  machine-code module.

Runtime library boundary:

- `src/runtime_library/runtime.fz` contains both primitive extern contracts and
  ordinary FZ standard-library modules. Primitive contracts are the top-level
  `extern "C"` declarations implemented by the Rust runtime; they remain
  runtime imports with explicit type contracts.
- Module bodies in `src/runtime_library/runtime.fz` (`Utf8`, `Process`, etc.)
  are treated as ordinary library modules. `runtime_library::interface_table`
  exposes their `ModuleInterface` facts to the resolver by default, so user
  modules can import from runtime-library interfaces without defining or
  source-pasting those modules.
- Interface emission does not export `extern "C"` declarations from modules.
  Those names are implementation contracts used by the module body, not
  public library functions.
- `runtime_library::artifacts` produces deterministic `.fzi` and `.fzo`
  envelopes for each built-in library module. The `.fzi` is the public
  contract; the `.fzo` records the runtime-module payload, implemented
  interface fingerprint, and implementation fingerprint for
  linker/runtime-library staging.
- `ArtifactStore::write_fzo_artifacts` and `load_fzo_artifact` persist and
  reload those object envelopes under the same `build/fz/objects/...` path
  policy used for user modules.

LTO / whole-program mode:

- Normal compilation remains the correctness path. Linked images must resolve
  imports through interfaces and must not require whole-program analysis.
- `--lto` (alias `--whole-program`) is an explicit optimized build/dump/run
  mode. It validates public module interfaces first, then treats loaded
  compatible implementations as available for whole-program optimization.
- `Module::interface_export_map` builds the implementation map from validated
  interface exports to loaded `FnId`s. `Module::rewrite_external_calls_for_lto`
  consumes that map and rewrites `ExternalCallEdge` placeholders to direct
  calls before reducer/planner/codegen work that benefits from boundary
  erasure.
- After validation, LTO clears spec-boundary firewalls for loaded
  implementations so reducer/inliner passes can cross public module contracts.
  This is deliberately restricted to explicit LTO; normal compilation keeps
  public specs as optimization boundaries.
