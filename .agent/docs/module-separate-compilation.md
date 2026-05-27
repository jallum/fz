# Module identity and separate compilation

Use this when changing module resolution, interfaces, compiled units, or runtime
library import behavior.

`ModuleName`, `QualifiedName`, and `ExportKey` are the semantic identity types.
Dotted strings remain compatibility/display spellings for current flattened IR,
dumps, and diagnostics. New module-boundary code should assemble typed names
from parsed segments or interface data and render dotted text only at the edge.

`ModuleInterface` is emitted by `resolve::flatten_modules` while source-level
`ModuleDef` nodes still exist, then carried on the flattened `Program`.
Resolvers, artifact writers, and LTO validation consume it as the public
contract; downstream execution must not inspect dependency implementation
bodies through it.

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
  module's IR code, planner facts, imports, exports, diagnostics, and visible
  interface fingerprint inputs.
- `CompiledProgram` is the immediate codegen product for the JIT path. It owns
  the executable `CompiledModule`, the `CompiledUnit`, and the matching
  `RuntimeUnitMetadata` derived from codegen/runtime facts.
- `CompiledImage` is the linked runnable artifact. It owns runtime-global JIT
  state, schema/atom tables, function pointers, and execution entrypoints.
- `CompiledModule` is the machine-code module produced by codegen.
  Driver code should treat it as the executable payload inside
  `CompiledProgram`/`CompiledImage`, not as the final product.
- Runtime metadata is split the same way: `RuntimeUnitMetadata` carries
  unit-local atoms, schemas, frame sizes, exported symbols, imported refs,
  static closure facts, halt kinds, and entrypoint requirements.
  `RuntimeImageMetadata::link_units` deterministically merges those tables and
  records per-unit relocation maps. Duplicate module identities or duplicate
  exported runtime symbols are controlled compiler errors, not warnings.
- Imported module calls are represented in IR as `ExternalCallEdge` metadata.
  The terminator keeps a temporary `FnId` placeholder until
  the image linker gives `Module::rewrite_external_calls_for_lto` an export map
  and rewrites the callsite to a direct local `FnId`. Codegen rejects any
  unresolved external edge; linked images must resolve or report the missing
  target first. `SpecPlan.call_edges` carries the matching provider-boundary
  target before link; `link_ir_units_with_plan` resolves it to the linked local
  `SpecKey` while rewriting the IR edge. A rewrite candidate must match the
  callsite identity and the target entry arity; matching only a source identity
  is insufficient because matcher-generated branches can share source spans.
- Artifact ownership is explicit. `.fzi` stores only the versioned
  `ModuleInterface` contract plus compiler/runtime ABI versions and the
  interface fingerprint. `.fzo` stores the implementation-unit envelope:
  module identity, a typed implementation payload, implementation fingerprint,
  implemented-interface fingerprint plus digest, and required imports. Normal
  `fz build --emit-fzo` artifacts use a materializable source payload
  (`fz-source-unit-v1`), not final object bytes; graph loading can recover the
  provider implementation input from the artifact without reading the original
  provider source path. Loading rejects unsupported ABI versions, empty
  payloads, unsupported materialization formats, digest mismatches, and
  fingerprint mismatches as `artifact/invalid` diagnostics.
- `link_ir_units` is the normal boundary-resolution step for executable module
  graphs. It copies all reachable `CompiledUnit` IR bodies into one dense linked
  `Module`, remaps `FnId`, `ExternId`, atom ids, and planner facts, builds the
  provider export map from implemented interfaces, and rewrites
  `ExternalCallEdge` placeholders to direct local calls before JIT codegen sees
  the module. Provider-backed codegen uses `link_ir_units_with_plan`; missing
  planner facts are a link error, not an invitation to replan the linked graph.
- `modules::pipeline::prepare_execution_graph` is the module graph correctness
  path for provider-backed run/build. It materializes provider units, calls
  `link_ir_units_with_plan`, and hands codegen one linked IR module and one
  remapped `ModulePlan` with no unresolved external edges. It does not run a
  normal post-link `plan_module` cleanup pass. `CompiledImage::from_linked_with_telemetry`
  then only wraps that already-linked machine-code module and emits link telemetry.
- `CompiledProgram::link_image_with_telemetry` remains the single-unit JIT run
  path. It validates that one unit through `link_ir_units`, links that unit's
  runtime metadata for runtime/debug facts, and wraps the compiled module.

Runtime library boundary:

- `src/modules/runtime_library/runtime.fz` is the tiny always-loaded prelude.
  It contains root imports from core prelude modules plus ordinary global type
  aliases such as `keyword/0` and `keyword/1`. Runtime primitive types such as
  `pid`, `ref`, and `utf8` are compiler-known built-ins, not source aliases in
  this file. It must not grow primitive extern declarations or ordinary
  `defmodule` bodies.
- Core prelude modules, currently `Kernel`, live in their own source files but
  are flattened into the built-in prelude during lowering. `runtime.fz` imports
  the selected public functions from those modules, so source can call
  `print/1` while raw extern contracts remain inside `Kernel`.
- Runtime-library modules live in individual files under
  `src/modules/runtime_library/`, such as `utf8.fz` and `process.fz`. Each file
  contains the ordinary `defmodule` for that module. Runtime modules should
  publish a crisp `@moduledoc` and narrow public specs; broad `any` is for
  genuinely shape-polymorphic values or areas without a richer type form.
  Public specs may name compiler-known runtime types such as `utf8`, `pid`,
  and `ref` directly.
- `modules::runtime_library` is the manifest and loader for those built-in
  module files. `interface(&ModuleName)` and `artifact(&ModuleName)` provide
  demand-loaded runtime facts keyed by the same `ModuleName` used for user
  artifacts.
- Import or alias declarations are the source-level request for a runtime
  module. `resolve::flatten_modules_with_interface_table` adds a built-in
  runtime interface only for requested runtime modules that are not defined
  locally and were not already provided by an external `.fzi`.
- Interface emission does not export `extern "C"` declarations from modules.
  Those names are implementation contracts used by the module body, not
  public library functions.
- `modules::runtime_library::artifacts` produces deterministic `.fzi` and `.fzo`
  envelopes for each built-in library module. The `.fzi` is the public
  contract; the `.fzo` uses the `fz-runtime-module-v1` payload and stores the
  module source text so graph loading can materialize the runtime module just
  like a user source-unit object.
- `ArtifactStore::write_fzo_artifacts` and `load_fzo_artifact` persist and
  reload those object envelopes under the same `build/fz/objects/...` path
  policy used for user modules.
- `modules::graph::ModuleGraphLoader` traverses reachable imports from root
  checked interfaces and explicit provider-root modules. It loads provider
  `.fzi` contracts first, queues their imports recursively, and loads `.fzo`
  objects only for reachable modules. Protocol implementation callback names do
  not add graph roots; they are functions packaged in the defining module's
  object. Runtime-library modules are checked first through
  `modules::runtime_library::interface`; reachable runtime modules contribute
  built-in `.fzo` objects through `modules::runtime_library::artifact` and do
  not require user `.fzi`/`.fzo` files.
- User builds can write object envelopes with
  `fz build --emit-fzo --artifact-root <dir> ...`. The writer consumes the
  checked `CompiledUnit` facts directly, so a module with artifact-backed
  imports can emit its own `.fzo` before those imports are linked into an
  executable image.
- User run/build commands consume provider graphs with
  `fz run --interface <Module> --artifact-root <dir> ...` and
  `fz build --interface <Module> --artifact-root <dir> ...`. `--provider` is
  accepted as an alias for the same provider-root input.
- Execution still prepends the runtime prelude: `runtime.fz` root aliases and
  imports plus core prelude module sources. Ordinary non-core runtime modules
  are graph-loaded when reachable from imports.
- The interactive REPL remains session-eager. `fz repl` compiles against
  definitions already present in the REPL source world plus built-in
  runtime-library interfaces; it does not accept provider roots or load user
  `.fzi`/`.fzo` artifacts through `ModuleGraphLoader`.
- `fz repl --script` has one whole-file root source, so it uses the same
  provider-free execution graph path as `fz run` for built-in runtime modules.
  It still does not accept user provider roots.

LTO / whole-program mode:

- Normal compilation remains the correctness path. Linked images must resolve
  imports through interfaces and must not require whole-program analysis.
- `--lto` (alias `--whole-program`) is an explicit optimized build/dump/run
  mode. It validates public module interfaces first, then treats loaded
  compatible implementations as available for whole-program optimization.
- `modules::pipeline::checked_module_for_mode` is the shared entry for normal
  and LTO run/build/dump paths. LTO mode creates a validated private
  `LtoLinkedProgram`; the boundary-erasure pass consumes that validated value,
  so callers cannot erase module boundaries before interface validation in
  normal control flow.
- Module process facts are telemetry, not dump payloads. Stats should include
  events such as `fz.module.interfaces_collected`, `.fzi`/`.fzo` write/load,
  `fz.module.graph_loaded`, `fz.link.succeeded` / `fz.link.failed`, and the
  LTO validation/erasure events. Product dumps remain separate: interfaces are
  public contracts; specs are planner state.
- `Module::interface_export_map` builds the implementation map from validated
  interface exports to loaded `FnId`s. `Module::rewrite_external_calls_for_lto`
  consumes that map and rewrites `ExternalCallEdge` placeholders to direct
  calls before reducer/planner/codegen work that benefits from boundary
  erasure.
- After validation, LTO clears spec-boundary firewalls for loaded
  implementations so reducer/inliner passes can cross public module contracts.
  This is deliberately restricted to explicit LTO; normal compilation keeps
  public specs as optimization boundaries.

Testing strategy:

- Assert public module contracts with `.fzi` artifacts and
  `fz dump --emit interfaces`.
- Assert implementation-unit and graph-loader behavior with `.fzo`
  source-unit round-trips and provider-source-free `run`/`build` fixtures.
- Use raw IR and spec dumps for compiler-internal planner behavior. They are
  useful diagnostics, but they are not the separate-compilation contract.
