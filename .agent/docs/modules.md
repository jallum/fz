# Modules and Compiler-Owned Loading

This codebase no longer uses `.fzi` or `.fzo` artifacts for normal
compilation. Source is the only compile-time truth.

The module subsystem behind `src/modules/mod.rs` now answers three questions:

- what module identity means
- what public contract a parsed source module exposes
- how the compiler reaches, lowers, and plans only the runtime modules a build
  actually touches

The pieces that matter:

- `identity`: typed `ModuleName` / `ModuleId` / `Mfa` / `ExportKey`
- `interface`: `ModuleInterface`, interface rendering, and strict public-spec
  validation
- `pipeline`: compiler-owned checked-module and execution-graph preparation
- `runtime_library`: embedded runtime source modules, loaded lazily by name

## Identity

`ModuleName` is the human-facing typed module identity. It owns path segments
and renders to dotted text only for display or IR spellings.

`ModuleId` is the compiler-owned stable module handle. Compiler-internal demand
tracking and cached source function ownership key on it, not on dotted strings.

`Mfa` is the compiler-facing source-function identity:

```text
module_id:     ModuleId
function_name: String
arity:         usize
```

`FnId` is no longer the semantic identity of a source function. It is a lowered
IR handle looked up from `Mfa` inside a materialized module.

`ExportKey` remains the public cross-module function identity:

```text
module: ModuleName
name:   String
arity:  usize
```

Link-time and resolution logic key on these typed values, not on split strings.

## Interfaces

`modules::interface::collect_from_program` walks the parsed source AST before
module structure is flattened away. It emits one `ModuleInterface` per module
and one per root protocol namespace.

`ModuleInterface` carries only contract data:

- module identity
- public imports
- public exported functions and ordered `@spec` overloads
- public type aliases / opaques / refines
- protocol declarations
- protocol impl callback surfaces
- optional docs
- deterministic `fingerprint_inputs`

The interface is an in-memory contract. It is extracted from source each time a
module is parsed and cached by `Compiler`.

`validate_public_export_specs` is still the strict boundary rule: every public
export must have an explicit `@spec`.

## Compiler-Owned Module State

`Compiler` is the single owner of module/file state. It tracks stable module
and file ids plus lazy phase advancement:

```text
discovered
-> source_loaded
-> parsed
-> body_surface_ready
-> interface_ready
-> macro_surface_ready
-> runtime_lowered
-> runtime_planned
```

Not every module reaches every phase. Import resolution only needs
`interface_ready`. Cross-module macro use only needs `macro_surface_ready`.
`body_surface_ready` is the first compiler-owned split between syntax and
executable work: the compiler has stable function-group descriptors keyed by
`Mfa` and root fn/group ownership without having emitted body IR yet. Once a
root program is resolved, lowering starts from entry `fn/arity` roots and
reacts outward from the lowered IR itself: if a live body references an
unloaded local group, the compiler requests that group in the same reactive
lowering loop and continues until the root set closes. The compiler emits only
the reachable function-groups and caches each group's IR in the compiler world.
Protocol declarations, impl facts, and protocol-callback ownership also live in
compiler world: a protocol callback reference is resolved against compiler-owned
facts first, so user-source impl callbacks never get misrouted into runtime
module discovery just because they target a builtin type like `List`.
Runtime codegen only needs the modules that become reachable from the checked
program. Runtime unit discovery now also reacts to already-materialized runtime
units: the checked root unit seeds exact external runtime exports, each
materialized runtime unit can seed more exact runtime exports from its planned
call edges, and only then does the compiler fall back to protocol-provider
discovery when a live protocol module still leaves the provider set dynamic.
Inside each reachable runtime module, the compiler lowers only the live
function-groups. Production entrypoints now hand source roots to compiler-owned
`checked` / `prepared` methods; the CLI, REPL script path, and runtime-unit
loader no longer sequence `frontend -> checked -> execution graph` themselves.

The compiler emits state/readiness telemetry such as:

```text
fz.compiler.module_discovered
fz.compiler.source_loaded
fz.compiler.parsed
fz.compiler.body_surface_ready
fz.compiler.fn_group_discovered
fz.compiler.fn_group_lowered
fz.compiler.fn_group_seeded
fz.compiler.fn_group_requested
fz.compiler.fn_group_cache_hit
fz.compiler.interface_ready
fz.compiler.macro_surface_ready
fz.compiler.runtime_module_reachable
fz.compiler.runtime_lowered
fz.compiler.runtime_planned
fz.compiler.cache_hit
```

Tests should prefer these signals over indirect structural assertions.

## Import Resolution

Resolution is source-backed. When a program imports `Foo`, the resolver asks the
compiler to ensure `Foo`'s interface from source. There is no external
artifact-store interface table on the normal path.

The resolver still enforces the same public-contract rules:

- missing module -> `RESOLVE_UNKNOWN_MODULE`
- missing imported export -> `RESOLVE_UNKNOWN_IMPORT`
- conflicting imports -> `RESOLVE_CONFLICTING_IMPORT`
- local sibling definitions shadow imports

Flattened dotted call spellings are still the IR rendering, not the identity.

## Runtime Library

`runtime_library` owns the embedded standard-library source modules. Each module
is registered individually with a role:

- core prelude modules are made available through the compiler's prelude path
- library modules are discovered and parsed only if a checked program reaches
  them

The important property is laziness: asking for `Process` does not parse `Utf8`,
`Enum`, or any other unrelated runtime module.

`Compiler::discover_runtime_reachable_modules` computes the runtime-module
closure from the checked program's external interfaces. The pipeline then lowers
and plans only those reachable runtime modules, one module at a time.

## Execution Graph

`modules::pipeline` owns the production path from a checked frontend result to
the linked runtime graph.

The shape is:

1. run the frontend and collect local/external interfaces
2. validate public interfaces if the caller asked for strict interface output
3. compute reachable runtime modules through the compiler
4. lower and plan only the reachable runtime modules
5. link the root module plus those runtime units
6. run the authoritative planner on the linked module

`CompileMode::Lto` still validates interfaces, erases boundaries, and replans
the linked module, but it operates on compiler-owned source modules and linked
IR only.

## Command Surface

The surviving CLI shape is intentionally small:

- `fz run [--lto] <src.fz>`
- `fz build [--lto] <src.fz> -o <out>`
- `fz dump <src.fz> --emit ...`

There are no provider-artifact flags on the live path. `dump --emit interfaces`
renders source-derived module contracts. `dump --emit specs`, `bodies`, and
`outcomes` are compiler-internal views over the linked program.

## Telemetry and Tests

The module system is proven by telemetry-driven tests in two layers:

- pinpoint tests assert local claims such as "a module parsed once" and record
  timings such as `elapsed_ns`
- suite-wide invariant checks validate compiler-world integrity after each
  phase

Representative properties the suite enforces:

- a source module is parsed once per compiler world
- repeated interface or macro-surface requests hit compiler caches
- unreachable source `fn/arity` groups stay cold
- repeated source compiles hit cached reachable function-groups
- runtime reachability marks only live modules
- quicksort-style builds parse only the root source plus the runtime modules
  they actually reference

That telemetry is the contract for keeping the source-backed loader honest.
