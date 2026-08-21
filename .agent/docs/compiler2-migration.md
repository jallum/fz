# Compiler2 Migration

Compiler2 owns the public command-line compiler surface. The old `fz` binary,
`Compiler`/`World` wrapper, REPL/test-runner front door, and old-world CLI dump
surface have been deleted.

## Current Decision

The compiler entry point is `fz2`. There is no compatibility `fz` wrapper.

The backend and type-name questions that blocked migration are settled:

- compiler2 owns source submission, type naming, contract resolution, semantic
  closure, backend-product construction, and `NativeProgram(root)`;
- `fz2 run`, `fz2 interp`, `fz2 build`, and `fz2 test` submit source directly to
  compiler2 (`fz2 test` discovers and runs every `test(:name) do ... end` item,
  one subprocess per test, instead of seeding `main/0`);
- native backend time is named at the compiler2 artifact boundary by
  `fz.compiler2.native_backend.compile`, with raw codegen phases nested below it;
- source-fragment re-lexing and per-call `ModuleTypeEnv` rebuilds are gone on the
  compiler2 path.

Remaining migration work is no longer about an old executable oracle. It is
about retiring shared old-world substrate once compiler2 has a native
replacement for each piece.

## Fixture Signal

Every fixture under `fixtures2/behavior/` participates in the compiler2 matrix
by default on all three paths (`run`, `interp`, `build`); a fixture only drops a
path through an explicit filename prefix (structural narrowing, e.g. an
AOT-only destructor fixture) or an explicit `defer.<path>:` frontmatter line
(a real, currently open gap). There is no separate "fz2 matrix path" opt-in
left to promote — `run`/`interp`/`build` in `tests/fixture_matrix.rs` are the
fz2 paths; the old `fz` compiler and its `repl`/`jit`/`aot` legs are gone.

`tests/fz2_cli.rs` also probes a handful of matrix fixtures directly
(`quicksort`, `map_three_path_parity`, `defstruct_runtime`,
`utf8_smart_constructor`, `enum_predicate_search`, `enum_take_drop_split`,
`case_with_total`, `case_tuple_pattern_sequential`, `concurrency_ping_pong`,
`receive_selective_refs`, `receive_float_pattern`, `macro_inc`,
`cross_module_macro`, `item_macro_source`, `pipe_headless_case`,
`lambda_sugars`, `operator_sugars`) for targeted CLI/telemetry contracts (macro
loading, module dispatch parity, reusable-cons counters); these reuse existing
matrix fixtures rather than duplicating fixture-only coverage.

## AOT Runtime Archive Resolution

`fz2 build` links generated object code against the `fz-runtime` staticlib.
`build.rs` builds the exact `fz-runtime` staticlib into its isolated `OUT_DIR`
target once, then records that path in the `fz2` binary. Ordinary AOT builds
use that recorded archive directly: they do not invoke Cargo, scan hashed
dependency archives, or depend on the caller's current directory.

`FZ_AOT_RUNTIME_STATICLIB=<absolute path>` is the escape hatch: set to a
non-empty absolute path naming a prebuilt `libfz_runtime*.a`, it short-circuits
archive resolution to that path. The override must be absolute and exist; its
ABI must match the linking `fz2`'s target/profile, which is not checked
automatically. Packaging a binary independently of Cargo's build directory
must supply this override with the packaged runtime archive.

## Remaining Classes

**Golden/allocation decisions are closed.** `append`, `bsx_guard_eq`,
`enum_sort`, `filter`, `process_heap_stats`, `quicksort`, and `reverse` each
carry an fz2-specific golden and pass the full matrix. `bsx_guard_eq`'s guard
dispatch materializes `GroundValue::Utf8Binary` in the backend interpreter, so
`s == "hi"` compares through the same brand-blind path on every leg.
`enum_list_allocations` still carries a real, open native-lowering allocation
regression (see below) and stays deferred on `run`/`build` rather than being
blessed. `tree` stays deferred on all three paths for an unrelated reason: it
still lacks the expected type/no-matching-clause diagnostic. `spec_violation`
is undeferred and now pins `spec/violation` on `run`, `interp`, and `build`.

**Source-surface gaps are closed.** The Elixir-surface parser batch for
keyword lists, no-parens calls, trailing `do`, quoted keyword keys, and
keyword-boundary diagnostics is covered by compiler2's `fixtures2/00532`-`00546`
corpus. `sample_tests` and `sample_tests_module` cover the `test()` macro
front door (`kind: test`, discovered via `fz2 test`/`fz2 test --interp`; the
`build` leg stays structurally deferred since a `kind: test` fixture has no
single `main/0` to AOT-build against).

**Callable/protocol/Enum artifact gaps are closed for closed unions.** Latent
callable executables derive from reachable value types and match callable
inventory against compatible closed activation keys instead of raw capture
`Ty` ids. Multi-target protocol dispatch for union receivers materializes
local dispatch from the settled multi-target semantic fact. Under that
mechanism the union-receiver fixtures sit at:

- `enum_take_drop_split` — declared on all three paths; green on `build`,
  red on `interp`/`run` (interp: "backend value 0 is unbound" on a plain
  `Enum.take` beside an unused range binding, tracked as fz-9in).
- `range_enumerable` — green on all three paths.
- `enum_map_family` — green on all three paths.
- `map_enumerable` — green on `run`/`build`; red on `interp`.
- `enum_tier0`, `enumerable_protocol_dispatch` — deferred on all three paths
  (`enum_tier0` on the shared `Enum.reduce*` bridge over non-List Enumerables;
  `enumerable_protocol_dispatch` pending nominal struct-vs-map
  protocol-dispatch tests).
- `membership_operator` — green on all three paths.

`enum_take_drop_split` runs as a full run/interp/build matrix fixture. The
take/drop/split runtime functions that carry tuple accumulators use
`Enum.reduce_while/3` directly with single-clause callbacks, avoiding the
shared `Enum.reduce/3` bridge for those reducer shapes. Transport projection
also seeds capture-prefix executable inputs from upstream callable-flow facts
before the generic callable fallback, so reducer callbacks that capture a
direct-only predicate keep the predicate's exact callable shape through native
lowering.

**Runtime/interpreter gaps.** `utf8_pattern_match` is green on all three
paths; the interpreter gap it used to have is closed. `resource_lifecycle` is
green on all three paths; resource `.value` field access routes through the
shared named-field runtime ABI on backend interpreter and native paths.
`enum_predicate_search` and `enum_take_drop_split` are declared on all three
paths but currently fail all three — real, open gaps, not golden questions.

The `bsx_guard_eq` interpreter gap is closed: dispatch guard constants
materialize `GroundValue::Utf8Binary` values in the backend interpreter,
so guards such as `s == "hi"` compare through the same brand-blind runtime
equality path as ordinary `==`.

## What Remains Load-Bearing

- Compiler2 still reuses neutral runtime/native substrate: `fz_ir` shapes,
  native codegen runtime wrappers, diagnostics, source spans, dispatch-matrix
  helpers, module identities, and selected legacy type/rendering adapters.
- Old-world planner/codegen text probes are no longer active fixture-matrix
  trials. Compiler-shape contracts should be expressed through compiler2
  telemetry, compiler2 dumps, or fixture contracts.
- Shared `ExternDecl` carries only ABI-facing metadata. Compiler2 semantic
  extern facts stay in `LoweredExtern`, backend program facts, and
  `NativeBody.extern_marshals`.

## What Is Not A Cutover Blocker

- Compiler2 does not need the old planner or type-infer pipeline for fz2 runs.
- Compiler2 does not need the old `function_type_env` runtime-library re-lex path.
- Compiler2 does not need the old native `prepare_preplanned_native` path for its
  public JIT/AOT front doors.

## Raw IR Call Target Invariant

Raw `fz_ir::Term::Call` and `Term::TailCall` no longer use a bare `FnId`
callee. Direct calls carry `DirectCallTarget`, which is either `Local(FnId)` for
a body in the current linked module or `ProviderBoundary(Mfa)` for a provider
symbol that must be resolved before interpreter/native execution. Import edge
metadata is derived from provider-boundary term targets; it is not an
authoritative side table and no `__external__` stub body should be synthesized.

## Compiler2 Callable Target Invariant

`FunctionId` is callable identity, not proof that a local body exists.
Compiler2 semantic summaries therefore distinguish `SelectedCallee::Function`
from `SelectedCallee::ProviderBoundary`. Artifact, ABI-ready, emission-ready,
and backend direct-call projections carry one generic `CallTarget<T>` with the
same local-vs-provider-boundary shape. Local targets point into the closed
executable frontier; provider-boundary targets keep the provider `FunctionId`
until native lowering converts it to raw IR `DirectCallTarget::ProviderBoundary`
with an `Mfa`.

Provider-boundary functions do not wait for `DefineFunction`, local activation
facts, dispatch masks, or local recursive graph expansion. They can contribute a
call summary and raw provider-boundary import edge, but they do not synthesize a
stub executable or a fake local body.

Because a provider boundary has no local body, no consumer may read it. Runtime
demand derivation crosses a `SelectedCallee::ProviderBoundary` target purely
through its settled `surface_inputs`, delivering each argument at its boundary
demand (`boundary_runtime_demand`); it never consults `lowered_body` to inspect
an extern signature, which is interface-only territory the body cannot answer.

## Captured-callable surface flows from the producer, not the closure value

When a clause builds a local closure that captures a callable, the captured
callable's runtime demand lives in the *producer's own executable*, in the
input-demand prefix that precedes the closure's parameters. `run(_list, f), do:
(fn () -> f.(1) end)` captures `f` into a returned continuation that invokes it
at `(int)`; the continuation executable already proves that surface, and
`propagate_lambda_capture_demands` reads it back off the producer by matching the
capture-type prefix. The closure value's *own* call surface only selects which
specialization to read — a directly-called closure restricts to its invoked
surfaces, but an **escaped** closure (returned or stored, never called here)
carries no direct surface of its own, so the prefix match must not be gated on
the closure value's `resolved` being non-empty. Gating on it dropped the proven
capture surface and let `f` reach transport as a surface-less first-class demand,
tripping `generic_callable_shape`'s "callable surfaces proven upstream" guard.
The surface is proven in the runtime-demand contract; transport never recovers
it from a type.

Callable-flow facts are part of `RuntimeDemand(executable)`, not a separate
top-level fact family and not transport-local recovery. Runtime-demand transfer
records direct callable surfaces where a callable is invoked, and first-class
surfaces where a callable crosses an extern/provider/return/structural
boundary. When a surface is resolved to an executable, the surface and
resolution travel together as callable-flow edge evidence. Projection only emits
the builder's recorded surfaces and edges. It may merge a richer direct-surface
set into first-class publication when the same local callable escapes through a
less-specific boundary seed: the decision is set-theoretic over callable
argument types, not based on the number of observed surfaces. It must not
reconstruct callable surfaces or pair surfaces with resolutions later by walking
value demands or lowered bodies.

## Compiler2 Semantic Reachability Invariant

Semantic analysis only follows control destinations that can actually receive a
value. A tail value whose type has settled to `none` / `never` returns that
empty type to its caller and does not mark its continuation entry reachable. The
semantic closure should therefore contain the still-observable never-returning
call edge, but it must not require activation analysis, call edges, or materialized
executables for continuation code that cannot run.

Backend product construction reads the transport and executable products it
needs directly. Missing closure or transport evidence should surface as exact
product waits on the facts that can produce that evidence, not as a root-level
materialization retry or whole-program projection.

## Compiler2 Struct Type Invariant

A compiler2 struct value type carries one shape: nominal impl-target identity
plus ordered structural field evidence. The nominal arm preserves protocol
identity (`impl-target::<Struct>`); the tuple arm preserves positional field
evidence used by lowered struct patterns; the map arm preserves named field
evidence used by field access and struct specs.

Source struct expressions, `%Struct{}` type expressions, and protocol impl-target
selection all derive this shape through `World::struct_value_ty`. User structs
must not collapse to opaque-only impl targets, because intersecting an opaque-only
target with a concrete struct value erases the field evidence that downstream
semantic analysis needs.

## Deletion Rule

Do not add a wrapper around the deleted `fz` surface. New compiler-facing tests
and tooling should enter through compiler2 APIs or `fz2`.
