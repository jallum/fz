# Compiler2 Migration

Compiler2 owns the public command-line compiler surface. The old `fz` binary,
`Compiler`/`World` wrapper, REPL/test-runner front door, and old-world CLI dump
surface have been deleted.

## Current Decision

The compiler entry point is `fz2`. There is no compatibility `fz` wrapper.

The backend and type-name questions that blocked migration are settled:

- compiler2 owns source submission, type naming, contract resolution, semantic
  closure, and the artifact ladder through `NativeProgram(root)`;
- `fz2 run`, `fz2 interp`, and `fz2 build` submit source directly to compiler2;
- native backend time is named at the compiler2 artifact boundary by
  `fz.compiler2.native_backend.compile`, with raw codegen phases nested below it;
- source-fragment re-lexing and per-call `ModuleTypeEnv` rebuilds are gone on the
  compiler2 path.

Remaining migration work is no longer about an old executable oracle. It is
about retiring shared old-world substrate once compiler2 has a native
replacement for each piece.

## Fixture Signal

As of 2026-06-10, fixture metadata declares fz2 matrix paths for 17 fixtures:

- `case_tuple_pattern_sequential`
- `case_with_total`
- `concurrency_ping_pong`
- `cross_module_macro`
- `defstruct_runtime`
- `item_macro_source`
- `lambda_sugars`
- `macro_inc`
- `map_three_path_parity`
- `operator_sugars`
- `opaque_fn_value_join`
- `pipe_headless_case`
- `receive_float_pattern`
- `receive_selective_refs`
- `repr_seam_closure_predicate`
- `tailcall_closure_captures`
- `utf8_smart_constructor`

`tests/fz2_cli.rs` also probes `quicksort` as a telemetry contract, but
quicksort is not yet a fixture-matrix fz2 path because its fz2 allocation output
does not match the old native goldens and needs an explicit fz2 golden decision.

An ad hoc sweep of success fixtures through `target/debug/fz2 run` and
`target/debug/fz2 interp` against `expected.txt` produced this fixture-level
shape:

```text
pass both run/interp:      88 fixtures
mismatch, no fz2 failure:   9 fixtures
has fz2 failure:           21 fixtures
```

This sweep is a triage signal, not the committed oracle. It excludes abort /
diagnostic fixtures and compares only against `expected.txt`, so allocation
fixtures with per-path goldens naturally appear as mismatches until fz2-specific
goldens are chosen.

## Remaining Classes

**Matrix coverage gap.** Many fixtures already pass fz2 run/interp in the sweep
but are not declared in fixture metadata. Those should move into the matrix in
batches, with fz2-build included only after it is observed for that batch.

**Golden/allocation decisions.** The no-fail mismatch set is:

```text
append
bsx_guard_eq
enum_list_allocations
enum_sort
filter
process_heap_stats
quicksort
reverse
tree
```

Most are allocation-stat or path-golden questions. `bsx_guard_eq` needs a
semantic check because fz2 interp returns a different branch.
After `fz-rh2.16.3`, `enum_reduce_suspend` also runs through fz2
run/interp/build but needs fz2-specific allocation goldens before it can enter
the matrix.

**Source-surface gaps.** The Elixir-surface parser batch for keyword lists,
no-parens calls, trailing `do`, quoted keyword keys, and keyword-boundary
diagnostics is now covered directly by compiler2's `fixtures2/00532`-`00546`
corpus. The remaining item-surface fixtures still called out in the sweep are
`sample_tests` and `sample_tests_module`.

**Callable/protocol/Enum artifact gaps.** `fz-rh2.16.3` fixed the closed
callable-entry side of this class by deriving latent callable executables from
reachable value types and by matching callable inventory against compatible
closed activation keys instead of raw capture `Ty` ids. `fz-rh2.16.7` closes
the remaining multi-target protocol dispatch gap for union receivers by
materializing local dispatch from the settled multi-target semantic fact, so
`enum_map_family`, `enum_take_drop_split`, `enum_tier0`,
`enumerable_protocol_dispatch`, `map_enumerable`, `membership_operator`, and
`range_enumerable` all run through fz2 again.

`fz-bin.16` re-enables `enum_take_drop_split` as a full run/interp/build matrix
fixture. The take/drop/split runtime functions that carry tuple accumulators now
use `Enum.reduce_while/3` directly with single-clause callbacks, avoiding the
shared `Enum.reduce/3` bridge for those reducer shapes. Transport projection
also seeds capture-prefix executable inputs from upstream callable-flow facts
before the generic callable fallback, so reducer callbacks that capture a
direct-only predicate keep the predicate's exact callable shape through native
lowering.

**Runtime/interpreter gaps.** Current fz2 failures also include
`resource_lifecycle`, `tail_recursion` on `fz2 interp`, `utf8_pattern_match` on
`fz2 interp`, and `enum_predicate_search` on `fz2 interp`.

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
boundary. Projection only emits the builder's recorded surfaces. It may merge a
richer direct-surface set into first-class publication when the same local
callable escapes through a less-specific boundary seed: the decision is
set-theoretic over callable argument types, not based on the number of observed
surfaces. It must not reconstruct callable surfaces later by walking value
demands or lowered bodies.

## Compiler2 Semantic Reachability Invariant

Semantic analysis only follows control destinations that can actually receive a
value. A tail value whose type has settled to `none` / `never` returns that
empty type to its caller and does not mark its continuation entry reachable. The
semantic closure should therefore contain the still-observable never-returning
call edge, but it must not require activation analysis, call edges, or materialized
executables for continuation code that cannot run.

`fz.compiler2.materialize.wait_fresh_closure` records the reason
`MaterializeRoot` is waiting for a sealed semantic closure. It is a diagnostic
signal for stale or incomplete closure facts, not a retry mechanism and not a
substitute for publishing the minimally necessary semantic facts.

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
