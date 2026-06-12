# Compiler2 Migration

Compiler2 is ready below the artifact seam, but the old compiler is still the
oracle for the full source surface. The cutover decision is therefore not
"backend readiness"; it is fixture-contract parity.

## Current Decision

Do not scrap the old `fz` surface yet.

The backend and type-name questions that blocked migration are settled:

- compiler2 owns source submission, type naming, contract resolution, semantic
  closure, and the artifact ladder through `NativeProgram(root)`;
- `fz2 run`, `fz2 interp`, and `fz2 build` submit source directly to compiler2
  and assert that old frontend/planner/type-infer telemetry stays absent;
- native backend time is named at the compiler2 artifact boundary by
  `fz.compiler2.native_backend.compile`, with raw codegen phases nested below it;
- source-fragment re-lexing and per-call `ModuleTypeEnv` rebuilds are gone on the
  compiler2 path.

The remaining blocker is above that seam: the checked fixture oracle still
covers more source/runtime behavior than the fz2 matrix declares.

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

**Runtime/interpreter gaps.** Current fz2 failures also include
`resource_lifecycle`, `tail_recursion` on `fz2 interp`, `utf8_pattern_match` on
`fz2 interp`, and `enum_predicate_search` on `fz2 interp`.

## What Remains Load-Bearing

- The old `fz` CLI and fixture matrix paths remain the executable oracle for
  source surfaces not yet represented by fz2 matrix paths.
- The legacy frontend/parser/lowering/spec environment remains load-bearing for
  that old surface until the fz2 fixture matrix covers the agreed contract.
- `crate::type_expr` / `ModuleTypeEnv` remain frozen for the old frontend only;
  compiler2 does not reuse them.
- `ExternDecl.ret_descr` and `ExternDecl.semantic_contract` are a native
  substrate cleanup, already tracked by `fz-rh2.15`.

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

## Cutover Rule

The old compiler can be scrapped only after the agreed source/contract fixture
surface is represented by fz2 matrix paths or explicitly declared out of scope.
Deletion tickets come after that coverage decision, not before it.
