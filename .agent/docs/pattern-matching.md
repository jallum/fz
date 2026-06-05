# Pattern Matching

Pattern matching has one decision model shared by function clauses, `case`,
`with else`, receive probes, and guard-compatible helper dispatch.
`SourcePatternRows` is row data over source patterns; `DispatchMatrix` owns the
questions, ordering, branch evidence, and executable `DispatchGraph`.

The pipeline is direct:

```text
source clauses
  -> SourcePatternRows
  -> PatternDispatchPlan
       matrix: DispatchMatrix
       graph: DispatchGraph
       payloads: outcomes, bindings, guards, pinned inputs, prepared keys
  -> inline lowering / interpreter execution / receive codegen
```

There is no production `Matcher` data model. Pattern code must not rebuild a
second graph shape to satisfy an old ABI. If a path needs matching semantics, it
should consume `PatternDispatchPlan` or the underlying `DispatchGraph` directly.

## Layer Ownership

- `src/dispatch_matrix/pattern/source.rs` owns AST-facing row data and diagnostics over those rows.
  It does not own executable matching.
- `src/dispatch_matrix/mod.rs` owns the generic dispatch model: `Region`,
  `Order`, `Outcome`, branch-local `EdgeEvidence`, and `DispatchGraph`.
- `src/dispatch_matrix/pattern.rs` owns source-pattern production. It converts
  AST patterns into `RegionQuestion`s and stores pattern-specific payloads beside
  the matrix as `PatternDispatchPlan`.
- `src/ir_lower/pattern_dispatch.rs` walks `DispatchGraph` into inline IR for
  function clauses, `case`, `with else`, and guard helper dispatch.
- `src/ir_interp/dispatch_exec.rs` executes receive probes from the same plan.
- `src/ir_codegen/receive.rs` emits the scheduler-facing receive probe function
  by walking the same plan.

## Test First, Project Second

Constructor projections are valid only on a branch where the constructor test
has succeeded. The graph carries that rule structurally.

For `[head | tail]`, the dispatch asks `ListCons(subject)`. The success edge
projects `ListHead(subject)` and `ListTail(subject)`; the miss edge does not.
For tuples, `TupleArity(n)` dominates every `TupleField` projection. For maps,
`MapKeyPresent(map, key)` projects a map value only on the present edge, so a
present `nil` value and an absent key remain distinguishable.

This rule is the reason the matrix carries branch evidence rather than letting
lowering freely materialize paths from syntax.

## Pattern Payloads

`PatternDispatchPlan` keeps producer-specific payloads outside the generic
matrix:

- `outcomes`: body id plus source bindings for the winning row.
- `guards`: guard expressions and nested guard dispatch plans.
- `pinned`: `^name` inputs captured from the surrounding scope.
- `prepared_keys`: heap values, such as atom/binary/float map keys, materialized
  once outside the dispatch graph.
- `bitstring_direct_bindings`: names introduced by bitstring fields that later
  field-size expressions may reference.

The generic `DispatchMatrix` sees only regions and opaque outcome ids. Bodies,
receive wakeup behavior, and guard result interpretation belong to the producer.

## Lowering Sites

- Multi-clause functions build one subject per parameter and route successful
  outcomes to `fn_clause_N` continuation functions. Exhaustion halts with
  `:function_clause`.
- `case` builds one subject for the scrutinee and routes outcomes to
  `case_clause_N`; exhaustion halts with `:case_clause`.
- `with else` dispatches the unmatched value through the same machinery.
- `receive` builds one subject for the candidate message. The receive term
  stores an `Arc<PatternDispatchPlan>`; the interpreter and native receive probe
  both run that cached plan against mailbox messages.
- Single-clause unguarded function heads and lambdas still bind inline because
  there is no dispatch choice. They must still obey test-first/project-second.

## Guards

Guards compile into `PatternGuardExpr`. A pure helper call in a guard lowers to a
nested `PatternGuardExpr::Dispatch` whose `PatternGuardDispatch` contains a
full `PatternDispatchPlan` for the helper clauses plus one expression per helper
body. Guard helper lowering tracks a call stack and rejects cycles with
`GuardCallCycle`.

Nested guard dispatch returns a boolean-ish guard value: no matching helper arm
means the guard fails, not that the surrounding match halts.

## Diagnostics

`src/dispatch_matrix/pattern/source.rs` uses the same producer. It normalizes guards to
`true` for coverage analysis, compiles the rows to a `PatternDispatchPlan`, and
walks the `DispatchGraph`:

- `find_unreachable_rows` reports row body ids that no graph path reaches.
- `is_inexhaustive_with_domains` reports whether some path reaches `Fail`.
- `KnownSubjectDomain::List` lets a known-list subject count as covered when both
  empty-list and cons regions are present.

Diagnostics should not reimplement matching with syntax walkers. If a warning
depends on dispatch reachability, ask the dispatch graph.
