# Pattern Matching

Pattern matching has one decision model shared by every match site. A
`PatternMatrix` (rows of patterns over a list of subjects) normalizes source AST
patterns into ordered rows. Those rows are converted through the current
adapter compiler into a `DispatchMatrix`, compiled to a `DispatchGraph`, and
then adapted back to the Matcher ABI for existing inline lowering and receive
storage. The rule the whole model enforces is **test first, project second**: a
constructor's fields are read only on the control-flow edge where that
constructor's shape is already proven.

Four layers, one decision model:

- `src/pattern_matrix` owns AST-facing row construction and diagnostics input.
  Its Matcher compiler is crate-internal adapter machinery, not a separate
  semantics owner.
- `src/dispatch_matrix/pattern.rs` owns source-pattern dispatch decisions. It
  converts AST-facing rows into `DispatchMatrix` region questions, compiles them
  to a `DispatchGraph`, and keeps body ids plus leaf bindings as opaque
  outcomes.
- `src/exec/matcher` owns the remaining backend ABI shape: subjects, tests,
  switch keys, guards, bindings, and outcomes, with no AST inside.
- `src/ir_lower/matcher.rs` owns turning the graph-derived `Matcher` adapter
  into IR primitives and branch structure.

Function clauses, `case`, `with` else arms, and `receive` all build a
`PatternMatrix`, route through `DispatchMatrix`, and lower/store the
graph-derived `Matcher` adapter the same way. Single-clause `fn` heads and
single, unguarded `fn` lambdas skip the matrix and bind their parameters inline,
but obey the same test-first rule.

## The Matrix And Its Compiler

A `Row` carries column `patterns` (one per subject), `preconditions` (`@spec`
type tests, run before the guard), `bindings` already proven as specialization
peeled columns away, an optional `guard`, and a `body_id`. Rows arrive in source
order with strictly increasing `BodyId`s; `validate_source_order` rejects
anything else, because first-match priority is encoded in that order.

The crate-internal PatternMatrix adapter compiler runs a Maranget-lite
algorithm in `builder.rs`:

- Pick the leftmost column that any row constrains (`pick_specialization_column`).
  `Wildcard`/`Var` rows are transparent and join every specialization, recording
  their bindings.
- `pick_kind_for_column` reads the first constraining pattern to choose a
  `SwitchKind` (`TupleArity`, `Atom`, `Int`, `Float`, `Bool`, `Nil`, `Binary`,
  `ListCons`). The matrix specializes that column into a `Switch` with one
  `SwitchKey` case per distinct constructor plus a default.
- Specializing a constructor replaces its column with the constructor's
  sub-subjects: a tuple of arity 3 becomes three `TupleField` columns; a cons
  becomes `ListHead` and `ListTail` columns. Merged constructor-and-default rows
  are re-sorted by `body_id` so priority survives.

A `SubjectRef` is the path to a value: it names *where* a value lives without
yet computing it. The matrix and the matcher carry distinct `SubjectRef` types.
The matrix's is rooted at a `Var` (`TupleField`/`ListHead`/`ListTail` reach into
it). Compilation rewrites it (`subject_to_matcher_ref`) into the matcher's, which
is rooted at `Input` and adds `MapValue` and `BitstringField` for the paths that
map and bitstring tests produce.

Some patterns have no constructor switch: `Map`, `Bitstring`, and `Pinned`.
`find_unspecializable_row` pulls such a row out and lowers it through the
per-row path (`per_row_to_matcher_node`), which walks the pattern with
`append_pattern_ops` into a straight-line chain of `MatcherTest`s. A `Pinned`
pattern dispatches on a runtime value (`MatcherTest::EqPinned` against a
`pinned` slot), so there is no switch kind for it.

## The Matcher ABI Adapter

`Matcher` holds `inputs`, `pinned` slots, `prepared_keys` (heap constants
materialized outside matcher execution, e.g. float/binary map keys), a `nodes`
arena, and a `root`. It is the current backend ABI shape. Every `MatcherNode` is
one of:

- `Fail` — no row matched on this edge.
- `Leaf` — a `body_id` plus the `MatcherBinding`s (name -> `SubjectRef`) to
  expose to the body.
- `Switch` — a `subject`, a `SwitchKind`, `(SwitchKey, NodeId)` cases, and a
  `default`.
- `Test` — one `MatcherTest` with `on_true` / `on_false` edges.
- `Guard` — a `GuardExpr` with `on_true` / `on_false` edges.

`MatcherTest` variants name exactly the questions the runtime can ask:
`EqConst`, `EqPinned`, `TupleArity`, `ListCons`, `MapKind`, `MapHasKey`,
`Bitstring`, `Type`. Bindings live only on `Leaf` nodes, so a name is exposed
only once its row's tests have all passed.

The DispatchMatrix producer preserves that boundary: tests become region
questions and leaf bindings become outcome metadata. Map-value and bitstring
field subjects are attached to successful branch evidence, not to failed edges.
Guards become guard-region questions with the original `GuardExpr` stored beside
the matrix as producer metadata. The graph-derived `Matcher` exists so current
lowering code and receive records can keep their ABI while the decision model is
unified.

### Guards

A `Guard` node holds a `GuardExpr` — constants, subject/pinned references, and
unary/binary operators. A guard that calls a helper function compiles that
helper's clauses through `DispatchMatrix` into a nested graph-derived `Matcher`
and stores it as
`GuardExpr::Dispatch { inputs, dispatch }`. `lower_guard_helper_call_to_dispatch`
builds the nested matrix, tracks a call stack to reject guard-call cycles
(`GuardCallCycle`), and lifts the helper's free names into `pinned` slots.
Lowering a `Dispatch` runs the nested matcher into a fresh value with a `false`
fallthrough, so a guard helper that matches nothing yields `false` rather than
halting.

## Lowering To IR

`lower_pattern_matrix_to_current_fn` compiles the matrix, routes it through
`DispatchMatrix`, adapts the resulting `DispatchGraph` back to `Matcher`, then
walks that adapter with `lower_matcher_node`, threading a `fail_block` and a
body callback. A `MatcherLowerState` caches each `SubjectRef`'s materialized
`Var` per control-flow edge, so a projection is computed once and only where it
is legal.

`materialize_matcher_subject` is where projections become primitives:

- `TupleField` -> `Prim::TupleField`
- `ListHead` -> `Prim::ListHead`
- `ListTail` -> `Prim::ListTail`
- `MapValue` -> `Prim::MapGet`

The tests become primitives too. `lower_matcher_bool_test` and
`lower_matcher_switch_test` map a `MatcherTest` / `SwitchKey` to:

- `TupleArity` / `MapKind` / `Type` -> `Prim::TypeTest` against a tuple-of-arity,
  map-top, or the annotated type.
- `ListCons` and `SwitchKey::Cons` -> `Prim::IsListCons`.
- `EqConst { EmptyList }` and `SwitchKey::EmptyList` -> `Prim::IsEmptyList`.
- other `EqConst` / literal keys -> a constant plus `Prim::BinOp(Eq, ...)`.
- `EqPinned` -> equality against the resolved pinned `Var`.

A `Test` node lowers as: emit the boolean primitive, branch, recurse into
`on_true` with the cloned (true-edge) state, then recurse into `on_false` with
the parent state. A `Switch` lowers each case as its own conditional branch and
recurses into the `default` last.

### Test First, Project Second

Constructor projections are valid only below a dominating constructor test. The
graph shape and the per-edge `MatcherLowerState` enforce this together: for

```text
[head | tail]
```

the matcher asks `Prim::IsListCons(subject)`. `Prim::ListHead(subject)` and
`Prim::ListTail(subject)` are materialized only inside the true edge; the false
edge falls to the next row or to `fail_block`. A non-empty-list test and an
empty-list test answer different questions: `Prim::IsEmptyList(subject)` is true
only for the empty-list sentinel, and its false edge still contains non-empty
lists *and* non-list values — so it cannot gate cons projections. The planner
narrows the false edge of `IsEmptyList` to `subject \ []` (set difference), not
to `non_empty_list(any)`; the true edge of `IsListCons` narrows to
`non_empty_list(any)` (`src/ir_planner/narrow.rs:216`,
`src/ir_planner/narrow.rs:227`).

Tuples follow the same rule: a field projection sits below the
arity `TypeTest`. The inline single-clause path mirrors it in `match_tuple` and
`match_list` (`src/ir_lower/expr.rs:702`, `src/ir_lower/expr.rs:725`): type-test
or `IsListCons`/`IsEmptyList`, enter the success block, then project.

### Maps Distinguish Present-nil From Absent

The matrix lowers a map entry as presence-then-value, not as a `nil` compare.
`MatcherTest::MapHasKey` lowers to `Prim::MatcherMapGet(map, key)` followed by
`Prim::IsMatcherMapMiss(value)`: a dedicated miss sentinel separates "key
absent" from "key present holding `nil`". The looked-up value becomes a
`SubjectRef::MapValue`, valid only on the present edge — a missed key never
inherits it. (The single-clause inline `match_map` path instead uses a plain
`Prim::MapGet` and a `nil` comparison.)

## Where Matrices Come From

- `lower_multi_clause` builds one column per parameter; matching leaves
  `TailCall` per-clause continuation fns (`fn_clause_N`); an exhausted matcher
  halts with `:function_clause`.
- `lower_case` builds a single-column matrix over the scrutinee; leaves route to
  `case_clause_N` continuations; exhaustion halts with `:case_clause`.
- `lower_with` lowers the `else` cascade through the same machinery.
- `lower_receive` compiles a one-column matrix over the candidate message
  through `DispatchMatrix` into a graph-derived cached `Matcher` carried on the
  receive term.
- Single-clause `fn` heads and single, unguarded lambdas bind parameters with
  `lower_pattern_bind`; on mismatch they halt with `:match_error`. A multi-clause
  or guarded lambda is rejected at lowering (`LowerError::Unsupported`).

## Compile-Time Analysis

`src/pattern_matrix/analysis.rs` reuses the dispatch producer for
diagnostics. `find_unreachable_rows` compiles the matrix (with guards normalized
to `true`, so a guard's reject edge is kept without evaluating it), routes it
through `DispatchMatrix`, and reports any `body_id` the `DispatchGraph` cannot
reach. `is_inexhaustive_with_domains` reports `true` when some graph path reaches
`Fail`; `SubjectDomain::List` lets a subject known to be a list count as covered
once both `EmptyList` and `Cons` cases exist in the dispatch matrix.
`src/frontend/pattern_check.rs` drives these over every match site and emits
warnings; it skips fns whose body is unreachable and skips coverage verdicts
when guards or type annotations are present, since the matrix treats those
clauses as plain catch-alls.

## Tiny Walkthrough

```text
fn f([h | t]), do: ...
fn f([]),      do: ...

matrix: subject s0, rows [ [h|t] -> 0 ], [ [] -> 1 ]
graph:   Test ListCons(s0)
           match -> Outcome 0  bind h=ListHead(s0), t=ListTail(s0)
           miss  -> Test EmptyList(s0)
                      match -> Outcome 1
                      miss  -> Fail
lower:   isc = IsListCons(s0); if isc -> cons-edge else next
           cons-edge: h = ListHead(s0); t = ListTail(s0); TailCall fn_clause_0
         else: ise = IsEmptyList(s0); if ise -> TailCall fn_clause_1 else Fail
Fail -> Halt(:function_clause)
```

The head and tail reads exist only inside the `IsListCons` true edge; the
empty-list edge never projects them.
