# Pattern Matching

Pattern matching has one canonical decision model: `PatternMatrix` compiles
rows into `MatcherNode` tests, switches, guards, failures, and leaves. Function
clauses, `case`, multi-clause lambdas after desugaring, receive matchers, and
destructuring all use the same idea: test first, then materialize bindings only
on the successful path.

## Refutable Projections

Constructor projections are only valid below a dominating constructor test.

For a cons pattern:

```text
[head | tail]
```

the matcher asks whether the subject is a non-empty list with
`Prim::IsListCons(subject)`. Only the true branch may emit
`Prim::ListHead(subject)` and `Prim::ListTail(subject)`. The false branch
continues to the next row or the match failure block.

`Prim::IsEmptyList(subject)` answers a different question. It is true only for
the empty-list sentinel. Its false branch includes both non-empty lists and
non-list values, so it must not guard cons projections. Planner narrowing for
the false branch is `subject \ []`, not `nonempty_list(any)`.

Tuple projections follow the same rule: a tuple field projection is below the
arity/schema `TypeTest`. Map patterns use matcher map lookup with an explicit
miss sentinel so present `nil` remains distinct from an absent key.

## Function Clauses

Multi-clause functions lower through `lower_multi_clause`, which builds a
`PatternMatrix` from the clause parameter patterns and guards. The inline
matcher lowering then routes matching leaves to per-clause continuation
functions. A failing row falls through to the next matcher row; an exhausted
matcher halts with `:function_clause`.

Single-clause functions still bind parameters inline, but their constructor
helpers follow the same dominance rule: test the shape, enter a success block,
then project fields or list head/tail.

## Proof Gates

Gate changes here with:

- `cargo test cons_function_clause_falls_through_for_non_lists_in_interp_and_native --lib`
- `cargo test recursive_cons_function_clause_runs_in_interp_and_native --lib`
- `cargo test if_is_empty_list_narrows_v_to_empty_list_in_then_branch --lib`
- `cargo test if_is_list_cons_narrows_only_then_branch_to_non_empty_list --lib`
- `cargo test nil_does_not_match_empty_list_pattern --lib`
- `cargo test empty_list_does_not_match_nil_pattern --lib`
