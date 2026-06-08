# Type Specialization

This is how compiler2 settles the types inside one activation, and why the set
of activations stays finite. It is the inference half of the semantic stratum;
[`semantic-fixpoint`](semantic-fixpoint.md) is the orchestration half (how
activations are discovered, keyed, and sealed). Read that first — this doc
assumes activations and the keying facts.

## Model

An activation is `(root, function, input)`. Inference settles its return type by
typing the function's **dispatch-reachable clauses** under those inputs:

```text
inputs                                    the activation's joined input types
reachable clauses = reachable_clause_ids(entry_dispatch, inputs)
return            = union over reachable clauses of each clause's body type
```

There is no separate inference IR and no per-cell solver lattice. `AnalyzeActivation`
walks the clause bodies once, threading a `values: HashMap<ValueId, Ty>` map, and
the cross-activation fixpoint lives entirely in the fact graph: a call reads its
callee's `ReturnType` fact, and when that fact widens the caller re-runs.

## Typing a body

`apply_step` types each `LoweredStep` directly against the `Types` algebra
(`world.types_mut()`), writing the result into `values`:

```text
Const          literal_ty(literal)               (int/float/atom/bool/binary/nil)
Tuple / List   tuple(elems) / list_ty(...)        from the element value types
FunctionRef    fn_ref_lit(target, arity)
Lambda         closure_ty(function, captures)     captures typed from `values`
BinaryOp       binop_ty(op, l, r)                 arithmetic -> int/float, cmp -> bool
UnaryOp        unop_ty(op, x)
DirectCall /   resolve_*_call -> callee activation + its current ReturnType
ClosureCall      (closure target read from the callee value's closure-lit type)
MapIndex /     any()                              not value-tracked
NamedFunctionRef
```

Operators are typed inline by `binop_ty`/`unop_ty` — there is no
`Kernel.<op>/2` spec lookup and no declared-spec backstop in inference. An
extern body types its return as `any()`.

Control flow and pattern steps refine the environment instead of producing a new
value:

```text
If              clone `values` into each branch, type both, union the results
AssertLiteral   values[source] := source ∩ literal       (narrow on a match arm)
AssertTuple     values[source] := source ∩ tuple(any×N)
AssertEmptyList values[source] := source ∩ []
AssertSame      values[source] = values[value] := source ∩ value
TupleField      values[value]  := tuple_field_type(source, index)
SplitList       values[head] := elem(source); values[tail] := list(elem(source))
```

`If` clones the value map per branch so a narrowing in one arm does not leak into
the other, then unions the arm results — the same shape `union` gives any branch.
The clause-level dispatch already proved the head shape, so clause params bind
without assertions; the `Assert*` steps narrow only where an inner `=` match or
guard demands it.

### Cross-activation flow

A call does not recurse into the callee's body. `resolve_function_call` computes
the callee activation key (reading `Recursive`/`DispatchMask`, see
[`semantic-fixpoint`](semantic-fixpoint.md)), contributes the callee's input
types to its `Activation` fact, subscribes the caller to the callee's
`ReturnType`, and returns the callee's *current* return estimate. When the callee
later widens its return, the caller re-runs and re-unions. Every moving part is
monotone, so the cross-activation loop settles.

## Specialization stays finite

The danger is a recursive function forking a fresh activation for every precise
input shape — an accumulator's `[] ⊔ [x] ⊔ [x,y] ⊔ …` cartesian product. Two
mechanisms bound it, both via the activation **key** (`canonical_activation_key`):

- **The convergence collapse.** For a recursive function, each non-dispatch input
  slot is keyed by its `convergence_class` — all pure list shapes fold to one
  class, disjoint families (`int` vs a tagged tuple) stay distinct. So many call
  shapes map to one key (the "balloon"), and the slot's actual type is recovered
  as the `refine_widen` join of the contributing inputs.
- **The dispatch mask.** The collapse applies only to slots that do *not* drive
  clause selection. A dispatch slot keeps empty-vs-cons (or tag) precision, so
  clause reachability stays sharp while accumulators balloon.

Termination rests on finite height: `refine_widen` collapses literal axes to
their base and merges list shapes, so a joined slot ascends a bounded chain
(`int_lit(1) ⊔ int_lit(2) = int`; `[] ⊔ nonempty(t) = list(t)`). Return types
ascend the same ladder. The key ops live in [`type-world`](type-world.md); the
algebra in [`set-theoretic-types`](set-theoretic-types.md).

```text
fib(0,0,1), fib(1,0,1), fib(10,0,1), fib(20,0,1)
  n is a dispatch slot (matched 0,1); a,b are accumulators
  recursive -> a,b keyed by convergence_class, n kept precise then widened to int
  one activation (root, fib, [int,int,int]); reachable clauses unioned -> int
```

## Not-computed is not `none`, and `none` is not `any`

Three states stay distinct, and conflating them poisons the fixpoint:

- **Not computed yet** — the callee's `ReturnType` fact does not exist or has not
  reached its final value. The caller subscribes and uses `none()` as the
  lattice-bottom estimate (the identity for `union`/`refine_widen`), then re-runs
  when the fact settles. The Pending/Known distinction is carried by *fact
  presence and revision*, not by a placeholder type.
- **`none`** — a settled empty type: the value set is uninhabited (a callee that
  always diverges, or a call with an empty argument type). It stays `none`.
- **`any`** — a real top fact (an untracked value, a named-ref call), not a stand-in
  for missing proof.

Because `none` is the union identity and the caller re-runs on every widening, a
transient `none` estimate never freezes a caller's return: it only ascends as the
callee settles.

## Proof gates

```text
cargo test --lib compiler2::drive_test::compiler2_quicksort_root_closes_with_a_finite_recursive_frontier
cargo test --lib compiler2::drive_test::compiler2_recursive_keying_sees_recursion_through_generated_lambdas
cargo test --lib compiler2::drive_test::compiler2_semantic_analysis_derives_reachable_call_edges_and_tuple_return_need
cargo test --lib compiler2::types     # refine_widen / convergence_class ladders
```
