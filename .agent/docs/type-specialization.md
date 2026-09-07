# Type Specialization

This is how compiler2 settles the types inside one activation, and why the set
of activations stays finite. It is the inference half of the semantic stratum;
[`semantic-fixpoint`](semantic-fixpoint.md) is the orchestration half (how
activations are discovered, keyed, and settled). Read that first — this doc
assumes activations and the keying facts.

## Model

An activation is `(root, function, input)`. Inference settles its return type by
typing the function's **dispatch-reachable clauses** under those inputs:

```text
inputs             = the activation's joined input types
entry reachability = reachable clauses plus whether failure remains reachable
return             = union over reachable clauses of each clause's body type
```

`compiler2/dispatch_reachability.rs` owns that first calculation. Its branch
state is only the original input-root `Ty` row, memoized with the graph node.
Every tested `PatternSubjectRef` is projected fresh from those roots; exact
tuple-field constraints lift back through the full projection path before
intersecting the match root or subtracting the miss root. This keeps sibling
fields correlated instead of caching independently widened projected types.
Value-only predicates and projections the type lattice cannot represent retain
both branches.

The reachable clauses and failure bit remain one `EntryReachability` value in
the activation-analysis fact. Runtime demand and materialization consume that
value directly: exactly one reachable clause with unreachable failure enters
the clause body without rebuilding the function's runtime dispatch; multiple
clauses or a reachable failure retain the source dispatch graph.

List head/tail observations are positional, while `ListSig` element types are
homogeneous. The calculator may select an already-correlated list alternative
whose projected element is proved inside or outside a region, but an ambiguous
head never narrows the whole list element type. Thus observing one head cannot
silently constrain a later element.

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
the callee activation key (reading `Recursive`/`InputDemand`, see
[`semantic-fixpoint`](semantic-fixpoint.md)), contributes the callee's input
types to its `Activation` fact, subscribes the caller to the callee's
`ReturnType`, and returns the callee's *current* return estimate. When the callee
later widens its return, the caller re-runs and re-unions. Every moving part is
monotone: return evidence joins upward, equivalent type representatives are
quiet, an `AnalyzeActivation` publisher preserves its prior activation-input
evidence and `Activation` claims within an epoch instead of retracting a
callsite whose targets are temporarily unnamed, and a callsite edge that
resolves nothing this round republishes as `Unresolved` — the lattice bottom,
which never overwrites a resolved answer
([`semantic-fixpoint`](semantic-fixpoint.md)). The cross-activation loop
therefore settles without downstream phases reconstructing semantic decisions.

## Specialization stays finite

The danger is a recursive function forking a fresh activation for every precise
input shape — an accumulator's `[] ⊔ [x] ⊔ [x,y] ⊔ …` cartesian product. Two
mechanisms bound it, both via the activation **key** (`canonical_activation_key`):

- **The convergence collapse.** For a recursive function, each UNDEMANDED input
  slot is keyed by its `convergence_class` — the whole list family, including
  `[] | [t]` joins, folds to one class, while disjoint families (`int` vs a
  tagged tuple) stay distinct. So many call shapes map to one key (the
  "balloon"), and the slot's actual type is recovered as the union join of the
  contributing inputs.
- **The input demand.** The collapse is shaped by `InputDemand::forwarded_dispatch`
  (`FactKey::InputDemand`, `jobs::keying::derive_input_demand`). `Whole`
  preserves an input, tuple-field demand preserves only the demanded fields, and
  `ListShape(elem_demand)` preserves demanded element information from the whole
  list-family descriptor while converging empty-vs-cons shape for recursive
  keys. That keeps recursive list walkers from splitting the initial cons call
  from the possibly-empty tail, even when the input surface is already a joined
  list family, while still letting body evidence decide which clauses are
  reachable.

### Demand is transitive, and that is what a key must name

An activation's published return may depend only on what its key names. A body's
OWN entry dispatch is not that: `List.reduce_step/3` asks about its accumulator
tag and nothing else, yet it FORWARDS its list to `List.reduce_cont/3`, whose
key IS ground in the element. The element therefore decides which callee
activation the forward reaches, and so decides what comes back. Keyed on the
local mask alone, one `reduce_step/3` activation stood for every `Enum.reduce/3`
user in a program and published the JOIN of their returns (fz-kdt.183,
fz-kdt.122).

So the fact is a least fixpoint over the `DispatchDemand` lattice:

```text
demand(f, i) = local(f, i) ⊔ ⨆ { demand(g, j) : f forwards i to g@j }
```

A second axis rides the same walk. A dispatched position answers "which callee
activation does this reach"; a RETURNED position answers "what does this
activation publish", and an activation publishes ONE return, so two callers
that share a key share one answer. `InputDemand::returned` names the positions
the body's return IS, CONTAINS, or is a PROJECTION of, solved by the same Kleene
iteration over the same cone:

```text
returned(f, i) = ret(f, i) ⊔ ⨆ { returned(g, j) : f forwards i to g@j }
```

`ret` reads the lowered body: every tail that RETURNS rather than delivers, the
constructions its value is assembled from opened, and each leaf traced back
through projection steps to an input position. A call result is opaque and
needs no rule -- the forwarding edge above already carries the callee's whole
demand, this axis included.

The two axes never join into one mask, because they ask for two collapses. On
the dispatch axis `Whole` means a question reads the value itself and the key
keeps it VERBATIM. On the returned axis it means the value is the answer, and
the key keeps its addressed convergence CLASS: list families normalise to
`list(elem)` with the element kept at every depth, and closure brands still
erase -- the same bounded collapse fz-kdt.183 gives a demanded list. The depth
cap applies to LIST families only: `Types::convergence_class_at` checks
`ADDRESS_COLLAPSE_DEPTH` inside its `is_pure_list_family` branch, so a tuple,
map or resource nest at a returned position recurses uncapped and is bounded
only by the type that arrives. Every program built to exercise that already
fails to terminate at base for fz-kdt.177's reason, so the uncapped case is a
reading of the code rather than a measured divergence. Folding the two axes
would have to raise a returned position to `Whole`, which has no collapse at
all.

Positions the RECURSION supplies are subtracted, as a LEAST FIXPOINT: a
position is supplied when a self-call hands it a value the caller held nowhere,
or held only at positions that are themselves supplied. A supplied position
ascends within ONE caller, so keying it mints one activation per ascent state
(measured: `split3/5` 1 -> 8, `split4/6` 1 -> 16, every body identical) while
the SEED activation -- the one every caller passes through with the same `[]`
-- stays shared and keeps publishing the join. Cost with nothing bought, so it
is dropped.

The fixpoint is what makes that subtraction sound, and the eager form is not.
"The caller did not hold this value at this same position" misreads a
PERMUTATION: `go(n - 1, b, a)` hands each slot the value held at the other, and
the eager test marks both supplied, re-blending `go(0, a, _b), do: a`'s two
users into one key publishing `non_empty_list(binary) | non_empty_list(int)`.
Under the fixpoint the permutation's obligations never discharge and the set
settles empty. A position the recursion only carries is constant along the
ascent, and two keys there are two callers: `loop(n, junk)`'s junk, the slots
`go/3` permutes, and the payload of `walk({:go, acc}, n - 1)`, which the
rebuilt tuple hands on unchanged (fz-kdt.199).

"Forwards" is narrow on purpose: a direct-call tail argument that IS a clause
parameter. A projection (`[head | tail]`), a construction (`[head | acc]`), a
closure call and a lambda capture are all opaque, because the value that arrives
at the callee is not the value the slot names. That is why `partition/4`'s two
consed accumulators stay ONE activation while `List.reduce_step/3` splits.
The returned axis inherits this narrowness: a reconstructed or projected
forwarding argument is not an edge for it either, and neither is a
`LoweredTail::DirectCall`'s `dest` (fz-kdt.214 owns the edge set).
A protocol callback forwards every input to
every implementation — a STATIC over-approximation of a runtime dispatch, so an
unrelated `defimpl` that asks more about its argument raises the demand of every
forwarder that reaches the callback.

One job (`Job::DeriveInputDemand`) walks the forwarding cone, reads every fact
it consults, and runs the Kleene iteration from the cone's LOCAL masks — never
from another function's published demand, so there is no wait cycle.
`convergence_class_at` then keeps the element wherever demand reached the list's
shape, at every depth; a list demand never reached is freight and collapses to
one addressed class per position exactly as before.

`InputDemand` carries all three. The forwarded demand and the returned axis
shape the key collapse; the LOCAL mask is what closure-brand erasure reads
(fz-6gb), because "does a clause of THIS body test this slot" is a different
question from "does anything downstream read it", and a forwarder that only
transports a callable must still key one activation for two same-shape lambdas.

Three limits are known and stated rather than argued away. A `Whole` slot has NO
collapse, and forwarding can hand a `Whole` up from a callee that tests a
literal, so fz-y6w's termination argument does not cover such a slot
(measured: 344 rows over 174 functions gain a forwarding-introduced `Whole`).
The returned axis does not widen that exposure: it never produces a verbatim
slot, only an addressed class. The CALLABLE slot is still blind. And the
recursion-supplied subtraction reads SELF calls only: a mutually recursive pair
rebuilds across the cycle rather than inside one body, and a recursion routed
through a generated lambda (`00032_lambda_recursion`) is not local either, so
both still key their ascent -- one rung per function, never a product.

So the rule "an activation's published return may depend only on what its key
names" holds for every shape the keying laws state, and is NOT proven in
general. Two named gaps remain, both cost or missed cure rather than
unsoundness, because a key that names MORE than the return depends on is only
wasteful. Measured corpus-wide at fz-kdt.199 (604 fixtures, 475 backend dumps):
of the executables the axis adds on functions whose key count grew, 36 land on
a function that gains a distinct published return and 91 do not — the 91
dominated by `List.reduce_cont/3` (21), `List.reduce_while_cont/3` (18),
`Range.reduce_while_cont/6` (9) and `List.reduce_while_step/3` (6) minting
fz-kdt.182
`empty_list()`/`list(τ)` ascent rungs across a mutual cycle the self-only
subtraction cannot see (fz-kdt.213). And the axis rides fz-kdt.183's dispatch
edge set, so a reconstructed or projected forwarding argument still re-joins
two keys onto one published return (fz-kdt.214).

Termination is a theorem, not a property of lucky inputs. Three facts carry it:
numeric literal chains cannot exist (the lattice has no numeric singletons —
see [`set-theoretic-types`](set-theoretic-types.md)); atom chains are bounded
by the program's finite atom set; and structural deepening is cut by the
return join's widening operator (`ActivationMap::define_return`,
`RETURN_WIDENING_BUDGET`): past N strict ascents of one activation's return
within an epoch the growing spine collapses via `convergence_class`, past 2N
it tops out at `any`. Every widening that coarsens the stored value emits
`fz.compiler2.return_type.widened`, so widening on a real program is a
visible regression, never silent precision loss. The key ops
live in [`type-world`](type-world.md).

```text
fib(0,0,1), fib(1,0,1), fib(10,0,1), fib(20,0,1)
  n is a dispatch slot (matched 0,1); a,b are accumulators
  recursive -> a,b undemanded, keyed by convergence_class; n kept precise (already int —
  numeric literals are not types)
  one activation (root, fib, [int,int,int]); reachable clauses unioned -> int
```

## Not-computed is not `none`, and `none` is not `any`

Three states stay distinct, and conflating them poisons the fixpoint:

- **Not computed yet** — the callee's return EVIDENCE is absent
  (`world.activation_return` yields `None`). Absence never becomes a type: the
  walk's path results are `Option<Ty>` and an evidence-less path contributes
  the join identity (`jobs/semantic.rs`), while the caller's subscription to
  the `ReturnType` fact re-wakes it when evidence rises. At the settled
  fixpoint, still-absent evidence IS the fact "provably never returns" and
  only there converts to `none` (`CallTargetSummary::settled_return`,
  the materializer).
- **`none`** — a settled empty type: the value set is uninhabited (a callee that
  always diverges, or a call with an empty argument type). It stays `none`.
- **`any`** — a real top fact (an untracked value, a named-ref call), not a stand-in
  for missing proof.

Because evidence only ascends between ground shifts (the return store joins by
union; descent requires a rebased publisher — see
[`fact-engine`](fact-engine.md)), a transient low read can never freeze or
flap a caller's return: re-derivations join upward and equal joins are quiet.

### The ascent ladder, and where it may not climb

`list_element_type([])` is `none`, so `empty_list()` never converges with
`list(τ)`: a slot that KEEPS its element keys an accumulator's first call apart
from every later one. That pair is a RUNG; the ladder it climbs and the
duplicate executables it mints are both open defects (see the rung census
below for the population).

A rung can only appear on a slot one of the two axes names. A FREIGHT slot --
one neither names — collapses every list family reaching it to one addressed
class, so `[]` and `list(τ)` cannot key apart there, which is what bounds the
cost to one accumulator per function rather than a product over accumulators.
`compiler2_no_ascent_rung_sits_on_a_freight_slot_of_a_recursive_key` holds that
over five fixtures, on the same comparand the corpus sweep reads (the canonical
type body) but a BROADER relation: it asks the rung question of each slot
independently, so it reads 23 rung/slot findings where the sweep's whole-key
relation reads none on those five — up from the 8 fz-kdt.183 recorded, and the
fifteen added are on positions the returned axis now names: the reduce
families' accumulators key their seed apart from their ascent, a supplied
position the SELF-only subtraction cannot see across the cont↔step cycle
(fz-kdt.213). Zero of the 23 sit on freight, which is what the gate asserts.
The two populations differ by construction --
162 slot findings over 16 fixtures against 58 whole-key rungs over the same 16 --
so a number from one is not a number from the other.

Corpus census recipe: the corpus is every `.fz` under `fixtures2/` —
`ls fixtures2/*.fz fixtures2/behavior/*.fz`, 605 files at fz-kdt.199, of which
475 reach a backend dump. Take the list from the tree each time rather than
from a saved file; the list this recipe was last written against had drifted
eight fixtures behind it, which is enough to change a mover count. Dump every
fixture with
`fz2 interp --dump backend=<out>/<name>.canon <fixture>`, then over the `key
<label>[<cols>] need=<need>` lines group by `(label, arity)` and count the
keys whose WHOLE column vector is a sibling's with one or more list positions
EMPTIED (`empty_list()` where the sibling has `list(τ)`), at any structural
depth -- every column must stand in that relation, or the pair is two unrelated
specializations rather than one rung.
`non_empty_list(τ)` is disjoint from `empty_list()`, so that pair is two clause
specializations rather than a rung. Last measured at fz-kdt.183: 58 rungs over 16
fixtures, up from 53 over 15 — six added (`Map.to_list/4` slot 3 with
`Map.reverse/2` slot 0, `Range.slice_from/5` slot 4 with `Range.reverse/2`
slot 0, and `Kernel.dbg/1` with `Kernel.fz_dbg_value/1` on
`00277_enum_tier0_fixture`), one retired (`Range.reduce/5` slot 3), and none of
them on a freight slot.

## Proof gates

```text
cargo test --lib compiler2::drive_test::compiler2_quicksort_root_closes_with_a_finite_recursive_frontier
cargo test --lib compiler2::drive_test::compiler2_recursive_keying_sees_recursion_through_generated_lambdas
cargo test --lib compiler2::drive_test::compiler2_semantic_analysis_derives_reachable_call_edges_and_tuple_return_need
cargo test --lib compiler2::drive_test::compiler2_input_demand_keys_one_activation_where_nothing_demands_the_slot
cargo test --lib compiler2::drive_test::compiler2_no_ascent_rung_sits_on_a_freight_slot_of_a_recursive_key
cargo test --lib compiler2::types     # refine_widen / convergence_class ladders
cargo test --test fixture_matrix -- --test-threads=1 users_key_apart_by_element
cargo test --test fixture_matrix -- --test-threads=1 returned_tuple_field_keys_its_users_apart
```
