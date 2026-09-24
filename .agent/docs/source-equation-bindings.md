# Source equations: the recursive binding boundary

This is the paper contract for fz-kdt.98.3.17.10, checked against `c5cde5833`.
It records an unresolved design gate, not an implemented inference engine.
The source equation now retains its lowered body and complete invocations.
Calls still create activations before learning their results.

## Definitions, substitutions, and sharing

```elixir
def first(x, y), do: x
def apply(f, x), do: f.(x)
def twice(f, x), do: f.(f.(x))
```

Their equations are `First(a,b)=a`, `Apply(f,a)=Invoke(f,a)`, and
`Twice(f,a)=Invoke(f,Invoke(f,a))`. Each use supplies a substitution; it does
not rewrite the definition. Thus int, float, and empty-list uses of first
retain their separate results. Changing its unused second argument does not
create an observed interface. An absent definition leaves the answer pending.
It supplies neither `any` nor `none`.

Ignoring a parameter does not erase strict argument evaluation:
`first(1, spin())` cannot return, and an unresolved argument producer keeps
the call pending. Successful execution prerequisites gate the substitution.

Two compatible callbacks may share apply's invocation interface and transfer
work. Their exact targets, captures, arguments, and results must still travel
together. For twice, the second invocation uses the first invocation's result
under the **same substitution**. Keeping two call-site IDs is necessary but
does not itself preserve that association.

## Finite addresses do not prove finite bindings

The proposed destination-slot addresses solve one problem: a growing type
need not mint a new graph location at every iteration. They do not bound the
number of substitutions stored there, or prove that merging them is sound.

The simple cases have different reasons for closing:

| Source relationship | Paper answer and reason |
| --- | --- |
| `spin() = spin()` | A registered, closed `R=R` has no returning base: `none`. A missing definition is still pending. |
| `loop(f,x) = loop(fn y -> f.(y) end,x)` | `R(a,b)=R(Wrap(a),b)`. Neither input is observed and no path returns. The closed return reduces to `R=R`; parameters remain alphas. This is substitution, not unification `a=Wrap(a)`. |
| `(x,y) -> (y,x)` from `(int,:tag)` | Exactly two row states, `(int,:tag)` and `(:tag,int)`. The permutation closes after two applications. |
| One growing accumulator | `A=seed | {A}` is a structural recursive equation, representable by the existing regular-type solver. |
| Enum's reducer adapter | It captures the reducer once and forwards that capture through the helper cycle. It does not wrap its predecessor on each iteration. |

These arguments do not establish the general wrapper case. Compare
`Wrap(f)(x)=f(x)` with `Wrap(f)(x)=f({x})`: the latter changes the invocation's
argument on every wrapping. Even the former's invocation equivalence does not
erase observable callable identity or escape obligations.

### A concrete correlation counterexample

```elixir
def aligned(:left, :right), do: :ok
def aligned({x}, {y}), do: aligned(x, y)
def aligned(_x, _y), do: :crossed

def grow(0, x, y), do: aligned(x, y)
def grow(n, x, y), do: grow(n - 1, {x}, {y})
def main(), do: dbg(grow(2, :left, :right))
```

Under the compiler's integer abstraction, the arriving pairs have arbitrary
but **equal** wrapping depths. Their relationship is

```text
P = {(:left,:right)} | map((x,y) -> ({x},{y}), P)
```

Splitting this into `X=:left | {X}` and `Y=:right | {Y}`, then forming
`(X,Y)`, invents pairs such as `({:left},:right)`. A row ID around these two
marginal types cannot recover the lost relationship. The exact result of
aligned on P is only `:ok`; unequal-depth inputs must still reach `:crossed`.

The required joint restriction has a small paper solution. The seed selects
the first aligned clause. The recursive alternative selects the second; its
two projections come from the same recursive row and restore P. Neither
alternative reaches the fallback. Consequently `Aligned(P)=:ok | Aligned(P)`
and its least return is `:ok`. This product has one recurring aligned/P state,
plus the existing finite clause/proof positions. Expanding all tuple depths
or separately solving the columns is unnecessary.

This proves a finite product for this witness. It does not prove that every
composition of source restrictions and substitutions has a finite quotient.
The implementation must specify which residual products are equal; neither
finite source syntax nor the regular interner supplies that proof.

### Parser restrictions are also relationships

For the ticket's reduced parser, preserve the tuple/tag test while its tail
remains symbolic:

```text
V(L) = {:ok,tail(L)} on :t | A(tail(L)) on :open
A(L) = :done on :close | I(V(L)) on fallback
I(Y) = A(field1(restrict(Y, tuple2 and field0=:ok)))
```

L abbreviates the token-list family, not one shared producer identity.
Restricting V exposes its explicit tuple; the alias through A rejects `:done`
and has no other tuple-producing base. The tail's producer and strict
prerequisites remain attached to that alternative. A back-edge must preserve
the same ordered bound producer relationships and complete restriction and
substitution state. Equal source-port IDs alone do not establish that equality.
Defining its finite normalization is the outstanding obligation; a completed
concrete V type is not a prerequisite to admitting the restriction.

## What the existing code loses

The callee activation admission during a call is
`jobs::semantic::prepare_function_call`.
Its callers already hold the function reference, ordered inputs, and closure
capture prefix. Replacing that helper alone would leave activation ownership
in the evaluator frame, CallSiteKey, CallEmission, return subscriptions,
contribution derivations, component membership, and solver Term/Bindings.

There are three distinct losses to remove together:

1. `evaluate_activation` evaluates input rows separately, then merges their
   value observations, reachability, calls, and return evidence into one
   ActivationAnalysis. The row-to-result association disappears there.
2. `return_component::Bindings::slots` and `gather` collect each recursive
   parameter independently. The solve reconstructs rows from solved columns;
   tuple lowering also uses independent child references. This cannot retain
   the synchronized P relationship above. External evidence and call-summary
   merging also have columnwise projections.
3. `key_inputs_for_call` leaves capture-prefix inputs unchanged. Its existing
   argument normalization therefore cannot bound recursively nested capture
   types. Captures need bound source references as well as current Ty evidence.

`ActivationInputAlternatives::rebuild` has an additional eight-row budget that
collapses rows columnwise. It is not a suitable exact binding authority.
`Sigma` substitutes type variables; `types::CallableApplication` applies
ground literal-free arrow sets. Neither supplies source binding/control or
joint recursive restrictions. Reuse the existing source graph, evaluator,
return solver, dispatch proof semantics, and contribution ledger.

## The next coherent implementation

First establish **whole-row substitution and joint restriction in the existing
solver**. An incoming edge binds ordered capture/argument producer references
together. Projection keeps its parent-row relationship. A multioperand proof
must consume alternatives from that same row. Retain the finite source
substitution rather than allocating a row for every unfolded history.
The first production witness must preserve evaluator rows before aggregation
and change their solver consumption together: a new row record without that
consumer would leave the existing loss in place.

Use rotate and synchronized growth to establish the normalization and product
bound, with mismatched inputs as a negative control. Then cover the parser,
reducer capture cycle, and observable wrapper distinctions. The general
admission law remains open until those products have a justified finite
representation; storing their source equations is only representation work.

With that law established, move semantic ownership coherently:

1. Retain each evaluator row's inputs, restrictions, observations, reached
   invocations, and result together before deriving aggregate views.
2. Address those bindings and their pending results through source ports;
   move call edges, input contributions, caller/component relationships, and
   Term/Bindings together. Keep exact capture producers off sharing keys.
3. Make `prepare_function_call`, root seeding, and latent callable seeding
   request those bindings. Established interfaces then group executable
   activations and feed the existing typed transport.
4. Remove activation-frontier inference and activation-snapshot gathering
   from the migrated path. No first-only evaluator, preflight, or fallback.

The work contract is causal, not a guessed scheduler count: one installed
source definition; each distinct transfer operand/proof row evaluated when
its dependencies change; a second compatible callback adds its own analysis
and target wiring without another apply-body walk or unchanged transfer.
For the closed unused loop, wrapper depth adds no demanded callback interface
or inference state. Pending external facts remain subscriptions, not `none`.

The acceptance gates are independent first results (including definition
arrival/replacement and strict dead/pending arguments), existing apply
work/ABI tests, and twice with different
intermediate tags in its two bindings. Give the callbacks explicit wrong-tag
arms so cross-binding results are observable. Measure work at the surviving
evaluator: deleting ActivationKey telemetry must not fake a zero-work pass.

## Measured checkpoint

The ticket's `binding-law` attachments contain the exact FZ probes, commands,
binary hash, trace summaries, and compressed raw telemetry. At `c5cde5833`,
rotate builds and its AOT executable prints `{:tag, 1}`. The other three
compiles exceed a 12-second process cutoff with telemetry **and** without it.
These interrupted traces are lower bounds on work, not completed runs or
proofs of nontermination:

| Probe | Relevant work before cutoff |
| --- | --- |
| Synchronized growth | One grow owner, 135 grow walks; 16 row-budget collapses. Types keep gaining tuple layers despite stable ownership. |
| Unused wrapper loop | 277 loop owners and 277 walks; no callback invocation is needed by its paper equation. |
| Observable wrapper | 201 iterate owners, 406 iterate walks, and 201 wrap owners/walks. |

Direct equal-depth and unequal-depth aligned controls build and execute as
`:ok` and `:crossed`, respectively. The explicitly unrolled two-wrapper control
builds and returns `{{:seed}}`. These separate the required behavior from the
recursive admission failure.

The existing compatible-apply RED still measures three versus six body walks
for one versus two callbacks. No inference ownership or compiler semantics
changed in this investigation. The ticket's review gate is reached: the
missing capability is now a specific joint-row solver operation, not an
unexplained new application identity.
