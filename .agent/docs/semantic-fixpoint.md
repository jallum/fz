# Semantic Fixpoint

Compiler2 semantic facts are local evidence about typed, reachable activations
and executable demand. Artifact readiness is now pulled by product keys; the
semantic side still publishes facts with two readiness levels:

- `Current(fact)`: the fact is present and may be read by iterative semantic
  work.
- `Settled(fact)`: every current publisher is clean, so downstream work may
  consume it as complete for now.

`SeedRoot`, `SeedActivation`, and `AnalyzeActivation` shape those local facts.
Artifact readiness is pulled entirely by product keys; no root-wide inventory
fact stands between local semantic settlement and the requesting product.

## What an activation is today

An **activation** is `ActivationKey { root, function, arrow: Ty }`: one
function specialized for one root at one canonical input shape. The canonical
inputs are the parameter side of an interned arrow type (`arrow_params`); the
result side is the addressed result var `r0` — "return not yet known", an
unknown to resolve, never a `none()` fallback. Read the inputs with
`key.inputs(types)` / `key.input_len(types)`
and build a key from raw inputs with `ActivationKey::from_inputs`. Demand and
evidence are separate facts:

```text
Activation(key)       # demand / existence (multi-publisher; callers claim it)
ActivationInputs(key) # correlated caller evidence (cumulative; per-publisher
                      # entries join as a canonical set of whole rows —
                      # ActivationInputAlternatives; AnalyzeActivation
                      # publishers preserve their prior frontier within an
                      # epoch)
```

Each publication is one `ActivationInputRow`: columns that arrived together
from one call analysis and may only be read together. Rows join by set
insertion with whole-row equivalence dedup — never by column-wise union, which
would invent Cartesian input combinations (fz-9i4.7.10.2). Past
`ACTIVATION_INPUT_ROW_BUDGET` rows the set widens to its single column-wise
joined row, so termination stays a theorem.

`world.activation_input_alternatives(key)` reads the rows once the fact is
live; `world.activation_inputs_joined(key)` reads the column-wise joined
projection, which is correlation-blind by construction and only for consumers
whose question is genuinely per-column (transport lane typing) after semantic
decisions. A clause whose params outnumber a row's evidence yields no evidence
that round — incomplete inputs never default to a type.

Clause reachability is a pure compiler2 calculation over the entry
`PatternDispatchPlan`, the shared `Types`, and one input row at a time —
`AnalyzeActivation` dispatches and analyzes each row independently and merges
only post-analysis results (reachable clauses by set union, failure by OR,
return evidence by join, call emissions by coalescing). Branch
states retain only root input `Ty` values and are memoized by graph node plus
root row. Edge proofs refine those roots; projected subjects are always derived
again through `PatternSubjectRef`, so no independently cached field/head type
can lose correlation or leak one list position into another. The result names
sorted reachable outcomes and whether graph failure remains reachable; it does
not publish a fact or consult `World`.

## Executable demand is local semantic output

`AnalyzeActivation(a)` follows `a`'s reachable clauses, infers value and return
types, and publishes semantic outputs. Path results are
`Option<Ty>`: `None` means "no evidence on this path yet" — a pending callee
(`prepare_function_call` returns the callee's return evidence as-is and keeps
the subscription that re-wakes the caller; no waits on returns, so mutual
recursion cannot deadlock), a halt, a dead arm, or a read of a value whose
defining path has produced nothing. All of these are the join's identity.
Availability is enforced per READ (`value_ty` returns `Option<Ty>`; a step
with an absent operand defines nothing), not per entry: an entry's capture
list is the transitive free-value closure of its children, so gating a whole
entry on it would suppress siblings of the one starved path. The empty type
`none` only ever arrives as a proven fact, so the dead-call checks
(`resolve_direct_call`'s empty-argument drop) are true statements, and `any`
appears only where it is earned: provider boundaries, unresolvable callable
values, mailbox binds, and the root's public inputs.

`resolve_closure_call` sorts every callee into exactly three answers. The line
between the first two is INHABITATION; the line between the last two is
GROUNDNESS. Collapsing any pair of them is a known defect class.

- **Dead — the empty type.** Nothing can arrive in the slot, so the call never
  happens. `callee_has_no_inhabitants` is the predicate: the proven-empty type,
  or a *value template* (`Types::is_value_template` — a bare type variable,
  which has no runtime representation). An activation keyed with a bare variable
  at a callee slot is a specialization for an argument no caller can ever supply
  (fz-hwn.23), so its call is unreachable and the Kleene reading of a call that
  never happens is `none`. That is evidence, not absence.
- **Absent — `None`, subscription retained.** The call has no evidence *yet*.
  Two callees look unresolvable and are not: one that names a concrete closure
  target whose analysis is merely pending this round, and one whose type still
  carries type VARIABLES — the slot has not been instantiated. A callable that
  merely carries a variable, `(int) -> a`, is a real pointer at runtime; only a
  BARE variable is uninhabitable.
- **A dynamic edge — earned `any`.** The narrow case: a callee type that is
  GROUND and carries *no* matching closure-shaped clause, so at runtime it
  really could be anything. `callee_is_a_dynamic_edge` is the predicate, and it
  is `!has_vars`.

The absent/earned line matters because `ReturnType` and the value-type join are
cumulative: a stale `any` unioned in early never retracts once the slot grounds,
and the callsite ends up holding two disagreeing facts — a precisely-resolved
`CallSiteSummary` and an `any` value type. The fz-f98.14.11 artifact guard is
the detector that makes that disagreement fatal instead of silent.

A dead callsite publishes no summary at all, and materialization reads that
absence with the same Kleene rule `CallTargetSummary::settled_return` uses:
behind the settled gate `materialize_closure_call_edge` lowers a summary-less
closure call as `CallReturnFlow::NoReturn` over the empty type, because every
`ClosureCall` tail needs a return flow and a call that never happens never
returns. Published outputs:

```text
ActivationAnalyzed(a)
ReturnType(a)
CallSiteTargets(callsite)
CallSiteSummary(callsite)
Activation(callee_key)
Executable(callee_key, need)
```

That publication is how executable demand grows. No separate sweep discovers
reachable callees. Publishing `Activation(callee_key)` is also the record site
for `World`'s activation frontier: `World::complete_job` folds the key into
`activation_frontier` unless `ActivationAnalyzed(callee_key)` has already
settled, and `World::demand_activation_frontier_analyses` — the non-root
analogue of `demand_root_entry_analyses` — demands the callee's own
`AnalyzeActivation` the next time the agenda drains. `analyze_activation`
itself never schedules the callee directly: `prepare_function_call` only
`reads` the callee's `ReturnType` (so mutual recursion cannot deadlock), so
nothing about discovering a callee blocks on its analysis, and the frontier is
the only thing that ignites a callee's first analysis pass.
`ActivationInputs(a)` is cumulative for semantic-analysis
publishers: if an `AnalyzeActivation` rerun temporarily stops seeing a callsite,
the publisher keeps its prior activation-input frontier and only adds/widens new
entries. Source/root publishers still use ordinary replacement so real external
changes can withdraw stale contributions. The callsite CLAIMS ride a
stricter rule than the inputs do: a non-rebased conclusion keeps every
`Activation`, `CallSiteSummary` and `CallSiteTargets` it did not re-emit, and
only a rebased one — whose ground actually shifted — withdraws. The
`ActivationInputs` contributions themselves never withdraw, rebase or not
(`preserve_frontier` is unconditional for `AnalyzeActivation`, so after a
rebased withdrawal of a claim the input evidence that fed it stays published
and joined — see fz-kdt.64 for the recorded asymmetry) (`World::preserved_analysis_claims`;
[`fact-engine`](fact-engine.md), *Absence is bottom; rebasing is the narrowing
path*). This keeps fixpoint evidence from descending just because an
intermediate clause-reachability approximation changed. The row set is compared by per-column type equivalence, not raw `Ty`
handle equality, so representative-only changes do not dirty the scheduler.
`ReturnType(a)` is a CUMULATIVE claim: the store
(`ActivationMap::define_return`) joins each round's evidence by union (which
preserves closure identities), reports `changed=false` for equal joins, and
only a rebased publisher replaces — within an epoch the return can only
ascend, which is what makes the iteration converge on every schedule. Past a per-epoch
budget of strict ascents (`RETURN_WIDENING_BUDGET`, a total since the last
rebase — not a consecutive-ascent delay, which spurious quiet wakes could
starve) the join widens the growing spine (`convergence_class`, then `any`),
emitting `fz.compiler2.return_type.widened` only when the operator actually
coarsened the stored value; corpus programs converge in a few rungs and never
meet it. `CallSiteSummary` snapshots carry
`return_ty: Option<Ty>` — honest mid-ascent records whose `None` reads, behind
the settled gate, as "provably never returns" (`settled_return`).

`CallSiteTargets(a, callsite)` is the membership signal: each edge carries only
callee identity plus the selected activation key, so surface/return type ascents
do not bump the revision that reachability readers subscribe to.
`CallSiteSummary(a, callsite)` remains the semantic call boundary fact. Its
target list is keyed by callee identity: repeated observations of the same
callee join their surface inputs and return evidence before artifact/native sees
the fact. The summary does not synthesize a new activation key while joining;
activation demand remains owned by the separate `Activation(callee_key)`
publications from local semantic analysis. Downstream products consume that
already-joined boundary surface instead of rediscovering or deduplicating
semantic targets.

## Product waits replace root semantic closure

The product path consumes settled facts directly. For one executable `E`,
`MaterializedExecutable(E)` waits on settled `ActivationAnalyzed(E.activation)`,
settled `ReturnType(E.activation)`, settled callsite summaries for that local
activation, `RuntimeDemand(E)`, `OutgoingInputEdges(E)`, and the transport
positions required by the local body. It returns `PullWait::Fact` or
`PullWait::Product` for those exact prerequisites.

The root product waits on `RootEntry(root)`, `Recursive(entry)`, and
`DispatchMask(entry)` only so it can key the entry executable, then asks for
`BackendExecutable(entry)`. Additional executables enter the request through
symbolic call edges and callable entries recorded by already demanded products.
There is no `SemanticClosed(root)` prerequisite on the product path and no
root-wide semantic scan that decides artifact membership.

`RuntimeDemand(E)` is a product that settles its whole demand SCC inside one
producer, the same pattern `ExecutableEffects` uses. Demand dependencies run
both ways along every call edge (callers read callee input demands; callee
return demands join caller contributions), so the demand SCC containing `E` is
`E`'s call cone, discovered from settled facts only: `CallSiteSummary` direct
targets, type-derived callable-flow resolutions, and any callee set a previous
epoch recorded. The producer runs a bottom-start monotone Kleene ascent over
the whole cone (return demands join up edges, input demands flow down edges,
`ShapeDemand::join` per round) until nothing changes, then memoizes the settled
fixpoint for every member at once. Members no contributor names at the fixpoint
(the entry, delivery-reached continuations, escaped closure bodies) get the
whole-by-need bootstrap at settle time — absence is a distinct settled cell.
No mid-ascent value is ever observable outside the producer: there is no
active-SCC seed, no consumed-return contribution floor, and no in-flight
retraction. Settled demand retracts when materialization resolves a call edge
outside the settled callee inventory, which re-keys and
re-settles the affected cone.

Exact products keep retries proportional to movement without changing the
iterates. `ExecutableFacts(E)` owns the activation analysis, lowered body,
entry dispatch, and callsite summaries consumed for one executable; exact
fact movement displaces that product and its readers. Inside the ascent, a
round re-derives only the members whose reads moved: a member reads its own joined
return demand, its cone-edge targets' demands, and (for a lambda producer)
every executable of the produced function — the two reverse indexes over
exactly those reads mark the dirty set when a member's iterate moves, and
every skipped member would have derived an identical value. A new world-fact
read must enter the producing product's dependencies, and a new mutable-round
read must extend the reverse indexes.

Publication closes the stale-caller window: when a settling cone's
contributions grow the joined return demand of an executable settled earlier
OUTSIDE the cone, that external's memo is displaced while the cone's members
were derived against its pre-growth input demands. The producer refuses to
memoize such a cone; it re-collects (the displaced external is memo-less and
joins as a member through the edge that carried the contribution) and settles
the grown group together. Each re-cycle strictly grows the member set —
enforced as a hard assertion — so the loop terminates within the finite
demanded universe. The per-cone ascent round budget is likewise a hard failure
in every build (a non-monotone regression fails loudly instead of hanging).

## Current vs settled is the key boundary

Semantic jobs iterate on **current** evidence. Product artifact producers consume
only **settled** fact evidence.

Examples:

```text
AnalyzeActivation(a)      reads Current(ReturnType(callee))
MaterializedExecutable(E) waits on Settled(ReturnType(a))
AbiExecutable(E)          waits on Product(MaterializedExecutable(E))
BackendExecutable(E)      waits on Product(AbiExecutable(E))
```

This is the important line in the current design: type values are not used to
encode readiness. `any` and `none` are semantic values. Fact readiness lives in
the scheduler.

## How recursive convergence works right now

`canonical_activation_key(function, raw_inputs)` still decides activation
identity. For recursive functions it collapses non-dispatch inputs by
`convergence_class`, using the `Recursive(fn)` and `DispatchMask(fn)` facts to
decide which slots may balloon.
List-family convergence is intentionally coarse at the key: `[]`, `[t]`, and
the joined `[] | [t]` shape share one recursive identity, and a
`ListShape(elem_demand)` dispatch slot keeps demanded element information while
converging the shape. The element is derived from the whole list-family
descriptor, not only from a pure-list singleton, so already-joined list evidence
does not split recursive keys. The precise caller evidence remains in
`ActivationInputs(key)`, so clause reachability is decided by evidence, not by
downstream code rebuilding a more precise key.

So today:

```text
key.input     = canonicalized identity and current body input
ReturnType(a) = current return approximation
Settled(...)  = scheduler-level proof that downstream work may rely on it
```

That is not yet the final semantic shape, but it is the current code shape and
the basis for the remaining type-system tickets.

## Ownership boundaries

- `SeedRoot` owns `RootEntry(root)` and seeds the entry `Activation` and
  `Executable` demand facts.
- `SeedActivation(a)` owns `Activation(a)`/`ActivationInputs(a)` for the
  activations nothing else describes: a root's own entry, or one the
  runtime-demand frontier minted from a callable surface which no analysis
  walked and no caller claimed. (A root entry thus has two possible minters
  today, `SeedRoot` and `SeedActivation`, whose reconstructions agree -- the
  measured 4 lib-suite cases -- see the fz-kdt ticket on collapsing that to
  one producer.) It reconstructs the
  input row from the key's own arrow, so `World::demand_fact_producer` routes
  a demand to it only while `ActivationInputs(a)` has no publisher
  (`World::seed_activation_producer`). A key a caller discovered is the
  caller's to publish and to withdraw.
- `AnalyzeActivation(a)` owns `ActivationAnalyzed(a)`, `ReturnType(a)`,
  `CallSiteTargets(...)`, `CallSiteSummary(...)`, and any callee demand facts it
  publishes; it withdraws the callsite ones only on a rebased conclusion. It
  schedules no follow-up job of its own: publishing `Activation(callee_key)` is
  what feeds `World`'s activation frontier. When its OWN `Activation(a)` is
  absent -- nothing claims `a` -- it concludes on the recorded read and
  re-lists its standing claims, rather than waiting on a producer that no
  longer exists for it.
- `World` owns the `activation_frontier` standing-demand set alongside the
  scheduler it wraps. `World::complete_job` is its sole maintenance site
  (insert on an `Activation(key)` publish, retire once `ActivationAnalyzed(key)`
  settles or once `AnalyzeActivation(key)` has run at all), and
  `World::demand_activation_frontier_analyses` is its sole reader.
- Product artifact producers own request-local `ProductValue`s in
  `PullSession`, not scheduler facts. They wait on settled semantic facts by
  exact key and must not publish activation facts or schedule follow-up jobs.

## Module facts at the walk's gates

`ModuleDefined(m)` means m's body has been scoped and published;
`ModuleInterface(m)` means m's exported callable surface is available. The
semantic walk consumes NO `ModuleInterface` facts, and that is correct:
names resolve during body lowering (which does consume the interface), so by
the time the walk runs, every callee is already a `FunctionId`. The walk's
remaining `ModuleDefined` gates are all body readiness or demand
bootstrapping, each carrying its verdict in place: the protocol gate exists
to make `DefineModule(protocol)` publish `ProtocolDispatch`; the
runtime-module gate loads defimpls that registration alone implies; the
unresolved-function gate produces a held `FunctionId`'s definition. Protocol
call targets gate per FUNCTION (the same `wait_for_unresolved_function_module`
the direct-call path uses) — the old `ModuleDefined(owner_module)` wait
re-serialized every protocol call behind whole-module scoping and was
removed as over-waiting.
