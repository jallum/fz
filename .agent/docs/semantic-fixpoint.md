# Semantic Fixpoint

Compiler2 semantic facts are local evidence about typed, reachable activations
and executable demand. Artifact readiness is now pulled by product keys; the
semantic side still publishes facts with two readiness levels:

- `Current(fact)`: the fact is present and may be read by iterative semantic
  work.
- `Settled(fact)`: every current publisher is clean, so downstream work may
  consume it as complete for now.

`SeedRoot`, `SeedActivation`, and `AnalyzeActivation` shape those local facts.
There is no root semantic-closure seal: the `SealSemanticClosure` job and its
`SemanticClosed(root)`/`SemanticReady(root)` facts were deleted (`fz-go4.18.4`).
Artifact readiness is pulled entirely by product keys.

## What an activation is today

An **activation** is `ActivationKey { root, function, arrow: Ty }`: one
function specialized for one root at one canonical input shape. The canonical
inputs are the parameter side of an interned arrow type (`arrow_params`); the
result side is a `none()` sentinel today and becomes the addressed result `r0`
in fz-hwn.27.6. Read the inputs with `key.inputs(types)` / `key.input_len(types)`
and build a key from raw inputs with `ActivationKey::from_inputs`. Demand and
evidence are separate facts:

```text
Activation(key)       # demand / existence (multi-publisher; callers claim it)
ActivationInputs(key) # joined caller evidence (cumulative; per-publisher
                      # entries join by union; AnalyzeActivation publishers
                      # preserve their prior frontier within an epoch)
```

`world.activation_inputs(key)` reads the joined evidence once its fact is
live. A clause whose params outnumber the joined evidence yields no evidence
that round — incomplete inputs never default to a type.

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
values, mailbox binds, and the root's public inputs. "Unresolvable" is the
narrow case — a closure call whose callee type carries *no* matching
closure-shaped clause. A callee that does name a concrete closure target whose
analysis is merely pending this round is absence of evidence (`None`), not a
dynamic edge: `resolve_closure_call` returns `None` and stays subscribed rather
than earning `any`, because `ReturnType` is cumulative and a stale `any` unioned
in early would never retract once the target settled to its real type. Published
outputs:

```text
ActivationAnalyzed(a)
ReturnType(a)
CallSiteTargets(callsite)
CallSiteSummary(callsite)
Activation(callee_key)
Executable(callee_key, need)
```

That publication is how executable demand grows. No separate sweep discovers
reachable callees. `ActivationInputs(a)` is cumulative for semantic-analysis
publishers: if an `AnalyzeActivation` rerun temporarily stops seeing a callsite,
the publisher keeps its prior activation-input frontier and only adds/widens new
entries. Source/root publishers still use ordinary replacement so real external
changes can withdraw stale contributions. This keeps fixpoint evidence from
descending just because an intermediate clause-reachability approximation
changed. The joined aggregate is compared by type equivalence, not raw `Ty`
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
retraction. Settled demand retracts only on an epoch event — materialization
resolving a call edge outside the settled callee inventory re-keys and
re-settles the affected cone.

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
- `AnalyzeActivation(a)` owns `ActivationAnalyzed(a)`, `ReturnType(a)`,
  `CallSiteTargets(...)`, `CallSiteSummary(...)`, and any callee demand facts it
  publishes.
- Product artifact producers own request-local `ProductValue`s in
  `PullSession`, not scheduler facts. They wait on settled semantic facts by
  exact key and must not publish activation facts or schedule follow-up jobs.

## Module facts at the walk's gates (fz-rh2.17.5.9)

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
