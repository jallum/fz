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
insertion — never by column-wise union, which would invent Cartesian input
combinations (fz-9i4.7.10.2). Two compressions run at the insertion point
(`ActivationInputAlternatives::insert_row`), and they are different
judgements:

Before that join, one `AnalyzeActivation` conclusion emits each exact
`(ActivationKey, input row)` contribution once. Several reached paths may
observe the same callee evidence, but they are one publisher making one claim;
first-observed order is retained. This boundary compares interned type identity
only. Distinct rows still reach the antichain below, and another analysis
conclusion has its own contribution set, so neither evidence nor publisher
ownership is collapsed.

- whole-row EQUIVALENCE (pointwise `Types::is_equivalent`): the incoming row
  says exactly what a standing row says;
- whole-row DOMINANCE (`Types::row_dominates`, fz-kdt.106): a dominated
  incoming row is not inserted, and standing rows dominated by the incoming
  one leave with its landing.

Dominance exists because a caller's ascent is a CHAIN, not a set of
alternatives: `conclude_preserving_frontier` joins every superseded conclusion
in and nothing takes it out, so a widening column deposits one row per rung.
`Types::row_column_dominates` is deliberately narrower than `is_subtype` — it
also requires equal free-var sets and containment of the closure-literal arrow
SHAPES, because `types::emptiness::func_clause_empty` decides a closure-literal
arrow from `fn_id` and captures alone and would otherwise let a template row
absorb its own ground instances. The relation's own doc records that its
termination argument is empirical, not proven.

Past `ACTIVATION_INPUT_ROW_BUDGET` rows the set still widens to its single
column-wise joined row, so termination stays a theorem. A fire now means
genuine correlation width, and `ExecutionContext::complete_job` reports each
one as `fz.compiler2.activation_inputs.budget_collapsed` carrying the count.
`correlated_input_rows_never_reach_the_widening_budget_on_the_lenses` GATES
four fixtures at zero collapses; a sweep of all 577 `fixtures2` fixtures at
fz-kdt.106 also found zero, but that number is a point-in-time measurement, not
something the suite holds.

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

The ARGUMENT decides which specialization a closure call reaches, and nothing
narrows it. A closure clause's arrow parameters are EVIDENCE — the surface that
lambda has already been analyzed at — not a contract the caller is checked
against, so intersecting the observed argument with them is not a refinement
but a loss: it names a specialization whose domain does not contain the value.
A fold's reducer is minted beside the initial accumulator and keeps that arrow,
so the intersection clamped every later call back onto the initial
specialization: the accumulator's ascent stopped one rung short, the grown
accumulator got no specialization and no construction member, and the values on
that rung reached a body that never named them (fz-kdt.132 — the whole
268-escape surface-membership census). A declared `@spec` return reaches the
same seam through `refine_call_return`, and it only ever OFFERS one the
calculator called a fact: a contract clause whose result names a
partially-joined variable answers `Underconstrained` and publishes no result at
all (see [`addressed-arrow`](addressed-arrow.md)), so the join a `[]`-seeded
fold observes is never met with the seed's own type. `refine_observed_return`
refuses the
kindred narrowing on the return side only where the arrow's type is a strict
subtype of the observed; the argument-side rule here is UNCONDITIONAL -- the
arrow's parameters never refine an observed argument -- which is the stronger
form the evidence-not-contract law implies, not a mirror of the return rule.
Declared `@spec` contracts still refine the surface, in
`apply_function_contract`, where the surface is also enforced; a declared
arrow's DOMAIN on a higher-order parameter no longer narrows a closure call's
argument (only the enclosing spec's own inputs do) -- measured
behaviour-neutral corpus-wide.

The absent/earned line matters because `ReturnType` and the value-type join are
cumulative: a stale `any` unioned in early never retracts once the slot grounds,
and the callsite ends up holding two disagreeing facts — a precisely-resolved
`CallSiteSummary` and an `any` value type. The fz-f98.14.11 artifact guard is
the detector that makes that disagreement fatal instead of silent.

A declared bound is one way that stale `any` used to be manufactured, and
fz-kdt.120 closed it. `close_bounds` fills a variable the walk observed NOWHERE
from its declaration, and the fz-f98.16 empty-list cleaner turned an OBSERVED
variable into an unobserved one by deleting its `[]` binding — so at an early
revision, while a fold's accumulator was still `[]`, `@spec dbg(t) :: t when
t: any` answered `any`, that `any` joined into the callsite's cumulative return,
and it never retracted once the accumulator grew. Fourteen corpus fixtures
published a `return fp[any] any` this way and twelve of those are `main/0`
itself, `00032_lambda_recursion` among them, where the same dump typed the
returned value `fp[L] list(int)` two lines above. With the cleaner gone the
contract answers `[]` at that revision and `list(int)` at the next, and the two
facts agree.

A call to a named function needs two things about the CALLEE before it can
resolve: the `FunctionContract` that refines the surface (only for a function
that declares one — `World::function_declares_contract`) and the facts its
activation key is built from (`Recursive`, `InputDemand`, via
`World::require_activation_key_facts`). `require_callee_prerequisites`
registers both in one pass at each of the three resolve sites, before either
is consumed, so a caller that holds neither blocks once rather than a rung at
a time ([`fact-engine`](fact-engine.md), *One block per prerequisite set*).
`refine_function_call_surface` is then pure contract APPLICATION and
`prepare_function_call` pure keying: neither can block. A provider boundary
names no compiler2 activation, so it asks for the contract alone; the
boundary test is contract-independent and runs before the ask.

Every callsite the walk REACHES publishes its edge, resolved or not
(`CallSiteResolution`, semantic.rs). Three answers, three representations:

- **no fact** — the call never happens. The walk never reached the callsite,
  or it proved the call dead (an uninhabited callee, a proven-empty argument).
- **`Unresolved`** — the walk reached a live call and can name no target yet.
  This is NOT a provider boundary and NOT an empty target list; it is the
  lattice bottom, so `CallSiteMap`/`CallSiteTargetsMap` never let it overwrite
  a resolved answer and re-emitting it moves no revision. A
  permanently-`Unresolved` edge on a COMPILING program is a standing state
  since fz-kdt.130: a mailbox-delivered callable's callsite settles with no
  summary at all (measured: five such callsites across the two mailbox
  fixtures, behind the settled gate, all three doors correct) — and the
  carrier rule below is exactly what lowers that population as live indirect
  calls instead of misreading the absent evidence as a dead call.
- **`Resolved`** — the targets. A provider-boundary target is a resolved edge
  whose `CallTargetEdge::activation` is `None`, because a boundary names no
  compiler2 activation.

Because the walk publishes unconditionally, the analysis's SILENCE about a
callsite is knowledge — the walk no longer reaches it — and its edge
withdraws. `World::preserved_analysis_claims` therefore carries no callsite
kind; only `Activation` still rides preservation (fz-kdt.69.2).

`World::callsite_summary`/`callsite_targets` answer the one question lowering
and demand ask — did this callsite NAME targets? — so they read `None` for an
absent edge and for an unresolved one alike; `World::callsite_resolution`/
`callsite_target_resolution` hand back the published answer itself.
Naming no targets is not the same claim as never running. For a closure call
the two are told apart by the callee's transport CARRIER, not by its target
evidence: `materialize_closure_call_edge` lowers any callee whose layout
carries a `TransportCarrier::ValueRef` as a live public indirect call, because
a runtime callable value reaches that callsite and the boxed-apply wrapper can
call it. A callable that arrived from outside the analysed world — a mailbox
message — is exactly this shape: no target is named and none ever will be, so
"no targets" there reads UNKNOWN. Only a callsite with neither a callable
carrier nor any evidence is the dead call, and it alone lowers as
`CallReturnFlow::NoReturn` over the empty type — every `ClosureCall` tail
needs a return flow, and a call that never happens never returns. The
distinction is load-bearing at the native door, where `NoReturn` emits a tail
call: lowering a live call that way returns the callee's result straight to the
caller's caller and silently drops everything the call was supposed to return
to (fz-kdt.130).

The other half of the same idea decides what a callable position PHYSICALLY
carries. `exact_direct_callable_layout` (`jobs/transport.rs`) asks how many
distinct callable LAYOUTS a position's settled target set names, not how many
targets: a layout is pure physics, so several activations of one function —
specializations reached at different argument types, describing the same
captures — name one layout, and the value travels as those captures with no
runtime identity at all (`TransportCarrier::Absent`). Which activation a
callsite reaches is decided at the callsite from the argument types it holds
(fz-kdt.132), so that choice never has to travel with the value. Only where
the targets disagree about the callable they describe (full CallableDescr
equality: function, arity, capture types, shapes and lanes -- two different
functions with identical captures also disagree, and must) does no exact
layout exist, and the
position falls back to the generic joined layout. Counting targets instead of
layouts made a many-target position carry NOTHING while the callsite still
ground a direct call to one of them — the shape a mailbox-delivered reducer
takes through `Enum.reduce/3`, where the accumulator specialization splits one
callable input across two activations of one lambda and the reducer's own
capture then had no lane to travel in (fz-kdt.152).

Published outputs:

```text
ActivationAnalyzed(a)
ReturnType(a)
CallSiteTargets(callsite)
CallSiteSummary(callsite)
Activation(callee_key)
Executable(callee_key, need)
```

That publication is how executable demand grows. No separate sweep discovers
reachable callees. Publishing any `Activation(key)` is also the record site
for `World`'s activation frontier: `World::complete_job` folds the key into
`activation_frontier` unless `ActivationAnalyzed(key)` has already settled,
and `World::demand_activation_frontier_analyses` demands its
`AnalyzeActivation` the next time the agenda drains. Root entries published by
`SeedRoot` and caller-discovered callees published by `analyze_activation` use
this one path.
`analyze_activation`
itself never schedules the callee directly: `prepare_function_call` only
`reads` the callee's `ReturnType` (so mutual recursion cannot deadlock), so
nothing about discovering a callee blocks on its analysis, and the frontier is
the ignition path for that caller-discovered callee's first analysis pass.
`ActivationInputs(a)` is cumulative for semantic-analysis
publishers: if an `AnalyzeActivation` rerun temporarily stops seeing a callsite,
the publisher keeps its prior activation-input frontier and only adds/widens new
entries. Source/root publishers still use ordinary replacement so real external
changes can withdraw stale contributions. The `Activation` CLAIM rides a
stricter rule than the inputs do: a non-rebased conclusion keeps every
`Activation` it did not re-emit, and only a rebased one — whose ground actually
shifted — withdraws. The
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

## Artifact products wait on exact facts

The product path consumes settled facts directly. For one executable `E`,
`MaterializedExecutable(E)` waits on settled `ExecutableFacts(E)`, settled
`ReturnType(E.activation)`, `RuntimeDemand(E)`, `OutgoingInputEdges(E)`, and the
transport positions required by the local body. The shared fact already carries
the analysis, lowered body, entry dispatch, and exact callsite summaries, so
materialization neither rereads nor reconstructs that projection.

The root product waits on `RootEntry(root)`, `Recursive(entry)`, and
`InputDemand(entry)` only so it can key the entry executable, then asks for
`BackendExecutable(entry)`. Additional executables enter the request through
symbolic call edges and callable entries recorded by already demanded products.
Those exact dependencies grow artifact membership; no root-wide scan decides
it.

`DeriveRuntimeDemand(E)` owns the ordinary `RuntimeDemand(E)` World
fact. It waits for `ExecutableFacts(E)` to appear settled and thereafter reads
its Current content, the Current exact `RuntimeDemandInput(E)`, and Current
`RuntimeDemandInputs(target)` sub-facts for direct and first-class callable
targets. First-class surfaces name exact
`CallableConstructionTarget(owner, value, surface)` facts. A loaded target
input vector can expose another captured local callable, so the formula follows
only those newly named target keys to a finite local closure; it does not
inventory functions or executables. A self sub-fact is read only when an exact
self edge names it. Absence is bottom. An owned job publishes its provisional
demand and caller-local/direct or construction-owner return contributions. An
absent non-self target adds a presence wait; only peer-dependent capture/input
contributions wait for it. It never waits for a cyclic peer to settle.

Each formula conclusion owns a complete forward contribution set. A wait-free
conclusion atomically replaces that publisher's exact target contributions, so
omission retracts only that publisher. A blocked run extends without recanting
prior evidence. Exact target activation keys retain capture/surface correlation;
there is no callable-row aggregate or contribution store. Ordinary fact
movement wakes the exact registered readers, including self and mutual cycles,
until the scheduler reaches finality; an equal answer moves no content and
wakes no current reader.

A first-class callable edge contributes the target's exact `ExecutableNeed`
return contract through that same ordinary map. Observed return demand remains
an independent publisher and joins with the construction owner's contract;
neither publication widens or replaces the other, and either retracts with its
owner.

`RuntimeDemand(E)` is the single stored semantic demand value.
`RuntimeDemandInputs(E)` addresses its input vector with an independent
revision, but stores no clone and has the same producer: return/value-only
movement wakes full-value consumers, while input movement wakes both keys.
Artifact producers
read it only when settled and retain that allocation in materialized, ABI, and
backend products. There is no runtime-demand product, private cone ascent,
dirty-member index, epoch replay, or PullSession demand side map. This makes the
same World fact authority observable to dormant retained sessions through the
normal fact-movement subscription path. The production arrival-order gate
registers independent, self-recursive, and mutually recursive roots in several
orders and compares the canonical backend, interpreter output, causal
`DeriveRuntimeDemand` work multiset, and settled state of every observed demand
fact. The target
fixture gates separately pin cross-door output. A second formula-only canon
would duplicate the production artifact proof while bypassing the reactive
scheduler that this boundary is meant to test.

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

The `ReturnType(a)` fact separates three statements, and each one is read by
somebody:

```text
the CLAIM      someone is deriving a's return -- the question is live
the REVISION   the derived answer moved; 0 means it is still at bottom
Settled + no
stored return  the Kleene answer IS bottom: a never returns
```

`analyze_activation` claims the key unconditionally, so the claim appears as
soon as the activation is analysed at all, before any evidence exists. That
first claim is presence, not content, so it is minted at revision 0 and wakes no
`Current` reader ([fact-engine](fact-engine.md), *Absence is bottom*): a
`Current` reader of the empty join sees exactly what a reader of the absent key
sees.

The third line is a real answer with four consumers, and it is why the empty
claim cannot simply be withheld until evidence arrives: `Settled(ReturnType(a))`
with no stored return is how a non-returning function is reported.
`produce_materialized_executable_product` (`jobs/artifact.rs`) waits on the
settled fact and unwraps the missing return to `none`; the transport pull reads
the same settled fact at three positions and, finding no return, takes the
bottom layout (`jobs/transport.rs`: `ExecutableReturn`/`ReturnPayload` in the
callable-owner path treat it as unreachable, the two `bottom_transport_shape`
arms take it as the shape). An absent fact could never carry that: nothing
claims it, so it can never settle.

## How recursive convergence works right now

`canonical_activation_key(function, raw_inputs)` still decides activation
identity. For recursive functions it collapses UNDEMANDED inputs by
`convergence_class`, using the `Recursive(fn)` and `InputDemand(fn)` facts to
decide which slots may balloon. `InputDemand` is transitive: a slot this body
hands unchanged to a callee carries that callee's demand too, because the value
that arrives decides which callee activation is reached and therefore what this
activation publishes (fz-kdt.183,
[`type-specialization`](type-specialization.md)). It carries a second axis
beside that one: a position the body RETURNS, and the recursion does not
supply, is kept as well, because an activation publishes ONE return and two
callers sharing a key would share it (fz-kdt.199).

A NON-recursive body is keyed by precise evidence, with one erasure. A body
that never consumes callable identity -- never calls through a callable, never
constructs a lambda, and is not itself a capture-holding lambda
(`BodyKeying::consumes_callable_identity`) -- only TRANSPORTS the closures that
reach it, so `Types::erase_transported_closure_identities` erases their BRANDS
from every non-dispatch slot: every same-shape lambda that travels through a
forwarder shares one activation of it, instead of dragging a private copy of
the whole library chain behind it (fz-6gb). What the value CLOSED OVER survives
the erasure, at every depth, brands inside captured closures erased by the same
rule (`closure[?](int)`, `closure[?](closure[?]((a1_p0) -> a1_r))`). That is
the whole difference between freight and meaning here: a body keyed at one
capture type grounds its callees' capture lanes to that type, so one key
holding two capture types would leave a choice only a runtime test could
answer, and a forwarder handed one lambda at an int capture and at a float
capture is a program that knows statically which is which (fz-kdt.127).

So a forwarder SHARES across lambda identity and SPLITS on capture tuple. In
this tree, over the 597 corpus fixtures and the 469 that reach a backend dump,
58 dumps differ from what the whole-literal erasure produced: 45 differ in key
TEXT only, 13 fixtures settle more executables and none settles fewer, five
lose dispatch nodes -- the key answers what a runtime test used to -- and four
gain ten between them. The gains are `enum_take_drop_split` and its `00420_`
twin, whose recursive core asks two real questions (the accumulator tag
`{:cont, _}` vs `{:cont | :halt, _}`, and which construction the reducer is),
the dynamic same-lambda witness, whose closure comes out of a `case` no key can
pin, and `callable_union_capture_containment`, rehomed on that same dynamic
shape because the key answered its old static body outright (fz-kdt.171).
Stdout is byte-identical on all three doors on every one of them.

Identity-consuming bodies still split into distinct semantic activations. That
semantic split is not, by itself, a claim that the native machine code must be
distinct. `NativeProgram` retains an `ExecutableKey -> FnId` entry for every
activation and shares physical sibling CPS graphs only after native lowering
has made the observable distinction explicit. In particular, a captured
callable carried as `ValueRef` and used only as the callee word of an indirect
call may differ in rich semantic `Ty` while producing the same native graph.
The graph comparison does not erase direct callees, closure-construction words,
ABI layouts, effects, captures, or any type attached to another use. Thus
grounded direct calls remain specialized while boxed calls can share code
without merging activation or construction identity (fz-kdt.163).

The split is by capture TUPLE, so it separates two lambdas with different
capture tuples as readily as one lambda at two capture types --
`spawn/1` keys `closure[?](pid)` apart from `closure[?](pid, int)`, and the
capture-free `Enum.all?/1` wrapper apart from the capturing `all?/2` one. Six
of the thirteen fixtures whose inventory moves are the same-lambda shape this
erasure exists for; the other seven are that different-lambda population.

List-family convergence is coarse at the key exactly where the slot is
FREIGHT. On a slot both `InputDemand::forwarded_dispatch` and
`InputDemand::returned` leave at `Ignore`,
`Types::convergence_class_at` maps every list family reaching it to one
addressed class, so `[]`, `[t]` and the joined `[] | [t]` shape share one
recursive identity there. On a slot demand REACHES,
`convergence_collapse_list_shape` keeps the element instead, at every depth, so
`empty_list()` does not converge with `list(t)` and two callers whose lists
differ in their element key two activations apart -- which is what stops one
caller's return from being published as the join of both. The precise caller
evidence remains in `ActivationInputs(key)`, so clause reachability is decided
by evidence, not by downstream code rebuilding a more precise key.

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
  activations the runtime-demand frontier minted from a callable surface which
  no analysis walked and no caller claimed. It reconstructs the input row from
  the key's own arrow, so `World::demand_fact_producer` routes a demand to it
  only while `ActivationInputs(a)` has no publisher
  (`World::seed_activation_producer`). A key a caller discovered is the
  caller's to publish and to withdraw.
- `AnalyzeActivation(a)` owns `ActivationAnalyzed(a)`, `ReturnType(a)`,
  `CallSiteTargets(...)`, `CallSiteSummary(...)`, and any callee demand facts it
  publishes; it publishes an edge for every callsite it reaches, so an omitted
  edge is withdrawn by any conclusion, while an omitted `Activation` is
  withdrawn only by a rebased one. It
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
