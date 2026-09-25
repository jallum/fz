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

An **activation** is `ActivationKey { root, function, signature,
callable_surfaces }`: one function specialized for one root at one canonical
input shape. The canonical inputs live directly in `signature.inputs`; its
result coordinate is the addressed result var `r0` — "return not yet known", an
unknown to resolve, never a `none()` fallback. `callable_surfaces` is a
per-input set of direct signature observations. It complements, rather than
changes, the input `Ty`: the `Ty` denotes the closure value; the sidecar records
the call shape a body can use. Read the inputs with `key.inputs()` / `key.input_len()`
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

Callsite coalescing joins the walked targets' transport surfaces and return
evidence while carrying their original activation contributions intact. For
example, rows `(list(int), list(:left))` and `(list(:right), list(int))`
remain two rows even when they select one callee key. The column-wise call
summary is a transport projection, never a new call to resolve or an input
row to publish.

At an extern or provider boundary, the runtime still needs the direct call
contract. The semantic summary therefore retains raw value inputs for closure
identity and a separate addressed boundary-input vector for that contract.
Runtime demand reads the boundary vector only for those boundaries; ordinary
compiler-owned calls read the value vector. This keeps an escaping closure's
literal target available to construction and dispatch while giving an ABI its
direct parameter shape.

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
return evidence by join, call emissions by coalescing). Branch states retain
root input `Ty` values and subject-indexed empty/cons list-shape evidence;
the graph node and this full state form the visited key. Edge proofs refine
the roots and list-shape evidence. Each plan-owned `SubjectId`'s type is projected
fresh by following its `SubjectSource` recipe from the roots, not cached
independently. List-shape evidence rejects contradictory paths without widening
one list position's observation into another's type. The result names sorted
reachable outcomes and whether graph failure remains reachable; it does not
publish a fact or consult `World`.

## Source positions and step transfers

A `StepSite` identifies a clause projection or entry step within one lowered
body revision. `BodyTables` indexes definitions; `value_definition_site` and
`step_at` expose that same index. Tails use their `ControlEntryId`. The body
owns ordered use/definition lists and `LoweredTail::child_entries`; a closure
callee is an operand, repeated arguments stay repeated, and control targets
include dispatch misses and receive timeouts. Coordinates belong to their
owning body, so a replacement body supplies replacement operations.

The activation walker evaluates a step through `step_inputs` and `step_delta`.
The input scope contains the operands that `apply_step` reads, including tuple
ancestors needed by an assertion's refinement. A primitive arithmetic operation
reads operand types without carrying unrelated callable surfaces. A tuple or
lambda construction retains the constituent evidence it actually uses.

`apply_step` reads the sparse inputs through `StepValues` and records writes
separately. Its delta contains produced values, operand refinements, and tuple
metadata written by the operation, even when they equal their input evidence.
For example, asserting an already-known tuple shape still writes that binding;
asserting a projected field can also refine its containing tuple. Applying the
writes leaves unrelated values and metadata intact. The transfer forwards its
fact reads and waits to the walker and retains no result across calls. An empty
delta reports no writes, not successful execution.

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

Absent evidence is the ascent's BOTTOM, and it is not the empty type. A
callsite whose callee has published nothing still yields a value -- type
`None` -- so the clause carries on past it, and the callee's `Activation` and
`CallSiteTargets` facts exist from the caller's FIRST walk. That is what lets
`return_membership` see the whole system on its first query, so a component is
solved once rather than growing a member at a time.

The checks that kill a path all test a TYPE, so bottom cannot trip them:
`resolve_direct_call` drops a call only when an argument's observed type is
proven empty, `deliver_tail_value` prunes only a delivered value it has
observed, and a callsite's local edge is drawn from the callee's STATIC
position (`FunctionUnknowns`), never from the shape currently standing at it.
Guarding on the observed shape instead would make membership a function of
published values, which is a flicker: the component grows and shrinks with
each revision, ownership moves with it, and the unreached-output rule retracts
the return the previous owner had just published.

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

The semantic-to-executable boundary closes one further distinction only after
the fixpoint settles. A call result omitted while analysis is climbing means
"no return evidence yet"; the same omission in a settled callsite summary means
the callee provably never returns. `project_executable_facts` records that
result value as `none`. This gives a structurally retained resume entry a
truthful bottom payload type without manufacturing `any` or pretending its
unreachable body can execute.

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
activation key is built from (`Recursive`, `InputDemand`, `ReturnUnknowns`,
named once by `World::activation_key_facts` and proven by
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
evidence: `closure_call_form` reads any callee whose layout carries a
`TransportCarrier::ValueRef` as a `Seam` call — a live public indirect one — because
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
carries. `exact_direct_callable_layout` (`jobs/transport.rs`) combines the
compatible capture requirements of the settled targets the position's own type
admits. The type brands each closure clause with the lambda the value was
minted from, and it is a coordinate of the key that addresses the position, so
it is what says which functions can arrive there. The demand's target set
answers where each one lives, and it accumulates across every callsite the
value is joined through, so it can name a lambda this slot's type excludes;
`targets_the_slot_type_admits` drops that target before the fold sees it.
Several activations of one construction combine their physical capture
requirements recursively. An absent capture requires nothing. The descriptor
also retains the lexical function and ordered semantic capture schema: distinct
schemas can require distinct selections even when their lanes coincide.
A singleton carries only its captures; a closed join adds a RawInt selector
followed by each alternative's capture lanes. Canonical source/type ordering
assigns tags independently of executable admission. The callsite uses that tag
and its arguments to select an invocation target. Unknown or first-class
callables keep the public representation. `closed_callable_clauses` and
`callable_targets_cover` prove every callee alternative and its complete capture
row is covered before runtime demand removes the public obligation.

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
for `World`'s activation frontier: `World::note_activation_frontier` folds
the key into `activation_frontier` unless `ActivationAnalyzed(key)` has
already settled (and, for a recursive-return component member, until its
`ReturnType` has too -- see *Recursive-return components* below), and
`World::demand_activation_frontier_analyses` demands its `AnalyzeActivation`
the next time the agenda drains. Root entries published by `SeedRoot` and
caller-discovered callees published by `analyze_activation` use this one
path.
`analyze_activation`
itself never schedules the callee directly: `prepare_function_call` only
`reads` the callee's `ReturnType` (so mutual recursion cannot deadlock), so
nothing about discovering a callee blocks on its analysis, and the frontier is
the ignition path for that caller-discovered callee's first analysis pass.
`ActivationInputs(a)` is cumulative for every publisher: a rerun that
temporarily stops seeing a callsite, or names no row at all, keeps the
publisher's prior activation-input frontier and can only add or widen entries
(`ContributionMap::conclude_preserving_frontier`). No publisher withdraws an
input contribution within a drive, rebased or not — the arm is unconditional
for every publisher. The `Activation` CLAIM rides a
stricter rule than the inputs do: a non-rebased conclusion keeps every
`Activation` it did not re-emit, and only a rebased one — whose ground actually
shifted — withdraws (`World::preserved_analysis_claims`;
[`fact-engine`](fact-engine.md), *Absence is bottom; rebasing is the narrowing
path*). This keeps fixpoint evidence from descending just because an
intermediate clause-reachability approximation changed. The row set is compared by per-column type equivalence, not raw `Ty`
handle equality, so representative-only changes do not dirty the scheduler.
`ReturnType(a)` is a CUMULATIVE claim, and its owning derivation follows a
closed rule (`World::define_activation_return_outcome`): when `a` is not a
member of any recursive-return component, `Derivation(AnalyzeActivation(a),
Activation(a))` owns it, exactly as before. When `a` IS a member —
`World::return_component(a)` finds it in a component — ownership moves to
`Derivation(SolveReturnComponent(owner), Activation(a))`, one derivation per
member, where `owner` is the component's own first member in semantic order.
`World::return_component` recomputes membership fresh from the current
`ActivationAnalysis.callsites` and `CallSiteTargets` facts every time it is
asked (see *Recursive-return components* below), so a membership change moves
ownership the moment the derivation offered for a `ReturnType` publish
changes: the mismatched derivation is refused by the same assertion that
enforces the rule, and the correct owner's next conclusion republishes the
fact through the ordinary join/replace path below. There is no separate
retraction step, and return storage is never cleared to force one. Either
owner's store (`ActivationMap::define_return`) takes its evidence according to
HOW IT MEETS the slot that already stands, which `ReturnArrival` names in two
cases. An ASCENDING round is a walk over unchanged ground: it reached one
round's worth of clauses, so its evidence joins by union (which preserves
closure identities) and reports `changed=false` for an equal join. Within an
epoch such a return can only ascend, which is what makes the iteration
converge on every schedule. Evidence that SUPERSEDES replaces the slot whole,
and it has two producers that say the same thing. A component solve produced
the whole recursive answer in one step, so its answer is the system's fixed
point rather than another rung of the climb, and a union with the partial
rounds that preceded it would pollute it. A walk whose ground shifted stands
on facts that no longer hold, so its standing value has to be able to
descend, or a re-analysis over edited source would keep a type its ground no
longer supports. `World::define_activation_return_outcome` reads the first
from the derivation it publishes under and the second from
`WorkGraph::derivation_rebased`. Nothing coarsens that join: a return that would otherwise
climb belongs to a cycle the static layer calls unknown, and its component's
solve names the recursive type outright, so there is no budget to spend and
no widened value to emit. `CallSiteSummary` snapshots carry
`return_ty: Option<Ty>` — honest mid-ascent records whose `None` reads, behind
the settled gate, as "provably never returns" (`settled_return`).
When the final `ReturnType(a)` claim retracts, `ActivationMap` clears its
value before a later claim can mint bottom revision zero. A remaining claim
leaves the shared payload intact.

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
`ReturnType(E.activation)`, `RuntimeDemand(E)`, the
transport positions required by the local body. The shared fact already carries
the analysis, lowered body, entry dispatch, and exact callsite summaries, so
materialization neither rereads nor reconstructs that projection.

The root product waits on `RootEntry(root)`, `Recursive(entry)`, and
`InputDemand(entry)` only so it can key the entry executable, then asks for
`BackendExecutable(entry)`. Each backend producer records typed membership
edges for its local calls, positioned callable targets, and reachable schemas.
The retained memo updates rooted membership from those committed edges, including
withdrawal when a recursive component loses its last root path. Value reads
and membership have separate roles: a caller can retain its unchanged body
while a changed callee remains part of the root artifact. Those exact
dependencies grow artifact membership; no root-wide scan decides it.

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
movement wakes the exact registered readers, self and mutual cycles included --
but only for the part of a fact a reader actually subscribes to. The law a
publisher follows is: subscribe to the part of a fact you do not yourself
produce, never the whole of it for the sake of catching a self-cycle.
`SolveReturnComponent` and `DeriveRuntimeDemand` both answer a self- or
mutually-recursive system this way: a member's own contribution to the cycle
arrives as an input value the walk publishes (`dup`'s own `wrap(dup(xs))`
call site lands at its `ActivationCallEvidence{wrap, Call(dup)}` edge cell,
one of many cells the whole `ActivationInputs` join folds together), never as
an echo of the reader's own conclusion filtered back out. Movement in a part
a reader never reads passes
it by unread; an equal answer moves no content and wakes no current reader.

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

## How a recursive call is keyed

The coordinates of an activation key are decided at the CALL SITE, by
`key_inputs_for_call` (`jobs/semantic.rs`), and `canonical_activation_key`
receives them already decided. Two static questions name each slot, in order.

The first: is the DESTINATION SLOT a position the fixpoint is still SOLVING?
The caller publishes that answer per call site as
`CallSiteUnknowns::destinations`, and it is a fact about the slot, not about
the value this site happens to write: the slot answers `Unknown` only when it
sits on a guarded cycle the caller's own walk reaches, and `Settled`
otherwise. A climbing slot keys on the variable that ADDRESSES it, because
what the walk observed there is how far the ascent has got rather than what
the program denotes, and keying on it would mint one activation per round.
Where the slot does climb, the call sites feeding it are folded together to
say where inside the arriving value: an accumulator built by consing an
unsolved value onto a solved list is `List(Unknown)` and keys as a list of the
variable at its element address, because only the element is still climbing.

That address variable is ONE coordinate shared by every caller in the program,
which is why the slot has to earn it. A seed call handing `[]` and an ascent
call handing `[x | acc]` do name the slot alike, because the cycle they are on
runs through the callee's own recursion and so lies inside the reach of every
caller that can get to it. A cycle that runs through a SIBLING caller instead
-- one helper read by two loops, each climbing in its own -- lies outside the
reach of a caller not on it, so that caller keys on what it observed and the
two loops do not share an activation. `destinations` is therefore the
answering caller's answer: two callers of one slot can differ, and each says
what its own reach can see. `Enum.chunk_by` and `Enum.sort_by` both end at
`Enum.reverse_list/1`, and only the sort chain's recursion feeds that slot
back round through a cons, so the helper keys twice -- `[int]` for the chunk
chain, the slot's address variable for the sort chain -- and the two chains'
element types never meet.

The second, asked only where the first settled everything: can a value at this
slot be observed from outside the activation at all? `observable_inputs` says
yes when a dispatch question reaches the slot
(`InputDemand::forwarded_dispatch`, source observations joined with what
every callee receiving an unchanged input asks of it), or its return may depend
on the slot (`FunctionUnknowns::returns_input`). Return observability includes
opaque calls: `forward(x) = Protocol.pick(1, {:tag, x})` cannot discard `x`'s
type merely because the protocol callback has no body. Its result may carry
`x` back out. An unused second parameter stays irrelevant; the dependency
comes from the arguments actually passed, not every input of `forward`.

Source observations include entry and inline dispatch, branch
conditions, closure calls and captures, and receive's outer bindings and timeout.
`SourceObservations` pulls these questions backward through existing transport
origins. For `case x`, the input is demanded `Whole`; for a case on a field of
`pair`, the tuple input is demanded `TupleFields`. Aliases and joined values
carry the question to each source. Observed computations and call results
conservatively ask about their actual operands; this dependency walk does not
evaluate those operations or infer precise callee return dependence.

The local worklist and unchanged-input forwarding use the four-state
`DispatchDemand` lattice. Each value or input slot can rise only twice, so
recursive source dependencies terminate. Callee bodies and entry plans remain
fact subscriptions even when their current demand is `Ignore`: adding or
removing a source question rederives the callers' demand.

Only a slot that neither question can reach is freight: its arriving type
does not distinguish the compiled activation, so it keys on its bare address
variable. Both keying facts must exist before this question is asked. Missing
return knowledge is conservative evidence, never a proof of no dependency.

Both questions want the same coordinate for a whole slot, so they fold into one
`KeyShape` and one `KeyShape::coordinate` call, where `Settled` means "key on
what arrived".


Observed call SURFACES travel beside the value type rather than inside it, so
they answer the same question in their own place:
`World::canonical_activation_key_with_callable_surfaces` blanks the surfaces of
exactly the slots that one vector calls unobservable. Nothing else collapses a
key. There is no separate brand erasure over the input types: it was measured
over the whole lib suite and the fixture matrix to change no key that
`key_inputs_for_call` had not already addressed, and it was deleted
(fz-kdt.98.3.17).

What a callable CLOSED OVER is not freight. Capture types travel in the type
the call site named, so a body keyed at one capture type grounds its callees'
capture lanes to that type; one key holding two capture types would leave a
choice only a runtime test could answer, and a forwarder handed one lambda at
an int capture and at a float capture is a program that knows statically which
is which (fz-kdt.127).

Distinct semantic activations are not, by themselves, a claim that the native
machine code must be distinct. `NativeProgram` retains an `ExecutableKey ->
FnId` entry for every activation and shares physical sibling CPS graphs only
after native lowering has made the observable distinction explicit. In
particular, a captured callable carried as `ValueRef` and used only as the
callee word of an indirect call may differ in rich semantic `Ty` while
producing the same native graph. The graph comparison does not erase direct
callees, closure-construction words, ABI layouts, effects, captures, or any
type attached to another use. Thus grounded direct calls remain specialized
while boxed calls can share code without merging activation or construction
identity (fz-kdt.163).

The context-free key therefore retains the capture tuple unless flow-sensitive
evidence proves that layout cannot become observable (fz-kdt.169). Collapsing
the tuple to its arity loses dispatch-free static grounding: the static
same-lambda witness needs one-slot `int` and `float` capture layouts to key
separately or else leave their choice to runtime. This is a conservative
correct-by-construction and performance law, not a proof that every possible
tuple component is universally necessary.

A measured flow-sensitive alternative added capture-layout relevance as a
fourth component of the existing `InputDemand` fact. It safely recovered six
executables, but added 3,173 work-graph applies across 478 backend-producing
fixtures while removing only 89 product evaluations. The deterministic
comparison and complete mover classification are recorded in
[`fz-kdt.169-capture-key-proof`](../measurements/fz-kdt.169-capture-key-proof.md).
The recurring read/join/transform cost is disproportionate, so that component
was rejected and capture relevance remains implicit in the retained tuple.

One fold then applies to what the key named. Where the callee's demand on the
slot is `DispatchDemand::ListShape`, the coordinate passes through
`Types::list_family_class`, so `[]` and `[t]` key one activation there: such a
question is `[]` against `[h | t]`, which the callee answers by testing the
value it is handed, so the refinement the value arrives with is not a
coordinate. Without it a recursive list walker keys twice, once for the seed's
cons and once for the tail the recursion hands back, and the two activations
compile the same body. The ELEMENT is untouched at every depth, so two callers
whose lists differ in their element key two activations apart -- which is what
stops one caller's return from being published as the join of both. Any other
demand leaves the coordinate exactly as it arrived; an absent fact reads as
`Whole`, so a coordinate is only ever folded on a proven answer. The precise
caller evidence remains in `ActivationInputs(key)` either way, so clause
reachability is decided by evidence, not by downstream code rebuilding a more
precise key.

So today:

```text
key.input     = canonicalized identity and current body input
ReturnType(a) = current return approximation
Settled(...)  = scheduler-level proof that downstream work may rely on it
```

That is not yet the final semantic shape, but it is the current code shape and
the basis for the remaining type-system tickets.

## Recursive-return components

Most activations' returns are settled by their own `AnalyzeActivation` alone.
When two or more activations reach each other -- or one reaches itself -- their
returns are mutually dependent, and one activation's ordinary fixpoint ascent
can no longer answer the question by itself: `AnalyzeActivation(a)` only ever
`reads` a callee's `ReturnType` (`prepare_function_call`), so a bare cycle of
reads alone converges, but the LEAST fixed point over the whole cycle is a
computation only one place can do once, for every member together.

`World::return_component(seed)` answers, freshly, which set of activations
`seed` solves its return with. It is built in two layers, and the split
between them is what makes the answer settle.

A function reference and its source relationship have separate lifetimes.
`FunctionId` is available before a body exists; `ReturnSkeleton(FunctionId)`
is the separately published definition. An undefined local relationship waits
on `LoweredBody`, without publishing `any`, `none`, or `Returns::Opaque`.
Definition arrival and replacement rederive the same referenced relationship.
For `first(x, y) = x`, its return is `Input(0)`; replacing the body with `y`
changes that to `Input(1)` without analyzing an activation of `first/2`.
Compile-time definition macros may themselves execute during source lowering.

The relationship retains the exact `Rc<LoweredBody>` published by lowering.
That body is the operation/control graph: ordered clause projections and entry
steps, lambda capture operands, multi-output operations, assertion-only steps,
tails, and inline dispatch plans. `LoweredBody::value_definition_site` (backed by `BodyTables`) and
`LoweredBody::step_at` address these operations without a second instruction
vocabulary or definition index. A `Ground(ValueId)` remains an address into
this definition even when the structural return view does not expand it.

Relationship equality includes the retained body, not just return shapes and
invocations. Replacing `not x` with `not y` can preserve the result ValueId;
replacing `if x` with `if y` can preserve both returning alternatives. Both
must publish a changed relationship. Old readers retain their immutable prior
body. Ordinary and extern definitions carry a body; opaque provider/protocol
relationships have no local body.
When a provider gains a local definition, its old opaque equation may still
stand while lowering runs. Local execution and callee prerequisites require
the replacement equation to contain a body; fact presence alone is insufficient.
They wait on the existing `ReturnSkeleton` producer until it publishes that body.

`AnalyzeActivation` consumes this published relationship's body and subscribes
to `ReturnSkeleton`, as do its local callee prerequisites. Its independent
`EntryDispatch` read remains: source relationship discovery does not require
planning entry dispatch. The evaluator and sparse step transfers are unchanged.
Keeping an assertion or discarded call in the source graph preserves its
execution prerequisite; it does not yet teach the return solver to solve that
prerequisite independently of activation reachability.

`FunctionSkeleton::invocations` contains one complete record per `CallSiteId`:
a named function or a value-callee skeleton, ordered argument skeletons, the
result `ValueId`, owning control entry, and return/deliver destination. The
entry refers back to the existing lowered tail and its control prerequisites.
Thus `f.(x)` and `g.(x)` differ before target resolution; `f.(f.(x))` retains
two invocation positions and the inner-result-to-outer-argument edge. A callee
can itself be a projection or a preceding call result. Discarding the result
does not remove the invocation or its successor destination. The old separate
argument and named-callee maps have been replaced in every consumer.

This is source relationship information. Current call binding still creates
an `ActivationKey` before reading return evidence, and the return solver still
binds `Ground` leaves from activation observations. Retaining the callable
operand does not yet move that ownership or implement shared inference.

The static layer decides which positions of a return system are still being
solved, from the function skeletons (`return_skeleton.rs`,
`return_unknowns.rs`). A position is a function's whole return, one of its
parameter slots, one of its own call sites' results, or an interior place
inside a skeleton. One graph carries three kinds of edge:

- `Alias`: a structural reference or projection.
- `Constructor`: a structural dependency held inside a constructor.
- `OpaqueMayFlow`: possible return dependence without a known return shape.

Return-input observability follows all three kinds. Productive-cycle detection
follows only structural edges and requires a `Constructor` edge within the
cycle. Such a cycle wraps another layer each turn, so its solution is a
recursive type. A cycle of aliases alone settles by the ordinary join: the
least solution of `rest = tail(rest) | [int]` is `[int]`.

An opaque edge contributes no structural branch. If `opaque(_)` actually
returns a constant, `loop(n - 1, [opaque(acc)])` does not grow another layer
around `acc`. Pretending the opaque result equals `acc` would invent that
growth. Possible dependence keeps the argument observable without asserting
such an equation.

Return descriptions distinguish absence from a known empty answer.
`Returns::Entries` contains known control-entry shapes; an empty set names
no returning entry. `Returns::Declared` carries a declared result type.
`Returns::Opaque` describes a bodyless provider: its inputs may flow to its
return, but it supplies no structural equation. An unavailable named callee
conservatively connects its call result to the positions referenced by the
actual arguments. A protocol callback uses this boundary without enumerating
or loading unrelated implementations. Provider boundaries name no local
activation and cannot enter a concrete return-component equation.

The function whose local keying answer is requested waits for its own return
skeleton through the normal producer chain. A transitively named function
without a definition is read rather than eagerly demanded; discovery reads
its `FunctionDefined` fact as well as its missing `ReturnSkeleton`, so a
definition arriving later makes the walk demand the real skeleton. Bodyless
protocol callbacks and provider boundaries do not wait for impossible local
bodies. There is one lowering of each real body's return, shared by the
static questions and the activation solver.

A call made through a value retains its callable operand in the source
relationship. The static position walk follows only `InvocationCallee::Named`
references; it does not resolve the value operand to targets. Its result
therefore has no static target edge yet. A cycle that closes only through a value call is
therefore invisible here, and the activation layer below handles it by the
ordinary climb rather than by a component solve.

The ACTIVATION layer lifts that answer to the activations that exist
(`return_membership.rs`). One rule draws every edge: a call is unsolved when
it hands on an argument the fixpoint is still solving, or when what it yields
is itself such a position. The argument case puts the callee's matching SLOT
on the caller's cycle -- that is how `wrap`, which mentions nothing
recursive, joins a cycle it is handed, and how the lambda that builds an
accumulator joins the system that names the accumulator's type. The result
case names no slot: a function that wraps a constructor around its own
recursive result hands on nothing unsolved, and only its result says the two
returns are one system. Membership is the CONNECTED component of that
relation, so the answer is a property of the set rather than of the seed and
either member's query agrees on the same canonical owner. A function whose
return the static layer says it owes is a member even when its call sites
resolved nothing -- a system of one -- which is what makes the owner known
from an activation's first walk. An activation on neither side of that
relation returns `None` and is answered by its own `AnalyzeActivation` as
always. The membership itself is found by `return_membership::discover`, a
local bidirectional worklist walk from the seed rather than a scan of every
activation the world holds: at each member it queued, the OUT direction
reads that member's own unsettled call sites the way the edge rule above
does, and the IN direction reads `Callers(member)` -- every call site that
has ever addressed it. `Callers` is cumulative and never withdrawn, so a
listed site is a CANDIDATE, not a live edge on its own; the walk re-verifies
each one fresh, checking that its own function's `ReturnUnknowns` still
calls it unsettled AND its current `CallSiteTargets` still resolves back to
`member`, and silently drops any candidate that fails either check. Both
directions run for every member the walk finds, so the same neighbour is
reached once from the caller's side and once from the callee's `Callers`
entry, and the two never disagree; the walk's cost is proportional to the
component and its immediate callers, never to the size of the world. Owner
selection is a fold over the discovered members, not a sort-and-take-first:
`owner` is the semantic minimum (`SemanticOrd`) over the member set,
computed once membership is known, while `members` is separately sorted
into semantic order for iteration and display. `World::return_membership` is
the one entry point onto all of this, and it is pure: no telemetry
parameter, no event of its own. It returns a `ReturnDiscovery` carrying the
settled `ReturnMembership` alongside what the walk measured -- `visited`
(every activation the walk touched, members and rejected `Callers`
candidates alike) and the member set the reads below are drawn from.
Callers that only want the settled answer call `.is_alone()` or
`.into_component()`, both forwarding to `membership`, so they read exactly
as they did before this type existed.

`SolveReturnComponent`'s own subscription reads the same relation `discover`
walked to reach its answer (`ReturnDiscovery::reads`, wrapping
`return_membership::reads_of`): each member's own unsettled out-edges, so a
target naming itself wakes the solve; each member's `Callers` set, so a
newcomer's arriving candidate wakes it too; and `CallSiteTargets` for any
non-member site `Callers` lists that already addresses a member, the same
candidate-verification check discovery makes, so a candidate resolving away
is caught without waiting on a member's own facts to move. `reads` is
computed once, off the same walk that found `membership`, and the solve
reuses that one `Vec` at every exit rather than asking a second walk for it.
Discovery and the solve's subscription read the one relation this way on
purpose: a subscription drawn independently could drift from what the walk
actually depended on, and either miss a wake or attribute one to a read that
was never load-bearing. Because this is a live query over current facts
rather than a cached one, a membership change is visible on the very next
call -- there is no separate component fact to retract.

The `return_membership.discovered` telemetry event belongs to the solve, not
to this query: `solve_return_component` dispatches it itself, once per
dispatch, from the one `ReturnDiscovery` it already computed. A whole-world
scan cannot see a call site aimed at an activation that has not been minted
yet, so it would answer such a seed `Alone` and self-publish a `ReturnType`
that a later solve then has to clear and republish; the local walk instead
reads the unresolved call directly off the facts that exist and answers
`Unknown` until the callee exists to be walked. `decode/1` in
`fixtures2/behavior/projected_recursive_result.fz` is built to hit exactly
this window -- its own activation does not exist the first time the
component reaching it walks -- and `return_membership_test.rs` proves the
window closes: production telemetry (`work_graph.applied`) shows `decode/1`'s
`ReturnType` published only by `SolveReturnComponent`, never by its own
`AnalyzeActivation`.

Ownership of each member's `ReturnType` follows that query directly (see
*Ownership boundaries* below): `SolveReturnComponent(owner)` -- one job per
component, keyed by its owner -- solves and publishes every member's
`ReturnType` at once. It evaluates each member's static return skeleton
under that member's own bindings, and every one of those bindings is a fact
the walk already publishes: `ReturnSolveInputs` (waiting only if one is
still missing entirely; a component cannot be solved from a partial
membership) binds a `Ground` leaf through `value_types` and says which
entries the activation returns through via `reachable_entries`;
`CallSiteTargets` binds a `Result` leaf to the activations that site
addressed; `ActivationCallEvidence` binds an `Input` slot to the evidence
already standing at each of the member's caller edges -- a member's `Seed`
cell and every non-member caller's `Call` cell, joined the same way the whole
`ActivationInputs` map joins its rows -- beside the arguments the member's
callers hand it. It never invents a fact to carry a shape, and there is no
second tree to keep in step.

`ReturnSolveInputs` is a second, narrower `FactKey` over the same stored
`ActivationAnalysis` a member's `AnalyzeActivation` walk already computes and
publishes as `ActivationAnalyzed` -- one stored value, two keys, mirroring
`RuntimeDemand`/`RuntimeDemandInputs`. It carries `reachable_entries` and
`value_types` at exactly the leaves the solve's equations read: every
`Ground` leaf, and a `Result` leaf only when its call site is still
unaddressed (`Unresolved`, or `Resolved` with no edge naming an activation).
A `Result` leaf whose call site IS addressed is answered by the solve's own
equations (`Term::Return`, one flattened branch per addressed call), never by
a value read -- so its observed type is not part of the projection, and a
member's own call site resolving (or its callee's value shifting under an
already-resolved call) moves `ActivationAnalyzed` without moving
`ReturnSolveInputs`, and wakes no solve. The walk computes the addressed set
once, from the same call resolutions it publishes as `CallSiteTargets`, so
consumption and subscription come from one value rather than two computed
separately and left to agree by convention.

One more fact is read, and it carries no shape at all. Membership is
discovered, not declared: an activation minted after the solve concludes can
call a member and so join the component. Every binding above names only the
members the solve already knew, so none of them moves on a newcomer's
account, and the scheduler's rule that a concluded producer already
subscribes to everything its conclusion depended on does not reach this case.
`Callers` -- the inverse of `CallSiteTargets`, keyed by the callee -- closes
it: the newcomer's call edge moves its callee's caller set, the owner
re-solves, and rediscovers membership with the newcomer in it. The solve
reads it for the movement, never for the value.

The solve (`jobs/return_component.rs`) is a small fixpoint over the finite
member set, not a re-run of type inference:

1. **Flatten.** An expression may reference another member two ways: guarded,
   nested inside a real constructor (a `Tuple` element, ...), or unguarded, as
   a bare alternative of a top-level `Union` (or the whole expression). An
   unguarded reference carries no information of its own -- the least fixed
   point of `x = x | y` is just `y` -- so it is inlined away before anything
   else runs. A guarded reference is left alone; it already denotes the
   standard equi-recursive type over however many times the cycle unfolds.
2. **Contributes.** For every member, whether at least one flattened branch
   reaches a `Published` leaf or an external activation's evidence without
   depending on a member that itself never contributes, computed as the least
   fixed point of that monotone rule over the finite member set. A member with
   flattened branches but none that contribute is a *productive cycle with no
   base case*: every branch is real, but every one of them depends, transitively,
   on another branch that never bottoms out in real evidence -- so its least
   fixed point is the empty type, published as `none`, a real, computed fact
   distinct from a member with NO flattened branches at all (a bare, unguarded
   self-reference, inlined away by step 1), which publishes nothing -- the
   ordinary bottom, exactly like an activation nothing has evidenced yet.
3. **Lower and intern.** Every contributing member's surviving branches lower
   to one `DescrOf<ComponentRef>` (`ComponentRef::Local(index)` for an
   in-component structural reference, `ComponentRef::Published(ty)` for a
   `none`-member or an external one), folded by `union_regular_bodies`.
   Every contributing member's body is handed to `Types::intern_regular_bodies`
   in ONE call -- the interner's own bisimulation partition refinement is what
   collapses two members whose bodies turn out identical (an alias pair), so
   the solve never needs a separate closure-comparison pass of its own.

   Before discovering descriptor SCCs, the regular kernel removes semantically
   empty clauses using the existing emptiness reader over a read-only view of
   the unpublished local bodies. This matters when a ground restriction removes
   a cycle's only seed: `X=:a|{Y}; Y=X\:a` denotes `X=:a, Y=none`. Empty
   clauses must disappear before keying, including those inside an otherwise
   productive body. Local references never acquire published identities during
   this check. The ordinary descriptor intersection/difference algebra works
   over those references as well as settled types; the source equation solver
   must still supply fixed ground filters and preserve pending prerequisites.

Every OTHER `Local` a member's expression names -- any activation outside the
component, including one owned by a different component -- is an external
dependency: its `ReturnType` is `reads`, never `waits`, mirroring
`prepare_function_call`'s own rule exactly. A still-absent external is this
solve's bottom so far, not a block; the read is what re-wakes the solve once
that external's evidence rises. Waiting on it instead would deadlock the
moment two components' owners depended on each other's members. The solve
`waits` on two things, never more. One is a member's own `ReturnSolveInputs`,
the part of that member's analysis its equations actually read, rather than
the whole `ActivationAnalyzed` -- a member's analysis moving somewhere the
skeleton never observes (an addressed call site's result type, an
unreachable entry) does not wake this solve. The other is, when
`World::return_membership` answers `Unknown` rather than naming a component,
the reached-but-Unresolved `CallSiteTargets` edges the walk found -- on
their own SETTLED movement, never their next Current reading, since each
already carries one revision (the Unresolved verdict itself) and a Current
wait would be satisfied immediately with nothing new to say. An `Unknown`
membership is not a conclusion: this exit declares no outputs and no
`changed` set, so the wait-free/blocked-run rule above (*Each formula
conclusion...*) keeps every `ReturnType` this job already published for the
component standing rather than retracting it, exactly as any other blocked
run would. Ownership reverts to a member's own `AnalyzeActivation` only once
membership actually settles to `Alone` -- a real transfer, not a block --
and that exit stays wait-free, because a different job now owns the return
and will republish it. A settled component publishes every member's
`ReturnType` in one atomic conclusion, so a reader waiting on any one member
sees the whole component settle together.

The same solve settles each member's own INPUT evidence: a member's slot
equation is the join of every call site's argument skeleton, evaluated in
the caller that made the call, so its solution is the closed form of an
accumulator that would otherwise be discovered one nesting at a time. It is contributed back through the ordinary
`ActivationInputs` join, one whole row per member -- and only when the solve
named EVERY column of that row. A row is one correlated observation, so a
member whose slots the system did not all reach contributes nothing rather
than filling the gap from somewhere else. Each column is the whole input the
solve settled -- the type AND the callable surfaces standing behind the
callers' parameters that reach it (`slot_surfaces`) -- so a solved row is one
the member's own walk could equally have published, and `insert_row`'s
equivalence recognises it as the row already standing instead of adding an
alternative beside it. An activation KEY coordinate is never that value: it
names a position rather than describing one, and a row that mixed a solved
type with the member's own key surfaces would offer a callable the walk never
saw, leaving the call it feeds with no clauses to match and an `any` result
that every callee keyed off the row inherits.

Every publisher into that join writes its own cell, not the joined row:
`FactKey::ActivationCallEvidence { callee, from: EvidenceSource }`, where
`EvidenceSource` is `Seed` (`SeedRoot`/`SeedActivation`, the callee's own seed
row), `Call(caller)` (one cell per calling activation, written by that
caller's own `AnalyzeActivation`), or `Settled` (this solve's own
contribution). `evidence_source_for(job)` is the one-to-one map from the
three jobs that ever publish an `activation_input_contributions` row to the
source they write under; `World::activation_call_evidence(callee, from)`
reads exactly one such cell, gated on that edge's own revision, never the
aggregate. `gather` reads a member's `Seed` cell always, and its
`Call(caller)` cell for every caller OUTSIDE the member set -- never a
member's own `Call` cell, because that edge is already modeled structurally
as a `Term::Shape` binding inside the solve's own equations, and never the
`Settled` cell, which is the solve's own answer and has no reader. This is
the edge-fact law applied one level below `ReturnSolveInputs`: a publisher
subscribes to the part of a fact it does not itself produce, by construction,
down to the one cell each individual publisher writes, decided by which
`JobEffects` field a job fills rather than by comparing job kinds at read or
dispatch time. A member's own walk republishing the same call evidence it
published before writes to the same `Call(that member)` cell `gather` never
reads, so it cannot re-wake the solve that already answered it -- the
component settles in the one dispatch its membership and evidence allow,
never a second one spent re-confirming a fact the solve already produced.

`SolveReturnComponent` schedules no follow-up job of its own, exactly like
`AnalyzeActivation`. Nothing ever `waits` on a member's `ReturnType`
(`prepare_function_call` only `reads` it, to avoid deadlocking mutual
recursion), so a genuine waiter or a changed-revision wake on one of its own
reads is not, by itself, enough to guarantee the solve ever ignites -- a
non-member's `ReturnType` has no such gap because `AnalyzeActivation`
self-publishes it unconditionally as a side effect of running, but ownership
moving to `SolveReturnComponent` carries no analogous guarantee. The
`activation_frontier` closes that gap the same way it ignites first-run
analysis: `World::activation_owes_return(key)` is true exactly while `key` is
a component member and its `ReturnType` has not yet settled, and both
`activation_frontier`'s insertion (`World::note_activation_frontier`) and its
retirement (inside `World::complete_job_with_external`) check it alongside
`ActivationAnalyzed(key)`'s own settledness. `World::demand_activation_frontier_analyses`
pokes the owning `SolveReturnComponent` once per distinct owner identity, the
same first-run gate it already applies to `AnalyzeActivation`, and leaves the
member on the frontier afterwards so a later owner change -- membership
growing to promote a different first member -- is still caught the next time
the frontier is scanned. A component whose members nothing ever reaches at
all -- a dead branch, statically unreachable -- never gets an `Activation`
fact published for any member, so it never enters the frontier and never
runs; its members' `ReturnType`s simply never settle, which is the same
"no fact" bottom an ordinary un-analyzed activation has. A component that IS
reached, by contrast, has every member's return settle once its own analysis
does, whether or not anything downstream happens to consume it -- matching
the same unconditional guarantee a non-member already carries.

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
- `AnalyzeActivation(a)` owns `ActivationAnalyzed(a)`, `CallSiteTargets(...)`,
  `CallSiteSummary(...)`, and any callee demand facts it publishes; it
  publishes an edge for every callsite it reaches, so an omitted edge is
  withdrawn by any conclusion, while an omitted `Activation` is withdrawn only
  by a rebased one. It
  schedules no follow-up job of its own: publishing `Activation(callee_key)` is
  what feeds `World`'s activation frontier. When its OWN `Activation(a)` is
  absent -- nothing claims `a` -- it concludes on the recorded read and
  re-lists its standing claims, rather than waiting on a producer that no
  longer exists for it. It also owns `ReturnType(a)` -- but ONLY while `a` is
  not a recursive-return component member; see *Recursive-return components*
  below for the member case.
- `SolveReturnComponent(owner)` owns `ReturnType(member)` for every member of
  `owner`'s component -- see *Recursive-return components* below.
- `World` owns the `activation_frontier` standing-demand set alongside the
  scheduler it wraps. `World::note_activation_frontier` is its sole insertion
  site (on an `Activation(key)` publish), and inserts whenever `key`'s
  analysis has not settled OR `key` currently owes a recursive-return
  component solve (`World::activation_owes_return`); `World::complete_job_with_external`
  retires a key once neither holds. `World::demand_activation_frontier_analyses`
  is its sole reader: it demands `AnalyzeActivation` the first time (as
  before), and once that has run, demands the owning `SolveReturnComponent`
  once per distinct owner identity while `activation_owes_return` still holds.
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

Entry planning is gated the same way. `PlanEntryDispatch(f)` asks for
`FunctionDefined(f)` and the exact `TypeDefined`, `StructDefined` and helper
`GuardDispatch` facts f's clause heads name. It does not wait on
`ModuleDefined(f's owner)`: the wait was there, and nothing ever read its
value. A plan settles whether or not that aggregate exists, which is what
`entry_dispatch_settles_without_its_module_aggregate` records.
