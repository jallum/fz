# Semantic Fixpoint

This is the heart of Compiler2: turning a root request into a **settled**
semantic frontier of typed, reachable activations and executables. The current
engine distinguishes two notions of fact readiness:

- `Current(fact)`: the fact is present and may be read by iterative semantic
  work.
- `Settled(fact)`: every current publisher is clean, so downstream work may
  consume it as complete for now.

Three jobs shape the frontier: `SeedRoot`, `AnalyzeActivation`, and
`SealSemanticClosure`.

## What an activation is today

An **activation** is `ActivationKey { root, function, input: Vec<Ty> }`: one
function specialized for one root at one canonical input shape. Demand and
evidence are separate facts:

```text
Activation(key)       # demand / existence (multi-publisher; callers claim it)
ActivationInputs(key) # joined caller evidence (cumulative; per-publisher
                      # entries join by refine_widen between ground shifts)
```

`world.activation_inputs(key)` reads the joined evidence once its fact is
live. A clause whose params outnumber the joined evidence yields no evidence
that round — incomplete inputs never default to a type.

## Discovery is still producer-driven

`AnalyzeActivation(a)` walks `a`'s reachable clauses, infers value and return
types, and publishes semantic outputs. The walk's path results are
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
values, mailbox binds, and the root's public inputs. Published outputs:

```text
ActivationAnalyzed(a)
ReturnType(a)
CallSiteSummary(callsite)
Activation(callee_key)
Executable(callee_key, need)
```

That publication is how the frontier grows. No separate sweep discovers
reachable callees. `ReturnType(a)` is a CUMULATIVE claim: the store
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

## The seal job now consumes settled facts

`SealSemanticClosure(root)` no longer carries its own freshness machinery. It
waits on and reads **settled** semantic prerequisites, assembles the reachable
activation/executable set, and publishes `SemanticClosed(root)` when that set is
clean. There is no `DependencySnapshot`, no `semantic_closure_is_current`, and
no manual revision polling.

That means artifact work can simply wait on `Settled(SemanticClosed(root))`
instead of trying to infer freshness from presence plus a stored revision set.

## Current vs settled is the key boundary

Semantic jobs iterate on **current** evidence. Artifact/backend jobs consume
only **settled** evidence.

Examples:

```text
AnalyzeActivation(a)      reads Current(ReturnType(callee))
SealSemanticClosure(root) waits on Settled(ReturnType(a))
MaterializeRoot(root)     waits on Settled(SemanticClosed(root))
DeriveAbiReady(root)      waits on Settled(MaterializedProgram(root))
```

This is the important line in the current design: type values are not used to
encode readiness. `any` and `none` are semantic values. Fact readiness lives in
the scheduler.

## How recursive convergence works right now

`canonical_activation_key(function, raw_inputs)` still decides activation
identity. For recursive functions it collapses non-dispatch inputs by
`convergence_class`, using the `Recursive(fn)` and `DispatchMask(fn)` facts to
decide which slots may balloon.

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
  `CallSiteSummary(...)`, and any callee demand facts it publishes.
- `SealSemanticClosure(root)` owns only `SemanticClosed(root)`. It observes the
  settled semantic frontier; it does not manually prove freshness anymore.

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
