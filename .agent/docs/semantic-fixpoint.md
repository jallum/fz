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
function specialized for one root at one input shape. That key still carries the
canonicalized input types today. The `Activation(key)` fact means only that the
activation has been demanded; its body input evidence is not yet split out into
its own fact. `world.activation_inputs(key)` currently reads `key.input` once
the demand fact exists.

That is an intentional temporary state. The next semantic ticket
(`fz-rh2.18.5`) is to separate:

```text
Activation(key)       # demand / existence
ActivationInputs(key) # joined caller evidence
```

For now, reason about `ActivationKey.input` as both identity and body input.

## Discovery is still producer-driven

`AnalyzeActivation(a)` walks `a`'s reachable clauses, infers value and return
types, and publishes semantic outputs:

```text
ActivationAnalyzed(a)
ReturnType(a)
CallSiteSummary(callsite)
Activation(callee_key)
Executable(callee_key, need)
```

That publication is how the frontier grows. No separate sweep discovers
reachable callees.

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
