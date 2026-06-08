# Compiler2 Semantic Fixpoint

This is the heart of Compiler2: turning a root request into a settled set of
typed, reachable function activations. It runs on the fact engine
(`fact-engine`), so read that first. Three jobs do the work —
`SeedRoot`, `AnalyzeActivation`, and `SealSemanticClosure` — and the surprising
part is how little each one does on its own.

## An activation, and where its inputs live

An **activation** is `ActivationKey { root, function, input: Vec<Ty> }`: one
function specialized for one root at one input shape. Its return type and its
clause/callsite analysis live in `ActivationMap`.

Its **input is not stored as state**. It is the fact `Activation(key)`, whose
value is `FactValue::Inputs` — the `refine_widen` join of every caller's
argument types. Callers contribute; the engine joins. `AnalyzeActivation` reads
its own input back with `world.activation_inputs(key)`. So "what types does this
activation see?" is answered by *who calls it*, not by a field someone set.

## Discovery is emergent; the seal job only watches

`AnalyzeActivation(a)` walks `a`'s dispatch-reachable clauses, infers value and
return types, and for each resolved callsite emits:

```text
CallSiteSummary(callsite)          # callee + input_types + need + return_ty
Activation(callee_key)  += inputs  # contributes the callee's inputs (join)
Executable(callee_key, need)       # the callee must be built for this need
```

That contribution **is** how the frontier grows. No job walks the call graph to
discover it.

`SealSemanticClosure(root)` does the opposite of what its old name suggested: it
**observes**. It reads the published `Activation`/`Executable`/`ActivationAnalyzed`
/`ReturnType`/`CallSiteSummary` facts, assembles the reachable set, records an
exact `DependencySnapshot` of `(fact, revision)` pairs, and writes
`SemanticClosed(root)` only when nothing is still pending. It never calls
`activate`. The analysis jobs fill the envelope; the seal job closes it once it
stops changing.

## The key and the analyzed value are different things

`canonical_activation_key(function, raw_inputs)` builds the activation **key**
(its identity for dedup). For a recursive function it collapses each
non-dispatch input slot to its `convergence_class`, so many call shapes share
one key — the "balloon" that keeps a recursive function from spawning endless
specializations.

The `Activation` fact's **value** is the `refine_widen` join of the *raw* input
types, not the collapsed key. `AnalyzeActivation` types the body with the value.

```text
fib(0,0,1), fib(1,0,1), fib(10,0,1), fib(20,0,1)
  all collapse to one key:  (root, fib, [int, int, int])
  one activation, analyzed once, value = join of the raw inputs
```

Key = identity. Value = the types the body is analyzed under. Keeping them
separate is what lets dedup be aggressive without making analysis imprecise.

## Two facts decide the key: Recursive and DispatchMask

`canonical_activation_key` only collapses when it must, and only the slots it
may. Both inputs are stable per-function facts:

- **`Recursive(fn)`** — does `fn` reach itself in the static call graph? Edges
  are direct calls **and lambda creation** (`f` creating a closure over `g`
  that calls `f` is recursion). `ClosureCall` is deliberately not an edge: the
  target is a runtime value, not a symbol, so pure higher-order self-application
  is invisible to this fact by construction.
- **`DispatchMask(fn)`** — which inputs drive clause selection. The mask
  **protects** these slots from the convergence collapse, so a recursive
  function keeps empty-vs-cons (or tag) precision exactly where dispatch needs
  it, while its accumulators balloon.

So the collapse is "recursive *and* not a dispatch slot." Both halves are facts,
derived once, read whenever a callee is keyed.

## Return types flow back; analysis re-runs by subscription

`AnalyzeActivation` reads each callee's `ReturnType` (a subscription). A callee
widens its inputs (a new caller, a wider argument), re-analyzes, and its return
widens — which wakes every caller. Everything is monotone (`refine_widen` has
finite height), so the loop settles.

A callee's **first** analysis is bootstrapped explicitly: the caller enqueues
`AnalyzeActivation(callee)` when it creates the activation
(`already_present == false`). Later re-analyses are not enqueued by anyone — the
callee subscribes to its own `Activation` input fact and wakes itself when the
join widens.

## Tiny walkthrough

```text
qsort([p|rest]) = append(qsort(lo), [p | qsort(hi)])
  AnalyzeActivation(qsort,[list(int)]) resolves two callsites to qsort:
    Activation(qsort,[list(int)]) += [list(int)]   (callsite for lo)
    Activation(qsort,[list(int)]) += [list(int)]   (callsite for hi)
  join of two equal contributions = [list(int)]  -> value unchanged -> no wake
  SealSemanticClosure reads the settled facts, writes SemanticClosed(root).
```

## Ownership boundaries

- `SeedRoot` owns the entry's `Activation`/`Executable` and `RootEntry`.
- `AnalyzeActivation(a)` owns `a`'s analysis/return/callsite facts and the
  `Activation`/`Executable` contributions for `a`'s callees.
- `SealSemanticClosure` owns only `SemanticClosed`. It reads everything else.
