# Type Specialization

Use this before touching `src/type_infer`, the colocated fixture corpus in
`src/type_infer/fixtures`, or planner work that consumes inferred call/return
facts.

## Model

Type specialization is an inference engine over the CPS-lowered `Module`. It
infers reachable function returns by running a monotone worklist over call
contracts:

```text
call contract = FnId + input ValueFacts
activation    = one inferred instance of that FnId at an identity class
return fact   = activation-local Info cell
```

`FnId` is body identity. It is the target used by direct calls, closure bodies,
continuations, and protocol implementation bodies. It is not the inference
instance. The same `FnId` can have separate activations for `id(1)` and
`id(:ok)` without joining those callers into one monomorphic function cell.

### Activation identity and convergence

An activation is keyed by its `FnId` plus a per-slot **identity class**, not by
the raw input tuple. For each entry-param slot the class is either:

- the exact input value, for a **dispatch subject** — a slot that can change
  which clause/branch the body selects or which callable it invokes; or
- the slot's `convergence_class` otherwise (a non-dispatch slot).

`FnIr::dispatch_subject_slots` computes the dispatch mask: a backward slice from
every `Term::If` condition and every invoked-closure operand to the entry params,
over the only intra-body binding edges (`Stmt::Let` operands and `Term::Goto`
args). It is sound by construction — it reaches every entry param a control
decision can depend on, never fewer.

Convergence applies **only to recursive fns** (`Module::recursive_fns`, the same
recursion notion the planner uses for recursive-key widening). For a recursive
fn, two calls that agree on every dispatch subject and on the *family* of each
non-dispatch slot share one activation; the exact non-dispatch types are then
recovered by joining the stored inputs through `refine_widen`
(`[] ⊔ nonempty_list(int) = list(int)`). `convergence_class` folds all pure list
shapes into one class, so an accumulator's emptiness×element cartesian product
stops forking activations — that product is the over-specialization balloon
(see `quicksort`'s `partition/4`). Cross-family non-dispatch differences (`int`
vs a tagged tuple `{:cont, int}`) keep distinct classes, so a shape-changing
accumulator and its type errors stay observable; the input-join is idempotent so
joining a callable slot with itself never erases its closure-literal identity.
Non-recursive fns are never converged: their distinct call sites are genuine
per-callsite polymorphism. The planner consumes the converged activations
directly — its `canonical_public_key` maps each narrow spec request onto the
single converged bucket, so no separate planner-side widening is needed.

Parameters do not own types and do not default to `any`. An activation supplies
the input facts. A return cell starts as `Pending` and moves upward only when the
body produces information. A declared `@spec` is a backstop for bodies the
engine cannot infer and the authoritative type source for declared
opaque/builtin seams, including operator-headed kernel functions.

The engine is implemented in `src/type_infer/mod.rs`, with model fixtures in
`src/type_infer/fixtures`, and is exercised by `cargo test --lib type_infer`.
Production planning still owns executable plan facts and codegen ABI shape while
this engine owns activation-based type flow.

The crate-visible API is intentionally small:

- `infer_from_entry` runs the reachable activation graph from an entry point and
  returns `TypeInferOutcome { status, activations, edges, dead_arms }` while
  also emitting telemetry.
- `TypeInferStatus` is the coarse API result: `Complete`, `Unresolved`, or
  `Invalid`.
- `TypeInferActivationFact` is the production data boundary for reached cells:
  an opaque per-outcome activation id, `FnId`, canonical input `Ty`s, and
  `TypeInferReturnState`.
- `TypeInferActivationEdgeFact` connects solved caller/callee activations and
  carries the structural `CallsiteId` plus callsite span metadata the planner
  uses to line solved edges up with its own dispatch slots.
- `TypeInferDeadArmFact` records matcher arms proved dead for a specific solved
  activation. Dead-arm telemetry is not just `FnId`/block level.
- `TypeInferReturnState` mirrors the settled boundary state:
  `Pending`, `Unknown`, `NoReturn`, or `Known(Ty)`. It is not the solver
  lattice; private `Info` remains the refinement cell.
  Matcher proof stays private and is erased at this boundary.

Production consumers read structured facts from the outcome. They must not
scrape telemetry to build planner state. Telemetry remains the shared observable
surface for tests and operators. The engine emits:

- `fz.type_infer.activation` for every reached activation, including function
  identity, the opaque activation id, return state, rendered return type, and
  in-process `Ty` data when known.
- `fz.type_infer.activation_edge` for every solved activation-to-activation
  edge, including caller/callee activation ids and callsite slot/span details.
- `fz.type_infer.fn_return` for each reached function, joining known activation
  returns through `Types` and reporting whether any activation is unsettled.
- `fz.type_infer.diagnostic` for located type errors.
- `fz.type_infer.dead_arm` for matcher arms proved inaccessible, keyed by the
  activation id that proved the branch dead.
- `fz.type_infer.dispatch_mask` for each activated fn: its arity and the entry
  slots that drive dispatch (the precise slots; the complement converges).

## Cells

Every local slot and activation return is an `Info`:

```text
Info = Pending
     | Unknown
     | NoReturn
     | Known(ValueFact)

ValueFact = {
  ty: Ty,
  proof: ValueProof,
}
```

The states are intentionally separate:

- `Pending` means a dependency has not produced its first fact.
- `Unknown` means a live value exists, but this engine cannot prove its type.
- `NoReturn` means a path contributes no value to the current continuation.
- `Known(ValueFact)` means the engine has a visible `Ty` plus optional proof.
- `Known(none)` is a proved contradiction: the value set is empty.
- `Known(any)` is a real top fact. It is not a placeholder for missing proof.

`Pending`, `Unknown`, and `NoReturn` are inference states, not public value
types. A settled edge that still has `Pending` or `Unknown` must be consumed
explicitly by a boundary decision. It may diagnose unsupported required
knowledge or erase a still-live dynamic value to `any`; it must not silently
turn uncertainty into `none`.

The planner boundary uses this rule when projecting activation facts onto
reachable executable entries. Semantic return truth and materialized executable
bodies are keyed by `BodyKey` (`FnId + semantic input`), while `SpecKey`
remains the planner entry key (`BodyKey + ReturnDemand`). `ReturnDemand` may
describe an edge ABI, but it is not a distinct semantic return and does not
create another body. If the planner key is polymorphic, compatibility is tested
by instantiating the requested shape against the concrete activation witness
through `Types`; inference facts are not rewritten into planner keys.

## Joins

The engine uses the same shape for activation-cell updates and control-flow
branch joins:

```text
join(Pending, x)         = x
join(Unknown, x)         = Unknown
join(NoReturn, x)        = x
join(Known(a), Known(b)) = Known(a.widen(b))
```

`Known(a).widen(Known(b))` calls `Types::refine_widen` for the visible type and
keeps proof only when both sides carry the same proof. This gives the worklist a
finite ascending chain while preserving exact proof only where it is still valid.
When both sides share one pure product outer shape, `refine_widen` performs the
structural convergence there too: tuple fields, list emptiness/element slots,
resource payloads, arrow returns, and map fields collapse recursively inside
`Types`. There is no second structural-widen primitive.

`Unknown` is sticky because a live unknown arm is still live. `NoReturn` is
neutral because a non-returning path contributes no value. `Pending` is neutral
because it is worklist latency.

## Proof

`ValueProof` is branch-selection evidence carried beside the visible type. It is
not a second type lattice and is not part of the public value type.

```text
ValueProof = Unproven
           | Exact(Ty)
           | TupleFields([ValueProof])
           | MapFields { fields, complete }
           | StructFields { module, fields }
           | MatcherMapMiss
           | MatcherMapHit(ValueProof)
```

`ty` answers ordinary type questions through `Types`. `proof` lets the pattern
matcher and guard reducer prove branch selection after lowering has turned
patterns into tests and projections.

Tuple, map, and struct construction preserve proof per field. Each field starts
`Unproven` until that field has its own evidence. A tuple with one proven field
is not a proven aggregate; projection carries only the selected field's proof.

Maps use key-wise proof. A complete static-key map can prove a matcher miss for
an absent key. The private `MatcherMapHit` and `MatcherMapMiss` states feed the
lowered map matcher; ordinary map field typing still belongs to `Types`.

Structs use the existing schema and opaque implementation-target type for their
visible type. `StructFields` only records field proof keyed by schema field
name, so protocol dispatch and nominal checks still flow through `Types`.

## Call Targets

A call site first resolves its callable value to an `ActivationRequestSet`;
applying a request activates the target `FnId` with its full inference inputs.

```text
CallTarget::Direct(FnId)
  -> ActivationRequest { fn_id, inputs: args }

CallTarget::Closure { value, env }
  -> read closure literal type
  -> ActivationRequest { fn_id: closure target, inputs: captures ++ args }
```

Direct calls include protocol-dispatch stubs. For a protocol stub, the receiver
must be `Known`; the engine selects the single implementation whose target type
contains the receiver type and then activates that implementation callback.
`Pending` waits for another worklist pass, `Unknown` remains unknown, and
`NoReturn` contributes no call.

A closure's capture types are inference inputs because lowering puts captures in
leading body parameters. The callable surface is still only the explicit
parameters. Capture types are used to infer the closure body and are erased from
the callable ABI after this phase.

`ActivationRequestSet` is explicit even though current resolved targets are singleton.
That is the model slot for overloaded callable specs, union closure targets, and
polymorphic named references: one call site can select one or more requests, and
their returns join through the ordinary cell join.

## Specs

Declared specs are arrow sets. `declared_spec_result` instantiates each arrow
against the activation's known input types and unions the results of matching
arrows. It is used when body inference returns `Unknown`, which keeps inferable
bodies from being blunted by broader declarations. Arithmetic `Prim::BinOp`
uses the same declared-spec path by looking up the corresponding
operator-headed `Kernel` function.

That lookup is a real data-model dependency. Any transform that leaves an
arithmetic `Prim::BinOp` in a module must also preserve the matching
`Kernel.<op>/2` function and its declared specs. Removing that function while
keeping the primitive makes the post-transform module incoherent for
activation inference.

Spec application distinguishes three cases:

- A matching arrow yields a known result fact.
- An underconstrained arrow yields `Unknown`, because the solver lacks enough
  evidence to instantiate the scheme.
- Known inputs that still contain free type variables also yield `Unknown` when
  no arrow can be proven, because the solver has not proven an empty value set.
- Known inputs that are disjoint from every arrow yield `Known(none)`, because
  the declared callable cannot accept that activation.
- Known but overly broad inputs that intersect one or more arrows yield the
  union of those arrows' successful return types. Runtime values outside the
  successful arrows are a separate non-returning/error path, not part of the
  successful return.

Inputs that are still `Pending`, `Unknown`, or `NoReturn` preserve that solver
state. They are not coerced to `any` to make a spec match.

Scheme variables are allowed inside declared specs and callable arrows. Concrete
activation facts and codegen-driving facts may not publish free variables; they
must be known concrete types, boundary-erased dynamic values, or diagnostics.

## Operators

Operators are strict declared-signature applications. The runtime kernel
declares arithmetic operators as ordinary public operator-headed functions, so
`&Kernel.+/2` and the prelude-imported `&+/2` resolve to the same callable
surface. Each operator has one primitive body and four concrete arrows:

```text
(int,   int)   -> int
(int,   float) -> float
(float, int)   -> float
(float, float) -> float
```

Application follows the same solver states as any spec edge:

```text
Pending operand       -> Pending
Unknown operand       -> Unknown
matching arrow(s)     -> union of matching arrow returns
overlapping arrow(s)  -> union of overlapping arrow returns
no matching arrow     -> Known(none)
underconstrained spec -> Unknown
```

The engine does not collapse `int | float` to a hidden `number` rung, does not
carry an internal numeric operator table, and does not treat `any` as numeric
evidence. `any` can be an explicit top type at the boundary. Because it
intersects the integer/float arrows, an `any` operand contributes the union of
successful numeric returns while non-numeric runtime values leave through the
operator's non-returning error path. When a value-required operator proves
`Known(none)`, telemetry reports `fz.type_infer.diagnostic` with code
`type/invalid-operator` and the activation path stops at that statement.

## Pattern Matcher

The matcher consumes `Info` and proof, not private solver state. Lowered
predicate facts refine environments for the true and false arms:

```text
Eq / Neq
IsEmptyList / IsListCons
IsMatcherMapMiss
TypeTest
```

If refinement proves an arm impossible, that arm contributes `NoReturn` and
emits `fz.type_infer.dead_arm`. Returning siblings still determine the branch
result. If every reachable arm is non-returning, the function boundary can
settle to `none`.

The normal call-site spec is the shape the top of the matcher decision tree can
process. A singleton or structural proof can select one leaf. A live union may
select multiple leaves and join their returns. A catch-all arm can be source-total
and still dead for a particular activation.

## Worklist

`Solver` owns:

- `activations`: activation keys mapped to current `Activation { inputs, ret }`.
- `deps`: callee activations mapped to callers that read their return.
- `edges`: solved caller/callee activation edges keyed by structural callsite.
- `queue` and `queued`: activations scheduled for another body walk.
- `diagnostics` and `diagnostic_sites`: located type errors emitted through
  telemetry after the fixpoint.
- `dead_arms` and `dead_arm_sites`: matcher proof telemetry facts.

Applying an activation request records the caller dependency, creates the callee
activation if needed, and returns the callee's current return estimate. When a
callee return ascends, its readers are scheduled again.

The worklist terminates because every moving piece is monotone and finite height:

- Return cells only ascend from `Pending` into `Known` facts or to `Unknown`.
- Visible types widen through `Types::refine_widen`.
- Literal and recursive structure collapse through the finite refinement ladder.
- Operator returns are bounded by declared arrows and cannot carry unbounded
  operand structure forward.

## Tiny Walkthrough

```fz
fn pick(:left), do: 1
fn pick(:right), do: 2

fn main do
  f = &pick/1
  f.(:left | :right)
end
```

`&pick/1` is a zero-capture closure/named target. Calling it with the deliberate
union input creates one activation whose input can reach both matcher leaves.
The matcher joins `1` and `2`, then `refine_widen` returns visible type `int`.

Separate calls `f.(:left)` and `f.(:right)` are separate activations of the same
`FnId`; they do not force the function body to become one global monomorphic
cell.

## Proof Gates

Gate this model with:

- `cargo test --lib type_infer`
- `cargo test --lib invalid_named_reduce_reducer_emits_operator_diagnostic`
- `cargo test --lib matcher_dead_arms_are_observable_via_telemetry`
- `cargo test --lib fixpoint_leaves_no_reached_fn_unknown`

When a change crosses into production planning, add a production-pipeline test
that lowers or links through the public API and asserts observable telemetry or
executable return facts, not private solver internals.
