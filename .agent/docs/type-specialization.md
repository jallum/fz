# Type Specialization

Use this before touching `src/type_infer`, the spike corpus in `spike/`, or
planner work that consumes inferred call/return facts.

## Model

Type specialization is a sidecar inference engine over the CPS-lowered
`Module`. It infers reachable function returns by running a monotone worklist
over call contracts:

```text
call contract = FnId + input ValueFacts
activation    = one inferred instance of that FnId at that input tuple
return fact   = activation-local Info cell
```

`FnId` is body identity. It is the target used by direct calls, closure bodies,
continuations, and protocol implementation bodies. It is not the inference
instance. The same `FnId` can have separate activations for `id(1)` and
`id(:ok)` without joining those callers into one monomorphic function cell.

Parameters do not own types and do not default to `any`. An activation supplies
the input facts. A return cell starts as `Pending` and moves upward only when the
body produces information. A declared `@spec` is a backstop for bodies the
engine cannot infer, not the primary source of a function's type.

The engine is implemented in `src/type_infer/mod.rs` and is exercised by
`cargo test --lib type_infer`. Production planning still owns executable plan
facts and codegen ABI shape.

The crate-visible API is intentionally small:

- `infer_return` runs one activation and returns its boundary-erased `Ty`.
- `infer_from_entry` runs the reachable activation graph from an entry point and
  returns a `TypeInferReport`.
- `TypeInferReport` exposes inferred returns by function name, unsettled
  activation names, and telemetry emission for diagnostics/dead arms.

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

Declared specs are arrow sets. `declared_spec_ret` instantiates matching arrows
against known input types and unions their results. It is used only when body
inference returns `Unknown`, which keeps inferable bodies from being blunted by
broader declarations.

No matching declared arrow returns `None` from the spec lookup, not `none`. The
lookup cannot prove whether the problem is an impossible call, an
underconstrained polymorphic scheme, or an unsupported matcher shape. The
activation therefore remains `Unknown` until body proof or a stricter diagnostic
path proves a contradiction.

Scheme variables are allowed inside declared specs and callable arrows. Concrete
activation facts and codegen-driving facts may not publish free variables; they
must be known concrete types, boundary-erased dynamic values, or diagnostics.

## Operators

Operators are strict signature applications. Numeric `+`, `-`, and `*` use the
four concrete arrows:

```text
(int,   int)   -> int
(int,   float) -> float
(float, int)   -> float
(float, float) -> float
```

Application is three-way:

```text
Pending operand -> Pending
Unknown operand -> Unknown
in-domain types -> union of matching arrow returns
out-of-domain   -> Known(none)
```

The engine does not collapse `int | float` to a hidden `number` rung and does
not use `any` as an internal fallback. A known operand outside every operator
domain is an illegal state. When such a value-required operation proves
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
- `queue` and `queued`: activations scheduled for another body walk.
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

When a change crosses from the spike into the production planner, add a
production-pipeline test that lowers or links through the public API and asserts
observable telemetry or executable return facts, not private solver internals.
