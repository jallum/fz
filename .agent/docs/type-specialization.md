# Type Specialization

Read this before touching `src/type_infer`, its colocated fixture corpus in
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

`FnId` is body/callable identity: the target used by direct calls, closure
bodies, continuations, and protocol implementation bodies. It is not the
inference instance. The same `FnId` can hold separate activations for `id(1)`
and `id(:ok)` without joining those callers into one monomorphic cell.

CPS lowering is what keeps this clean. Recursion, continuations, and closure
application are each a *separate* `FnIr`, reached through call-shape terminators
(`Term::Call`, `Term::TailCall`, `Term::CallClosure`, `Term::TailCallClosure`,
`Term::ReceiveMatched`). A body walk only ever touches its own blocks (a finite
intra-fn graph via `Term::Goto`/`Term::If`) and makes call requests at its
edges. Every inter-fn edge, including every loop back-edge, flows through the
activation table, never through the walk, so the recursion fixpoint lives
entirely in the worklist. The walk's own block-revisit guard returns `Pending`,
because an unfinished intra-fn loop has produced no fact yet.

The engine lives in `src/type_infer/mod.rs`, with model fixtures in
`src/type_infer/fixtures`, exercised by `cargo test --lib type_infer`. It owns
activation-based type flow; the planner owns executable plan facts and codegen
ABI shape and reads inference facts as input.

### Activation identity and convergence

An activation is keyed by its `FnId` plus a per-slot **identity class**
(`ActivationKey { fn_id, class_inputs }`), not by the raw input tuple. For each
entry-param slot the class is either:

- the exact input value, for a **dispatch subject** — a slot that can change
  which clause/branch the body selects or which callable it invokes; or
- the slot's `convergence_class` otherwise (a non-dispatch slot).

`FnIr::dispatch_subject_slots` computes the dispatch mask: a backward slice to
the entry params from every `Term::If` condition and every closure operand of
`Term::CallClosure`/`Term::TailCallClosure`, over the intra-body binding edges
(`Stmt::Let` operand uses and `Term::Goto` argument-to-param edges). It reaches
every entry param a control decision can depend on, never fewer.

Convergence applies **only to recursive fns** (`Module::recursive_fns`, the
SCC-based recursion notion the planner shares for recursive-key widening).
`Solver::is_dispatch_slot` returns `true` for every slot of a non-recursive fn,
and for a recursive fn returns the mask (defaulting to precise for unknown fns
and out-of-range slots), so convergence is a strict opt-in earned by both
recursion and a proven mask. For a recursive fn, two calls that agree on every
dispatch subject and on the *family* of each non-dispatch slot share one
activation; the exact non-dispatch types are recovered by joining the stored
inputs through `refine_widen` (`[] ⊔ nonempty_list(int) = list(int)`).
`Types::convergence_class` folds every pure list shape into one class and is the
identity otherwise, so an accumulator's emptiness×element cartesian product
stops forking activations — that product is the over-specialization balloon (see
`quicksort`'s `partition/4`). A cross-family non-dispatch difference (`int` vs a
tagged tuple `{:cont, int}`) keeps distinct classes, so a shape-changing
accumulator and its type errors stay observable. The input-join is idempotent —
equal slots stay byte-identical rather than passing through `refine_widen`,
which reconstructs a bare arrow and would erase a callable slot's
closure-literal identity. Non-recursive fns are never converged: their distinct
call sites are genuine per-callsite polymorphism. The planner consumes the
converged activations directly — `canonical_public_key` maps each narrow spec
request onto the single covering bucket, so no separate planner-side widening is
needed.

Parameters do not own types and do not default to `any`. An activation supplies
the input facts. A return cell starts `Pending` and moves upward only when the
body produces information. A declared `@spec` is a backstop for bodies the
engine cannot infer and the authoritative source for declared opaque/builtin
seams, including operator-headed kernel functions.

### Crate-visible API

The API is small. Activation ids are the production handoff identity: they name
one solved activation within an outcome without exposing the private proof
lattice.

- `infer_from_entry` runs the reachable activation graph from an entry point,
  returns `TypeInferOutcome { status, activations, edges, dead_arms }`, and
  emits telemetry.
- `TypeInferStatus` is the coarse result: `Complete`, `Unresolved`, or
  `Invalid` (`Invalid` whenever a diagnostic fired; `Unresolved` whenever any
  reached activation return is `Pending` or `Unknown`).
- `TypeInferActivationFact` is the data boundary for reached cells: an opaque
  per-outcome `TypeInferActivationId`, `FnId`, the activation's joined input
  `Ty`s (full arity), and a `TypeInferReturnState`.
- `TypeInferActivationEdgeFact` connects solved caller/callee activations and
  carries the structural `CallsiteId` plus callsite span metadata the planner
  uses to line solved edges up with its own dispatch slots.
- `TypeInferDeadArmFact` records matcher arms proved dead for a specific solved
  activation, keyed by activation id — not merely by `FnId`/block.
- `TypeInferReturnState` mirrors the settled boundary state: `Pending`,
  `Unknown`, `NoReturn`, or `Known(Ty)`. It is not the solver lattice; private
  `Info` owns refinement, and matcher proof is erased at this boundary.

Production consumers read these structured facts; telemetry is the shared
observable surface for tests and operators, not a place to rebuild planner
state. The engine emits:

- `fz.type_infer.activation` for every reached activation: function identity,
  the opaque activation id, return state, rendered return type, and in-process
  `Ty` data when known.
- `fz.type_infer.activation_edge` for every solved activation-to-activation
  edge: caller/callee activation ids and callsite slot/span details.
- `fz.type_infer.fn_return` for each reached function, joining known activation
  returns through `Types::union` and reporting whether any activation is
  unsettled.
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

ValueFact = { ty: Ty, proof: ValueProof }
```

The states are deliberately separate:

- `Pending` means a dependency has not produced its first fact (worklist
  latency).
- `Unknown` means a live value exists, but this engine cannot prove its type.
- `NoReturn` means a path contributes no value to the current continuation.
- `Known(ValueFact)` means a visible `Ty` plus optional proof.
- `Known(none)` is a proved contradiction: the value set is empty.
- `Known(any)` is a real top fact, not a placeholder for missing proof.

`Pending`, `Unknown`, and `NoReturn` are inference states, not public value
types. The reason they cannot collapse: conflating `Unknown` with `none` lets a
not-yet-computed continuation argument project to a field type and poison the
fixpoint. Projecting `Unknown` stays `Unknown` (we still know nothing);
projecting `Known(none)` stays `Known(none)` (a field of an uninhabited value
is itself uninhabited).

A settled edge that still carries `Pending` or `Unknown` is consumed explicitly
by a boundary decision: it may diagnose unsupported required knowledge or erase
a still-live dynamic value to `any`. The solver itself never uses `any` as the
placeholder for "not proven yet."

The planner boundary applies this when projecting activation facts onto
reachable executable entries. Semantic return truth and materialized executable
bodies are keyed by `BodyKey` (`FnId + input` slots); `SpecKey` adds the
planner-entry `ReturnDemand` (`BodyKey + ReturnDemand`). `ReturnDemand`
describes an edge ABI (`Value` or `TupleFields(arity)`); it is not a distinct
semantic return and does not create another body. For a polymorphic planner
key, compatibility is tested by instantiating the requested shape against the
concrete activation witness through `Types`; inference facts are not rewritten
into planner keys.

## Joins

Activation-cell updates and control-flow branch joins use one shape:

```text
join(Pending, x)         = x
join(Unknown, x)         = Unknown
join(NoReturn, x)        = x
join(Known(a), Known(b)) = Known(a.widen(b))
```

`ValueFact::widen` calls `Types::refine_widen` for the visible type and keeps
proof only when both sides carry the same proof. This gives the worklist a
finite ascending chain while preserving exact proof only where it is still
valid. When both sides share one pure product outer shape, `refine_widen`
performs the structural convergence there too: tuple fields, list
emptiness/element slots, resource payloads, arrow returns, and map fields
collapse recursively inside `Types`. There is one widen primitive; there is no
second structural-widen entry point.

`Unknown` is sticky because a live unknown arm is still live. `NoReturn` and
`Pending` are neutral because a non-returning path and a not-yet-produced
dependency each contribute no value.

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
patterns into tests and projections. A join keeps proof only when both sides
prove the same fact (`ValueProof::join`).

Tuple, map, and struct construction preserve proof per field. Each field starts
`Unproven` until that field has its own evidence; a tuple with one proven field
is not a proven aggregate, and projection carries only the selected field's
proof.

Maps use key-wise proof. A `complete` static-key map can prove a matcher miss
for an absent key. The `MatcherMapHit`/`MatcherMapMiss` states feed the lowered
map matcher; ordinary map field typing belongs to `Types`.

Structs take their visible type from the schema's opaque implementation-target
type. `StructFields` records field proof keyed by schema field name, so
protocol dispatch and nominal checks flow through `Types`.

## Call Targets

A call site first resolves its callable value to an `ActivationRequestSet`;
applying a request activates the target `FnId` with its full inference inputs.

```text
CallTarget::Direct(FnId)
  -> ActivationRequest { fn_id, inputs: args }

CallTarget::Closure { value, env }
  -> read closure literal type (closure_lit_parts)
  -> ActivationRequest { fn_id: closure target, inputs: captures ++ args }
```

Direct calls include protocol-dispatch stubs (`Module::protocol_call_targets`).
For a stub the receiver must be `Known`; the engine selects the single
implementation whose target type the receiver is a subtype of (mirroring
`ir_planner::walk::protocol_dispatch_key`) and activates that callback. A
`Pending` receiver waits for another worklist pass, an `Unknown` receiver stays
`Unknown`, and a `NoReturn`/absent receiver contributes no call.

A closure's capture types are inference inputs because lowering puts captures in
the body's leading parameters. The callable surface stays only the explicit
parameters; capture types infer the closure body and are erased from the
callable ABI past this phase. A known value that cannot resolve to a single
closure target stays `Unknown`, not `any` — `any` is earned by a boundary, not
asserted by the solver.

`ActivationRequestSet` holds a `Vec<ActivationRequest>` with a `singleton`
constructor. Every resolver yields one request, and `apply_requests` joins the
returns of whatever requests a site selects through the ordinary cell join, so
union closure targets and overloaded callable specs are a data-model extension
rather than another call path.

Extern arguments and selective-receive bodies seed activations through the same
machinery: an `Prim::Extern` argument that is callable is activated at an
`EmitSlot::CallableBoundary` callsite, and each `Term::ReceiveMatched`
guard/body fn is activated with opaque (`any`) message bindings followed by the
captured locals. The after fn binds no message, so it is activated with the
captured locals only. All of these returns are joined.

## Specs

Declared specs are arrow sets. `declared_spec_result` instantiates each arrow
against the activation's known input types and unions the results of matching
arrows (`apply_spec_set`). It runs when body inference returns `Unknown`, which
keeps inferable bodies from being blunted by broader declarations. Arithmetic
`Prim::BinOp` reaches the same path by looking up the corresponding
operator-headed `Kernel.<op>/2` function (`operator_spec_result`).

That lookup is a real data-model dependency. Any transform that leaves an
arithmetic `Prim::BinOp` in a module must also keep the matching `Kernel.<op>/2`
function and its declared specs. Removing the function while keeping the
primitive makes the post-transform module incoherent for activation inference.

`SpecApplicationOutcome` has three cases, and `declared_spec_result` maps them
onto cells:

- `Known` → a known result fact (the union of matching-arrow returns).
- `Underconstrained` → `Unknown`: the solver lacks evidence to instantiate the
  scheme, or known inputs still carry free type variables and no arrow is
  proven.
- `NoMatch` with free-variable inputs → `Unknown` (no empty value set proven).
- `NoMatch` with fully concrete inputs disjoint from every arrow → `Known(none)`:
  the declared callable cannot accept that activation.

Inputs that are `Pending`, `Unknown`, or `NoReturn` preserve that solver state;
they are not coerced to `any` to make a spec match.

Scheme variables are allowed inside declared specs and callable arrows. Concrete
activation facts and codegen-driving facts may not publish free variables; they
must be known concrete types, boundary-erased dynamic values, or diagnostics.

## Operators

The runtime kernel declares each arithmetic operator as an ordinary public
operator-headed function (`fn left + right` in `kernel.fz`) with four concrete
`@spec` arrows, so operator application is just a declared-signature spec edge:

```text
(integer, integer) -> integer
(integer, float)   -> float
(float,   integer) -> float
(float,   float)   -> float
```

`+`, `-`, `*`, `/`, and `%` each carry this surface. Application follows the
same solver states as any spec edge:

```text
Pending operand       -> Pending
Unknown operand       -> Unknown
matching arrow(s)     -> union of matching arrow returns
overlapping arrow(s)  -> union of overlapping arrow returns
no matching arrow     -> Known(none)
underconstrained spec -> Unknown
```

The engine does not collapse `integer | float` to a hidden `number` rung, carry
an internal numeric operator table, or treat `any` as numeric evidence. `any`
can be an explicit top type at the boundary; because it intersects the
integer/float arrows it contributes the union of successful numeric returns,
while non-numeric runtime values leave through the operator's non-returning
error path. When a value-required operator proves `Known(none)`,
`record_value_required_none` records a diagnostic, `fz.type_infer.diagnostic`
reports code `type/invalid-operator`, and the activation path stops at that
statement.

## Pattern Matcher

The matcher consumes `Info` and proof, not private solver state. Lowered
predicate facts (`PredicateFact`) refine environments for the true and false
arms:

```text
Eq / Neq
IsEmptyList / IsListCons
IsMatcherMapMiss
TypeTest
```

`narrow_predicate` builds the per-arm environment; `predicate_truth` may decide
an arm statically. If refinement proves an arm impossible, that arm contributes
`NoReturn` and emits `fz.type_infer.dead_arm`. Returning siblings still
determine the branch result. If every reachable arm is non-returning, the
function boundary settles to `none`.

A singleton or structural proof can select one matcher leaf; a live union can
select several and join their returns. A catch-all arm can be source-total and
still dead for a particular activation.

## Worklist

`Solver` owns:

- `activations`: `ActivationKey` → current `Activation { inputs, ret }`.
- `deps`: callee activation → callers that read its return.
- `edges`: solved caller/callee activation edges keyed by structural callsite.
- `queue`/`queued`: activations scheduled for another body walk.
- `diagnostics`/`diagnostic_sites`: located type errors emitted after the
  fixpoint.
- `dead_arms`/`dead_arm_sites`: matcher-proof telemetry facts.
- `dispatch_masks`: per-`FnId` dispatch-subject mask (`make_key` keeps masked
  slots precise and folds the rest into the joined `Activation.inputs`).
- `recursive_fns`: the fns convergence applies to.

Applying an activation request records the caller dependency, creates the callee
activation if new (or folds the call's non-dispatch inputs into the existing one
via `join_inputs`), and returns the callee's current return estimate (`Pending`
for a callee not yet processed). A widened input re-enqueues the callee — the
same monotone re-evaluation the return fixpoint relies on. When a callee return
ascends, its readers are re-enqueued.

Termination holds because every moving piece is monotone and finite height:

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
`FnId`; they do not force the body into one global monomorphic cell.

## Proof Gates

Gate this model with:

- `cargo test --lib type_infer`
- `cargo test --lib invalid_named_reduce_reducer_emits_operator_diagnostic`
- `cargo test --lib matcher_dead_arms_are_observable_via_telemetry`
- `cargo test --lib fixpoint_leaves_no_reached_fn_unknown`

A change that crosses into production planning earns a production-pipeline test
that lowers or links through the public API and asserts observable telemetry or
executable return facts, not private solver internals.
