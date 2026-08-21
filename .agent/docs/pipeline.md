# Pipeline: From Source To Artifact

The compiler turns submitted source plus a root request into a frozen,
backend-ready program — and touches only what the root reaches. This doc traces
that journey across direct fact producers and product-keyed artifact pulls. The
engine underneath is `fact-engine`; the semantic core is `semantic-fixpoint`.

## Identity first, work on demand

Referencing a module or an MFA allocates a stable id (`ModuleId`, `FunctionId`)
immediately; defining it later fills the slot behind that id. A function can be
*defined* without being *lowered*, *typed*, or *emitted*. Nothing past
definition happens unless a root reaches it, so an uncalled function stays a cold
definition fact and never grows an activation.

## Fact and product families

Fact families share one agenda; "stratum" is a write boundary, not a pass. The
artifact path for interpreter execution is product-keyed and request-local:
product producers return `ProductValue` or exact `PullWait`s, and the product
driver is the only code that expands product waits.

```text
source    IndexCode, ScopeCode, DefineModule, ExpandFunctionSource, DefineFunction
            parse/read quoted source, apply Fz.Compiler publication, stage demanded function bodies,
            define modules/functions -> *Defined facts
body      LowerFunction
            one demanded function -> LoweredBody (+ generated lambda defs)
            after this boundary compiler2 carries callable identity as FunctionId:
            unresolved local runtime names are fatal, while exact remote references
            survive only as interface-backed FunctionId expectations
dispatch  ReifyGuardDispatch, PlanEntryDispatch
            guard-pure helpers and clause matching -> GuardDispatch/EntryDispatch
macro     BuildMacroExecutable
            one demanded defmacro -> hidden macro root
            -> BackendProgram -> MacroExecutable
keying    DeriveRecursive, DeriveDispatchMask
            stable per-function facts used to canonicalize activation keys
semantic  SeedRoot, SeedActivation, AnalyzeActivation
            root entry facts, activation evidence, return types, callsite targets,
            callsite summaries, and executable demand
product   RootBackendProduct(root)
            final dense interpreter package for a root
          BackendExecutable(E)
            one symbolic backend executable
          AbiExecutable(E)
            ABI lanes, return delivery, entry captures, resumes, and callable entries
            for one executable
          MaterializedExecutable(E)
            one pruned body, selected call edges, local return/value types, and local
            transport positions
          ExecutableEffects(E)
            effect summary over the symbolic call-edge closure demanded by E
          RuntimeDemand(E), OutgoingInputEdges(E), IncomingInputSlot(slot)
            request-local representation demand and input-source accounting
          TransportShape(position), CallableConstruction(position)
            position-owned transport layouts and callable construction facts
```

The product inventory is not a root projection stack. A demanded executable forms
the product chain below, and each product can name only its exact product/fact
prerequisites:

```text
BackendExecutable(E)
  <- AbiExecutable(E)
     <- MaterializedExecutable(E)
     <- ExecutableEffects(E)
     <- TransportShape/CallableConstruction positions named by E
     <- RuntimeDemand(E), OutgoingInputEdges(E), IncomingInputSlot(slot)
```

`RootBackendProduct(root)` is the final assembly boundary. It keys the root
entry, pulls `BackendExecutable(entry)`, follows symbolic backend call edges and
positioned callable owners embedded in each reached backend product, assigns
dense executable indices, and publishes one `RootBackendProductAnswer`. That
answer owns both the symbolic `MaterializedTransportPlan` and the closed runtime
`BackendProgram`; runtime consumers project only the program. The product pull
path is the only artifact path.

A callable target keeps its exact private return layout. A first-class callable
wrapper publishes one uniform contract: `Diverges`, `Absent`, or one `ValueRef`
for every nonempty returning result. Native lowering decodes the private target
layout and materializes the public word once; no consumer derives a second
return contract from semantic types or target enumeration.

The planning artifact `../pull-based.html` documents the pull-based design
and remains available as a reference; this doc and `northstar.html` are the
durable source of truth for the pull artifact path as built.

`RootEntry.kind` decides where a root is allowed to go:

- `RootKind::Runtime` is a user/runtime entry request. It uses the submitted
  entry arity, rejects macro entry functions, and the interpreter front door
  pulls `RootBackendProduct(root)`.
- `RootKind::Macro` is a hidden compile-time entry request created only by
  `BuildMacroExecutable`. It uses the macro ABI input vector
  `__CALLER__ + captures + quoted args`, uses the legacy backend program path,
  and publishes `MacroExecutable(function)` for the macro expander.

## A root's journey

```text
submit_root(main/0)
  SeedRoot(root)
    publishes RootEntry, and once main is defined + key facts exist:
      Activation(root, main, []) , Executable(...)
  ProductDriver pulls RootBackendProduct(root)
    waits on settled RootEntry(root), Recursive(main), DispatchMask(main)
    pulls BackendExecutable(entry E)
      pulls AbiExecutable(E)
        pulls MaterializedExecutable(E)
          waits on settled ActivationAnalyzed(E.activation), ReturnType(E.activation),
          and local CallSiteSummary facts
          pulls RuntimeDemand(E), OutgoingInputEdges(E), and local TransportShape products
        pulls ExecutableEffects(E)
        pulls EntryCapture, resume, input, return, and callable-boundary transport products
      lowers one symbolic backend executable
    follows exact reachable backend products and publishes RootBackendProductAnswer(root)
```

Each fact wait names the exact prerequisite: `LowerFunction` /
`PlanEntryDispatch` / `DeriveRecursive` / `DeriveDispatchMask` run because a
product asked for a fact that requires them. New artifact producers must not
self-schedule or smuggle broad follow-up work into that path.

Root submission is not a source-publication phase. `submit_root` creates the
root query and enqueues `SeedRoot(root)` only. If the entry function is not
defined yet, `DefineFunction(entry)` waits on `FunctionSource(entry)` and
demands the code contribution whose indexed source surface can actually publish
that function. That source `ScopeCode` may wait on the runtime prelude's
`CodeScoped` fact, but the root never broadcasts `ScopeCode` across every known
code id. Unrelated submitted code therefore stays indexed-but-unscoped unless a
root, explicit demand, or active late-code path actually asks for its surface.

Macro executable readiness uses a hidden macro root and pulls the backend
product:

```text
demand BuildMacroExecutable(inc/1)
  waits for FunctionDefined(inc/1)
  creates macro root input [Any(__CALLER__), Any(x)]
  produces BackendProgram(macro_root) through RootBackendProduct(macro_root)
  publishes MacroExecutable(inc/1)
```

The macro root does not schedule `LowerNativeProgram`; compile-time macro
execution uses the backend interpreter over the quoted source heap.
`BuildMacroExecutable` does not wait with a producer list. If the macro root's
`BackendProgram` fact is missing, it directly invokes the backend product
producer and completes that exact product job's effects so the fact table sees
the published backend program.

`Fz.Compiler.define(source_root, __ENV__)` is the source-tier publication point
for definitions. It receives compiler-shaped quoted AST on the active source
heap and applies that root through the live `ScopeSession` in source order.
`FunctionSource(function)` facts are saved there as raw grouped quoted source;
downstream `DefineFunction` reads `ExpandedFunctionSource(function)` and does
not need to know whether the source root came from literal code or macro
expansion.

Names inside compiler-defined fragments are resolved through that same live
namespace. `defimpl` does not keep a second "local protocol names" side table;
its protocol and `for:` target references both resolve against the namespace
bindings already established by source-order publication.

Source publication expands only scope-shaping source: item macros and sibling
definitions that can change what exists in the surrounding scope. Ordinary
function bodies stay raw in `FunctionSource(function)`. When a caller later
demands that function, `ExpandFunctionSource(function)` recursively expands
body-local macros and normalizes source-only sugar on the same quoted heap
before `DefineFunction(function)` decodes the body. Function heads establish
identity and are not expression positions. Local macros, imported macros, and
required remote macros all converge on the same `MacroExecutable(function)`
fact. Exact `import/require ... only:` forms do not wait during scoping: they
reserve callable identity lazily by recording a module-interface expectation and
binding a `Callable` placeholder into the namespace immediately. `require`
also binds module-path visibility for the required name, but remote macro
permission is still tracked separately as selected macro `FunctionId`s; an
alias or other visible module binding does not authorize expansion by itself.
For dotted required paths, the spelled full path is visible through its leading
segment, and the short final segment is not implicitly aliased. A later job
waits only if it needs more than that placeholder. In practice that means
`ExpandFunctionSource(function)` waits on `FactKey::ModuleInterface(module)`
when a reserved exact callable must be classified as macro vs ordinary
function; once the interface settles, expansion either invokes the macro path
or leaves the call alone as runtime code. Exact `require ... only:` records the
selected remote macro expectations for the scope immediately, and
`define_module` / `define_module_interface` prove those expectations when the
provider surface settles, emitting the unknown-import diagnostic there if the
export never existed.

The recursive quoted-tree rewrite itself is single-sourced in
`src/compiler2/quoted_expander.rs`. Scope publication and
`ExpandFunctionSource(function)` choose different entry roots and different
post-expansion handling, but they do not carry separate walkers anymore.

Item macro calls are source-order work, not body-lowering work. The macro call
expands through `MacroExecutable(function)`, the returned compiler-shaped root
is read as a source fragment, and any function source inside that fragment is
published through `Fz.Compiler.define` with a projected `__ENV__`. Literal functions,
protocol callbacks, synthesized module-info functions, and explicit compiler
services all use that same publication event; module indexing does not have a
raw function-body capture side path.

## Runtime and built-ins are ordinary, lazy code

`Enum`, `Kernel`, and friends are not a special class and not a prelude phase.
The first reachable reference pulls the owning runtime module's source through
`ensure_runtime_module`, which submits it as ordinary code; the same
`IndexCode`/`ScopeCode`/`DefineModule` jobs index it. Unreached runtime
functions are never lowered. The prelude itself is just a namespace head saved
after bootstrap bindings — visibility, not a stage.

## Function-local control is an entry graph

`LoweredBlock { steps, result }` was enough for straight-line code plus a
special-cased `if`, but it was too weak for `case`, `with`, and `receive`.
Compiler2 now lowers one function body as:

- `LoweredClause`: head projections plus the `ControlEntryId` where the clause
  body starts
- `LoweredEntry`: one reusable local control node with `captures`, straight-line
  `steps`, and one `LoweredTail`
- `LoweredTail`: the only place control can branch, call, or return
- `ControlDestination`: either `Return` or `Deliver(next_entry)`

That makes local control explicit instead of positional.

- `ControlEntryOrigin::Clause` is a clause body entry.
- `ControlEntryOrigin::Branch` is a compiler-made join/arm entry.
- `ControlEntryOrigin::DeliveredResume { value }` is where a continuation-owned
  delivery seam resumes local work. Non-tail calls use it, and so does
  post-`receive` work once an outcome closure hands a value back into the entry
  graph.
  A delivered-resume entry can be structurally required by a reachable native
  call even when its lowered body is specialized away. Transport still publishes
  the resume payload ABI for that call target; backend may specialize the body
  to `Halt`, but it preserves the delivered-resume origin so native can build a
  well-typed continuation descriptor.
  The structural shape of a delivered DATA payload is owned by the PRODUCER: the
  callee's settled `ExecutableReturn` ABI. A destination-passing callee writes
  every field of its return into the caller's continuation, so the resume's shape
  is unioned with the callee return position and a field this caller ignores is
  never erased — the caller's value-demand may select the callable-boundary lane
  for a callable return, but it never drops delivered data structure.
- `ControlEntryOrigin::LocalResume { value }` is where local control like
  `if` or `dispatch` delivers a value without creating a callable
  continuation boundary.

So a non-tail direct call is not "call, then keep walking the remaining steps."
It is:

```text
entry N:
  steps...
  tail = DirectCall { ..., dest: Deliver(resume_k) }

entry resume_k:
  origin = DeliveredResume { value: v }
  captures = [...]
  steps...
  tail = ...
```

The backend and native jobs preserve this shape mechanically. They derive ABI
for resume entries, clause-entry helpers, and continuations from the same entry
graph instead of rebuilding hidden CPS structure from "tail position" guesses.
The backend interpreter preserves the same distinction: tail calls can park on
`receive`, and blocked tasks keep an explicit backend continuation stack so a
woken callee can still deliver into the caller's resume entry later. For the
compiler2 backend executable/entry seam, it now drives transitions from that
explicit resume state in a loop instead of re-entering through nested helper
calls.

Selective receive reuses the same delivered-resume model. A parked outcome
closure publishes whether the resumed body reaches the post-`receive` join
through its `outer_cont` or through an explicit continuation handoff, and
native codegen consumes that contract directly when it builds the parked clause
templates. That choice is derived from the reachable receive-outcome entry
graph, not from the first tail in the clause body, so branches and local
resumes cannot silently reclassify the join seam.

## The artifact boundary is product-keyed

`MaterializedExecutable(E)` is the first backend-owned product. It waits on
settled local semantic facts for `E.activation`, `RuntimeDemand(E)`,
`OutgoingInputEdges(E)`, and the transport shapes required by that local body.
It clones and prunes one body, freezes that executable's live callsites to
selected call edges, and records symbolic callee edges for later product pulls.
It cannot ask a new type question or discover a callee except through the
settled callsite facts for the activation it is materializing.

- If a local prerequisite is missing, it returns a `PullWait` for that exact fact
  or product.
- If a settled callsite is genuinely unresolvable, it is a fatal
  `incomplete-semantic-plan` diagnostic.

So semantic facts settle locally, then products consume those facts by key.
Growth across that line is represented by another named product/fact wait, not
by a root pass.

Backend-required transport positions wait for an actual produced
`TransportShape(position)`. Backend and ABI products consume layouts, so their
waits test the exact position product.
Product entries retain exact product generations and fact-use states. Producers
record dependencies at the read site; waits name those reads without restamping
or rereading the world. Scheduler movements are reconciled to their final exact
states before the next pull.

Outgoing input publication is request-local and order-free.
`OutgoingEdgeFrontier(root)` is the immutable set of executables whose
`OutgoingInputEdges(E)` product has actually been requested. Each outgoing
product is an immutable `InputSlot -> Set<IncomingInputSource>` contribution.
`IncomingInputRelations(root)` derives the immutable request-relative relation
for the exact current frontier generation. `IncomingInputSlot(slot)`
projects one exact value from it. Replacement, withdrawal, and equal reproduction use the
ordinary product-generation rules; there is no append-only call-edge inventory.

Each `TransportShape(position)` producer owns one exact answer. It reads the
position owner's `ExecutableFacts`, settled `RuntimeDemand`, and only the
upstream position products named by the normalized origin. `ExecutableFacts`
distinguishes direct call returns from public callable returns before transport:
direct returns refine from the selected target position, while public returns
project every nonempty result to `ValueRef`. Recursive position dependencies are
settled as one atomic product group from external anchors, so no member observes
a partial result. `CallableConstruction(position)` uses the same position-owned
layout and carries direct callable and boundary facts independently of wrapper
authority. A direct-only local producer owns `construction: None`; a first-class
producer owns `Some` with at least one exact executable member. There is no root
solve, component inventory, or absence-provenance side channel.

Closure-call materialization reads the callee's positioned transport carrier.
`ValueRef` calls through the public wrapper even when semantic resolution has
one target; target cardinality cannot turn a transported value back into a
private call. `Absent` leaves one exact target eligible for direct invocation
and cannot support a call without one exact target. Callable-construction
ownership remains the authority for wrapper construction and packaging, not for
rediscovering the invocation carrier. Public delivery names the caller-owned
`ReturnPayload` as its source and adapts it into the separate delivered-resume
destination.

World movements arrive from the scheduler as borrowed `FactMovement` values,
one exact final `FactState` per moved key. Product generations and reader edges
invalidate only products that consumed a changed fact or product. Equal
reproduction preserves generations, and unrelated products remain valid.

Runtime demand is what makes that line precise for *representation*. A semantic
fact — an activation, a callsite summary, an exact callable surface — is
evidence about what the program *means*; it is never an obligation to
materialize a runtime value. Representation is derived from
`RuntimeDemand(E)`: a value earns an ABI lane, a tuple earns field lanes, and a
callable earns a first-class boundary *only* when a settled product demand asks
for one. One shared boundary-transport model governs every runtime-carried
value — inputs, executable returns, delivered resumes, and closure captures all
draw their shape from the same demand-derived recursive layout family, so a
return can never collapse to a narrower vocabulary than an input.

The exact callable surfaces demand reads from live in
`CallSiteSummary.targets[*].surface_inputs`: that is the authority for which
callable shape a call actually uses, and it is small and executable-origin-aware
by construction — it names the surfaces a body proves, not every surface a type
permits. Recursive transport (nested captures, tuple fields, direct-callable
producers) is not stored on that witness; it is derived downstream from settled
demand into `TransportShape(position)` and related callable/boundary products.
Actual call-argument values also inherit the selected callee input demand during
transport projection, so recursive calls do not omit a local argument value just
because the caller's own `call_arg_demands` are temporarily bottom.
That inheritance uses the lowered call form, not arity alone: direct calls bind
explicit arg 0 to callee semantic input 0, while closure calls bind explicit
args after the callee capture prefix. Product runtime-demand pulls record the
same dependency edge (`callee RuntimeDemand -> caller RuntimeDemand`) so a
changed callee demand invalidates only the products that read it.

A callable surface that publishes a transport boundary names a runtime dispatch
site, so it must be **ground**: type variables are an inference-phase concept and
never reach a boundary. A first-class callable that escapes through a generic
parameter slot (e.g. `Enum.reduce`'s reducer, or the `Enum.with_index` mapper
threading through the recursive `with_index_list/3`) is analyzed against the
polymorphic template that slot is typed at *and* the concrete arrow a real call
instantiates — the template is not a distinct dispatch, so publishing a boundary
per surface would put several boundaries on one boxed value, which has exactly one
entry. `semantic::ground_dispatch_surfaces` resolves each surface to the ground
shapes the runtime invokes (templates replaced by their consistent-substitution
instantiations via `Types::key_list_subsumes`; a genuinely polymorphic escape
with no ground surface in the same carried demand or producer flow keeps its
template). It is the authoritative surface-set
operation, applied at the demand→representation seam — `CallableFlowFact`
first-class surfaces at construction and every callable axis at demand
finalization (`ExecutableRuntimeDemand::ground_callable_surfaces`) — so transport
never re-derives or relitigates the choice. The legacy root telemetry twins
`fz.compiler2.runtime_demand.defined` and `fz.compiler2.transport_flow.defined`
do not exist; the five distinctions
this model keeps separate — omitted lanes, tuple-field transport,
direct-callable transport, first-class materialization, and callable-entry
publication — stay individually observable through the demanded `RuntimeDemand`
product and the per-position transport products pinned in
`transport_contract_test.rs`.

A closure callsite's result is the producer fact
`TransportOrigin::ClosureCallReturn { callsite, callee }` — which callsite, and
which value is called; no judgment is baked in at collection. The claim is
decided at transport-recipe evaluation from the callee VALUE's own carrier —
the same fact `materialize_closure_call_edge` uses to choose the call form —
so claim and call share one authority (fz-9i4.4.5). An exact (non-`ValueRef`)
callee carrier with a settled singleton compiler-owned target lowers as a
direct edge, and the result aliases that target's own `ExecutableReturn`:
caller and callee read one fact and agree on the exact return lanes by
construction (three-level currying returns its nested closure as capture
lanes, no boxing). A `ValueRef` callee dispatches through its construction
wrapper, whose return is the public boxed contract
(`BackendCallableReturn::ValueRef`), and the claim stays public with it. Both
the callee-value shape and, when present, the singleton target's return fact
are recorded as position dependencies, so replacement or withdrawal of either
re-settles the claim.

A transport `ShapeId` is a faithful, total description of *physical runtime
layout* and nothing else. A boxed first-class callable's VALUE shape is
therefore one `ValueRef` value lane — the boxed pointer — and its width is a
single stable fact read identically by every carrier (function entry, closure
capture, continuation capture). The invocation contract (the observed surfaces)
is a property of the BOUNDARY the value is published through, not of the value's
identity: it lives on `BoundaryId` facts, not on the value shape, so two boxed
callables of the same value-lane repr share one shape regardless of surface and
dispatch by position + type. Fusing the contract into the value identity instead
fragments layout-identical pointers and forces out-of-band lane patching at each
carrier — the defect class behind a first-class callable captured by a non-tail
continuation arriving with zero lanes.

## Product inventory and fact taxonomy

`MaterializedExecutable(E)` is the first backend-owned executable product. It is
allowed to carry only local facts already proven by semantics:

- one pruned lowered body
- selected call edges
- return types and per-value types
- effect summaries
- frozen extern marshal classes

Transport planning owns physical layout before packaging:
`TransportPosition -> TransportLayout`, lane facts, callable and boundary
facts, call-result payload positions, and `CodegenSeamFact` rows. One
`TransportLayout` contains both structural shape and carrier presence; later
stages do not derive either component by rescanning semantic types or lowered
bodies.

`CallableFlowFact` is the semantic authority for one producer construction. It
keeps the producer's function and captures correlated with direct and
first-class surfaces, resolved members, and semantic input mappings. Transport
projects these facts and never recovers them from callable types or callsite
scans.

The next products narrow the contract:

- `ExecutableEffects(E)` derives local effects over symbolic call edges already
  present in the request-local session.
- `AbiExecutable(E)` reads `MaterializedExecutable(E)`,
  `ExecutableEffects(E)`, and the exact transport products for executable
  inputs, returns, entry captures, resumes, local backend values, and callable
  boundaries. It does not derive movement from root-wide demand state.
- `BackendExecutable(E)` reads `AbiExecutable(E)` and lowers one symbolic
  backend executable. Direct calls remain symbolic executable keys until final
  packaging.
- `RootBackendProduct(root)` traverses exact reachable `BackendExecutable`
  product values and packages them into dense `BackendProgram` indices and
  closed `BackendValueLayout` contracts. Its answer retains the symbolic plan;
  the program is the interpreter-ready projection.
- `NativeProgram(root)` is the native-specific projection above
  `BackendProgram(root)`: it carries direct executable bodies, clause helpers,
  continuations, construction wrappers, native body return contracts, and
  extern-marshal facts instead of rebuilt `ModulePlan`, `PlannedProgram`, or
  `AbiFacts`.

`RootBackendProduct(root)` preserves one `BackendConstructionWrapper` per
positioned owner whose exact product contains a first-class construction. It
does not reconstruct eligibility from the materialized publication-boundary
inventory. Boundary publication follows first-class callable surfaces,
independently of whether any member returns. The wrapper owns all
resolved members, retained captures, semantic input mappings, private member
layouts, member selection, and one public return form: `Diverges`, `Absent`, or
`ValueRef`. Every nonempty returning member adapts to that one public word;
mixed empty and nonempty returning members are invalid. The public form is not
copied from one private member or reconstructed from a semantic return type.

Construction identity is allocation-only. `MakeFnRef` or `MakeClosure` selects
the producer wrapper when the runtime object is created; the resulting code
pointer and environment are the callable's identity thereafter. Generic calls
do not carry a parallel construction ID or per-variable boundary table. Exact
calls may bypass the public object and use a member's private ABI.

Packaged call flow is `NoReturn`, `Tail`, `Continue { source }`, or
`Deliver { source, entry }`. Every settled-empty callsite or exact target
publishes `NoReturn` before physical packaging, including public indirect
calls. A local target's return endpoint must independently agree that it
diverges. `Continue` and `Deliver` carry the resolved source return layout; a
divergent target carries no delivery layout and creates no continuation. Native
callable wrappers likewise tail-call divergent members while returning members,
including returning zero-lane members, retain their return adapters. The caller
executable or destination entry already owns its layout. Native adapters
consume those contracts directly and never scan endpoints, positions, types, or
`World` to rebuild them. The backend interpreter follows the selected target's
`ControlDestination` only if that target returns.

Things that belong in Compiler2 artifact facts:

- selected call edges
- return delivery
- extern marshal classes
- effect summaries
- callable-boundary obligations
- settled clause-entry dispatch
- stable emission inventory
- native-codegen handoff facts derived from `BackendProgram`

Things that do not belong there:

- old `SpecPlan` as a backend artifact surface
- `SpecRegistry` or `SpecId` as semantic identity
- old `AbiFacts` sets such as `native_fns`, `cont_fns`, `cont_target_fns`, and
  `cont_extras_count`
- backend-specific callable wrapper signatures
- formatted telemetry payloads

Interpreter work should consume `BackendProgram`, and native work should
consume `NativeProgram`, not invent old planner/codegen state while wiring
JIT or AOT entry points.

Backend-facing product work has one hard rule after
`MaterializedExecutable(E)`: it may read only exact prerequisites named by the
requested product.

- `MaterializedExecutable(E)` may consume only settled local semantic facts for
  `E`, `RuntimeDemand(E)`, `OutgoingInputEdges(E)`, and local transport shape
  products.
- `ExecutableEffects(E)` may consume only materialized executables reachable
  through symbolic call edges already recorded in the request-local session.
- `AbiExecutable(E)` may consume only `MaterializedExecutable(E)`,
  `ExecutableEffects(E)`, exact transport products, and the world-owned type
  store.
- `BackendExecutable(E)` may consume only `AbiExecutable(E)` and its embedded
  positioned transport answers.
- `RootBackendProduct(root)` may consume only `RootEntry(root)`/entry key facts
  and exact `BackendExecutable(E)` products reached through their symbolic call
  edges and positioned callable owners.

If backend code needs to ask semantic, reachability, callee-selection, or
type-inference questions after that line, the product contract is incomplete or
the consumer is violating it. The fix is to publish or pull the missing named
fact/product, not to scan semantic state.

## Native codegen contract

`NativeProgram(root)` is the last Compiler2-owned artifact before JIT/AOT
consumption. Native codegen is allowed to ask only backend-consumption
questions at that rung:

| Old shared-native input | Compiler2-native answer |
| --- | --- |
| prepared `Module` | `NativeProgram.module` |
| executable / helper inventory | `NativeProgram.entry` plus `NativeProgram.bodies[*].fn_id` and `origin` |
| `ModulePlan.effective_returns` and `fn_effects` | `NativeBody.return_ty`, `return_reprs`, and `effects` |
| `SpecPlan.vars` type queries | `NativeBody.value_types` |
| `PlannedProgram.callable_entries` | `NativeProgram.callable_boundaries` |
| callable-boundary lookup through planner state | `MakeFnRef` / `MakeClosure` `identity_fn` resolved against `NativeProgram.callable_boundaries` |
| extern decls plus wire classes | `NativeProgram.module.externs` plus `NativeBody.extern_marshals` |
| continuation / entry ABI classification | `NativeBody.entry_abi` and `NativeBodyOrigin::Continuation` |
| runtime type-membership questions | explicit `RuntimeTypePredicate` facts |

Questions that are illegal after `NativeProgram(root)`:

- reading `ModulePlan`, `PlannedProgram`, `SpecPlan`, `SpecRegistry`, or
  `AbiFacts`
- asking reachability, callee-selection, or semantic-closure questions
- re-deriving callable-entry obligations, return lanes, or extern marshal
  classes from old-world planner state

Compiler2-native no longer carries copied planner-shaped baggage
(`SpecPlan`, `SpecRegistry`, synthetic `SpecKey`, widened `return_tys`) as part
of its backend handoff. Runtime type-membership questions now cross the handoff
through explicit `RuntimeTypePredicate` facts: compiler2 keeps rich semantic
`Ty` facts for dispatch/refinement above the seam, then projects them into the
runtime-observable predicate model the runtime can actually answer below it.

Shared `ExternDecl` carries only ABI-facing metadata after `NativeProgram(root)`.
Semantic extern facts stay in compiler2-owned structures: `LoweredExtern`,
backend program facts, and `NativeBody.extern_marshals`.

The same rule applies to native return delivery. `NativeBody.return_reprs` is
the published result contract for a native body. Native lowering consumes the
packaged `BackendReturnFlow`; `NoReturn` emits a tail call without a
continuation, while `Continue` and `Deliver` carry their resolved source layout and
the caller executable or destination entry owns the other side of the adapter.
Codegen does not rediscover ABI at individual tailcall or callable entry sites.

The same two-layer split now applies on both sides of the migration seam:
legacy lowering may still project legacy `Ty` handles into
`RuntimeTypePredicate` for cached receive dispatch while that world exists, but
the shared runtime predicate itself is first-class and is not a second semantic
type system.

Current conclusion from the code:

- no missing closed fact has been identified for the current compiler2-native
  codegen inputs
- the compiler2-native JIT fixture tests now consume `NativeProgram(root)`
  through the compiler2-owned backend path directly
- `Compiler2::compile_root_jit`, `run_root_jit`, and `compile_root_aot` now
  consume that same compiler2-owned backend path directly, using the world's
  interned type store instead of a fresh legacy one
- the native/JIT/AOT front doors reach `NativeProgram(root)` through the same
  product boundary as interp: `native_program_for_root` runs the single demanded
  `LowerNativeProgram(root)` job, which builds `BackendProgram(root)` via the
  product driver (`build_backend_product`)
- `fz2` is now the side-by-side outer shell for those front doors: `fz2 run`,
  `fz2 interp`, and `fz2 build` submit source directly to Compiler2, seed
  `main/0`, and never reopen old planner or type-infer work; `fz2 test`
  submits the same way but seeds one root per discovered `test(:name) do ...
  end` item instead of `main/0`, running each in its own subprocess
- the old `fz` surface is retired; new compiler-facing work enters through
  compiler2 APIs or `fz2`

## Redefinition retracts by ownership

Redefinition is not a special path; it falls out of owned-output replacement.

```text
redefine main to drop the qsort call
  FunctionDefined(main) changes -> LowerFunction(main) -> LoweredBody(main)
  AnalyzeActivation(main) re-runs, stops contributing Activation(qsort,...)
    qsort had only main as caller -> slot empties -> Activation(qsort) retracts
    AnalyzeActivation(qsort) wakes, no input -> drops its outputs
      Activation(partition), Activation(append) lose their owners -> retract
  the next RootBackendProduct(root) pull asks only for products still reachable
    through the new settled local call edges
```

The blast radius is exactly the dependency chain, propagated by fact ownership.
A function that was defined but never reached is untouched: redefining it changes
its definition fact and wakes no semantic work for that root.
