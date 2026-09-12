# Pattern Matching

Pattern matching has one decision model shared by function clauses, `case`,
`with else`, ordinary conditionals, lazy logical operators, receive probes,
and guard-compatible helper dispatch.
`SourcePatternRows` is row data over source patterns; `DispatchMatrix` owns the
questions, ordering, branch evidence, and executable `DispatchGraph`.

The pipeline is direct:

```text
source clauses
  -> SourcePatternRows
  -> PatternDispatchPlan
       matrix: DispatchMatrix
       graph: DispatchGraph
       payloads: outcomes, bindings, guards, pinned inputs, prepared keys
  -> inline lowering / interpreter execution / receive codegen
```

There is no production `Matcher` data model. Pattern code must not rebuild a
second graph shape to satisfy an old ABI. If a path needs matching semantics, it
should consume `PatternDispatchPlan` or the underlying `DispatchGraph` directly.

## Layer Ownership

- `src/dispatch_matrix/pattern/source.rs` owns AST-facing row data and diagnostics over those rows.
  It does not own executable matching.
- `src/dispatch_matrix/mod.rs` owns the generic dispatch model: `Region`,
  `Order`, `Outcome`, branch-local `EdgeEvidence`, and `DispatchGraph`.
- `src/dispatch_matrix/pattern.rs` owns source-pattern production. It converts
  AST patterns into `RegionQuestion`s and stores pattern-specific payloads beside
  the matrix as `PatternDispatchPlan`.
- `src/compiler2/jobs/body.rs` constructs inline outcome edges and their target
  signatures together; `jobs/native.rs` lowers the graph and its winning values.
- `src/ir_interp/dispatch_exec.rs` returns the winning outcome and successful
  subject state for inline dispatch, function dispatch, and receive probes.
- `src/compiler2/native_codegen/receive.rs` emits the scheduler-facing receive
  probe function by walking the same plan.

## Test First, Project Second

Constructor projections are valid only on a branch where the constructor test
has succeeded. The graph carries that rule structurally.

For `[head | tail]`, the dispatch asks `ListCons(subject)`. The success edge
projects `ListHead(subject)` and `ListTail(subject)`; the miss edge does not.
For tuples, `TupleArity(n)` dominates every `TupleField` projection. For maps,
`MapKeyPresent(map, key)` projects a map value only on the present edge, so a
present `nil` value and an absent key remain distinguishable.

For `%Box{value: x}`, the source producer asks `Region::Type` with Box's
atomic tagged-record `Ty`. Its success edge publishes a `StructField("value")`
projection; both a binding and a literal subpattern read that field subject.
The miss edge publishes no field access. Named fields resolve through the
runtime schema's named-field accessor; tuple offsets never establish struct
identity or field meaning.

`PatternResolver` supplies the source producer's two contextual answers:
struct types and guard-helper dispatch. Compiler2's `SourcePatternResolver`
uses the definition's World namespace and owner to resolve `ModuleTarget` to
`ModuleId`, then constructs the existing tagged-record type with unconstrained
fields. Definition diagnostics use that same identity resolver without needing
physical layout. Entry, guard-helper, and body jobs record the source pattern's
ordinary struct-reference and field obligations before executable planning.

This rule is the reason the matrix carries branch evidence rather than letting
lowering freely materialize paths from syntax.

## Pattern Payloads

`PatternDispatchPlan` keeps producer-specific payloads outside the generic
matrix:

- `outcomes`: body id plus source bindings for the winning row.
- `guards`: guard expressions and nested guard dispatch plans.
- `pinned`: `^name` inputs captured from the surrounding scope.
- `prepared_keys`: heap values, such as atom/binary/float map keys, materialized
  once outside the dispatch graph.

Nested guard calls carry their own typed operand-binding edge. A child pin
comes from an evaluated helper argument; a child prepared key
names a caller `PreparedKeyId`. The source constructor lifts child keys into
the parent's existing prepared operands, transitively through helpers. Receive
therefore prepares constants before parking, not while probing messages. Only
the root ABI decoder knows flattened offsets; child execution receives its own
plan-local bindings. Caller demand follows the call operands, never child
subject ordinals.
Named helpers have no implicit lexical capture edge: an unresolved helper name
is a construction diagnostic even when the caller has a same-spelled pin.

`matrix.subjects` is the sole retained subject graph. Source-facing
`PatternSubjectRef` values exist only during construction. Bitstring field
subjects carry their exact extraction recipe: source, preceding field subject,
kind, size (including a dependent subject), endian, signedness, unit, and whether
the field is last. Shape questions reference those subjects; consumers do not
recover field meaning from an arm or field ordinal.
Edge evidence reveals only projected subject IDs; it stores no second copy of
their source or projection recipe.

The generic `DispatchMatrix` sees only regions and opaque outcome ids. Bodies,
receive wakeup behavior, and guard result interpretation belong to the producer.

## Lowering Sites

- `if`, `and`, and `or` share a two-row constructor: a wildcard constrained
  to `false | nil`, then an unrestricted wildcard. Both rows inspect the same
  once-evaluated condition value. Their blocks are lowered once, and the mandatory
  miss is an inert Halt. A proven exhaustive plan does not semantically activate
  its miss. The reachability calculator narrows that original value
  separately in each arm; Return/DeliveredResume joins forward selected values.
- Multi-clause functions build one subject per parameter and route successful
  outcomes to `fn_clause_N` continuation functions. Exhaustion halts with
  `:function_clause`.
- `case` builds one subject for the scrutinee and routes outcomes to
  `case_clause_N`; exhaustion halts with `:case_clause`.
- `with else` dispatches the unmatched value through the same machinery.
- `receive` builds one subject for the candidate message. The receive term
  stores an `Arc<PatternDispatchPlan>`; the interpreter and native receive probe
  both run that cached plan against mailbox messages.
- Function heads retain their separate `bind_pattern` lowering until
  fz-5xp.56. Inline `case`, `with`, and `with else` outcomes do not re-walk
  syntax to bind values. Standalone asserting matches retain `apply_pattern`.

## Outcome Values and Retained Lists

Each inline or receive `OutcomeEdge` owns its outcome, target, and explicit
`{ subject, parameter: ValueId, role: Semantic | Physical }` arguments. Target
parameters are constructed from that relation. Semantic typing and the existing
value-origin machinery borrow the owning body's plan and dispatch inputs;
keying, tuple/callable transport, and execution do not reconstruct bindings by
position or source spelling. Execution transfers the actual successful state;
native miss paths keep the pre-test state.

Executable-local value origins, delivered joins, and runtime demand read
`ActivationAnalysis::reachable_entries`. An impossible arm contributes no
callable origin or capture demand. Function-level `InputDemand` still walks
the structural body because its input contract covers all specializations.

Receive origins terminate at `MailboxMessage(owner)`, not a fabricated caller
value. Semantic parameters project their types from mailbox `any` through the
winning plan's evidence. Native receive preserves subject-to-parameter identity
in its function ABI; pinned values and prepared keys are indexed by the plan,
never by source spelling. A sender-side winning probe copies only those exact
projected arguments, including physical sources, into the receiver heap with
one forwarding map. Misses and timeouts expose no outcome arguments.

A one-cons `List` construction may carry `ListRetention { source, permission }`.
The source is an ordinary traced physical operand through entries, captures,
and `Prim::MakeList`, not a head-to-source capability map. Identical head/tail
contents retain the source even when published. Changed contents require both
construction-owned `Rewrite` permission and a runtime unaliased cell; otherwise
they allocate. Body-local permission examines the existing origins and reachable
entry DAG: desired operands cannot retain the source, and no later competing
use may retain it. A live ancestor/equal path retains the cell; a strict descendant
does not reach its parent. Another construction's retention is an exact-cell
identity edge, not access to the source's old children. The result and its pure
projections are the new owner; exclusive arms may each receive conditional Rewrite.

Actual call arguments and tuple fields own `Transfer | Share` annotations.
Peer overlap and caller-retained semantic/physical sources force Share before
independent incoming or returned roots are used. Unknown overlap stays
conservative; one-shot captures themselves do not split ownership. Receive arms
share their traced physical capture layout. The runtime guard and container/copy
publication rules live in [AnyValue's list ownership section](any-value.md#list-ownership).

## Guards

Guards compile into `PatternGuardExpr`. A pure helper call in a guard lowers to a
nested `PatternGuardExpr::Dispatch` whose `PatternGuardDispatch` contains a
full `PatternDispatchPlan` for the helper clauses plus one expression per helper
body. Guard helper lowering tracks a call stack and rejects cycles with
`GuardCallCycle`.

Nested guard dispatch returns a boolean-ish guard value: no matching helper arm
means the guard fails, not that the surrounding match halts.

## Diagnostics

`src/dispatch_matrix/pattern/source.rs` uses the same producer for domain-free
coverage. It normalizes guards to `true`, compiles the rows to a
`PatternDispatchPlan`, and walks the `DispatchGraph`:

- `find_unreachable_rows` reports row body ids that no graph path reaches.
- `is_inexhaustive` reports whether some path reaches `Fail` for unconstrained
  inputs.

Declared function domains use the Types-backed reachability calculator after
both `FunctionContract` and `EntryDispatch` settle. Each `ContractArrow` keeps
its parameter row intact; the calculator evaluates that row against the shared
plan and the function is exhaustive only when every valid row makes `Fail`
unreachable. It does not union argument columns or enumerate products. Guard
tests remain conservative, so a guard-false path can still prove fallthrough.
Each row instantiates its arrow parameters through that arrow's bounds using
`Types::instantiate`. Dependent bounds close to a fixed point; unbounded or
cyclic variables remain polymorphic and therefore conservative.
The traversal keeps branch-local empty/cons facts beside the refined root
types. The list type lattice does not encode a minimum spine length, so a test
of a projected tail cannot refine its root; when that projection is already
known to be a proper list, however, `not empty` proves cons and `not cons`
proves empty. This makes zero/one/two-plus partitions exhaustive without
inventing a length type or treating a non-list domain as covered.
This deterministic closure belongs specifically to
`FunctionContract::input_domain_rows` for diagnostics. Ordinary dependent-bound
call matching is a separate unresolved path and must not be inferred from this
diagnostic behavior.

Definition-time diagnostics still walk function bodies immediately. Only a
declared function's head check is deferred to contract derivation. Functions
without contracts retain the domain-free check, and an empty contract produced
after a resolution error does not create a coverage domain.

Runtime-library helpers declare the exact producer-owned boundary they consume;
coverage does not infer a private helper's domain from whichever activations a
particular program happened to create. For example, `List.member?/2` accepts a
list and any search value, `Enum.member_result/3` accepts the two result variants
published by `Enumerable.member?/2`, and both `Enum.with_index_list` arities
accept lists. Their empty and cons clauses are therefore total without a
wildcard that would admit an impossible container or result variant.

Diagnostics should not reimplement matching with syntax walkers. If a warning
depends on dispatch reachability, ask the dispatch graph.
