# Pattern Matching

Pattern matching has one decision model shared by function clauses, `case`,
`with else`, receive probes, and guard-compatible helper dispatch.
`SourcePatternRows` is row data over source patterns; `DispatchMatrix` owns the
questions, ordering, branch evidence, and executable `DispatchGraph`.

The pipeline is direct:

```text
source clauses
  -> SourcePatternRows
  -> PatternDispatchPlan
       graph: DispatchGraph
       payloads: outcomes, bindings, guards, pinned inputs, prepared keys
       graph payload: input_demand -- what the questions read of each input
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
  AST patterns into `RegionQuestion`s, consumes that temporary matrix into a
  graph, and stores pattern-specific payloads beside the retained graph as
  `PatternDispatchPlan`.
- `src/compiler2/jobs/body.rs` constructs inline outcome edges and their target
  signatures together; `jobs/native.rs` lowers the graph and its winning values.
- `src/ir_interp/dispatch_exec.rs` owns `Dispatch`, the interpreter's one
  dispatch door, for inline dispatch, function dispatch, guard helpers, callable
  construction and receive probes.
- `src/compiler2/native_codegen/receive.rs` emits the scheduler-facing receive
  probe function by walking the same plan.

Once a typed plan leaves its producer, `Rc<PatternDispatchPlan<Ty>>` is its
only retained representation. Inline control, receive control, call-edge
dispatch, and callable-construction selection all carry that same immutable
allocation through the artifact projections; cloning one retains identity, it
does not copy the graph or payloads. Native receive is the deliberate type
boundary: it maps that typed plan once to `RuntimeTypePredicate` and puts the
result in the scheduler-facing `Arc` receive term.

## Test First, Project Second

Constructor projections are valid only on a branch where the constructor test
has succeeded. The graph carries that rule structurally.

For `[head | tail]`, the dispatch asks `ListCons(subject)`. The success edge
projects `ListHead(subject)` and `ListTail(subject)`; the miss edge does not.
For tuples, `TupleArity(n)` dominates every `TupleField` projection. Where the
subject already arrives in field form -- a caller delivered the tuple as one
lane per field -- the arity is read from the transport shape and the projection
is a view over those lanes, so the domination is structural rather than a
runtime test on a heap value. A `Region::Type` over such a subject is decided the
same way, one question per position, through the predicate's own
`tuple_positions` decomposition. For maps,
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
- `pinned`: names the patterns reach for but do not bind, each with the span
  that reaches for it, how it reached (`^name`, a guard variable, a bitstring
  size), and the input that delivers it when the rows carry a prematch.
- `prepared_keys`: the heap values a map pattern is keyed by -- atom, binary or
  float -- which the graph names by id instead of spelling out, so one prepared
  key is one value however many questions ask it. Each door decides when to
  build them.

The graph carries one payload of its own: `input_demand`, a slot per declared
input saying what the plan's questions read of it. `input_demand` and
`required_input` on the plan are how every door asks.

## Pins Resolve Against The Prematch

A pin names a binding that existed BEFORE the pattern began. Three spellings
reach for one: `^name`, a guard variable the row's patterns do not bind, and a
bitstring `size(name)` no earlier field of the same bitstring binds. All three
become a `PatternPinnedInput` carrying a `PinnedKind`, which says what the
diagnostic has to say back: `Pin` names the pin and why it is undefined, and
the two spellings without a caret are `Variable`, an undefined variable.

`SourcePatternRows::prematch` is that snapshot, and it has two shapes.

- `Prematch::Lexical`, from `SourcePatternRows::lexical`: an enclosing scope
  holds the earlier bindings. `case`, `with`, `receive` and `cond` all match
  inside a body where that scope is live, as do the rows built to ask a
  question about patterns rather than to execute them. Each pin keeps
  `input: None` and travels to the lowerer, which resolves it by name.
- `Prematch::Inputs`, from `SourcePatternRows::entry`: the earlier bindings
  arrive as the leading inputs, and they are all there is. `entry_source_patterns`
  passes a lambda's captures paired with the input that delivers each; a `def`
  closes over nothing and passes an empty list. So `fn ^x -> ... end` pins the
  input that delivers `x`, while a `def` head can pin nothing at all.

`collect_pinned_names` resolves every pin against that snapshot, and
`pin_for_name` resolves the ones bitstring sizes create on first use. Under
`Inputs`, the producer then refuses every pin left unresolved — all of them at
once, in one `SourcePatternError::UndefinedPins`, because Elixir reports every
undefined name in a head rather than only the first. The diagnostics repeat
Elixir's wording: `undefined variable ^NAME. No variable "NAME" has been
defined before the current pattern` for a pin, `undefined variable "NAME"` for
a guard name or a bitstring size.

A reified guard helper is an ordinary function, so `guard_dispatch_from_surface`
builds its rows with an empty `Inputs` list and a pin in the helper's head is
refused while the helper's own plan is built. The diagnostic therefore lands on
the helper, which is the locus Elixir names too, not on the guard that calls it.

A lambda closes over the names its pins reach for: `lambda_free_names` collects
the free names of a clause's parameters against the empty pre-pattern scope
before binding them, so a pinned capture is captured. A bitstring size is the
exception — `collect_pattern_free_names` walks a field's value but not its size
expression, so a lambda whose field size names a capture does not yet close
over it.

Nested guard calls carry their own typed operand-binding edge, and a child
prepared key names a caller `PreparedKeyId`. The source constructor lifts child
keys into the parent's existing prepared operands, transitively through
helpers. Receive therefore prepares constants before parking, not while probing
messages. Only the root ABI decoder knows flattened offsets; child execution
receives its own plan-local bindings. Caller demand follows the call operands,
never child subject ordinals.
Named helpers have no implicit lexical capture edge. A helper body names either
something its own head bound or something that was never bound, and lowering
the body says which, so an unresolved helper name is a construction diagnostic
against the helper even when the caller has a same-spelled binding.

`graph.subjects` is the sole retained subject graph. Source-facing
`PatternSubjectRef` values exist only during construction. Bitstring field
subjects carry their exact extraction recipe: source, preceding field subject,
kind, size (including a dependent subject), endian, signedness, unit, and whether
the field is last. Shape questions reference those subjects; consumers do not
recover field meaning from an arm or field ordinal.
Edge evidence reveals only projected subject IDs; it stores no second copy of
their source or projection recipe.

Test builds retain the consumed matrix only as a compile-phase witness for
source-arm census assertions. Release `PatternDispatchPlan`s do not contain it
or map it across type handles.

The generic `DispatchMatrix` sees only regions and opaque outcome ids. Bodies,
receive wakeup behavior, and guard result interpretation belong to the producer.

## The Interpreter's Dispatch Door

`Dispatch` in `src/ir_interp/dispatch_exec.rs` borrows what deciding a plan
needs -- runtime, types, program, module, the plan, and its `DispatchOperands`
(transport, inputs, pins and prepared keys) -- and owns the subject state the
walk fills in. Every step of the walk is a method on it, so a question reads its
operands rather than being handed them, and a type test asks
`Types::runtime_type_predicate` through the same context instead of a closure
built per call. The lane-form decomposition (`TypeTest::matches`) and the
whole-value answer (`TypeTest::whole_value_matches`) are two methods on the
reader half of that context, borrowed apart from the subject state they are
asking about; `backend.rs` answers only what the representation owns, which
callable a code word denotes.

The subject state is one slot per subject the plan's graph declares, allocated
once for the run, beside a journal of the subjects written since the branch
point the test being walked opened. A test that misses clears the slots its
journal names and a test that matches keeps them, so the questions after a taken
branch read what it learned and nothing a failed branch produced outlives it.
`undo` drains only the writes the branch it closes made, so what an earlier
branch learned still stands. Reading a bitstring is why it has work to do: it
binds field by field and can still fail on a later field, and a bitstring field
is written only inside the branch of the shape test that reads it -- nothing
else produces one, since `resolve_subject` answers no such subject -- so the
fields a failed shape bound go with it. Every other slot the drain clears is
produced again from the operands when a later question asks for it.

`Dispatch::run` is the only entry. It consumes the run and answers `Ok(None)`
where no clause matched, an error where the plan and its operands disagree, and
otherwise a `Decided`: the decision as a value, holding both the winning outcome
and the run that produced it. A winning outcome's arguments are read through
`Decided::subject_word`, off the operands the decision was made on, so nothing
rebuilds them and no caller can ask a run that never decided what it bound. A
guard's nested dispatch runs the helper plan through the same door; a helper
that matches nothing is a guard that does not hold. `OutcomeId` is dense and
plan-owned: every retained target table is built in that order, validates one
slot per outcome, and indexes its winner directly. Entry dispatch therefore
routes an `OutcomeId` straight to `ExecutableDispatch::clause_index`; call
dispatch, inline dispatch, and receive route it to their own target slot. A
source `body_id` remains plan payload; it is not duplicated into a retained
reverse lookup authority for target routing.

`dispatch_values` builds the operands every door needs beyond its inputs, and
each door goes through it. Its `DispatchSource` says where those come from:
`Inputs` reads a pin from the ordinal the plan's prematch recorded out of the
decoded inputs and gets one empty cell per constant the plan's patterns named,
while `Bound` reads both out of the environment values a match site named. A
guard helper is the one exception to building: its prepared keys are its
caller's, named by position, because the source constructor lifted every child
key into the caller's operands, so the helper reads through the caller's cells.

A prepared key is built the first time a question reads it and kept for the rest
of the run. A binary key is a copy of its bytes onto the process heap, so a call
whose clause is decided before the map pattern is ever asked makes no copy, and a
key two questions read -- in one plan, or in a plan and the guard helper it calls
-- is copied once. Native lowering emits the same constant at the head of the
function it belongs to, which is one copy per call;
`fixtures2/behavior/map_key_unreached.fz` pins the interpreter's floor at zero
for that reason.

Only a map pattern's heap key is prepared. Every other constant a question
compares against is built where it is asked, through `dispatch_const_to_value`,
so a guard that compares a binary -- `when v == "key"` -- copies those bytes on
every evaluation of that guard.

Inputs are borrowed as decoded -- `None` for a semantic input the ABI published
no layout for. An input the plan's demand says it reads is refused before the
run; reaching one inside the walk stops the run naming the ordinal, so the two
readings of "did this input arrive" cannot disagree quietly.

## Lowering Sites

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

Each inline or receive target slot owns its `OutcomeEdge` target and explicit
`{ subject, parameter: ValueId, role: Semantic | Physical }` arguments. Its
index is the plan-owned `OutcomeId`; construction validates that alignment once.
Target parameters are constructed from that relation. Semantic typing and the
existing value-origin machinery borrow the owning body's plan and dispatch
inputs; keying, tuple/callable transport, and execution do not reconstruct
bindings by position or source spelling. Execution transfers the actual
successful state; native miss paths keep the pre-test state.

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
independent incoming or returned roots are used. Both questions -- where a value
is defined, and whether a use that can still happen wants it -- are answered
from the body's tables (see [pipeline](pipeline.md#function-local-control-is-an-entry-graph)),
so a decision costs a lookup rather than a search through the body. Unknown overlap stays
conservative; one-shot captures themselves do not split ownership. Receive arms
share their traced physical capture layout. The runtime guard and container/copy
publication rules live in [AnyValue's list ownership section](any-value.md#list-ownership).

## Guards

Guards compile into `PatternGuardExpr`. A pure helper call in a guard lowers to a
nested `PatternGuardExpr::Dispatch` whose `PatternGuardDispatch` contains a
full `PatternDispatchPlan` for the helper clauses plus one expression per helper
body. That helper is shared, not copied: the node holds an
`Arc<PatternGuardDispatch>`, so every reference to a helper — across guards,
across clauses and across caller plans — names the one artifact
`Job::ReifyGuardDispatch` built, and `World::guard_dispatch` hands out that same
pointer. The share is atomic because a plan travels between scheduler threads
inside `fz_ir::Term::ReceiveMatched`. Guard helper lowering tracks a call stack
and rejects cycles with `GuardCallCycle`.

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
