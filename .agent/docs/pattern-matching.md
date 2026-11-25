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
A cons is non-empty and says nothing of its terminator, so the test passes
improper lists too; `ListTail` of a list type is `cons(E, L) ∪ L`, where `E` is
its element type and `L` its terminator (`Types::list_tail_type`).
For tuples, `TupleArity(n)` dominates every `TupleField` projection. Where the
subject already arrives in field form -- a caller delivered the tuple as one
lane per field -- the arity is read from the transport shape and the projection
is a view over those lanes, so the domination is structural rather than a
runtime test on a heap value. A `Region::Type` over such a subject is decided the
same way, one question per position, through the predicate's own
`tuple_positions` decomposition. For maps,
`MapKeyPresent(map, key)` projects a map value only on the present edge, so a
present `nil` value and an absent key remain distinguishable. The key is a
`ComparisonValue`, the type an equality question compares against: a literal
(`%{name: v}`) or a pin (`%{^key => v}`), which looks the map up by the value
the pinned variable holds, in a `case`, a `receive` or a closure head. A
pinned key is read as a plan input like any other pin, narrows nothing about the map's type, and projects a value typed `any`.
A key that is neither is `SourcePatternError::UnsupportedMapKey`.
`fixtures/01767_a_map_pattern_looks_a_key_up_by_the_value_of_a_pinned_variable.fz`
checks the pinned form against Elixir on all three paths.

Compiled code decides a map-key question whose key is an atom or an integer
where the question stands. `WordKeyFind` (`native_codegen/clif.rs`) reads the
subject's header. For a flat map it compares the key's word against each
stored key word, then the stored key's kind. For a trie it hashes the key as
`TermHasher` does, an atom by reading the key hash its table keeps through
`Process::atom_key_hashes`, an integer by the finalizer, and walks the nodes
with a popcount at each (`docs/any-value.md`, the hash trie). Either way the
value's ref word is formed from its slot. A struct, a walk that reaches a
collision node and every other kind of key call `fz_matcher_map_get_ref`.
Function bodies (`Prim::MatcherMapGet`) and the receive matcher
(`emit_dispatch_map_get_value`) both go through it. The sequences are
`fz_flat_get` in `bench/maps/floor/flat.s` and `fz_trie_get` in
`bench/maps/floor/trie.s`;
`fixtures/01768_a_map_pattern_finds_a_one_word_key_in_a_small_map_a_large_map_and_a_struct.fz`
holds the three layouts and the value kinds to one answer, and
`fixtures/01771_a_map_pattern_finds_a_one_word_key_in_a_map_past_the_flat_limit.fz`
holds tries up to three levels deep, new atoms, both key kinds in one map, and
a receive.

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

## Both Sides Of `=`

`p1 = p2` in a pattern decodes to `Pattern::Both(p1, p2)`; each side is any
pattern, so `%{} = m`, `m = %{}`, `{a, _} = {_, b}` and `[h | _] = [_, x | _] = l`
all decode. Every consumer handles the two sides against the same subject:
the planner (`append_pattern`) appends both sides' questions and bindings on
one subject, the lowering of a pattern that asks nothing (`bind_unasked_pattern`) binds both from one source, and the
collectors of bound names, pins and requirements recurse into both. Function
heads, `case`, `fn`, `receive` and body matches share this path. Reachability
and the interpreter, native and receive doors read only the compiled plan, so
they see no `Both`. A variable that appears twice in one pattern is not tested
for equality.

## Concatenation Patterns

`src/compiler2/quoted_concat_pattern.rs` decodes `<>` and `++` in a pattern
into patterns the matrix already knows; no new row kind exists.

- `l <> r` flattens, through chains and nested `<<>>`, into one bitstring
  pattern. A literal operand is a binary segment sized by its byte length. A
  pinned variable is a binary segment sized `BitSize::ByteSizeOf(name)`: the
  byte size of the pinned value. The final name takes the rest as an unsized
  binary.
- `ByteSizeOf` reaches the matrix as `BitstringFieldSize::PinnedByteSize`, whose
  pin is delivered like any pin (lexical, or as a dispatch input when a lambda
  captures it). Each backend converts the pin to a size at match time through
  `fz_pinned_binary_segment_size`, which answers `u32::MAX` for a value that is
  not a byte-aligned bitstring, so the segment fails to match. The step path
  carries it as `LoweredBitSize::ByteSizeOf` and `BitSizeIr::ByteSizeOf`.
- `[a, b] ++ r` is `[a, b | r]`; the left side must be a literal proper list,
  `[] ++ r` is `r`, and a chain merges.
- A left operand of `<>` that is a bare variable or `_`, a non-binary operand
  of `<>`, or a left operand of `++` that is not a literal proper list is
  refused with `parse/concat-pattern-operand`, in Elixir's wording.

## A Bitstring Size May Be An Expression

`<<n, body::binary-size(n * 2 - 1), rest::binary>>` and
`<<head::binary-size(byte_size(p) + 1), tail::binary>>` parse to
`BitSize::Expr`: any guard expression other than a bare name (`decode_bit_size`
in `quoted_function.rs`). A bare name stays `BitSize::Var`, and a pinned
`binary` operand stays `BitSize::ByteSizeOf`.

- In a pattern, `bitstring_question` (`dispatch_matrix/pattern.rs`) compiles the
  expression with the same `guard_expr_from_ast` a `when` clause uses and
  stores it in the plan's `guards`; the field's size is
  `BitstringFieldSize::Guard(GuardId)`. Names an earlier field of the same
  bitstring binds are that field's subject; every other name is a pin, resolved
  like any size name. `collect_local_pattern_requirements` waits for the guard
  callees (`+`, `div`, `byte_size`, ...) a size calls, so a size may call
  whatever a guard may.
- Every backend evaluates the size with its one guard evaluator: the interpreter
  in `Dispatch::bit_size_value`, native dispatch in `lower_dispatch_bit_size`,
  and the receive matcher in `emit_dispatch_bit_size`. A guard that fails (a
  call that errors, an unbound earlier field) or a size the binary cannot hold
  is a miss of the whole bitstring test, as for a guard; the result narrows to
  `u32` like every other runtime size, so a negative size misses.
- The matrix charges a size guard's leaves like a guard's (`charge_guard`), so
  an earlier field the size reads is extracted even when no outcome reads it.
- In a construction, `lower_bitstring_expr` evaluates the expression into a
  value named by `segment_size(index)` before the segment's own value. That name
  stands for the size in the construction check (`construction_contract.rs`) and
  in the lowered `LoweredBitSize::Value`, so a negative size raises Elixir's
  construction `ArgumentError` through the same check a named size meets.

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

A clause becomes a dispatch row in one place, `compiler2::dispatch::surface_pattern_rows`:
its patterns after the leading inputs, one type precondition per annotated
parameter (the annotation resolved by `resolve_type_expr_body` and wrapped in
`runtime_type_test_envelope`), and its guard. `entry_source_patterns` and the
reification of a guard helper both take their rows from it, so a helper's
typed head asks in a guard the same type question a direct call asks. Both
wait on the same facts through `collect_annotation_requirements`: the
`TypeDefined` facts the annotations name and the `StructDefined` facts behind
any `%Mod{}` they spell.

An extern's entry row takes the same shape: wildcard patterns and one
precondition per fixed parameter, from the contract's entry domain
(`extern_entry_preconditions`), with no annotation to resolve. An unproven
argument that fails one raises the same `FunctionClauseError`. The test for a
`pid`, `ref` or `c_pointer` parameter admits every value, as it does for an
annotated parameter of an ordinary function.

A guard helper's clauses are kept as facts over the helper's own parameters
(`PatternGuardDispatch::facts`, built in `PatternDispatchProducer::finish` and
defined in `dispatch_matrix/pattern/unfold.rs`). A clause's facts are the
questions its patterns and preconditions ask, the residual guard expressions
that are not questions, and what it answers: `Holds` with the facts of its body,
or a refusal (`False` for a body that answers false, `Fails` for a body that
raises, `Either` when the cause is not kept). No name is matched, so `is_integer`, `is_function/2`,
`is_struct` and a user's own helper unfold alike.

In `PatternDispatchProducer::add_row` the guard's top-level `and` chain is read
left to right (`admit_guard`). A conjunct that calls a helper with every
argument a variable the row binds or a literal is replaced by the helper's
facts rebased onto the caller's subjects (`unfold_call`): its questions are
asked of the argument's subject, placed after the pattern and precondition
questions and before the guard, and a question already asked of that subject is
not asked twice. Its residual expressions stay the guard, with the helper's
parameters replaced by the arguments. A literal argument is substituted, a
conjunct made only of constants is evaluated on the spot (`evaluate`), and a
question about a literal is decided at once (`decide_at_constant`). A helper
that ignores an argument asks nothing of it. A clause whose body raises answers
false, as it does in the guard evaluator, where any failure fails the guard.

The call unfolds only when one clause can answer true for the arguments
(`resolve`). Two clauses that can both answer true, or a live clause that
follows a clause that conditionally matches and answers false or raises (only a
negation separates them), leave the call as the guard it is, with the helper's
own plan embedded. A conjunct that is not a call, a call under `or` or `not`, a
call with an expression argument, and one naming an unbound (pinned) variable
also stay guards. Names resolve through the same `bound` map the guard uses, so
the unfolded questions cannot disagree with the guard about which value a name
means. Every row source passes through `add_row`, so entry clauses, `case` arms,
`receive` arms and lambda clauses unfold alike, and the analysis reads an
unfolded question like a typed parameter's: the body narrows by it and an
activation whose type decides the clause skips the test.

A call that stays a guard inside a larger expression still makes its call, so
what it needs to answer at all is asked first (`ask_what_its_calls_need`): the
questions every clause that can answer asks, of a variable argument. `byte_size/1`
answers in its `when is_bitstring(bits)` clause and raises in the other, so
`def kind(b) when byte_size(b) > 1` asks `b` a bitstring before the guard, and
`kind(:a)` never reaches the body. A call is sure to be made at any depth of a
conjunct, under `not` and inside a comparison or another call's arguments, but
not under `and` or `or` within the conjunct, which may decide without their
right-hand side. A residual that is an extern call on a callable
(`is_function(f, 2)` leaves `fz_function_arity(f) == 2`) still reads the
callable whole, so the callable is constructed first-class.

A reified guard helper is an ordinary function, so `guard_dispatch_from_rows`
builds its plan with an empty `Inputs` list and a pin in the helper's head is
refused while the helper's own plan is built. The diagnostic therefore lands on
the helper, which is the locus Elixir names too, not on the guard that calls it.

A lambda closes over the names its pins reach for: `lambda_free_names` collects
the free names of a clause's parameters against the empty pre-pattern scope
before binding them, so a pinned capture is captured. A bitstring field's size
is walked too: a size name, or any name in a size expression, that the head does
not bind is a capture.

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
that matches nothing is a guard that does not hold, however deep in the guard
it was called. `OutcomeId` is dense and
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
of the run. A binary of 64 bytes or fewer is read-only data on every path, so
naming one as a key, or comparing against one in a guard, allocates nothing;
`fixtures/01542_map_key_unreached.fz` pins that at zero. A longer binary is
built on the process heap where it is asked.

Only a map pattern's literal heap key is prepared; a pinned key is already a
value. Every other constant a question
compares against is built where it is asked, through `dispatch_const_to_value`.

Inputs are borrowed as decoded -- `None` for a semantic input the ABI published
no layout for. An input the plan's demand says it reads is refused before the
run; reaching one inside the walk stops the run naming the ordinal, so the two
readings of "did this input arrive" cannot disagree quietly.

## Lowering Sites

- Multi-clause functions build one subject per parameter and route each
  outcome to its clause's body, which native code lowers as a block of the
  function that decides (see [pipeline](pipeline.md)). Exhaustion raises
  `FunctionClauseError`.
- `case` builds one subject for the scrutinee and routes each outcome to an arm
  entry. An arm has one way in, so native code lowers it as a block of the
  function that decides (see [pipeline](pipeline.md)). Exhaustion raises
  `CaseClauseError` showing the scrutinee.
- `pattern = value` is a one-row decision over the value
  (`Lowerer::lower_match`); exhaustion raises `MatchError` showing the value.
  In statement position the match reads as `case value do pattern -> rest
  end`: `Lowerer::lower_statements` hands the rest of the block to
  `lower_match`, whose single arm binds the pattern's names and runs the rest,
  and the arm's result is the block's result. A match that ends its block runs
  an arm that yields the value. A match whose value an enclosing expression
  consumes, such as `foo(x = 1)`, binds into the enclosing scope and yields the
  value. A pattern whose plan wins at its root, such as a bare name, binds
  directly with no decision.
- `cond`'s last condition, `and`, `or` and `not` are decisions over a value;
  exhaustion raises `CondClauseError`, `BadBooleanError` or `ArgumentError`.
- `with else` dispatches the unmatched value through the same machinery and
  raises `WithClauseError` when no `else` clause matches.

Each of these plans carries the exception it raises
(`PatternDispatchPlan::last_resort`); see
[exceptions](exceptions.md) for the table of what each prints.
- `receive` builds one subject for the candidate message. The receive term
  stores an `Arc<PatternDispatchPlan>`; the interpreter and native receive probe
  both run that cached plan against mailbox messages.
- Function heads, inline `case`, `with`, `with else` and `=` outcomes do not
  re-walk syntax to bind values: an outcome argument names the subject each
  bound name reads. Only a pattern that asks nothing is bound from syntax
  (`bind_unasked_pattern`): every name in it is the matched value itself.

## Outcome Values and Retained Lists

Each inline or receive target slot owns its `OutcomeEdge` target and explicit
`{ subject, parameter: ValueId, role: Semantic | Physical }` arguments. Its
index is the plan-owned `OutcomeId`. The pattern payload and every target record
derive that identity from their shared slot; none repeats it or validates a
parallel copy.
Target parameters are constructed from that relation. Semantic typing and the
existing value-origin machinery borrow the owning body's plan and dispatch
inputs; keying, tuple/callable transport, and execution do not reconstruct
bindings by position or source spelling. Execution transfers the actual
successful state; native miss paths keep the pre-test state.

Receive origins terminate at `MailboxMessage(owner)`, not a fabricated caller
value. Semantic parameters project their types from mailbox `any` through the
winning plan's evidence. Native receive preserves subject-to-parameter identity
in its function ABI; pinned values and prepared keys are indexed by the plan,
never by source spelling. `PatternDispatchPlan::outcome_roots` names, for a
clause's arguments, the *roots*: the outermost argument subjects on each
chain of tuple-field, struct-field, list-head and list-tail projections (a
bitstring field or a map value ends a chain and is its own root). Roots are
disjoint, and each argument is a root plus the path of projections below it.
The native matcher writes the roots to its `out` buffer, and a clause whose
roots are not its arguments in order gets a projector beside the matcher that
reads the arguments back out of the roots by those paths; the interpreter reads
the same table. A sender-side winning probe runs the matcher on the sender and
copies each root once, with no record of what it has copied, into a gift on the
sender's own heap; the receiver grafts the gift at its next dispatch and
projects its arguments from the roots it finds there. A pattern like
`[_, head | tail]` gifts the second cell alone, and `head` and `tail` are read
out of the receiver's copy of it. Misses and timeouts expose no
outcome arguments.

A one-cons `List` construction may carry `ListRetention { source, permission }`.
The source is an ordinary traced physical operand through entries, captures,
and `Prim::MakeList`, not a head-to-source capability map. A source that is
the decision's own input is that input value, captured by the arm like any
other value; only a subject with no value of its own in the deciding entry,
such as a projected tail or a received message, reaches the arm as a
`Physical` outcome argument. Identical head/tail
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
so a decision costs a lookup rather than a search through the body. A value that
several deliverers join (the arms of an `if` or `case`, or a call and a local
value) is one of the values they deliver, so it overlaps what one of them
overlaps, each judged by its own origin. A delivering call's result is a root of
its own, so an arm that raises holds nothing the program still uses, and an arm
that builds a value holds only what that value holds. Unknown overlap stays
conservative; one-shot captures themselves do not split ownership. Receive arms
share their traced physical capture layout. The runtime guard and container/copy
publication rules live in [AnyValue's shared lists and structs section](any-value.md#shared-lists-and-structs).

## Guards

Guards compile into `PatternGuardExpr`. A call in a guard resolves, through
`PatternResolver::guard_call`, to a `GuardCallee`: either a helper or an extern.
The callee may be named on a module alias (`Kernel.f(x)`) or on an Erlang-style
bare-atom module (`:erlang.binary_part(b, 0, 1)`): `Callee::for_call` resolves
both to the same exact callable. `binary_part/3` is guard-callable because
`:erlang.binary_part/3` clause 1 is one extern call, `fz_binary_part`, over
normalized bounds, and its other clause only raises.

`left in right` and `left not in right` in a guard are expanded by the quoted
expander (`expand_guard_membership`, rules in `source_sugar::rewrite_guard_membership`)
before decoding, as Elixir's `in` macro does: a literal list becomes an `or`
chain of `===` comparisons (`1 in [1.0]` is false), an empty list becomes
`false`, and an integer-literal range, with or without a step, becomes
`is_integer(left)` with bounds and, for a step other than 1 or -1, a `rem` test.
A right side that is neither stays `in` and fails as not dispatch-pure.

A helper call lowers to a nested `PatternGuardExpr::Dispatch` whose
`PatternGuardDispatch` contains a full `PatternDispatchPlan` for the helper
clauses plus one expression per helper body. That helper is shared, not copied:
the node holds an `Arc<PatternGuardDispatch>`, so every reference to a helper --
across guards, across clauses and across caller plans -- names the one artifact
`Job::ReifyGuardDispatch` built, and `World::guard_callee` hands out that same
pointer. The share is atomic because a plan travels between scheduler threads
inside `fz_ir::Term::ReceiveMatched`. Guard helper lowering tracks a call stack
and rejects cycles with `GuardCallCycle`.

An extern call lowers to `PatternGuardExpr::Extern { extern_fn, args }`. Every
extern is guard-callable. `Job::ReifyGuardDispatch` publishes the same
`GuardDispatch(function)` fact for an extern, holding a `GuardExtern` built from
the extern's settled wire, so a guard waits on the extern's `FunctionContract`.
`GuardExtern::new` admits parameters of class `I64`, `F64`, `Any`, `StoredValue` or `BinaryCursor` and a return
of `I64`, `F64`, `Any`, `Bool` or `Never`, either plain or `Checked` (an extern that
declares `raises:`); any other class (a binary, a pair, a variadic extern) is
refused with `GuardExternClass` where the node is made, so no evaluator is handed
a call it cannot carry. A `Checked` extern's failure is the guard's failure: the
clause does not match and nothing is raised. The three evaluators each handle the
node once:

- the interpreter's `eval_guard` calls `call_lowered_extern`, and
  `ExternCallValue::CheckedFailure` ends the guard with `DispatchStop::NoMatch`;
- native entry and case lowering (`lower_guard_extern`) emits `Prim::Extern`,
  declares the extern the first time a guard names it, and branches a `Checked`
  return's `failed` lane to the guard's failure block;
- the receive matcher (`emit_guard_extern`) carries an integer, a float, a
  reference word (`emit_receive_value_ref`) and a stored word with its kind
  (`receive_value_stored_parts`), and answers a `Bool` return as the
  atom `true` or `false`, and `emit_checked_return` branches
  the `failed` lane to the guard's failure block.

The arithmetic operators in a guard (`+ - * / %`, unary plus and unary minus) are calls, not
guard operators: `guard_expr_from_ast` resolves them through `guard_call_expr`
to the same Kernel functions a body calls (`BinOp::arithmetic_function`,
`CallableName::negation`; unary plus is the call `+/1`), so a program that imports its own `+` is answered by
that `+` in a guard as in a body, and a failed operation (overflow, `rem` or
`/` by zero) leaves the clause unmatched. `PatternGuardBinOp` keeps comparison
and boolean operators; `PatternGuardUnaryOp` is `Not`.

A helper's dispatch graph tests the clauses of every operand type, so a value
held unboxed in one scalar lane meets tests of other lanes. A test the lane
decides is answered without a branch: `emit_runtime_type_test` returns a
`TypeTestAnswer` (`Always`, `Never` or a flag), `RuntimeTypePredicate::
settled_for_scalar_lane` supplies the answer, entry dispatch
(`lower_dispatch_test`, through `scalar_lane_answer`) and the receive matcher
(`emit_test_edges`) lower only the live successor, and the readers of a wrong
lane (`as_raw_i64`, `as_raw_f64`, `receive_value_int`, `receive_value_float`)
refuse rather than reinterpret.

A list question (`Region::List`) of a value that cannot be a list is answered
`false` the same way: entry dispatch asks `value_may_be_list`, which is false for
a tuple held as lanes and for a variable whose type
`RuntimeTypePredicate::admits_a_list` refuses. A helper whose clause head is a
cons pattern, called with an integer, an atom or a tuple, therefore lowers only
its failure successor, and the cons clause's `ListHead` and `ListTail` projections
are never emitted for a value that is not a list.

`tests/guard_matrix_test.rs` runs 296 generated mixed-lane guard programs
(`tests/guard_matrix/programs.json`, with Elixir's answers recorded in it) on the
interpreter, the JIT and AOT; `tests/guard_matrix/generate.py` regenerates the
table, and the test's doc gives the command.

An extern whose return is `none` fails the guard and is not called. That is
decided by the declared return, not by a name: `Kernel.raise/2` reaches
`fz_panic :: none`, so a helper clause
`def tuple_size(_), do: raise(ArgumentError, "...")` makes the guard false for a
non-tuple and raises `ArgumentError` in a body. A call that can only abort is
one `PatternGuardExpr::Fails` node, made in `guard_expr_from_ast` for an extern
returning `none` and for a helper whose every body is itself `Fails`: the callee
is resolved before its arguments, so they are never built and no evaluator
lowers them. The walk that gathers what a guard function's reification needs
(`collect_requirements`, `jobs/dispatch.rs`) follows the same order: it asks
whether the callee only aborts (`only_aborts`) before it looks at the arguments,
so an aborting call's arguments may be anything, a struct literal or a call to
an impure function included, and name no requirement. A function's domain is
therefore written once, in its Kernel heads, and the extern under it is only
called inside the domain.

Failing is propagated to the guard, not to the helper: a helper that matches
nothing, or an extern that aborts, makes the whole guard false however deeply it
was called, so `not (map_size(x) == 0)` is false for a non-map. `and` and `or`
evaluate their right side only when the left leaves it open, in all three
evaluators. The Kernel functions a guard may call this way are `map_size/1`,
`tuple_size/1`, `elem/2`, `length/1`, `bit_size/1`, `byte_size/1`, `hd/1`, `tl/1`, `abs/1`,
`round/1`, `trunc/1`, `floor/1`, `ceil/1` and the `is_*` type tests; `is_tuple/1`
is a typed-head helper over `tuple`, like the other type tests, and
`is_function/1` is one over `fun`. `is_function/2` checks its arity first and
raises `ArgumentError` for one that is not a non-negative integer, so in a
guard such an arity makes the guard false; for a function it compares the
arity the closure header records (`fz_function_arity`). `abs/1` and the
float-to-integer conversions are typed heads over `Checked` externs
(`fz_op_abs_i`, `fz_op_round_f` and its siblings), so a result outside the
64-bit range fails the guard; their last clause raises `ArgumentError`, which is
the guard's failure for a non-number. `hd/1` and `tl/1` test the cell with
`fz_list_is_cons` in a clause guard and read it with `fz_list_head_ref` and
`fz_list_tail_ref`; a cons pattern in a helper head is not used there because
native entry-guard lowering does not carry one.
Unsupported guard expressions (a list or tuple literal, say) are still refused as
not dispatch-pure.

The receive matcher's `<`, `<=`, `>` and `>=` (`emit_ordering_cmp_value`) compare
two integers as machine words and ask `fz_value_cmp_ref`, the one dynamic
ordering a body and the interpreter use, for every other pair: a float, a mixed
integer and float, an atom against a number, or a value of unknown type. Two
values of unknown type first test both kinds and take the `fz_op_lt_bb`,
`fz_op_lte_bb`, `fz_op_gt_bb` or `fz_op_gte_bb` row for two binaries.

Its `==` and `!=` are the loose comparison (`emit_typed_eq_cmp` with
`Equality::Loose`): two integers or two atoms compare as words, two floats by
value, two binaries by the `fz_op_eq_bb` row (behind a test of both kinds), and every
other pair asks `fz_value_eq_widening_ref`, the comparator the
interpreter and body lowering use for the `==` operator, so `1 == 1.0` and
`0.0 == -0.0` hold. A pinned match and a literal pattern use `Equality::Strict`
(`fz_value_eq_ref`, with the same binary test), which tells `1` from `1.0`.

### Receive Guards Run On The Sender

A send to another process runs the receiver's parked matcher on the sender, so
the matcher's process argument is the sender and serves allocation only. A
guard therefore never asks it for identity. `lower_receive` hoists every
zero-argument call a receive guard makes (`hoist_zero_argument_guard_calls`,
`jobs/dispatch.rs`): the call becomes an ordinary call the receiver evaluates
before it parks, its result is bound to a generated variable, and the guard
reads that variable, which the plan pins like any guard variable the patterns do
not bind. A zero-argument call has no inputs but process state, so `self()` and
every other identity builtin reach the matcher as a pinned value in the park
record, and a constant helper such as `answer()` keeps its value. The
interpreter evaluates the same plan and reads the pin from the same slot.

Guards run on the sender under the probe, so they must be pure and non-faulting.
The exception-handling design (fz-sc8.9 and fz-sc8.24, PR #278) keeps guards
non-faulting, and gift-heap send depends on that.

`compiler2_receive_guard_zero_argument_calls_lower_to_pinned_values` pins the
lowered shape, and fixture 00904 pins the behaviour: a message carrying the
sender's pid misses and one carrying the receiver's pid hits.

## Diagnostics

A missing clause is not a compile-time diagnostic. A function or `case`/`with`
whose clauses do not cover every input compiles clean; an input that reaches
none of them raises `FunctionClauseError` or `CaseClauseError` at runtime, the
same exception Elixir raises for the same program.

What the compiler does flag at compile time is the opposite shape: a clause
that can *never* run because an earlier clause already matches everything it
could see. `src/dispatch_matrix/pattern/source.rs` finds this from the
compiled plan, not from a syntax walk. `find_redundant_rows_with_resolver`
takes the caller's own already-compiled `PatternDispatchPlan` for the real
rows — real guards, real annotation preconditions, nothing normalized away —
and walks the `DispatchGraph` to collect every body id some path still
reaches. A row whose body id is missing from that set is unreachable; its
`RedundantRow` also names the earliest earlier row (`always_matches`) whose
own coverage, once you replay just that prefix plus the redundant row, already
renders it unreachable on its own. Coverage only grows as earlier rows are
added, so the first prefix that reproduces the miss is the row responsible for
it.

Because the check runs on the real compiled plan, a guarded clause is never
mistaken for redundant — a guard always compiles to a real `on_miss` branch in
the graph, so a row behind a guard can still fall through to whatever follows
it — and a parameter annotation that actually partitions the input (`f(x ::
integer)` beside `f(x :: atom)`) is never mistaken for overlap either; each
clause's own precondition row is what the plan branches on.

`plan_entry_dispatch` (function clauses) and `compile_match_dispatch` (`case`
and `with` arms) each run this check once, right after their own plan
compiles, skipping it when there is only one row. The warning is
`type/redundant-clause`, worded the way Elixir words the same warning: "this
clause cannot match because a previous clause at line N always matches".

Diagnostics should not reimplement matching with syntax walkers. If a warning
depends on dispatch reachability, ask the dispatch graph.

A variable a clause binds and never reads warns `lower/unused-variable`, in
Elixir's words: "variable \"x\" is unused (if the variable is not meant to be
used, prefix it with an underscore)". A binding of a name already bound where
it is made (a rebinding match, a `case` clause over an outer name) carries
Elixir's other advice: "there is a variable with the same name in the context,
use the pin operator (^) to match on it or prefix this variable with
underscore if it is not meant to be used". A name that starts with `_`, and a
name a macro or the compiler wrote (any context but `nil`), never warns.

The question is one of scope, not of matching, and
`src/compiler2/jobs/scope.rs` answers it. `ScopeWalk` holds the function's
scoping rules once: every binding a head makes, with its span and whether it
shadows, and which binding each reference reaches. A head is one pattern: a
pin reads the scope before it, a name written twice is bound by its first
occurrence and compared by the rest, and a binary size reads a field bound
earlier in the same head. Lowering asks the same walk which names a nested
block, handler, `receive` or lambda reads from outside it (`free_names` and
its siblings), which is what each captures. `lower_function` asks it for the
unused bindings of each clause, judged on its own, and emits them through
`emit_warning_once`. Only a lowered function warns: a function the program
never reaches is never lowered, where Elixir warns for every function it
compiles. Fixtures `01304` through `01308` are the cases. A variable named
as a segment's size, in a construction or a pattern, is read there; `01821`
is the case.

## A rest that is only matched is a cursor

`<<..., rest :: binary>>` binds `rest` as the subject's source binary and the
bit position the fields before it end at. When `rest` is demanded `Matched`
(only matched again or measured with `byte_size`), no binary is built: the next
clause's reads and dispatch start at that position, a rest a dispatch matches
is held in its state as the same cursor, and a use that needs a binary makes it
whole. Interp, JIT and AOT agree. A sizeless last
`binary` segment holds whole bytes, so a `rest :: binary` that starts or ends
between bytes does not match: `field_end` in the runtime and the `Rest` arm of
native `BitFieldFits` both ask whether the bits that remain are a multiple of 8.
When the activation proves the rest whole, neither asks: the subject's type is a
subtype of `binary` and every field before the rest spans whole bytes (a sized
field whose size times unit is a multiple of 8, a `size(n)` field whose unit is a
multiple of 8, or a `utf8` field). `DispatchGraph::trimmed` records that in the
rest field's `rest_proven_whole`, `BitstringFieldShape::runtime_kind` then
answers `Bits`, and the interp dispatch, the native dispatch and the native
receive read that kind. Reachability decides it from every visit of the
bitstring test, so one visit that cannot prove it (an `any` or `bitstring`
subject) leaves the test in place.
A last `bits` segment takes whatever remains, and the value it binds is typed
`bitstring`. A cursor stands for the bitstring that remains from its position,
and `is_binary(rest)` answers whether those bits are whole bytes.

A binary literal in pattern position is a bitstring pattern with one literal
segment of its bytes and nothing after it. `""` is the zero-length binary
pattern: the pattern with no segments, which `<<>>` is. `"abc"` is the pattern
`<<"abc">>` is. `append_pattern` in `src/dispatch_matrix/pattern.rs` asks a
literal the questions of that bitstring (an exact size and the bytes at the
cursor, through `ast::binary_literal_fields`), so a subject that is a rest
stays a cursor and no constant is compared. A map-pattern key stays a literal
compared by value. Fixture `01707` walks a binary with each pair of spellings
and prints equal allocation counts.
