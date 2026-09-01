# Dispatch Matrix

`src/dispatch_matrix` is the shared model for source-pattern and type-directed
dispatch. Function heads, `case`, `with else`, selective receive, guard helper
dispatch, and protocol finite-union dispatch all build a `DispatchMatrix`,
compile it to a `DispatchGraph`, and let producer policy decide what a winning
outcome means. `SourcePatternRows` normalizes AST patterns into rows, but the
runtime decision graph for source patterns is owned by `DispatchMatrix`.

The model names four separate concepts so dispatch work does not grow new
subsystem-specific cascades:

- `Region` is the value-space question an arm asks of a subject: type,
  constructor shape, equality against a literal or pinned value, map-key
  presence, bitstring shape, or a guard predicate.
- `Order` is why an arm wins when regions overlap: source order, type
  specificity, or an explicit materialized order.
- `Outcome` is an opaque handle chosen after an arm wins. Pattern bodies,
  receive accept/reject behavior, protocol direct calls, fallthroughs, and halts
  stay outside the region model.
- `DispatchGraph` is the executable decision shape: tests route to nodes, and
  successful edges carry branch-local proofs and projections.

`compile_dispatch_matrix` is pure and side-effect-free. It compiles ordered arms
into a deterministic graph and returns `DispatchCompileStats` so tests can assert
shape signals such as test count, fallback count, and shared-prefix tests without
depending on formatted graph dumps.

`compile_dispatch_matrix_with_type_order` handles `Order::Specificity` for
type-region arms. It uses `Types` operations only: pairwise relations are
`Equal`, more-specific, less-specific, disjoint, or ambiguous overlap; ordering
puts strict subtypes before supertypes while orthogonal arms keep deterministic
identity order. Equal-overlap handling is producer-policy driven: a producer can
classify equal regions with different outcomes as duplicate coverage or as an
ambiguity. `analyze_type_coverage` computes covered and residual receiver
domains, distinguishing closed coverage from open residuals.

Protocol call dispatch is callsite-owned in compiler2. `jobs/semantic.rs`
settles each callsite as a `CallSiteSummary` with one `CallTargetSummary` per
viable impl target. `compiler2::callsite_dispatch::call_destinations` is the one
door from that summary to what the call actually is: it answers
`CallDestinations::None`, `::Direct(target)`, or `::Dispatch(plan + targets)`,
and materialization follows the answer. The plan is a `PatternDispatchPlan<Ty>`
built from the receiver-narrowed `CallTargetSummary.surface_inputs`, with opaque
body ids assigned to the destinations in order.

A settled target is not automatically a destination. An arm asks its question
through `RuntimeTypePredicate`, which is coarser than the type it is projected
from: `{:cont, pair}` and `{:cont | :halt, pair}` both project to "a 2-tuple".
Two targets that project to ONE question are not two alternatives — nothing but
their order would decide which body runs, and that order is the scheduler's. A
target is therefore dropped when a sibling both (a) is runtime-indistinguishable
from it and (b) *stands in for* it: names the SAME callee and accepts a strictly
wider domain. A callsite left with one destination is a `Direct` call rather
than a one-armed dispatch.

(b) is judged on the OBSERVABLE surfaces — the settled `surface_inputs` run
through `Types::runtime_type_test_envelope`, which is the same projection the
plan's rows are built from — not on the settled semantic types. The envelope
erases what no runtime test can read back off a value: a callable argument
keeps its literal `fn_id` and loses its arrow and its captures, because a
closure object's heap word at `+8` is the code it was minted from and nothing
else about it survives into the value.

A callable position is therefore a real question, and it is what separates
`Range.reduce_step/6`'s `({:cont, int} | {:halt, int}, #66closure[])` from its
`({:cont, int}, #68closure[])` sibling. Both project to "a 2-tuple" at the
state column, so before the callable axis existed the pair asked one question,
neither arm contained the other, and `:halt` was one legal arm order away from
being read as a continue. Now each arm is reached by the values its own reducer
travelled with. What the callable axis does NOT reach is one callable at two
capture layouts: `#66closure[int]` and `#66closure[float]` are one code
pointer, and the capture record the runtime could read back is not on this axis
(fz-kdt.127).

Dropping does not decide a routing. Every question an indistinguishable
group's rows ask projects to one and the same `RuntimeTypePredicate` — the
rows still carry distinct observable types and the plan still emits a test per
row, but no test it can emit separates the group, so the member the graph
reaches first receives every value the group can see — one member was going to
get them all whatever the arrival order. The rule only decides WHICH: the
survivors are the maximal elements of the observable containment order,
computed order-independently. Where one maximal member exists it is the only
choice complete on every axis a runtime test can see; where two maximal arms
are incomparable both stay and that pair remains order-decided (this corrects
fz-kdt.104's inherited "unique maximal survivor" phrasing — uniqueness holds
per containment CHAIN, not per question class). Every routing reachable after
the drop is one some legal arm order already produced, which is what makes it
safe; what it removes is the dependence on that order. Two adjacent facts
close the loop: a drop to a single destination converts the plan to a
`Direct` call, which also removes the plan's fail node — a value outside
every arm's observable domain would have trapped at base and now routes to
the survivor; that conversion is fz-kdt.104's pre-existing `sole_destination`
and is fenced by the semantic analysis, not by this rule. And a drop cannot
ground a call it should not: `call_destinations` has exactly one consumer, at
artifact materialization — the semantic fixpoint, `RuntimeDemand`, and
transport never read it, so dropping an arm cannot shrink a
`CallableDemand.targets` count or manufacture a `CallEdge::Direct`.

Both halves of (b) are load-bearing. Domain containment alone is not behavioral
completeness — a multi-target summary normally names one target per selected
callee, which is exactly what protocol dispatch is, and a wider domain sitting
on a different function's body is no stand-in at all. And one-way containment is
not (a): when the questions differ the plan CAN separate the pair, so both
survive. What separability does not buy is order-independence. A test is coarser
than the surface it was projected from, so a value can pass an arm's test
without belonging to the domain that test was projected from, and seating
decides which arm receives it — order costs meaning wherever two tests overlap,
and that is fz-kdt.107's subject one rung wider than the arms asking ONE
question. (fz-kdt.129 corrects the "order costs precision, not meaning"
phrasing this paragraph inherited; the measurement is under *Seating*.) A
`:timeout` arm beside an `any` arm is the benign case — the atom test is exact,
so nothing but a `:timeout` passes it — and the narrower TEST is seated first.

Twins with no stand-in between them (neither observable domain
contains the other, or two different functions) also survive and stay
order-decided — including arms alike everywhere the runtime CAN look and
different only where it cannot, where containment is mutual and strictness
keeps both.

That surviving order-decided residue is a live wrong answer, not a tolerated
imprecision: a body specialized on a closure literal can ground a DIRECT call
to it (`exact_direct_callable_layout` → `TransportCarrier::Absent` →
`materialize_closure_call_edge`), so a sibling's closure routed into it never
runs. Keeping the dead arm does not prevent that — the plan has no question to
separate them either way. See fz-kdt.107 and fz-kdt.125.

Arm order is the scheduler's, so any permutation of a callsite's targets is an
order the fixpoint could have delivered. `arm_order_stress` makes that testable:
`FZ_STRESS_REVERSE_DISPATCH_ARMS` (or `ReversedArmOrder::install()` in-process)
reverses each runtime-indistinguishable group, and
`compiler2_dispatch_answers_the_same_under_a_reversed_arm_order` holds the
fixtures that carry such groups to one answer under both orders.

## Seating

Which arm is tested first is therefore not read off arrival alone.
`specificity_order` starts from arrival order and corrects it wherever the arms
themselves say it is wrong.

### What a seat can get wrong

An arm's `RuntimeTypePredicate` is COARSER than the surface its body was
compiled for: list shape erases the elements, tuple arity erases the payloads.
So a value can satisfy every question an arm asks and still lie outside that
arm's surface, and seating that arm first routes the value into a body whose
representation never named it — `fz_list_head_int_ref` reads a list of atoms as
a list of ints and aborts on the JIT and native doors, while the interpreter's
dynamic tags hide it.

Call that a BLIND ESCAPE: `early` is seated before `late`, and at some position
the two tests both admit some value on an axis whose projection erases what the
bodies read, while `late`'s surface holds values `early`'s does not. Two orderings were built on containment alone and BOTH
create blind escapes, in opposite directions:

- seating the narrower SURFACE first puts `list(int) × {all?/1, all?/2, empty?}`
  ahead of `list(:ok) × {empty?}`. `list(int)` is a subtype of its sibling and
  the very same test — every list is "a non-empty list" to a predicate that
  records list shape and nothing else — so the surface rule seats an arm whose
  CALLABLE test admits three lambdas in front of one admitting a single lambda,
  where it swallows that sibling's values.
- seating the narrower TEST first puts `list(int) × {all?/1}` ahead of
  `list(:ok) × {all?/1, empty?}`, because a callable set of one is strictly
  inside a set of two. Then `Enum.all?([:ok, :ok])` carrying the shared lambda
  satisfies BOTH of its questions — list shape is element-blind — and reaches
  the int-reading body. `dispatch_seat_element_blind` is that program.

Neither containment is the criterion on its own. SURFACE COVERAGE is: `covers`
holds of `(early, late)` when, at every position where their tests could both
admit a value on an ERASING axis (list elements, tuple payloads, struct, map,
binary and resource contents -- `overlaps_on_an_erasing_axis`), `early`'s
surface already contains `late`'s. "The tests differ" is not separation on an
erasing axis: tuple arities {2} and {2,3} both admit a 2-tuple, list shapes
{NonEmpty} and {Empty, NonEmpty} both admit a cons cell. Only the exact axes
(ints, floats, atoms, callables) separate by mere difference, because a value
passes an exact test only by being in the tested set, which the arm's surface
names. Under that definition, seating a covering arm first cannot escape
anything, by construction -- the surface check is skipped only where the tests
cannot both admit a value the projection would blur.

### The rule

- arms are seated by their QUESTION GROUP, and a group's members keep arrival
  order. The carve-out is the safety story — no test the plan emits separates a
  group's members, so their order decides which body their shared values run,
  and fz-kdt.107 prototyped canonically ordering them and got `{:done, 3}` where
  `{:halted, 3}` was due.
- groups start in arrival order, and group `x` is moved ahead of group `y` when

      covers(x, y) and ( not covers(y, x) or test(x) strictly inside test(y) )

  The first disjunct is the OBLIGATION — only one direction is escape-free, so
  take it. The second is the PRECISION preference — both directions are
  escape-free, so hand a value both tests admit to the arm that named it most
  precisely. The relation is antisymmetric: if both directions held, both would
  need `covers` both ways, so both would rest on strict mutual containment of
  the tests, which makes the tests equal and the two groups one.
- where NEITHER group covers the other, no seat is escape-free and the rule
  declines to have an opinion: the pair keeps arrival order. That is fz-kdt.107's
  inseparable class one rung wider, and **fz-kdt.131** owns it. The cure is a
  runtime test that can see what the body relies on — fz-kdt.119's per-position
  tuple tags, fz-kdt.107 step 3's list elements — not a cleverer sort.

The correction is one backward insertion pass: each group walks left past
already-seated groups for as long as the relation holds of the pair, and stops
at the first group it may not pass. A permutation comes out, so the seat is
TOTAL by construction and needs no tie-break to fall through to, and it is a
deterministic function of the arms and their arrival order. Stopping at the
first refusal is a requirement, not a compromise: passing a group means passing
everything between. `covers` is not transitive — two groups can be blind at
different positions — so no rank or comparator linearizes it, which is why the
pass is an explicit insertion rather than a sort.

### What the seat guarantees

Every pair whose seat differs from arrival order was individually checked and
moved only under `covers`, which admits no blind escape; every other pair sits
exactly as arrival left it. So **the seat's blind escapes are a SUBSET of
arrival order's** — this rule can only ever remove one, never add one. A
`debug_assert` in `specificity_order` holds every callsite of every debug
compile to it, and
`compiler2_dispatch_seats_the_covering_arm_where_one_covers` reads the same
property back off the landed artifact across the arm-order census.

What the seat does NOT guarantee is that no blind escape remains.
`compiler2_dispatch_blind_escape_census_is_the_known_population` counts the
survivors: 19 positions over 12 arm pairs, every one of them a list-shape test
that cannot see its elements, and every one of them arrival order's before any
seating rule existed. Three of `enum_map_family`'s are the ones that already
abort natively under a reversed arm order; `dispatch_seat_element_blind`'s one
is why that fixture prints the right answers only because arrival seats the atom
arm first. The census is a RATCHET pointing at fz-kdt.131, not a target: a new
entry is a new latent miscompile and wants a ticket, not a re-blessed constant.

Arm order was the settled targets' order and nothing else before fz-kdt.129 —
the fixpoint's, which is the agenda's — and `enum_predicate_search` seated one
`List.reduce_while_step/3` dispatch's wide arm first under FIFO and its narrow
one first under LIFO. That pair is now seated wide-first under both, because the
wide arm is the one that covers.

The artifact rung materializes a `CallEdge::Dispatch` for the `::Dispatch`
answer: the plan is the runtime type-test graph, while each `DispatchCallArm`
carries the existing impl `CallTarget`, return flow, and extern marshal facts
outside `DispatchMatrix`. Dispatch misses are unreachable for closed receiver
unions and lower to an explicit halt/trap path; there is no residual
protocol-stub outcome in the matrix.

A fired trap is reported at the process-exit boundary as a fault, not unified
with normal completion. Compiler2's `Term::Halt` codegen (the only producer is
the fault traps: `function_clause`, `match_error`, unreachable-control) calls
`fz_exit_fault` after recording the reason atom into `halt_value`, setting
`Process.exit_fault = Some(atom)`. Normal completion never touches the field,
and drivers never infer fault-ness from `halt_value` (a program may
legitimately return a fault-shaped atom). `Compiler2::run_root_jit` reads the
root task's `exit_fault` after `run_until_idle` and returns the reason as an
`Err`; `fz_aot_run_main` reads it before teardown, names the reason on stderr,
and exits nonzero. The backend interpreter needs no marker — its trap is a
Rust `Err` that already propagates to the CLI.

`pattern_dispatch_from_source` is the source-pattern producer. It consumes the
AST-facing `SourcePatternRows`, extracts positive proof paths into `Order::Source`
arms, and keeps pattern-specific payloads as opaque outcome metadata: body id,
leaf bindings, pinned inputs, prepared keys, and guard expressions.
Inline lowering for function heads, `case`, and `with else`, plus interpreter
receive probes and native receive codegen, walk the resulting
`PatternDispatchPlan` directly. Receive accept/reject policy is not encoded in
`DispatchMatrix`; selective receive remains a producer/outcome policy layered
above the same regions. For selective receive specifically, the winning outcome
is not "put the message somewhere and revisit it later". A hit outcome is a
projected outcome-closure payload for the winning clause body; a miss outcome is
"append the full message to the mailbox and stay parked".

Compiler2 semantic reachability is another consumer, not another dispatch
model. `compiler2/dispatch_reachability.rs` interprets the graph's edge proofs
against root input `Ty` rows and uses plan-owned `PatternSubjectRef` paths to
derive every tested projection. It never stores types by `SubjectId` and never
adds type/domain policy to this generic module. Before traversal, a runtime
envelope replaces bare inference templates in positive, recursively inspectable
tuple/list/map/resource slots with `any`, narrows unresolved negative exclusions
instead of widening them, and preserves callable arrows that the pattern graph
cannot inspect. Negative finite variable branches are erased while preserving
their concrete axes; negative cofinite branches with excluded variable IDs
become empty. A cofinite variable axis with no excluded IDs remains ordinary
top. Exact tuple projections lift to their roots;
ambiguous positional list projections keep both edges. Each reachable outcome
retains its refined root inputs for clause analysis, so reachability and clause
binding consume the same proof.

## Vocabulary Boundary

DispatchMatrix has three layers that must stay separate:

- **Region question:** the semantic question, such as "is subject in this type",
  "is this value a cons cell", "is this key present", or "is this value equal to
  that literal or pinned value".
- **Branch evidence:** what becomes true only on a branch. A cons success can
  project head/tail. A map-key-present success can project the map value, even if
  that value is `nil`; the miss branch records absence. A failed empty-list
  question means "not empty list", not "cons".
- **Backend emission:** the current IR can still use `TypeTest`, equality,
  `IsListCons`, `IsEmptyList`, or `MatcherMapGet` plus `IsMatcherMapMiss`.
  Those names are lowering choices, not DispatchMatrix source vocabulary.

Future dispatch changes should add producers on top of this model instead of
adding one-off pattern, protocol, or planner dispatch passes. Graph compilation
is tested with fake outcome handles, callsite-dispatch arm ids, and
source-pattern-derived pattern outcomes. Protocol dispatch and source-pattern
dispatch share the same decision model; runtime helper names that still say
"matcher" are ABI vocabulary, not a separate compiler data model.
