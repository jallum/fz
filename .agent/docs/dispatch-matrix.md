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
erases a callable argument to `fun_top`, so two arms whose reducers are
different closure literals are one and the same observable; judged
semantically, that incomparable literal blocks the containment and keeps a
narrow arm alive at a position no runtime test can look at. That is how
`Range.reduce_step/6`'s `({:cont, int} | {:halt, int}, #66closure[])` /
`({:cont, int}, #68closure[])` pair used to survive and swallow `:halt` under a
legal arm order.

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
not (a): when the questions differ, the narrower test matches only values its own
domain names and everything else falls through, so whichever order the pair is
tested in a value lands in an arm whose domain contains it — order costs
precision, not meaning. A `:timeout` arm beside an `any` arm is that case, and
both survive. Twins with no stand-in between them (neither observable domain
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
