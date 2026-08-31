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
wider domain (subtype at every input position). A callsite left with one
destination is a `Direct` call rather than a one-armed dispatch.

Both halves of (b) are load-bearing. Domain containment alone is not behavioral
completeness — a multi-target summary normally names one target per selected
callee, which is exactly what protocol dispatch is, and a wider domain sitting
on a different function's body is no stand-in at all. And one-way containment is
not (a): when the questions differ, the narrower test matches only values its own
domain names and everything else falls through, so whichever order the pair is
tested in a value lands in an arm whose domain contains it — order costs
precision, not meaning. A `:timeout` arm beside an `any` arm is that case, and
both survive. Twins with no stand-in between them (neither domain contains the
other, or two different functions) also survive and stay order-decided.

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
