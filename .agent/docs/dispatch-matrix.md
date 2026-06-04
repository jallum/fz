# Dispatch Matrix

`src/dispatch_matrix` is the shared model for the dispatch unification epic
(`fz-v19`). Protocol finite-union dispatch and source-pattern dispatch now both
build a `DispatchMatrix`, compile it to a `DispatchGraph`, and let producer
policy decide what a winning outcome means. `PatternMatrix` still normalizes AST
patterns into rows and emits the current `Matcher` shape as adapter input, but
the runtime decision graph for source patterns is owned by `DispatchMatrix`.

The model names four separate concepts so future dispatch work does not grow new
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

`collect_protocol_dispatch_matrix_candidates` is the protocol producer. It reads
planner facts and classifies a protocol callsite as ordinary static dispatch, no
local dispatch, or a specificity-ordered matrix over visible local impls. A
closed receiver union gets one direct-call outcome per covering local impl and no
fallback; an open, erased, or provider-only overlap gets an explicit residual
fallback outcome that preserves the protocol stub path. The frontend rewrite hook
lowers the compiled `DispatchGraph` into the current `TypeTest`/`If` IR shape:
closed graph `Fail` tails become the final direct `else`, while open residual
fallbacks become the original stub call.

`pattern_dispatch_from_matcher` is the source-pattern producer. It consumes the
AST-free `Matcher` that `PatternMatrix` emits as a compatibility input, extracts
positive proof paths into `Order::Source` arms, and keeps pattern-specific
payloads as opaque outcome metadata: body id, leaf bindings, pinned inputs,
prepared keys, and guard expressions. `matcher_from_pattern_dispatch_plan`
rebuilds a graph-derived `Matcher` from the compiled `DispatchGraph` so existing
inline lowering and the receive ABI can keep using their current backend shape
while their decisions come from `DispatchMatrix`. Receive accept/reject policy is
not encoded in `DispatchMatrix`; receive remains a producer/outcome policy
layered above the same regions.

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
adding one-off matcher or planner dispatch passes. At this ticket boundary,
graph compilation is tested with fake outcome handles, protocol direct-call /
stub outcomes, and PatternMatrix-derived pattern outcomes. Protocol dispatch and
source-pattern dispatch share the same decision model; the remaining `Matcher`
usage is an ABI/lowering adapter, not a separate runtime semantics owner.
