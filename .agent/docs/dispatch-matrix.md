# Dispatch Matrix

`src/dispatch_matrix` is the side-by-side model for the dispatch unification
epic (`fz-v19`). It is deliberately not in the production path yet: today,
`PatternMatrix` still owns source-pattern matching and
`rewrite_closed_union_protocol_dispatch` still owns protocol union rewrites.

The model names four separate concepts so future dispatch work does not grow new
subsystem-specific cascades:

- `Region` is the value-space question an arm asks of a subject: type,
  constructor shape, literal equality, map-key presence, bitstring shape, or a
  guard predicate.
- `Order` is why an arm wins when regions overlap: source order, type
  specificity, or an explicit materialized order.
- `Outcome` is an opaque handle chosen after an arm wins. Pattern bodies,
  receive accept/reject behavior, protocol direct calls, fallthroughs, and halts
  stay outside the region model.
- `DispatchGraph` is the executable decision shape: tests route to nodes, and
  successful edges carry branch-local proofs and projections.

Future dispatch changes should add producers or graph compilation on top of this
model instead of adding one-off matcher or planner dispatch passes. At this
ticket boundary, tests cover only construction invariants; no runtime behavior is
owned by `DispatchMatrix`.
