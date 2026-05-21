---
purpose: "receive whose clauses interleave tuple-3 / atom / tuple-3 — matrix shares the tuple-arity test across the non-adjacent tuple clauses"
paths: [jit, interp, aot]
---

# receive_interleaved_tuple_arity

fz-puj.39 (H14) — matrix-derived shared-constructor verification.

The deleted `same_tuple_arity_run` peephole (fz-puj.23, retired in H12)
only shared a tuple-arity test across *adjacent* clauses with the same
arity. The matrix specializer shares across non-adjacent clauses by
construction: every tuple-3 row, regardless of source position, flows
into a single `TupleArity = 3` arm; the interleaved atom clause flows
through the default arm.

Locks behavioral parity (interp / JIT / AOT all consume each message in
source order) for the adjacency-break shape the old peephole gave up on.
The shape oracle lives at `ir_lower::tests::receive_oracle_interleaved_tuples_share_via_matrix`.
