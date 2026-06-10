---
purpose: "total case and with clauses share one stdout oracle across old paths and fz2"
paths: [jit, interp, aot, repl, fz2-run, fz2-interp, fz2-build]
---

# case_with_total

Exercises `case` tuple-pattern dispatch and `with` tuple-pattern binding with
explicit fallback clauses. The older `case_tuple_pattern_sequential` fixture
keeps the partial-clause warning oracle; this fixture is the total-control
surface used for fz2 fixture-matrix parity.
