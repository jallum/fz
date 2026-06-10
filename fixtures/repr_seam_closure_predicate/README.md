---
purpose: "Closure predicate results stay truth-preserving across native representation seams"
paths: [jit, interp, aot, repl, fz2-run, fz2-interp, fz2-build]
---

Pins callback shapes used by `Enum.count/2`: a closure returns a boolean, the
caller branches on it, a reducer captures that predicate, and a generic
higher-order list reducer repeatedly invokes the captured reducer while the
accumulator stays in the raw integer lane. It also pins the `Enum.count/2`
shape where an outer function receives the predicate as a parameter and a nested
reducer closure captures that parameter.
