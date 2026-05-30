---
purpose: "Enum.count/2 remains correct after Enum.reduce/3 retains the same list"
paths: [jit, interp, aot, repl]
---

Pins the retained-list non-tail-call shape before a predicate count.
