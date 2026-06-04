---
purpose: "Enumerable protocol dispatch covers List, Range, and Map receivers"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

Exercises a closed-union `Enumerable.count/1` call whose receiver can be a
list, a `Range` struct, or a map. The mixed receiver forces protocol dispatch
to emit runtime type arms for all three impl targets.
