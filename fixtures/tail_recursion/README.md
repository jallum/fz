---
purpose: "100k-deep self-recursion must TCO — exits cleanly with the accumulated count"
paths: [jit, interp, aot]
repl-skip: "eval::Interp lacks TCO; 100k self-recursion overflows the host stack"
---

# tail_recursion

100k-deep self-recursion must TCO — exits cleanly with the accumulated count
